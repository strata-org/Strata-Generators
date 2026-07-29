# Call-Statement Generator (`genCallStmt`) — Progress & Handoff

_Worktree: `/Users/ernestng/Documents/strata-generators-proc` (branch `procedure-generator`)._
_Last updated: 2026-07-28._

## Task

Extend the statement generator so it can also generate **procedure calls**
(`CmdExt.call pname args md`). A call site must respect the callee's type
signature: each formal parameter is `in`, `out`, or `inout`, and for `inout`
(and `out`) parameters the generated program must **contain, in scope and at the
right type, the exact name the callee's signature dictates** — the callee's
typing rule (`CmdExtHasType'.call`, premises 6 and 7) leaves the generator *no
naming freedom* for `M ∪ O`.

### Design decisions already locked in (user, 2026-07-28)

1. **Callees are monomorphic** (`typeArgs = []`), so the type-instantiation
   `σ := []` discharges every type obligation as the identity substitution.
2. **Emit strategy = "reuse ctx vars + init only missing".** For each required
   `M ∪ O` name: if it is already in the threaded `VarCtx` at the *right* type,
   reuse it; if absent, emit a fresh `init … nondet`; if present at the *wrong*
   type, the callee is uncallable (that branch yields `default`). This is
   **required for correctness**, not an optimization — the callee dictates the
   names, so we must make those exact names exist at those exact types.
3. **Layout — front-aligned three blocks.** `inputs = M ++ I`, `outputs = M ++ O`
   (M = inout, I = input-only, O = output-only, mutually key-disjoint). This is
   exactly what `genProcedure` already emits, so no change to the *declaration*
   generator is needed.
4. **The call recipe:**
   `mkArgs M O exprs = M.map (.inoutArg ·.1) ++ exprs.map .inArg ++ O.map (.outArg ·.1)`
   ⟹ `getInputExprs = M.map (fvar () ·.1 none) ++ exprs`, `getLhs = M.keys ++ O.keys`.
5. **genCallStmt emits a lexically-scoped block:**
   `Stmt.block freshLabel (initChain missing ++ [Statement.call pname (mkArgs M O exprs) default]) default`.
   The block's output context = its input context, so the freshly-`init`'d names
   do **not** leak into the surrounding scope (keeps the threaded invariant clean).

## Status

**Feasibility fully de-risked. Zero production code written yet.** All four
load-bearing soundness kernels are proved in isolation and verified
**axiom-clean** (`propext, Classical.choice, Quot.sound` only) via `lean_run_code`.
The remaining work is (largely mechanical but broad) *threading* a new `procs`
context parameter through the generator + proof files, then assembling the
proved kernels into the real `.call` soundness case.

### The 4 verified kernels (copy these into production)

All are stated with `open Lambda LExpr Core Imperative TypeSpec` and
`abbrev Sig := ListMap (Identifier Unit) LMonoTy`.

1. **`call_recipe_inout_sound`** — the 7-premise call-typing kernel. Given the
   front-aligned decomposition, `find?`, arity/typing/disjointness hypotheses,
   produces `CmdExtHasTypeA C P Γ (CmdExt.call pname (mkArgs M O exprs) md) Γ`.
   Full signature and premise-by-premise proof are in the memory note
   `project_procedure_gen` (search "call_recipe_inout_sound"). Key hypotheses the
   generator must supply:
   - `hInputs : proc.header.inputs = M ++ I`, `hOutputs : proc.header.outputs = M ++ O`
   - `hfind : Program.Procedure.find? P pname = some proc`
   - `hExLen : exprs.length = I.length`
   - `hMinΓ` / `hOinΓ` : every `M`/`O` name is in `Γ` at its formal type ← **this
     is what the init-chain establishes**
   - `hExTy` / `hExNoFvar` : the by-value input exprs are well-typed and are not
     bare unannotated fvars (both from `genLExpr` at `fctx = []`)
   - `hIdisjOut : ∀ i < I.keys.length, (M ++ O).keys.contains I.keys[i] = false`

2. **`initChain_types`** — an `init … nondet` chain over the *missing* names
   builds a `Γ` binding all of them at their formal types:
   ```
   def initChain (news) := news.map (fun (x,mty) => Statement.init x (.forAll [] mty) .nondet default)
   def insertAll (Γ) (news) := news.foldl (fun Γ p => {Γ with types := Γ.types.insert p.1 (.forAll [] p.2)}) Γ
   theorem initChain_types {P C L} (news) : ∀ Γ,
     (∀ i (hi : i < news.length), (insertAll Γ (news.take i)).types.find? (news[i].1) = none) →
     StmtsHasTypeA P C Γ L (initChain news) C (insertAll Γ news)
   ```
   Proof: induction on `news`; head via `StmtHasType'.cmd`/`CmdExtHasType'.cmd`/
   `CmdHasType'.init_nondet … (rigidAnnotCompat_forAll_nil hd.2)`. **NB**
   `rigidAnnotCompat_forAll_nil` is `private` in `CmdHasTypeAGen.lean:340` — either
   de-privatize it or re-prove inline (body captured in the memory note). The
   `cons` step uses `StmtsHasType'.cons C C C Γ {Γ.insert} (insertAll Γ (hd::tl)) L _ _ hhead htail`
   (arg order: **three `LContext`s then three `TContext`s**).

3. **`StmtsHasTypeA_append`** — chains two statement-list judgments:
   ```
   theorem StmtsHasTypeA_append {P L} {l1} :
     ∀ {C Γ Γ' Γ'' C' C'' l2},
     StmtsHasTypeA P C Γ L l1 C' Γ' → StmtsHasTypeA P C' Γ' L l2 C'' Γ'' →
     StmtsHasTypeA P C Γ L (l1 ++ l2) C'' Γ''
   ```
   Proof: `induction l1` (**not** `induction h1` — mutual inductive rejects it);
   **must** generalize `C` in the motive (`∀ {C …}`) or the tail (typed at the
   mid context `Ca`) won't unify. `cons` arm:
   `cases h1 with | cons _ Ca _ _ Γa _ _ _ _ hs hss => StmtsHasType'.cons _ _ _ _ _ _ _ _ _ hs (ih hss h2)`.

4. **`block_wraps`** — wraps a body judgment in a lexically-scoped block:
   ```
   theorem block_wraps {P C L} {Γ Γbody Cbody} {label body md}
     (hfresh : label ∉ L)
     (hbody : StmtsHasTypeA P C Γ (label :: L) body Cbody Γbody) :
     StmtHasTypeA P C Γ L (Stmt.block label body md) C Γ
   := StmtHasType'.block C Γ Cbody Γbody L label body md hfresh hbody
   ```

### How they assemble (the real `.call` soundness case)

```
block_wraps hfresh
  (StmtsHasTypeA_append
     (initChain_types missing …)                       -- Γ ⟶ Γ' (all M∪O names bound)
     (StmtsHasType'.cons … (call_recipe_inout_sound …)  -- the single call stmt
                           (StmtsHasType'.nil …)))
```
where the `hMinΓ`/`hOinΓ` premises of `call_recipe_inout_sound` are read off the
`insertAll` context produced by `initChain_types` (plus the reused ctx entries).

## What remains — production threading (pending tasks #1–#6)

The generator/proof files break *atomically* on any signature change, so thread
the new parameter through all of them in one pass, then build once.

### #1 — Add the proc-sig context type + thread it

- Define `ProcSig` (per-callee: `pname : String`, three blocks `M I O : Sig`) and
  `ProcSigCtx := List ProcSig`. Store the three blocks **directly** (do not
  re-derive from `inputs`/`outputs` — front-alignment is not automatic for an
  arbitrary `P`-procedure, though it *is* what `genProcedure` emits).
- Define the correspondence predicate
  `ProcSigCorresponds (procs : ProcSigCtx) (P : Program) : Prop :=
     ∀ s ∈ procs, ∃ proc, Program.Procedure.find? P s.pname = some proc ∧
       proc.header.typeArgs = [] ∧ proc.header.inputs = s.M ++ s.I ∧
       proc.header.outputs = s.M ++ s.O ∧
       (∀ i < s.I.keys.length, (s.M ++ s.O).keys.contains s.I.keys[i] = false)`.
- Thread `procs : ProcSigCtx` **after `immutableVars`** in `genStmt`/`genStmts`
  (`StmtHasTypeAGen/Core.lean`). It does **not** need to go through `genCmd` (a
  call is a `Stmt.cmd (CmdExt.call …)` typed at the statement level, not a base
  `Cmd`), so `CmdHasTypeAGen/Core.lean` is untouched — narrower than `immutableVars`.
- Default `procs := []` at every external call site: `genProgramStmts`
  (`StmtHasTypeAGen/Core.lean:336`), `genProcedure` body seed
  (`ProcedureHasTypeAGen/Core.lean:140`), and `CmdHasTypeAGen/TestSupport.lean`,
  `TestScaffold.lean`, `TycheViz.lean`.

### #2 — Implement `genCallStmt`

New leaf sub-generator (in `StmtHasTypeAGen/Core.lean`), added as a new
`frequency` branch in **both** the size-0 and size+1 lists of `genStmt` (bump the
`hw` sum proofs and every `_mem`/`_outCtx_functional`/`_sound` dispatch `rcases`
arm count accordingly — that's the fiddly part).

Behavior: pick a callee `s ∈ procs`; compute the missing `M ∪ O` names (absent
from `ctx`, or present at wrong type → skip callee → `default`); for the by-value
inputs `I`, draw `exprs ← I.values.mapM (genLExpr [] octx [] tvars [] depth ·)`;
emit `Stmt.block freshLabel (initChain missing ++ [Statement.call s.pname (mkArgs s.M s.O exprs) default]) default`;
return output ctx = **input** `ctx` (block is lexically scoped).

Define `mkArgs` (currently only exists in the isolated proofs) in production —
put it next to `Statement.call`, or in the generator file. Its two projection
lemmas `getIn_mkArgs` / `getLhs_mkArgs` are already proved axiom-clean (see memory
note) — port them.

### #3 — Prove the `.call` soundness case

Assemble the four kernels as shown above. Add `hProcs : ProcSigCorresponds procs P`
as a new hypothesis to `genStmt_sound`/`genStmts_sound` (and thread it through the
mutual recursion). The `M`/`O`-in-Γ facts come from `initChain_types`'s
`insertAll` result composed with the reused ctx entries; the correspondence
hypothesis supplies `hfind`/`hInputs`/`hOutputs`/`hIdisjOut`.

### #4 — Extend the mutable-vars invariant for `.call`

`ProcedureHasTypeAGen/MutableVars.lean`: `genStmt_mutableVars`/`genStmts_mutableVars`
gain a `.call` arm. The block's body `init`s fresh names, but the block is
lexically scoped so `outCtx = ctx` — **no** new mutable keys escape. Should be a
short "context unchanged" arm mirroring the `block` case.

### #5 — Update `genProcedure` soundness/completeness

- `genProcedure` passes `procs := []`, so **`ProcSigCorresponds [] P` is
  trivially true** and `genProcedure_sound` can stay side-condition-free (just
  supply the trivial witness). *Alternatively*, per the older "bodies may call"
  decision, give `genProcedure` a real `procs` and add `hProcs` to its soundness
  — but the `[]` route keeps the clean statement; **recommend `[]` for now** and
  revisit if we want procedure bodies to call each other.
- Completeness: extend `StmtReachable`/`StmtsReachable` with a `.call`
  constructor and add the dispatch arm to `genStmt_complete`. Add a `call_mem`
  membership-lifting lemma (mirrors `block_mem`).
- Update `PROCEDURE_GENERATOR_PROGRESS.md` "Remaining" section.

### #6 — Build & verify

`lean_build` the whole worktree (was 240 jobs, exit 0 before this work). Then
`lean_verify` the touched top-level theorems + `genProcedure_sound`/`_complete`
to confirm axioms stay `[propext, Classical.choice, Quot.sound]`.

## Lean gotchas (carried over — save time)

- **No Mathlib in this worktree:** `set`, `push_neg` are unavailable. Use
  `Nat.not_lt` / `Nat.le_of_not_lt` / `omega`.
- **Dependent `getElem` index `rw` fails** ("motive is not type correct"):
  normalize indices with `simp only [hEq]`, or gather all length facts as `have`s
  and let `omega` close bound side-goals. For *name* equalities use the
  non-dependent `getElem?` route.
- `Sig := ListMap (Identifier Unit) LMonoTy` has **no `GetElem`** — index via
  `M.keys[i]` / `M.values[i]` (they're `List`s), never `M[i]`.
- `pname : String` (not `Ident`) in the call rule.
- `mem_support_frequency_iff` needs the positive-weight-sum proof; every
  `frequency` dispatch site enumerates branches by `.head`/`.tail` — adding the
  `.call` branch shifts all subsequent branch positions.
- `lean_multi_attempt` gives false positives on stale imports; run `lean_build`
  before trusting `lean_goal` after edits. `lean_run_code` is always reliable.

## Constraint

**Do not commit unless the user explicitly asks.** Nothing is committed beyond
`ff3840b`; all Phase-B + this work is uncommitted (or, for this session, not yet
written to production).
