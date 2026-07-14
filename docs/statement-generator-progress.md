# Statement generator — progress & handoff

**Branch:** `statement-generator` (worktree at `~/Documents/strata-generators-stmt`,
sharing the main repo's `.lake` via a symlink).

**Goal:** a sound and complete generator for random well-typed Strata Core
**statements** (`Statement = Imperative.Stmt Core.Expression Core.Command`),
w.r.t. `StmtHasTypeA` / `StmtsHasTypeA` in
`~/Documents/Strata/Strata/Languages/Core/StatementTypeSpec.lean`.

It reuses the existing, already-proven-sound-and-complete generators:
- `genCmd` / `genCmd_sound_env` / `genCmd_complete` (`StrataGenerators/CmdHasTypeAGen{,/Core}.lean`)
- `genFunction` / `genFunction_sound` / `genFunction_complete` (`StrataGenerators/FunctionHasTypeAGen{,/Core}.lean`)
- `genLExpr` + the `GenLExprSound` / `GenLExprComplete` predicates (`StrataGenerators/HasTypeAGen{,/Core}.lean`)

---

## Files added

| File | Status |
|---|---|
| `StrataGenerators/StmtHasTypeAGen/Core.lean` | **Complete, builds clean.** Generator defs. |
| `StrataGenerators/StmtHasTypeAGen.lean` | **Soundness and completeness complete.** |
| `lakefile.toml` | Two `lean_lib` entries added (`StmtHasTypeAGen.Core`, `StmtHasTypeAGen`). |

Everything currently on the branch **builds with zero `sorry`**:
```
cd ~/Documents/strata-generators-stmt
lake build StrataGenerators.StmtHasTypeAGen   # EXIT=0
```
(The only `sorry` warnings are pre-existing in Strata's `LExprTypeSpec.lean`,
lines 900/928/5495 — not ours.)

---

## Design decisions (already made — keep these)

1. **Two threaded contexts.** `StmtHasType'` is 5-place: `C Γ s C' Γ'`.
   - `Γ` (variable scope) is threaded as the flat `VarCtx` from
     `CmdHasTypeAGen/Core.lean`, related to the semantic `TContext` via
     `VarCtxCorresponds` — exactly as `genCmds` does.
   - `C` (ambient `LContext`) is threaded as an honest `LContext CoreLParams`;
     `GenStmtResult.outC` **is** the output ambient context of the typing relation.

2. **`cmd` case** reuses `genCmd` (wrapped `CmdExt.cmd`); typing goes through
   `CmdExtHasType'.cmd → CmdHasType'`.

3. **`funcDecl` case.** The syntactic decl node (`PureFunc`, polytypes) and the
   well-typed witness `func` (monotypes, added to `C`) are **independent** in the
   spec (rule only needs `¬decl.isRecursive` ∧ `FuncHasType' func`). The
   generator samples them independently: `genDecl` (a non-recursive `PureFunc` via
   `Function.toPureFuncDecl <$> genFunction`) for the node, and a separate
   `genFunction` for the witness.

4. **`typeDecl` case.** The premise is `C.addKnownTypeWithError … = .ok C'`.
   The generator **matches** on the very same `addKnownTypeWithError` call, so the
   `.ok` branch's output context is *definitionally* `C'` — no `HashMap` freshness
   reasoning needed. On `.error` (name clash) it falls back to a well-typed `exit`.
   Soundness inverts this with `split at hr`.

5. **Lexical scoping.** `block`, each `ite` branch, and the `loop` body have
   output context = **input** `(C, Γ)`. The generator discards the nested output
   context and returns the input `C, ctx`.

6. **Single `size` budget + termination.** `genStmt`/`genStmts` take **one**
   `size` (the QuickCheck `sized` knob), *not* a separate nesting `fuel` and term
   `depth`. `size` bounds nesting depth, is passed on to the leaf/expression
   sub-generators as their term depth, and bounds every generated list length via
   `choose 0 (size+1)` — exactly as the single `Nat` argument of `genLExprBase`
   does for expressions. As a statement nests, `size` shrinks, so sub-programs get
   smaller deeper down. `genStmt`/`genStmts` are mutually recursive with a
   lexicographic measure `(size, tag, len)`: `genStmt n ↦ (n,0,0)`,
   `genStmts size len ↦ (size,1,len)`; the nesting cases generate bodies via
   `genStmts … size …` at the *smaller* `size`, and `genStmts` recurses on `len`
   with `size` fixed. The same measure is repeated on the mutual soundness
   theorems. **Consequence:** the soundness environment `GenStmtSoundEnv` is
   *depth-generic* (its `exprSound`/`freshDisjoint` obligations are quantified over
   all depths `d`), since leaves are generated at the shrinking size rather than a
   fixed depth.

7. **Enclosing block labels (`exit` realism).** `genStmt`/`genStmts` thread a
   `labels : List String` of the *enclosing block labels*. `genExitStmt` samples
   its label from `labels` (falling back to `String.arbitrary` only when empty, at
   top level), so a generated `exit` breaks out of a live enclosing block instead
   of a dead random string — the `exiting l` config is consumed by a matching
   `block` (`Imperative.StmtSemantics`, `step_block_exit_match`). A `block`
   descends into its body under `label :: labels`; `ite`/`loop` bodies inherit
   `labels` unchanged (only `block` introduces a named exit target). Labels are
   typing-irrelevant (no `StmtHasType'` rule constrains them), so this affects only
   operational realism, never soundness/completeness. `labels` is a *proof-relevant
   index* of the `StmtReachable`/`StmtsReachable` relations (the `block`
   constructor extends it) and an explicit argument of the mutual
   soundness/completeness theorems (recursive calls vary it).
   Design informed by *Testing Noninterference, Quickly* (Hriţcu et al., ICFP'13):
   their "generation by execution" makes jump targets valid by construction;
   Strata's lexical scoping lets us achieve the same guarantee statically.

---

## Soundness — DONE ✅

In `StmtHasTypeAGen.lean`:
- `GenStmtSoundEnv` — bundles the context-dependent obligations (`toTCtx`, `corr`,
  `exprSound`, `freshDisjoint`, `toTCtx_insert`, `simpleOps`). `toCmdEnv` reinterprets
  it as a `GenCmdSoundEnv` at any `C` (legal: no `GenCmdSoundEnv` field mentions `C`).
- Per-constructor: `genCmdStmt_sound`, `genExitStmt_sound`, `genFuncDeclStmt_sound`,
  `genTypeDeclStmt_sound`.
- Guard/measure/invariant helpers: `genCondOrNondet_det_sound`,
  `genOptMeasure_some_sound`, `genInvariants_sound`.
- **Mutual** `genStmt_sound` / `genStmts_sound` — full soundness by WF recursion on
  `(size, tag, len)`. Every generated statement satisfies `StmtHasTypeA P C Γ s C' Γ'`
  for any program `P`.

---

## Completeness — DONE ✅

**Final design differs from the sketch below** (which is retained for context).
Two facts forced the change:

1. **`StmtHasTypeA` alone can't state a meaningful completeness goal.** Lexical
   scoping makes the typing judgment of `block`/`ite`/`loop` equal `C Γ ⟶ C Γ` —
   the body/branches don't appear in it. So "∃ reachable `r` re-realizing the
   judgment" is *vacuous* for every nesting constructor (an `exit` would witness
   any block). The spec relation discards exactly the structure completeness must
   pin down.
2. **`CmdHasTypeA` output context is not deterministic** (`init_nondet` leaves the
   stored monotype free up to `RigidAnnotCompat`), so `genCmd_complete` can't be
   black-boxed + bridged by a determinism lemma to thread the sequence.

**What was proven instead.** A `size`-indexed, `VarCtx`-threaded mutual inductive
**reachability relation** `StmtReachable` / `StmtsReachable` that mirrors
`genStmt` / `genStmts` constructor-for-constructor. Each constructor carries the
generator's normal-form conditions (metadata `default`) plus component
reachability (leaf sub-generator support membership at the current `size`;
`genLExpr` support for guards/measures/invariants at `size+1`; `len ≤ size+1`
bounds; bodies reachable at the smaller `size`). Then:

- `genStmt_complete` / `genStmts_complete` (mutual): every reachable statement /
  list is in the generator's support with the **exact** statement, output ambient
  context `C'`, and output scope `ctx'` — i.e. `⟨s, C', ctx'⟩ ∈ support …`.
  Proof is a one-line-per-constructor dispatch to the `_mem` lemmas.
- `genStmt_complete_sound` (capstone): reachable ⇒ in support **and** well-typed
  (`StmtHasTypeA`, via `genStmt_sound`), confirming `StmtReachable` characterizes
  exactly the generator's *well-typed* support (not vacuous).

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only). The
procedure-call (`cmd`→`.call`) sub-case remains genuinely unreachable: the `cmd`
constructor of `StmtReachable` ranges over `genCmdStmt` (wrapping `CmdExt.cmd`)
support only; there is no procedure-call generator (out of scope, as before).

### As-built structure

Membership-lifting lemmas (lift a sub-generator result into `genStmt`/`genStmts`
support):
- `genCmdStmt_mem`, `genExitStmt_mem`, `genFuncDeclStmt_mem`, `genTypeDeclStmt_mem`
  — a leaf result at depth `n` lands in `genStmt … n` (`exit` at every `n`).
- `block_mem`, `ite_det_mem`, `ite_nondet_mem`, `loop_mem` — reachable at `size+1`
  given body/branch reachability at `size` (+ guard/measure/invariant reachability
  at `size+1`, `len ≤ size+1`).
- `genStmts_nil_mem`, `genStmts_cons_mem` — the list-level constructors.

Completeness-helper support-inversion lemmas (`pick`/`map`/`listOfMaxLength`):
`genCondOrNondet_complete`, `genOptMeasure_complete`, `genInvariant(s)_complete`,
`genTypeConstructor_complete`.

The mutual `genStmt_complete` / `genStmts_complete` are then a
one-line-per-constructor induction on the `StmtReachable` / `StmtsReachable`
derivation, dispatching to the `_mem` lemmas. Because the reachability relation
threads a *single* `size` through a whole list (exactly as `genStmts` does), the
sequence `cons` case needs **no** fuel-monotonicity lemma — the head and tail are
both at the same `size`. (An earlier design with separate `fuel`/`depth` needed
`genStmt_mem_mono`/`genStmts_mem_mono` to realign per-element fuel; those were
deleted in the single-`size` merge, where they are in fact *false* — a leaf
generated at depth `n` need not be in `genStmt`'s support at `n' > n`.)

**No procedure calls.** The `cmd` constructor of `StmtReachable` ranges over
`genCmdStmt` (which wraps `CmdExt.cmd`) only; `CmdExt.call` is genuinely
unreachable. Out of scope, and additionally there is no `ProcedureHasType'`
declarative spec to be complete against.

---

## Build / test notes

- **Worktree `.lake`** is a symlink to the main repo's (7.9 G). Don't delete it.
- **Runtime `#eval` of any generator throws** `(`Inhabited.default` for `IO.Error`)`
  in this environment — this is a **pre-existing Basalt `Gen IO` quirk** affecting
  `genCmd`/`genFunction` too (confirmed in the main repo). It does **not** affect
  correctness: the proofs use `SetGen.Set` support semantics, never `IO`. The
  existing repo `#eval` smoke tests only pass because of `#guard_msgs(drop all)`.
  The three smoke `#eval`s at the bottom of `StmtHasTypeAGen/Core.lean` follow the
  same convention.
- Rebuild deps first if you hit transient "failed to open olean" errors:
  `lake build StrataGenerators.CmdHasTypeAGen StrataGenerators.FunctionHasTypeAGen`.

---

## Reference points in the existing code (copy these patterns)

- Support inversion / reconstruction over `frequency`: `genCmd_support_iff` in
  `CmdHasTypeAGen/Core.lean` — the canonical `.head`/`.tail` witness pattern (our
  `_mem` lemmas already use it).
- Completeness by derivation inversion: `genCmd_complete` (`CmdHasTypeAGen/Core.lean`)
  and `genFunction_complete` (`FunctionHasTypeAGen.lean`) — the reachability-hypothesis
  style to imitate.
- Sequence soundness by induction with a threaded env: `genCmds_sound` /
  `GenCmdSoundEnv` (`CmdHasTypeAGen/Core.lean`) — we mirrored this in
  `genStmts_sound` / `GenStmtSoundEnv`.
- `pick`/`map` optional-generator inversion: `genOptExpr_sound` / `genOptExpr_complete`
  (`FunctionHasTypeAGen.lean`).
