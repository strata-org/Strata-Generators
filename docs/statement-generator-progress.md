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

6. **Termination.** `genStmt`/`genStmts` are mutually recursive with a
   lexicographic measure `(fuel, tag, len)`: `genStmt n ↦ (n,0,0)`,
   `genStmts fuel len ↦ (fuel,1,len)`. The nesting cases (`block`/`ite`/`loop`)
   generate their bodies via `genStmts … fuel …` at the *smaller* `fuel`. The same
   measure is repeated on the mutual soundness theorems.

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
   soundness/completeness/monotonicity theorems (recursive calls vary it).
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
  `(fuel, tag, len)`. Every generated statement satisfies `StmtHasTypeA P C Γ s C' Γ'`
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

**What was proven instead.** A fuel-indexed, `VarCtx`-threaded mutual inductive
**reachability relation** `StmtReachable` / `StmtsReachable` that mirrors
`genStmt` / `genStmts` constructor-for-constructor. Each constructor carries the
generator's normal-form conditions (metadata `default`) plus component
reachability (leaf sub-generator support membership; `genLExpr` support for
guards/measures/invariants; `len ≤ depth` bounds; bodies reachable at the smaller
fuel). Then:

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

### Original sketch (superseded — kept for reference)

The originally-planned scope was the **reachability-hypothesis** style used by
`genCmd_complete` / `genFunction_complete`: given a well-typed statement whose
*sub-components* are individually reachable, the statement is in `genStmt`'s
support at sufficient fuel.

### Done so far (membership-lifting lemmas, all build clean)
These lift a sub-generator result into `genStmt`/`genStmts` support:
- `genCmdStmt_mem`, `genFuncDeclStmt_mem`, `genTypeDeclStmt_mem` — reachable at
  **every** fuel `n`.
- `block_mem`, `ite_det_mem`, `ite_nondet_mem`, `loop_mem` — reachable at fuel
  `fuel+1` given body/branch reachability at `fuel` (+ guard/measure/invariant
  reachability, `len ≤ depth`).
- `genStmts_nil_mem`, `genStmts_cons_mem` — the list-level constructors.

(There is intentionally **no** `genExitStmt_mem` yet — `exit` is only needed as a
target if you want completeness to cover the `typeDecl`-clash fallback, which the
spec never forces; skip it.)

### What remains

**Step A — fuel monotonicity (likely needed).**
`genStmts` threads a *single* `fuel` across a whole list, but different statements
in a well-typed sequence may nest to different depths. So completeness needs:

> `genStmt_mono` / `genStmts_mem_mono`: if `r ∈ support (genStmt … n)` then
> `r ∈ support (genStmt … n')` for all `n' ≥ n` (and the `genStmts` analogue).

Prove this as a **mutual** WF recursion mirroring the generators (same
`(fuel,tag,len)` measure). Base/leaf branches: reuse the `_mem` lemmas above
(they already hold at every fuel). Nesting branches at `n = fuel+1 → n' = fuel'+1`:
invert the source membership, bump each body via the `genStmts` IH at `fuel' ≥ fuel`,
then re-package with `block_mem`/`ite_*_mem`/`loop_mem`. This is the main new
proof effort and the trickiest part (the `choose 0 depth` length witnesses carry
through unchanged since `depth` is fixed).

*Alternative that avoids monotonicity:* state completeness with a **per-statement
fuel** and pick `fuel = max` nesting depth of the whole block up front, threading
that one big fuel everywhere. Cleaner to state, but you still need the bodies to be
reachable at that shared fuel — which is exactly what monotonicity gives you. Recommend
just proving monotonicity.

**Step B — the mutual completeness theorem.**
```
mutual
theorem genStmt_complete (P) (reach-hyps…) (C ctx) (s C' Γ')
    (hwt : StmtHasTypeA P C (toTCtx ctx) s C' (toTCtx Γ')) :
    ∃ r, r ∈ support (genStmt … C ctx depth (nesting s)) ∧ r.stmt = s ∧ r.outC = C' ∧ r.outCtx = Γ'
theorem genStmts_complete … (hwt : StmtsHasTypeA …) : ∃ …
end
```
Proof by induction on the `StmtHasType'` / `StmtsHasType'` derivation (use
`cases hwt`, as `genCmd_complete` does with `CmdHasTypeA`). Per constructor:
- `cmd`: invert `CmdExtHasType'`. The `.cmd c` sub-case → `genCmd_complete` then
  `genCmdStmt_mem`. The `.call …` sub-case → **reachability hypothesis** (bundle a
  `hCallReach` premise: the call statement is in `genCmd`/command-gen support; state
  it opaquely, mirroring `genCmd_complete`'s `hNameReach`/`hExprComplete`).
- `block`: IH on body → `block_mem`. Output context is input `C,ctx` (lexical).
- `ite_det`/`ite_nondet`: `hExprComplete` for the `.bool` cond (det case) + IH on both
  branches → `ite_det_mem`/`ite_nondet_mem`.
- `loop`: guard via a `genCondOrNondet` reachability lemma (prove
  `genCondOrNondet_complete`: `.det`-of-reachable-bool and `.nondet` are both in
  support — trivial `pick`/`map` inversion), measure via `genOptMeasure_complete`,
  invariants via `genInvariants_complete` (each `.2` a reachable bool, `len ≤ depth`),
  body via IH → `loop_mem`.
- `funcDecl`: `genFunction_complete` for the witness `func` + `genFuncDeclStmt_mem`.
  ⚠️ **Subtlety:** the generator's decl node is `Function.toPureFuncDecl (genFunction …)`,
  which is *not* an arbitrary well-typed `decl`. Completeness here is only up to the
  generator producing *some* funcDecl with the right witnessed `func` and a
  non-recursive node — state the conclusion about the generator's node, not the
  spec's `decl` (again mirroring how `genCmd_complete` fixes labels/metadata and
  concludes about the generator's chosen values). Add a reachability premise that
  the spec's `decl` is reachable if you want the exact node.
- `typeDecl`: needs a `genTypeConstructor` reachability lemma + that
  `addKnownTypeWithError` succeeds (it does by hypothesis `hwt`). Reconstruct the
  `.ok` branch. `genTypeConstructor_complete`: name reachable via `String.arbitrary`,
  params via `mem_support_listOfMaxLength_iff` (`len ≤ depth` + per-name
  `String.arbitrary`) — same shape as `genFunction_complete`'s typeArgs.
- `nil`/`cons` (`genStmts`): `genStmts_nil_mem` / `genStmts_cons_mem` + Step-A
  monotonicity to align the head's fuel with the tail's.

**Helper lemmas still to write** (all straightforward `pick`/`map`/`listOfMaxLength`
inversions, mirror `genOptExpr_complete` in `FunctionHasTypeAGen.lean`):
`genCondOrNondet_complete`, `genOptMeasure_complete`, `genInvariants_complete`,
`genTypeConstructor_complete`.

**Reachability-hypothesis bundle.** Package the opaque premises
(`hExprComplete : GenLExprComplete …`, function/cmd/call/decl/typeconstructor
reachability) in a `GenStmtCompleteEnv`-style structure, mirroring the explicit
hypothesis lists of `genCmd_complete` / `genFunction_complete`. Keep the
`GenLExprComplete` predicate as-is.

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
