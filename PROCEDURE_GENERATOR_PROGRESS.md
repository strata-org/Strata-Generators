# Procedure Generator — Progress & Handoff

_Worktree: `/Users/ernestng/Documents/strata-generators-proc` (branch off `main`).
Last updated: 2026-07-28._

## Task

Derive a generator for random well-typed Strata Core **procedures** from the typing
relation in `~/Documents/Strata/Strata/Languages/Core/ProcedureTypeSpec.lean`, and
prove it **sound** and **complete** with respect to `ProcHasTypeA`. Reuse the existing
expression/command/statement/function generators and their proofs. **Minimize the
number of side-conditions in the theorem statements** — in particular
`genProcedure_sound` must be **side-condition-free**.

Follow-on feature request (all landed): the generator should also produce non-empty
`typeArgs`, `inputs`, and `preconditions`/`postconditions`.

## Status: procedure *declaration* generator COMPLETE (with in-out params); call
## generator (`genCallStmt`) IN PROGRESS

The `ProcedureHasTypeAGen` module builds (`lake build`, exit 0). Both top-level theorems are
axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only — the standard Lean/Mathlib
axioms, verified with `lean_verify`).

- `StrataGenerators.Procedure.genProcedure_sound` — **side-condition-free.** Signature is
  just `(P) (octx) (size len) (proc) (hproc : proc ∈ support (genProcedure octx size len))`
  ⟹ `ProcHasTypeA P LContext.default default proc`.
- `StrataGenerators.Procedure.genProcedure_complete` — reachability hypotheses for each
  generated field (name / typeArgs / three signature blocks M/I/O / pre / post / body), plus
  the three-block decomposition (`hInputsEq : inputs = M ++ I`, `hOutputsEq : outputs =
  M ++ O`) and the two completeness-only disjointness side-conditions (`hIdisjM`, `hOdisjMI`)
  witnessing that the generator's `disjointInputs` filters reproduce `I`/`O` unchanged
  (idempotence, via `disjointInputs_eq_self`). These side-conditions are on *completeness
  only*; soundness carries none.

### In-out parameters (three-block signature layout — DONE)

`genProcedure` now emits **in-out parameters** by decomposing each signature into three
mutually key-disjoint blocks, front-aligned so call-site argument positions line up:

- `M` (in-out) — parameters in *both* input and output roles (`getInoutParams = M`);
- `I` (input-only) — `disjointInputs rawInputOnly M`;
- `O` (output-only) — `disjointInputs rawOutputOnly (M ++ I)`.

`inputs := M ++ I`, `outputs := M ++ O`. The threaded body invariant is the **`Functional`**
predicate (not `Nodup`): the in-out block `M` appears in both signatures bound to the *same*
type, so the seed `M ++ I ++ (M ++ O) ++ oldVars M` has duplicate keys that agree on values;
`old`-keys (`"old " ++ name`, space-containing) never collide with space-free generated
names. Body scope mirrors the declarative `procBodyContext` (`inputScope ++ outputScope ++
oldScope`), identified via `procBodyContext_inout`; immutable names are
`keys (M ++ I) ++ keys (oldVars M)`, so the body may read inputs and `old` bindings but only
assign to the output-only names `O`.

### Remaining: call-statement generator (`genCallStmt`)

Emit procedure *calls* (`CmdExt.call pname args md` with `List CallArg`), threading a
**procedure-signature context** (proc names + type signatures) through the statement
generators. Per the AST lowering: in-out args are same-named fvars (`.inoutArg id`,
satisfying `areInoutArgsValid`), input args are exprs (`.inArg e`), output args are ids
(`.outArg id`). No change to `genProcedure` (the declaration generator) is needed — its
three-block M/I/O layout already matches what a call site consumes.

## What the generator produces (`ProcedureHasTypeAGen/Core.lean`, `genProcedure`)

- **`typeArgs`** — a `Nodup` list of type-variable names via `genTypeArgs size` (exactly
  as `genFunction`). Threaded into `genInputs typeArgs` (input/output types drawn over
  these tyvars ⟹ `noUndeclaredVars`) and into the body `tvars`.
- **three signature blocks** `M`/`I`/`O`, each a `Nodup`-keyed signature via
  `genInputs typeArgs size`, made mutually key-disjoint by `disjointInputs` filtering
  (`I := disjointInputs rawInputOnly M`, `O := disjointInputs rawOutputOnly (M ++ I)`).
  Front-aligned: `inputs := M ++ I`, `outputs := M ++ O`, so `getInoutParams = M` — the
  in-out block. This is what makes the declarative body context `procBodyContext` (whose
  body scope is `inputScope ++ outputScope ++ oldScope`) align with the seed the statement
  generator threads, via `procBodyContext_inout`.
- **`preconditions` / `postconditions`** — labeled `bool` expressions via `genChecks`
  (labels from `genNameList`, each expr from `genLExpr … .bool`, `attr`/`md` at defaults).
- **`body`** — a `.structured` list of ≤ `len` statements via `genStmts`, **seeded with
  `M ++ I ++ (M ++ O) ++ oldVars M` as the initial `VarCtx` and
  `keys (M ++ I) ++ keys (oldVars M)` as the immutable names `immutableVars`.** The body may
  freely *read* the inputs and the `old` bindings (in scope for freshness + expression typing)
  but can only *assign* to the output-only names `O` (`set` targets are drawn from the mutable
  sub-context, which excludes the immutable inputs and `old` bindings).

Body + contract expressions are generated at empty operator/fvar/label contexts and
`LContext.default`, matching the empty-context instantiation both test harnesses use.

## Key design idea: the mutable/immutable split (Phase B)

Non-empty inputs were the hard part. The tension:

- `init x` **freshness** is checked against `procBodyContext` (which binds the inputs), so
  the threaded immutable `VarCtx` **must contain** the inputs.
- `set` targets are drawn from the context, but modifying an input would violate
  `ProcHasType'.modRights`, so the **mutable** targets **must exclude** the inputs.
- Inputs cannot be smuggled into `fctx` (the free-var context): the soundness chain relies
  on `fctx = []` so body expressions are closed (`genLExpr_no_fvars`);
  `FreshNamesDisjointFromExprs` is provably false for non-empty `fctx`.

Resolution: thread a new **`immutableVars : List (Identifier Unit)`** parameter through the
shared generators. It sits **before `ctx`** in the signatures of `genCmd`, `genCmds`,
`genStmt`, `genStmts` (`CmdHasTypeAGen/Core.lean`, `StmtHasTypeAGen/Core.lean`). `set`
draws from `elements (ctx.writable immutableVars)` where
`VarCtx.writable immutableVars ctx := ctx.filter (fun p => !immutableVars.contains p.1)`.

The bridge lemma is **`mem_writable_keys_iff`** (`ProcedureHasTypeAGen/MutableVars.lean`):
a mutable key = a context key that is not a immutable name. At the top level,
`(inputs ++ outputs).writable inputs.keys` drops exactly the input keys, leaving
`outputs.keys` — precisely the `modRights` obligation, with **no disjointness side-condition
needed** for that part.

## File map (all under `StrataGenerators/`)

- `ProcedureHasTypeAGen/Core.lean` — `genProcedure`, `disjointInputs`, `genChecks`.
- `ProcedureHasTypeAGen/Support.lean` — `procToTCtx` (single-scope), `procToTCtx_corr`
  (unconditional, `find?`-based `VarCtxCorresponds`), `procStmtEnv` (concrete
  `GenStmtSoundEnv`).
- `ProcedureHasTypeAGen/MutableVars.lean` — mutual `genStmt_mutableVars` / `genStmts_mutableVars`
  + per-command `genCmd_mutableVars` (every modified var ∈ `ctx.writable immutableVars` keys ++
  definedVars), `mem_writable_keys_iff`, and the membership-monotonicity helpers
  (`mem_append_grow_*`, `trans_step`, `ite_combine`).
- `ProcedureHasTypeAGen.lean` — the two top-level theorems + the `genChecks_*` reachability
  lemmas + the `disjointInputs_*` filter facts + `procBodyContext_default`,
  `getInoutParams_nil_of_disjoint`, `Map_keys_eq_ListMap_keys`, `mem_writable_append_keys`.
- `CmdHasTypeAGen/Core.lean`, `StmtHasTypeAGen/Core.lean`, `StmtHasTypeAGen.lean`,
  `CmdHasTypeAGen.lean`, `CmdHasTypeAGenSound.lean` — carry the `immutableVars` param through
  generators, support lemmas, `StmtReachable`/`StmtsReachable`, `genStmt(s)_complete`.
- `CmdHasTypeAGen/TestSupport.lean`, `TestScaffold.lean`, `TycheViz.lean` — external
  callers, updated to pass `[]` for `immutableVars` (no immutable names in standalone
  command/statement testing).

## Lean gotchas discovered (save the next agent time)

- **`set` tactic is unavailable** — Mathlib is not imported in this worktree. Use direct
  term references, not `set … with h` abbreviations.
- **`ListMap α β := List (α × β)` is non-reducible.** Theorem *signatures* using
  `∀ p ∈ (ins : ListMap …), … p.1` fail to elaborate ("failed to synthesize Membership",
  "Invalid projection") even with a `List` ascription in binder position. **Workaround:**
  state hypotheses in **filter-equation form** — `(ins.filter fun p => …) = []` instead of
  `∀ p ∈ ins, …`.
- **`ListMap` has its own `instHAppendListMap` (`hAppend := List.append`)**, distinct from
  `List.instAppend`. `Map.keys_append`'s LHS pattern `(?m₁ ++ ?m₂).keys` does **not** unify
  with a `ListMap` `++`. Bridge it with a `have hkey : Map.keys (a ++ b) = ListMap.keys a
  ++ ListMap.keys b := by rw [← Map_keys_eq_ListMap_keys, …]; exact Map.keys_append _ _`.
- **`lean_multi_attempt` gives false positives on stale imports.** After editing, run
  `lean_build` (rebuilds + restarts the LSP) before trusting `lean_goal`/`lean_multi_attempt`.
  `lean_run_code` (isolated snippets) is always reliable.

## What remains / possible follow-ups

The task as stated is **done**. Optional polish a future agent might consider:

1. **Remove the completeness side-condition `hInDisjoint`.** It is genuine (the generator's
   filter is idempotent on already-disjoint inputs) but could perhaps be replaced by
   deriving disjointness from a `Nodup`/well-formedness fact if one is available on
   reachable procedures — low priority; soundness is already clean.
2. **Commit & open a PR.** Nothing has been committed on this worktree yet beyond the
   "First pass at procedure generator" commit (`3ab7bb4`); the Phase B changes are all
   uncommitted working-tree edits. Per the standing constraint, **do not commit unless the
   user asks.** `git status` currently shows 11 modified files (listed in the file map).
3. Extend the smoke test / harness properties (`TestScaffold.lean`, `TycheViz.lean`) to
   exercise procedures with non-empty inputs specifically, if broader test coverage is
   wanted.
