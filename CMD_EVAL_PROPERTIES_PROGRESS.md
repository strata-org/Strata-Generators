# Progress: Command-evaluation Tyche properties

## ✅ DONE — properties #2 and #6 are implemented, build, and pass

Both properties are now wired into **both** harnesses (Plausible `test-lexpr` and
Tyche `tyche-viz`), sharing decidable helpers in
`StrataGenerators/CmdHasTypeAGen/TestSupport.lean`.

**Shared helpers added to `TestSupport.lean`:**
- `envFromVarCtxWellTyped` — seeds the store with annotated `fvar`s (`(x : τ)`)
  instead of `intConst 0`, so the *starting* store is well-typed. (Needed because
  the existing `envFromVarCtx` seeds every var as `intConst 0` regardless of type,
  which would make #2 fail spuriously on untouched non-`int` bindings.)
- `storeWellTyped` — every store binding typechecks at its declared type.
- `checkStoreTypePreservation` (#2) — run cmd on well-typed store; if no error,
  store stays well-typed; errored run = vacuous pass.
- `checkEvalRunAgreement` (#6) — **refinement** form: if concrete `Cmd.run`
  succeeds, symbolic `Cmd.eval` also succeeds with the *same* store.
- `cmdConditionKind` — classifies assert/assume/cover condition as
  `true`/`false`/`non-concrete`/`n/a` (a Tyche feature for #6).

**Plausible (`PlausibleTestMain.lean`):** added `prop_cmd_store_type_preservation`
and `prop_cmd_eval_run_agreement` + their `checkProperty` calls. Both **PASS**
at 2000 trials.

**Tyche (`TycheMain.lean`):** added Panel 4 (`CmdStoreTypePreservationResult`,
"genCmd: store type preservation under eval") and Panel 5
(`CmdEvalRunAgreementResult`, "genCmd: symbolic/concrete eval agreement", with a
`condition_kind` feature). Regenerated `tyche_output.jsonl`: 1000/1000 passed each.
The agreement panel's `condition_kind` spans all divergence cases (false 228,
non-concrete 152, true 212, n/a 408), confirming the refinement is genuinely
exercised on the stuck-concrete branches.

### Important correction vs. the original design below

The doc originally proposed comparing `run.error.isNone == eval.error.isNone`
(conditioned on a concrete bool). **That equivalence is false for `assume false`:**
concrete `Cmd.run` errors but symbolic `Cmd.eval` adds a path condition (no error).
The implemented property states the **refinement** (`run` succeeds ⟹ `eval`
succeeds + same store), which is always true and still meaningful — see
`checkEvalRunAgreement` for the full rationale.

### Two failing properties are PRE-EXISTING and unrelated
`progress (closed)` and `resolve after erase` fail by design (documented as
known-falsifiable in source comments). My two new properties are the last two
lines and both pass.

---

## Original design notes (kept for reference)

Status as of the previous session. (Now superseded — see the DONE section above.)

## What's already done (committed-adjacent, in working tree)

These are unrelated to #2/#6 but are uncommitted changes in `TycheMain.lean`:

1. **Reverted** the `expr_x_type` mosaic feature (it made the mosaic worse).
2. **Added** a dedicated `"Distribution of term_kind"` property — single nominal
   feature `term_kind`, renders as a flat bar chart instead of a mosaic.
   - `TermKind` struct + `TycheSample` instance
   - `genTermKind` wrapper
   - `Tyche.run` call in `main` appending to the main JSONL file
3. **Made `exprKind` exhaustive over `LConst`**: replaced the catch-all `"const"`
   label with explicit `strConst` / `realConst` / `bitvecConst` (previously
   `boolConst`/`intConst` were explicit and everything else was `"const"`).

`tyche_output.jsonl` was regenerated. No git commit was made (per the
"only commit when asked" preference).

## The two properties to add (NOT yet implemented)

### Property #2 — Store type preservation

> After running a command, every variable in the resulting store still maps to
> an expression that typechecks at its declared type — i.e. evaluation keeps the
> store well-typed.

This is the command-level analogue of the existing expression-level
"Type preservation under eval" panel.

**How to decide it:**
- Run the command concretely: `Cmd.run σ c` where `σ : Core.Env`.
- Enumerate the store entries from the resulting env's
  `exprEnv.state` (a `Scopes`, i.e. `Maps CoreIdent (Option LMonoTy × LExpr ...)`).
  - `Maps.toSingleMap : Maps α β → Map α β` (it's just `.flatten`) flattens all
    scopes into one assoc list. Entry shape: `(CoreIdent, (Option LMonoTy, Expr))`.
  - Alternatively `Maps.values` / `Maps.keys`.
- For each `(name, (some τ, e))`: check `LExpr.typeCheck (T := LExprParams') [] e == some τ`.
  - Entries with `none` declared type: treat as vacuous pass (or check
    `(typeCheck [] e).isSome`).
- The property is the conjunction (`List.all`) over store entries, **only when
  `Cmd.run` produced no error** (`env.error.isNone`). When `Cmd.run` errored,
  the run is a vacuous pass (the command never produced a new store) — this is
  the standard way to sidestep the invalid "no errors" framing.

**Caveat:** `cover` is unsupported in `Cmd.run` (always yields a `Misc` error).
So a concrete-execution panel will treat every `cover` as a vacuous pass.
That's fine but worth a comment, OR exclude `cover` from this panel.

### Property #6 — Symbolic / concrete agreement

> When `assert`/`assume`'s condition reduces to a concrete boolean, the symbolic
> evaluator (`Cmd.eval`) and the concrete executor (`Cmd.run`) agree on the
> outcome.

A differential-testing panel between the two evaluators.

**How to decide it:**
- `Cmd.eval σ c : Cmd P × S` (symbolic simulation) vs `Cmd.run σ c : S` (concrete).
- Their behaviors deliberately differ on the *non-concrete* path:
  - `assert e` where `denoteBool (eval e) = none`: `Cmd.eval` *defers* a proof
    obligation (no error); `Cmd.run` *errors* (`Misc "... did not reduce to bool"`).
  - `assert false` with **non-empty** assumptions: `Cmd.eval` defers; `Cmd.run`
    errors with `AssertFail`.
  - `assume false`: `Cmd.eval` adds a path condition + warning (no error);
    `Cmd.run` errors (`Misc "assume ... is false"`).
  - `cover`: `Cmd.eval` defers an obligation; `Cmd.run` errors (unsupported).
- **They agree on the concrete-bool path:**
  - `assert e` with `denoteBool (eval e) = some true`: both succeed (no error).
  - `assert e` with `some false` AND empty assumptions: both error `AssertFail`.
  - `assume e` with `some true`: both succeed.
- So the property should be **conditioned on the condition reducing to a concrete
  boolean** (and, for `assert`, on the assumptions being empty — which they are
  for freshly generated single commands run from an empty/init-only context).
  Restricting to `assert`/`assume` whose evaluated condition `denoteBool` is
  `some _` gives a clean, true differential property:
  `(Cmd.run σ c).error.isNone == ((Cmd.eval σ c).2.error.isNone)`
  — or more precisely compare the *outcome classification* (ok vs AssertFail).
- For non-assert/assume commands (`init`/`set`), `eval` and `run` have identical
  store-update logic, so they should always agree (no error in both, same store).

**Practical generation note:** the existing `genCmdFromRandomCtx` helper
(in `TycheMain.lean`) generates a single command from a random-size init-only
context. Reuse it. Build the starting `Core.Env` from the `VarCtx` via
`envFromVarCtx` (already defined in `CmdHasTypeAGen/TestSupport.lean`, fills each
var with `intConst 0`).

## Key source facts (verified this session)

### Evaluation entry points
- `Imperative.Cmd.run {P S} [BEq P.Ident] [EvalContext P S] (σ : S) (c : Cmd P) : S`
  — concrete execution. File: `.lake/packages/Strata/Strata/DL/Imperative/CmdEval.lean:123`.
- `Imperative.Cmd.eval ... (σ : S) (c : Cmd P) : Cmd P × S`
  — symbolic simulation. Same file, line 20.
- `Imperative.Cmds.run` / `Cmds.eval` — list versions.
- Both short-circuit if `EC.lookupError σ` is already `some _`.

### The `EvalContext` instance for Core
`Core.CmdEval` provides the instance (`.lake/.../Core/CmdEval.lean:129`):
- `eval E e = LExpr.eval E.exprEnv.config.fuel E.exprEnv e`
- `denoteBool e = Lambda.LExpr.denoteBool e` → `Option Bool`
- `lookup E v` → `Option Expression.TypedExpr` (looks up `exprEnv.state`)
- `update`, `updateError`, etc.

### `Core.Env` (`.lake/.../Core/Env.lean:147`)
```
structure Env where
  error : Option (Imperative.EvalError Expression)
  program : Program
  substMap : SubstMap
  exprEnv : Expression.EvalEnv      -- = Lambda.LState ⟨Unit, Unit⟩
  datatypes : ...
  distinct : ...
  pathConditions : Imperative.PathConditions Expression
  warnings : List (Imperative.EvalWarning Expression)
  deferred : Imperative.ProofObligations Expression
  pathCap : Option Nat
```
- `Env.init` / `(∅ : Env)` for empty envs.
- Store lives in `E.exprEnv.state : Scopes CoreLParams`.

### Store representation
- `Scopes T := Maps T.Identifier (Option LMonoTy × LExpr T.mono)`
  (`.lake/.../Lambda/Scopes.lean:86`).
- `Maps α β` is a list of `Map α β` (scope stack).
- `Maps.toSingleMap = .flatten` (`.lake/.../Util/Maps.lean:91`).
- `Maps.keys`, `Maps.values` available.

### `EvalError` constructors (`.lake/.../Imperative/EvalError.lean:21`)
`InitVarExists`, `AssignVarNotExists`, `HavocVarNotExists`, `AssertFail label b`,
`LabelNotExists`, `Misc f`, `OutOfFuel`.

### `LExpr.typeCheck` (`.lake/.../Lambda/Denote/LExprAnnotated.lean:28`)
`LExpr.typeCheck {T} (ctx : List LMonoTy) : LExpr T.mono → Option LMonoTy`.
- Annotated `fvar`/`op` typecheck off their annotation; unannotated → `none`.
- Already used in `checkExprTypechecks` with `(T := LExprParams')`.

### Type aliases
- `LExprParams' : LExprParams := ⟨Unit, Unit⟩` (`StrataGenerators/HasTypeAGen/Core.lean:15`)
- `LExpr' := LExpr LExprParamsT'`, `LExprParamsT' := LExprParams.mono LExprParams'`.
- Core's `Expression.Expr = Lambda.LExpr ⟨⟨Unit, Unit⟩, LMonoTy⟩` — same shape as
  `LExpr'`, so `typeCheck (T := LExprParams')` applies to store expressions.
  (The existing `checkExprTypechecks` already relies on this equivalence.)

### Generators / helpers to reuse (all in scope in `TycheMain.lean`)
- `genCmdFromRandomCtx (depth) : IO (Cmd Expression × VarCtx × VarCtx × Nat)`
  — defined in `TycheMain.lean` (~line 361). Generates a single command from a
  random init-only context. Returns `(cmd, baseCtx, ctx', d)`.
- `envFromVarCtx (ctx : VarCtx) : Core.Env`
  — `CmdHasTypeAGen/TestSupport.lean:78`. Seeds store with `intConst 0` per var.
- `cmdKind (cmd : Cmd Expression) : String` — already defined for the feature.
- Pattern to follow for adding a panel: copy one of the existing command panels
  (`CmdInitFreshResult` / `genAndCheckInitFresh` + its `Tyche.run` block in
  `main`). Each panel = a result struct + `TycheSample` instance + a generator
  wrapper + a `Tyche.run`-then-append block in `main`.

## Suggested feature sets for the two new panels

**#2 panel (`CmdStoreTypePreservationResult`):**
- `status`: passed iff (errored run → vacuous) or (all store entries well-typed)
- features: `cmd_kind`, `store_size` (ordinal), `ran_without_error` (nominal yes/no),
  `ctx_size`, `generator_size`.

**#6 panel (`CmdEvalRunAgreementResult`):**
- only meaningful for `assert`/`assume` with concrete-bool condition; for other
  kinds, both agree trivially (still a pass).
- `status`: passed iff symbolic and concrete outcomes agree (per the
  classification above).
- features: `cmd_kind`, `condition_reduced` (nominal: `true`/`false`/`non-concrete`),
  `agreement` (nominal yes/no), `generator_size`.

## Open questions / things to double check before finalizing
1. Confirm `Cmd.eval`/`Cmd.run` are exported/public from the imported modules
   (`Strata.DL.Imperative.CmdEval` is imported transitively via
   `CmdHasTypeAGen/TestSupport.lean`). May need an explicit import.
2. Confirm `Maps.toSingleMap` is accessible (it's `@[expose]`, should be fine).
3. For #6, decide whether to compare `error.isNone` booleans or full error
   classification. Comparing `isNone` is simpler and sufficient for a slide.
4. `denoteBool` needs the *evaluated* condition: call
   `CmdEval.eval σ e` first, then `denoteBool`. Note `assert`/`assume` store the
   condition inside the cmd constructor — extract it via a match on `cmd`.
