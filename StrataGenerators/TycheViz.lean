import StrataGenerators.Tyche
import StrataGenerators.Properties
import StrataGenerators.RetryGen
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.Roundtrip
import StrataGenerators.StmtHasTypeAGen.TestSupport
-- Supplies `minimizeProcsCounterexample`, so the procedure panels can report the
-- minimal well-typed counterexample rather than the raw generated one.
import StrataGenerators.ProcedureHasTypeAGen.Shrink
import Basalt.IO
-- `Basalt.PlausibleGen` supplies the `[Gen Plausible.Gen]` instance used by the
-- procedure-list panels, which run the backtracking `genProcedure` generator via
-- `Plausible.Gen.run` (the direct `G := IO` path is unreliable for procedures).
import Basalt.PlausibleGen
import Strata.DL.Lambda.LExprT
-- Imports for Function.typeCheck property (typeCheck_annotated_sound)
import Strata.Languages.Core.FunctionType
import Strata.DL.Lambda.Denote.LExprAnnotated
-- Imports for pretty-print/parse round-trip property
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda RandomChoice ArbNat Tyche Std Core Imperative
open Strata Strata.CoreDDM
open StrataDDM (initDialect)

/-!
# Tyche Visualization Panels

Generates samples from the `HasTypeA` / command / function / statement generators
and writes them in Tyche JSONL format for visualization.

This module holds every Tyche panel (feature extractors, `TycheSample` instances,
`IO` generator wrappers, and `runTychePanels`). It is *not* an executable root: the
merged test driver in `TestMain.lean` calls `runTychePanels` after the LSpec suite,
gated behind a CLI flag (Tyche visualization is on by default).

All property *check* logic (pass/fail verdicts and the helper contexts behind them)
is shared with the Plausible harness via the `*.TestSupport` modules — this file
only adds the Tyche-specific visualization scaffolding (feature breakdowns, sample
representations, and rejection-sampling for counterexample-dense panels).
-/

-- ── Feature extraction ────────────────────────────────────────────────

/-- Compute the depth (nesting level) of an LExpr. -/
def exprDepth : LExpr' → Nat
  | .abs _ _ _ body => exprDepth body + 1
  | .app _ fn arg => max (exprDepth fn) (exprDepth arg) + 1
  | .ite _ c t e => max (exprDepth c) (max (exprDepth t) (exprDepth e)) + 1
  | .eq _ e₁ e₂ => max (exprDepth e₁) (exprDepth e₂) + 1
  | .quant _ _ _ _ tr body => max (exprDepth tr) (exprDepth body) + 1
  | _ => 0

/-- Compute the size (number of nodes) of an LExpr (delegates to `LExpr.size` from Strata). -/
def exprSize (e : LExpr') : Nat := LExpr.size LExprParamsT' e

/-- Classify the top-level expression constructor. -/
def exprKind : LExpr' → String
  | .bvar _ _ => "bvar"
  | .fvar _ _ _ => "fvar"
  | .op _ _ _ => "op"
  | .abs _ _ _ _ => "abs"
  | .app _ _ _ => "app"
  | .ite _ _ _ _ => "ite"
  | .eq _ _ _ => "eq"
  | .const _ (.boolConst _) => "boolConst"
  | .const _ (.intConst _) => "intConst"
  | .const _ (.strConst _) => "strConst"
  | .const _ (.realConst _) => "realConst"
  | .const _ (.bitvecConst _ _) => "bitvecConst"
  | .quant _ _ _ _ _ _ => "quant"

/-- Classify the top-level type constructor. -/
def typeKind : LMonoTy → String
  | .bool => "bool"
  | .int => "int"
  | .arrow _ _ => "arrow"
  | .ftvar _ => "ftvar"
  | .bitvec _ => "bitvec"
  | .tcons _ _ => "tcons"

-- ── Type preservation property ────────────────────────────────────────

/-- Result of generating, evaluating, and re-typechecking. -/
structure EvalResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  evaledTy : Option LMonoTy
  exprIsValue : Bool
  madeProgress : Bool
  generatorSize : Nat

instance : Tyche.TycheSample EvalResult where
  toSample r :=
    -- The pass/fail verdict is the shared `checkPreservation`; `evaledTy` is kept
    -- only to display the re-inferred type in the sample representation.
    let preserved := checkPreservation r.expr r.expectedTy
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status := if preserved then .passed else .failed
      features := [
        ("preservation", .nominal (if preserved then "pass" else "fail")),
        ("is_value", .nominal (if r.exprIsValue then "value" else "non-value")),
        ("made_progress", .nominal (if r.madeProgress then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

-- ── Generator wrappers ────────────────────────────────────────────────
-- Each wrapper varies the depth parameter uniformly over [1, 5] so that
-- Tyche visualizations cover the full range of generator behavior, not
-- just a single fixed depth.

/-- Randomly choose a depth between 1 and `maxDepth` (inclusive). -/
def randomDepth (maxDepth : Nat := 5) : IO Nat := do
  let r ← IO.rand 1 maxDepth
  return r

/-- Generate a closed expression, evaluate it, and check type preservation.
    Uses empty fctx since preservation is stated for the empty context. -/
def genAndEval (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] coreMonoOps corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  let evaledTy := LExpr.typeCheck (T := LExprParams') [] evaled
  return ⟨expr, ty, evaled, evaledTy, isValue expr, !(expr == evaled), d⟩

-- ── Eval progress property ───────────────────────────────────────────

/-- Result of checking whether `LExpr.eval` makes progress on a generated term. -/
structure EvalProgressResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  generatorSize : Nat

instance : Tyche.TycheSample EvalProgressResult where
  toSample r :=
    -- Shared `checkProgress` decides the verdict; the `made_progress` /
    -- `input_is_value` features break down *why* it passed.
    let madeProgress := !(r.expr == r.evaled)
    let inputIsValue := isValue r.expr
    let status := if checkProgress r.expr then Tyche.Status.passed else .failed
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status
      features := [
        ("made_progress", .nominal (if madeProgress then "yes" else "no")),
        ("input_is_value", .nominal (if inputIsValue then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_depth", .ordinal (exprDepth r.expr)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a closed expression and check whether eval makes progress (or
    the input is already a value). Uses empty fctx since progress is stated
    for the empty context. -/
def genAndCheckProgress (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalProgressResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] coreMonoOps corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, d⟩

-- ── Fvar preservation property ───────────────────────────────────────

structure FvarPreservationResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  genDepth : Nat

instance : Tyche.TycheSample FvarPreservationResult where
  toSample r :=
    let fvarsPreserved := checkFvarsPreserved r.expr
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status := if fvarsPreserved then .passed else .failed
      features := [
        ("fvars_preserved", .nominal (if fvarsPreserved then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("gen_depth", .ordinal r.genDepth)
      ] }

def genAndCheckFvarPreservation (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO FvarPreservationResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) defaultFCtx coreMonoOps corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, d⟩

-- ── Resolve after erasure property ──────────────────────────────────
-- `resolveLContext`, `intBoolOpCtx`, `eraseAllTypes`, and `isInstanceOf` are the
-- shared definitions from `HasTypeAGen.TestSupport` — the same ones the Plausible
-- `checkResolveAfterErase` uses, so the two harnesses score this property
-- identically.

/-- Whether the expression contains a quantifier (`∀`/`∃`) anywhere. Every known
    counterexample to the resolve-after-erase property contains one: after the
    binder annotation is erased, `LExpr.resolve` gives the bound variable a fresh
    type variable and then rejects the quantifier with a *syntactic* `≠ bool`
    check on the body instead of unifying it with `bool`. -/
private def containsQuant : LExpr' → Bool
  | .quant _ _ _ _ _ _ => true
  | .abs _ _ _ b => containsQuant b
  | .app _ a b => containsQuant a || containsQuant b
  | .ite _ c t e => containsQuant c || containsQuant t || containsQuant e
  | .eq _ a b => containsQuant a || containsQuant b
  | _ => false

structure ResolveAfterEraseResult where
  expr : LExpr'
  expectedTy : LMonoTy
  resolvedTy : Option LMonoTy
  generatorSize : Nat

instance : Tyche.TycheSample ResolveAfterEraseResult where
  toSample r :=
    -- Counterexample-focused scoring: a sample PASSES only when `resolve`
    -- succeeds *and* infers a type the generation type is an instance of.
    -- A `resolve` *failure* is scored as a FAIL (a counterexample) rather than
    -- a vacuous pass, so these cases surface in the Tyche panel. The
    -- `failure_mode` feature distinguishes the two kinds of counterexample.
    let failureMode := match r.resolvedTy with
      | some inferred => if isInstanceOf r.expectedTy inferred then "none" else "wrong_type"
      | none => "resolve_failed"
    let passed := failureMode == "none"
    let general := match r.resolvedTy with
      | some inferred => !(inferred == r.expectedTy)
      | none => false
    { representation := match r.resolvedTy with
        | some inferred => s!"{ppExpr r.expr}, expected = {ppType r.expectedTy}, inferred = {ppType inferred}"
        | none => s!"{ppExpr r.expr} : {ppType r.expectedTy} (LExpr.resolve failed to infer type)"
      status := if passed then .passed else .failed
      features := [
        ("resolve_result", .nominal (if passed then "pass" else "fail")),
        -- Which kind of counterexample: `resolve_failed` (resolve errored) vs
        -- `wrong_type` (resolve succeeded but inferred a non-instance type) vs
        -- `none` (passing sample).
        ("failure_mode", .nominal failureMode),
        -- Does the counterexample contain a quantifier? (Expected: every failure.)
        ("has_quantifier", .nominal (if containsQuant r.expr then "yes" else "no")),
        ("inferred_more_general", .nominal (if general then "yes" else "no")),
        ("resolve_succeeded", .nominal (if r.resolvedTy.isSome then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("expr_depth", .ordinal (exprDepth r.expr)),
        ("expr_size", .ordinal (exprSize r.expr)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate one expression, erase its type annotations, and re-infer with
    `LExpr.resolve`. The `resolvedTy` is `none` when `resolve` errors. -/
def genAndCheckResolveAfterErase (depth : Nat := 0) : IO ResolveAfterEraseResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] intBoolOpCtx [] tvars [] d ty
  let erased := eraseAllTypes expr
  let resolvedTy := match LExpr.resolve resolveLContext Lambda.TEnv.default erased with
    | .ok (resolved, _) => some resolved.toLMonoTy
    | .error _ => none
  return ⟨expr, ty, resolvedTy, d⟩

/-- Whether a result is a counterexample to the resolve-after-erase property:
    either `resolve` failed, or it inferred a type the generation type is not an
    instance of. -/
private def isResolveCounterexample (r : ResolveAfterEraseResult) : Bool :=
  match r.resolvedTy with
  | some inferred => !(isInstanceOf r.expectedTy inferred)
  | none => true

/-- Search for a *counterexample* to the resolve-after-erase property, so the
    Tyche panel is densely populated with failing cases (counterexamples are
    rare — well under 1% of generated terms — so an unbiased panel shows only a
    handful). Retries generation up to `budget` times; if none is found within
    the budget, returns the last sample generated so the run still terminates. -/
partial def genResolveCounterexample (budget : Nat := 4000) : IO ResolveAfterEraseResult := do
  let mut last : Option ResolveAfterEraseResult := none
  for _ in List.range budget do
    let r ← try some <$> genAndCheckResolveAfterErase catch _ => pure none
    match r with
    | some res =>
      if isResolveCounterexample res then return res
      last := some res
    | none => pure ()
  match last with
  | some res => return res
  | none => genAndCheckResolveAfterErase

-- ── Command-level Tyche support ──────────────────────────────────────

/-- Classify the top-level command constructor. -/
def cmdKind (cmd : Cmd Expression) : String :=
  match cmd with
  | .init _ _ (.det _) _ => "init_det"
  | .init _ _ .nondet _ => "init_nondet"
  | .set _ (.det _) _ => "set_det"
  | .set _ .nondet _ => "set_nondet"
  | .assert _ _ _ => "assert"
  | .assume _ _ _ => "assume"
  | .cover _ _ _ => "cover"

/-- Shared helper: generate a command from a random-size context.
    Uses a large `numCmds` (3× desired context size) to compensate for the
    fact that only `init` commands grow the context, while `assert`/`assume`/
    `cover`/`set` leave it unchanged. -/
private def genCmdFromRandomCtx (depth : Nat := 0) : IO (Cmd Expression × VarCtx × VarCtx × Nat) := do
  let d ← if depth == 0 then randomDepth else pure depth
  let tvars : List TyIdentifier := []
  let numCmds ← IO.rand 0 8
  let (_, baseCtx) ← genCmds (G := IO) [] coreMonoOps tvars [] [] d numCmds
  let ⟨cmd, ctx'⟩ ← genCmd (G := IO) [] coreMonoOps tvars [] baseCtx d
  return (cmd, baseCtx, ctx', d)

-- ── Panels 1–4: single-verdict command properties ───────────────────
-- These four properties share an identical sample shape (a command, its context
-- size, and a pass/fail verdict), so one `CmdPropResult` serves them all; the
-- panel title distinguishes them. The check predicate receives both the command
-- and its generating context (`checkInitFreshNotInRhs`/`checkExprTypechecks`
-- ignore the context; the other two use it).

structure CmdPropResult where
  cmd : Cmd Expression
  ctxSize : Nat
  generatorSize : Nat
  passed : Bool

instance : Tyche.TycheSample CmdPropResult where
  toSample r :=
    { representation := ppCmd r.cmd
      status := if r.passed then .passed else .failed
      features := [
        ("cmd_kind", .nominal (cmdKind r.cmd)),
        ("ctx_size", .ordinal r.ctxSize),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a command from a random context and apply a check predicate. -/
def genCmdProp (check : Cmd Expression → VarCtx → Bool) : IO CmdPropResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctxSize := baseCtx.length, generatorSize := d,
           passed := check cmd baseCtx }

-- ── Panel 5: symbolic/concrete eval agreement ────────────────────────

structure CmdEvalRunAgreementResult where
  cmd : Cmd Expression
  ctx : VarCtx
  ctxSize : Nat
  generatorSize : Nat
  passed : Bool

instance : Tyche.TycheSample CmdEvalRunAgreementResult where
  toSample r :=
    { representation := ppCmd r.cmd
      status := if r.passed then .passed else .failed
      features := [
        ("cmd_kind", .nominal (cmdKind r.cmd)),
        -- How the command's condition reduced, which determines whether the
        -- symbolic and concrete evaluators take the same branch.
        ("condition_kind", .nominal (cmdConditionKind r.cmd r.ctx)),
        ("ctx_size", .ordinal r.ctxSize),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckEvalRunAgreement : IO CmdEvalRunAgreementResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctx := baseCtx, ctxSize := baseCtx.length, generatorSize := d,
           passed := checkEvalRunAgreement cmd baseCtx }

-- ── Function-level Tyche support ─────────────────────────────────────

/-- Whether a generated function has a body / a measure, for the panel's
    breakdown (the property is vacuously true when both are absent, so this
    lets us see how often the property is exercised non-trivially). -/
private def funcShape (func : Function) : String :=
  match func.body.isSome, func.measure.isSome with
  | true,  true  => "body+measure"
  | true,  false => "body"
  | false, true  => "measure"
  | false, false => "neither"

structure FunctionFvarsAnnotatedResult where
  func : Function
  /-- The property under test: all fvars in body/measure annotated per the
      context type map. -/
  passed : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionFvarsAnnotatedResult where
  toSample r :=
    { representation := formatFunc r.func
      status := if r.passed then .passed else .failed
      features := [
        ("fvars_annotated", .nominal (if r.passed then "yes" else "no")),
        -- Which optional sub-expressions are present (so we can see how often
        -- the property is checked non-vacuously).
        ("func_shape", .nominal (funcShape r.func)),
        ("has_body", .nominal (if r.func.body.isSome then "yes" else "no")),
        ("has_measure", .nominal (if r.func.measure.isSome then "yes" else "no")),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a `Function` via `genFunction` (against `defaultFCtx`) and check the
    `fvars_annotated_by` property against the matching type map. -/
def genAndCheckFunctionFvarsAnnotated (depth : Nat := 0) : IO FunctionFvarsAnnotatedResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO defaultFCtx coreMonoOps d
  let passed := functionFvarsAnnotatedBy (fctxToTyMap defaultFCtx) func
  return { func, passed, generatorSize := d }

-- ── Function property 1: typeCheck_annotated_sound ─────────────────────
-- Tests the *sorry*'d theorem `Function.typeCheck_annotated_sound`
-- (`Strata/Languages/Core/FunctionTypeSpecSound.lean:31`): when
-- `Function.typeCheck` accepts a generated (spec-well-typed) function, the
-- output satisfies the declarative spec `FuncHasTypeA`. Generated with an
-- *empty* fvar context so bodies are closed (no ambient-context dependency).
-- `funcCheckContext` / `checkFuncHasTypeA` are the shared definitions from
-- `FunctionHasTypeAGen.TestSupport`, so this scores identically to the Plausible
-- `checkTypeCheckAnnotatedSound`.

structure FunctionTypeCheckSoundResult where
  func : Function
  /-- Whether `Function.typeCheck` accepted the function. -/
  accepted : Bool
  /-- When accepted, whether the output satisfies `FuncHasTypeA`. -/
  specHolds : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionTypeCheckSoundResult where
  toSample r :=
    -- A sample "passes" iff soundness is not violated: either typeCheck
    -- rejected (vacuous — soundness untriggered) or it accepted and the spec
    -- holds. A failure is: accepted but spec violated.
    let passed := !r.accepted || r.specHolds
    { representation := formatFunc r.func
      status := if passed then .passed else .failed
      features := [
        ("typecheck_accepted", .nominal (if r.accepted then "yes" else "no")),
        ("spec_holds", .nominal (if r.accepted then (if r.specHolds then "yes" else "no") else "—")),
        ("func_shape", .nominal (funcShape r.func)),
        ("has_body", .nominal (if r.func.body.isSome then "yes" else "no")),
        ("has_measure", .nominal (if r.func.measure.isSome then "yes" else "no")),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a closed function (empty fctx), run `Function.typeCheck`, and record
    whether it was accepted and whether the output satisfies `FuncHasTypeA`. -/
def genAndCheckFunctionTypeCheckSound (depth : Nat := 0) : IO FunctionTypeCheckSoundResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreMonoOps d
  match Function.typeCheck funcCheckContext TEnv.default func with
  | .ok (func', _) =>
    return { func := func', accepted := true, specHolds := checkFuncHasTypeA func', generatorSize := d }
  | .error _ =>
    return { func, accepted := false, specHolds := true, generatorSize := d }

-- ── Function property: typechecker COMPLETENESS ────────────────────────
-- Dual to the soundness panel above. `genFunction` is proven sound, so
-- `Function.typeCheck` should accept every generated function — but it does NOT:
-- the spec permits a measure without a body, the algorithm rejects it. Here a
-- REJECTED function renders as a FAILED mark (the real gap is visible), and the
-- `measure_no_body` feature shows it is the cause. Uses the full-Core-factory
-- predicates from the shared statement module so no operator spuriously fails to
-- resolve. The `[body=…, measure=…]` shape is surfaced explicitly since the
-- pretty-printer omits an absent body/measure.
open StrataGenerators.Stmt.TestSupport in
structure FunctionTypeCheckCompleteResult where
  func : Function
  accepted : Bool
  generatorSize : Nat

open StrataGenerators.Stmt.TestSupport in
instance : Tyche.TycheSample FunctionTypeCheckCompleteResult where
  toSample r :=
    -- Passes iff the typechecker accepted the (spec-well-typed) function. A
    -- rejection is a FAILURE — the genuine completeness gap.
    let measNoBody := funcMeasureWithoutBody r.func
    { representation := s!"[body={r.func.body.isSome}, measure={r.func.measure.isSome}]\n{formatFunc r.func}"
      status := if r.accepted then .passed else .failed
      features := [
        ("typecheck_accepted", .nominal (if r.accepted then "yes" else "no")),
        -- The known gap: rejected because it has a measure but no body.
        ("measure_no_body", .nominal (if measNoBody then "yes" else "no")),
        ("func_shape", .nominal (funcShape r.func)),
        ("has_body", .nominal (if r.func.body.isSome then "yes" else "no")),
        ("has_measure", .nominal (if r.func.measure.isSome then "yes" else "no")),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

open StrataGenerators.Stmt.TestSupport in
/-- Generate a closed function and record whether `Function.typeCheck` accepts it
    (in the full Core ambient context). -/
def genAndCheckFunctionTypeCheckComplete (depth : Nat := 0) : IO FunctionTypeCheckCompleteResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreMonoOps d
  return { func, accepted := checkFunctionTypeCheckerComplete func, generatorSize := d }

-- ── Function property 2: pretty-print / parse round-trip ───────────────
-- Embeds a generated function in a `Program`, formats it via
-- `Core.formatProgram`, re-parses via DDM, re-formats, and compares. A parse
-- failure is scored as a FAILURE: names are legal Core identifiers by
-- construction (`genIdentName`), so unparseable output is a printer/parser bug.
--
-- `formatFuncAsProgram`, `parseCoreProgram`, `parseCoreProgramErr`, the
-- structural shrinker (`shrinkWhile` et al.) and the failure predicates
-- (`failsRoundtrip`, …) are shared with the Plausible harness — see
-- `StrataGenerators.FunctionHasTypeAGen.Roundtrip`.

/-- Extract a short, position-independent "kind" from a parser error message,
    for grouping in the Tyche panel. Strips the `Parse errors:` prefix and the
    `line:col` location so that e.g. every "Map expects 2 arguments" collapses
    into one bucket regardless of where in the input it occurred. -/
private def parseErrorKind (msg : String) : String :=
  -- Drop everything up to and including the last "N:M:" location marker.
  let afterLoc := (msg.splitOn ": ").reverse.headD msg
  let core := afterLoc.trimAscii
  (core.take 45).toString

structure FunctionRoundtripResult where
  func : Function
  /-- Whether the printed function parsed back successfully. -/
  parsed : Bool
  /-- When parsed, whether format→parse→re-format is a fixed point. -/
  roundtripped : Bool
  /-- On parse failure, the parser's diagnostic message (else ""). -/
  parseError : String
  generatorSize : Nat

instance : Tyche.TycheSample FunctionRoundtripResult where
  toSample r :=
    -- Passes iff the printed function parsed back AND round-tripped. A parse
    -- failure is a FAILURE, not vacuous: `genIdentName` produces only legal Core
    -- identifiers by construction, so legal-but-unparseable output is a genuine
    -- printer/parser bug to report.
    let passed := r.parsed && r.roundtripped
    -- Show the exact string the round-trip tested (Strata's `Core.formatProgram`
    -- output), so the panel is a faithful reproducer of any failure.
    { representation := formatFuncAsProgram r.func
      status := if passed then .passed else .failed
      statusReason := r.parseError
      features := [
        ("parsed", .nominal (if r.parsed then "yes" else "no")),
        ("roundtripped", .nominal (if r.parsed then (if r.roundtripped then "yes" else "no") else "—")),
        ("error_kind", .nominal (if r.parsed then "—" else parseErrorKind r.parseError)),
        ("func_shape", .nominal (funcShape r.func)),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Build a `FunctionRoundtripResult` for a specific function. -/
def mkRoundtripResult (func : Function) (d : Nat) : IO FunctionRoundtripResult := do
  let s1 := formatFuncAsProgram func
  match ← parseCoreProgramErr s1 with
  | .ok ast2 =>
    let s2 := (Core.formatProgram ast2).pretty
    return { func, parsed := true, roundtripped := s1 == s2, parseError := "", generatorSize := d }
  | .error e =>
    return { func, parsed := false, roundtripped := false, parseError := e, generatorSize := d }

def genAndCheckFunctionRoundtrip (depth : Nat := 0) : IO FunctionRoundtripResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreMonoOps d
  -- If the function fails to round-trip, shrink it to a minimal witness and
  -- report that instead, so the Tyche `representation` shows the smallest
  -- reproducer (features / status_reason are recomputed on the shrunk func).
  if ← failsRoundtrip func then
    let minF ← shrinkWhile failsRoundtrip 1000 func
    mkRoundtripResult minF d
  else
    mkRoundtripResult func d

-- ── Function property 3: type preservation under eval ──────────────────
-- Corresponds to `Step.type_preserved` / `StepStar.type_preserved` /
-- `eval_denote_sound`. Evaluates a generated function body and checks the
-- result still type-checks at the declared output type. The verdict is the
-- shared `checkFunctionBodyPreservation`.

structure FunctionBodyPreservationResult where
  func : Function
  /-- Whether the function has a body (the property is exercised non-vacuously). -/
  hasBody : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionBodyPreservationResult where
  toSample r :=
    -- Passes iff no body (vacuous) or the body's type is preserved under eval.
    let passed := checkFunctionBodyPreservation r.func
    -- When a body is present, whether eval preserved the output type.
    let preserved := passed
    { representation := formatFunc r.func
      status := if passed then .passed else .failed
      features := [
        ("has_body", .nominal (if r.hasBody then "yes" else "no")),
        ("type_preserved", .nominal (if r.hasBody then (if preserved then "yes" else "no") else "—")),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a closed function, evaluate its body (if any), and check the result
    still type-checks at the declared output type. -/
def genAndCheckFunctionBodyPreservation (depth : Nat := 0) : IO FunctionBodyPreservationResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreMonoOps d
  return { func, hasBody := func.body.isSome, generatorSize := d }

-- ── Function property: special-character identifier round-trip ─────────
-- Isolates one *legal* identifier that contains special (non-alphanumeric)
-- characters (`genQuotedName`: letter/`_`/`$`-initial, then `. ' | \ ? ! @` in
-- the interior) in one syntactic position (function name / type-arg / binder)
-- inside an otherwise-trivial function, so a failure is a minimal reproducer.
-- Every generated name is a legal Core identifier by construction, so a failure
-- is a genuine printer/parser bug, not a generator artifact. `IdentPosition` and
-- `minimalFuncWithName` are the shared definitions from
-- `FunctionHasTypeAGen.TestSupport`.

/-- Character class of the identifier that likely triggered a failure — used as
    the panel's grouping feature so distinct mechanisms surface separately. -/
def identCharClass (name : String) : String :=
  if name.any (· == '.') then "dot"
  else if name.any (· == '|') then "pipe"
  else if name.any (· == '\\') then "backslash"
  else if name.any (· == '\'') then "apostrophe"
  else if name.toList.head?.map (·.isDigit) == some true then "leading-digit"
  else if name.any (fun c => c == '?' || c == '!' || c == '@') then "special"
  else "plain"

structure IdentProbeResult where
  pos : IdentPosition
  name : String
  /-- Whether the printed single-identifier function parsed back. -/
  parsed : Bool
  /-- When parsed, whether format→parse→re-format is a fixed point. -/
  roundtripped : Bool
  /-- On parse failure, the parser's diagnostic message (else ""). -/
  parseError : String
  rendered : String

instance : Tyche.TycheSample IdentProbeResult where
  toSample r :=
    -- Passes iff the identifier parsed back AND round-tripped. A parse failure
    -- is a FAILURE: the name is a legal Core identifier, so unparseable output
    -- is a printer/parser bug.
    let passed := r.parsed && r.roundtripped
    { representation := r.rendered.replace "\n" " "
      status := if passed then .passed else .failed
      statusReason := r.parseError
      features := [
        ("position", .nominal r.pos.label),
        ("char_class", .nominal (identCharClass r.name)),
        ("parsed", .nominal (if r.parsed then "yes" else "no")),
        ("roundtripped", .nominal (if r.parsed then (if r.roundtripped then "yes" else "no") else "—")),
        ("error_kind", .nominal (if r.parsed then "—" else parseErrorKind r.parseError))
      ] }

/-- Draw an adversarial identifier, place it in a random position, and record
    whether that single identifier round-trips. -/
def genAndCheckIdentProbe : IO IdentProbeResult := do
  let name ← genQuotedName (G := IO)
  let posIdx ← IO.rand 0 2
  let pos := match posIdx with
    | 0 => IdentPosition.funcName
    | 1 => IdentPosition.typeArg
    | _ => IdentPosition.binder
  let s1 := formatFuncAsProgram (minimalFuncWithName pos name)
  match ← parseCoreProgramErr s1 with
  | .ok ast2 =>
    let s2 := (Core.formatProgram ast2).pretty
    return { pos, name, parsed := true, roundtripped := s1 == s2, parseError := "", rendered := s1 }
  | .error e =>
    return { pos, name, parsed := false, roundtripped := false, parseError := e, rendered := s1 }

-- ── Statement-level Tyche support ────────────────────────────────────
-- Panels visualizing the six statement-transform / typechecker properties on
-- well-typed statement lists from `genProgramStmts` (proven sound+complete
-- against `StmtsHasTypeA`). The `check*` predicates and measurements are shared
-- with the Plausible harness via `StrataGenerators.StmtHasTypeAGen.TestSupport`.

open StrataGenerators.Stmt.TestSupport

/-- Shared statement-list features for every statement panel: structural
    breakdown (size, kind counts) plus the generator size. -/
private def stmtListFeatures (ss : List Statement) (genSize : Nat) :
    List (String × Tyche.Feature) :=
  [ ("num_stmts", .ordinal ss.length),
    ("ast_size", .ordinal (sizeStmts ss)),
    ("num_loops", .ordinal (countLoopsStmts ss)),
    ("num_exits", .ordinal (countExitStmts ss)),
    ("num_funcDecls", .ordinal (countFuncDeclStmts ss)),
    ("num_typeDecls", .ordinal (countTypeDeclStmts ss)),
    ("has_funcDecl", .nominal (if stmtsHaveFuncDecl ss then "yes" else "no")),
    ("top_kind", .nominal (match ss with | s :: _ => stmtKind s | [] => "empty")),
    ("generator_size", .ordinal genSize) ]

/-- Render a statement list for a Tyche panel using Strata's own formatter (real
    Core concrete syntax), appending a `funcDecl[body=…, measure=…]` summary since
    the CST formatter cannot represent a bodiless `funcDecl` statement (it
    substitutes a dummy body) — exactly the completeness counterexample shape. -/
def stmtRepr (ss : List Statement) : String :=
  let shapes := funcDeclShapesList ss
  let suffix := if shapes.isEmpty then "" else s!"\n-- {" ".intercalate shapes}"
  formatStmts ss ++ suffix

/-- A generated statement list paired with a single property's pass/fail verdict
    and the property name (used as the pass/fail nominal feature). One structure
    serves every boolean statement property; the panel title distinguishes them. -/
structure StmtPropResult where
  stmts : List Statement
  passed : Bool
  genSize : Nat
  /-- Short property tag, surfaced as the primary nominal feature. -/
  tag : String

instance : Tyche.TycheSample StmtPropResult where
  toSample r :=
    { representation := stmtRepr r.stmts
      status := if r.passed then .passed else .failed
      features := (r.tag, .nominal (if r.passed then "pass" else "fail"))
        :: stmtListFeatures r.stmts r.genSize }

/-- Generate one well-typed statement list in `IO` for the Tyche panels. Caps
    `size`/`len` low (mirrors the Plausible wrapper) so whole-list generation
    rarely hits an empty sub-generator. -/
def genStmtsForTyche : IO (List Statement × Nat) := do
  let d ← IO.rand 1 3
  let len ← IO.rand 1 4
  let ss ← genProgramStmtsIO d len
  return (ss, d)

/-- Build a `StmtPropResult` by generating a statement list and applying a check
    predicate under the given tag. -/
def genStmtProp (tag : String) (check : List Statement → Bool) : IO StmtPropResult := do
  let (ss, d) ← genStmtsForTyche
  return { stmts := ss, passed := check ss, genSize := d, tag }

-- ── The `StmtToKleeneStmt` definedness panel (extra breakdown) ────────
-- Unlike the pass/fail panels, this one also records *why* the transform was (un)
-- defined, so the definedness contract (#6) is eyeballable.

structure KleeneDefinedResult where
  stmts : List Statement
  defined : Bool
  genSize : Nat

instance : Tyche.TycheSample KleeneDefinedResult where
  toSample r :=
    let unsupported := hasKleeneUnsupported r.stmts
    let invLoop := hasInvLoopStmts r.stmts
    -- Passes iff the definedness matches the documented contract.
    let passed := checkKleeneDefinedIff r.stmts
    { representation := stmtRepr r.stmts
      status := if passed then .passed else .failed
      features := [
        ("defined", .nominal (if r.defined then "yes" else "no")),
        ("has_unsupported_ctor", .nominal (if unsupported then "yes" else "no")),
        ("has_invariant_loop", .nominal (if invLoop then "yes" else "no")),
        ("contract_holds", .nominal (if passed then "yes" else "no"))
      ] ++ stmtListFeatures r.stmts r.genSize }

def genKleeneDefined : IO KleeneDefinedResult := do
  let (ss, d) ← genStmtsForTyche
  return { stmts := ss, defined := (kleeneStmts ss).isSome, genSize := d }

-- ── Procedure ↔ transform-pass panels ────────────────────────────────
-- One panel per procedure/transform property. Each sample is a generated
-- procedure *list* (assembled into a `Program`), scored by the same shared
-- `check* : List Procedure → Bool` predicate the Plausible suite uses (via the
-- `Properties.procTransforms` bundle), so a panel and its `checkIO` counterpart
-- always agree. Two panels visualize honest failures: `proc: FilterProcedures
-- changed flag is faithful` (samples where nothing is removed yet the pass reports
-- `changed = true` show up as failed marks) and `proc: PrecondElim changed flag is
-- faithful` (the rarer samples where a declared function's body calls a partial
-- function, so a `$$wf` block is inserted while the pass reports unchanged).

open StrataGenerators.Procedure.TestSupport in
/-- Structural features of an assembled procedure program: the procedure count and
    a total statement-body size across all procedures. -/
private def procListFeatures (ps : List Core.Procedure) (genSize : Nat) :
    List (String × Tyche.Feature) :=
  let bodyLen (p : Core.Procedure) := (bodyStmts p.body).length
  [ ("num_procs", .ordinal ps.length),
    ("total_body_stmts", .ordinal (ps.foldl (fun n p => n + bodyLen p) 0)),
    ("generator_size", .ordinal genSize) ]

open StrataGenerators.Procedure.TestSupport in
/-- Render an assembled procedure program via Strata's own formatter. -/
private def procsRepr (ps : List Core.Procedure) : String :=
  let prog : Core.Program := { decls := ps.map (Core.Decl.proc · .empty) }
  (Core.formatProgram prog).pretty

/-- A generated procedure list paired with a single property's pass/fail verdict
    and the property name. One structure serves every boolean procedure property;
    the panel title distinguishes them.

    `diagnostic` and `extraFeatures` let an individual panel append property-specific
    detail to the otherwise uniform program rendering. They exist for properties
    whose failure cause is not *in* the program — see
    `procFactoryStrippedDiagnostic`. Both default to empty, so every other panel is
    unaffected. -/
structure ProcPropResult where
  procs : List Core.Procedure
  passed : Bool
  genSize : Nat
  tag : String
  diagnostic : String := ""
  extraFeatures : List (String × Tyche.Feature) := []

instance : Tyche.TycheSample ProcPropResult where
  toSample r :=
    { representation :=
        if r.diagnostic.isEmpty then procsRepr r.procs
        else procsRepr r.procs ++ "\n\n" ++ r.diagnostic
      status := if r.passed then .passed else .failed
      features := (r.tag, .nominal (if r.passed then "pass" else "fail"))
        :: procListFeatures r.procs r.genSize ++ r.extraFeatures }

open StrataGenerators.Procedure.TestSupport in
/-- Generate a well-typed procedure list in `IO` for the Tyche panels, via
    `Gen.run` on the same `retryGen` wrapper the Plausible harness uses (the
    direct `G := IO` path is unreliable — nested sub-generators hit empty-support
    fallbacks — so we run the retrying `Plausible.Gen` at a random size).
    Names are relabelled `P0…Pk` for collision-free identities.

    Mirrors `TestScaffold.genProcsWith`: the procedures form an acyclic call DAG,
    body `i` generated against the monomorphic siblings `0..i-1` (named `P0…P{i-1}`,
    matching `relabelProcs`), so the panels see programs with real call-graph edges
    (issue #37). -/
def genProcsForTyche : IO (List Core.Procedure × Nat) := do
  let genSize ← IO.rand 0 60
  let n ← IO.rand 2 4
  let size := max 1 (min 2 (genSize / 30))
  let len := max 1 (min 3 (genSize / 25))
  let mut ps : List Core.Procedure := []
  let mut sigs : StrataGenerators.Stmt.ProcSigCtx := []
  for i in List.range n do
    let proc ← Plausible.Gen.run
      (retryGen 8000
        (StrataGenerators.Procedure.genProcedure (G := Plausible.Gen) corePartialOps sigs size len))
      genSize
    ps := ps ++ [proc]
    if proc.header.typeArgs.isEmpty then
      sigs := sigs ++ [StrataGenerators.Procedure.headerProcSig s!"P{i}" proc.header]
  return (relabelProcs ps, genSize)

open StrataGenerators.Procedure.TestSupport in
/-- Build a `ProcPropResult` by generating a procedure list and applying a check
    predicate under the given tag.

    When the property *fails*, the list is first minimized by
    `minimizeProcsCounterexample`, so the panel's `representation` shows the
    smallest well-typed reproducer instead of the raw generated program — the same
    shrink-then-report pattern `genAndCheckFunctionRoundtrip` uses. Features are
    recomputed from the minimized list, so `num_procs` / `total_body_stmts`
    describe what is actually displayed.

    The minimized list still fails `check` (the minimizer only keeps candidates
    that do) and is still well-typed (every candidate passes `procsTypeCheck`), so
    the verdict is unchanged — only the witness gets smaller. Passing samples are
    reported as generated: there is nothing to minimize, and skipping the work
    keeps the common case cheap. -/
def genProcProp (tag : String) (check : List Core.Procedure → Bool) : IO ProcPropResult := do
  let (ps, d) ← genProcsForTyche
  if check ps then
    return { procs := ps, passed := true, genSize := d, tag }
  else
    return { procs := minimizeProcsCounterexample check 200 ps, passed := false, genSize := d, tag }

open StrataGenerators.Procedure.TestSupport in
/-- Render the offending factory entries for the `factoryStripped` panel: each
    output-factory entry that still carries a precondition, with its formatted
    preconditions and whether the program declared it.

    Why this panel needs its own representation: `checkPrecondFactoryStripped`
    fails on *every* input, so the shrinker minimizes the program all the way to
    the empty one — an honest witness, but a mute one, because the failure cause
    is not in the program at all. The formatted program alone therefore reads as
    `program Core;` with no indication of what went wrong. The offenders are the
    actual evidence, so we print them.

    Entries are grouped by `declared` to keep the two independent causes visually
    distinct, and the seeded-builtin list is truncated (58 entries on the empty
    program) since it is long and uniform; the count is always reported in full. -/
private def procFactoryStrippedDiagnostic (ps : List Core.Procedure) : String :=
  let offenders := precondFactoryStrippedOffenders ps
  if offenders.isEmpty then
    "-- output factory: no entry retains a precondition (property holds)"
  else
    let fmt (e : String × List String × Bool) : String :=
      s!"  {e.1} requires {String.intercalate ", " e.2.1}"
    let declared := offenders.filter (·.2.2)
    let builtin := offenders.filter (fun e => !e.2.2)
    let declaredBlock :=
      if declared.isEmpty then []
      else [s!"-- declared by this program ({declared.length}) — PASS-SIDE bug:",
            "-- PrecondElim pushed these into the factory unstripped."]
              ++ declared.map fmt
    let shown := builtin.take 6
    let builtinBlock :=
      if builtin.isEmpty then []
      else [s!"-- seeded Core.Factory builtins ({builtin.length}) — SPEC-SIDE bug:",
            "-- the pass must KEEP these; they are the WF obligations it reads."]
              ++ shown.map fmt
              ++ (if builtin.length > shown.length
                  then [s!"  … and {builtin.length - shown.length} more builtins"] else [])
    String.intercalate "\n"
      ([s!"-- factoryStripped offenders: {offenders.length} factory entries retain a precondition"]
        ++ declaredBlock ++ builtinBlock)

open StrataGenerators.Procedure.TestSupport in
/-- The `factoryStripped` panel: as `genProcProp`, but appends the offending
    factory entries to the representation and records their counts as features, so
    the panel shows *why* the property fails rather than just an empty program.

    The verdict still comes from the shared `checkPrecondFactoryStripped`, so this
    panel and its Plausible counterpart continue to agree. -/
def genProcFactoryStrippedProp (tag : String) (check : List Core.Procedure → Bool) :
    IO ProcPropResult := do
  let r ← genProcProp tag check
  let offenders := precondFactoryStrippedOffenders r.procs
  return { r with
    diagnostic := procFactoryStrippedDiagnostic r.procs
    extraFeatures :=
      [ ("factory_offenders", .ordinal offenders.length),
        ("declared_offenders", .ordinal (offenders.filter (·.2.2)).length),
        ("builtin_offenders", .ordinal (offenders.filter (fun e => !e.2.2)).length) ] }

-- ── Panel runner ────────────────────────────────────────────────────

/-- Write every Tyche panel to `handle` in JSONL format, `numSamples` samples per
    panel. `startTime` is the run-start timestamp shared by all panels (from
    `IO.monoMsNow`). Called by the merged test driver after the LSpec suite, unless
    Tyche visualization is disabled via the CLI flag.

    Each panel's title comes from the shared `PropertyNames.*` catalog, and each
    pass/fail verdict comes from the shared `check*` predicates — so a panel here
    and its `checkIO` counterpart in the Plausible suite always agree. -/
def runTychePanels (handle : IO.FS.Handle) (numSamples : Nat) (startTime : Nat) : IO Unit := do
  let panel {α} [Tyche.TycheSample α] (title : String) (gen : IO α)
      (count : Nat := numSamples) : IO Unit :=
    Tyche.runInto handle gen title count startTime

  panel PropertyNames.exprPreservation genAndEval
  panel PropertyNames.exprProgress genAndCheckProgress
  panel PropertyNames.exprFvarsPreserved genAndCheckFvarPreservation
  -- Counterexample-focused panel: every sample here is a *counterexample* to the
  -- resolve-after-erase property (found by rejection-sampling), so the panel is
  -- densely populated with failing cases for visualization.
  panel PropertyNames.exprResolveAfterErase genResolveCounterexample

  -- Command-level property tests (one panel each). The first four share the
  -- `CmdPropResult` shape and a shared name↔check bundle (`Properties.cmdSingleVerdict`,
  -- also consumed by the Plausible harness); #5 has its own richer panel.
  for p in Properties.cmdSingleVerdict do
    panel p.name (genCmdProp (fun c ctx => p.check (c, ctx)))
  panel PropertyNames.cmdEvalRunAgreement genAndCheckEvalRunAgreement

  -- Function generator property: fvars in generated functions are annotated
  -- consistently with the context type map.
  panel PropertyNames.fnFvarsAnnotated genAndCheckFunctionFvarsAnnotated
  -- Function.typeCheck_annotated_sound: when typeCheck accepts a generated
  -- (spec-well-typed) function, the output satisfies the declarative spec
  -- FuncHasTypeA.
  panel PropertyNames.fnTypeCheckSound
    genAndCheckFunctionTypeCheckSound
  -- Typechecker COMPLETENESS (dual to the panel above). Rejected functions render
  -- as failed marks — the measure-without-body gap shows up as failures, with
  -- `measure_no_body = yes` identifying the cause.
  panel PropertyNames.fnTypeCheckComplete
    genAndCheckFunctionTypeCheckComplete
  -- Pretty-print / parse round-trip: format → parse → re-format is a fixed point
  -- (parse failures marked separately).
  panel PropertyNames.fnRoundtrip genAndCheckFunctionRoundtrip
  -- Type preservation under eval (Step.type_preserved / StepStar.type_preserved /
  -- eval_denote_sound). Evaluating a function body preserves the declared output.
  panel PropertyNames.fnBodyPreservation genAndCheckFunctionBodyPreservation
  -- Special-character identifier round-trip: a legal identifier containing special
  -- (non-alphanumeric) characters (`genQuotedName`) in one syntactic position; a
  -- parse failure or mismatch is a minimal printer/parser bug reproducer.
  panel PropertyNames.fnIdentProbe genAndCheckIdentProbe

  -- ── Statement generator panels (transforms + typechecker) ───────────
  -- One panel per property (#1, #3, #4, #5a, #5b, #6, #9). Each generates a
  -- well-typed statement list (proven sound+complete against `StmtsHasTypeA`) and
  -- visualizes the property's pass/fail against structural features.
  -- Shared name↔check bundles (`Properties.stmtTransforms`), also consumed by the
  -- Plausible harness, so a name is never paired with the wrong check.
  for p in Properties.stmtTransforms do
    panel p.name (genStmtProp p.name p.check)

  -- #6 gets its own richer panel (definedness + why).
  panel PropertyNames.stmtKleeneDefinedIff genKleeneDefined

  -- ── Procedure ↔ transform-pass panels ──────────────────────────────
  -- One panel per property (four FilterProcedures, five PrecondElim, four
  -- ANFEncoder), from the shared `Properties.procTransforms` bundle (also consumed
  -- by both Plausible harnesses). The FilterProcedures changed-flag panel
  -- visualizes the honest failure.
  -- `factoryStripped` gets a diagnostic representation instead of the plain
  -- program: it fails on every input, so its minimized witness is the empty
  -- program and the cause (factory entries retaining preconditions) would
  -- otherwise be invisible. Every other property uses the uniform renderer.
  for p in Properties.procTransforms do
    if p.name == PropertyNames.procPrecondFactoryStripped then
      panel p.name (genProcFactoryStrippedProp p.name p.check)
    else
      panel p.name (genProcProp p.name p.check)
