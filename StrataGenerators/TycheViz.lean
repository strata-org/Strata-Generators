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
-- Supplies the two properties about the `Rat`/`Decimal` boundary, and the property
-- about the SMT escape function.
import StrataGenerators.HasTypeAGen.DecimalAgreement
import StrataGenerators.HasTypeAGen.SmtStringEscaping
import StrataGenerators.AdtLaws
import StrataGenerators.MutualBlockShape
import StrataGenerators.AliasResolution
import StrataGenerators.ProcedureHasTypeAGen.Shrink
-- The whole-program generator, and `minimizeProgramCounterexample` so the program
-- panels report the minimal well-typed counterexample rather than the raw draw.
import StrataGenerators.ProgramGen
import StrataGenerators.ProgramGen.Shrink
-- Supplies the phase-sweep checks and their reporting helpers, and the printer
-- oracle with its per-width / per-operator checks. (Both arrive via `Properties`
-- too; named here because the panels below use them directly.)
import StrataGenerators.PhaseChangedFlag
import StrataGenerators.PrinterCoverage
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

Generates samples from the `HasTypeA` / command / function / statement / procedure
/ whole-program generators and writes them in Tyche JSONL format for
visualization, plus panels for the properties whose input space is a fixed finite
set (the pipeline-phase no-op witnesses, and the printer's bitvector widths and
`Bv↔Int` operators) rather than a distribution — those are *enumerated* via
`Tyche.writeInto` rather than sampled.

This module holds every Tyche panel (feature extractors, `TycheSample` instances,
`IO` generator wrappers, and `runTychePanels`). It is *not* an executable root: the
merged test driver in `TestMain.lean` calls `runTychePanels` after the LSpec suite,
gated behind a CLI flag (Tyche visualization is on by default).

All property *check* logic (pass/fail verdicts and the helper contexts behind them)
is shared with the Plausible harness via the `*.TestSupport` modules — this file
only adds the Tyche-specific visualization scaffolding (feature breakdowns, sample
representations).
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
--
-- Note the expression panels below instantiate at `G := IO` and so leave
-- `genLExpr`'s `retryCont` at its `id` default (no retrying). `retryGenArg` — the
-- retry continuation `TestScaffold` passes — is `Plausible.Gen`-specific, since
-- retrying needs `tryCatch`. The panels that *do* go through `Plausible.Gen`
-- (`genProcsForTyche`, below) get the outer `retryGen` treatment instead.

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
-- `resolveLContext`, `coreOpCtx`, `eraseAllTypes`, and `isInstanceOf` are the
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
  let expr ← genLExprWithOps (G := IO) [] coreOpCtx [] tvars [] d ty
  let erased := eraseAllTypes expr
  let resolvedTy := match LExpr.resolve resolveLContext Lambda.TEnv.default erased with
    | .ok (resolved, _) => some resolved.toLMonoTy
    | .error _ => none
  return ⟨expr, ty, resolvedTy, d⟩

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
  let (_, baseCtx) ← genCmds (G := IO) coreMonoOps tvars [] [] d numCmds
  let ⟨cmd, ctx'⟩ ← genCmd (G := IO) coreMonoOps tvars [] baseCtx d
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
-- (`Strata/Languages/Core/FunctionTypeSpecSound.lean`): when
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
-- against `StatementsHasTypeA`). The `check*` predicates and measurements are shared
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
-- defined, so the definedness contract is eyeballable.

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
-- always agree. The two `changed`-flag panels discriminate the samples that bear on
-- the flag: for `proc: FilterProcedures changed flag is faithful`, those where
-- nothing is removed; for `proc: PrecondElim changed flag is faithful`, the rarer
-- ones where a declared function's body calls a partial function and a `$$wf` block
-- is inserted.

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
    matching `relabelProcs`), so the panels see programs with real call-graph
    edges. -/
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
        (StrataGenerators.Procedure.genProcedure (G := Plausible.Gen) corePartialOps sigs LContext.default {} size len))
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

    Why this panel needs its own representation: the relevant cause is not in the
    program at all, so the shrinker minimizes the program all the way to the empty
    one and the formatted program reads as `program Core;` with no indication of what
    bore on the result. The offenders are the actual evidence, so we print them.

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

-- ── Whole-program panels ────────────────────────────────────────────
-- One panel per property in `Properties.programChecks`. Each sample is a whole
-- generated `Program` (every declaration kind, ambient context threaded across the
-- fold) with a pass/fail verdict.
--
-- For the `typechecker accepts generated programs` panel, ~60% of draws are
-- rejected on one of three known causes, and the `rejection_cause` feature below is
-- what makes the breakdown legible — the panel separates the three causes rather
-- than showing one undifferentiated block. Those rejections are also the ones the
-- shrinker cannot minimize (its oracle is the checker under test), so `num_decls`
-- on a rejected sample is the generated size, not a reduced one.

open StrataGenerators.Program.TestSupport in
/-- Structural features of a generated program: declaration count, reducible size,
    which declaration kinds it contains, and — the discriminating feature for the
    completeness panel — which known gap (if any) it bears. -/
private def programFeatures (p : Core.Program) (genSize : Nat) :
    List (String × Tyche.Feature) :=
  let kind : Core.Decl → String
    | .type (.con _) _ => "type.con"
    | .type (.syn _) _ => "type.syn"
    | .type (.data _) _ => "type.data"
    | .ax _ _ => "axiom"
    | .distinct _ _ _ => "distinct"
    | .proc _ _ => "proc"
    | .func _ _ => "func"
    | .recFuncBlock _ _ => "recFuncBlock"
  let causes := programRejectionCause p
  [ ("num_decls", .ordinal p.decls.length),
    ("program_size", .ordinal (sizeProgram p)),
    ("decl_kinds", .nominal (" ".intercalate (p.decls.map kind).eraseDups)),
    ("rejection_cause", .nominal (if causes.isEmpty then "none" else "+".intercalate causes)),
    ("generator_size", .ordinal genSize) ]

/-- A generated program paired with one property's verdict and the property name. -/
structure ProgramPropResult where
  prog : Core.Program
  passed : Bool
  genSize : Nat
  tag : String

open StrataGenerators.Program.TestSupport in
instance : Tyche.TycheSample ProgramPropResult where
  toSample r :=
    -- Render via Strata's own formatter, annotating a typechecker-rejected program
    -- with the gap it bears via the *shared* `programStatusNote` — the same function
    -- the Plausible `Repr` uses, so a counterexample reads identically in both views.
    { representation := (Core.formatProgram r.prog).pretty ++ programStatusNote r.prog
      status := if r.passed then .passed else .failed
      features := (r.tag, .nominal (if r.passed then "pass" else "fail"))
        :: programFeatures r.prog r.genSize }

/-- Generate a whole program in `IO` for the Tyche panels, via `ProgramGen.sample`
    (which runs the generator through the retrying `Plausible.Gen` interpretation —
    the direct `G := IO` path is unreliable, as `ProgramGen.sample`'s docstring
    records). Mirrors `TestScaffold.genProgramWith`'s bounds. -/
def genProgramForTyche : IO (Core.Program × Nat) := do
  let genSize ← IO.rand 0 60
  let numDecls := max 2 (min 5 (2 + genSize / 25))
  let prog ← ProgramGen.sample numDecls {} 30000 genSize
  return (prog, genSize)

open StrataGenerators.Program.TestSupport in
/-- Build a `ProgramPropResult` by generating a program and applying a check
    predicate under the given tag.

    A failing sample is first minimized by `minimizeProgramCounterexample`, so the
    panel shows the smallest well-typed reproducer rather than the raw draw — the
    same shrink-then-report pattern `genProcProp` uses. The minimized program still
    fails `check` and is still well-typed, so the verdict is unchanged; features are
    recomputed from it, so `num_decls`/`program_size` describe what is displayed.

    For `programTypecheck` specifically the minimizer is a no-op by construction
    (the negative result *is* oracle rejection, so no candidate survives the filter)
    and the raw draw is shown, which is why the `rejection_cause` feature exists.
    Other samples are reported as generated. -/
def genProgramProp (tag : String) (check : Core.Program → Bool) : IO ProgramPropResult := do
  let (p, d) ← genProgramForTyche
  if check p then
    return { prog := p, passed := true, genSize := d, tag }
  else
    return { prog := minimizeProgramCounterexample check 400 p, passed := false,
             genSize := d, tag }

-- ── Pipeline-phase `changed`-flag panels ────────────────────────────
-- One panel per property in `Properties.phaseNoOpWitnesses` / `phaseChangedFlags`
-- (see `StrataGenerators.PhaseChangedFlag`). The properties have two shapes and so
-- do the panels:
--
--   * the two no-op witnesses take no generated input at all — each is one
--     constructed program on which one phase provably cannot change anything — so
--     their panels *enumerate* their single witness rather than sample it. Drawing
--     it a thousand times would give a thousand identical marks;
--   * the two sweeps quantify over generated procedure lists, so they sample like
--     the `proc:` panels, with the offending phases as the discriminating feature.
--
-- The first three discriminate the four hardcoded `changed := true` sites.
-- `phase: non-hardcoded pipeline phases have a faithful changed flag` is the
-- regression guard, so a single discriminating mark in its panel is the interesting
-- event.

open StrataGenerators.PhaseChangedFlag in
/-- One constructed no-op witness. The verdict is the shared `NoOpWitness.check`,
    and the reported/actual flags come from the same `phaseOutcome` that check
    reads, so the panel cannot display a flag other than the one it scored. -/
structure PhaseNoOpResult where
  witness : NoOpWitness

open StrataGenerators.PhaseChangedFlag in
instance : Tyche.TycheSample PhaseNoOpResult where
  toSample r :=
    let passed := r.witness.check
    let outcome := phaseOutcome r.witness.phase r.witness.prog
    let flag (b : Option Bool) : String := match b with
      | some true => "yes" | some false => "no" | none => "—"
    { representation :=
        (Core.formatProgram r.witness.prog).pretty
          ++ s!"\n-- {r.witness.label}: {outcomeDescription r.witness.named r.witness.prog}"
      status := if passed then .passed else .failed
      statusReason :=
        if passed then ""
        else s!"{r.witness.label} cannot have changed this program, yet reported changed = true"
      features := [
        ("verdict", .nominal (if passed then "pass" else "fail")),
        ("phase", .nominal r.witness.label),
        -- The flag the phase reported against what it actually did: the whole
        -- content of the finding is that these two disagree.
        ("reported_changed", .nominal (flag (outcome.map (·.1)))),
        ("program_changed", .nominal (flag (outcome.map (·.2)))),
        ("num_decls", .ordinal r.witness.prog.decls.length) ] }

open StrataGenerators.PhaseChangedFlag in
/-- A generated procedure list swept by a phase list, with the sweep's verdict and
    the labels of the phases that violated it.

    `violatingPhases` and `diagnostic` are what make a failed mark legible. Like the
    `factoryStripped` panel, the failure cause is not *in* the program — every phase
    of `allCorePhases` sees the same program, and the two `Verifier.lean` phases
    report `changed = true` on all of them — so the minimized witness is nearly
    empty and the program alone would say nothing about which phase lied. -/
structure PhaseSweepResult where
  procs : List Core.Procedure
  passed : Bool
  genSize : Nat
  tag : String
  /-- Labels of the swept phases whose flag was unfaithful, deduplicated. -/
  violatingPhases : List String
  /-- How many phases this property sweeps, for context on the count above. -/
  numSwept : Nat
  /-- Per-violator detail, from the shared `phaseChangedFlagDiagnostic`. -/
  diagnostic : String
  /-- Whether the program contains a loop — i.e. whether `symbolicEval` was skipped
      on this sample rather than scored. -/
  hasLoop : Bool

instance : Tyche.TycheSample PhaseSweepResult where
  toSample r :=
    { representation := procsRepr r.procs ++ "\n\n" ++ r.diagnostic
      status := if r.passed then .passed else .failed
      statusReason :=
        if r.passed then ""
        else s!"unfaithful changed flag in: {" ".intercalate r.violatingPhases}"
      features := (r.tag, .nominal (if r.passed then "pass" else "fail"))
        :: procListFeatures r.procs r.genSize ++ [
        ("num_violators", .ordinal r.violatingPhases.length),
        -- Which phases lied on this sample. On the full sweep this should be
        -- constantly the known set; a *new* label appearing here is the regression
        -- the property exists to catch, and this feature is where it shows up.
        ("violating_phases", .nominal
          (if r.violatingPhases.isEmpty then "none"
           else " ".intercalate r.violatingPhases)),
        ("num_phases_swept", .ordinal r.numSwept),
        -- `symbolicEval` is skipped (not scored) on a program with a loop, so a
        -- `yes` here marks a sample that is vacuous for that one phase.
        ("symbolic_eval_skipped", .nominal (if r.hasLoop then "yes" else "no")) ] }

open StrataGenerators.Procedure.TestSupport StrataGenerators.PhaseChangedFlag in
/-- Build a `PhaseSweepResult` by generating a procedure list, scoring it with the
    shared sweep check, and recording which of `phases` violated the contract.

    Generation and minimization are `genProcProp`'s, so this panel draws from the
    same distribution as the `proc:` ones. The violators are recomputed from the
    (possibly minimized) list the panel actually displays, so the diagnostic always
    describes the program on screen. -/
def genPhaseSweepProp (tag : String) (check : List Core.Procedure → Bool)
    (phases : List NamedPhase) : IO PhaseSweepResult := do
  let r ← genProcProp tag check
  let prog := mkProgram r.procs
  return { procs := r.procs, passed := r.passed, genSize := r.genSize, tag,
           violatingPhases := violators phases prog,
           numSwept := phases.length,
           diagnostic := phaseChangedFlagDiagnostic phases prog,
           hasLoop := programHasLoop prog }

open StrataGenerators.PhaseChangedFlag in
/-- The phase list a sweep property quantifies over, so the panel's diagnostic
    reports on *exactly* the phases its check scored. Keyed on the property name
    because the check is a `List Procedure → Bool` that has already closed over its
    list; the narrower sweep is the one that excludes `knownDefectivePhases`. -/
def sweptPhasesFor (name : String) : List NamedPhase :=
  if name == PropertyNames.phaseHonestChangedFlag then honestPhases else allCorePhases

-- ── Printer-expressiveness panels ───────────────────────────────────
-- One panel per property in `Properties.printerWitnesses` / the whole-program
-- printer property (see `StrataGenerators.PrinterCoverage`).
--
-- The three witness panels enumerate a *fixed finite* input space — the registered
-- bitvector widths, the eighteen `Bv↔Int` operators, the widths `0..63` — rather
-- than sampling it, and score each element with the shared per-element check whose
-- conjunction *is* the property. So the panel shows the shape of the gap (which
-- widths, which directions) where the property's single `Bool` can only report that
-- a gap exists.

/-- Is `n` a power of two? The panels record this because the usual framing
    predicts the printable widths are the powers of two, and they are not: `2`, `4`
    and `128` are powers of two that do not print. Seeing that in the panel is the
    point. -/
private def isPowerOfTwo (n : Nat) : Bool := n != 0 && (n &&& (n - 1)) == 0

/-- A generated whole program, scored by the printer-expressiveness oracle ("the
    printer logged no conversion error"). -/
structure PrinterProgramResult where
  prog : Core.Program
  passed : Bool
  genSize : Nat
  /-- The distinct Strata-attributable conversion-error lines. -/
  errorLines : List String
  /-- Whether the text the printer *claims* to have produced still re-parses.
      `none` when nothing went wrong, so there was nothing to ask. -/
  reparsedDespiteError : Option Bool

open StrataGenerators.PrinterCoverage in
instance : Tyche.TycheSample PrinterProgramResult where
  toSample r :=
    -- Show the printer's *whole* output, error block included: that block is the
    -- evidence, and the placeholders it explains (`$__unknown_type`,
    -- `mkGenericCall`) are visible in the program text right above it.
    { representation := (Core.formatProgram r.prog).pretty
      status := if r.passed then .passed else .failed
      statusReason := " ".intercalate r.errorLines
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        ("num_error_sites", .ordinal r.errorLines.length),
        -- Which printer functions failed, e.g. `lconstToExpr` or `handleUnaryOps`.
        -- Grouped by site rather than by message so that one gap hit at two widths
        -- reads as one gap.
        ("error_sites", .nominal
          (if r.errorLines.isEmpty then "none"
           else " ".intercalate (r.errorLines.map errorSite).eraseDups)),
        -- **The dangerous case.** A program that logged an error and still
        -- re-parses is one where a placeholder silently produced a *different*
        -- program — precisely what a string round-trip cannot detect, and the reason
        -- this property is worth having alongside the round-trip one.
        ("silently_different", .nominal (match r.reparsedDespiteError with
          | some true => "yes" | some false => "no" | none => "—")),
        ("reparsed", .nominal (match r.reparsedDespiteError with
          | some true => "yes" | some false => "no" | none => "—"))
      ] ++ programFeatures r.prog r.genSize }

open StrataGenerators.Program.TestSupport StrataGenerators.PrinterCoverage in
/-- Generate a whole program and score it with the shared printer oracle.

    A failing draw is minimized first, as in `genProgramProp` — and unlike
    `programTypecheck`, these failures *do* shrink: the oracle is the printer, not
    the typechecker the shrinker uses to keep candidates well-typed, so a smaller
    unprintable program survives the filter. What the panel shows is therefore a
    minimal unprintable program, and the error lines and re-parse verdict are
    recomputed from it.

    Read `error_sites` accordingly: it is which site the *minimal* witness blames,
    not which site fires most often across raw draws — shrinking keeps one of
    several independent gaps and discards the rest. The unbiased cross-sample tally
    is the ungated `printerErrorDiagnostic`. -/
def genPrinterProgramProp : IO PrinterProgramResult := do
  let (raw, d) ← genProgramForTyche
  let passed := checkProgramPrintsWithoutError raw
  let prog :=
    if passed then raw
    else minimizeProgramCounterexample checkProgramPrintsWithoutError 400 raw
  let errorLines := programErrorLines prog
  -- Only ask the parser when the printer already logged something: a `no` here is
  -- the ordinary case (the round-trip property is red too) and a `yes` is the
  -- silently-different one. With no error there is no question to ask.
  let reparsedDespiteError ←
    if errorLines.isEmpty then pure none
    else pure (some (← parseCoreProgram (printedText (Core.formatProgram prog).pretty)).isSome)
  -- `passed` describes `prog`: minimization only ever returns a candidate that
  -- still fails the check, so the verdict survives it unchanged.
  return { prog, passed, genSize := d, errorLines, reparsedDespiteError }

/-- One bitvector literal width, scored by the shared per-width check whose
    instance at `128` *is* `checkBv128LiteralPrints`. -/
structure BvLitWidthResult where
  width : Nat
  passed : Bool

open StrataGenerators.PrinterCoverage in
instance : Tyche.TycheSample BvLitWidthResult where
  toSample r :=
    { representation := (Core.formatExprs [bvLit r.width]).pretty
      status := if r.passed then .passed else .failed
      statusReason :=
        if r.passed then "" else s!"lconstToExpr cannot print a bitvec {r.width} literal"
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        ("width", .ordinal r.width),
        ("power_of_two", .nominal (if isPowerOfTwo r.width then "yes" else "no")),
        -- The width this panel's property is about. It is the *only* registered
        -- width that fails, which is what makes it an omission rather than a
        -- design boundary — and that is legible only next to its siblings.
        ("pinned_by_property", .nominal (if r.width == 128 then "yes" else "no"))
      ] }

/-- One `Bv↔Int` conversion operator, scored by the shared per-operator check whose
    conjunction over all eighteen *is* `checkBvIntConversionsPrint`. -/
structure BvIntConversionResult where
  op : String
  width : Nat
  /-- Which of the three registered directions this operator is. -/
  direction : String
  passed : Bool

open StrataGenerators.PrinterCoverage in
instance : Tyche.TycheSample BvIntConversionResult where
  toSample r :=
    { representation := (Core.formatExprs [unaryApp r.op]).pretty
      status := if r.passed then .passed else .failed
      statusReason :=
        if r.passed then ""
        else s!"no grammar production and no printer arm for {r.op}; falls through to mkGenericCall"
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        ("operator", .nominal r.op),
        ("width", .ordinal r.width),
        -- The gap is the whole family: every direction at every width. Splitting
        -- the panel by these two features is what shows that, rather than an
        -- undifferentiated block of eighteen failures.
        ("direction", .nominal r.direction)
      ] }

/-- Labels for the three conversion directions, in the order
    `PrinterCoverage.bvIntConversionOps` returns them. -/
private def conversionDirections : List String := ["bv_to_int", "bv_to_uint", "int_to_bv"]

-- The zip below silently drops operators if these two lists ever disagree in
-- length, which would understate the finding.
#guard (StrataGenerators.PrinterCoverage.bvIntConversionOps 8).length
         == conversionDirections.length

open StrataGenerators.PrinterCoverage in
/-- Every registered `Bv↔Int` conversion operator, scored individually. -/
def bvIntConversionSamples : List BvIntConversionResult :=
  factoryBvWidths.flatMap fun w =>
    ((bvIntConversionOps w).zip conversionDirections).map fun (op, direction) =>
      { op, width := w, direction, passed := checkBvIntConversionPrints op }

/-- One bitvector width in *type* position, scored by the shared per-width
    implication (`typechecks → prints`) whose conjunction over `0..63` *is*
    `checkAllWidthsAgree`. -/
structure BvWidthAgreementResult where
  width : Nat
  typechecks : Bool
  prints : Bool
  passed : Bool

open StrataGenerators.PrinterCoverage in
instance : Tyche.TycheSample BvWidthAgreementResult where
  toSample r :=
    { representation := formatFuncAsProgram (bvIdentityFunc r.width)
      status := if r.passed then .passed else .failed
      statusReason :=
        if r.passed then ""
        else s!"Function.typeCheck accepts bitvec {r.width}, the printer substitutes $__unknown_type"
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        ("width", .ordinal r.width),
        -- Read these two together: `typechecks = yes, prints = no` is the
        -- divergence, and it is 60 of the first 64 widths.
        ("typechecks", .nominal (if r.typechecks then "yes" else "no")),
        ("prints", .nominal (if r.prints then "yes" else "no")),
        -- The usual framing predicts the printable set is the powers of two.
        -- Grouping by this feature is what refutes that: `2`, `4` and `128` are red.
        ("power_of_two", .nominal (if isPowerOfTwo r.width then "yes" else "no")),
        ("factory_registered", .nominal
          (if factoryBvWidths.contains r.width then "yes" else "no"))
      ] }

open StrataGenerators.PrinterCoverage in
/-- The widths `0..63`, each scored individually — the same range
    `checkAllWidthsAgree` conjoins over. -/
def bvWidthAgreementSamples : List BvWidthAgreementResult :=
  (List.range 64).map fun w =>
    { width := w, typechecks := widthTypeChecks w, prints := widthPrintsCleanly w,
      passed := checkWidthTypeCheckPrinterAgreement w }

-- ── Panel for the SMT escape function ───────────────────────────────
-- Each sample is one string from `genInterestingString`, serialized through
-- `Strata.SMTDDM.termToString`, which is the real path to the solver. A sample
-- passes when each character of the emitted literal is printable ASCII, which is
-- the requirement of SMT-LIB 2.6+ itself.

/-- One sample for the property about the SMT escape function. -/
structure EscapingResult where
  /-- The drawn string. -/
  s : String
  /-- Whether the emitted literal holds only printable ASCII. -/
  passed : Bool
  /-- The codepoints that reach the literal without an escape. -/
  offenders : List Nat

/-- The highest codepoint in `s`, or `0` for the empty string. This is the feature
    that separates a pass from a failure, because the escape function stops at
    U+00A1. -/
private def maxCodepoint (s : String) : Nat :=
  s.toList.foldl (fun acc c => max acc c.toNat) 0

/-- The number of UTF-8 bytes that `c` needs. The defect emits a raw UTF-8 byte, so
    the count of bytes is what a solver measures where Lean counts one
    codepoint. -/
private def utf8Width (c : Char) : Nat :=
  let n := c.toNat
  if n < 0x80 then 1 else if n < 0x800 then 2 else if n < 0x10000 then 3 else 4

/-- The widest UTF-8 encoding among the characters of `s`. -/
private def maxUtf8Width (s : String) : Nat :=
  s.toList.foldl (fun acc c => max acc (utf8Width c)) 1

/-- Which band of codepoints the widest character of `s` falls in. The bands are
    the ones that the escape function treats differently. -/
private def codepointBand (s : String) : String :=
  let m := maxCodepoint s
  if s.isEmpty then "empty"
  else if m < 0x20 then "ascii_control"
  else if m < 0x80 then "ascii_printable"
  else if m ≤ 0xA0 then "escaped_latin1"
  -- U+00AD, the soft hyphen, is the one special case of `useXHex` above U+00A1, so
  -- it gets an escape and its band is separate. Without this band, a sample that
  -- holds U+00AD looks like a pass inside a failing band.
  else if m == 0xAD then "soft_hyphen"
  else if m < 0x100 then "unescaped_latin1"
  else if m ≤ 0x2FFFF then "bmp_or_astral"
  else "above_smtlib_alphabet"

instance : Tyche.TycheSample EscapingResult where
  toSample r :=
    { representation := s!"{repr r.s}",
      status := if r.passed then .passed else .failed,
      statusReason :=
        if r.passed then ""
        else
          let hex := String.intercalate ", " (r.offenders.map (fun n =>
            s!"U+{(String.ofList (Nat.toDigits 16 n)).toUpper}"))
          s!"emitted with unescaped {hex}",
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        -- The band of the widest codepoint. The boundary of the defect is between
        -- `escaped_latin1`, which ends at U+00A0, and `unescaped_latin1`, which
        -- starts at U+00A1.
        ("codepoint_band", .nominal (codepointBand r.s)),
        ("max_codepoint", .ordinal (maxCodepoint r.s)),
        -- The widest UTF-8 encoding. A value above 1 is where a count of bytes and
        -- a count of codepoints disagree.
        ("max_utf8_width", .ordinal (maxUtf8Width r.s)),
        ("num_offenders", .ordinal r.offenders.length),
        ("string_length_codepoints", .ordinal r.s.length),
        ("string_length_bytes", .ordinal r.s.utf8ByteSize),
        -- Whether the two counts of length differ, which is the discriminating
        -- case for each property about `Str.Length`.
        ("byte_length_differs", .nominal
          (if r.s.length == r.s.utf8ByteSize then "no" else "yes")),
        ("is_empty", .nominal (if r.s.isEmpty then "yes" else "no")),
        -- Whether the string holds any non-ASCII character at all. A sample with
        -- `no` here passes for a trivial reason, so this feature separates a true
        -- pass from a vacuous one.
        ("has_non_ascii", .nominal
          (if r.s.toList.any (fun c => c.toNat ≥ 0x80) then "yes" else "no"))
      ] }

/-- Draw one string and record whether its SMT-LIB literal is printable ASCII. -/
private def genEscapingSample : IO EscapingResult := do
  let s ← StrataGenerators.PrimitiveGens.genInterestingString (G := IO)
  return { s := s,
           passed := StrataGenerators.SmtStringEscaping.escapedIsPrintableAscii s,
           offenders := StrataGenerators.SmtStringEscaping.offendingCodepoints s }

-- ── Panels for the `Rat`/`Decimal` boundary ─────────────────────────
-- Two properties about the representation of a real in the SMT dialect. Each pair
-- of samples is two `Decimal` spellings of **one** rational value, from
-- `genSameValuePair`. Therefore each sample is a case that must pass, and each
-- failure is a true defect and not an artifact of the draw.

/-- One sample for a property about the `Rat`/`Decimal` boundary. -/
structure DecimalPairResult where
  /-- The first spelling, from `Decimal.fromRat` on a drawn rational. -/
  d₁ : StrataDDM.Decimal
  /-- The second spelling of the *same* value, from `inflate`. -/
  d₂ : StrataDDM.Decimal
  /-- Whether the property holds on this pair. -/
  passed : Bool
  /-- Whether the fold of `Factory.eq` gave a literal `bool`, and which one. -/
  eqFold : Option Bool
  /-- The verdicts of the comparator, in both directions. -/
  lt₁ : Bool
  lt₂ : Bool

/-- Render a `Decimal` as `mantissa e exponent`, the form that shows the spelling
    rather than the value. Two samples that render differently and denote one value
    are the whole subject of these panels. -/
private def ppDecimal (d : StrataDDM.Decimal) : String :=
  s!"{d.mantissa}e{d.exponent}"

/-- The number of decimal digits in the mantissa, which measures how far `inflate`
    moved the spelling away from the normal form. -/
private def mantissaDigits (d : StrataDDM.Decimal) : Nat :=
  (toString d.mantissa.natAbs).length

/-- The sign of the value, as a nominal feature. A defect that appeared for one
    sign only would be visible here. -/
private def valueSign (d : StrataDDM.Decimal) : String :=
  if d.mantissa == 0 then "zero" else if d.mantissa < 0 then "negative" else "positive"

instance : Tyche.TycheSample DecimalPairResult where
  toSample r :=
    let value := StrataDDM.Decimal.toRat r.d₁
    { representation :=
        s!"{ppDecimal r.d₁} and {ppDecimal r.d₂} both denote {value}",
      status := if r.passed then .passed else .failed,
      statusReason :=
        if r.passed then ""
        else
          s!"eq folded to {match r.eqFold with | some b => toString b | none => "no literal"}, \
lt in both directions gave {r.lt₁} and {r.lt₂}, for two spellings of {value}",
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        -- What the fold of `eq` gave. `false` on a pair of equal value is the
        -- defect; `no_literal` means `Factory.eq` left the comparison to the solver.
        ("eq_fold", .nominal (match r.eqFold with
          | some true => "true"
          | some false => "false"
          | none => "no_literal")),
        -- How many of "less than", "greater than" and "equal" hold. Trichotomy
        -- needs exactly 1, and the defect gives 0.
        ("trichotomy_count", .ordinal
          ((if r.lt₁ then 1 else 0) + (if r.lt₂ then 1 else 0)
            + (if r.eqFold == some true then 1 else 0))),
        ("value_sign", .nominal (valueSign r.d₁)),
        -- Whether the value has an integer denominator of 1, so the panel shows
        -- that the defect is not confined to a whole number.
        ("value_is_integer", .nominal (if value.den == 1 then "yes" else "no")),
        ("mantissa_digits_first", .ordinal (mantissaDigits r.d₁)),
        ("mantissa_digits_second", .ordinal (mantissaDigits r.d₂)),
        -- The distance in digits between the two spellings, which is the inflation
        -- factor. A defect that needed a large factor would be visible here.
        ("inflation_digits", .ordinal
          (mantissaDigits r.d₂ - mantissaDigits r.d₁)),
        ("exponent_first", .ordinal r.d₁.exponent),
        ("exponent_second", .ordinal r.d₂.exponent),
        -- Whether the two spellings are structurally equal. `Factory.eq` folds a
        -- structurally equal pair correctly through its first branch, so a
        -- non-vacuous sample needs `no` here.
        ("structurally_equal", .nominal (if r.d₁ == r.d₂ then "yes" else "no"))
      ] }

/-- Draw one pair of equal value and record the verdict of the property that
    `check` states. -/
private def genDecimalPairProp
    (check : StrataDDM.Decimal → StrataDDM.Decimal → Bool) : IO DecimalPairResult := do
  let (d₁, d₂) ← StrataGenerators.DecimalAgreement.genSameValuePair (G := IO)
  return { d₁ := d₁, d₂ := d₂,
           passed := check d₁ d₂,
           eqFold := StrataGenerators.DecimalAgreement.actualEqFold d₁ d₂,
           lt₁ := Strata.SMT.TermPrim.lt (.real d₁) (.real d₂),
           lt₂ := Strata.SMT.TermPrim.lt (.real d₂) (.real d₁) }

-- ── ADT-law / mutual-block panels ──────────────────────────────────
--
-- The `adt:` and `mutual:` properties quantify over a generated `mutual … end`
-- block rather than over a program, so they need their own sample type. The
-- features are the ones that separate a real pass from a vacuous one: how many
-- datatypes the block held (a `mutual:` property is vacuous below two), whether the
-- datatypes' type parameters agree (the condition `elimFuncs` assumes, and the
-- discriminator for the eliminator-scoping failure), whether the block is
-- cross-referenced at all, whether Strata accepted it, and whether it passed the
-- SMT-safety screen the `--smt` law properties apply.

/-- A generated datatype block paired with one property's verdict. -/
structure AdtBlockPropResult where
  block : Lambda.MutualDatatype Unit
  passed : Bool
  tag : String

open StrataGenerators.MutualBlockShape StrataGenerators.AdtLaws in
instance : Tyche.TycheSample AdtBlockPropResult where
  toSample r :=
    { representation := renderBlock r.block
      status := if r.passed then .passed else .failed
      features :=
        [ (r.tag, .nominal (if r.passed then "pass" else "fail")),
          ("num_datatypes", .ordinal r.block.length),
          ("num_constrs", .ordinal (r.block.foldl (fun n d => n + d.constrs.length) 0)),
          ("params_uniform", .nominal (if blockParamsUniform r.block then "yes" else "no")),
          ("independent", .nominal (if isIndependentBlock r.block then "yes" else "no")),
          ("addMutualBlock", .nominal (if blockAccepted r.block then "accepted" else "rejected")),
          ("smt_safe", .nominal (if blockIsSmtSafe r.block then "yes" else "no")) ] }

/-- Sample an ordinary block and score it with `check`. Drawn at `maxSize := 0`,
    matching the `Arbitrary GenAdtBlock` instance the Plausible harnesses use, so a
    panel and its LSpec counterpart see the same distribution. -/
def genAdtBlockProp (tag : String) (check : Lambda.MutualDatatype Unit → Bool) :
    IO AdtBlockPropResult := do
  let block ← DatatypeGen.sample (maxSize := 0)
  return { block, passed := check block, tag }

/-- Sample a block of *independent* datatypes and score it with `check`. Mirrors
    `Arbitrary GenIndepBlock`. -/
def genIndepBlockProp (tag : String) (check : Lambda.MutualDatatype Unit → Bool) :
    IO AdtBlockPropResult := do
  let extra ← IO.rand 0 2
  let block ← StrataGenerators.MutualBlockShape.genIndependentBlock (G := IO) (extra + 1)
  return { block, passed := check block, tag }


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
  -- For a property whose input space is a fixed finite set rather than a
  -- distribution: enumerate it once instead of sampling it `numSamples` times.
  let enumerate {α} [Tyche.TycheSample α] (title : String) (samples : List α) :
      IO Unit :=
    Tyche.writeInto handle samples title startTime

  panel PropertyNames.exprPreservation genAndEval
  panel PropertyNames.exprProgress genAndCheckProgress
  panel PropertyNames.exprFvarsPreserved genAndCheckFvarPreservation
  panel PropertyNames.exprResolveAfterErase genAndCheckResolveAfterErase

  panel PropertyNames.exprSmtStringEscaping genEscapingSample

  panel PropertyNames.realDecimalEqFold
    (genDecimalPairProp StrataGenerators.DecimalAgreement.checkEqFold)
  panel PropertyNames.realDecimalTrichotomy
    (genDecimalPairProp StrataGenerators.DecimalAgreement.checkTrichotomy)

  -- Command-level property tests (one panel each). The first four share the
  -- `CmdPropResult` shape and a shared name↔check bundle (`Properties.cmdSingleVerdict`,
  -- also consumed by the Plausible harness); eval/run agreement has its own
  -- richer panel.
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
  -- One panel per property. Each generates a
  -- well-typed statement list (proven sound+complete against `StatementsHasTypeA`) and
  -- visualizes the property's pass/fail against structural features.
  -- Shared name↔check bundles (`Properties.stmtTransforms`), also consumed by the
  -- Plausible harness, so a name is never paired with the wrong check.
  for p in Properties.stmtTransforms do
    panel p.name (genStmtProp p.name p.check)

  -- Kleene definedness gets its own richer panel (definedness + why).
  panel PropertyNames.stmtKleeneDefinedIff genKleeneDefined

  -- ── Procedure ↔ transform-pass panels ──────────────────────────────
  -- One panel per property (four FilterProcedures, five PrecondElim, four
  -- ANFEncoder), from the shared `Properties.procTransforms` bundle (also consumed
  -- by both Plausible harnesses).
  -- `factoryStripped` gets a diagnostic representation instead of the plain
  -- program: its minimized witness is the empty
  -- program and the cause (factory entries retaining preconditions) would
  -- otherwise be invisible. Every other property uses the uniform renderer.
  for p in Properties.procTransforms do
    if p.name == PropertyNames.procPrecondFactoryStripped then
      panel p.name (genProcFactoryStrippedProp p.name p.check)
    else
      panel p.name (genProcProp p.name p.check)

  -- ── Whole-program panels ───────────────────────────────────────────
  -- One panel per property in the shared `Properties.programChecks` and
  -- `Properties.programADTProps` bundles (both also consumed by both Plausible
  -- harnesses, so the LSpec suite and these panels cover the same ten checks). A
  -- failing sample is minimized by the whole-program shrinker before display, except
  -- for `programTypecheck`, whose failures are oracle rejections and so cannot
  -- shrink — there the `rejection_cause` feature is what makes the three gaps
  -- legible. The `programADTProps` panels pass on every draw; their value is the
  -- `decl_kinds` feature, which shows whether a sample even contained a datatype
  -- block for the ADT-derived-call path to be exercised.
  for p in Properties.programChecks ++ Properties.programADTProps do
    panel p.name (genProgramProp p.name p.check)

  -- ── Pipeline-phase `changed`-flag panels ───────────────────────────
  -- The two no-op witnesses are enumerated (one constructed program each, from the
  -- shared `Properties.phaseNoOpWitnesses` bundle, so the panel scores the same
  -- `NoOpWitness.check` both Plausible harnesses assert). The two sweeps sample
  -- generated procedure lists from the shared `Properties.phaseChangedFlags`
  -- bundle, each reporting which of the phases *it* sweeps were unfaithful.
  for (name, witness) in Properties.phaseNoOpWitnesses do
    enumerate name [({ witness } : PhaseNoOpResult)]
  for p in Properties.phaseChangedFlags do
    panel p.name (genPhaseSweepProp p.name p.check (sweptPhasesFor p.name))

  -- ── Printer-expressiveness panels ───────────────────────────────────
  -- The whole-program property samples (and shrinks, since its oracle is the
  -- printer rather than the typechecker); the three witness properties enumerate
  -- their fixed input space — the six registered widths, the eighteen `Bv↔Int`
  -- operators, the widths `0..63` — scoring each element with the shared per-element
  -- check whose conjunction is the property the Plausible harnesses assert.
  panel PropertyNames.printerNoConversionError genPrinterProgramProp
  enumerate PropertyNames.printerBv128Literal
    (StrataGenerators.PrinterCoverage.factoryBvWidths.map fun w =>
      ({ width := w,
         passed := StrataGenerators.PrinterCoverage.checkBvLitPrints w } : BvLitWidthResult))
  enumerate PropertyNames.printerBvIntConversions bvIntConversionSamples
  enumerate PropertyNames.printerBvWidthAgreement bvWidthAgreementSamples

  -- ── Panels for the eight unproven Core transform passes ────────────
  -- One panel per property in the shared `Properties.unprovenTransforms` bundle
  -- (also consumed by both Plausible harnesses), for the passes in
  -- `Strata/Transform/` that carry no correctness proof. Each sample is
  -- a whole generated program, so the `programFeatures` breakdown
  -- (`num_decls`, `decl_kinds`, `program_size`, `rejection_cause`) applies
  -- unchanged, and `decl_kinds` is what makes a vacuous panel legible: a property
  -- about the axioms is uninformative on a sample that declares none.
  --
  -- Several of these panels are discriminated by shape: `s2u: every block is
  -- reachable from the entry` by whether a body holds a labelled block, `s2u: a
  -- cfg-bodied procedure prints` by whether a procedure is declared, `loop: LoopElim
  -- mints distinct block labels` by whether a loop is present, and the two
  -- `procInline` ones by the rarer samples that hold a call. So `decl_kinds` and
  -- `program_size` separate a live sample from a vacuous one on each.
  for p in Properties.unprovenTransforms do
    panel p.name (genProgramProp p.name p.check)

  -- ── ADT-law, alias-resolution and mutual-block panels ──────────────
  -- The block-based properties (`Properties.adtBlockChecks` over ordinary blocks,
  -- `Properties.mutualIndepChecks` over independent ones) sample through the block
  -- panel; the two alias properties quantify over a whole program, so they reuse
  -- `genProgramProp` unchanged — same renderer, same features, same shrinking as the
  -- `program:` panels.
  --
  -- One panel shows an honest failure: `mutual: derived functions bind every type
  -- variable they mention` is red on every sample whose `params_uniform` feature is
  -- `no`, which is exactly what that feature is there to show. The three solver-backed
  -- `adt:` properties have no panel — they are `--smt`-only `IO` actions with their own
  -- per-family tallies, like `expr: SMT/concrete eval agreement`.
  for p in Properties.adtBlockChecks do
    panel p.name (genAdtBlockProp p.name p.check)
  for p in Properties.mutualIndepChecks do
    panel p.name (genIndepBlockProp p.name p.check)
  for p in Properties.aliasChecks do
    panel p.name (genProgramProp p.name p.check)
