import StrataGenerators.Tyche
import StrataGenerators.RetryGen
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.Roundtrip
import StrataGenerators.StmtHasTypeAGen.TestSupport
-- `minimizeProcsCounterexample` lets a panel for a procedure report the smallest well-typed
-- counterexample, and not the raw draw.
-- The two properties about the boundary between a `Rat` and a `Decimal`, and the property about the
-- escape function for SMT.
import StrataGenerators.HasTypeAGen.DecimalAgreement
import StrataGenerators.HasTypeAGen.SmtStringEscaping
import StrataGenerators.AdtLaws
import StrataGenerators.MutualBlockShape
import StrataGenerators.AliasResolution
import StrataGenerators.ProcedureHasTypeAGen.Shrink
-- The whole-program generator, and `minimizeProgramCounterexample`, so that a panel for a program
-- reports the smallest well-typed counterexample and not the raw draw.
import StrataGenerators.ProgramGen
import StrataGenerators.ProgramGen.Shrink
-- The checks for the sweep over the phases and their helpers for a report, and the oracle for the
-- printer with its checks for each width and for each operator. `Properties` also imports both of
-- them. They are named here because the panels below use them directly.
import StrataGenerators.PhaseChangedFlag
import StrataGenerators.PrinterCoverage
import Basalt.IO
-- `Basalt.PlausibleGen` gives the `[Gen Plausible.Gen]` instance that the panels for a list of
-- procedures use. Those panels run the `genProcedure` generator, which backtracks, through
-- `Plausible.Gen.run`. The direct path at `G := IO` is not reliable for a procedure.
import Basalt.PlausibleGen
import Strata.DL.Lambda.LExprT
-- The imports for the property about `Function.typeCheck`.
import Strata.Languages.Core.FunctionType
import Strata.DL.Lambda.Denote.LExprAnnotated
-- The imports for the property about the round trip from the printer to the parser.
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda RandomChoice ArbNat Tyche Std Core Imperative
open Strata Strata.CoreDDM
open StrataDDM (initDialect)

/-!
# The panels for Tyche

This module draws samples from the generators of this package, and it writes them in the JSONL format of
Tyche, for a visualization. The generators are the ones for an expression, a command, a function, a
statement, a procedure and a whole program.

The module also holds a panel for each property whose set of inputs is a fixed finite set, and not a
distribution. Those inputs are the witnesses that a pipeline phase changes nothing, the bitvector widths
of the printer, and the operators between a bitvector and an integer. `Tyche.writeInto` *enumerates* such
a set, and it draws no sample.

This module holds the panels that no code can *derive*. `StrataGenerators.Test.TycheReport` derives most
panels from the `GenSpec` of a property, which carries the renderer, the shrinker and the breakdown of
the features of each input. Therefore a new property appears in Tyche with no change to this file. Two
kinds of panel remain here. The oracle of the first kind is itself an `IO` action, such as a run of a
solver or a round trip from a format to a parse. The breakdown of the second kind reports *why* a sample
failed, in terms that the generated input alone does not fix, such as which pipeline phase gave the wrong
answer, or which site in the printer refused.

`TestDecl.withPanel` attaches such a panel to its property, in the file under `StrataTests/` that
declares the property. Therefore a reader reads the panel together with the claim that it visualizes, and
no central list of the panels needs a change.

The `*.TestSupport` modules hold the *check* logic of each property, which is the verdict and the helper
contexts behind it, and the property itself scores it. This file adds the scaffolding for the
visualization only, which is the breakdown of the features and the representation of a sample.
-/

-- ── The features of a sample ─────────────────────────────────────────

/-- The depth of an `LExpr`, which is its level of nesting. -/
def exprDepth : LExpr' → Nat
  | .abs _ _ _ body => exprDepth body + 1
  | .app _ fn arg => max (exprDepth fn) (exprDepth arg) + 1
  | .ite _ c t e => max (exprDepth c) (max (exprDepth t) (exprDepth e)) + 1
  | .eq _ e₁ e₂ => max (exprDepth e₁) (exprDepth e₂) + 1
  | .quant _ _ _ _ tr body => max (exprDepth tr) (exprDepth body) + 1
  | _ => 0

/-- The size of an `LExpr`, which is its number of nodes. The function calls `LExpr.size` of Strata. -/
def exprSize (e : LExpr') : Nat := LExpr.size LExprParamsT' e

/-- The name of the constructor at the top of an expression. -/
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

/-- The name of the constructor at the top of a type. -/
def typeKind : LMonoTy → String
  | .bool => "bool"
  | .int => "int"
  | .arrow _ _ => "arrow"
  | .ftvar _ => "ftvar"
  | .bitvec _ => "bitvec"
  | .tcons _ _ => "tcons"

-- ── The property about the preservation of a type ────────────────────

/-- The result of one draw: the generation, the evaluation and the second type check. -/
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
    -- The shared `checkPreservation` gives the verdict. The field `evaledTy` holds the type that the
    -- second check infers, for the representation of the sample only.
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

-- ── The wrappers around a generator ──────────────────────────────────
--
-- Each wrapper draws the depth parameter uniformly from 1 up to 5, so that a visualization in Tyche
-- covers the whole range of the behaviour of the generator, and not one fixed depth.
--
-- Each panel for an expression below instantiates the generator at `G := IO`, so it leaves the
-- `retryCont` of `genLExpr` at its default value `id`, which retries nothing. The retry continuation
-- that `TestScaffold` gives works at `Plausible.Gen` only, because a retry needs `tryCatch`. The panels
-- that *do* go through `Plausible.Gen`, such as the one for a list of procedures below, get the outer
-- `retryGen` wrapper instead.

/-- The largest size a panel samples at.

    A panel runs outside the property loop and so receives no `RunConfig`. This mirrors
    `StrataGenerators.Test.defaultMaxSize`, which is the bound the properties themselves
    run at, so a panel shows the distribution the suite actually tested. Keep the two in
    step; a panel drawn at a size the suite never uses describes nothing the suite did. -/
def panelMaxSize : Nat := 5

/-- Randomly choose a depth between 1 and `maxDepth` (inclusive). -/
def randomDepth (maxDepth : Nat := 5) : IO Nat := do
  let r ← IO.rand 1 maxDepth
  return r

/-- Generate a closed expression, evaluate it, and check the preservation of its type. The context of the
    free variables is empty, because the property holds for that context. -/
def genAndEval (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] coreMonoOps corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  let evaledTy := LExpr.typeCheck (T := LExprParams') [] evaled
  return ⟨expr, ty, evaled, evaledTy, isValue expr, !(expr == evaled), d⟩

-- ── The property about progress under evaluation ─────────────────────

/-- The result of the check whether `LExpr.eval` makes progress on a generated term. -/
structure EvalProgressResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  generatorSize : Nat

instance : Tyche.TycheSample EvalProgressResult where
  toSample r :=
    -- The shared `checkProgress` gives the verdict. The features `made_progress` and `input_is_value`
    -- say *why* the sample satisfies the property.
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

/-- Generate a closed expression, and check whether the evaluator makes progress, or whether the input is
    already a value. The context of the free variables is empty, because the property holds for that
    context. -/
def genAndCheckProgress (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalProgressResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] coreMonoOps corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, d⟩

-- ── The property about the preservation of a free variable ───────────

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

-- ── The property about a resolve after an erasure ────────────────────
--
-- `resolveLContext`, `coreOpCtx`, `eraseAllTypes` and `isInstanceOf` come from
-- `HasTypeAGen.TestSupport`. The check in the other harness uses the same definitions, so both harnesses
-- score this property in the same way.

/-- Whether the expression holds a quantifier at any position.

    Each known counterexample to the property about a resolve after an erasure holds one. After the
    erasure of the annotation on the binder, `LExpr.resolve` gives the bound variable a fresh type
    variable. It then rejects the quantifier by a *syntactic* check that the body is not `bool`, and it
    does not unify the type of the body with `bool`. -/
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
    -- The scoring looks for a counterexample. A sample satisfies the property only when `resolve`
    -- succeeds *and* infers a type that the type of the generation is an instance of. A *failure* of
    -- `resolve` counts as a counterexample, and not as a sample that says nothing, so the Tyche panel
    -- shows such a case. The feature `failure_mode` separates the two kinds of counterexample.
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
        -- The kind of the counterexample. `resolve_failed` means that `resolve` gave an error.
        -- `wrong_type` means that `resolve` succeeded and inferred a type that is not an instance.
        -- `none` means that the sample satisfies the property.
        ("failure_mode", .nominal failureMode),
        -- Whether the counterexample holds a quantifier.
        ("has_quantifier", .nominal (if containsQuant r.expr then "yes" else "no")),
        ("inferred_more_general", .nominal (if general then "yes" else "no")),
        ("resolve_succeeded", .nominal (if r.resolvedTy.isSome then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("expr_depth", .ordinal (exprDepth r.expr)),
        ("expr_size", .ordinal (exprSize r.expr)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate one expression, erase each of its type annotations, and infer the type again with
    `LExpr.resolve`. The field `resolvedTy` is `none` when `resolve` gives an error. -/
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

-- ── The panels for a command ─────────────────────────────────────────

/-- The name of the constructor at the top of a command. -/
def cmdKind (cmd : Cmd Expression) : String :=
  match cmd with
  | .init _ _ (.det _) _ => "init_det"
  | .init _ _ .nondet _ => "init_nondet"
  | .set _ (.det _) _ => "set_det"
  | .set _ .nondet _ => "set_nondet"
  | .assert _ _ _ => "assert"
  | .assume _ _ _ => "assume"
  | .cover _ _ _ => "cover"

/-- Generate a command from a context of a random size. The value of `numCmds` is three times the size of
    the wanted context, because only an `init` command grows the context. An `assert`, an `assume`, a
    `cover` and a `set` command leave the context unchanged. -/
private def genCmdFromRandomCtx (depth : Nat := 0) : IO (Cmd Expression × VarCtx × VarCtx × Nat) := do
  let d ← if depth == 0 then randomDepth else pure depth
  let tvars : List TyIdentifier := []
  let numCmds ← IO.rand 0 8
  let (_, baseCtx) ← genCmds (G := IO) coreMonoOps tvars [] [] d numCmds
  let ⟨cmd, ctx'⟩ ← genCmd (G := IO) coreMonoOps tvars [] baseCtx d
  return (cmd, baseCtx, ctx', d)

-- ── The four command properties that give one verdict ────────────────
--
-- These four properties share one shape of a sample, which is a command, the size of its context, and a
-- verdict. Therefore one `CmdPropResult` serves each of them, and the title of the panel names the
-- property. Each check predicate takes the command and the context that generated it.
-- `checkInitFreshNotInRhs` and `checkExprTypechecks` read no context, and the other two read it.

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

/-- Generate a command from a random context, and apply a check predicate to it. -/
def genCmdProp (check : Cmd Expression → VarCtx → Bool) : IO CmdPropResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctxSize := baseCtx.length, generatorSize := d,
           passed := check cmd baseCtx }

-- ── The panel for the agreement between the two evaluators ───────────

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
        -- The value that the condition of the command reduces to. That value decides whether the
        -- symbolic evaluator and the concrete evaluator take the same branch.
        ("condition_kind", .nominal (cmdConditionKind r.cmd r.ctx)),
        ("ctx_size", .ordinal r.ctxSize),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckEvalRunAgreement : IO CmdEvalRunAgreementResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctx := baseCtx, ctxSize := baseCtx.length, generatorSize := d,
           passed := checkEvalRunAgreement cmd baseCtx }

-- ── The panels for a function ────────────────────────────────────────

/-- Whether a generated function has a body, and whether it has a measure. The panel breaks the samples
    down by these two features. The property says nothing when both are absent, so the breakdown shows how
    often a sample gives the property real content. -/
private def funcShape (func : Function) : String :=
  match func.body.isSome, func.measure.isSome with
  | true,  true  => "body+measure"
  | true,  false => "body"
  | false, true  => "measure"
  | false, false => "neither"

structure FunctionFvarsAnnotatedResult where
  func : Function
  /-- The property: each free variable of the body and of the measure holds the annotation that the type
      map of the context gives. -/
  passed : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionFvarsAnnotatedResult where
  toSample r :=
    { representation := formatFunc r.func
      status := if r.passed then .passed else .failed
      features := [
        ("fvars_annotated", .nominal (if r.passed then "yes" else "no")),
        -- Which optional subexpressions are present. These features show how often a sample gives the
        -- property real content.
        ("func_shape", .nominal (funcShape r.func)),
        ("has_body", .nominal (if r.func.body.isSome then "yes" else "no")),
        ("has_measure", .nominal (if r.func.measure.isSome then "yes" else "no")),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a `Function` with `genFunction`, against `defaultFCtx`, and check the property about the
    annotations of the free variables against the matching type map. -/
def genAndCheckFunctionFvarsAnnotated (depth : Nat := 0) : IO FunctionFvarsAnnotatedResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO defaultFCtx coreMonoOps d
  let passed := functionFvarsAnnotatedBy (fctxToTyMap defaultFCtx) func
  return { func, passed, generatorSize := d }

-- ── The soundness of `Function.typeCheck` ────────────────────────────
--
-- This panel covers a theorem of Strata that has no proof: when `Function.typeCheck` accepts a generated
-- function that satisfies the specification, its output satisfies the declarative specification
-- `FuncHasTypeA`. The context of the free variables is *empty*, so each body is closed and depends on no
-- context. `funcCheckContext` and `checkFuncHasTypeA` come from `FunctionHasTypeAGen.TestSupport`, so this
-- panel scores the property in the same way as the other harness.

structure FunctionTypeCheckSoundResult where
  func : Function
  /-- Whether `Function.typeCheck` accepted the function. -/
  accepted : Bool
  /-- Whether the output satisfies `FuncHasTypeA`, when the typechecker accepted the function. -/
  specHolds : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionTypeCheckSoundResult where
  toSample r :=
    -- A sample satisfies the property when soundness holds. Either the typechecker rejected the
    -- function, and the property then says nothing, or it accepted the function and the specification
    -- holds. A sample fails when the typechecker accepted the function and the specification does not
    -- hold.
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

/-- Generate a closed function, with an empty context of free variables, run `Function.typeCheck`, and
    record whether the typechecker accepted it and whether the output satisfies `FuncHasTypeA`. -/
def genAndCheckFunctionTypeCheckSound (depth : Nat := 0) : IO FunctionTypeCheckSoundResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreMonoOps d
  match Function.typeCheck funcCheckContext TEnv.default func with
  | .ok (func', _) =>
    return { func := func', accepted := true, specHolds := checkFuncHasTypeA func', generatorSize := d }
  | .error _ =>
    return { func, accepted := false, specHolds := true, generatorSize := d }

-- ── The completeness of the typechecker ──────────────────────────────
--
-- This panel is the dual of the panel for soundness above. `genFunction` has a proof of soundness, so
-- `Function.typeCheck` must accept each generated function. It does not accept each one: the
-- specification permits a measure with no body, and the algorithm rejects such a function. Therefore a
-- function that the typechecker rejects counts as a counterexample here, and the feature
-- `measure_no_body` shows the cause. The panel uses the predicates over the full Core factory from the
-- shared module for a statement, so no operator fails to resolve for a false reason. The representation
-- names the body and the measure, because the printer omits an absent body and an absent measure.
open StrataGenerators.Stmt.TestSupport in
structure FunctionTypeCheckCompleteResult where
  func : Function
  accepted : Bool
  generatorSize : Nat

open StrataGenerators.Stmt.TestSupport in
instance : Tyche.TycheSample FunctionTypeCheckCompleteResult where
  toSample r :=
    -- A sample satisfies the property when the typechecker accepts the function, which the
    -- specification already accepts. A rejection is a counterexample, and it is a true gap in
    -- completeness.
    let measNoBody := funcMeasureWithoutBody r.func
    { representation := s!"[body={r.func.body.isSome}, measure={r.func.measure.isSome}]\n{formatFunc r.func}"
      status := if r.accepted then .passed else .failed
      features := [
        ("typecheck_accepted", .nominal (if r.accepted then "yes" else "no")),
        -- The known gap: the typechecker rejects a function that has a measure and no body.
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
/-- Generate a closed function, and record whether `Function.typeCheck` accepts it in the full context of
    Strata Core. -/
def genAndCheckFunctionTypeCheckComplete (depth : Nat := 0) : IO FunctionTypeCheckCompleteResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreMonoOps d
  return { func, accepted := checkFunctionTypeCheckerComplete func, generatorSize := d }

-- ── The round trip from the printer to the parser ────────────────────
--
-- This panel puts a generated function into a `Program`, formats it with `Core.formatProgram`, parses the
-- output again with DDM, formats the result again, and compares the two strings. A failure of the parse
-- counts as a counterexample, because `genIdentName` gives a legal Core identifier by construction.
-- Therefore output that a parser cannot read is a defect of the printer or of the parser.
--
-- `formatFuncAsProgram`, `parseCoreProgram`, `parseCoreProgramErr`, the structural shrinker and the
-- predicates for a failure come from `StrataGenerators.FunctionHasTypeAGen.Roundtrip`. The property that
-- scores this claim uses the same definitions.

/-- A short kind for an error message of the parser, which does not depend on a position. The Tyche panel
    groups the samples by this value. The function removes the prefix `Parse errors:` and the location, so
    that each message of one kind falls into one group, at each position in the input. -/
private def parseErrorKind (msg : String) : String :=
  -- Remove each character up to the last location marker of the form `N:M:`, and that marker too.
  let afterLoc := (msg.splitOn ": ").reverse.headD msg
  let core := afterLoc.trimAscii
  (core.take 45).toString

structure FunctionRoundtripResult where
  func : Function
  /-- Whether the parser read the printed function again. -/
  parsed : Bool
  /-- Whether the format, the parse and the second format give the first output again. -/
  roundtripped : Bool
  /-- The message of the parser after a failure. The value is the empty string after a success. -/
  parseError : String
  generatorSize : Nat

instance : Tyche.TycheSample FunctionRoundtripResult where
  toSample r :=
    -- A sample satisfies the property when the parser reads the printed function again *and* the round
    -- trip gives the same output. A failure of the parse is a counterexample, and not a sample that says
    -- nothing. `genIdentName` gives a legal Core identifier by construction, so output that is legal and
    -- that a parser cannot read is a true defect of the printer or of the parser.
    let passed := r.parsed && r.roundtripped
    -- Show the exact string that the round trip used, which is the output of `Core.formatProgram`. The
    -- panel is therefore an exact reproducer of a failure.
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

/-- Build a `FunctionRoundtripResult` for one function. -/
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
  -- After a failure of the round trip, shrink the function to a smallest witness and report that witness.
  -- The `representation` of the Tyche panel then shows the smallest reproducer. The code computes the
  -- features and the reason for the status again, on the shrunk function.
  if ← failsRoundtrip func then
    let minF ← shrinkWhile failsRoundtrip 1000 func
    mkRoundtripResult minF d
  else
    mkRoundtripResult func d

-- ── The preservation of a type under the evaluator ───────────────────
--
-- This panel covers the theorems of Strata about the preservation of a type under one step and under many
-- steps. It evaluates the body of a generated function, and it checks that the result still type checks at
-- the declared output type. The shared `checkFunctionBodyPreservation` gives the verdict.

structure FunctionBodyPreservationResult where
  func : Function
  /-- Whether the function has a body. The property has real content only then. -/
  hasBody : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionBodyPreservationResult where
  toSample r :=
    -- A sample satisfies the property when the function has no body, and the property then says nothing,
    -- or when the evaluator keeps the type of the body.
    let passed := checkFunctionBodyPreservation r.func
    -- Whether the evaluator kept the output type, when the function has a body.
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

/-- Generate a closed function, evaluate its body if it has one, and check that the result still type
    checks at the declared output type. -/
def genAndCheckFunctionBodyPreservation (depth : Nat := 0) : IO FunctionBodyPreservationResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreMonoOps d
  return { func, hasBody := func.body.isSome, generatorSize := d }

-- ── The round trip of an identifier with a special character ─────────
--
-- This panel isolates one *legal* identifier that holds a character which is not alphanumeric.
-- `genQuotedName` draws such a name: it starts with a letter, an underscore or a `$`, and its interior
-- can hold one of `. ' | \ ? ! @`. The panel puts that identifier at one syntactic position inside a
-- function that is trivial in each other part. That position is the name of the function, a type
-- argument or a binder. Therefore a failure is a smallest reproducer. Each generated name is a legal
-- Core identifier by construction, so a failure is a true defect of the printer or of the parser, and
-- not an artefact of the generator. `IdentPosition` and `minimalFuncWithName` come from
-- `FunctionHasTypeAGen.TestSupport`.

/-- The class of the character of the identifier that most probably caused a failure. The panel groups the
    samples by this feature, so that two different causes stay separate. -/
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
  /-- Whether the parser read the printed function again. That function holds one identifier. -/
  parsed : Bool
  /-- When parsed, whether format→parse→re-format is a fixed point. -/
  roundtripped : Bool
  /-- On parse failure, the parser's diagnostic message (else ""). -/
  parseError : String
  rendered : String

instance : Tyche.TycheSample IdentProbeResult where
  toSample r :=
    -- A sample satisfies the property when the parser reads the identifier again *and* the round trip
    -- gives the same output. A failure of the parse is a counterexample, because the name is a legal Core
    -- identifier, and output that a parser cannot read is a defect of the printer or of the parser.
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

/-- Draw an adversarial identifier, put it at a random position, and record whether that one identifier
    survives the round trip. -/
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

-- ── The panels for a statement ───────────────────────────────────────
--
-- These panels visualize the six properties about a statement transform and about the typechecker. Each
-- one runs on a well-typed statement list from `genProgramStmts`, which has a proof of soundness and of
-- completeness against `StatementsHasTypeA`. The `check*` predicates and the measurements come from
-- `StrataGenerators.StmtHasTypeAGen.TestSupport`, and the property that scores each claim uses the same
-- definitions.

open StrataGenerators.Stmt.TestSupport

/-- The features of a statement list that each panel for a statement uses. They are the structural
    breakdown, which is the size and the count of each kind, together with the size of the generator. -/
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

/-- Render a statement list for a Tyche panel with the formatter of Strata, which gives real Core concrete
    syntax. The function appends a summary of the form `funcDecl[body=…, measure=…]`, because the formatter
    cannot write a `funcDecl` statement with no body, and it puts a dummy body there instead. That shape is
    exactly the counterexample to completeness. -/
def stmtRepr (ss : List Statement) : String :=
  let shapes := funcDeclShapesList ss
  let suffix := if shapes.isEmpty then "" else s!"\n-- {" ".intercalate shapes}"
  formatStmts ss ++ suffix

/-- Generate one well-typed statement list in `IO` for the Tyche panels. Draws the nesting
    and the length from one size, as `TestScaffold.genStmtsWith` does, so the panel shows
    the shapes the gating property saw. -/
def genStmtsForTyche : IO (List Statement × Nat) := do
  let d ← max 1 <$> IO.rand 0 panelMaxSize
  let len := d
  let ss ← genProgramStmtsIO d len
  return (ss, d)

-- ── The panel for the definedness of `StmtToKleeneStmt` ──────────────
--
-- This panel also records *why* the transform is defined or is not defined. A reader can therefore read
-- the contract for definedness from the panel.

structure KleeneDefinedResult where
  stmts : List Statement
  defined : Bool
  genSize : Nat

instance : Tyche.TycheSample KleeneDefinedResult where
  toSample r :=
    let unsupported := hasKleeneUnsupported r.stmts
    let invLoop := hasInvLoopStmts r.stmts
    -- A sample satisfies the property when the definedness agrees with the contract in the docstring.
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

-- ── The panels for a procedure and a transform pass ──────────────────
--
-- This section holds the sampler and the renderer for a list of procedures, which the panel for the sweep
-- over the phases uses. `Gens.procs` derives the panel of each `proc:` property, because the renderer and
-- the axes of such a panel are exactly `procsRepr` and `procListFeatures` here. What remains in this
-- section is what a derivation cannot express. The two panels about a `changed` flag separate the samples
-- that concern that flag. For the property about the flag of `FilterProcedures`, those samples are the ones
-- where the pass removes nothing. For the property about the flag of `PrecondElim`, they are the rarer ones
-- where the body of a declared function calls a partial function, and the pass inserts a `$$wf` block.

open StrataGenerators.Procedure.TestSupport in
/-- The structural features of an assembled program of procedures. They are the number of the procedures,
    and the total size of the bodies of each procedure. -/
private def procListFeatures (ps : List Core.Procedure) (genSize : Nat) :
    List (String × Tyche.Feature) :=
  let bodyLen (p : Core.Procedure) := (bodyStmts p.body).length
  [ ("num_procs", .ordinal ps.length),
    ("total_body_stmts", .ordinal (ps.foldl (fun n p => n + bodyLen p) 0)),
    ("generator_size", .ordinal genSize) ]

open StrataGenerators.Procedure.TestSupport in
/-- Render an assembled program of procedures with the formatter of Strata. -/
def procsRepr (ps : List Core.Procedure) : String :=
  let prog : Core.Program := { decls := ps.map (Core.Decl.proc · .empty) }
  (Core.formatProgram prog).pretty

/-- A generated list of procedures, with the verdict of one property and the name of that property. One
    structure serves each procedure property that gives a `Bool`, and the title of the panel names the
    property.

    The fields `diagnostic` and `extraFeatures` let one panel append detail of its own to the uniform
    rendering of the program. They exist for a property whose cause of a failure is not *in* the program.
    Read `procFactoryStrippedDiagnostic`. Both fields are empty by default, so each other panel needs no
    change. -/
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
    `Gen.run` on the same `retryGen` wrapper the gating property uses (the
    The direct path at `G := IO` is not reliable, because a nested sub-generator reaches a fallback for an
    empty support. Therefore this function runs the `Plausible.Gen` interpretation, which retries, at a
    random size. It also renames each procedure to `P0` up to `Pk`, so that no two names collide.

    The function follows `TestScaffold.genProcsWith`. The procedures form an acyclic graph of calls, and
    the generator makes the body of each procedure against the monomorphic procedures before it. Therefore
    each panel sees a program with real edges in its call graph. -/
def genProcsForTyche : IO (List Core.Procedure × Nat) := do
  let genSize ← IO.rand 0 panelMaxSize
  let n := max 2 genSize
  let size := max 1 genSize
  let len := max 1 genSize
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
/-- Build a `ProcPropResult`. The function generates a list of procedures, and it applies a check predicate
    under the given tag.

    After a *failure* of the property, `minimizeProcsCounterexample` first minimizes the list. Therefore
    the `representation` of the panel shows the smallest well-typed reproducer, and not the raw program.
    `genAndCheckFunctionRoundtrip` uses the same pattern of a shrink and then a report. The function
    computes the features again from the minimized list, so each feature describes the program on the
    screen.

    The minimized list still fails the check, because the minimizer keeps only a candidate that fails it.
    It is also still well typed, because each candidate passes `procsTypeCheck`. Therefore the verdict does
    not change, and only the witness becomes smaller. For a sample that satisfies the property, the
    function reports the list as generated, because there is nothing to minimize. -/
def genProcProp (tag : String) (check : List Core.Procedure → Bool) : IO ProcPropResult := do
  let (ps, d) ← genProcsForTyche
  if check ps then
    return { procs := ps, passed := true, genSize := d, tag }
  else
    return { procs := minimizeProcsCounterexample check 200 ps, passed := false, genSize := d, tag }

open StrataGenerators.Procedure.TestSupport in
/-- Render each factory entry that causes a failure of the `factoryStripped` panel. Such an entry is an
    entry of the output factory that still holds a precondition. The rendering gives its formatted
    preconditions, and whether the program declared it.

    This panel needs a representation of its own, because the cause is not in the program at all. The
    shrinker therefore minimizes the program to the empty one, and the formatted program reads as
    `program Core;`, with nothing about the cause. The entries are the evidence, so this function prints
    them.

    The rendering groups the entries by the field `declared`, to keep the two independent causes visually
    apart. It also truncates the list of the entries that come from the builtin factory, because that list
    is long and uniform. The rendering always gives the full count. -/
def procFactoryStrippedDiagnostic (ps : List Core.Procedure) : String :=
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

-- ── The panels for a whole program ───────────────────────────────────
--
-- This section holds the sampler for a whole program and the breakdown of its features.
-- `programFeatures` also appears as the feature function of `Gens.program`, which gives the axes of each
-- derived `program:` panel. The copy here supports the panel for the printer below, whose verdict is an
-- `IO` computation and which no code can therefore derive.
--
-- For the panel about the acceptance of a program by the typechecker, the typechecker rejects a large part
-- of the draws, for one of three known causes. The feature `rejection_cause` below separates those three
-- causes, so the panel does not show one undifferentiated block. The shrinker cannot minimize such a
-- rejection, because its oracle is the checker under test. Therefore the feature `num_decls` of a rejected
-- sample gives the size of the draw, and not a smaller size.

open StrataGenerators.Program.TestSupport in
/-- The structural features of a generated program. They are the number of the declarations, the reducible
    size, the kinds of the declarations that the program holds, and the known gap that the program holds,
    if it holds one. That last feature separates the samples of the panel for completeness. -/
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

/-- Generate a whole program at `IO`, for the Tyche panels, through `ProgramGen.sample`. That function
    runs the generator through the `Plausible.Gen` interpretation, which retries, because the direct path
    at `G := IO` is not reliable. The docstring of `ProgramGen.sample` records that fact. This function
    uses the same limits as `TestScaffold.genProgramWith`. -/
def genProgramForTyche : IO (Core.Program × Nat) := do
  let genSize ← IO.rand 0 panelMaxSize
  let numDecls := max 2 genSize
  let prog ← ProgramGen.sample numDecls {} 30000 genSize
  return (prog, genSize)

-- ── The panels for the `changed` flag of a pipeline phase ────────────
--
-- Read `StrataGenerators.PhaseChangedFlag`. The properties have two shapes, and so do the panels:
--
--   * The two witnesses that a phase changes nothing take no generated input. Each of them is one
--     program that a person wrote, and one phase provably changes nothing on it. Therefore the panel of
--     each witness *enumerates* that one witness, and it draws no sample. A thousand draws would give a
--     thousand identical marks.
--   * The two sweeps quantify over a generated list of procedures. Therefore they draw samples, as a
--     `proc:` panel does, and the phases that break the contract are the feature that separates the
--     samples.
--
-- The first three properties separate the four sites that set `changed := true` as a literal. The property
-- about each other phase is the guard against a change, so one mark in its panel is the interesting event.

open StrataGenerators.PhaseChangedFlag in
/-- One witness that a phase changes nothing. The shared `NoOpWitness.check` gives the verdict. The flag
    that the phase reports and the flag that describes its true effect both come from the same
    `phaseOutcome` that the check reads. Therefore the panel cannot show a flag other than the one that it
    scored. -/
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
        -- The flag that the phase reports, beside its true effect. The whole content of the finding is
        -- that the two disagree.
        ("reported_changed", .nominal (flag (outcome.map (·.1)))),
        ("program_changed", .nominal (flag (outcome.map (·.2)))),
        ("num_decls", .ordinal r.witness.prog.decls.length) ] }

open StrataGenerators.PhaseChangedFlag in
/-- A generated list of procedures, together with a list of phases that a sweep runs over it, the verdict of
    that sweep, and the labels of the phases that break the contract.

    The fields `violatingPhases` and `diagnostic` make a failed mark readable. As in the `factoryStripped`
    panel, the cause of a failure is not *in* the program. Each phase of `allCorePhases` sees the same
    program, and two of those phases report `changed = true` on each program. Therefore the minimized
    witness is nearly empty, and the program alone says nothing about which phase reported the wrong
    flag. -/
structure PhaseSweepResult where
  procs : List Core.Procedure
  passed : Bool
  genSize : Nat
  tag : String
  /-- The label of each phase of the sweep whose flag disagrees with its effect, with no duplicate. -/
  violatingPhases : List String
  /-- The number of the phases that this property sweeps, as context for the count above. -/
  numSwept : Nat
  /-- The detail for each such phase, from the shared `phaseChangedFlagDiagnostic`. -/
  diagnostic : String
  /-- Whether the program holds a loop, which is to say whether the sweep skipped `symbolicEval` on this
      sample and did not score it. -/
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
        -- Which phases reported the wrong flag on this sample. Over the full sweep, this feature should
        -- always give the known set. A *new* label here is the change that the property exists to catch.
        ("violating_phases", .nominal
          (if r.violatingPhases.isEmpty then "none"
           else " ".intercalate r.violatingPhases)),
        ("num_phases_swept", .ordinal r.numSwept),
        -- The sweep skips `symbolicEval` on a program with a loop, and it scores nothing there. A `yes`
        -- here therefore marks a sample that says nothing about that one phase.
        ("symbolic_eval_skipped", .nominal (if r.hasLoop then "yes" else "no")) ] }

open StrataGenerators.Procedure.TestSupport StrataGenerators.PhaseChangedFlag in
/-- Build a `PhaseSweepResult`. The function generates a list of procedures, scores it with the shared
    check for a sweep, and records which of the phases break the contract.

    The generation and the minimization are the ones of `genProcProp`, so this panel draws from the same
    distribution as a `proc:` panel. The function computes the list of the phases again, from the list of
    procedures that the panel displays, which can be a minimized one. Therefore the diagnostic always
    describes the program on the screen. -/
def genPhaseSweepProp (tag : String) (check : List Core.Procedure → Bool)
    (phases : List NamedPhase) : IO PhaseSweepResult := do
  let r ← genProcProp tag check
  let prog := mkProgram r.procs
  return { procs := r.procs, passed := r.passed, genSize := r.genSize, tag,
           violatingPhases := violators phases prog,
           numSwept := phases.length,
           diagnostic := phaseChangedFlagDiagnostic phases prog,
           hasLoop := programHasLoop prog }

-- ── The panels for the coverage of the printer ────────────────────────
--
-- Read `StrataGenerators.PrinterCoverage`.
--
-- The three panels for a witness *enumerate* a fixed finite set of inputs, and they draw no sample. Those
-- sets are the registered bitvector widths, the eighteen operators between a bitvector and an integer, and
-- the widths from 0 up to 63. Each panel scores each element with the shared check for one element, and the
-- conjunction of those checks *is* the property. Therefore a panel shows the shape of the gap, which is
-- which widths and which directions, and the one `Bool` of the property can report only that a gap exists.

/-- Whether `n` is a power of two. The panels record this feature, because a reader expects the printable
    widths to be exactly the powers of two, and they are not. The widths 2, 4 and 128 are powers of two that
    the printer does not write. The panel shows that fact. -/
private def isPowerOfTwo (n : Nat) : Bool := n != 0 && (n &&& (n - 1)) == 0

/-- A generated whole program, with the verdict of the oracle for the coverage of the printer. That oracle
    says that the printer wrote no error about a conversion. -/
structure PrinterProgramResult where
  prog : Core.Program
  passed : Bool
  genSize : Nat
  /-- The different lines of an error about a conversion that belong to Strata, with no duplicate. -/
  errorLines : List String
  /-- Whether the parser reads the text that the printer gave. The value is `none` when the printer wrote
      no error, because there was then no question to ask. -/
  reparsedDespiteError : Option Bool

open StrataGenerators.PrinterCoverage in
instance : Tyche.TycheSample PrinterProgramResult where
  toSample r :=
    -- Show the *whole* output of the printer, together with the block of the errors. That block is the
    -- evidence, and the text of the program above it holds the placeholders that the block explains.
    { representation := (Core.formatProgram r.prog).pretty
      status := if r.passed then .passed else .failed
      statusReason := " ".intercalate r.errorLines
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        ("num_error_sites", .ordinal r.errorLines.length),
        -- Which functions of the printer failed, such as `lconstToExpr` or `handleUnaryOps`. The panel
        -- groups the samples by the site, and not by the message, so that one gap at two widths reads as
        -- one gap.
        ("error_sites", .nominal
          (if r.errorLines.isEmpty then "none"
           else " ".intercalate (r.errorLines.map errorSite).eraseDups)),
        -- **The dangerous case.** A program for which the printer wrote an error, and whose output the
        -- parser still reads, is a program where a placeholder gave a *different* program in silence. A
        -- round trip over a string cannot find that case, and that is why this property exists beside the
        -- property about a round trip.
        ("silently_different", .nominal (match r.reparsedDespiteError with
          | some true => "yes" | some false => "no" | none => "—")),
        ("reparsed", .nominal (match r.reparsedDespiteError with
          | some true => "yes" | some false => "no" | none => "—"))
      ] ++ programFeatures r.prog r.genSize }

open StrataGenerators.Program.TestSupport StrataGenerators.PrinterCoverage in
/-- Generate a whole program, and score it with the shared oracle for the printer.

    The function first minimizes a draw that fails, as `genProgramProp` does. Such a failure *does* shrink,
    unlike a rejection by the typechecker. The oracle here is the printer, and not the typechecker that the
    shrinker uses to keep each candidate well typed. Therefore a smaller program that the printer cannot
    write passes the filter of the shrinker. The panel therefore shows a smallest such program, and the
    function computes the lines of the errors and the verdict of the parse again from it.

    Read the feature `error_sites` with that in mind. It gives the site that the *smallest* witness blames,
    and not the site that fails most often over the raw draws. A shrink keeps one of several independent
    gaps, and it drops the others. `printerErrorDiagnostic`, which has no guard, gives the count over each
    sample. -/
def genPrinterProgramProp : IO PrinterProgramResult := do
  let (raw, d) ← genProgramForTyche
  let passed := checkProgramPrintsWithoutError raw
  let prog :=
    if passed then raw
    else minimizeProgramCounterexample checkProgramPrintsWithoutError 400 raw
  let errorLines := programErrorLines prog
  -- Ask the parser only when the printer wrote an error. A `no` here is the ordinary case, and a `yes` is
  -- the case where the output is a different program. With no error there is no question to ask.
  let reparsedDespiteError ←
    if errorLines.isEmpty then pure none
    else pure (some (← parseCoreProgram (printedText (Core.formatProgram prog).pretty)).isSome)
  -- The field `passed` describes `prog`. A minimization gives back only a candidate that still fails the
  -- check, so the verdict does not change.
  return { prog, passed, genSize := d, errorLines, reparsedDespiteError }

/-- One width of a bitvector literal, with the verdict of the shared check for one width. That check at the
    width 128 *is* `checkBv128LiteralPrints`. -/
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
        -- The width that the property of this panel is about. It is the *only* registered width that
        -- fails, so the gap is an omission and not a boundary of the design. A reader sees that only beside
        -- the other widths.
        ("pinned_by_property", .nominal (if r.width == 128 then "yes" else "no"))
      ] }

/-- One conversion operator between a bitvector and an integer, with the verdict of the shared check for one
    operator. The conjunction of that check over each of the eighteen operators *is*
    `checkBvIntConversionsPrint`. -/
structure BvIntConversionResult where
  op : String
  width : Nat
  /-- Which of the three registered directions this operator has. -/
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
        -- The gap covers the whole family, which is each direction at each width. A split of the panel by
        -- these two features shows that fact, and not one block of eighteen failures.
        ("direction", .nominal r.direction)
      ] }

/-- The label of each of the three conversion directions, in the order that
    `PrinterCoverage.bvIntConversionOps` gives. -/
private def conversionDirections : List String := ["bv_to_int", "bv_to_uint", "int_to_bv"]

-- The `zip` below drops an operator in silence if the two lists have different lengths, and the panel
-- would then understate the gap.
#guard (StrataGenerators.PrinterCoverage.bvIntConversionOps 8).length
         == conversionDirections.length

open StrataGenerators.PrinterCoverage in
/-- Each registered conversion operator between a bitvector and an integer, with its own verdict. -/
def bvIntConversionSamples : List BvIntConversionResult :=
  factoryBvWidths.flatMap fun w =>
    ((bvIntConversionOps w).zip conversionDirections).map fun (op, direction) =>
      { op, width := w, direction, passed := checkBvIntConversionPrints op }

/-- One bitvector width at a *type* position, with the verdict of the shared implication for one width. That
    implication says that the printer writes each width that the typechecker accepts. Its conjunction over
    the widths from 0 up to 63 *is* `checkAllWidthsAgree`. -/
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
        -- Read these two features together. The pair `typechecks = yes, prints = no` is the disagreement,
        -- and it holds for most of the first 64 widths.
        ("typechecks", .nominal (if r.typechecks then "yes" else "no")),
        ("prints", .nominal (if r.prints then "yes" else "no")),
        -- A reader expects the printable set to be exactly the powers of two. A group by this feature
        -- shows that it is not, because the widths 2, 4 and 128 fail.
        ("power_of_two", .nominal (if isPowerOfTwo r.width then "yes" else "no")),
        ("factory_registered", .nominal
          (if factoryBvWidths.contains r.width then "yes" else "no"))
      ] }

open StrataGenerators.PrinterCoverage in
/-- The widths from 0 up to 63, each with its own verdict. `checkAllWidthsAgree` takes the conjunction over
    the same range. -/
def bvWidthAgreementSamples : List BvWidthAgreementResult :=
  (List.range 64).map fun w =>
    { width := w, typechecks := widthTypeChecks w, prints := widthPrintsCleanly w,
      passed := checkWidthTypeCheckPrinterAgreement w }

-- ── The panel for the escape function of SMT ─────────────────────────
--
-- Each sample is one string from `genInterestingString`, which the panel serializes through
-- `Strata.SMTDDM.termToString`. That function is the real path to the solver. A sample satisfies the
-- property when each character of the emitted literal is printable ASCII, which is what SMT-LIB 2.6 and
-- later require.

/-- One sample for the property about the SMT escape function. -/
structure EscapingResult where
  /-- The drawn string. -/
  s : String
  /-- Whether the emitted literal holds only printable ASCII. -/
  passed : Bool
  /-- The codepoints that reach the literal without an escape. -/
  offenders : List Nat

/-- The highest codepoint of `s`, and `0` for the empty string. This feature separates a sample that
    satisfies the property from a counterexample, because the escape function stops at U+00A1. -/
private def maxCodepoint (s : String) : Nat :=
  s.toList.foldl (fun acc c => max acc c.toNat) 0

/-- The number of UTF-8 bytes that `c` needs. A raw UTF-8 byte in the literal makes a solver measure the
    number of the bytes, where Lean counts one codepoint. -/
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
        -- Whether the string holds a character outside ASCII. A sample with `no` here satisfies the
        -- property for a trivial reason, so this feature separates a real sample from such a one.
        ("has_non_ascii", .nominal
          (if r.s.toList.any (fun c => c.toNat ≥ 0x80) then "yes" else "no"))
      ] }

/-- Draw one string and record whether its SMT-LIB literal is printable ASCII. -/
def genEscapingSample : IO EscapingResult := do
  let s ← StrataGenerators.PrimitiveGens.genInterestingString (G := IO)
  return { s := s,
           passed := StrataGenerators.SmtStringEscaping.escapedIsPrintableAscii s,
           offenders := StrataGenerators.SmtStringEscaping.offendingCodepoints s }

-- ── The panels for the boundary between a `Rat` and a `Decimal` ──────
--
-- These are two properties about the representation of a real number in the dialect of SMT. Each sample is
-- a pair of two `Decimal` spellings of **one** rational value, from `genSameValuePair`. Therefore each
-- sample is a case that must satisfy the property, and each counterexample is a true defect and not an
-- artefact of the draw.

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
def genDecimalPairProp
    (check : StrataDDM.Decimal → StrataDDM.Decimal → Bool) : IO DecimalPairResult := do
  let (d₁, d₂) ← StrataGenerators.DecimalAgreement.genSameValuePair (G := IO)
  return { d₁ := d₁, d₂ := d₂,
           passed := check d₁ d₂,
           eqFold := StrataGenerators.DecimalAgreement.actualEqFold d₁ d₂,
           lt₁ := Strata.SMT.TermPrim.lt (.real d₁) (.real d₂),
           lt₂ := Strata.SMT.TermPrim.lt (.real d₂) (.real d₁) }

-- ── The panels for the laws of an ADT and for a mutual block ─────────
--
-- Each `adt:` property and each `mutual:` property quantifies over a generated `mutual … end` block, and
-- not over a program. Therefore they need a sample type of their own. The features are the ones that
-- separate a sample with real content from a sample with none. They are the number of the datatypes in the
-- block, because a `mutual:` property says nothing below two, whether the type parameters of the datatypes
-- agree, which is the condition that `elimFuncs` assumes and the feature that separates the failure about
-- the scope of an eliminator, whether one datatype of the block references another, whether Strata accepted
-- the block, and whether the block passed the screen for safety under SMT that the law properties behind the
-- `--smt` gate apply.

-- ── A panel belongs to its property, and not to a list here ──────────
--
-- This module holds no central function that registers each panel. `StrataGenerators.Test.TycheReport`
-- *derives* a panel from the `GenSpec` of a property, because that structure holds the renderer, the
-- shrinker and the breakdown of the features. `TestDecl.withPanel` attaches each richer panel above to its
-- property, in the file under `StrataTests/` that declares it.
--
-- The generators above are therefore the panels that no code can derive. Each of them has an oracle at `IO`,
-- such as a run of a solver or a round trip from a format to a parse, or a breakdown of the cause of a
-- failure that the generated input alone does not fix. A panel that is a renderer, a verdict and the
-- features of each input is derived, because a `GenSpec` already holds those three.
