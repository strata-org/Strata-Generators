import StrataGenerators.Tyche
import StrataGenerators.HasTypeAGen.TestSupport
import Basalt.IO

open Lambda RandomChoice ArbNat Tyche Std

/-!
# Tyche Visualization Runner

This executable generates samples from the `HasTypeA` generator and writes
them in Tyche JSONL format for visualization.

## Usage

```
lake build tyche-viz && .lake/build/bin/tyche-viz [numSamples] [outputPath]
```

Then open the output file with the Tyche VS Code extension (`Tyche: Open`).
-/

-- ── Pretty-printing ──────────────────────────────────────────────────
-- These differ from Strata's built-in `ToFormat LMonoTy` / `ToFormat (LExpr T)`:
--   • Types: arrows print as `α -> bool` instead of `(arrow α bool)`.
--     Higher-order function arguments are parenthesized appropriately, e.g.
--     `(int -> int) -> bool` (since the function arrow is right-associative by default)
--   • Exprs: precedence-based parenthesization instead of wrapping every
--     compound subexpression in parens. Binder bodies extend to the right
--     without extra parens (`λint. λint. #1`), and application is left-
--     associative (`f x y` means `(f x) y`; only compound arguments like
--     lambdas or if-then-else get wrapped).

-- ppType and ppExpr are imported from TestSupport

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
  | .const _ _ => "const"
  | .quant _ _ _ _ _ _ => "quant"

/-- Classify the top-level type constructor. -/
def typeKind : LMonoTy → String
  | .bool => "bool"
  | .int => "int"
  | .arrow _ _ => "arrow"
  | .ftvar _ => "ftvar"
  | .bitvec _ => "bitvec"
  | .tcons _ _ => "tcons"

/-- A generated expression paired with its type and the depth (size parameter to the generator) used to generate it, ready for Tyche. -/
structure TypedExpr where
  expr : LExpr'
  ty : LMonoTy
  generatorSize : Nat
instance : Tyche.TycheSample TypedExpr where
  toSample te :=
    { representation := ppExpr te.expr
      features := [
        ("depth", .ordinal (exprDepth te.expr)),
        ("LExpr.size", .ordinal (exprSize te.expr)),
        ("expr_kind", .nominal (exprKind te.expr)),
        ("type_kind", .nominal (typeKind te.ty)),
        ("type_depth", .ordinal (monoTyDepth te.ty)),
        ("generator_size", .ordinal te.generatorSize)
      ] }

/-- A generated monotype, ready for Tyche. -/
instance : Tyche.TycheSample LMonoTy where
  toSample ty :=
    { representation := ppType ty
      features := [
        ("depth", .ordinal (monoTyDepth ty)),
        ("type_kind", .nominal (typeKind ty))
      ] }

-- ── Typecheck property ────────────────────────────────────────────────

/-- Result of generating an expression and running the typechecker on it. -/
structure TypeCheckResult where
  expr : LExpr'
  expectedTy : LMonoTy
  actualTy : Option LMonoTy
  generatorSize : Nat

/-- The typecheck property passes when `LExpr.typeCheck [] expr = some expectedTy`. -/
instance : Tyche.TycheSample TypeCheckResult where
  toSample r :=
    let passed := r.actualTy == some r.expectedTy
    let statusStr := if passed then "pass" else "fail"
    { representation := s!"{ppExpr r.expr} : {ppType r.expectedTy}"
      status := if passed then .passed else .failed
      features := [
        ("typecheck_result", .nominal statusStr),
        ("expected_type_kind", .nominal (typeKind r.expectedTy)),
        ("exprDepth", .ordinal (exprDepth r.expr)),
        ("LExpr.size", .ordinal (exprSize r.expr)),
        ("exprKind", .nominal (exprKind r.expr)),
        ("monoTyDepth", .ordinal (monoTyDepth r.expectedTy)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

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
    let preserved := r.evaledTy == some r.expectedTy
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

/-- Generate a typed expression with free variables from `defaultFCtx`. -/
def genTypedExpr (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO TypedExpr := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) defaultFCtx coreOpCtx corePolyOps tvars [] d ty
  return ⟨expr, ty, d⟩

/-- Generate just a monotype. -/
def genType (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO LMonoTy := do
  let d ← if depth == 0 then randomDepth else pure depth
  genLMonoTy (G := IO) tvars d

/-- Generate an expression and typecheck it against the expected type. -/
def genAndTypeCheck (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO TypeCheckResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) defaultFCtx coreOpCtx corePolyOps tvars [] d ty
  let actualTy := LExpr.typeCheck (T := LExprParams') [] expr
  return ⟨expr, ty, actualTy, d⟩

/-- Generate a closed expression, evaluate it, and check type preservation.
    Uses empty fctx since preservation is stated for the empty context. -/
def genAndEval (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] coreOpCtx corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  let evaledTy := LExpr.typeCheck (T := LExprParams') [] evaled
  return ⟨expr, ty, evaled, evaledTy, isValue expr, !(expr == evaled), d⟩

-- ── Eval progress property ───────────────────────────────────────────

/-- Result of checking whether `LExpr.eval` makes progress on a generated term. -/
structure EvalProgressResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  madeProgress : Bool
  inputIsValue : Bool
  generatorSize : Nat

instance : Tyche.TycheSample EvalProgressResult where
  toSample r :=
    let status := if r.madeProgress || r.inputIsValue then Tyche.Status.passed
                  else .failed
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status
      features := [
        ("made_progress", .nominal (if r.madeProgress then "yes" else "no")),
        ("input_is_value", .nominal (if r.inputIsValue then "yes" else "no")),
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
  let expr ← genLExprWithOps (G := IO) [] coreOpCtx corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, !(expr == evaled), isValue expr, d⟩

-- ── Fvar preservation property ───────────────────────────────────────

structure FvarPreservationResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  fvarsPreserved : Bool
  genDepth : Nat

instance : Tyche.TycheSample FvarPreservationResult where
  toSample r :=
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status := if r.fvarsPreserved then .passed else .failed
      features := [
        ("fvars_preserved", .nominal (if r.fvarsPreserved then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("gen_depth", .ordinal r.genDepth)
      ] }

def genAndCheckFvarPreservation (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO FvarPreservationResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) defaultFCtx coreOpCtx corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  let inputFvars := LExpr.collectFvarNames expr
  let outputFvars := LExpr.collectFvarNames evaled
  let preserved := outputFvars.all (· ∈ inputFvars)
  return ⟨expr, ty, evaled, preserved, d⟩

-- ── Main ──────────────────────────────────────────────────────────────

def main (args : List String) : IO Unit := do
  let numSamples := (args[0]? >>= String.toNat?).getD 1000
  let outputPath := (args[1]?).getD "tyche_output.jsonl"
  IO.println s!"Generating {numSamples} samples..."

  -- Run the typed expression generator
  Tyche.run (genTypedExpr) { numSamples, propertyName := "Distribution of terms generated by genLExpr", outputPath }

  -- Run the typecheck property
  Tyche.run (genAndTypeCheck)
    { numSamples, propertyName := "Terms generated by genLExpr typecheck", outputPath := outputPath ++ ".tc" }

  -- Append typecheck results to the main file
  let tcContent ← IO.FS.readFile (outputPath ++ ".tc")
  let handle ← IO.FS.Handle.mk outputPath .append
  handle.putStr tcContent
  IO.FS.removeFile (outputPath ++ ".tc")

  -- Run the type preservation property
  Tyche.run (genAndEval)
    { numSamples, propertyName := "Type preservation under eval (closed terms)", outputPath := outputPath ++ ".ev" }
  let evContent ← IO.FS.readFile (outputPath ++ ".ev")
  handle.putStr evContent
  IO.FS.removeFile (outputPath ++ ".ev")

  -- Run the eval progress property
  Tyche.run (genAndCheckProgress)
    { numSamples, propertyName := "LExpr.eval makes progress on closed terms", outputPath := outputPath ++ ".prog" }
  let progContent ← IO.FS.readFile (outputPath ++ ".prog")
  handle.putStr progContent
  IO.FS.removeFile (outputPath ++ ".prog")

  -- Run the fvar preservation property
  Tyche.run (genAndCheckFvarPreservation)
    { numSamples, propertyName := "LExpr.eval preserves fvars", outputPath := outputPath ++ ".cls" }
  let clsContent ← IO.FS.readFile (outputPath ++ ".cls")
  handle.putStr clsContent
  IO.FS.removeFile (outputPath ++ ".cls")

  -- Also generate type samples into the same file
  let startTime ← IO.monoMsNow
  for _ in List.range numSamples do
    try
      let d ← randomDepth
      let ty ← genType d
      let sample := TycheSample.toSample ty
      let line := sample.toJsonLine "Distribution of types generated by genLMonoTy" startTime
      handle.putStrLn line
    catch _ => pure ()

  IO.println s!"Done! Output written to {outputPath}"
  IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
