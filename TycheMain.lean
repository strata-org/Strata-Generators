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

/-- Pretty-print a monotype with `→` for arrows. -/
partial def ppType : LMonoTy → String
  | .arrow τ₁ τ₂ =>
    let lhs := match τ₁ with
      | .arrow _ _ => s!"({ppType τ₁})"
      | _ => ppType τ₁
    s!"{lhs} -> {ppType τ₂}"
  | .ftvar name => name
  | .bool => "bool"
  | .int => "int"
  | .bitvec n => s!"bv{n}"
  | .tcons name tys =>
    if tys.isEmpty then name
    else s!"({name} {" ".intercalate (tys.map ppType)})"

/-- Pretty-print an LExpr with minimal parenthesization.
    `prec` tracks the enclosing precedence to avoid unnecessary parens.
    Precedence levels: 0 = top/binder body, 1 = if/eq, 2 = application fn, 3 = application arg -/
def ppExpr (e : LExpr') (prec : Nat := 0) : String :=
  let wrap (p : Nat) (s : String) := if prec ≥ p then s!"({s})" else s
  match e with
  | .const _ (.boolConst b) => s!"#{b}"
  | .const _ (.intConst i) => s!"#{i}"
  | .const _ (.strConst s) => s!"\"{s}\""
  | .const _ (.realConst r) => s!"#{r}"
  | .const _ (.bitvecConst _ b) => s!"#{b.toNat}"
  | .op _ o ty => match ty with
    | some t => s!"~{o.name} : {ppType t}"
    | none => s!"~{o.name}"
  | .bvar _ i => s!"%{i}"
  | .fvar _ x ty => match ty with
    | some t => s!"{x.name} : {ppType t}"
    | none => s!"{x.name}"
  | .abs _ _ ty body => wrap 1 <| match ty with
    | some t => s!"λ{ppType t}. {ppExpr body 0}"
    | none => s!"λ_. {ppExpr body 0}"
  | .quant _ .all _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∀{ppType t}. {ppExpr body 0}"
    | none => s!"∀_. {ppExpr body 0}"
  | .quant _ .exist _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∃{ppType t}. {ppExpr body 0}"
    | none => s!"∃_. {ppExpr body 0}"
  | .app _ fn arg => wrap 3 <| s!"{ppExpr fn 2} {ppExpr arg 3}"
  | .ite _ c t e => wrap 1 <| s!"if {ppExpr c 0} then {ppExpr t 0} else {ppExpr e 0}"
  | .eq _ e₁ e₂ => wrap 2 <| s!"{ppExpr e₁ 2} == {ppExpr e₂ 2}"

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
  let expr ← genLExpr (G := IO) defaultFCtx [] tvars [] d ty
  return ⟨expr, ty, d⟩

/-- Generate just a monotype. -/
def genType (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO LMonoTy := do
  let d ← if depth == 0 then randomDepth else pure depth
  genLMonoTy (G := IO) tvars d

/-- Generate an expression and typecheck it against the expected type. -/
def genAndTypeCheck (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO TypeCheckResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExpr (G := IO) defaultFCtx [] tvars [] d ty
  let actualTy := LExpr.typeCheck (T := LExprParams') [] expr
  return ⟨expr, ty, actualTy, d⟩

/-- Generate a closed expression, evaluate it, and check type preservation.
    Uses empty fctx since preservation is stated for the empty context. -/
def genAndEval (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExpr (G := IO) [] [] tvars [] d ty
  let evaled := eval 100 expr
  let evaledTy := LExpr.typeCheck (T := LExprParams') [] evaled
  return ⟨expr, ty, evaled, evaledTy, isValue expr, !(expr == evaled), d⟩

-- ── Evaluates-to-value property ──────────────────────────────────────

/-- Result of generating an expression and checking whether it evaluates to a value. -/
structure EvalToValueResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  evaledIsValue : Bool
  generatorSize : Nat

instance : Tyche.TycheSample EvalToValueResult where
  toSample r :=
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status := if r.evaledIsValue then .passed else .failed
      features := [
        ("is_value", .nominal (if r.evaledIsValue then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_depth", .ordinal (exprDepth r.expr)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a closed expression, evaluate it, and check if the result is a value.
    Uses empty fctx since normalization is stated for the empty context. -/
def genAndCheckValue (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalToValueResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExpr (G := IO) [] [] tvars [] d ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, isValue evaled, d⟩

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
  let expr ← genLExpr (G := IO) [] [] tvars [] d ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, !(expr == evaled), isValue expr, d⟩

-- ── Eval idempotence property ────────────────────────────────────────

structure EvalIdempotentResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  evaledAgain : LExpr'
  isIdempotent : Bool
  generatorSize : Nat

instance : Tyche.TycheSample EvalIdempotentResult where
  toSample r :=
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status := if r.isIdempotent then .passed else .failed
      features := [
        ("idempotent", .nominal (if r.isIdempotent then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

-- TODO: generate terms w/ free vars (we can use a fixed context for now)

-- TODO: this may not be true in general
def genAndCheckIdempotent (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalIdempotentResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExpr (G := IO) defaultFCtx [] tvars [] d ty
  let evaled := eval 100 expr
  let evaledAgain := eval 100 evaled
  return ⟨expr, ty, evaled, evaledAgain, evaled == evaledAgain, d⟩

-- ── Eval monotonicity property ───────────────────────────────────────

structure EvalMonotoneResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled50 : LExpr'
  evaled100 : LExpr'
  evaled100From50 : LExpr'
  isMonotone : Bool
  generatorSize : Nat

instance : Tyche.TycheSample EvalMonotoneResult where
  toSample r :=
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled100}"
      status := if r.isMonotone then .passed else .failed
      features := [
        ("monotone", .nominal (if r.isMonotone then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled100)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckMonotone (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalMonotoneResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExpr (G := IO) defaultFCtx [] tvars [] d ty
  let evaled50 := eval 50 expr
  let evaled100 := eval 100 expr
  let evaled100From50 := eval 50 evaled50
  return ⟨expr, ty, evaled50, evaled100, evaled100From50, evaled100 == evaled100From50, d⟩

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
  let expr ← genLExpr (G := IO) defaultFCtx [] tvars [] d ty
  let evaled := eval 100 expr
  let inputFvars := LExpr.collectFvarNames expr
  let outputFvars := LExpr.collectFvarNames evaled
  let preserved := outputFvars.all (· ∈ inputFvars)
  return ⟨expr, ty, evaled, preserved, d⟩

-- ── Size non-increase property ───────────────────────────────────────

structure SizeResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  inputSize : Nat
  outputSize : Nat
  sizeNonIncreased : Bool
  generatorSize : Nat

instance : Tyche.TycheSample SizeResult where
  toSample r :=
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status := if r.sizeNonIncreased then .passed else .failed
      features := [
        ("size_ok", .nominal (if r.sizeNonIncreased then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_size", .ordinal r.inputSize),
        ("output_size", .ordinal r.outputSize),
        ("size_reduction", .ordinal (r.inputSize - r.outputSize)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckSize (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO SizeResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExpr (G := IO) defaultFCtx [] tvars [] d ty
  let evaled := eval 100 expr
  let inputSize := exprSize expr
  let outputSize := exprSize evaled
  return ⟨expr, ty, evaled, inputSize, outputSize, outputSize ≤ inputSize, d⟩

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

  -- Run the evaluates-to-value property
  Tyche.run (genAndCheckValue)
    { numSamples, propertyName := "Closed LExprs evaluate to values", outputPath := outputPath ++ ".val" }
  let valContent ← IO.FS.readFile (outputPath ++ ".val")
  handle.putStr valContent
  IO.FS.removeFile (outputPath ++ ".val")

  -- Run the eval progress property
  Tyche.run (genAndCheckProgress)
    { numSamples, propertyName := "LExpr.eval makes progress on closed terms", outputPath := outputPath ++ ".prog" }
  let progContent ← IO.FS.readFile (outputPath ++ ".prog")
  handle.putStr progContent
  IO.FS.removeFile (outputPath ++ ".prog")

  -- Run the eval idempotence property
  Tyche.run (genAndCheckIdempotent)
    { numSamples, propertyName := "LExpr.eval is idempotent", outputPath := outputPath ++ ".idem" }
  let idemContent ← IO.FS.readFile (outputPath ++ ".idem")
  handle.putStr idemContent
  IO.FS.removeFile (outputPath ++ ".idem")

  -- Run the eval monotonicity property
  Tyche.run (genAndCheckMonotone)
    { numSamples, propertyName := "LExpr.eval is monotone in fuel", outputPath := outputPath ++ ".mono" }
  let monoContent ← IO.FS.readFile (outputPath ++ ".mono")
  handle.putStr monoContent
  IO.FS.removeFile (outputPath ++ ".mono")

  -- Run the fvar preservation property
  Tyche.run (genAndCheckFvarPreservation)
    { numSamples, propertyName := "LExpr.eval preserves fvars", outputPath := outputPath ++ ".cls" }
  let clsContent ← IO.FS.readFile (outputPath ++ ".cls")
  handle.putStr clsContent
  IO.FS.removeFile (outputPath ++ ".cls")

  -- Run the size non-increase property
  Tyche.run (genAndCheckSize)
    { numSamples, propertyName := "LExpr.size does not increase under eval", outputPath := outputPath ++ ".sz" }
  let szContent ← IO.FS.readFile (outputPath ++ ".sz")
  handle.putStr szContent
  IO.FS.removeFile (outputPath ++ ".sz")

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
