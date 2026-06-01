import StrataGenerators.Tyche
import StrataGenerators.HasTypeAGen.Defs
import Strata.DL.Lambda.LExprEval
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

/-- A generated expression paired with its type, ready for Tyche. -/
structure TypedExpr where
  expr : LExpr'
  ty : LMonoTy

instance : Tyche.TycheSample TypedExpr where
  toSample te :=
    { representation := ppExpr te.expr
      features := [
        ("depth", .ordinal (exprDepth te.expr)),
        ("LExpr.size", .ordinal (exprSize te.expr)),
        ("expr_kind", .nominal (exprKind te.expr)),
        ("type_kind", .nominal (typeKind te.ty)),
        ("type_depth", .ordinal (monoTyDepth te.ty))
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
        ("monoTyDepth", .ordinal (monoTyDepth r.expectedTy))
      ] }

-- ── Evaluator ─────────────────────────────────────────────────────────
-- Uses Strata's `LExpr.eval` with an empty state (closed terms, no operators).

def emptyState : LState LExprParams' := LState.init

def eval (fuel : Nat) (e : LExpr') : LExpr' :=
  LExpr.eval fuel emptyState e

def isValue (e : LExpr') : Bool :=
  LExpr.isCanonicalValue emptyState.config.factory e

-- ── Type preservation property ────────────────────────────────────────

/-- Result of generating, evaluating, and re-typechecking. -/
structure EvalResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  evaledTy : Option LMonoTy
  exprIsValue : Bool
  madeProgress : Bool

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
        ("output_size", .ordinal (exprSize r.evaled))
      ] }

-- ── Generator wrappers ────────────────────────────────────────────────

/-- Generate a typed expression using `genClosedLExpr` from HasTypeAGen. -/
def genTypedExpr (size : Nat := 3) (tvars : List TyIdentifier := ["α", "β"]) : IO TypedExpr := do
  let ty ← genLMonoTy (G := IO) tvars size
  let expr ← genLExpr (G := IO) [] [] tvars [] size ty
  return ⟨expr, ty⟩

/-- Generate just a monotype. -/
def genType (size : Nat := 3) (tvars : List TyIdentifier := ["α", "β"]) : IO LMonoTy :=
  genLMonoTy (G := IO) tvars size

/-- Generate an expression and typecheck it against the expected type. -/
def genAndTypeCheck (size : Nat := 3) (tvars : List TyIdentifier := ["α", "β"]) : IO TypeCheckResult := do
  let ty ← genLMonoTy (G := IO) tvars size
  let expr ← genLExpr (G := IO) [] [] tvars [] size ty
  let actualTy := LExpr.typeCheck (T := LExprParams') [] expr
  return ⟨expr, ty, actualTy⟩

/-- Generate an expression, evaluate it, and check type preservation. -/
def genAndEval (size : Nat := 3) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalResult := do
  let ty ← genLMonoTy (G := IO) tvars size
  let expr ← genLExpr (G := IO) [] [] tvars [] size ty
  let evaled := eval 100 expr
  let evaledTy := LExpr.typeCheck (T := LExprParams') [] evaled
  return ⟨expr, ty, evaled, evaledTy, isValue expr, !(expr == evaled)⟩

-- ── Evaluates-to-value property ──────────────────────────────────────

/-- Result of generating an expression and checking whether it evaluates to a value. -/
structure EvalToValueResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  evaledIsValue : Bool

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
        ("expr_kind", .nominal (exprKind r.expr))
      ] }

/-- Generate an expression, evaluate it, and check if the result is a value. -/
def genAndCheckValue (size : Nat := 3) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalToValueResult := do
  let ty ← genLMonoTy (G := IO) tvars size
  let expr ← genLExpr (G := IO) [] [] tvars [] size ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, isValue evaled⟩

-- ── Eval progress property ───────────────────────────────────────────

/-- Result of checking whether `LExpr.eval` makes progress on a generated term. -/
structure EvalProgressResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  madeProgress : Bool
  inputIsValue : Bool

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
        ("expr_kind", .nominal (exprKind r.expr))
      ] }

/-- Generate an expression and check whether eval makes progress (or the input is already a value). -/
def genAndCheckProgress (size : Nat := 3) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalProgressResult := do
  let ty ← genLMonoTy (G := IO) tvars size
  let expr ← genLExpr (G := IO) [] [] tvars [] size ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, !(expr == evaled), isValue expr⟩

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
    { numSamples, propertyName := "Type preservation under eval", outputPath := outputPath ++ ".ev" }
  let evContent ← IO.FS.readFile (outputPath ++ ".ev")
  handle.putStr evContent
  IO.FS.removeFile (outputPath ++ ".ev")

  -- Run the evaluates-to-value property
  Tyche.run (genAndCheckValue)
    { numSamples, propertyName := "Generated LExprs evaluate to values", outputPath := outputPath ++ ".val" }
  let valContent ← IO.FS.readFile (outputPath ++ ".val")
  handle.putStr valContent
  IO.FS.removeFile (outputPath ++ ".val")

  -- Run the eval progress property
  Tyche.run (genAndCheckProgress)
    { numSamples, propertyName := "LExpr.eval makes progress or input is a value", outputPath := outputPath ++ ".prog" }
  let progContent ← IO.FS.readFile (outputPath ++ ".prog")
  handle.putStr progContent
  IO.FS.removeFile (outputPath ++ ".prog")

  -- Also generate type samples into the same file
  let startTime ← IO.monoMsNow
  for _ in List.range numSamples do
    try
      let ty ← genType
      let sample := TycheSample.toSample ty
      let line := sample.toJsonLine "Distribution of types generated by genLMonoTy" startTime
      handle.putStrLn line
    catch _ => pure ()

  IO.println s!"Done! Output written to {outputPath}"
  IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
