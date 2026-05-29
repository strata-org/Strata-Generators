import StrataGenerators.Tyche
import StrataGenerators.HasTypeAGen
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

-- ── Feature extraction ────────────────────────────────────────────────

/-- Compute the depth (nesting level) of an LExpr. -/
def exprDepth : LExpr' → Nat
  | .abs _ _ _ body => exprDepth body + 1
  | .app _ fn arg => max (exprDepth fn) (exprDepth arg) + 1
  | .ite _ c t e => max (exprDepth c) (max (exprDepth t) (exprDepth e)) + 1
  | .eq _ e₁ e₂ => max (exprDepth e₁) (exprDepth e₂) + 1
  | .quant _ _ _ _ tr body => max (exprDepth tr) (exprDepth body) + 1
  | _ => 0

/-- Compute the size (number of nodes) of an LExpr. -/
def exprSize : LExpr' → Nat
  | .abs _ _ _ body => exprSize body + 1
  | .app _ fn arg => exprSize fn + exprSize arg + 1
  | .ite _ c t e => exprSize c + exprSize t + exprSize e + 1
  | .eq _ e₁ e₂ => exprSize e₁ + exprSize e₂ + 1
  | .quant _ _ _ _ tr body => exprSize tr + exprSize body + 1
  | _ => 1

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
    { representation := (format te.expr).pretty
      features := [
        ("depth", .ordinal (exprDepth te.expr)),
        ("size", .ordinal (exprSize te.expr)),
        ("expr_kind", .nominal (exprKind te.expr)),
        ("type_kind", .nominal (typeKind te.ty)),
        ("type_depth", .ordinal (monoTyDepth te.ty))
      ] }

/-- A generated monotype, ready for Tyche. -/
instance : Tyche.TycheSample LMonoTy where
  toSample ty :=
    { representation := (format ty).pretty
      features := [
        ("depth", .ordinal (monoTyDepth ty)),
        ("type_kind", .nominal (typeKind ty))
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

-- ── Main ──────────────────────────────────────────────────────────────

def main (args : List String) : IO Unit := do
  let numSamples := (args[0]? >>= String.toNat?).getD 1000
  let outputPath := (args[1]?).getD "tyche_output.jsonl"
  IO.println s!"Generating {numSamples} samples..."

  -- Run the typed expression generator
  Tyche.run (genTypedExpr) { numSamples, propertyName := "genLExpr (HasTypeA)", outputPath }

  -- Also generate type samples into a second property in the same file
  let handle ← IO.FS.Handle.mk outputPath .append
  let startTime ← IO.monoMsNow
  for _ in List.range numSamples do
    let ty ← genType
    let sample := TycheSample.toSample ty
    let line := sample.toJsonLine "genLMonoTy" startTime
    handle.putStrLn line

  IO.println s!"Done! Output written to {outputPath}"
  IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
