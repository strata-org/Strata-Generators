import StrataGenerators.HasTypeAGen.Defs
import StrataGenerators.PlausibleGen
import Strata.DL.Lambda.LExprEval
import Plausible

/-!
# Property-based tests for LExpr generators

Uses Plausible's `Gen` monad (via `PlausibleGen`) to run the generators with
varying sizes, testing properties of `LExpr.eval`.

## Usage

```bash
lake build test-lexpr && .lake/build/bin/test-lexpr [numTrials] [maxSize]
```
-/

open Lambda RandomChoice ArbNat Basalt.PlausibleGen Plausible

-- ── Typed expression generation via Plausible.Gen ────────────────────

structure TypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving Repr, BEq

instance : Shrinkable TypedExpr where
  shrink _ := []

def genTypedExpr : Plausible.Gen TypedExpr := do
  let size := (← Gen.getSize) / 20
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := Plausible.Gen) tvars size
  let expr ← genLExpr (G := Plausible.Gen) [] [] tvars [] size ty
  pure ⟨expr, ty⟩

instance : Arbitrary TypedExpr where
  arbitrary := genTypedExpr

-- ── Evaluator ────────────────────────────────────────────────────────

def emptyState : LState LExprParams' := LState.init

def eval (fuel : Nat) (e : LExpr') : LExpr' :=
  LExpr.eval fuel emptyState e

def isValue (e : LExpr') : Bool :=
  LExpr.isCanonicalValue emptyState.config.factory e

-- ── Pretty-printing (minimal, for counter-examples) ──────────────────

open Std in
instance : ToFormat Unit where
  format _ := .nil

def ppExpr (e : LExpr') : String := s!"{Std.format e}"

-- ── Properties ───────────────────────────────────────────────────────

def prop_typecheck (te : TypedExpr) : Bool :=
  LExpr.typeCheck (T := LExprParams') [] te.expr == some te.ty

def prop_type_preservation (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  LExpr.typeCheck (T := LExprParams') [] evaled == some te.ty

def prop_progress (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  isValue te.expr || !(te.expr == evaled)

def prop_normalization (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  isValue evaled

-- ── Test runner ──────────────────────────────────────────────────────

def runProperty (name : String) (prop : TypedExpr → Bool)
    (numTrials : Nat) (maxSize : Nat) : IO Bool := do
  let mut failures := 0
  let mut gaveUp := 0
  for i in [:numTrials] do
    let size := i % (maxSize + 1)
    try
      let te ← Plausible.Gen.run genTypedExpr size
      if !prop te then
        failures := failures + 1
        if failures ≤ 3 then
          let evaled := eval 100 te.expr
          IO.eprintln s!"    Counter-example (size={size}):"
          IO.eprintln s!"      {ppExpr te.expr}  ⟶  {ppExpr evaled}"
    catch _ =>
      gaveUp := gaveUp + 1
  let passed := numTrials - failures - gaveUp
  if failures == 0 then
    IO.println s!"  {name} ... PASS ({passed} passed, {gaveUp} discarded)"
    return true
  else
    IO.println s!"  {name} ... FAIL ({failures}/{numTrials - gaveUp} failed, {gaveUp} discarded)"
    return false

def main (args : List String) : IO UInt32 := do
  let numTrials := (args[0]? >>= String.toNat?).getD 1000
  let maxSize := (args[1]? >>= String.toNat?).getD 100

  IO.println s!"Running property-based tests ({numTrials} trials, max size {maxSize})..."
  IO.println ""
  let mut allPassed := true
  for (name, prop) in [
    ("typecheck", prop_typecheck),
    ("type_preservation", prop_type_preservation),
    ("progress", prop_progress),
    ("normalization", prop_normalization)
  ] do
    let passed ← runProperty name prop numTrials maxSize
    if !passed then allPassed := false
  IO.println ""
  if allPassed then
    IO.println "All tests passed."
    return 0
  else
    IO.println "Some tests failed."
    return 1
