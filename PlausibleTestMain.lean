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

instance : Arbitrary TypedExpr where
  arbitrary := do
    let size := (← Gen.getSize) / 20
    let tvars : List TyIdentifier := []
    let ty ← genLMonoTy (G := Plausible.Gen) tvars size
    let expr ← genLExpr (G := Plausible.Gen) [] [] tvars [] size ty
    pure ⟨expr, ty⟩

-- ── Evaluator ────────────────────────────────────────────────────────

def emptyState : LState LExprParams' := LState.init

def eval (fuel : Nat) (e : LExpr') : LExpr' :=
  LExpr.eval fuel emptyState e

def isValue (e : LExpr') : Bool :=
  LExpr.isCanonicalValue emptyState.config.factory e

-- ── Pretty-printing ──────────────────────────────────────────────────

open Std in
instance : ToFormat Unit where
  format _ := .nil

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

def checkProperty (name : String) (p : Prop) [Testable p]
    (cfg : Configuration) : IO Bool := do
  IO.print s!"  {name} ... "
  match ← Testable.checkIO p cfg with
  | .success _ =>
    IO.println "PASS"
    return true
  | .gaveUp n =>
    IO.println s!"GAVE UP ({n} discards)"
    return true
  | .failure _ xs n =>
    IO.println s!"FAIL (after {n} trials)"
    IO.eprintln s!"    {Testable.formatFailure "" xs n}"
    return false

def main (args : List String) : IO UInt32 := do
  let numTrials := (args[0]? >>= String.toNat?).getD 1000
  let maxSize := (args[1]? >>= String.toNat?).getD 100
  let cfg : Configuration := { numInst := numTrials, maxSize }

  IO.println s!"Running property-based tests ({numTrials} trials, max size {maxSize})..."
  IO.println ""

  let mut allPassed := true

  if !(← checkProperty "typecheck"
    (NamedBinder "te" (∀ te : TypedExpr, prop_typecheck te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "type_preservation"
    (NamedBinder "te" (∀ te : TypedExpr, prop_type_preservation te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "progress"
    (NamedBinder "te" (∀ te : TypedExpr, prop_progress te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "normalization"
    (NamedBinder "te" (∀ te : TypedExpr, prop_normalization te = true)) cfg) then
    allPassed := false

  IO.println ""
  if allPassed then
    IO.println "All tests passed."
    return 0
  else
    IO.println "Some tests failed."
    return 1
