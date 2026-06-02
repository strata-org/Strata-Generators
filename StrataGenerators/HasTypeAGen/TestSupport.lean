import StrataGenerators.HasTypeAGen.Defs
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.IntBoolFactory

open Lambda

/-!
# Shared test support for the `HasTypeA` generator

Utilities shared between `PlausibleTestMain` and `TycheMain`: the default
free-variable context, the operator context from `IntBoolFactory`, the
evaluator wrapper, and the value predicate.
-/

-- ── Default contexts ────────────────────────────────────────────────────

/-- A fixed free-variable context providing variables of common types.
    Used by both the Plausible and Tyche test harnesses to exercise the
    `fvar` generation path. -/
def defaultFCtx : FVarCtx :=
  [("x", .bool), ("f", .arrow .int .bool), ("n", .int)]

/-- The `IntBoolFactory` instantiated at our parameter types. Provides
    integer arithmetic (Add, Sub, Mul, ...), comparisons (Lt, Le, ...),
    and boolean operations (And, Or, Not, ...). -/
def intBoolFactory : Factory LExprParams' :=
  @IntBoolFactory (T := LExprParams') ⟨()⟩ ⟨()⟩

-- ── Evaluator ───────────────────────────────────────────────────────────

/-- An evaluation state with `IntBoolFactory` loaded. Operators like `Int.Add`
    will reduce when applied to concrete arguments. -/
def intBoolState : LState LExprParams' :=
  { state := [],
    config := { factory := intBoolFactory,
                fuel := 200,
                usedNames := {} } }

/-- Evaluate an expression with the given fuel using `IntBoolFactory`.
    Operators reduce when applied to constants; free variables are irreducible. -/
def eval (fuel : Nat) (e : LExpr') : LExpr' :=
  LExpr.eval fuel intBoolState e

/-- Check whether an expression is a canonical value under `IntBoolFactory`. -/
def isValue (e : LExpr') : Bool :=
  LExpr.isCanonicalValue intBoolState.config.factory e
