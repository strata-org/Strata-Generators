import StrataGenerators.HasTypeAGen.Defs
import Strata.DL.Lambda.LExprEval

open Lambda

/-!
# Shared test support for the `HasTypeA` generator

Utilities shared between `PlausibleTestMain` and `TycheMain`: the default
free-variable context, the evaluator wrapper, and the value predicate.
-/

-- ── Default contexts ────────────────────────────────────────────────────

/-- A fixed free-variable context providing variables of common types.
    Used by both the Plausible and Tyche test harnesses to exercise the
    `fvar` generation path. -/
def defaultFCtx : FVarCtx :=
  [("x", .bool), ("f", .arrow .int .bool), ("n", .int)]

-- ── Evaluator ───────────────────────────────────────────────────────────

/-- An empty evaluation state. Free variables evaluate to themselves (stuck). -/
def emptyState : LState LExprParams' := LState.init

/-- Evaluate an expression with the given fuel and empty state.
    Free variables are irreducible under this state. -/
def eval (fuel : Nat) (e : LExpr') : LExpr' :=
  LExpr.eval fuel emptyState e

/-- Check whether an expression is a canonical value (constant, abs, quant,
    fvar, op, or bvar). -/
def isValue (e : LExpr') : Bool :=
  LExpr.isCanonicalValue emptyState.config.factory e
