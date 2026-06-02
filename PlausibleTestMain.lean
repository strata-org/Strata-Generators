import StrataGenerators.HasTypeAGen.Defs
import Basalt.PlausibleGen
import Strata.DL.Lambda.LExprEval
import Plausible

/-!
# Property-based tests for LExpr generators

Uses Plausible's `Gen` monad (via Basalt's `PlausibleGen`) to run the generators with
varying sizes, testing properties of `LExpr.eval`.

## Usage

```bash
lake build test-lexpr && .lake/build/bin/test-lexpr [numTrials] [maxSize]
```

## Why we define our own test runner

Plausible's standard entry point `Testable.check` returns `CoreM` (it uses
the `mk_decorations` tactic to wrap quantifiers in `NamedBinder` annotations
for better error messages). Since `CoreM` requires the Lean elaboration
environment, it cannot be called from a standalone `IO`-based `main` function.

The lower-level `Testable.checkIO` works in `IO`, but its `Testable` instance
for `∀ x : α, p x` only matches when the proposition is wrapped in
`NamedBinder`. We apply this wrapper explicitly at each call site, which is
the manual equivalent of what `Testable.check`'s `mk_decorations` tactic does
automatically in `#eval` contexts.
-/

open Lambda RandomChoice ArbNat Basalt.PlausibleGen Plausible

-- ── Typed expression generation via Plausible.Gen ────────────────────

structure TypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving Repr, BEq

instance : Shrinkable TypedExpr where
  shrink _ := []

private def defaultFCtx : FVarCtx :=
  [("x", .bool), ("f", .arrow .int .bool), ("n", .int)]

private def genTypedExpr : Gen TypedExpr := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := Plausible.Gen) tvars depth
  let expr ← genLExpr (G := Plausible.Gen) defaultFCtx [] tvars [] depth ty
  pure ⟨expr, ty⟩

-- `genLExpr` can fail (via `default`) when a depth-0 arrow case has no
-- bvar/fvar/op in context. Since `Plausible.Gen` doesn't backtrack on its
-- own, we use `Gen.backtrack` to retry with fresh randomness on failure.
instance : Arbitrary TypedExpr where
  arbitrary := Gen.backtrack (List.replicate 20 (1, genTypedExpr))

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
--
-- These properties test `LExpr.eval` from `Strata.DL.Lambda.LExprEval`.
-- The first two (typecheck, preservation) correspond to standard type-safety
-- theorems. The rest exercise operational properties of the fuel-bounded
-- evaluator, inspired by the theorems in `Strata.DL.Lambda.Semantics`:
-- Some theorems are omitted though:
--   • `eval_StepStar` (Semantics.lean): eval is sound w.r.t. the
--     small-step relation `Step`. We don't test this directly because the
--     existential witness (`∃ e', StepStar ... e e'`) would require searching
--     for a reachable expression. Instead, our idempotence + monotonicity +
--     preservation properties try to cover this.
--
--   • `eval_eraseMetadata_invariant` (Semantics.lean): eval is invariant
--     under metadata changes. Since our metadata type is `Unit`, eraseMetadata
--     is the identity (proved in LExprEvalTests.lean:106), so this property
--     holds trivially and we omit it.

-- Soundness of the generator: every generated expression typechecks
-- to the type it was generated for.
def prop_typecheck (te : TypedExpr) : Bool :=
  LExpr.typeCheck (T := LExprParams') [] te.expr == some te.ty

-- Preservation: the type of an expression is unchanged after evaluation.
-- That is, if Γ ⊢ e : τ and e →* e', then Γ ⊢ e' : τ.
def prop_preservation (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  LExpr.typeCheck (T := LExprParams') [] evaled == some te.ty

-- Progress: either the expression is already a canonical value, or
-- `LExpr.eval` reduces it to something different.
-- Falsified by quantifiers (`∀`/`∃`) in non-value positions — `LExpr.eval`
-- has no reduction rule for them, so `if (∀x. e) then ...` gets stuck.
def prop_progress (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  isValue te.expr || !(te.expr == evaled)

-- Normalization: every expression evaluates to a canonical value.
-- Falsified by (1) stuck quantifiers (as above) and (2) equality of lambdas
-- with non-identical bodies (e.g. `(λx. x+1) == (λx. 1+x)`), where
-- `LExpr.eql` returns `none` (inconclusive) and the `==` node gets stuck.
def prop_normalization (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  isValue evaled

-- Idempotence: evaluating an already-evaluated expression again produces
-- the same result. This follows from the structure of `LExpr.eval`
-- (LExprEval.lean:207): it returns `e` unchanged when `isCanonicalValue` is
-- true, and stuck terms have no applicable reduction rules.
-- Inspired by `LExprEvalTests.lean:78` (`check`) which verifies eval reaches
-- a fixpoint.
def prop_eval_idempotent (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  let evaled2 := eval 100 evaled
  evaled == evaled2

-- Monotonicity (fuel composability): `eval 100 e == eval 50 (eval 50 e)`.
-- Since eval is deterministic and fuel-bounded, splitting fuel across two
-- calls should produce the same result as using it all at once.
-- Inspired by `eval_StepStar` (Semantics.lean:2926) which proves eval traces
-- a sequence of `Step`s — the same sequence regardless of how fuel is split.
def prop_eval_monotone (te : TypedExpr) : Bool :=
  let evaled50 := eval 50 te.expr
  let evaled100 := eval 100 te.expr
  let evaled100_from50 := eval 50 evaled50
  evaled100 == evaled100_from50

-- Fvar preservation: evaluation does not introduce *new* free variables.
-- Free variables from the context (x, f, n) may appear in both the input
-- and output, but eval should not create fvars that weren't already present.
def prop_closedness_preservation (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  let inputFvars := LExpr.collectFvarNames te.expr
  let outputFvars := LExpr.collectFvarNames evaled
  outputFvars.all (· ∈ inputFvars)

-- Size non-increase: evaluation should never grow the term. With an empty
-- factory (no function inlining), every reduction step either eliminates
-- structure (beta-reduction discards the lambda wrapper, ite-reduction
-- discards a branch) or leaves size unchanged (stuck terms).
-- Inspired by the termination arguments in `Semantics.lean` which rely on
-- `sizeOf` decreasing through reduction steps.
def prop_size_non_increase (te : TypedExpr) : Bool :=
  let evaled := eval 100 te.expr
  LExpr.size LExprParamsT' evaled ≤ LExpr.size LExprParamsT' te.expr

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
    (NamedBinder "te" (∀ te : TypedExpr, prop_preservation te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "progress"
    (NamedBinder "te" (∀ te : TypedExpr, prop_progress te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "normalization"
    (NamedBinder "te" (∀ te : TypedExpr, prop_normalization te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "eval_idempotent"
    (NamedBinder "te" (∀ te : TypedExpr, prop_eval_idempotent te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "eval_monotone"
    (NamedBinder "te" (∀ te : TypedExpr, prop_eval_monotone te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "closedness_preservation"
    (NamedBinder "te" (∀ te : TypedExpr, prop_closedness_preservation te = true)) cfg) then
    allPassed := false

  if !(← checkProperty "size_non_increase"
    (NamedBinder "te" (∀ te : TypedExpr, prop_size_non_increase te = true)) cfg) then
    allPassed := false

  IO.println ""
  if allPassed then
    IO.println "All tests passed."
    return 0
  else
    IO.println "Some tests failed."
    return 1
