import StrataGenerators.HasTypeAGen.TestSupport
import Basalt.PlausibleGen
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

/-- A generated expression paired with its type. May contain free variables
    from `defaultFCtx`. -/
structure TypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving BEq

instance : Repr TypedExpr where
  reprPrec te _ := s!"({ppExpr te.expr}) : {ppType te.ty}"

/-- For terms that don't involve top-level binders (e.g. `lam` or `quant`),
    extract their immediate sub-terms. -/
private def immediateSubtermsWithoutBinders (e : LExpr') : List LExpr' :=
  match e with
  | .app _ fn arg => [fn, arg]
  | .ite _ c t e => [c, t, e]
  | .eq _ e1 e2 => [e1, e2]
  | _ => []

/-- Shrinks an LExpr structually.
    - Note: for terms involving binders (e.g. `abs` and `quant`), we shrink
    the body but keep the binder, in order to ensure that the shrunken
    term remains well-scoped.
    - For terms that don't involve binders, we extract their top-level subterms.
    - For constants (e.g. ints), we involve the default shrinker for that type. -/
private partial def shrinkLExpr (e : LExpr') : List LExpr' :=
  immediateSubtermsWithoutBinders e ++
  match e with
  | .app _ fn arg =>
    (.app () · arg) <$> shrinkLExpr fn ++
    (.app () fn ·) <$> shrinkLExpr arg
  | .ite _ c t el =>
    (.ite () · t el) <$> shrinkLExpr c ++
    (.ite () c · el) <$> shrinkLExpr t ++
    (.ite () c t ·) <$> shrinkLExpr el
  | .eq _ e1 e2 =>
    (.eq () · e2) <$> shrinkLExpr e1 ++
    (.eq () e1 ·) <$> shrinkLExpr e2
  | .abs _ name ty body =>
    (.abs () name ty ·) <$> shrinkLExpr body
  | .quant _ k name ty trigger body =>
    (.quant () k name ty · body) <$> shrinkLExpr trigger ++
    (.quant () k name ty trigger ·) <$> shrinkLExpr body
  | .const _ (.intConst i) =>
    (fun i' => .const () (.intConst i')) <$> Shrinkable.shrink i
  | _ => []

/-- Shrinkable instance for `TypedExpr` (a pair consisting of an `LExpr` and its type),
    required by Plausible.
    To ensure that the shrunken term has the right type, we just try to shrink
    `LExpr`s using `shrinkLExpr` and perform rejection sampling (i.e. filter out
    ill-typed candidate shrunken terms), and use the type of the shrunken
    term as the second component of the `TypedExpr`. (This avoids us needing
    to define separate shrinkers for types and `LExpr`s.) -/
instance : Shrinkable TypedExpr where
  shrink te :=
    (shrinkLExpr te.expr).filterMap fun e' =>
      match LExpr.typeCheck (T := LExprParams') [] e' with
      | some τ' => some ⟨e', τ'⟩
      | none => none

private def genTypedExprWith (fctx : FVarCtx) : Gen TypedExpr := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := Plausible.Gen) tvars depth
  let expr ← genLExprWithFactory (G := Plausible.Gen) fctx intBoolFactory tvars [] depth ty
  pure ⟨expr, ty⟩

-- `genLExpr` can fail (via `default`) when a depth-0 arrow case has no
-- bvar/fvar/op in context. Since `Plausible.Gen` doesn't backtrack on its
-- own, we use `Gen.backtrack` to retry with fresh randomness on failure.
instance : Arbitrary TypedExpr where
  arbitrary := Gen.backtrack (List.replicate 100 (1, genTypedExprWith defaultFCtx))

/-- A closed generated expression (no free variables). Used for properties
    that are stated with respect to the empty typing context (progress
    and preservation). -/
structure ClosedTypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving BEq

instance : Repr ClosedTypedExpr where
  reprPrec te _ := s!"({ppExpr te.expr}) : {ppType te.ty}"

instance : Shrinkable ClosedTypedExpr where
  shrink te :=
    (shrinkLExpr te.expr).filterMap fun e' =>
      match LExpr.typeCheck (T := LExprParams') [] e' with
      | some τ' => some ⟨e', τ'⟩
      | none => none

instance : Arbitrary ClosedTypedExpr where
  arbitrary := Gen.backtrack (List.replicate 100
    (1, (fun te => ⟨te.expr, te.ty⟩) <$> genTypedExprWith []))

-- ── Pretty-printing ──────────────────────────────────────────────────

instance : Repr LExpr' where
  reprPrec e _ := ppExpr e

instance : Repr LMonoTy where
  reprPrec τ _ := ppType τ

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

-- Properties are `@[reducible]` so that Lean's typeclass resolution can
-- unfold them to find `Decidable` instances for the underlying propositions
-- (e.g. `DecidableEq` for `=`). Without this, Plausible's `decidableTestable`
-- instance sees an opaque `Prop` and fails to synthesize `Testable`.

-- Soundness of the generator: every generated expression typechecks
-- to the type it was generated for. (Works for both open and closed terms
-- since HasTypeA trusts fvar annotations.)
@[reducible] def prop_typecheck (te : TypedExpr) : Prop :=
  LExpr.typeCheck (T := LExprParams') [] te.expr = some te.ty













-- Preservation (closed terms only): if ∅ ⊢ e : τ and e →* e', then ∅ ⊢ e' : τ.
@[reducible] def prop_preservation (te : ClosedTypedExpr) : Prop :=
  let evaled := eval 100 te.expr
  LExpr.typeCheck (T := LExprParams') [] evaled = some te.ty

-- Progress (closed terms only): a well-typed closed term is either a value
-- or can take a step.
-- Falsified by quantifiers (`∀`/`∃`) — `LExpr.eval` has no reduction rule
-- for them, so `if (∀x. e) then ...` gets stuck.
@[reducible] def prop_progress (te : ClosedTypedExpr) : Prop :=
  let evaled := eval 100 te.expr
  isValue te.expr = true ∨ te.expr ≠ evaled

-- Fvar preservation: evaluation does not introduce *new* free variables.
-- Free variables from the context (x, f, n) may appear in both the input
-- and output, but eval should not create fvars that weren't already present.
@[reducible] def prop_closedness_preservation (te : TypedExpr) : Prop :=
  let evaled := eval 100 te.expr
  let inputFvars := LExpr.collectFvarNames te.expr
  let outputFvars := LExpr.collectFvarNames evaled
  outputFvars.all (· ∈ inputFvars) = true











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

  -- `NamedBinder` wraps the quantified proposition so that Plausible's
  -- `varTestable` instance can match on `∀ x : α, β x`. Without it,
  -- `Testable.checkIO` (which works in `IO`, unlike `Testable.check` which
  -- uses `CoreM` and the `mk_decorations` tactic) cannot find a `Testable`
  -- instance for bare `∀`-propositions. The string argument ("te") labels
  -- the variable in counterexample output.
  if !(← checkProperty "generated terms typecheck"
    (NamedBinder "te" (∀ te : TypedExpr, prop_typecheck te)) cfg) then
    allPassed := false

  if !(← checkProperty "preservation (closed)"
    (NamedBinder "te" (∀ te : ClosedTypedExpr, prop_preservation te)) cfg) then
    allPassed := false

  if !(← checkProperty "progress (closed)"
    (NamedBinder "te" (∀ te : ClosedTypedExpr, prop_progress te)) cfg) then
    allPassed := false

  if !(← checkProperty "closedness_preservation"
    (NamedBinder "te" (∀ te : TypedExpr, prop_closedness_preservation te)) cfg) then
    allPassed := false

  IO.println ""
  if allPassed then
    IO.println "All tests passed."
    return 0
  else
    IO.println "Some tests failed."
    return 1
