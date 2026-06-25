import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.CmdHasTypeAGen.TestSupport
import Basalt.PlausibleGen
import Plausible
import Strata.DL.Lambda.LExprT

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

open Lambda RandomChoice ArbNat Basalt.PlausibleGen Plausible Core Imperative

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
    extract their immediate sub-terms. Excludes bare `.op` nodes since
    unapplied operators (interpretered functions)
    are trivial counterexamples to progress (they aren't
    values and can't reduce without arguments). -/
private def immediateSubtermsWithoutBinders (e : LExpr') : List LExpr' :=
  (match e with
  | .app _ fn arg => [fn, arg]
  | .ite _ c t e => [c, t, e]
  | .eq _ e1 e2 => [e1, e2]
  | _ => []).filter fun
    | .op _ _ _ => false
    | _ => true

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
  let expr ← genLExprWithOps (G := Plausible.Gen) fctx coreOpCtx corePolyOps tvars [] depth ty
  pure ⟨expr, ty⟩

-- `genLExpr` can fail (via `default`) when a depth-0 arrow case has no
-- bvar/fvar/op in context. Since `Plausible.Gen` doesn't backtrack on its
-- own, we use `Gen.backtrack` to retry with fresh randomness on failure.
instance : Arbitrary TypedExpr where
  arbitrary := Gen.backtrack (List.replicate 500 (1, genTypedExprWith defaultFCtx))

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
  arbitrary := Gen.backtrack (List.replicate 500
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

-- ── Resolve after erasure ────────────────────────────────────────────

/-- Known types covering all base types the generator can produce. -/
private def resolveKnownTypes : Lambda.KnownTypes :=
  open Lambda.LTy.Syntax in
  Lambda.makeKnownTypes ([t[∀a b. %a → %b],
    t[bool], t[int], t[string], t[real], t[regex],
    t[∀n. bitvec n],
    t[∀a b. Map %a %b],
    t[∀a. Sequence %a]].map (fun k => k.toKnownType!))

/-- LContext with `intBoolFactory` and all generator-relevant known types. -/
private def resolveLContext : Lambda.LContext LExprParams' :=
  { Lambda.LContext.default with
    functions := intBoolFactory,
    knownTypes := resolveKnownTypes }

/-- A closed expression generated using only `intBoolFactory` ops,
    suitable for round-tripping through `eraseTypes` + `resolve`. -/
structure ResolveTypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving BEq

instance : Repr ResolveTypedExpr where
  reprPrec te _ := s!"({ppExpr te.expr}) : {ppType te.ty}"

instance : Shrinkable ResolveTypedExpr where
  shrink te :=
    (shrinkLExpr te.expr).filterMap fun e' =>
      match LExpr.typeCheck (T := LExprParams') [] e' with
      | some τ' => some ⟨e', τ'⟩
      | none => none

private def intBoolOpCtx : OpCtx := factoryOps intBoolFactory

private def genResolveTypedExpr : Gen ResolveTypedExpr := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := Plausible.Gen) tvars depth
  let expr ← genLExprWithOps (G := Plausible.Gen) [] intBoolOpCtx [] tvars [] depth ty
  pure ⟨expr, ty⟩

instance : Arbitrary ResolveTypedExpr where
  arbitrary := Gen.backtrack (List.replicate 500 (1, genResolveTypedExpr))

/-- Erase op and fvar type annotations but keep binder types (abs and quant).
    This is the subset of erasure that `resolve` can always recover from, since
    it infers op types from the factory and fvar types from the context, but
    needs binder types to seed fresh type variables. -/
def eraseOpFvarTypes : LExpr' → LExpr'
  | .const m c => .const m c
  | .op m o _ => .op m o none
  | .fvar m x _ => .fvar m x none
  | .bvar m i => .bvar m i
  | .abs m name ty e => .abs m name ty (eraseOpFvarTypes e)
  | .quant m qk name ty tr e => .quant m qk name ty (eraseOpFvarTypes tr) (eraseOpFvarTypes e)
  | .app m e1 e2 => .app m (eraseOpFvarTypes e1) (eraseOpFvarTypes e2)
  | .ite m c t f => .ite m (eraseOpFvarTypes c) (eraseOpFvarTypes t) (eraseOpFvarTypes f)
  | .eq m e1 e2 => .eq m (eraseOpFvarTypes e1) (eraseOpFvarTypes e2)

def checkResolveAfterErase (te : ResolveTypedExpr) : Bool :=
  let erased := eraseOpFvarTypes te.expr
  match LExpr.resolve resolveLContext Lambda.TEnv.default erased with
  | .ok (resolved, _) => resolved.toLMonoTy == te.ty
  | .error _ => false

@[reducible] def prop_resolve_after_erase (te : ResolveTypedExpr) : Prop :=
  checkResolveAfterErase te = true








-- ── Command generation via Plausible.Gen ─────────────────────────────

/-- A generated command paired with its input context. -/
structure GenCmdWithCtx where
  cmd : Cmd Expression
  inCtx : VarCtx
  outCtx : VarCtx

instance : Repr GenCmdWithCtx where
  reprPrec gc _ := s!"{ppCmd gc.cmd}  [ctx: {ppVarCtx gc.inCtx}]"

instance : Shrinkable GenCmdWithCtx where
  shrink _ := []

private def genCmdWith (ctx : VarCtx) : Gen GenCmdWithCtx := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ⟨cmd, ctx'⟩ ← genCmd (G := Plausible.Gen) [] coreOpCtx tvars ctx depth
  pure ⟨cmd, ctx, ctx'⟩

private def genCmdFromBuiltCtx (ctxSize : Nat) : Gen GenCmdWithCtx := do
  let depth := 2
  let tvars : List TyIdentifier := []
  let (_, baseCtx) ← genCmds (G := Plausible.Gen) [] coreOpCtx tvars [] depth ctxSize
  let ⟨cmd, ctx'⟩ ← genCmd (G := Plausible.Gen) [] coreOpCtx tvars baseCtx depth
  pure ⟨cmd, baseCtx, ctx'⟩

instance : Arbitrary GenCmdWithCtx where
  arbitrary := Gen.backtrack (List.replicate 1000
    (1, genCmdFromBuiltCtx 3))

/-- A generated command sequence paired with its context. -/
structure GenCmdsWithCtx where
  cmds : List (Cmd Expression)
  inCtx : VarCtx
  outCtx : VarCtx

instance : Repr GenCmdsWithCtx where
  reprPrec gc _ :=
    let cmdStrs := gc.cmds.map ppCmd |> "; ".intercalate
    s!"{cmdStrs}  [in: {ppVarCtx gc.inCtx}, out: {ppVarCtx gc.outCtx}]"

instance : Shrinkable GenCmdsWithCtx where
  shrink _ := []

private def genCmdsWithCtx : Gen GenCmdsWithCtx := do
  let depth := 2
  let n := 4
  let tvars : List TyIdentifier := []
  let (cmds, ctx') ← genCmds (G := Plausible.Gen) [] coreOpCtx tvars [] depth n
  pure ⟨cmds, [], ctx'⟩

instance : Arbitrary GenCmdsWithCtx where
  arbitrary := Gen.backtrack (List.replicate 1000 (1, genCmdsWithCtx))

-- ── Command-level properties ─────────────────────────────────────────

-- For `init x τ (det e)`, the freshly declared variable `x` does not appear
-- in the free variables of its own initializer `e`. This is a key
-- precondition for the `CmdHasType'.init_det` typing rule.
@[reducible] def prop_cmd_init_fresh (gc : GenCmdWithCtx) : Prop :=
  checkInitFreshNotInRhs gc.cmd = true

-- Every expression sub-term in a generated command typechecks to the
-- expected monotype in the empty bound-variable context.
@[reducible] def prop_cmd_expr_typechecks (gc : GenCmdWithCtx) : Prop :=
  checkExprTypechecks gc.cmd = true

-- For a generated command sequence, the output context equals the input
-- context prepended with the newly defined variables (in reverse order,
-- since `init` conses onto the front).
@[reducible] def prop_cmds_context_growth (gc : GenCmdsWithCtx) : Prop :=
  checkContextGrowth gc.inCtx gc.outCtx gc.cmds = true

-- Running a well-typed generated command produces no scoping error
-- (e.g., set on undefined variable).
@[reducible] def prop_cmd_run_no_error (gc : GenCmdWithCtx) : Prop :=
  checkCmdRunNoError gc.cmd gc.inCtx = true

-- Running a well-typed generated command sequence produces no scoping error.
@[reducible] def prop_cmds_run_no_error (gc : GenCmdsWithCtx) : Prop :=
  checkCmdsRunNoError gc.cmds gc.inCtx = true

-- After `set x e`, the variable `x` remains defined in the store.
@[reducible] def prop_cmd_set_preserves_var (gc : GenCmdWithCtx) : Prop :=
  checkSetPreservesVar gc.cmd gc.inCtx = true

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

  if !(← checkProperty "erasing type annotations then performing type inference recovers the same type"
    (NamedBinder "te" (∀ te : ResolveTypedExpr, prop_resolve_after_erase te)) cfg) then
    allPassed := false

  IO.println ""
  IO.println "Command generator properties:"

  if !(← checkProperty "init: fresh var not in RHS"
    (NamedBinder "gc" (∀ gc : GenCmdWithCtx, prop_cmd_init_fresh gc)) cfg) then
    allPassed := false

  if !(← checkProperty "cmd: expressions typecheck"
    (NamedBinder "gc" (∀ gc : GenCmdWithCtx, prop_cmd_expr_typechecks gc)) cfg) then
    allPassed := false

  if !(← checkProperty "cmds: context growth matches inits"
    (NamedBinder "gc" (∀ gc : GenCmdsWithCtx, prop_cmds_context_growth gc)) cfg) then
    allPassed := false

  if !(← checkProperty "cmd: run produces no error"
    (NamedBinder "gc" (∀ gc : GenCmdWithCtx, prop_cmd_run_no_error gc)) cfg) then
    allPassed := false

  if !(← checkProperty "cmds: run sequence produces no error"
    (NamedBinder "gc" (∀ gc : GenCmdsWithCtx, prop_cmds_run_no_error gc)) cfg) then
    allPassed := false

  if !(← checkProperty "cmd: set preserves variable"
    (NamedBinder "gc" (∀ gc : GenCmdWithCtx, prop_cmd_set_preserves_var gc)) cfg) then
    allPassed := false

  IO.println ""
  if allPassed then
    IO.println "All tests passed."
    return 0
  else
    IO.println "Some tests failed."
    return 1
