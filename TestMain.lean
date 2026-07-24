import StrataGenerators.PropertyNames
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.Roundtrip
import StrataGenerators.StmtHasTypeAGen.TestSupport
import StrataGenerators.TycheViz
import Basalt.PlausibleGen
import Plausible
import LSpec
import Strata.DL.Lambda.LExprT
-- Imports for Function.typeCheck property (typeCheck_annotated_sound)
import Strata.Languages.Core.FunctionType
import Strata.DL.Lambda.Denote.LExprAnnotated
-- Imports for pretty-print/parse round-trip property
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

/-!
# Property-based tests using the Strata generators (single merged driver)

The one executable test driver for this package, registered as the `lake test`
driver. It exercises the expression, command, function, and statement generators
in *two* complementary ways from a single run:

1. **Plausible + LSpec** — each property is a `Bool` check asserted over many
   randomly-generated inputs; `LSpec.lspecIO` prints a per-suite `✓/×` summary and
   returns the exit code (`0` all-pass, `1` on any failure).
2. **Tyche visualization** — the same properties are sampled and written as Tyche
   JSONL panels for interactive exploration (see `StrataGenerators.TycheViz`).

Every property's *pass/fail decision* comes from a shared `check*` predicate in the
`*.TestSupport` modules, so the LSpec assertion and the Tyche panel for a given
property always agree; only the Tyche-specific visualization scaffolding (feature
breakdowns, counterexample-dense rejection sampling) lives separately.

## Usage

```bash
lake test -- [numTrials] [maxSize] [flags]
```

or, equivalently:

```bash
lake build test && .lake/build/bin/test [numTrials] [maxSize] [flags]
```

Positional arguments configure the Plausible run (`numTrials` = trials per
property, default 1000; `maxSize` = max generator size, default 100). Flags:

- `--no-tyche` — skip the Tyche visualization pass (it runs by default).
- `--tyche-out=PATH` — Tyche JSONL output path (default `tyche_output.jsonl`).
- `--tyche-samples=N` — samples per Tyche panel (default 1000).

The exit code is always the LSpec verdict; the Tyche pass never affects it.

## How the tests are run

The two format→parse round-trip checks are not plain `Prop`s: they run in `IO`,
shrink counterexamples, and print minimal reproducers. They are wrapped as
custom `TestSeq.individualIO` nodes so they join the same `lspecIO` suite.
-/

open Lambda RandomChoice ArbNat Basalt.PlausibleGen Plausible Core Imperative
open Strata Strata.CoreDDM
open StrataDDM (initDialect)
open LSpec (TestSeq checkIO lspecIO group)

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

/-- Shared shrinker for the expr/type-pair wrappers (`TypedExpr`,
    `ClosedTypedExpr`, `ResolveTypedExpr`), which all pair an `LExpr` with its
    type and differ only in how they are generated.
    To ensure that the shrunken term has the right type, we shrink the `LExpr`
    with `shrinkLExpr` and perform rejection sampling (i.e. filter out ill-typed
    candidates), re-typechecking to recover the shrunken term's type; `mk`
    rebuilds the concrete wrapper from the `(expr, type)` pair. (This avoids us
    needing to define separate shrinkers for types and `LExpr`s.) -/
private def shrinkTypedExpr (mk : LExpr' → LMonoTy → α) (e : LExpr') : List α :=
  (shrinkLExpr e).filterMap fun e' =>
    match LExpr.typeCheck (T := LExprParams') [] e' with
    | some τ' => some (mk e' τ')
    | none => none

instance : Shrinkable TypedExpr where
  shrink te := shrinkTypedExpr (⟨·, ·⟩) te.expr

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
  shrink te := shrinkTypedExpr (⟨·, ·⟩) te.expr

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
  checkPreservation te.expr te.ty = true

-- Progress (closed terms only): a well-typed closed term is either a value
-- or can take a step.
-- Falsified by quantifiers (`∀`/`∃`) — `LExpr.eval` has no reduction rule
-- for them, so `if (∀x. e) then ...` gets stuck.
@[reducible] def prop_progress (te : ClosedTypedExpr) : Prop :=
  checkProgress te.expr = true

-- Fvar preservation: evaluation does not introduce *new* free variables.
-- Free variables from the context (x, f, n) may appear in both the input
-- and output, but eval should not create fvars that weren't already present.
@[reducible] def prop_closedness_preservation (te : TypedExpr) : Prop :=
  checkFvarsPreserved te.expr = true

-- ── Resolve after erasure ────────────────────────────────────────────

/-- A closed expression generated using only `intBoolFactory` ops,
    suitable for round-tripping through `eraseTypes` + `resolve`. -/
structure ResolveTypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving BEq

instance : Repr ResolveTypedExpr where
  reprPrec te _ := s!"({ppExpr te.expr}) : {ppType te.ty}"

instance : Shrinkable ResolveTypedExpr where
  shrink te := shrinkTypedExpr (⟨·, ·⟩) te.expr

private def genResolveTypedExpr : Gen ResolveTypedExpr := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := Plausible.Gen) tvars depth
  let expr ← genLExprWithOps (G := Plausible.Gen) [] intBoolOpCtx [] tvars [] depth ty
  pure ⟨expr, ty⟩

instance : Arbitrary ResolveTypedExpr where
  arbitrary := Gen.backtrack (List.replicate 500 (1, genResolveTypedExpr))

/-- After erasing *all* type annotations, `resolve` infers a principal type that
    may be more general than the type the expression was generated at (e.g. a
    fully-erased `λx. x` resolves to `?a -> ?a`, of which `int -> int` is an
    instance). So we check that the original type is a substitution instance of
    the inferred type rather than syntactically equal to it.

    `resolve` can legitimately *fail* on a fully-erased quantifier whose body
    type is exactly the bound variable (e.g. `∃x. x`): with the binder
    annotation gone it assigns the bound variable a fresh type variable `?a`,
    infers the body's type as `?a`, and then rejects the quantifier because its
    rule checks the body type is literally `bool` rather than unifying it with
    `bool`. This is an incompleteness of `resolve` on erased quantifiers, not a
    soundness violation, so we treat resolve-failure as a (vacuous) pass and
    only assert the instance relation when `resolve` succeeds.

    The decision procedure (`checkResolveAfterErase`) and its helpers
    (`eraseAllTypes` / `isInstanceOf` / `resolveLContext`) are shared with the
    Tyche harness — see `StrataGenerators.HasTypeAGen.TestSupport`. -/
@[reducible] def prop_resolve_after_erase (te : ResolveTypedExpr) : Prop :=
  checkResolveAfterErase te.expr te.ty = true

/-- Run `resolve` on the fully-erased term and report the outcome as a string:
    `none` if the property holds (resolve succeeded and inferred a general-enough
    type), or `some msg` describing the counterexample — either the `resolve`
    error message verbatim, or the unexpected inferred type. -/
def resolveErrorMessage (te : ResolveTypedExpr) : Option String :=
  let erased := eraseAllTypes te.expr
  match LExpr.resolve resolveLContext Lambda.TEnv.default erased with
  | .ok (resolved, _) =>
    if isInstanceOf te.ty resolved.toLMonoTy then none
    else some s!"inferred {ppType resolved.toLMonoTy}, not an instance of {ppType te.ty}"
  | .error e => some s!"{e}"

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

-- The four single-verdict command properties — init-fresh, expr-typechecks,
-- set-preserves-var, store-type-preservation — are defined by the shared
-- `Properties.cmdSingleVerdict` bundle (see `StrataGenerators.PropertyNames`),
-- which pairs each name with its check in one place, so they are folded directly
-- into `cmdSuite` below rather than restated as `prop_*` wrappers here.

-- For a generated command sequence, the output context equals the input
-- context prepended with the newly defined variables (in reverse order,
-- since `init` conses onto the front).
@[reducible] def prop_cmds_context_growth (gc : GenCmdsWithCtx) : Prop :=
  checkContextGrowth gc.inCtx gc.outCtx gc.cmds = true

-- Symbolic/concrete agreement: whenever concrete execution (`Cmd.run`) succeeds,
-- symbolic simulation (`Cmd.eval`) also succeeds with the same store.
@[reducible] def prop_cmd_eval_run_agreement (gc : GenCmdWithCtx) : Prop :=
  checkEvalRunAgreement gc.cmd gc.inCtx = true

-- ── Function generation via Plausible.Gen ────────────────────────────

/-- A `Function` generated by `genFunction`, paired with the fvar context it was
    generated against (so the `fvars_annotated_by` property can be checked
    against the corresponding type map). -/
structure GenFunction where
  func : Function
  fctx : FVarCtx

instance : Repr GenFunction where
  reprPrec gf _ := formatFunc gf.func

-- Functions are generated whole (body/measure are drawn by sub-generators that
-- already respect the typing spec); we do not attempt structural shrinking.
instance : Shrinkable GenFunction where
  shrink _ := []

/-- Generate a function against `defaultFCtx`, exposing the fvar context so the
    property can consult the matching type map. Depth scales with Plausible's
    size parameter, mirroring `genCmdWith`. -/
private def genFunctionWith (fctx : FVarCtx) : Gen GenFunction := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let func ← genFunction (G := Plausible.Gen) fctx coreOpCtx depth
  pure ⟨func, fctx⟩

instance : Arbitrary GenFunction where
  arbitrary := Gen.backtrack (List.replicate 1000 (1, genFunctionWith defaultFCtx))

-- ── Function-level properties ────────────────────────────────────────

-- `fvars_annotated_by`: every free variable in the generated function's body
-- and measure is annotated consistently with the type map derived from the
-- fvar context it was generated against. This holds because `pickFVar` always
-- emits `fvar` nodes annotated with `some τ`, where `τ` is exactly the type the
-- variable carries in the fvar context.
@[reducible] def prop_function_fvars_annotated (gf : GenFunction) : Prop :=
  functionFvarsAnnotatedBy (fctxToTyMap gf.fctx) gf.func = true

-- ── Closed function generator (for typeCheck + round-trip + preservation) ──

/-- A `Function` generated with an *empty* fvar context. Bodies are closed (no
    free variables), so `Function.typeCheck` can succeed without an ambient
    context carrying those variables. -/
structure ClosedGenFunction where
  func : Function

instance : Repr ClosedGenFunction where
  reprPrec gf _ :=
    -- Show body/measure presence explicitly: the pretty-printer omits an absent
    -- body/measure, but that distinction is exactly what the completeness gap
    -- (measure-without-body) turns on, so make it visible in counterexamples.
    let tag := s!"[body={gf.func.body.isSome}, measure={gf.func.measure.isSome}]"
    s!"{tag}\n{formatFunc gf.func}"

instance : Shrinkable ClosedGenFunction where
  shrink _ := []

private def genClosedFunctionWith : Gen ClosedGenFunction := Gen.sized fun s => do
  let depth := max 2 (s / 20)
  let func ← genFunction (G := Plausible.Gen) [] coreOpCtx depth
  pure ⟨func⟩

instance : Arbitrary ClosedGenFunction where
  arbitrary := Gen.backtrack (List.replicate 2000 (1, genClosedFunctionWith))

-- ── Property 1: Function.typeCheck_annotated_sound ─────────────────────
--
-- Tests the *sorry*'d theorem `Function.typeCheck_annotated_sound` at
-- `Strata/Languages/Core/FunctionTypeSpecSound.lean:31`:
--
--   If `Function.typeCheck C Env func = .ok (func', _)` then `func'` satisfies
--   `FuncHasTypeA C Γ` for any Γ.
--
-- The decision procedure (`checkTypeCheckAnnotatedSound`, which reflects
-- `FuncHasTypeA` via `checkFuncHasTypeA` using `funcCheckContext`) is shared with
-- the Tyche harness — see `StrataGenerators.FunctionHasTypeAGen.TestSupport`.

@[reducible] def prop_function_typeCheck_annotated_sound (gf : ClosedGenFunction) : Prop :=
  checkTypeCheckAnnotatedSound gf.func = true

-- ── Property 2: Pretty-print / parse round-trip ───────────────────────
--
-- Embeds a generated `Function` in a trivial `Program`, pretty-prints it via
-- `Core.formatProgram`, re-parses via DDM, re-formats, and asserts string
-- equality. A parse failure is a genuine printer/parser bug (names are legal
-- Core identifiers by construction).
--
-- `formatFuncAsProgram`, `parseCoreProgram`, `parseCoreProgramErr`, the
-- structural shrinker (`shrinkWhile` et al.) and the failure predicates
-- (`failsRoundtripParsed`, `failsRoundtripParseFail`) are shared with the Tyche
-- harness — see `StrataGenerators.FunctionHasTypeAGen.Roundtrip`.

/-- The round-trip property: format → parse → re-format yields the same string.
    Returns `true` only if the round-trip succeeds. Runs in `IO`.

    A parse failure is scored as a **failure**, not a vacuous pass: the name
    generators (`genIdentName`) produce only legal Core identifiers by
    construction, so if the printed function does not parse back, the printer has
    emitted legal-but-unparseable output — a genuine round-trip bug to report. -/
def checkPrintParseRoundtrip (func : Function) : IO Bool := do
  let s1 := formatFuncAsProgram func
  match ← parseCoreProgram s1 with
  | some ast2 =>
    let s2 := (Core.formatProgram ast2).pretty
    pure (s1 == s2)
  | none => pure false  -- parse failure = round-trip bug (names are legal by construction)

-- ── Special-character identifier round-trip (minimal reproducers) ──────
--
-- The full-function round-trip fails on samples that bundle a name, typeargs,
-- types, a body, etc., so a failure can't be attributed to one cause. This
-- probe isolates a single generated identifier in one syntactic position at a
-- time, using an otherwise-trivial function, so a failure yields a minimal
-- reproducer: "identifier X in position P does not round-trip".
--
-- Identifiers are drawn from `genQuotedName`: legal Core identifiers (so a
-- failure is a genuine bug, not a generator artifact) that contain special
-- (non-alphanumeric) characters `. ' | \ ? ! @` in interior positions. This
-- deliberately exercises the special-character and pipe-escape paths that
-- `genIdentName` (fed to `genFunction`) never reaches.
--
-- `IdentPosition` and `minimalFuncWithName` are shared with the Tyche harness —
-- see `StrataGenerators.FunctionHasTypeAGen.TestSupport`.

/-- Round-trip a single identifier in one position. Returns `none` on success,
    or `some (renderedProgram, reparsedOrMismatch)` describing the failure. -/
def probeIdentRoundtrip (pos : IdentPosition) (name : String) :
    IO (Option (String × String)) := do
  let s1 := formatFuncAsProgram (minimalFuncWithName pos name)
  match ← parseCoreProgramErr s1 with
  | .error e => pure (some (s1, s!"parse-failure: {e.take 140}"))
  | .ok ast2 =>
    let s2 := (Core.formatProgram ast2).pretty
    if s1 == s2 then pure none
    else pure (some (s1, s2))

-- ── Property 3: Type preservation under evaluation ────────────────────
--
-- Corresponds to `Step.type_preserved` / `StepStar.type_preserved` /
-- `eval_denote_sound` (`Strata/DL/Lambda/Denote/LExprSemanticsConsistent.lean`).
-- The decision procedure (`checkFunctionBodyPreservation`) is shared with the
-- Tyche harness — see `StrataGenerators.FunctionHasTypeAGen.TestSupport`.

@[reducible] def prop_function_body_preservation (gf : ClosedGenFunction) : Prop :=
  checkFunctionBodyPreservation gf.func = true

-- ── Function typechecker completeness ─────────────────────────────────
-- Dual to the soundness property above. `genFunction` is proven sound (output
-- satisfies `FuncHasType'`), so `Function.typeCheck` should accept every generated
-- function. It does NOT — the spec permits a measure without a body, the algorithm
-- rejects it. Checks live in `StrataGenerators.StmtHasTypeAGen.TestSupport`
-- (`checkFunctionTypeCheckerComplete` / `funcRejectionImpliesMeasureNoBody`), run
-- against the full `Core.Factory` context so no operator spuriously fails to
-- resolve. The `funcDecl` gap in the statement test (#1) is the syntactic-statement
-- analogue of exactly this.

open StrataGenerators.Stmt.TestSupport in
-- Completeness: the typechecker accepts every generated function. FAILS on the
-- measure-without-body gap — asserted honestly, so a real failure is reported.
@[reducible] def prop_function_typeCheck_complete (gf : ClosedGenFunction) : Prop :=
  checkFunctionTypeCheckerComplete gf.func = true

open StrataGenerators.Stmt.TestSupport in
-- Every rejection is a measure-without-body function (pins the sole known gap).
@[reducible] def prop_function_rejection_only_measure (gf : ClosedGenFunction) : Prop :=
  funcRejectionImpliesMeasureNoBody gf.func = true

-- ── Statement generation via Plausible.Gen ────────────────────────────
--
-- `genProgramStmts` generates a well-typed Strata Core statement list
-- (`StmtsHasTypeA`), proven sound AND complete against the declarative typing
-- spec. We use it as a certified-well-typed oracle input for the statement
-- typechecker (property #1) and the Core statement-level transformations
-- (properties #3–#6, #9). All check predicates live in the shared module
-- `StrataGenerators.StmtHasTypeAGen.TestSupport`.

open StrataGenerators.Stmt.TestSupport

/-- A generated well-typed statement list. -/
structure GenStmts where
  stmts : List Statement

instance : Repr GenStmts where
  -- Render via Strata's own formatter (real Core concrete syntax), plus a summary
  -- of any `funcDecl` shapes: the CST formatter cannot represent a bodiless
  -- `funcDecl` statement (it substitutes a dummy body), and a bodiless funcDecl
  -- with a measure is exactly the typechecker-completeness counterexample, so the
  -- summary records the true shape the rendered form can't show.
  reprPrec gs _ :=
    let shapes := funcDeclShapesList gs.stmts
    let suffix := if shapes.isEmpty then "" else s!"\n  -- {" ".intercalate shapes}"
    formatStmts gs.stmts ++ suffix

-- Statement lists are generated whole by a sound+complete generator; we do not
-- attempt structural shrinking (a shrunk sub-list need not remain well-typed).
instance : Shrinkable GenStmts where
  shrink _ := []

/-- Generate a well-typed statement list. `size` (nesting/expression size) and
    the sequence length both scale with Plausible's size parameter. -/
-- Statement nesting `size` and sequence length `len` are capped low (≤ 3 / ≤ 4):
-- the properties under test don't need large programs, and a bigger `size`
-- multiplies the chance that *some* nested sub-generator hits its empty-support
-- fallback (`default`) — e.g. a `typeDecl` name clash or an `exit` with no
-- enclosing label — which forces `Gen.backtrack` to retry the *whole* list and
-- can exhaust its fuel at large Plausible sizes.
private def genStmtsWith : Gen GenStmts := Gen.sized fun s => do
  let size := max 1 (min 3 (s / 25))
  let len := max 1 (min 4 (s / 20))
  let (ss, _, _) ← StrataGenerators.Stmt.genProgramStmts (G := Plausible.Gen) [] coreOpCtx [] size len
  pure ⟨ss⟩

-- `genStmt` can hit the empty generator (`default`) in sub-cases (e.g. a
-- `typeDecl` name clash), so — like the other generators — we retry with fresh
-- randomness via `Gen.backtrack`.
instance : Arbitrary GenStmts where
  arbitrary := Gen.backtrack (List.replicate 4000 (1, genStmtsWith))

-- ── Statement-level properties (all currently unproven) ───────────────

-- The six statement-transform / typechecker properties (#1, #3, #4, #5a, #5b, #9)
-- are defined by the shared `Properties.stmtTransforms` bundle (see
-- `StrataGenerators.PropertyNames`), which pairs each name with its check in one
-- place, so they are folded directly into `stmtSuite` below rather than restated
-- as `prop_*` wrappers here. Only #6 keeps a wrapper — its Tyche panel records
-- extra breakdown, so it is not part of the shared bundle.

-- #6: `StmtToKleeneStmt` is defined exactly when the block has no
-- `exit`/`funcDecl`/`typeDecl` (and, for the invariant-loop caveat, not defined
-- when an invariant-bearing loop is present).
@[reducible] def prop_stmt_kleene_defined_iff (gs : GenStmts) : Prop :=
  checkKleeneDefinedIff gs.stmts = true

-- ── Test runner ──────────────────────────────────────────────────────

/-- Sample erased terms and print the `resolve` error messages behind any
    counterexamples to the resolve-after-erase property. Shows, per failure, the
    erased term and the verbatim `resolve` outcome, plus a tally of distinct
    error messages. Returns the number of counterexamples found. -/
def printResolveErrors (numTrials maxSize : Nat) : IO Nat := do
  let attempts := max numTrials 2000
  let mut shown := 0
  let mut msgTally : List (String × Nat) := []
  IO.println "    ── resolve error messages on counterexamples ──"
  for i in List.range attempts do
    let size := i % (maxSize + 1)
    let te ← try Gen.run (Arbitrary.arbitrary (α := ResolveTypedExpr)) size
             catch _ => pure ⟨.const () (.boolConst true), .bool⟩
    match resolveErrorMessage te with
    | none => pure ()
    | some msg =>
      -- Print the first 15 concrete examples (erased term → error).
      if shown < 15 then
        IO.println s!"    erased: {ppExpr (eraseAllTypes te.expr)}"
        IO.println s!"      → {msg}"
        shown := shown + 1
      -- Tally distinct messages (the error string, ignoring specific type-var ids).
      let key := msg
      msgTally := match msgTally.find? (·.1 == key) with
        | some _ => msgTally.map (fun (m, c) => if m == key then (m, c + 1) else (m, c))
        | none => (key, 1) :: msgTally
  IO.println ""
  IO.println s!"    distinct resolve error messages ({msgTally.length}):"
  for (m, c) in msgTally.reverse do
    IO.println s!"      [{c}×] {m}"
  return shown

-- ── IO-based round-trip checks (wrapped as `TestSeq.individualIO` nodes) ──
--
-- These two checks don't fit `checkIO` (they aren't plain `Prop`s): they run in
-- `IO`, shrink their own counterexamples, and print minimal reproducers as they
-- go. Each returns the `checkIO`-style tuple `(success, numSamples, totalTests,
-- errorMsg)` so it can be dropped into an `lspecIO` suite via `.individualIO`.

/-- Pretty-print each generated function to concrete syntax and parse it back,
    expecting an identical re-print. Shrinks and prints minimal reproducers for
    the first few parse failures and mismatches. Gates the suite (a
    legal-by-construction function that fails to round-trip is a printer/parser
    bug). -/
def roundtripFunctionAction (numTrials maxSize : Nat) : IO (Bool × Nat × Nat × Option String) := do
  let total := min numTrials 200
  let mut rtOk := 0
  let mut rtParseFail := 0
  let mut rtMismatch := 0
  for i in List.range total do
    let size := i % (maxSize + 1)
    let gf ← try Gen.run (Arbitrary.arbitrary (α := ClosedGenFunction)) size
             catch _ => pure ⟨default⟩
    let s := formatFuncAsProgram gf.func
    match ← parseCoreProgram s with
    | none =>
      -- Legal-by-construction names that fail to parse = printer/parser bug.
      rtParseFail := rtParseFail + 1
      if rtParseFail ≤ 3 then
        -- Shrink to a minimal unparseable witness and show the parser's error.
        let minF ← shrinkWhile failsRoundtripParseFail 1000 gf.func
        let ms1 := formatFuncAsProgram minF
        let err := match ← parseCoreProgramErr ms1 with
                   | .error e => e | .ok _ => "<parsed unexpectedly>"
        IO.println s!"    FAIL (parse): original: {s.replace "\n" " " |>.take 80}"
        IO.println s!"      shrunk (size {sizeFunc minF}): {ms1.replace "\n" " "}"
        IO.println s!"      parser error:                 {err.take 160}"
    | some ast2 =>
      let s2 := (Core.formatProgram ast2).pretty
      if s == s2 then
        rtOk := rtOk + 1
      else
        rtMismatch := rtMismatch + 1
        if rtMismatch ≤ 3 then
          -- Shrink this mismatch to a minimal parses-but-doesn't-round-trip witness.
          let minF ← shrinkWhile failsRoundtripParsed 1000 gf.func
          let ms1 := formatFuncAsProgram minF
          let ms2 ← (do match ← parseCoreProgram ms1 with
                        | some a => pure (Core.formatProgram a).pretty
                        | none => pure "<parse-failed>")
          IO.println s!"    FAIL (mismatch): original: {s.replace "\n" " " |>.take 80}"
          IO.println s!"      shrunk (size {sizeFunc minF}): {ms1.replace "\n" " "}"
          IO.println s!"      re-formatted to:              {ms2.replace "\n" " "}"
  if rtParseFail == 0 && rtMismatch == 0 then
    pure (true, rtOk, total, none)
  else
    pure (false, rtOk, total,
      some s!"{rtParseFail} parse-failures, {rtMismatch} mismatches, {rtOk} ok")

/-- Special-character identifier probe: for each position (funcName/typeArg/binder)
    render a legal identifier containing special characters and check it round-trips,
    printing one reproducer per distinct (position, outcome, char-class). This is a
    **diagnostic** — it reports how many probes fail but does not gate the exit code
    (special-character round-tripping is a known limitation). Returns the number of
    failing and passing probes. -/
def specialCharProbeDiagnostic (numTrials maxSize : Nat) : IO (Nat × Nat) := do
  let positions := [IdentPosition.funcName, .typeArg, .binder]
  let mut probeOk := 0
  let mut probeFail := 0
  let mut shownReprs : List String := []
  for i in List.range (min numTrials 200) do
    let size := i % (maxSize + 1)
    let name ← try Gen.run genQuotedName size catch _ => pure "x"
    for pos in positions do
      match ← probeIdentRoundtrip pos name with
      | none => probeOk := probeOk + 1
      | some (rendered, outcome) =>
        probeFail := probeFail + 1
        -- One reproducer per distinct (position, outcome, triggering-char-class),
        -- so different mechanisms surface separately instead of collapsing.
        let cls :=
          if name.any (· == '.') then "dot"
          else if name.any (· == '|') then "pipe"
          else if name.any (· == '\\') then "backslash"
          else if name.any (· == '\'') then "apostrophe"
          else if name.toList.head?.map (·.isDigit) == some true then "leading-digit"
          else "other"
        let isParseFail := outcome.startsWith "parse-failure"
        let key := s!"{pos.label}/{if isParseFail then "parse" else "mismatch"}/{cls}"
        if !shownReprs.contains key then
          shownReprs := key :: shownReprs
          IO.println s!"    REPRO [{pos.label}] class={cls} name={name.quote}"
          IO.println s!"           rendered: {rendered.replace "\n" " "}"
          if isParseFail then
            IO.println s!"           {outcome.replace "\n" " "}"
          else
            IO.println s!"           reparsed: {outcome.replace "\n" " "}"
  return (probeFail, probeOk)

-- ── CLI ────────────────────────────────────────────────────────────────

/-- Parsed command-line configuration for the merged driver. -/
structure CliConfig where
  numTrials : Nat
  maxSize : Nat
  tycheEnabled : Bool
  tycheOut : String
  tycheSamples : Nat

/-- Parse `args` into a `CliConfig`. Positional args are `[numTrials] [maxSize]`;
    `--`-prefixed flags configure the Tyche visualization (on by default). -/
def parseArgs (args : List String) : CliConfig :=
  let flags := args.filter (·.startsWith "--")
  let positional := args.filter (fun a => !a.startsWith "--")
  let flagValue (key : String) : Option String :=
    (flags.find? (·.startsWith key)).map (·.drop key.length |>.toString)
  { numTrials := (positional[0]? >>= String.toNat?).getD 1000
    maxSize := (positional[1]? >>= String.toNat?).getD 100
    tycheEnabled := !flags.contains "--no-tyche"
    tycheOut := (flagValue "--tyche-out=").getD "tyche_output.jsonl"
    tycheSamples := ((flagValue "--tyche-samples=").bind String.toNat?).getD 1000 }

def main (args : List String) : IO UInt32 := do
  let cli := parseArgs args
  let numTrials := cli.numTrials
  let maxSize := cli.maxSize
  let cfg : Configuration := { numInst := numTrials, maxSize }

  IO.println s!"Running property-based tests ({numTrials} trials, max size {maxSize})..."
  IO.println ""

  -- Expression-generator properties.
  let exprSuite : TestSeq :=
    checkIO PropertyNames.exprTypecheck
      (∀ te : TypedExpr, prop_typecheck te) (cfg := cfg) $
    checkIO PropertyNames.exprPreservation
      (∀ te : ClosedTypedExpr, prop_preservation te) (cfg := cfg) $
    checkIO PropertyNames.exprProgress
      (∀ te : ClosedTypedExpr, prop_progress te) (cfg := cfg) $
    checkIO PropertyNames.exprFvarsPreserved
      (∀ te : TypedExpr, prop_closedness_preservation te) (cfg := cfg) $
    checkIO PropertyNames.exprResolveAfterErase
      (∀ te : ResolveTypedExpr, prop_resolve_after_erase te) (cfg := cfg)

  -- Command-generator properties. The four single-verdict properties are folded
  -- from the shared `Properties.cmdSingleVerdict` bundle (name↔check paired in one
  -- place, also driving the Tyche panels), so their names can never be attached to
  -- the wrong check. Context-growth and eval-agreement have distinct shapes and
  -- are stated directly.
  let cmdTail : TestSeq :=
    checkIO PropertyNames.cmdContextGrowth
      (∀ gc : GenCmdsWithCtx, prop_cmds_context_growth gc) (cfg := cfg) $
    checkIO PropertyNames.cmdEvalRunAgreement
      (∀ gc : GenCmdWithCtx, prop_cmd_eval_run_agreement gc) (cfg := cfg)
  let cmdSuite : TestSeq :=
    Properties.cmdSingleVerdict.foldr
      (fun p rest => checkIO p.name
        (∀ gc : GenCmdWithCtx, p.check (gc.cmd, gc.inCtx) = true) (cfg := cfg) rest)
      cmdTail

  -- Function-generator properties. The two format→parse round-trip checks below
  -- run in `IO` and shrink/print their own reproducers, so they join the suite as
  -- custom `TestSeq.individualIO` nodes rather than `checkIO` `Prop`s. The
  -- special-character probe is a diagnostic (see below) and is not part of this
  -- gating suite.
  let functionSuite : TestSeq :=
    checkIO PropertyNames.fnFvarsAnnotated
      (∀ gf : GenFunction, prop_function_fvars_annotated gf) (cfg := cfg) $
    -- Property 1: Function.typeCheck_annotated_sound
    checkIO PropertyNames.fnTypeCheckSound
      (∀ gf : ClosedGenFunction, prop_function_typeCheck_annotated_sound gf) (cfg := cfg) $
    -- Property 3: type preservation under evaluation (Step.type_preserved / StepStar.type_preserved)
    checkIO PropertyNames.fnBodyPreservation
      (∀ gf : ClosedGenFunction, prop_function_body_preservation gf) (cfg := cfg) $
    -- Function typechecker completeness. FAILS on the measure-without-body gap
    -- (spec permits it, algorithm rejects it) — the function-level analogue of the
    -- statement `funcDecl` gap (#1), asserted honestly as a real failure.
    checkIO PropertyNames.fnTypeCheckComplete
      (∀ gf : ClosedGenFunction, prop_function_typeCheck_complete gf) (cfg := cfg) $
    -- Every typeCheck rejection is a measure-without-body function (pins the gap).
    checkIO PropertyNames.fnRejectionOnlyMeasure
      (∀ gf : ClosedGenFunction, prop_function_rejection_only_measure gf) (cfg := cfg) $
    -- Property 2: pretty-print / parse round-trip (IO-based, shrinks + prints reproducers)
    .individualIO PropertyNames.fnRoundtrip none
      (roundtripFunctionAction numTrials maxSize) .done

  -- Statement-generator properties (transforms + typechecker). The six transform
  -- / typechecker properties (#1, #3, #4, #5a, #5b, #9) are folded from the shared
  -- `Properties.stmtTransforms` bundle (name↔check paired in one place, also
  -- driving the Tyche panels), so their names can never be attached to the wrong
  -- check. #1 FAILS honestly on the funcDecl gap (the spec's funcDecl rule is
  -- strictly more permissive than the algorithm) — a genuine spec/algorithm
  -- divergence surfaced as a real failure. #6 (Kleene definedness) has a richer
  -- Tyche panel, so it is stated directly here.
  let stmtSuite : TestSeq :=
    Properties.stmtTransforms.foldr
      (fun p rest => checkIO p.name
        (∀ gs : GenStmts, p.check gs.stmts = true) (cfg := cfg) rest)
      (checkIO PropertyNames.stmtKleeneDefinedIff
        (∀ gs : GenStmts, prop_stmt_kleene_defined_iff gs) (cfg := cfg))

  let exitCode ← lspecIO (.ofList [
    ("expr", [exprSuite]),
    ("cmd", [cmdSuite]),
    ("function", [functionSuite]),
    ("stmt", [stmtSuite])
  ]) []

  -- Always-run diagnostics (do not gate the exit code):
  --
  -- Surface the actual `resolve` error messages behind any resolve-after-erase
  -- counterexamples. The standard Plausible failure output only shows one shrunk
  -- term; here we sample fresh terms and print the resolve errors verbatim so the
  -- failure mode (e.g. "Quantifier body has non-Boolean type") is visible.
  IO.println ""
  IO.println "Resolve-after-erase error diagnostics:"
  let _ ← printResolveErrors numTrials maxSize

  -- Special-character identifier probe: minimal reproducers per position, using
  -- legal identifiers that contain special (non-alphanumeric) characters
  -- (`genQuotedName`). Reported as a diagnostic (known limitation), not gated.
  IO.println ""
  IO.println "Special-character identifier round-trip diagnostics:"
  let (probeFail, probeOk) ← specialCharProbeDiagnostic numTrials maxSize
  if probeFail == 0 then
    IO.println s!"  PASS ({probeOk} ident/position round-trips)"
  else
    IO.println s!"  FOUND {probeFail} failing ident/position cases ({probeOk} ok) — see reproducers above"

  -- Tyche visualization pass (on by default; disable with `--no-tyche`). Writes
  -- one JSONL panel per property to `cli.tycheOut`, using the *same* shared
  -- `check*` verdicts as the LSpec suite above. Never affects the exit code.
  if cli.tycheEnabled then
    IO.println ""
    IO.println s!"Generating Tyche visualizations ({cli.tycheSamples} samples/panel)..."
    let startTime ← IO.monoMsNow
    let handle ← IO.FS.Handle.mk cli.tycheOut .write
    runTychePanels handle cli.tycheSamples startTime
    IO.println s!"Tyche output written to {cli.tycheOut}"
    IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
  else
    IO.println ""
    IO.println "Tyche visualizations disabled (--no-tyche)."

  return exitCode
