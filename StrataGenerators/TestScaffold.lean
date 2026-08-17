import StrataGenerators.Properties
import StrataGenerators.RetryGen
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.HasTypeAGen.SmtEval
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.Roundtrip
import StrataGenerators.FunctionHasTypeAGen.Shrink
import StrataGenerators.StmtHasTypeAGen.TestSupport
-- Supplies `relabelProcs` and `shrinkProcsList`, backing the `Shrinkable GenProcs`
-- instance so Plausible reports minimal well-typed procedure counterexamples.
import StrataGenerators.ProcedureHasTypeAGen.Shrink
-- The whole-program generator, and the whole-program shrinker backing the
-- `Shrinkable GenProgram` instance (plus the `checkProgram*` predicates).
import StrataGenerators.ProgramGen
import StrataGenerators.ProgramGen.Shrink
-- The ADT-derived-call test support (`checkProgramADTCalls*` predicates).
import StrataGenerators.ProgramGen.TestSupport
import Basalt.PlausibleGen
import Plausible
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
# Shared test scaffold (harness-independent)

Everything the property-based test suite needs that does **not** depend on the
test-runner library (LSpec) lives here: the generator wrapper structures and
their `Repr`/`Shrinkable`/`Arbitrary` instances, the `prop_*` property
definitions, the IO-based checks/diagnostics (`roundtripFunctionAction`,
`specialCharProbeDiagnostic`, `printResolveErrors`), and the CLI parser
(`CliConfig`/`parseArgs`).

This module is the **single source of truth** imported by *both* test
executables — the LSpec-based `TestMain` (the reference "nice harness") and the
Plausible-only `PlainTestMain` (which de-risks dropping the LSpec dependency). By
sharing the properties, generators, and CLI here, the two drivers cannot drift:
they exercise the same checks over the same generated inputs and only differ in
how results are formatted and aggregated into an exit code.
-/

open Lambda RandomChoice ArbNat Basalt.PlausibleGen Plausible Core Imperative
open Strata Strata.CoreDDM
open StrataDDM (initDialect)

-- ── Typed expression generation via Plausible.Gen ────────────────────

/-- A generated expression paired with its type. May contain free variables
    from `defaultFCtx`. -/
structure TypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving BEq

instance : Repr TypedExpr where
  reprPrec te _ := s!"({ppExpr te.expr}) : {ppType te.ty}"

-- The structural expression shrinker `shrinkLExpr` (and its helper
-- `immediateSubtermsWithoutBinders`) now lives in
-- `StrataGenerators.HasTypeAGen.TestSupport` so the command / statement /
-- function shrinkers can reuse the exact same reduction rules. It is imported
-- transitively here.

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
  -- `retryGenArg` is the retry continuation: on a failed *subterm* it redraws that
  -- subterm rather than letting the failure discard the whole term. It applies at
  -- every nesting level, which is what the outer `retryGen` below cannot reach —
  -- without it, one unfillable leaf deep in a term costs a full redraw. Measured
  -- at depth 3 (target `int`): mean root attempts per success drops from ~6.0 to
  -- ~1.0. The outer `retryGen` is still needed for the root draw itself.
  let expr ← genLExprWithOps (G := Plausible.Gen) fctx coreMonoOps corePolyOps tvars []
               depth ty 3 (retryGenArg 20)
  pure ⟨expr, ty⟩

-- `genLExpr` can fail (via `default`) when a depth-0 arrow case has no
-- bvar/fvar/op in context. Since `Plausible.Gen` doesn't backtrack on its
-- own, we use `retryGen` to retry with fresh randomness on failure.
instance : Arbitrary TypedExpr where
  arbitrary := retryGen 500 (genTypedExprWith defaultFCtx)

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
  arbitrary := retryGen 500 ((fun te => ⟨te.expr, te.ty⟩) <$> genTypedExprWith [])

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
--     is the identity (proved in LExprEvalTests.lean), so this property
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

/-- A closed expression generated over `coreOpCtx`, the operators of
    `coreFactory`,
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
  -- See `genTypedExprWith`: `retryGenArg` retries failed subterms in place.
  let expr ← genLExprWithOps (G := Plausible.Gen) [] coreOpCtx [] tvars [] depth ty 3
               (retryGenArg 20)
  pure ⟨expr, ty⟩

instance : Arbitrary ResolveTypedExpr where
  arbitrary := retryGen 500 genResolveTypedExpr

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

-- Shrink the command with the shared structural command shrinker (keeps it
-- well-typed via `checkExprTypechecks`), holding the input context fixed and
-- recomputing the output context from the shrunk command so the wrapper stays
-- internally consistent (`inCtx` extended with any variable the command defines).
instance : Shrinkable GenCmdWithCtx where
  shrink gc := (shrinkCmd gc.cmd).map fun c' =>
    { gc with cmd := c', outCtx := cmdOutCtx gc.inCtx c' }

private def genCmdWith (ctx : VarCtx) : Gen GenCmdWithCtx := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ⟨cmd, ctx'⟩ ← genCmd (G := Plausible.Gen) coreMonoOps tvars [] ctx depth
  pure ⟨cmd, ctx, ctx'⟩

private def genCmdFromBuiltCtx (ctxSize : Nat) : Gen GenCmdWithCtx := do
  let depth := 2
  let tvars : List TyIdentifier := []
  let (_, baseCtx) ← genCmds (G := Plausible.Gen) coreMonoOps tvars [] [] depth ctxSize
  let ⟨cmd, ctx'⟩ ← genCmd (G := Plausible.Gen) coreMonoOps tvars [] baseCtx depth
  pure ⟨cmd, baseCtx, ctx'⟩

instance : Arbitrary GenCmdWithCtx where
  arbitrary := retryGen 1000 (genCmdFromBuiltCtx 3)

/-- A generated command sequence paired with its context. -/
structure GenCmdsWithCtx where
  cmds : List (Cmd Expression)
  inCtx : VarCtx
  outCtx : VarCtx

instance : Repr GenCmdsWithCtx where
  reprPrec gc _ :=
    let cmdStrs := gc.cmds.map ppCmd |> "; ".intercalate
    s!"{cmdStrs}  [in: {ppVarCtx gc.inCtx}, out: {ppVarCtx gc.outCtx}]"

-- Shrink the command sequence (drop or shrink individual commands), holding the
-- input context fixed and recomputing the output context from the shrunk
-- sequence so `checkContextGrowth` still relates `inCtx` and `outCtx`.
instance : Shrinkable GenCmdsWithCtx where
  shrink gc := (shrinkCmds gc.inCtx gc.cmds).map fun cs' =>
    { gc with cmds := cs', outCtx := cmdsOutCtx gc.inCtx cs' }

private def genCmdsWithCtx : Gen GenCmdsWithCtx := do
  let depth := 2
  let n := 4
  let tvars : List TyIdentifier := []
  let (cmds, ctx') ← genCmds (G := Plausible.Gen) coreMonoOps tvars [] [] depth n
  pure ⟨cmds, [], ctx'⟩

instance : Arbitrary GenCmdsWithCtx where
  arbitrary := retryGen 1000 genCmdsWithCtx

-- ── Command-level properties ─────────────────────────────────────────

-- The four single-verdict command properties — init-fresh, expr-typechecks,
-- set-preserves-var, store-type-preservation — are defined by the shared
-- `Properties.cmdSingleVerdict` bundle (see `StrataGenerators.Properties`),
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

-- Shrink the function structurally (drop body/measure/inputs/type-args, shrink
-- types, shrink body/measure expressions), keeping the fvar context fixed. Every
-- candidate satisfies `funcWellFormed`, so it stays well-typed; and because
-- `shrinkLExpr` only reduces to sub-terms (never introducing a fresh, differently
-- annotated fvar), the fvar-annotation property continues to hold against the
-- unchanged `fctx`.
instance : Shrinkable GenFunction where
  shrink gf := (shrinkFuncWellFormed gf.func).map fun f' => { gf with func := f' }

/-- Generate a function against `defaultFCtx`, exposing the fvar context so the
    property can consult the matching type map. Depth scales with Plausible's
    size parameter, mirroring `genCmdWith`. -/
private def genFunctionWith (fctx : FVarCtx) : Gen GenFunction := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let func ← genFunction (G := Plausible.Gen) fctx coreMonoOps depth
  pure ⟨func, fctx⟩

instance : Arbitrary GenFunction where
  arbitrary := retryGen 1000 (genFunctionWith defaultFCtx)

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

-- Same structural function shrinker as `GenFunction`. `funcWellFormed` admits a
-- measure-without-body function (body absent ⇒ vacuously body-typed), so the
-- shrinker *preserves* that shape — the very counterexample the completeness
-- properties (`prop_function_typeCheck_complete` / `prop_function_rejection_only_measure`)
-- hunt for — and can even reach it by dropping a body while keeping the measure,
-- yielding a minimal witness rather than discarding it.
instance : Shrinkable ClosedGenFunction where
  shrink gf := (shrinkFuncWellFormed gf.func).map fun f' => { gf with func := f' }

private def genClosedFunctionWith : Gen ClosedGenFunction := Gen.sized fun s => do
  let depth := max 2 (s / 20)
  let func ← genFunction (G := Plausible.Gen) [] coreMonoOps depth
  pure ⟨func⟩

instance : Arbitrary ClosedGenFunction where
  arbitrary := retryGen 2000 genClosedFunctionWith

-- ── Property 1: Function.typeCheck_annotated_sound ─────────────────────
--
-- Tests the *sorry*'d theorem `Function.typeCheck_annotated_sound` at
-- `Strata/Languages/Core/FunctionTypeSpecSound.lean`:
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
-- resolve. The `funcDecl` gap in the statement test is the syntactic-statement
-- analogue of exactly this.

open StrataGenerators.Stmt.TestSupport in
-- Completeness: the typechecker accepts every generated function. Asserted
-- unweakened, so the measure-without-body gap is reported rather than masked.
@[reducible] def prop_function_typeCheck_complete (gf : ClosedGenFunction) : Prop :=
  checkFunctionTypeCheckerComplete gf.func = true

open StrataGenerators.Stmt.TestSupport in
-- Every rejection is a measure-without-body function (pins the sole known gap).
@[reducible] def prop_function_rejection_only_measure (gf : ClosedGenFunction) : Prop :=
  funcRejectionImpliesMeasureNoBody gf.func = true

-- ── Statement generation via Plausible.Gen ────────────────────────────
--
-- `genProgramStmts` generates a well-typed Strata Core statement list
-- (`StatementsHasTypeA`), proven sound AND complete against the declarative typing
-- spec. We use it as a certified-well-typed oracle input for the statement
-- typechecker and the Core statement-level transformations. All check predicates
-- live in the shared module
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

-- Shrink the statement list structurally (drop a statement, replace one by a
-- smaller one, or splice a compound's body in place of the compound), keeping
-- only candidates the algorithmic typechecker still accepts (`shrinkStmts`
-- filters on `checkTypeChecks`). A shrunk sub-list *does* remain well-typed by
-- construction — the well-typedness invariant is re-established by re-checking
-- the whole list rather than assumed to be preserved locally.
instance : Shrinkable GenStmts where
  shrink gs := (shrinkStmts gs.stmts).map (⟨·⟩)

/-- Generate a well-typed statement list. `size` (nesting/expression size) and
    the sequence length both scale with Plausible's size parameter. -/
-- Statement nesting `size` and sequence length `len` are capped low (≤ 3 / ≤ 4):
-- the properties under test don't need large programs, and a bigger `size`
-- multiplies the chance that *some* nested sub-generator hits its empty-support
-- fallback (`default`) — e.g. a `typeDecl` name clash or an `exit` with no
-- enclosing label — which forces `retryGen` to redraw the *whole* statement list
-- and can exhaust its fuel at large Plausible sizes.
private def genStmtsWith : Gen GenStmts := Gen.sized fun s => do
  let size := max 1 (min 3 (s / 25))
  let len := max 1 (min 4 (s / 20))
  let (ss, _, _) ← StrataGenerators.Stmt.genProgramStmts (G := Plausible.Gen) coreMonoOps [] size len
  pure ⟨ss⟩

-- `genStmt` can hit the empty generator (`default`) in sub-cases (e.g. a
-- `typeDecl` name clash), so — like the other generators — we retry with fresh
-- randomness via `retryGen`.
instance : Arbitrary GenStmts where
  arbitrary := retryGen 4000 genStmtsWith

-- ── Statement-level properties (all currently unproven) ───────────────

-- The six statement-transform / typechecker properties
-- are defined by the shared `Properties.stmtTransforms` bundle (see
-- `StrataGenerators.Properties`), which pairs each name with its check in one
-- place, so they are folded directly into `stmtSuite` below rather than restated
-- as `prop_*` wrappers here. Only Kleene definedness keeps a wrapper — its Tyche
-- panel records extra breakdown, so it is not part of the shared bundle.

-- Kleene definedness: `StmtToKleeneStmt` is defined exactly when the block has no
-- `exit`/`funcDecl`/`typeDecl` (and, for the invariant-loop caveat, not defined
-- when an invariant-bearing loop is present).
@[reducible] def prop_stmt_kleene_defined_iff (gs : GenStmts) : Prop :=
  checkKleeneDefinedIff gs.stmts = true

-- ── Procedure generation via Plausible.Gen ────────────────────────────
--
-- `genProcedure` generates a well-typed Strata Core procedure (`ProcHasTypeA`),
-- proven sound AND complete against the declarative typing spec. We assemble a
-- *list* of them into a multi-declaration `Program` and use it as a
-- certified-well-typed oracle input for the three Core transform passes
-- (FilterProcedures, PrecondElim, ANFEncoder). All check predicates live in the
-- shared module `StrataGenerators.ProcedureHasTypeAGen.TestSupport`, folded into
-- the suites via the `Properties.procTransforms` bundle.

open StrataGenerators.Procedure.TestSupport

/-- A generated list of well-typed procedures, to be assembled into a program.
    The names are rewritten to `P0, P1, …` so procedure identities never collide
    (the generator draws each name independently, so two procedures could
    otherwise share a name and confound the name-based filter/order checks). -/
structure GenProcs where
  procs : List Core.Procedure

instance : Repr GenProcs where
  -- Render the assembled program via Strata's own formatter (real Core concrete
  -- syntax), so a counterexample shows exactly the program the pass ran on.
  reprPrec gp _ :=
    let prog : Core.Program := { decls := gp.procs.map (Core.Decl.proc · .empty) }
    (Core.formatProgram prog).pretty

-- Shrink via the shared procedure shrinker `shrinkProcsList`, which offers both
-- dropping a whole procedure *and* reducing one procedure in place (its body via
-- `shrinkStmtsList`, its pre/postconditions via `shrinkLExpr`), relabelling the
-- survivors `P0…Pk`. Every candidate is re-checked with Strata's own
-- `Procedure.typeCheck`, so a reported counterexample is always a *well-typed*
-- program — which matters because these properties are only meaningful on
-- well-typed input. Headers are held fixed, so each procedure keeps its signature.
instance : Shrinkable GenProcs where
  shrink gp := (shrinkProcsList gp.procs).map (⟨·⟩)

-- Per-procedure nesting `size` is capped at 2 and body length at 3, and the
-- procedure count at 2–4: the transform properties don't need large programs, and
-- (as with `genStmtsWith`) a bigger `size` multiplies the chance a nested
-- sub-generator hits its empty-support fallback, forcing a retry of the whole
-- procedure and risking fuel exhaustion at large Plausible sizes. The 8000-retry
-- budget was tuned so this never throws through max size 100.
--
-- The procedures are generated **left to right into an acyclic call DAG**: the
-- body of procedure `i` is generated against the signatures of the
-- already-generated siblings `0..i-1` (named `P0…P{i-1}` — exactly what
-- `relabelProcs` assigns each position below, so the `call`s and the renamed
-- headers line up). This lets a body call its siblings: a body may emit `call P{j}`
-- for `j < i`, so the assembled program's call graph carries real edges and the
-- callee-closure / call-graph dimensions of the FilterProcedures/PrecondElim
-- properties are no longer vacuous. **Polymorphic** siblings are now callable too
--: `headerProcSig` records the callee's `typeArgs`, and `genCallStmt`
-- samples a concrete instantiation `σ` at the call site (`ProcSigCorresponds` no
-- longer requires `typeArgs = []`).
private def genProcsWith : Gen GenProcs := Gen.sized fun s => do
  let n := max 2 (min 4 (2 + s / 30))
  let size := max 1 (min 2 (s / 30))
  let len := max 1 (min 3 (s / 25))
  let (ps, _) ← (List.range n).foldlM
    (fun (acc : List Core.Procedure × StrataGenerators.Stmt.ProcSigCtx) (i : Nat) => do
      let proc ← (retryGen 8000
        (StrataGenerators.Procedure.genProcedure (G := Plausible.Gen)
          corePartialOps acc.2 LContext.default {} size len) : Gen Core.Procedure)
      -- Add this procedure to the callable context (its post-relabel name is
      -- `P{i}`; its generated header name is discarded). Both monomorphic and
      -- polymorphic siblings are callable — the call site instantiates `typeArgs`.
      let sigs := acc.2 ++ [StrataGenerators.Procedure.headerProcSig s!"P{i}" proc.header]
      pure (acc.1 ++ [proc], sigs))
    (([], []) : List Core.Procedure × StrataGenerators.Stmt.ProcSigCtx)
  pure ⟨relabelProcs ps⟩

instance : Arbitrary GenProcs where
  arbitrary := retryGen 8000 genProcsWith

-- The thirteen procedure/transform properties (four FilterProcedures, five
-- PrecondElim, four ANFEncoder) are defined by the shared
-- `Properties.procTransforms` bundle, so they are folded directly into
-- `procSuite` below rather than restated as `prop_*` wrappers here. Two of them
-- state a faithful `changed ↔ program changed` contract that the pass violates:
-- `proc: FilterProcedures changed flag is faithful` (the pass hardcodes
-- `changed := true` even when it removes nothing) and `proc: PrecondElim changed
-- flag is faithful` (the `.funcDecl` branch reports unchanged while inserting a
-- `$$wf` block).

-- ── Whole-program generation via Plausible.Gen ─────────────────────────
--
-- `genProgram` generates a whole well-typed Strata Core `Program` — every
-- declaration kind, with the ambient context threaded across the declaration fold
-- — and is proven sound against the declarative spec `ProgramHasTypeA`
-- (`ProgramGen.SoundProgram`). Unlike `GenProcs`, which assembles a program out of
-- procedures only, this exercises abstract types, aliases, axioms, `distinct`,
-- datatype blocks and functions as well.
--
-- Three suites quantify over this type: the whole-program checks of
-- `Properties.programChecks`, the ADT-derived-call checks of
-- `Properties.programADTProps`, and the printer-expressiveness property of
-- `StrataGenerators.PrinterCoverage` — the last needs a whole `Program` because
-- the unprintable constructs are spread across type declarations (`bitvec` widths
-- in a signature), expressions (`Bv↔Int` operators) and statements (bodiless
-- `funcDecl`), and `genProgram` reaches all three.
--
-- This is also the only place the ADT-derived-function work is observable
-- end-to-end: a datatype block extends the operator vocabulary, and *later*
-- functions and procedures draw from it, so their bodies can call the block's
-- constructors, testers, and safe/unsafe field accessors. `derivedCallCoverage`
-- below reports that as a statistic.

open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport

/-- A generated whole program. -/
structure GenProgram where
  prog : Core.Program

instance : Repr GenProgram where
  -- Render via Strata's own formatter (real Core concrete syntax), so a
  -- counterexample shows exactly the program under test, followed by the shared
  -- `programStatusNote`. That note matters because a typechecker-rejected program
  -- (~60% of draws) is one the shrinker cannot minimize — its oracle *is* that
  -- typechecker — so the note names the gap responsible instead of leaving the
  -- reader to infer it from an unreduced program, and falls back to the checker's
  -- verbatim diagnostic when the rejection matches no known gap. Sharing the
  -- function with the Tyche panel renderer keeps the two views from drifting.
  reprPrec gp _ :=
    (Core.formatProgram gp.prog).pretty ++ programStatusNote gp.prog

-- Shrink via the whole-program shrinker `shrinkProgram`: drop a declaration,
-- truncate to a prefix, cut every gap-bearing declaration at once, or reduce one
-- declaration in place (delegating to the procedure / function / statement /
-- expression shrinkers below it). Every candidate is re-checked with Strata's own
-- `Program.typeCheck`, so a reported counterexample is always a well-typed
-- program; declaration order is preserved and nothing is renamed.
instance : Shrinkable GenProgram where
  shrink gp := (shrinkProgram gp.prog).map (⟨·⟩)

-- `numDecls` is capped at 2–5 and scales with Plausible's size parameter. As with
-- `genProcsWith`, the retry budget has to absorb the residual `inhabitedWitness`
-- failure in the expression generator (a compound argument type nothing in scope
-- inhabits): each declaration is an independent chance to hit it, so whole-program
-- success decays geometrically in `numDecls`.
--
-- The fuel is 30000, matching `ProgramGen.sample`'s default. That default rose from
-- 4000 once function and procedure bodies could call a datatype's derived functions:
-- a call to a *polymorphic* datatype's tester or accessor goes through `IndirPoly`,
-- which samples instantiations, and an unfillable sample is another `inhabitedWitness`
-- failure for the retry loop to absorb (measured 1/8 versus 8/8 draws surviving at
-- `numDecls = 12` — see the `sample` docstring). `numDecls ≤ 5` here is far below that, so
-- 30000 is ample rather than tight.
private def genProgramWith : Gen GenProgram := Gen.sized fun s => do
  let numDecls := max 2 (min 5 (2 + s / 25))
  let prog ← (retryGen 30000 (ProgramGen.genProgram (G := Plausible.Gen) numDecls {})
    : Gen Core.Program)
  pure ⟨prog⟩

instance : Arbitrary GenProgram where
  arbitrary := retryGen 8000 genProgramWith

-- ── Whole-program shrinker diagnostic ─────────────────────────────────
--
-- The six whole-program properties come from the shared `Properties.programChecks`
-- bundle, so they are folded directly into each driver's `programSuite` rather than
-- restated as `prop_*` wrappers here.
--
-- What the bundle cannot show is how well the *shrinker* works. Its one reliable
-- failure (`programTypecheck`) fails only on gap-bearing programs, which are
-- precisely the ones no shrinker with this oracle can minimize; the one shrinkable
-- failure (`programTypeCheckIdem`) fires on roughly 1 draw in 500, so most runs do
-- not see it. On a run that hits neither, the `Shrinkable GenProgram` instance goes
-- unexercised and a regression in it would pass unnoticed until the day it matters.
--
-- This diagnostic closes that hole: it minimizes each sampled program against a
-- deliberately-always-failing property, and reports the reduction achieved plus the
-- two invariants that matter. It is a diagnostic, not a gated property — it
-- measures shrinker quality rather than asserting a fact about Strata.

/-- Exercise the whole-program shrinker on freshly sampled programs and report how
    far it reduces them, checking on the way that every candidate it emits is
    well-typed and that no reduction leaves a `requires` clause stranded.

    The target property is `sizeProgram p ≤ 3`, chosen because it fails on
    essentially every generated program and keeps failing as the program shrinks, so
    the minimizer runs to its fixpoint and the reported ratio measures the
    shrinker's reach rather than an early exit.

    Returns `(candidates, illTyped, stranded)` — the second and third must be 0. -/
def programShrinkDiagnostic (numTrials : Nat) : IO (Nat × Nat × Nat) := do
  let samples := max 1 (min 20 numTrials)
  let mut candidates := 0
  let mut illTyped := 0
  let mut stranded := 0
  let mut sizeBefore := 0
  let mut sizeAfter := 0
  let mut declsBefore := 0
  let mut declsAfter := 0
  for _ in [0:samples] do
    let prog ← ProgramGen.sample 6
    -- Every one-step candidate must be well-typed, and none may strand a
    -- `requires` clause (the one ill-formedness the typechecker does not catch —
    -- see `funcPreconditionsScoped`).
    let cands := shrinkProgram prog
    candidates := candidates + cands.length
    illTyped := illTyped + (cands.filter (!progTypeChecks ·)).length
    stranded := stranded + (cands.filter (fun c => c.decls.any fun
      | .func f _ => !funcPreconditionsScoped f
      | .recFuncBlock fs _ => fs.any (!funcPreconditionsScoped ·)
      | _ => false)).length
    let minimized := minimizeProgramCounterexample (fun p => sizeProgram p ≤ 3) 400 prog
    sizeBefore := sizeBefore + sizeProgram prog
    sizeAfter := sizeAfter + sizeProgram minimized
    declsBefore := declsBefore + prog.decls.length
    declsAfter := declsAfter + minimized.decls.length
  IO.println s!"    {samples} programs: size {sizeBefore} → {sizeAfter}, \
    decls {declsBefore} → {declsAfter}"
  IO.println s!"    {candidates} candidates emitted; {illTyped} ill-typed, \
    {stranded} with a stranded `requires` (both must be 0)"
  pure (candidates, illTyped, stranded)

-- ── ADT-derived-call coverage ─────────────────────────────────────────

/-- Sample programs and report how often a generated function/procedure/axiom
    body actually **calls** a derived function of an earlier datatype, broken down
    by family (constructor / tester / safe accessor / unsafe accessor).

    This is a *coverage statistic*, not a pass/fail property: the generator is free
    to draw a program whose bodies happen to call nothing. It is reported because
    the interesting failure mode for the ADT work is silent regression to zero —
    which no `True`-valued property would catch. Returns
    `(programs, withDatatype, withCall, ctors, testers, accessors, unsafeAccessors)`. -/
def derivedCallCoverage (samples maxSize : Nat) (coverageNumDecls : Nat := 10) :
    IO (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
  let mut drawn := 0
  let mut withDt := 0
  let mut withCall := 0
  let mut ctors := 0
  let mut testers := 0
  let mut accs := 0
  let mut uaccs := 0
  -- Deliberately *not* the size-scaled `Arbitrary GenProgram`: a derived call needs
  -- a datatype block AND a later function/procedure in the same program, so the
  -- property suite's small draws (`numDecls` ~3 at default sizes) essentially never
  -- exhibit one. Coverage is measured at a fixed, realistic declaration count.
  for i in [:samples] do
    let r ← (try
      let prog ← Plausible.Gen.run
        (retryGen 30000 (ProgramGen.genProgram (G := Plausible.Gen) coverageNumDecls {})
         : Gen Core.Program) (4 + i % (maxSize + 1))
      pure (some prog)
     catch _ => pure none)
    match r with
    | none => pure ()
    | some prog =>
      drawn := drawn + 1
      unless (datatypeBlocks prog).isEmpty do withDt := withDt + 1
      if mentionsDerivedFunction prog then
        withCall := withCall + 1
        let (c, t, a, u) := calledByFamily prog
        unless c.isEmpty do ctors := ctors + 1
        unless t.isEmpty do testers := testers + 1
        unless a.isEmpty do accs := accs + 1
        unless u.isEmpty do uaccs := uaccs + 1
  pure (drawn, withDt, withCall, ctors, testers, accs, uaccs)

/-- Print the `derivedCallCoverage` report. Never gates the exit code — it is a
    distribution, not an assertion. -/
def printDerivedCallCoverage (samples maxSize : Nat) : IO Unit := do
  let (drawn, withDt, withCall, ctors, testers, accs, uaccs) ←
    derivedCallCoverage samples maxSize
  IO.println s!"  programs drawn: {drawn}/{samples} (declaring >= 1 datatype: {withDt})"
  IO.println s!"  bodies calling an ADT-derived function: {withCall}"
  IO.println s!"    constructors {ctors} | testers {testers} \
| safe accessors {accs} | unsafe accessors {uaccs}"
  if withDt > 0 && withCall == 0 then
    IO.println "  NOTE: no derived calls in this run -- if persistent, this is the \
regression the ADT-derived-function work fixed."

-- ── Datatype-block generation via Plausible.Gen ───────────────────────
--
-- Two wrappers over the *same* generator, differing only in how a block is
-- assembled, because the properties they feed ask different questions:
--
--   * `GenAdtBlock` is one draw of `DatatypeGen.genMutuallyRecursiveDatatypes` —
--     an ordinary, usually connected block. It feeds `Properties.adtBlockChecks`
--     (the two pure companions to the SMT law properties, plus the
--     eliminator-scoping property, which is *not* specific to the independent
--     shape).
--   * `GenIndepBlock` concatenates independent one-datatype draws
--     (`MutualBlockShape.genIndependentBlock`), so no field can mention a sibling.
--     It feeds `Properties.mutualIndepChecks`.
--
-- Both are drawn at `maxSize := 0`. At a larger size `genArgTy` emits arrows, and
-- `validateDatatypesForSMT` refuses a function-typed field for the whole block, so
-- the arrow-free fraction falls from 40/40 to about 5/40 — three quarters of the
-- budget would go to blocks no solver ever sees. The larger sizes are exercised
-- where they are the point: `AdtLawsSmt.adtSolverAcceptsQueryAction` draws over a
-- size schedule, since it *wants* the refusals.

/-- A generated `mutual … end` block (ordinary shape). -/
structure GenAdtBlock where
  block : Lambda.MutualDatatype Unit

/-- A generated `mutual … end` block whose datatypes are pairwise independent. -/
structure GenIndepBlock where
  block : Lambda.MutualDatatype Unit

instance : Repr GenAdtBlock where
  reprPrec b _ := StrataGenerators.MutualBlockShape.renderBlock b.block

instance : Repr GenIndepBlock where
  reprPrec b _ := StrataGenerators.MutualBlockShape.renderBlock b.block

/-- Shrink a block by dropping one datatype. `MutualDatatype` is a plain `List`, so
    no proof obligation travels with the drop (each datatype carries its own
    `constrs_ne`); the empty list is excluded, since `validateMutualBlock` rejects
    an empty block. A candidate that drops below two datatypes makes the `mutual:`
    properties vacuously true, and Plausible discards a candidate that no longer
    fails — so the shrinker cannot report a one-datatype "counterexample". -/
private def shrinkBlock (block : Lambda.MutualDatatype Unit) :
    List (Lambda.MutualDatatype Unit) :=
  if block.length ≤ 1 then []
  else (List.range block.length).map (fun i => block.eraseIdx i)

instance : Shrinkable GenAdtBlock where
  shrink b := (shrinkBlock b.block).map (⟨·⟩)

instance : Shrinkable GenIndepBlock where
  shrink b := (shrinkBlock b.block).map (⟨·⟩)

instance : Arbitrary GenAdtBlock where
  arbitrary := do
    let block ← DatatypeGen.genMutuallyRecursiveDatatypes (G := Plausible.Gen)
      (maxSize := 0)
    pure ⟨block⟩

instance : Arbitrary GenIndepBlock where
  arbitrary := Gen.sized fun s => do
    -- Two to four datatypes: `mutual` is vacuous for one, and the properties need
    -- at least a pair to be about the *block* rather than about a datatype.
    let extra := min 2 (s / 30)
    let block ← StrataGenerators.MutualBlockShape.genIndependentBlock
      (G := Plausible.Gen) (extra + 1) (maxSize := 0)
    pure ⟨block⟩

-- ── Datatype-block coverage diagnostic ────────────────────────────────

/-- Report what the block-based suites actually drew: how many blocks held two or
    more datatypes, how many had uniform type parameters (the condition `elimFuncs`
    assumes), how many Strata's `addMutualBlock` accepted, how many passed the
    `blockIsSmtSafe` screen the `--smt` law properties apply, and how many
    independent draws really were independent.

    Printed as a diagnostic, never gating the exit code, for the reason the rest of
    this suite reports coverage: a green block property on blocks that are all
    single-datatype, or all rejected, is a property that tested nothing. -/
def datatypeBlockCoverage (samples : Nat) : IO (Nat × Nat × Nat × Nat × Nat) := do
  let mut multi := 0
  let mut uniform := 0
  let mut accepted := 0
  let mut smtSafe := 0
  let mut indep := 0
  for i in List.range samples do
    let block ← DatatypeGen.sample (maxSize := i % 3)
    if block.length ≥ 2 then multi := multi + 1
    if StrataGenerators.MutualBlockShape.blockParamsUniform block then
      uniform := uniform + 1
    if StrataGenerators.AdtLaws.blockAccepted block then accepted := accepted + 1
    if StrataGenerators.AdtLaws.blockIsSmtSafe block then smtSafe := smtSafe + 1
    let ind ← StrataGenerators.MutualBlockShape.genIndependentBlock (G := IO) 1
    if StrataGenerators.MutualBlockShape.isIndependentBlock ind then indep := indep + 1
  pure (multi, uniform, accepted, smtSafe, indep)

/-- Print the block coverage report. -/
def printDatatypeBlockCoverage (samples : Nat) : IO Unit := do
  let (multi, uniform, accepted, smtSafe, indep) ← datatypeBlockCoverage samples
  IO.println s!"  ordinary blocks drawn: {samples} \
(>= 2 datatypes: {multi} | uniform type params: {uniform})"
  IO.println s!"    accepted by addMutualBlock: {accepted} | \
SMT-safe (arrow-free, no bitvec 0, bare SMT symbols): {smtSafe}"
  IO.println s!"  independent blocks drawn: {samples} (actually independent: {indep})"
  if accepted < samples then
    IO.println s!"  NOTE: {samples - accepted} block(s) rejected by addMutualBlock -- \
DatatypeGen does not thread reserved names across the datatypes of one block, so two \
of them can declare a constructor of the same name (docs/adt-laws-alias-mutual-blocks.md)."

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

/-- Printer-expressiveness diagnostic: sample whole programs, and tally the
    *distinct* conversion-error messages `Core.formatProgram` logs, most frequent
    first. Also reports, of the programs that logged an error, how many still
    re-parse — those are the dangerous ones, where a placeholder produced a
    syntactically valid but **different** program, which the string round-trip
    property cannot detect.

    A **diagnostic**: it does not gate the exit code (the gating statement is
    `printer: no conversion error on generated programs`). Its job is
    localisation — naming the offending *constructs* across a whole sample, which
    the per-counterexample view cannot give. The whole-program shrinker does
    minimize the gating property's witness, but only when the draw typechecks: its
    candidate filter is `Program.typeCheck`, so on a gap-bearing draw (~60%) the
    witness is reported unshrunk and this tally is the only localisation available.

    Returns `(programsWithErrors, programsSampled, reparsedDespiteError)`. -/
def printerErrorDiagnostic (numTrials maxSize : Nat) : IO (Nat × Nat × Nat) := do
  let total := min numTrials 60
  let mut withErrors := 0
  let mut reparsed := 0
  let mut sampled := 0
  let mut tally : List (String × Nat) := []
  for i in List.range total do
    let size := i % (maxSize + 1)
    let gp ← try Gen.run (Arbitrary.arbitrary (α := GenProgram)) size
             catch _ => pure ⟨{ decls := [] }⟩
    -- A retry-exhausted draw yields the empty program; don't score it either way.
    if gp.prog.decls.isEmpty then continue
    sampled := sampled + 1
    let s := (Core.formatProgram gp.prog).pretty
    let lines := StrataGenerators.PrinterCoverage.strataErrorLines s
    if !lines.isEmpty then
      withErrors := withErrors + 1
      for line in lines.dedup do
        tally := match tally.find? (·.1 == line) with
          | some _ => tally.map (fun (m, c) => if m == line then (m, c + 1) else (m, c))
          | none => (line, 1) :: tally
      -- Did the text the printer *claims* to have produced still parse?
      match ← parseCoreProgram (StrataGenerators.PrinterCoverage.printedText s) with
      | some _ => reparsed := reparsed + 1
      | none => pure ()
  IO.println s!"    {withErrors}/{sampled} programs logged a conversion error"
  IO.println s!"    {reparsed} of those still re-parsed (placeholder ⇒ silently different program)"
  IO.println s!"    distinct messages ({tally.length}), most frequent first:"
  for (m, c) in (tally.mergeSort (fun a b => a.2 > b.2)) do
    IO.println s!"      [{c}×] {m}"
  -- Bitvector width divergence, reported alongside because several of the
  -- messages above are instances of it. Deterministic, so it is a scan rather
  -- than a sample: `Function.typeCheck` accepts every width, the printer supports
  -- five, and the five are *not* the powers of two.
  let divergent := StrataGenerators.PrinterCoverage.divergentBvWidths 64
  IO.println s!"    bitvec widths 0..63: {64 - divergent.length} printable, {divergent.length} typecheck-but-unprintable"
  IO.println s!"      printable: {StrataGenerators.PrinterCoverage.printableBvWidths}"
  IO.println s!"      first divergent: {divergent.take 12}{if divergent.length > 12 then " …" else ""}"
  return (withErrors, sampled, reparsed)

-- ── CLI ────────────────────────────────────────────────────────────────

/-- Parsed command-line configuration for the merged driver. -/
structure CliConfig where
  numTrials : Nat
  maxSize : Nat
  tycheEnabled : Bool
  tycheOut : String
  tycheSamples : Nat
  smtEnabled : Bool

/-- The number of trials that `--quick` selects. -/
def quickNumTrials : Nat := 100

/-- The maximum generator size that `--quick` selects. -/
def quickMaxSize : Nat := 40

/-- Parse `args` into a `CliConfig`. The positional arguments are
    `[numTrials] [maxSize]`. Each flag with the prefix `--` selects an option, and
    the pass for the Tyche visualization is on by default.

    `--quick` selects a fast preset for a short cycle of work: 100 trials, a
    maximum size of 40, and no Tyche pass. Use it to find a defect, and use the
    default settings to gate a merge. A measurement gives about 16 seconds for the
    preset, against about 7 minutes for the default settings.

    A positional argument has a higher precedence than `--quick`, so
    `--quick 500` gives 500 trials and keeps the other two parts of the preset.
    Therefore a user can make one part of the preset wider without the loss of the
    others. `--tyche-samples=N` also keeps its value, but it has no effect while
    `--quick` holds the Tyche pass off. To get the Tyche pass together with the
    other parts of the preset, give the trials and the size as positional
    arguments and do not use `--quick`. -/
def parseArgs (args : List String) : CliConfig :=
  let flags := args.filter (·.startsWith "--")
  let positional := args.filter (fun a => !a.startsWith "--")
  let flagValue (key : String) : Option String :=
    (flags.find? (·.startsWith key)).map (·.drop key.length |>.toString)
  let quick := flags.contains "--quick"
  { numTrials := (positional[0]? >>= String.toNat?).getD
                   (if quick then quickNumTrials else 1000)
    maxSize := (positional[1]? >>= String.toNat?).getD
                 (if quick then quickMaxSize else 100)
    tycheEnabled := !flags.contains "--no-tyche" && !quick
    tycheOut := (flagValue "--tyche-out=").getD "tyche_output.jsonl"
    tycheSamples := ((flagValue "--tyche-samples=").bind String.toNat?).getD 1000
    smtEnabled := flags.contains "--smt" }
