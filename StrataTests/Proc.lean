import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Procedure-generator ↔ transform-pass properties

One property per *named field* of the three `*PhaseCorrect` structures in
`Strata/Transform/CustomSpecifications.lean` — including the `ChangedFlagValid` and
`PreservesCachedAnalysesWF` fields shared by all three — so coverage of those specs
is complete rather than partial. See the module doc of
`ProcedureHasTypeAGen/TestSupport` for the analysis and for which properties run on
the mixed-declaration program shape.

`genProcedure` is proven sound *and* complete against the declarative typing spec,
and the generated procedures form an acyclic call DAG (body `i` drawn against the
signatures of siblings `P0…P{i-1}`), so the callee-closure and call-graph dimensions
of the FilterProcedures / PrecondElim properties are not vacuous.

Two state a faithful `changed ↔ program changed` contract that the pass violates:
`FilterProcedures changed flag is faithful` (the pass hardcodes `changed := true`
even when it removes nothing) and `PrecondElim changed flag is faithful` (the
`.funcDecl` branch reports unchanged while inserting a `$$wf` block).
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Procedure.TestSupport

/-- The twenty-eight procedure/transform properties: seven FilterProcedures,
    thirteen PrecondElim, eight ANFEncoder. -/
@[strata_properties]
def procTransforms : List TestDecl :=
  family GenProcs
    [ -- FilterProcedures — `FilterProcedurePhaseCorrect`
      ("proc: FilterProcedures output decls are a sublist",
       fun gp => checkFilterDeclsSublist gp.procs),
      ("proc: FilterProcedures retains targets",
       fun gp => checkFilterTargetsRetained gp.procs),
      ("proc: FilterProcedures retains callee closures",
       fun gp => checkFilterCalleeClosureRetained gp.procs),
      ("proc: FilterProcedures removes only procedures",
       fun gp => checkFilterOnlyProcsRemoved gp.procs),
      ("proc: FilterProcedures removes unreachable procs",
       fun gp => checkFilterUnreachableRemoved gp.procs),
      ("proc: FilterProcedures changed flag is faithful",
       fun gp => checkFilterChangedFlagValid gp.procs),
      ("proc: FilterProcedures preserves call-graph WF",
       fun gp => checkFilterAnalysisPreserving gp.procs),
      -- PrecondElim — `PrecondElimPhaseCorrect`
      ("proc: PrecondElim $wf procs are well-formed",
       fun gp => checkPrecondGeneratedWF gp.procs),
      ("proc: PrecondElim strips all preconditions",
       fun gp => checkPrecondPreconditionsStripped gp.procs),
      ("proc: PrecondElim preserves type/ax/distinct decls",
       fun gp => checkPrecondNonProcDeclsPreserved gp.procs),
      ("proc: PrecondElim preserves procedures (name+spec)",
       fun gp => checkPrecondProceduresPreserved gp.procs),
      ("proc: PrecondElim preserves functions (name+body+sig)",
       fun gp => checkPrecondFunctionsPreserved gp.procs),
      ("proc: PrecondElim removes no declarations",
       fun gp => checkPrecondNoDeclsRemoved gp.procs),
      ("proc: PrecondElim preserves declaration order",
       fun gp => checkPrecondOrderPreserved gp.procs),
      ("proc: PrecondElim changed flag is faithful",
       fun gp => checkPrecondChangedFlagValid gp.procs),
      ("proc: PrecondElim asserts every partial call",
       fun gp => checkPrecondCallSiteAsserts gp.procs),
      ("proc: PrecondElim factory only grows",
       fun gp => checkPrecondFactoryGrows gp.procs),
      ("proc: PrecondElim factory has every declared function",
       fun gp => checkPrecondFactoryComplete gp.procs),
      ("proc: PrecondElim factory strips declared functions",
       fun gp => checkPrecondDeclaredFactoryStripped gp.procs),
      ("proc: PrecondElim preserves call-graph WF",
       fun gp => checkPrecondAnalysisPreserving gp.procs),
      -- ANFEncoder — `ANFEncoderPhaseCorrect`
      ("proc: ANFEncoder preserves declaration count",
       fun gp => checkAnfDeclsLength gp.procs),
      ("proc: ANFEncoder leaves non-procedures unchanged",
       fun gp => checkAnfNonProcsUnchanged gp.procs),
      ("proc: ANFEncoder preserves procedure headers+specs",
       fun gp => checkAnfHeadersPreserved gp.procs),
      ("proc: ANFEncoder fresh vars are deterministic",
       fun gp => checkAnfFreshVarsDet gp.procs),
      ("proc: ANFEncoder preserves declaration order",
       fun gp => checkAnfOrderPreserved gp.procs),
      ("proc: ANFEncoder does not change control flow",
       fun gp => checkAnfControlFlowPreserved gp.procs),
      ("proc: ANFEncoder changed flag is faithful",
       fun gp => checkAnfChangedFlagValid gp.procs),
      ("proc: ANFEncoder preserves call-graph WF",
       fun gp => checkAnfAnalysisPreserving gp.procs) ]

/-- `PrecondElim factory entries are stripped` is separated out because its panel
    needs a diagnostic view rather than the plain program: its minimized witness is
    the *empty* program, and the cause — output-factory entries that still carry a
    precondition — is not in the program text at all. So this is the one property that
    names its `PropertyRunner` explicitly, to extend the printer with
    `procFactoryStrippedDiagnostic`. -/
@[strata_property]
def procPrecondFactoryStripped : TestDecl :=
  .forAll "proc: PrecondElim factory entries are stripped"
    (Generators.procs.withRender fun gp =>
      procsRepr gp.procs ++ "\n\n" ++ procFactoryStrippedDiagnostic gp.procs)
    (fun gp => checkPrecondFactoryStripped gp.procs)
