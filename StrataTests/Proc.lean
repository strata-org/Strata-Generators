import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Properties that relate the procedure generator to a transform pass

There is one property for each *named field* of the three `*PhaseCorrect` structures. This
includes the `ChangedFlagValid` field and the `PreservesCachedAnalysesWF` field, which all
three structures share. The coverage of those specifications is therefore complete. The
module documentation of `ProcedureHasTypeAGen/TestSupport` gives the analysis, and it says
which properties run on the program shape that mixes declarations.

`genProcedure` is sound *and* complete against the declarative typing specification. The
generated procedures also form an acyclic call graph, because the generator draws body `i`
against the signatures of the siblings `P0` to `P{i-1}`. Therefore the properties for the
closure of the callees and for the call graph are not vacuous.

Two properties state a faithful contract between the `changed` flag and a real change to the
program, and the passes break the contract in two places. `FilterProcedures` sets
`changed := true` even when it removes nothing. The `.funcDecl` branch of `PrecondElim`
reports no change while it inserts a `$$wf` block.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Procedure.TestSupport

/-- The twenty-eight properties for the procedures and the transform passes: seven for
    `FilterProcedures`, thirteen for `PrecondElim` and eight for `ANFEncoder`. -/
@[strata_properties]
def procTransforms : List TestDecl :=
  family GenProcs
    [ -- FilterProcedures: `FilterProcedurePhaseCorrect`
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
      -- PrecondElim: `PrecondElimPhaseCorrect`
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
      -- ANFEncoder: `ANFEncoderPhaseCorrect`
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

/-- `PrecondElim` removes the precondition from each entry of the output factory.

    This property is separate from the family, because its panel needs a diagnostic view and
    not the plain program. Its smallest witness is the *empty* program, and the cause is not
    in the text of the program: an entry of the output factory still holds a precondition.
    Therefore this is the one property that names its `PropertyRunner`, so that the printer
    also uses `procFactoryStrippedDiagnostic`. -/
@[strata_property]
def procPrecondFactoryStripped : TestDecl :=
  .forAll "proc: PrecondElim factory entries are stripped"
    (Generators.procs.withRender fun gp =>
      procsRepr gp.procs ++ "\n\n" ++ procFactoryStrippedDiagnostic gp.procs)
    (fun gp => checkPrecondFactoryStripped gp.procs)
