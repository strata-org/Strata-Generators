import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Properties of the `changed` flag of a pipeline phase

Four phases set `changed := true` without a test: `FilterProcedures`,
`RemoveIrrelevantAxioms`, `typeCheck` and `symbolicEval`. The `proc:` suite pins
`FilterProcedures` and `PrecondElim` one at a time. The properties here state the contract
*uniformly over a list of phases*, so they also cover a phase that someone adds later.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.PhaseChangedFlag

/-- The two witnesses for a phase that changes nothing. Each witness gives a phase and a
    program that the phase cannot change. The verdict is therefore a closed `Bool`, and a
    random sample would hide which case the witness covers. Together the two witnesses pin
    two of the four sites that set the flag without a test. -/
@[strata_properties]
def phaseNoOpWitnesses : List TestDecl :=
  [ ("phase: RemoveIrrelevantAxioms changed flag is faithful on a no-op",
     irrelevantAxiomsNoOp),
    ("phase: FilterProcedures changed flag is faithful on a no-op",
     filterNoOp) ].map fun (name, witness) =>
      (TestDecl.witness name witness.check).withEnumeratedPanel
        [({ witness } : PhaseNoOpResult)]

/-- The uniform sweep over each phase of `corePipelinePhases` and over
    `RemoveIrrelevantAxioms`. The property finds a *new* phase that sets the flag without a
    test. Its panel names the phases whose flag was wrong on each sample, so a new label in
    the panel is the signal. -/
@[strata_property]
def phaseAllChangedFlag : TestDecl :=
  let name := "phase: every pipeline phase has a faithful changed flag"
  (TestDecl.property name
    (fun (gp : GenProcs) => checkAllPhasesChangedFlag gp.procs)).withPanel
    (genPhaseSweepProp name (checkAllPhasesChangedFlag ·) allCorePhases)

/-- Each phase *except* the four known sites that set `changed := true` without a test. The
    property guards the phases that really compute the flag. -/
@[strata_property]
def phaseHonestChangedFlag : TestDecl :=
  let name := "phase: non-hardcoded pipeline phases have a faithful changed flag"
  (TestDecl.property name
    (fun (gp : GenProcs) => checkHonestPhasesChangedFlag gp.procs)).withPanel
    (genPhaseSweepProp name (checkHonestPhasesChangedFlag ·) honestPhases)
