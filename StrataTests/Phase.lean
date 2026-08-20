import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Pipeline-phase `changed`-flag properties

Four phases hardcode `changed := true` (`FilterProcedures`,
`RemoveIrrelevantAxioms`, `typeCheck`, `symbolicEval`). The `proc:` suite pins
`FilterProcedures` and `PrecondElim` individually; these state the contract
*uniformly over a phase list*, so a phase added later is covered without a new
property being written.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.PhaseChangedFlag

/-- The two no-op witnesses: a phase paired with a program it provably cannot
    change, so the verdict is a closed `Bool` and sampling would only obscure which
    case is at stake. Between them they pin two of the four hardcoded sites. -/
@[strata_properties]
def phaseNoOpWitnesses : List TestDecl :=
  [ ("phase: RemoveIrrelevantAxioms changed flag is faithful on a no-op",
     irrelevantAxiomsNoOp),
    ("phase: FilterProcedures changed flag is faithful on a no-op",
     filterNoOp) ].map fun (name, witness) =>
      (TestDecl.witness name "phase" witness.check).withEnumeratedPanel
        [({ witness } : PhaseNoOpResult)]

/-- The uniform sweep over every phase of `corePipelinePhases` plus
    `RemoveIrrelevantAxioms`. This is the regression gate that catches a *newly
    added* hardcoding phase; its panel names which phases lied on each sample, so a
    new label appearing there is the signal. -/
@[strata_property]
def phaseAllChangedFlag : TestDecl :=
  let name := "phase: every pipeline phase has a faithful changed flag"
  (TestDecl.forAll name "phase"
    (fun (gp : GenProcs) => checkAllPhasesChangedFlag gp.procs)).withPanel
    (genPhaseSweepProp name (checkAllPhasesChangedFlag ·) allCorePhases)

/-- Every phase *except* the four known hardcoded-`true` sites: this is what guards
    the honestly-computing phases against regression. -/
@[strata_property]
def phaseHonestChangedFlag : TestDecl :=
  let name := "phase: non-hardcoded pipeline phases have a faithful changed flag"
  (TestDecl.forAll name "phase"
    (fun (gp : GenProcs) => checkHonestPhasesChangedFlag gp.procs)).withPanel
    (genPhaseSweepProp name (checkHonestPhasesChangedFlag ·) honestPhases)
