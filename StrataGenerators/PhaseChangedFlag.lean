import StrataGenerators.ProcedureHasTypeAGen.TestSupport
-- This import supplies `countLoopsStmts`. The module uses it to skip `symbolicEval` on a
-- program that holds a `loop`, because the evaluator answers a `.loop` with a `panic!`. See
-- `programHasLoop`.
import StrataGenerators.StmtHasTypeAGen.TestSupport
import Strata.Transform.IrrelevantAxioms
import Strata.Languages.Core.Verifier

/-!
# The `changed` flag of *each* `PipelinePhase`

`Core.PipelinePhase.transform` returns a `Bool` and a `Program`. The specification
`ChangedFlagValid` says that the `Bool` means "this phase changed the program", which is
`changed = true ↔ progOut ≠ progIn`.

Four phases return the literal `true`, and they do so whether or not they changed anything.
The property `proc: FilterProcedures changed flag is faithful` already pins
`FilterProcedures`. This module covers the other three phases. More importantly, it states
the contract **uniformly over a list of phases**, so it also covers a phase that someone
adds later and no one must write a new property.

| Phase | Flag |
|---|---|
| `FilterProcedures` | `return (true, filtered)` |
| `RemoveIrrelevantAxioms` | `return (true, pruned)` |
| `typeCheck` | `return (true, prog')` |
| `symbolicEval` | `return (true, prog')` |

Each *other* phase computes the flag correctly, and this is what makes these four phases
look like an oversight and not a different convention. `CSE.runCSE` uses
`changed || idx' > idx`. `loopElim`, `insertLoopInvariantAsserts`, `CallElim` and
`ProcedureInlining` thread the flag through `runProgramUntil`, which collects `anyChanged`.
`PrecondElim` and `TermCheck` each compute their own flag.

## How serious the defect is

No consumer reads the flag. Both call sites discard it, and one of them is
`let (_, next) ← pp.transform prog`. Nothing therefore behaves wrongly at run time. The
defect is that the specification of the field gives it a meaning that it does not have, and
the first consumer that trusts the field gets wrong answers with no message. These
properties are a net around the future fix, and not a report of a live failure.

## Why a witness, and not generated input

A generated program is a *weak* witness here. To show that the flag is wrong, a run must
give the phase nothing to do, and most generated programs give each phase something to do.
The sharp witnesses are therefore ones that the module builds:

- `RemoveIrrelevantAxioms` on a program with **no axiom**. It can remove nothing, so
  `changed` must be `false`.
- `FilterProcedures` with **each** procedure in the target set. It can remove nothing. The
  `proc:` property already uses this scenario, and the module states it again so that the
  uniform sweep is complete on its own.

The direction with generated input is also useful, and `checkAllPhasesChangedFlag` gives
it. That property runs the sweep over programs that generated procedures build, and it
therefore finds a *new* phase that sets its flag without a test, on input that no one can
predict.
-/

namespace StrataGenerators.PhaseChangedFlag

open Lambda Core
open StrataGenerators.Procedure.TestSupport

-- ── The phases under test ─────────────────────────────────────────────────

/-- A pipeline phase and a label for a report. `PipelinePhase.phase.name` already holds the
    name of a phase. This structure exists to give a stable label to the two phases of the
    verifier, because a local `let` inside `corePipelinePhases` binds those two phases and no
    name addresses them. -/
structure NamedPhase where
  label : String
  phase : Core.PipelinePhase

/-- The options that the module uses to build the pipeline. `.quiet` matters, because
    `typeCheck` and `symbolicEval` trace their progress at a verbosity of `.normal` and above.
    Such a trace would put a line about a successful type check, and a dump of the
    verification conditions, into the output of the harness on each trial. -/
def phaseOptions : Core.VerifyOptions := Core.VerifyOptions.quiet

/-- A list of target procedures. A value for `procs` is what makes `corePipelinePhases` hold
    the two `FilterProcedures` phases. With `procs := none`, those two phases are absent and
    the sweep misses the one site that a report already names. `"P0"` is the first procedure
    name that `relabelProcs` gives, so on generated input this is a real target and not a name
    that filters each procedure away. -/
def phaseTargets : List String := ["P0"]

/-- The phase of `corePipelinePhases` whose name is `name`, or `none`.

    `typeCheck` and `symbolicEval` are not top-level definitions. A `let` inside
    `Core.corePipelinePhases` binds them. This function finds them in `corePipelinePhases` by
    their `phase.name`, and it does not copy their bodies. A copy would test the code of this
    package and not the code of Strata. If Strata renames or removes a phase, this function
    returns `none` and the suite skips the property, and it does not test another phase. -/
def verifierPhase (name : String) : Option Core.PipelinePhase :=
  (Core.corePipelinePhases (procs := some phaseTargets) (options := phaseOptions)).find?
    (fun ph => ph.phase.name == name)

/-- The phases that set `changed := true` without a test, as far as a name addresses them.
    `FilterProcedures` needs a list of targets, and each check gives that list from the program
    under test. -/
def hardcodedPhases : List NamedPhase :=
  [ ⟨"RemoveIrrelevantAxioms", Core.irrelevantAxiomsPipelinePhase []⟩ ]
  ++ (match verifierPhase "typeCheck" with
      | some ph => [⟨"typeCheck", ph⟩] | none => [])
  ++ (match verifierPhase "symbolicEval" with
      | some ph => [⟨"symbolicEval", ph⟩] | none => [])

/-- Each phase of the standard Core pipeline, for the uniform sweep. This list is what keeps
    the property correct in the future: the sweep covers a phase that someone adds to
    `corePipelinePhases`, and no one edits this file.

    The list also holds `RemoveIrrelevantAxioms`, which is *not* a part of
    `corePipelinePhases`. Strata offers it as `Core.passRemoveIrrelevantAxioms` for a caller to
    add, so a sweep over the standard pipeline alone misses it.

    `FilterProcedures` occurs **two times** in `corePipelinePhases`: one time before
    `PrecondElim`, and one time after it with `respectNoFilter := false`. The sweep therefore
    tests both configurations. Two labels can therefore be equal, and `violators` removes a
    duplicate for the report. -/
def allCorePhases : List NamedPhase :=
  (Core.corePipelinePhases (procs := some phaseTargets) (options := phaseOptions)).map
    (fun ph => ⟨ph.phase.name, ph⟩)
  ++ [⟨"RemoveIrrelevantAxioms", Core.irrelevantAxiomsPipelinePhase phaseTargets⟩]

-- ── The contract ──────────────────────────────────────────────────────────

/-- What one phase did to one program. The result holds the `changed` flag that the phase
    *reported*, and whether the program *really* changed. The second value comes from full
    structural equality of two `Program` values. The result is `none` when the phase gave a
    diagnostic.

    The verdict in `changedFlagValid` and the report in `outcomeDescription` both read this one
    function, and so do the features of the Tyche panels. A panel can therefore never show a
    flag other than the flag that gave its verdict. -/
def phaseOutcome (ph : Core.PipelinePhase) (prog : Program) : Option (Bool × Bool) :=
  (runPhase ph prog).map (fun (changed, out) => (changed, !decide (out = prog)))

/-- `ChangedFlagValid` for one phase on one program: `changed = true ↔ progOut ≠ progIn`, on
    full structural equality of two `Program` values.

    A phase that gives a diagnostic is *skipped*, and the result is `true` and not a failure.
    Several phases reject an input correctly: `typeCheck` rejects an ill-typed program, and
    `symbolicEval` rejects a program that it cannot evaluate. A diagnostic is not a wrong
    `changed` flag. `Procedure.TestSupport.checkChangedFlagValid` uses the same convention. -/
def changedFlagValid (ph : Core.PipelinePhase) (prog : Program) : Bool :=
  match phaseOutcome ph prog with
  | some (reported, actuallyChanged) => reported == actuallyChanged
  | none => true

/-- Whether a procedure in `prog` holds a `loop` statement, at any depth.

    **This is a precondition of `symbolicEval`, and not a filter for style.**
    `Core.Statement.evalOneStmt` answers a `.loop` with a `panic!`, and the message of that
    panic says that the caller must transform the program to remove each loop first. The real
    pipeline meets this precondition, because it runs `loopElimPipelinePhase` first. A sweep
    that applies each phase *on its own* to raw generated input does not meet it. A run of
    `symbolicEval` on a program that holds a loop then prints a panic of Lean and a backtrace
    into the output of the harness.

    The panic is recoverable, because `panic!` returns the `Inhabited` default value and it does
    not stop the run. The verdict is therefore correct. However, a backtrace among the results
    looks like a crash, and it also makes the output of the suite change between runs. -/
def programHasLoop (prog : Program) : Bool :=
  prog.decls.any fun
    | .proc p _ => StrataGenerators.Stmt.TestSupport.countLoopsStmts (bodyStmts p.body) > 0
    | _ => false

/-- The phases whose input must hold no loop. Only `symbolicEval` evaluates a statement. Each
    other phase is a syntactic transform from a program to a program. -/
def requiresLoopFree : List String := ["symbolicEval"]

/-- `changedFlagValid`, but it skips a phase whose precondition the input breaks. A skip is not
    a failure, and `changedFlagValid` uses the same convention for a phase that gives a
    diagnostic: a precondition that does not hold is not a wrong `changed` flag. -/
def changedFlagValidGuarded (np : NamedPhase) (prog : Program) : Bool :=
  if requiresLoopFree.contains np.label && programHasLoop prog then true
  else changedFlagValid np.phase prog

/-- The labels of the phases in `phases` whose flag is wrong on `prog`. The list holds no
    duplicate, because `FilterProcedures` occurs two times in the pipeline. The properties and
    the diagnostic that names the phases both use this list. -/
def violators (phases : List NamedPhase) (prog : Program) : List String :=
  (phases.filterMap fun np =>
    if changedFlagValidGuarded np prog then none else some np.label).dedup

-- ── The report ────────────────────────────────────────────────────────────
-- A sweep that fails says only *that* the flag of some phase is wrong. The functions below say
-- *which* phase and *how*, for the Tyche panels and for a reader who debugs a run.

/-- What `np` did to `prog`, in one line. The line holds the flag that the phase reported and
    whether the program really changed, or it holds the reason for a skip. The function reads
    `phaseOutcome`, so it reports exactly what `changedFlagValidGuarded` scored. -/
def outcomeDescription (np : NamedPhase) (prog : Program) : String :=
  if requiresLoopFree.contains np.label && programHasLoop prog then
    "skipped — the input has a loop, which this phase's evaluator cannot answer"
  else match phaseOutcome np.phase prog with
    | none => "skipped — the phase raised a diagnostic"
    | some (reported, actuallyChanged) =>
      s!"reported changed = {reported}, program {if actuallyChanged then "differs" else "unchanged"}"

/-- The phases of the sweep whose flag is wrong on `prog`, one line for each phase. Each line
    names the phase and what it reported. This report locates a failure of the sweep: the
    property says that a flag is wrong somewhere, and this report says where and how.

    The description of a label comes from the *first* phase that carries it, because `violators`
    removes a duplicate and `FilterProcedures` occurs two times in `corePipelinePhases`. -/
def phaseChangedFlagDiagnostic (phases : List NamedPhase) (prog : Program) : String :=
  let bad := violators phases prog
  if bad.isEmpty then
    s!"-- changed flag: faithful on every one of the {phases.length} swept phases"
  else
    String.intercalate "\n"
      (s!"-- changed-flag violators: {bad.length} of {phases.length} swept phases"
        :: bad.map fun label =>
             match phases.find? (fun np => np.label == label) with
             | some np => s!"  {label}: {outcomeDescription np prog}"
             | none => s!"  {label}")

-- ── The witnesses that the module builds ──────────────────────────────────

/-- The smallest procedure. Its structured body is empty. -/
def mkProc (n : String) : Procedure :=
  { header := { name := ⟨n, ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] }

/-- A program with one procedure and **no axiom declaration**. `RemoveIrrelevantAxioms` can
    therefore remove nothing, and a `changed = true` for this program is wrong for each meaning
    of the word "irrelevant". -/
def axiomFreeProgram : Program :=
  { decls := [Decl.proc (mkProc "A") .empty] }

/-- One witness that the module builds: a phase and a program that the phase cannot change. A
    correct flag must therefore be `false`.

    The structure holds the phase *and* its program, and each check is not a closed `Bool` on
    its own. A Tyche panel can therefore show the program that gave the verdict. `check` below
    is the verdict, and no other function computes it again. -/
structure NoOpWitness where
  /-- The name of the phase, for a report. -/
  label : String
  phase : Core.PipelinePhase
  /-- The program that `phase` cannot change. -/
  prog : Program

/-- `ChangedFlagValid` on the witness. The result is `false` exactly when the phase claims that
    it changed a program that it cannot change. -/
def NoOpWitness.check (w : NoOpWitness) : Bool := changedFlagValid w.phase w.prog

/-- The phase of the witness as a `NamedPhase`, so that the report functions above also apply to
    a witness. -/
def NoOpWitness.named (w : NoOpWitness) : NamedPhase := ⟨w.label, w.phase⟩

/-- `RemoveIrrelevantAxioms` on a program with no axiom. It has nothing to remove, for each
    meaning of the word "irrelevant". -/
def irrelevantAxiomsNoOp : NoOpWitness :=
  ⟨"RemoveIrrelevantAxioms", Core.irrelevantAxiomsPipelinePhase [], axiomFreeProgram⟩

/-- `FilterProcedures` with each procedure of the program in the target set. It can remove
    nothing. -/
def filterNoOp : NoOpWitness :=
  ⟨"FilterProcedures",
   Core.filterProceduresPipelinePhase (programProcNames axiomFreeProgram) true,
   axiomFreeProgram⟩

/-- Pins the defect in `RemoveIrrelevantAxioms`. On a program with no axiom, the phase changes
    nothing, so its flag must be `false`. The phase returns `(true, pruned)` for each input. -/
def checkIrrelevantAxiomsNoOpFlag : Bool := irrelevantAxiomsNoOp.check

/-- Pins the defect in `FilterProcedures`. With each procedure in the target set, the phase can
    remove nothing, so its flag must be `false`. This check states the `proc:` property again on
    a witness that the module builds, so the uniform sweep is complete on its own. -/
def checkFilterNoOpFlag : Bool := filterNoOp.check

-- ── The uniform sweep over generated input ────────────────────────────────

/-- **`ChangedFlagValid` holds uniformly over each phase of the Core pipeline**, on a program
    that generated procedures build.

    This property is the net around the future fix. It does not list the four known phases, and
    it quantifies over `corePipelinePhases`. It therefore finds a phase that someone adds later
    and that sets its flag without a test, and no one writes a new property.

    `typeCheck` and `symbolicEval` are in the list, and both set the flag to `true` without a
    test. `phaseChangedFlagDiagnostic` shows which phases cause a failure on a given program.
    That report is useful only when the set of such phases is exactly the known set. -/
def checkAllPhasesChangedFlag (ps : List Procedure) : Bool :=
  (violators allCorePhases (mkProgram ps)).isEmpty

/-- The phases with a *known* defect in the `changed` flag. The second half of the sweep below
    does not cover them.

    The first four phases set the flag to `true` without a test, as the documentation of this
    module says. `PrecondElim` is different, and a reader must not group it with the four. It
    *computes* its flag, but it computes the flag wrongly in one branch. The `.funcDecl` case of
    `transformStmt` inserts a `{name}$$wf` block for the obligations that it finds in the
    **body** of a declared function, and it returns a flag that comes only from
    `!decl.preconditions.isEmpty`. It therefore reports `changed = false` after it rewrote the
    program. This is a false *negative*, and the other four phases give a false positive.

    The property `proc: PrecondElim changed flag is faithful` pins that defect. A draw finds the
    defect rarely, because it needs a declared function that has no precondition of its own and
    whose body calls a partial function, such as `Int.SafeDiv`. This is the reason why the list
    below names the phase, and does not leave it to chance. -/
def knownDefectivePhases : List String :=
  [ -- These four phases set the flag to `true` without a test, which gives a false positive.
    "FilterProcedures", "RemoveIrrelevantAxioms", "typeCheck", "symbolicEval",
    -- This phase computes the flag, but it misses the `$$wf` insertion in the `.funcDecl` case,
    -- which gives a false negative.
    "PrecondElim" ]

/-- The phases that the second half of the sweep covers: each phase of the pipeline, without the
    phases that have a known defect. This list has a name, so that a report can sweep *exactly*
    the list that the property scores, and not a copy of that list. -/
def honestPhases : List NamedPhase :=
  allCorePhases.filter (fun np => !knownDefectivePhases.contains np.label)

/-- The second half of the sweep: each phase *except* the phases with a known defect must have a
    correct flag. This property guards the phases that really compute the flag, which are
    `CallElim`, `TermCheck`, `InsertLoopInvariantAsserts`, `LoopElim` and `CommonSubexprElim`.

    The two halves are separate properties. A new defect among these phases therefore appears as
    a separate property, and not as a change in the detail of another property. This works only
    when the scope of this property is deterministic, and `knownDefectivePhases` above gives that
    scope. -/
def checkHonestPhasesChangedFlag (ps : List Procedure) : Bool :=
  (violators honestPhases (mkProgram ps)).isEmpty

end StrataGenerators.PhaseChangedFlag
