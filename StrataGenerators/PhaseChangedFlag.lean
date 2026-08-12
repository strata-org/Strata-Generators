import StrataGenerators.ProcedureHasTypeAGen.TestSupport
-- Supplies `countLoopsStmts`, used to skip `symbolicEval` on programs containing a
-- `loop` (its evaluator answers `.loop` with `panic!`; see `programHasLoop`).
import StrataGenerators.StmtHasTypeAGen.TestSupport
import Strata.Transform.IrrelevantAxioms
import Strata.Languages.Core.Verifier

/-!
# `changed`-flag faithfulness across *every* `PipelinePhase`

`Core.PipelinePhase.transform` returns `Bool × Program`. The `Bool` is specified
by `ChangedFlagValid` (`Strata/Transform/CustomSpecifications.lean:97`) to mean
"this phase changed the program", i.e. `changed = true ↔ progOut ≠ progIn`.

Four phases return it as the literal `true` regardless of whether they changed
anything. `FilterProcedures` was already pinned by
`proc: FilterProcedures changed flag is faithful` in
`ProcedureHasTypeAGen/TestSupport.lean`; this module covers the other three and,
more importantly, states the contract **uniformly over a phase list** so that a
phase added later is covered without anyone writing a new property.

| Phase | Site | Flag |
|---|---|---|
| `FilterProcedures` | `FilterProcedures.lean:82` | `return (true, filtered)` |
| `RemoveIrrelevantAxioms` | `IrrelevantAxioms.lean:81` | `return (true, pruned)` |
| `typeCheck` | `Verifier.lean:1510` | `return (true, prog')` |
| `symbolicEval` | `Verifier.lean:1517` | `return (true, prog')` |

Every *other* phase computes the flag honestly, which is what makes these four
read as oversights rather than a different convention: `CSE.runCSE` uses
`changed || idx' > idx`; `loopElim`, `insertLoopInvariantAsserts`, `CallElim` and
`ProcedureInlining` thread it through `runProgramUntil`, which accumulates
`anyChanged`; `PrecondElim` and `TermCheck` compute theirs.

## Severity, stated honestly

No consumer reads the flag today. Both call sites discard it —
`PipelinePhase.lean:101` (`let (_, next) ← pp.transform prog`) and
`CoreToGOTOPipeline.lean:583`. So nothing misbehaves at runtime; the defect is
that the field is *specified* to mean something it does not mean, and the first
consumer to trust it gets wrong answers silently. These properties are a
regression gate on the eventual fix, not a report of live breakage.

## Why a no-op witness rather than generated input

A generated program is a *weak* witness here: to show the flag is unfaithful you
need a run on which the phase does nothing, and most generated programs give the
phases something to do. So the sharp witnesses are constructed:

- `RemoveIrrelevantAxioms` on a program with **no axioms at all** — it cannot
  possibly prune anything, so `changed` must be `false`.
- `FilterProcedures` with the target set covering **every** procedure — nothing
  can be removed. (This is the scenario the existing `proc:` property already
  uses; it is restated here so the uniform sweep is self-contained.)

The generated-input direction is still worth having, and `phaseChangedFlagFaithful`
supplies it: it runs the sweep over programs assembled from generated procedures,
which is what would catch a *newly added* phase that hardcodes its flag on inputs
we cannot predict.
-/

namespace StrataGenerators.PhaseChangedFlag

open Lambda Core
open StrataGenerators.Procedure.TestSupport

-- ── The phases under test ─────────────────────────────────────────────────

/-- A pipeline phase paired with a display name. `PipelinePhase.phase.name` is
    already the phase's own name, so this exists only to give the two
    `Verifier.lean` phases — which are `let`-bound locally inside
    `corePipelinePhases` and so not separately addressable — a stable label. -/
structure NamedPhase where
  label : String
  phase : Core.PipelinePhase

/-- The options used to build the pipeline. `.quiet` matters: `typeCheck` and
    `symbolicEval` `dbg_trace` their progress at `verbose ≥ .normal`
    (`Verifier.lean:660`, `:833`), which would interleave "[Strata.Core] Type
    checking succeeded." and a VC dump into the harness output on every trial. -/
def phaseOptions : Core.VerifyOptions := Core.VerifyOptions.quiet

/-- A representative target list. Supplying `procs` is what makes
    `corePipelinePhases` include the two `FilterProcedures` phases at all
    (`Verifier.lean:1487–1493`); with `procs := none` they are absent and the
    sweep would silently omit the one site that is already known-and-reported.
    `"P0"` is the first procedure name `relabelProcs` assigns, so on generated
    input this is a real target rather than a name that filters everything. -/
def phaseTargets : List String := ["P0"]

/-- `typeCheck` and `symbolicEval` are not exported as top-level definitions:
    they are `let`-bound inside `Core.corePipelinePhases` (`Verifier.lean:1507`,
    `:1512`). Rather than duplicate their bodies — which would test our copy
    instead of Strata's — we recover them positionally from
    `corePipelinePhases`, keying on `phase.name`. If Strata renames or drops a
    phase this returns `none` and the corresponding property is skipped rather
    than silently testing the wrong phase. -/
def verifierPhase (name : String) : Option Core.PipelinePhase :=
  (Core.corePipelinePhases (procs := some phaseTargets) (options := phaseOptions)).find?
    (fun ph => ph.phase.name == name)

/-- The four phases that hardcode `changed := true`, as far as they are
    addressable. `FilterProcedures` needs a target list, so it is supplied by
    each check from the program under test. -/
def hardcodedPhases : List NamedPhase :=
  [ ⟨"RemoveIrrelevantAxioms", Core.irrelevantAxiomsPipelinePhase []⟩ ]
  ++ (match verifierPhase "typeCheck" with
      | some ph => [⟨"typeCheck", ph⟩] | none => [])
  ++ (match verifierPhase "symbolicEval" with
      | some ph => [⟨"symbolicEval", ph⟩] | none => [])

/-- Every phase of the standard Core pipeline, for the uniform sweep. This is the
    list that makes the property future-proof: a phase added to
    `corePipelinePhases` is swept without editing this file.

    `RemoveIrrelevantAxioms` is appended because it is *not* part of
    `corePipelinePhases` — it is offered as `Core.passRemoveIrrelevantAxioms`
    (`Core.lean:174`) for a caller to compose in — so a sweep of the standard
    pipeline alone would miss it.

    Note `FilterProcedures` appears **twice** in `corePipelinePhases` (once
    pre- and once post-`PrecondElim`, the latter with `respectNoFilter := false`),
    so the sweep tests both configurations. Labels are therefore not unique;
    `violators` deduplicates for reporting. -/
def allCorePhases : List NamedPhase :=
  (Core.corePipelinePhases (procs := some phaseTargets) (options := phaseOptions)).map
    (fun ph => ⟨ph.phase.name, ph⟩)
  ++ [⟨"RemoveIrrelevantAxioms", Core.irrelevantAxiomsPipelinePhase phaseTargets⟩]

-- ── The contract ──────────────────────────────────────────────────────────

/-- What one phase did to one program: the `changed` flag it *reported*, paired
    with whether the program *actually* changed (full structural equality of
    `Program`). `none` when the phase raised a diagnostic.

    Both the verdict (`changedFlagValid`) and the reporting (`outcomeDescription`,
    and the Tyche panels' features) read this one function, so a panel can never
    display a flag other than the one its verdict was computed from. -/
def phaseOutcome (ph : Core.PipelinePhase) (prog : Program) : Option (Bool × Bool) :=
  (runPhase ph prog).map (fun (changed, out) => (changed, !decide (out = prog)))

/-- `ChangedFlagValid` for one phase on one program: `changed = true ↔
    progOut ≠ progIn`, on full structural equality of `Program`.

    A phase that raises a diagnostic is *skipped* (`true`), not failed: several
    phases legitimately reject inputs (`typeCheck` on an ill-typed program,
    `symbolicEval` on one it cannot evaluate), and a diagnostic is not a
    `changed`-flag violation. This is the same convention as
    `Procedure.TestSupport.checkChangedFlagValid`. -/
def changedFlagValid (ph : Core.PipelinePhase) (prog : Program) : Bool :=
  match phaseOutcome ph prog with
  | some (reported, actuallyChanged) => reported == actuallyChanged
  | none => true

/-- Does any procedure in `prog` contain a `loop` statement, at any depth?

    **This is a precondition of `symbolicEval`, not a stylistic filter.**
    `Core.Statement.evalOneStmt` answers a `.loop` with `panic!`
    (`StatementEval.lean:605`), whose message says "transform your program to
    eliminate loops before calling `Core.Statement.evalAux`". The real pipeline
    satisfies this by running `loopElimPipelinePhase` first; a sweep that applies
    each phase *independently* to raw generated input does not, so running
    `symbolicEval` on a program with a loop prints a Lean panic and backtrace into
    the middle of the harness output.

    The panic is recoverable (`panic!` returns the `Inhabited` default rather than
    aborting), so this was cosmetic rather than a wrong verdict — but a backtrace
    interleaved into the results is indistinguishable from a crash at a glance,
    and it made the suite output non-deterministic. -/
def programHasLoop (prog : Program) : Bool :=
  prog.decls.any fun
    | .proc p _ => StrataGenerators.Stmt.TestSupport.countLoopsStmts (bodyStmts p.body) > 0
    | _ => false

/-- Phases that require loop-free input. Only `symbolicEval` evaluates statements;
    every other phase is a syntactic program-to-program transform. -/
def requiresLoopFree : List String := ["symbolicEval"]

/-- `changedFlagValid`, skipping a phase whose precondition the input violates.
    Skipping (rather than failing) is the same convention `changedFlagValid`
    already uses for a phase that raises a diagnostic: an unmet precondition is
    not a `changed`-flag violation. -/
def changedFlagValidGuarded (np : NamedPhase) (prog : Program) : Bool :=
  if requiresLoopFree.contains np.label && programHasLoop prog then true
  else changedFlagValid np.phase prog

/-- The phases from `phases` whose flag is unfaithful on `prog`, by label,
    deduplicated (`FilterProcedures` occurs twice in the pipeline). Used both by
    the properties and by the diagnostic that names the offenders. -/
def violators (phases : List NamedPhase) (prog : Program) : List String :=
  (phases.filterMap fun np =>
    if changedFlagValidGuarded np prog then none else some np.label).dedup

-- ── Reporting ─────────────────────────────────────────────────────────────
-- A failing sweep says only *that* some phase's flag is unfaithful. These render
-- *which* phase and *how*, for the Tyche panels and for anyone debugging a run.

/-- What `np` did to `prog`, in one line: the flag it reported against whether the
    program actually changed, or why the sweep skipped it. Reads `phaseOutcome`, so
    it reports exactly what `changedFlagValidGuarded` scored. -/
def outcomeDescription (np : NamedPhase) (prog : Program) : String :=
  if requiresLoopFree.contains np.label && programHasLoop prog then
    "skipped — the input has a loop, which this phase's evaluator cannot answer"
  else match phaseOutcome np.phase prog with
    | none => "skipped — the phase raised a diagnostic"
    | some (reported, actuallyChanged) =>
      s!"reported changed = {reported}, program {if actuallyChanged then "differs" else "unchanged"}"

/-- The sweep's offenders on `prog`, one line each, naming the phase and what it
    reported. This is the localisation behind a failing sweep: the property says
    the flag is unfaithful somewhere, this says where and how.

    A label is described by the *first* phase carrying it, since `violators`
    deduplicates and `FilterProcedures` occurs twice in `corePipelinePhases`. -/
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

-- ── Constructed no-op witnesses ───────────────────────────────────────────

/-- A minimal procedure with an empty structured body. -/
def mkProc (n : String) : Procedure :=
  { header := { name := ⟨n, ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] }

/-- A program with one procedure and **no axiom declarations at all**, so
    `RemoveIrrelevantAxioms` cannot prune anything: any `changed = true` here is
    unconditionally wrong, independent of which axioms count as irrelevant. -/
def axiomFreeProgram : Program :=
  { decls := [Decl.proc (mkProc "A") .empty] }

/-- One constructed witness: a phase applied to a program on which it provably
    cannot change anything, so a faithful flag must be `false`.

    Bundling the phase *with* its program — rather than leaving each check a
    standalone closed `Bool` — is what lets a Tyche panel display the very
    program the verdict was computed on. `check` below is the verdict; nothing
    else recomputes it. -/
structure NoOpWitness where
  /-- The phase's own name, for display. -/
  label : String
  phase : Core.PipelinePhase
  /-- The program on which `phase` is provably a no-op. -/
  prog : Program

/-- `ChangedFlagValid` on the witness: `false` exactly when the phase claims to
    have changed a program it cannot have changed. -/
def NoOpWitness.check (w : NoOpWitness) : Bool := changedFlagValid w.phase w.prog

/-- The witness's phase as a `NamedPhase`, so the reporting helpers above apply to
    a witness as they do to a swept phase. -/
def NoOpWitness.named (w : NoOpWitness) : NamedPhase := ⟨w.label, w.phase⟩

/-- `RemoveIrrelevantAxioms` on a program with no axioms — it has nothing to
    prune, whatever "irrelevant" means. -/
def irrelevantAxiomsNoOp : NoOpWitness :=
  ⟨"RemoveIrrelevantAxioms", Core.irrelevantAxiomsPipelinePhase [], axiomFreeProgram⟩

/-- `FilterProcedures` with every procedure of the program in the target set —
    nothing is removable. -/
def filterNoOp : NoOpWitness :=
  ⟨"FilterProcedures",
   Core.filterProceduresPipelinePhase (programProcNames axiomFreeProgram) true,
   axiomFreeProgram⟩

/-- **HONEST FAILURE — pins `IrrelevantAxioms.lean:81`.** `RemoveIrrelevantAxioms`
    on an axiom-free program is necessarily a no-op, so the flag must be `false`.
    The phase returns `(true, pruned)` unconditionally, so this **fails**. -/
def checkIrrelevantAxiomsNoOpFlag : Bool := irrelevantAxiomsNoOp.check

/-- **HONEST FAILURE — pins `FilterProcedures.lean:82`.** With every procedure in
    the target set nothing can be removed, so the flag must be `false`. Restates
    the already-pinned `proc:` property on the constructed witness, so the
    uniform sweep is self-contained. -/
def checkFilterNoOpFlag : Bool := filterNoOp.check

-- ── The uniform sweep over generated input ────────────────────────────────

/-- **Uniform `ChangedFlagValid` over every phase of the Core pipeline**, on a
    program assembled from generated procedures.

    This is the regression gate: it does not enumerate the four known offenders,
    it quantifies over `corePipelinePhases`. A phase added later that hardcodes
    its flag is caught here with no new property written.

    **Expected to FAIL** while the four known sites stand — `typeCheck` and
    `symbolicEval` are in this list and both hardcode `true`. Use
    `phaseChangedFlagDiagnostic` to see which phases are responsible on a given
    program; the failure is only informative if the offender set is exactly the
    known one. -/
def checkAllPhasesChangedFlag (ps : List Procedure) : Bool :=
  (violators allCorePhases (mkProgram ps)).isEmpty

/-- Phases with a *known* `changed`-flag defect, excluded from the honest half of
    the sweep below.

    The first four hardcode the flag to `true` (see the module doc). `PrecondElim`
    is different and must not be conflated with them: it *computes* its flag, but
    computes it wrongly in one branch — `transformStmt`'s `.funcDecl` case
    (`PrecondElim.lean:318–338`) inserts a `{name}$$wf` block for obligations found
    in a declared function's **body** while returning a flag derived only from
    `!decl.preconditions.isEmpty`. So it reports `changed = false` having rewritten
    the program: a false *negative*, where the other four are false positives.

    That bug is separately pinned by `proc: PrecondElim changed flag is faithful`,
    and it fires on only ~0.5% of generated programs (it needs a declared function
    with no preconditions of its own whose body calls a partial function, e.g.
    `Int.SafeDiv`), which is exactly why it must be excluded here by name rather
    than left to chance: otherwise this property is *intermittently* red and its
    green runs mean nothing. -/
def knownDefectivePhases : List String :=
  [ -- hardcode `true` (false positives)
    "FilterProcedures", "RemoveIrrelevantAxioms", "typeCheck", "symbolicEval",
    -- computes the flag, but misses the `.funcDecl` `$$wf` insertion (false negative)
    "PrecondElim" ]

/-- The phases the honest half of the sweep covers: every phase of the pipeline
    with a known defect removed. Named so that a report can sweep *exactly* the
    list the property scores rather than a hand-copied approximation of it. -/
def honestPhases : List NamedPhase :=
  allCorePhases.filter (fun np => !knownDefectivePhases.contains np.label)

/-- The honest half of the sweep: every phase *except* those with a known defect
    must have a faithful flag. Expected to **pass**, and it is what actually
    guards against a regression in the honestly-computing phases — `CallElim`,
    `TermCheck`, `InsertLoopInvariantAsserts`, `LoopElim` and `CommonSubexprElim`.

    Keeping the two directions in separate properties means a new violation among
    the honest phases shows up as a *newly failing* property rather than as a
    change in the detail of an already-red one. That only works if this property
    is reliably green, hence `knownDefectivePhases` above. -/
def checkHonestPhasesChangedFlag (ps : List Procedure) : Bool :=
  (violators honestPhases (mkProgram ps)).isEmpty

end StrataGenerators.PhaseChangedFlag
