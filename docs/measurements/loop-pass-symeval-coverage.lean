import StrataGenerators.TestScaffold
import StrataGenerators.ProgramGen.UnprovenTransforms

open Plausible
open Lambda Core Imperative
open StrataGenerators
open StrataGenerators.Program.TestSupport
open StrataGenerators.Procedure.TestSupport
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Program.UnprovenTransforms

/-! Coverage measurement for the three §2.9 obligation-preservation properties
    (`checkLoopVcSymbolicNoLoss`, `checkNondetElimSymbolicNoLoss`,
    `checkHoistSymbolicNoLoss` in `ProgramGen/UnprovenTransforms`).

    Each of the three is guarded several times over — the input must typecheck, it
    must not hold a nondeterministic measure-carrying loop, both sides must reach
    the evaluator, and for the hoist the input must satisfy `uniqueInits`. A
    property that is vacuous on every draw reports green while testing nothing, so
    this counts, per draw, how far each one gets:

    * `typechecks`  — the draw survives the `progTypeChecks` screen
    * `screened`    — plus no nondeterministic measure-carrying loop
    * `baseline`    — plus the before-side actually reaches the evaluator
    * `live`        — plus the after-side reaches it too, i.e. the claim is real
    * `fires`       — plus the pass has something to do on this draw

    Run: `lake env lean --run docs/measurements/loop-pass-symeval-coverage.lean` -/

/-- The five-stage tally for one property. -/
structure Tally where
  typechecks : Nat := 0
  screened   : Nat := 0
  baseline   : Nat := 0
  live       : Nat := 0
  fires      : Nat := 0

def fmt (name : String) (t : Tally) (n : Nat) : String :=
  s!"{name}: typechecks={t.typechecks}/{n} screened={t.screened} " ++
  s!"baseline={t.baseline} live={t.live} fires={t.fires}"

/-- Whether some loop of the program carries an invariant or a measure, i.e.
    `InsertLoopInvariantAsserts` has anything to insert. -/
def loopVcFires (p : Program) : Bool :=
  programInvariantCount p > 0 || programMeasureLoopCount p > 0

/-- Whether some body holds a nondeterministic guard, i.e. `NondetElim` rewrites
    something. -/
def nondetFires (p : Program) : Bool :=
  (cmdShapedBodies p).any stmtsHaveNondetGuard

/-- Whether some loop body holds an `init`, i.e. `LoopInitHoist` hoists
    something. -/
def hoistFires (p : Program) : Bool :=
  (cmdShapedBodies p).any fun ss => !Imperative.Block.loopBodyNoInits ss

def main : IO Unit := do
  let n := 400
  let maxSize := 30
  let mut sampled := 0
  let mut vc : Tally := {}
  let mut nd : Tally := {}
  let mut ho : Tally := {}
  -- Every property that FAILED on a draw, so a red tick here is attributable.
  let mut failures : List String := []
  for i in List.range n do
    let size := i % (maxSize + 1)
    let gp ← try Gen.run (Arbitrary.arbitrary (α := GenProgram)) size
             catch _ => pure ⟨{ decls := [] }⟩
    if gp.prog.decls.isEmpty then continue
    let p := gp.prog
    sampled := sampled + 1
    if !progTypeChecks p then continue
    -- `InsertLoopInvariantAsserts`
    vc := { vc with typechecks := vc.typechecks + 1 }
    nd := { nd with typechecks := nd.typechecks + 1 }
    ho := { ho with typechecks := ho.typechecks + 1 }
    if hasNondetMeasureLoop p then continue
    vc := { vc with screened := vc.screened + 1 }
    nd := { nd with screened := nd.screened + 1 }
    if (cmdShapedBodies p).all uniqueInitsB then
      ho := { ho with screened := ho.screened + 1 }
    -- Baselines and live claims, per property.
    if (elimObligationLabels (bareLoopsProgram p)).isSome then
      vc := { vc with baseline := vc.baseline + 1 }
      if (vcElimObligationLabels p).isSome then
        vc := { vc with live := vc.live + 1 }
        if loopVcFires p then vc := { vc with fires := vc.fires + 1 }
    if (vcElimObligationLabels p).isSome then
      nd := { nd with baseline := nd.baseline + 1 }
      if (vcElimObligationLabels (nondetElimProgram p)).isSome then
        nd := { nd with live := nd.live + 1 }
        if nondetFires p then nd := { nd with fires := nd.fires + 1 }
      if (cmdShapedBodies p).all uniqueInitsB then
        ho := { ho with baseline := ho.baseline + 1 }
        if (vcElimObligationLabels (loopInitHoistProgram p)).isSome then
          ho := { ho with live := ho.live + 1 }
          if hoistFires p then ho := { ho with fires := ho.fires + 1 }
    -- And the verdicts themselves.
    if !checkLoopVcSymbolicNoLoss p then failures := "loopVcSymbolicNoLoss" :: failures
    if !checkNondetElimSymbolicNoLoss p then failures := "nondetElimSymbolicNoLoss" :: failures
    if !checkHoistSymbolicNoLoss p then failures := "hoistSymbolicNoLoss" :: failures
  IO.println s!"sampled non-empty draws: {sampled}/{n}"
  IO.println (fmt "loopVcSymbolicNoLoss    " vc sampled)
  IO.println (fmt "nondetElimSymbolicNoLoss" nd sampled)
  IO.println (fmt "hoistSymbolicNoLoss     " ho sampled)
  IO.println s!"failures: {failures.length} {failures.dedup}"
