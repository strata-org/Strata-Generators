import StrataGenerators.MapSeqRunner
import StrataGenerators.Properties

open StrataGenerators.MapSeqRunner

/-!
# Standalone driver for the `Map`/`Sequence` property suite

Separate executable rather than a node in the main `test` driver, for the same
reason `exprSmtEvalAgreement` is opt-in: every sample shells out to a solver, so
a default `lake test` must not depend on one being installed.

Property names come from `PropertyNames` (the shared catalog) rather than being
spelled here, so this driver's labels cannot drift from the catalog's.

Run: `lake build map-seq && .lake/build/bin/map-seq [numTrials] [maxLen]`
-/

def main (args : List String) : IO UInt32 := do
  let numTrials := (args[0]?.bind String.toNat?).getD 10
  let maxLen    := (args[1]?.bind String.toNat?).getD 3

  let report (name : String) (r : Bool × Nat × Nat × Option String) : IO Bool := do
    let (ok, passed, attempted, note) := r
    let status := if ok then "PASS" else "FAIL"
    IO.println s!"[{status}] {name}: {passed}/{attempted} decided obligations"
    match note with
    | some n => IO.println s!"         {n}"
    | none   => pure ()
    pure ok

  IO.println s!"Running Map/Sequence properties ({numTrials} trials, maxLen {maxLen})\n"

  let r1 ← seqModelAgreement numTrials maxLen
  let ok1 ← report PropertyNames.seqModelAgreement r1

  let r2 ← mapModelAgreement numTrials maxLen
  let ok2 ← report PropertyNames.mapAxiomAgreement r2

  let r3 ← arrayTheoryMetamorphic numTrials maxLen
  let ok3 ← report PropertyNames.mapArrayTheoryMetamorphic r3

  let r4 ← seqPrecondObligations numTrials maxLen
  let ok4 ← report PropertyNames.seqPrecondObligations r4

  pure (if ok1 && ok2 && ok3 && ok4 then 0 else 1)
