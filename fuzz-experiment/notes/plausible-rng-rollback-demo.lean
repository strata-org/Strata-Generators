/-
Why the coverage-fuzzing plausible backend hit the stale-RNG bug, but legacy Strata and
Plausible-on-its-own do not. Run from a basalt checkout that has Plausible built:

    cd ../basalt && lake env lean ../Strata-Generators/fuzz-experiment/notes/plausible-rng-rollback-demo.lean

Root cause (case B): Plausible's `Gen` signals failure through `Except GenError`, and catching that
exception ROLLS THE RNG STATE BACK — so a failed draw, if you don't explicitly advance the generator,
repeats forever. Legacy Strata advances in-`Gen` via `Rand.next` inside `retryGen` (case C). The fuzz
backend ran raw generators with one `Gen.run` per draw and no advance (case A) -> stuck. `runPlausible`
advances at the per-draw level (case D).

Observed output (A/B stuck: never a `some` after a `none`; C/D recover):
  A per-draw, no advance   (buggy fuzz)  : [some 116, none, none, none, none, none, none, none, none, none]
  B in-Gen, bare tryCatch  (naive)       : [none, none, none, none, none, none, none, none, none, none]
  C in-Gen + Rand.next     (legacy)      : [some 67, some 64, some 90, some 116, ...]  (all some)
  D per-draw + advance     (runPlausible): [none, some 24, none, none, ..., some 70, ..., some 78]
-/
import Plausible.Gen
open Plausible

/-- Succeeds iff the drawn byte < 128 (so it "fails" ~half the time), else throws a generation
    failure — exactly what a Basalt generator does at a dead end (`default`). -/
def picky : Gen Nat := do
  let ⟨n, _⟩ ← Gen.choose Nat 0 255 (by omega)
  if n < 128 then pure n else throw (.genError "rejected")

/-- One draw, catching a failure to `none`, WITHOUT advancing the RNG. -/
def drawNaive : Gen (Option Nat) := tryCatch (some <$> picky) (fun _ => pure none)

/-- One draw; on failure advance the RNG (`Rand.next`) and retry — this IS Strata's `retryGen`. -/
def drawRetry : Nat → Gen (Option Nat)
  | 0 => pure none
  | fuel+1 => tryCatch (some <$> picky) (fun _ => do let _ ← Rand.next; drawRetry fuel)

/-- (A) FUZZING, buggy: one `Gen.run` PER draw, no advance on failure. -/
def a_fuzzBuggy (k : Nat) : IO (List (Option Nat)) := do
  let mut o := #[]
  for _ in [0:k] do o := o.push (← (try (some <$> Gen.run picky 0) catch _ => pure none))
  return o.toList

/-- (B) NAIVE in-`Gen`: one `Gen.run`, threaded, bare `tryCatch` (no `Rand.next`). -/
def b_naiveInGen (k : Nat) : IO (List (Option Nat)) :=
  Gen.run ((List.range k).mapM (fun _ => drawNaive)) 0

/-- (C) LEGACY: one `Gen.run`, threaded, in-`Gen` retry via `Rand.next` (`retryGen`). -/
def c_legacyRetry (k : Nat) : IO (List (Option Nat)) :=
  Gen.run ((List.range k).mapM (fun _ => drawRetry 60)) 0

/-- (D) FIX (`runPlausible`): one `Gen.run` per draw, advance the RNG on failure. -/
def d_fuzzFixed (k : Nat) : IO (List (Option Nat)) := do
  let mut o := #[]
  for _ in [0:k] do
    o := o.push (← (try (some <$> Gen.run picky 0)
                    catch _ => do let _ ← Gen.run (Rand.next : Gen Nat) 0; pure none))
  return o.toList

#eval do IO.println s!"A per-draw, no advance   (buggy fuzz)  : {← a_fuzzBuggy 10}"
#eval do IO.println s!"B in-Gen, bare tryCatch  (naive)       : {← b_naiveInGen 10}"
#eval do IO.println s!"C in-Gen + Rand.next     (legacy)      : {← c_legacyRetry 10}"
#eval do IO.println s!"D per-draw + advance     (runPlausible): {← d_fuzzFixed 10}"
