import Plausible

/-!
# A minimal, LSpec-free property-test harness (Plausible only)

This module reimplements the *small slice* of `LSpec` that the Strata generator
test suite actually uses, directly against `Plausible`. Its purpose is to
de-risk dropping the LSpec dependency: `PlainTestMain` assembles the exact same
suites as the LSpec-based `TestMain`, using the combinators here instead of
`LSpec.checkIO`/`LSpec.lspecIO`, and both drivers must report the same
pass/fail verdicts and the same exit code.

The key observation is that LSpec's runtime
harness is a thin wrapper over Plausible: `checkIO` runs `Plausible`'s testable
runner and packages the result, `TestSeq.individualIO` merely holds an
`IO (Bool × Nat × Nat × Option String)` action, and `lspecIO` iterates suites,
prints per-property lines, and aggregates an exit code. Nothing in the Strata
property plumbing leaks an LSpec type, so this ~small reimplementation suffices.

## Output format

Unlike LSpec's subscript/superscript quantifier notation, this harness prints a
deliberately simpler `PASS`/`FAIL (n/m)` line. The point of the second driver is
dependency-independence, not byte-identical output, so we do not reproduce the
`∃ₙ` / `∃ⁿ/ₘ` formatting. Verdicts and the aggregate exit code match LSpec
exactly; only the surface text differs.
-/

namespace StrataGenerators.PlainHarness

open Plausible

/-- The result of running one property: whether it passed and the line to print. -/
structure Result where
  pass : Bool
  line : String

open Plausible.Decorations in
/-- Run a Plausible property `p` under configuration `cfg` and produce a
    `Result`. Mirrors `LSpec.checkIO`: it synthesizes the `Testable` instance via
    the same `mk_decorations` elaborator (so `∀`-props over our wrapper types are
    testable verbatim), runs `Plausible.Testable.checkIO`, and formats the
    outcome. On failure the counterexample text from Plausible is appended,
    indented, so the diagnostics match what LSpec would surface. -/
def runProperty (name : String) (p : Prop) (cfg : Configuration := {})
    (p' : DecorationsOf p := by mk_decorations) [Testable p'] : IO Result := do
  match ← Testable.checkIO p' cfg with
  | .success _ =>
    pure ⟨true, s!"  ✓ PASS ({cfg.numInst}/{cfg.numInst}) {name}"⟩
  | .gaveUp n =>
    pure ⟨false, s!"  × FAIL {name}\n    Gave up {n} times"⟩
  | .failure _ xs n =>
    let msg := Testable.formatFailure "Found problems!" xs n
    pure ⟨false, s!"  × FAIL {name}\n    {msg}"⟩

/-- Run an IO-based check that already produces the `LSpec.checkIO`-style tuple
    `(success, numSamples, totalTests, errorMsg)`. This is the plain-harness
    analogue of `TestSeq.individualIO`: the action shrinks/prints its own
    reproducers as it runs, and here we only format the final verdict line. -/
def runIOProperty (name : String)
    (action : IO (Bool × Nat × Nat × Option String)) : IO Result := do
  let (success, numSamples, totalTests, msgOpt) ← action
  if success then
    pure ⟨true, s!"  ✓ PASS ({numSamples}/{totalTests}) {name}"⟩
  else
    let suffix := match msgOpt with
      | some m => s!"\n    {m}"
      | none   => ""
    pure ⟨false, s!"  × FAIL ({numSamples}/{totalTests}) {name}{suffix}"⟩

/-- Assert a closed `Bool` — a property with no generated input, whose verdict is
    a single constructed witness rather than a sample. The plain-harness analogue
    of `LSpec.test`.

    Used by the pipeline-phase no-op witnesses and the two targeted printer
    witnesses: in each case the sharp statement of the defect is one specific
    program or operator, so sampling would only obscure it. There is no trial
    count to report, hence the bare `PASS`/`FAIL` line. -/
def runUnitProperty (name : String) (verdict : Bool) : IO Result :=
  if verdict then
    pure ⟨true, s!"  ✓ PASS {name}"⟩
  else
    pure ⟨false, s!"  × FAIL {name}"⟩

/-- Run one named suite: print its header, run each property in order (printing
    each result line as it completes), and return whether every property in the
    suite passed. Mirrors the per-suite structure of `LSpec.lspecIO`. -/
def runSuite (name : String) (props : List (IO Result)) : IO Bool := do
  IO.println name
  let mut ok := true
  for prop in props do
    let r ← prop
    IO.println r.line
    ok := ok && r.pass
  pure ok

/-- Run all suites and return the aggregate exit code: `0` if every property in
    every suite passed, `1` otherwise. Matches `LSpec.lspecIO`'s exit-code
    semantics (the whole run gates on any single failure). -/
def runSuites (suites : List (String × List (IO Result))) : IO UInt32 := do
  let mut allOk := true
  for (name, props) in suites do
    let ok ← runSuite name props
    allOk := allOk && ok
  if allOk then pure 0 else pure 1

end StrataGenerators.PlainHarness
