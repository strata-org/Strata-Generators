import Plausible

/-!
# A small harness for a property test, on `Plausible` only

This module holds the *small part* of `LSpec` that the test suite of the Strata generators uses,
written against `Plausible`. It makes the dependency on LSpec removable. The driver that does
not use LSpec builds the same suites as the driver that uses LSpec, with the functions of this
module in place of `LSpec.checkIO` and `LSpec.lspecIO`. Both drivers must give the same verdicts
and the same exit code.

The harness of LSpec is a thin layer over Plausible. `checkIO` runs the testable runner of
Plausible and packs the result. `TestSeq.individualIO` holds only an
`IO (Bool × Nat × Nat × Option String)` action. `lspecIO` walks the suites, prints one line for
each property, and collects an exit code. No part of the property code of Strata holds an LSpec
type, so this small module is enough.

## The output

LSpec prints its quantifiers with a subscript and a superscript. This harness prints a simpler
line of the form `PASS (n/m)` or `FAIL (n/m)`, and it does not print the `∃ₙ` and `∃ⁿ/ₘ` forms.
The purpose of the second driver is independence from a dependency, and not output that is equal
byte for byte. The verdicts and the exit code agree with LSpec, and only the text differs.
-/

namespace StrataGenerators.PlainHarness

open Plausible

/-- The result of one property: whether the property passed, and the line to print. -/
structure Result where
  pass : Bool
  line : String

open Plausible.Decorations in
/-- Runs a Plausible property `p` under the configuration `cfg`, and gives a `Result`.

    The function does the same work as `LSpec.checkIO`. It synthesizes the `Testable` instance
    with the `mk_decorations` elaborator, so a `∀` proposition over a wrapper type of this package
    is testable without a change. It then runs `Plausible.Testable.checkIO` and formats the
    result. When the property does not hold, the function adds the text of the counterexample from
    Plausible, with an indent, so the output holds the same data as the output of LSpec. -/
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

/-- Runs a check in `IO` that gives the tuple `(success, numSamples, totalTests, errorMsg)`, which
    is the tuple of `LSpec.checkIO`. This function does the work of `TestSeq.individualIO` for this
    harness. The action shrinks and prints its own reproducers while it runs, so this function only
    formats the last line of the verdict. -/
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

/-- Asserts a closed `Bool`. Such a property has no generated input, and its verdict comes from one
    witness that the author builds. This function does the work of `LSpec.test` for this harness.

    The witnesses for a phase that changes nothing use this function, and so do the two witnesses
    for the printer. In each case the best statement of the defect is one program or one operator,
    and a random sample would hide it. There is no count of trials to report, so the line holds
    only `PASS` or `FAIL`. -/
def runUnitProperty (name : String) (verdict : Bool) : IO Result :=
  if verdict then
    pure ⟨true, s!"  ✓ PASS {name}"⟩
  else
    pure ⟨false, s!"  × FAIL {name}"⟩

/-- Runs one suite with a name. It prints the heading of the suite, and then it runs each property
    in order and prints the line of each result. The result is `true` when each property in the
    suite passed. The structure follows the structure of one suite in `LSpec.lspecIO`. -/
def runSuite (name : String) (props : List (IO Result)) : IO Bool := do
  IO.println name
  let mut ok := true
  for prop in props do
    let r ← prop
    IO.println r.line
    ok := ok && r.pass
  pure ok

/-- Runs each suite and returns the exit code for the whole run: `0` when each property in each
    suite passed, and `1` otherwise. This is the exit code that `LSpec.lspecIO` gives, because one
    property that fails makes the whole run fail. -/
def runSuites (suites : List (String × List (IO Result))) : IO UInt32 := do
  let mut allOk := true
  for (name, props) in suites do
    let ok ← runSuite name props
    allOk := allOk && ok
  if allOk then pure 0 else pure 1

end StrataGenerators.PlainHarness
