import StrataTests
import LSpec

/-!
# The test driver (`lake test`)

This driver prints the property registry through `LSpec.lspecIO`. The setting
`testDriver = "test"` names it.

```bash
lake test -- [numTrials] [maxSize] [flags]
```

The same command in two steps:

```bash
lake build test && .lake/build/bin/test [numTrials] [maxSize] [flags]
```

For the flags, see `StrataGenerators.Test.Cli`. The exit code gives the verdict of the
properties. The diagnostics and the Tyche pass do not change it.

The suite holds each `@[strata_property]` declaration that `StrataTests` reaches. This
file names no single property, and you cannot add a property here.

`StrataGenerators.Test.Driver` does all of the work except the output. The
`PlainTestRunner` driver, which does not use LSpec, uses the same module. Both drivers
fold the same `List TestDecl`. Therefore the two drivers always agree on what the suite
tests, and they can differ only in how they print a verdict.
-/

open StrataGenerators.Test
open LSpec (TestSeq lspecIO)

/-- Every property that a file under `StrataTests/` registers. -/
def registry : List TestDecl := strata_registry%

/-- Every diagnostic that a file under `StrataTests/` registers. -/
def diagnostics : List Diagnostic := strata_diagnostics%

/-- The label that LSpec prints. The *name* of a property shows if the property is
    expected to fail. `TestSeq.individualIO` reports a `Bool`, so it has no third state
    for such a property. Without the tag in the name, a reconciled verdict looks the
    same as a pass. -/
def label (d : TestDecl) : String :=
  match d.expect with
  | .mustHold => d.name
  | .knownFailure _ => s!"{d.name} [known failure]"

/-- One property as an LSpec node. `TestDecl.run` reduces the verdict to the tuple
    `(passed, counts, message)`, which is the tuple that `individualIO` needs. LSpec
    therefore never sees a `Prop`, and Lean synthesizes no `Testable` instance here.
    LSpec supplies only the groups, the output and the exit code. -/
def node (cfg : RunConfig) (d : TestDecl) : TestSeq :=
  .individualIO (label d) none
    (do
      let o ← d.run cfg
      let (samples, total) := o.counts.getD (0, 0)
      let msg := if o.skipped then some "skipped (gate not enabled)" else o.message
      pure (o.passed, samples, total, msg))
    .done

def main (args : List String) : IO UInt32 := do
  let cli := parseCli args
  if let some code ← setup cli registry then
    return code
  let selected := cli.resolve registry

  -- One LSpec suite per report group, in the registry's own order.
  let suites := (suiteGroups selected).map fun (group, props) =>
    (group, [props.foldr (fun d rest => node cli.run d ++ rest) TestSeq.done])
  let exitCode ← lspecIO (.ofList suites) []

  cleanup cli selected diagnostics
  return exitCode
