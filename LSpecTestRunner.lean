import StrataTests
import LSpec

/-!
# The test driver (`lake test`)

The reference driver. It renders the registry through `LSpec.lspecIO`, and it is what
`testDriver = "test"` names.

```bash
lake test -- [numTrials] [maxSize] [flags]
```

or, equivalently:

```bash
lake build test && .lake/build/bin/test [numTrials] [maxSize] [flags]
```

See `StrataGenerators.Test.Cli` for the flags. The exit code is the property verdict;
the diagnostics and the Tyche pass never affect it.

The suite it runs is whatever `@[strata_property]` declarations are reachable from
`StrataTests` — it knows no individual property, and there is nowhere to add one.

Everything except the rendering is `StrataGenerators.Test.Driver`, shared with the
LSpec-free `PlainTestRunner`. Both fold the same `List TestDecl`, so the two cannot
disagree about what is tested, only about how a verdict is printed.
-/

open StrataGenerators.Test
open LSpec (TestSeq lspecIO)

/-- Every property registered anywhere under `StrataTests/`. -/
def registry : List TestDecl := strata_registry%

/-- Every diagnostic registered anywhere under `StrataTests/`. -/
def diagnostics : List Diagnostic := strata_diagnostics%

/-- One property as an LSpec node. `TestDecl.run` has already reduced the verdict to
    `(passed, counts, message)`, which is exactly `individualIO`'s tuple — so LSpec never
    sees a `Prop` and no `Testable` instance is synthesized here. LSpec supplies the
    grouping, the printing and the exit code, and nothing else. -/
def node (cfg : RunConfig) (d : TestDecl) : TestSeq :=
  .individualIO d.name none
    (do
      let o ← d.run cfg
      let (samples, total) := o.counts.getD (0, 0)
      let msg := if o.skipped then some "skipped (gate not enabled)" else o.message
      pure (o.passed, samples, total, msg))
    .done

def main (args : List String) : IO UInt32 := do
  let cli := parseCli args
  if let some code ← preflight cli registry then
    return code
  let selected := cli.select registry

  -- One LSpec suite per report group, in the registry's own order.
  let suites := (suiteGroups selected).map fun (group, props) =>
    (group, [props.foldr (fun d rest => node cli.run d ++ rest) TestSeq.done])
  let exitCode ← lspecIO (.ofList suites) []

  postlude cli selected diagnostics
  return exitCode
