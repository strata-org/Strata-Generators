import StrataTests

/-!
# The driver that does not use LSpec (`test-plain`)

This driver runs the same registry as `lake test`, but the reporter of this package
prints the results in place of LSpec. It depends only on `Plausible`.

```bash
lake build test-plain && .lake/build/bin/test-plain [numTrials] [maxSize] [flags]
```

The driver keeps the dependency on LSpec removable. A fork supplies LSpec to this
package, so it is useful to know that the suite runs without LSpec.

This argument holds only if the two drivers agree on all things except the output.
Therefore `StrataGenerators.Test.Driver` holds all of the work except the output, and
the suite is one `List TestDecl` that neither driver builds. The two drivers can differ
only in how they print the results.
-/

open StrataGenerators.Test

/-- Every property that a file under `StrataTests/` registers. -/
def registry : List TestDecl := strata_registry%

/-- Every diagnostic that a file under `StrataTests/` registers. -/
def diagnostics : List Diagnostic := strata_diagnostics%

def main (args : List String) : IO UInt32 := do
  let cli := parseCli args
  if let some code ← setup cli registry then
    return code
  let selected := cli.resolve registry

  let exitCode ← runRegistry selected cli.run
  cleanup cli selected diagnostics
  return exitCode
