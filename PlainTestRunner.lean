import StrataTests

/-!
# The LSpec-free driver (`test-plain`)

The same registry as `lake test`, rendered by the package's own reporter instead of by
LSpec. It depends on `Plausible` and nothing else.

```bash
lake build test-plain && .lake/build/bin/test-plain [numTrials] [maxSize] [flags]
```

It exists to keep the LSpec dependency droppable. LSpec reaches this package only
through a fork pinned to Lean 4.29, because mainline LSpec is on 4.31, so it is worth
knowing at all times that the suite runs without it.

That argument only holds if the two drivers agree on everything except the rendering,
which is why everything except the rendering is `StrataGenerators.Test.Driver` and the
suite itself is one `List TestDecl` that neither driver constructs. A disagreement
between them could only be in the printing.
-/

open StrataGenerators.Test

/-- Every property registered anywhere under `StrataTests/`. -/
def registry : List TestDecl := strata_registry%

/-- Every diagnostic registered anywhere under `StrataTests/`. -/
def diagnostics : List Diagnostic := strata_diagnostics%

def main (args : List String) : IO UInt32 := do
  let cli := parseCli args
  if let some code ← setup cli registry then
    return code
  let selected := cli.resolve registry

  let exitCode ← runRegistry selected cli.run
  cleanup cli selected diagnostics
  return exitCode
