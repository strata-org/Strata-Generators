import StrataTests
import LSpec

/-!
# The same registry, rendered by LSpec

A second driver over the *same* `List TestDecl`, printing through `LSpec.lspecIO`
instead of the plain reporter. It exists to keep the package honest about its
dependency on LSpec: if the two drivers ever disagreed about a verdict, the
disagreement would be in the rendering, since the suite they run is one value neither
of them constructs.

That is a much stronger guarantee than the arrangement it replaces, where each driver
assembled the suite itself from shared bundles and the two assemblies had to be kept
in step by review.

```bash
lake build lspec-test && .lake/build/bin/lspec-test [numTrials] [maxSize] [flags]
```

Every property joins the suite as a `TestSeq.individualIO` node holding
`TestDecl.run`, so LSpec supplies only the grouping, the printing and the exit code.
The plain driver (`TestRunner.lean`) is the one registered with `lake test`.
-/

open StrataGenerators.Test
open LSpec (TestSeq lspecIO)

/-- Every property registered anywhere under `StrataTests/`. -/
def registry : List TestDecl := strata_registry%

/-- Every diagnostic registered anywhere under `StrataTests/`. -/
def diagnostics : List Diagnostic := strata_diagnostics%

/-- One property as an LSpec node. `TestDecl.run` has already reduced the verdict to
    `(passed, counts, message)`, which is exactly `individualIO`'s tuple — so LSpec
    never sees a `Prop` and no `Testable` instance has to be synthesized here. -/
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

  -- Refuse to run against a stale import root: this binary was linked from the old
  -- one, so a property file added since then is not in `registry` at all. Rewriting it
  -- here and asking for a re-run is the only honest option — reporting a green suite
  -- that silently omits a file is the failure this guards against.
  if ← StrataGenerators.Test.ImportRoot.ensureFresh then
    return 1
  let selected := cli.select registry

  if cli.listOnly then
    listRegistry selected
    return 0

  let dups := duplicateNames selected
  unless dups.isEmpty do
    IO.eprintln s!"error: property name(s) registered twice: {String.intercalate ", " dups}"
    return 1

  IO.println s!"Running {selected.length} of {registry.length} properties \
    ({cli.run.numTrials} trials, max size {cli.run.maxSize})..."
  IO.println ""

  -- One LSpec suite per report group, in the registry's own order.
  let suites := (suiteGroups selected).map fun (suite, props) =>
    (suite, [props.foldr (fun d rest => node cli.run d ++ rest) TestSeq.done])
  let exitCode ← lspecIO (.ofList suites) []

  if cli.only.isEmpty then
    runDiagnostics diagnostics cli.run

  if cli.tycheEnabled then
    IO.println ""
    IO.println s!"Generating Tyche visualizations ({cli.tycheSamples} samples/panel)..."
    let handle ← IO.FS.Handle.mk cli.tycheOut .write
    writePanels handle selected diagnostics cli.run cli.tycheSamples
    IO.println s!"Tyche output written to {cli.tycheOut}"

  return exitCode
