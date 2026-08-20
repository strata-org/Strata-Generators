import StrataTests

/-!
# The test driver

The whole driver. It knows the registry, the CLI and the Tyche output file, and
nothing about any individual property: the suite it runs is whatever
`@[strata_property]` declarations are reachable from `StrataTests`.

Compare the shape this replaces — a per-property `checkIO` line in a hand-assembled
`TestSeq`, duplicated in a second driver and again in a panel registry. Adding a
property here costs nothing, because there is nowhere to add it.

## Usage

```bash
lake test -- [numTrials] [maxSize] [flags]
```

or, equivalently:

```bash
lake build strata-test && .lake/build/bin/strata-test [numTrials] [maxSize] [flags]
```

See `StrataGenerators.Test.Cli` for the flags. The exit code is the property verdict;
diagnostics and the Tyche pass never affect it.

This driver depends on `Plausible` and nothing else — no test framework. The
LSpec rendering of the same registry is `LSpecTestRunner.lean`; because both fold the
same `List TestDecl`, they cannot disagree about what is tested.
-/

open StrataGenerators.Test

/-- Every property registered anywhere under `StrataTests/`. -/
def registry : List TestDecl := strata_registry%

/-- Every diagnostic registered anywhere under `StrataTests/`. -/
def diagnostics : List Diagnostic := strata_diagnostics%

/-- `--smt` needs a live solver on `PATH`. The agreement property runs each solver in
    `SmtEval.agreementSolvers`, so error out only when it can launch none of them —
    without this check the suite reports a green "0/0 checked". When only some are
    absent, the property itself names them in its report, because each absent solver
    costs coverage: cvc5 and z3 give different verdicts on a malformed string
    literal. -/
def checkSolvers : IO (Option UInt32) := do
  let available ← StrataGenerators.SmtEval.availableAgreementSolvers
  if available.isEmpty then
    IO.eprintln s!"error: --smt requires an SMT solver on PATH, but none of \
      {String.intercalate ", " StrataGenerators.SmtEval.agreementSolvers} could be launched."
    IO.eprintln "Install one (e.g. cvc5 or z3) and ensure it is on PATH, or run without --smt."
    return some 1
  let absent := StrataGenerators.SmtEval.agreementSolvers.filter (!available.contains ·)
  unless absent.isEmpty do
    IO.eprintln s!"warning: --smt will skip these solvers (not on PATH): \
      {String.intercalate ", " absent}"
  return none

def main (args : List String) : IO UInt32 := do
  let cli := parseCli args
  let selected := cli.select registry

  if cli.listOnly then
    listRegistry selected
    return 0

  if selected.isEmpty then
    IO.eprintln "error: no property matched the --only/--suite filters."
    IO.eprintln "Run with --list to see what is registered."
    return 1

  if cli.run.gates.contains "smt" then
    if let some code ← checkSolvers then return code

  IO.println s!"Running {selected.length} of {registry.length} properties \
    ({cli.run.numTrials} trials, max size {cli.run.maxSize})..."
  IO.println ""
  let exitCode ← runRegistry selected cli.run

  -- Diagnostics run after the gating suite and never affect the exit code. They are
  -- skipped under a filter: a `--only` run is a run about one property, and six
  -- unrelated distribution reports would bury its result.
  if cli.only.isEmpty && cli.suites.isEmpty then
    runDiagnostics diagnostics cli.run

  -- The Tyche pass writes one panel per property to `cli.tycheOut`, scoring each
  -- sample with the *same* check the suite asserted, so a panel and a result line can
  -- never disagree.
  if cli.tycheEnabled then
    IO.println ""
    IO.println s!"Generating Tyche visualizations ({cli.tycheSamples} samples/panel)..."
    let handle ← IO.FS.Handle.mk cli.tycheOut .write
    writePanels handle selected diagnostics cli.run cli.tycheSamples
    IO.println s!"Tyche output written to {cli.tycheOut}"
    IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
  else
    IO.println ""
    -- Name the flag that actually held the pass off. `--quick` disables it too, and
    -- reporting `--no-tyche` for a `--quick` run sends the reader looking for a flag
    -- they did not pass — or, worse, at a stale `tycheOut` from an earlier run, since
    -- no file is written here at all.
    if cli.quick then
      IO.println s!"Tyche visualizations disabled (--quick); no file written, so \
        {cli.tycheOut} — if it exists — is from an earlier run."
      IO.println "For the preset's trials/size *with* panels, pass them positionally instead: 100 40"
    else
      IO.println "Tyche visualizations disabled (--no-tyche)."

  return exitCode
