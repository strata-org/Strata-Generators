import StrataGenerators.Test.Report
import StrataGenerators.Test.TycheReport
import StrataGenerators.Test.Cli
import StrataGenerators.Test.ImportRoot
import StrataGenerators.HasTypeAGen.SmtEval

/-!
# The work that each driver does around the suite

The package holds 2 drivers. `test` prints the registry through LSpec. `test-plain` prints it
through the reporter of this package, so it depends on no test framework.

This module holds all of the work except the output. The reason for the second driver is to
keep the dependency on LSpec removable, and that argument holds only if the two drivers agree
on *all other things*. Therefore this module holds the check of the import root, the work for
`--list` and `--only`, the check of the solvers for `--smt`, the diagnostics and the Tyche
pass. A driver is then a call to `setup`, the output, and a call to `cleanup`.
-/

namespace StrataGenerators.Test

/-- `--smt` needs a solver on the `PATH`. The agreement property runs each solver in
    `SmtEval.agreementSolvers`, so this function gives an error only when it can start none of
    them. Without the check, the suite reports `0/0 checked` as a pass. When only some solvers
    are absent, the property names them in its own report, because each absent solver costs
    coverage: cvc5 and z3 give different verdicts on a string literal that is not well
    formed. -/
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

/-- The work that a driver does before it prints anything. It refuses a stale import root, it
    answers `--list`, it rejects an empty selection and a duplicate name, it checks the solvers,
    and it prints the header.

    The name has the sense of xUnit: the work before a test run. The function builds nothing, it
    allocates nothing, and it has no partner function that releases a resource.

    The result is `some code` when the driver must stop with that code. It is `none` when the
    driver must continue and print `cli.select registry`. The function does not return the
    selection, because `TestDecl` is in `Type 1` and therefore cannot cross an `IO` boundary.
    `Cli.select` is pure, so a driver calls it. -/
def setup (cli : Cli) (registry : List TestDecl) : IO (Option UInt32) := do
  -- Refuse to run against a stale import root. The linker built this binary from the old root,
  -- so `registry` does not hold a property file that someone added later. The only correct
  -- action is to write the root again and to ask for another run. Without this check, a suite
  -- that misses a file reports a pass.
  if ← ImportRoot.ensureFresh then
    return some 1

  let selected := cli.resolve registry

  if cli.listOnly then
    listRegistry selected
    return some 0

  if selected.isEmpty then
    IO.eprintln "error: no property matched the --only filter."
    IO.eprintln "Run with --list to see what is registered."
    return some 1

  -- A `--known-failure=` name with a spelling mistake must not pass. The run would look as if
  -- the mark took effect, and the property that the flag names would still fail. The check uses
  -- the *selected* registry, so a `--only` filter that removes the property is also an error
  -- and not a no-op.
  let unknown := cli.unknownKnownFailures selected
  unless unknown.isEmpty do
    IO.eprintln s!"error: --known-failure= names no property that this run selected:"
    for n in unknown do
      IO.eprintln s!"  {n}"
    IO.eprintln "It takes a whole property name, not a substring. Run with --list to see \
      the names."
    return some 1

  let dups := duplicateNames selected
  unless dups.isEmpty do
    IO.eprintln s!"error: {dups.length} property name(s) are registered twice: \
      {String.intercalate ", " dups}"
    IO.eprintln "Each `TestDecl.name` must be unique; rename one of them."
    return some 1

  if cli.run.gates.contains "smt" then
    if let some code ← checkSolvers then
      return some code

  IO.println s!"Running {selected.length} of {registry.length} properties \
    ({cli.run.numTrials} trials, max size {cli.run.maxSize})..."

  -- This line is here and not in one of the two reporters, so both drivers print it. The LSpec
  -- driver collects its results through `lspecIO` and never sees an `Outcome`, so it cannot
  -- count the known failures itself. The count at the start also stops a suite that passes
  -- *because* of the marks from looking like a clean run.
  let marked := selected.filter fun d => match d.expect with | .mustHold => false | _ => true
  unless marked.isEmpty do
    IO.println s!"{marked.length} of them are expected to fail and do not gate the exit \
      code (--list shows which, and why)."
  IO.println ""
  return none

/-- The work that a driver does after the suite. It runs the registered diagnostics, and then it
    writes the Tyche panels. Neither part changes the exit code.

    The function releases no resource. It *reports*: the diagnostics print statistics for
    coverage and counts that locate an error, and the Tyche pass writes the panel file. Skip
    this function only when you want none of that output. -/
def cleanup (cli : Cli) (selected : List TestDecl) (diags : List Diagnostic) : IO Unit := do
  -- A filter turns the diagnostics off. A `--only` run is a run about one property, and six
  -- reports about other distributions would hide its result.
  if cli.only.isEmpty then
    runDiagnostics diags cli.run

  -- There is one Tyche panel for each property, and it uses the *same* check as the suite.
  -- Therefore a panel and a result line always agree.
  if cli.tycheEnabled then
    IO.println ""
    IO.println s!"Generating Tyche visualizations ({cli.tycheSamples} samples/panel)..."
    let handle ← IO.FS.Handle.mk cli.tycheOut .write
    writePanels handle selected diags cli.run cli.tycheSamples
    IO.println s!"Tyche output written to {cli.tycheOut}"
    IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
  else
    IO.println ""
    -- Name the flag that stopped the pass. `--quick` also turns the pass off. A report of
    -- `--no-tyche` for a `--quick` run makes a reader look for a flag that they did not give,
    -- or look at a stale `tycheOut` from an earlier run, because this branch writes no file.
    if cli.quick then
      IO.println s!"Tyche visualizations disabled (--quick); no file written, so \
        {cli.tycheOut} — if it exists — is from an earlier run."
      IO.println s!"For the preset's trials/size *with* panels, pass them positionally \
        instead: {quickNumTrials} {quickMaxSize}"
    else
      IO.println "Tyche visualizations disabled (--no-tyche)."

end StrataGenerators.Test
