import StrataGenerators.Test.Report
import StrataGenerators.Test.TycheReport
import StrataGenerators.Test.Cli
import StrataGenerators.Test.ImportRoot
import StrataGenerators.HasTypeAGen.SmtEval

/-!
# What every driver does around the suite

The package ships 2 drivers: `test`, which renders the registry through LSpec, and
`test-plain`, which renders it through the package's own reporter and so carries no
test-framework dependency at all.

Everything except the rendering lives here. That is deliberate: the reason for having a
second driver is to keep the LSpec dependency droppable, and that argument is only worth
anything if the two drivers agree on *everything else*. So the import-root check, the
`--list` and `--only` handling, the `--smt` solver check, the diagnostics and the Tyche
pass are written once, and a driver is a `preflight`, a render, and a `postlude`.
-/

namespace StrataGenerators.Test

/-- `--smt` needs a live solver on `PATH`. The agreement property runs each solver in
    `SmtEval.agreementSolvers`, so this errors out only when it can launch none of them:
    without the check the suite reports a green "0/0 checked". When only some are absent
    the property itself names them in its report, because each absent solver costs
    coverage — cvc5 and z3 give different verdicts on a malformed string literal. -/
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

/-- Everything a driver does before it renders anything: refuse a stale import root,
    serve `--list`, reject an empty selection or a duplicate name, check the solvers, and
    print the header.

    Returns `some code` when the driver should stop with that code, and `none` when it
    should go on and render `cli.select registry`. It does not return the selection,
    because `TestDecl` lives in `Type 1` and so cannot cross an `IO` boundary;
    `Cli.select` is pure, so a driver simply calls it. -/
def preflight (cli : Cli) (registry : List TestDecl) : IO (Option UInt32) := do
  -- Refuse to run against a stale import root. This binary was linked from the old
  -- root, so a property file added since then is not in `registry` at all. Rewriting
  -- the root and asking for a re-run is the only honest option; a green suite that
  -- silently omits a file is the failure this guards against.
  if ← ImportRoot.ensureFresh then
    return some 1

  let selected := cli.select registry

  if cli.listOnly then
    listRegistry selected
    return some 0

  if selected.isEmpty then
    IO.eprintln "error: no property matched the --only filter."
    IO.eprintln "Run with --list to see what is registered."
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
  IO.println ""
  return none

/-- Everything a driver does after the suite. Neither part affects the exit code. -/
def postlude (cli : Cli) (selected : List TestDecl) (diags : List Diagnostic) : IO Unit := do
  -- Diagnostics are skipped under a filter: a `--only` run is a run about one property,
  -- and six unrelated distribution reports would bury its result.
  if cli.only.isEmpty then
    runDiagnostics diags cli.run

  -- One Tyche panel per property, scored with the *same* check the suite asserted, so a
  -- panel and a result line can never disagree.
  if cli.tycheEnabled then
    IO.println ""
    IO.println s!"Generating Tyche visualizations ({cli.tycheSamples} samples/panel)..."
    let handle ← IO.FS.Handle.mk cli.tycheOut .write
    writePanels handle selected diags cli.run cli.tycheSamples
    IO.println s!"Tyche output written to {cli.tycheOut}"
    IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
  else
    IO.println ""
    -- Name the flag that actually held the pass off. `--quick` disables it too, and
    -- reporting `--no-tyche` for a `--quick` run sends the reader looking for a flag
    -- they did not pass, or worse at a stale `tycheOut` from an earlier run, since no
    -- file is written here at all.
    if cli.quick then
      IO.println s!"Tyche visualizations disabled (--quick); no file written, so \
        {cli.tycheOut} — if it exists — is from an earlier run."
      IO.println "For the preset's trials/size *with* panels, pass them positionally instead: 100 40"
    else
      IO.println "Tyche visualizations disabled (--no-tyche)."

end StrataGenerators.Test
