import StrataGenerators.Test.Types

/-!
# The report for a registry

This module holds the groups, the output and the exit code. This is all of a test driver that
is not the Tyche pass and not the command line. It depends on `Plausible` only through `Types`,
so a driver on this module depends on no test framework.

Both drivers read the same `List TestDecl`. Therefore they cannot disagree about *what* the
suite tests. They differ only in how they print a verdict and how they collect the results.
-/

namespace StrataGenerators.Test

/-- The registry in groups, by `TestDecl.group`, which is the `area` part of a name of the form
    `area: description`. The groups are in the order of their first occurrence, and the
    properties in a group are in registration order. The order is deterministic, so a diff of
    two reports shows only the changes of a verdict. -/
def suiteGroups (ds : List TestDecl) : List (String × List TestDecl) :=
  ds.foldl (init := []) (fun acc d =>
    let g := d.group
    if acc.any (·.1 == g) then
      acc.map (fun (s, xs) => if s == g then (s, xs ++ [d]) else (s, xs))
    else acc ++ [(g, [d])])

/-- The names that more than one property has. Two properties with one name would join their
    Tyche panels and make a result line unclear. Therefore a driver refuses to run when this
    list is not empty. The check reads the registry itself, so no one keeps a list of names by
    hand. -/
def duplicateNames (ds : List TestDecl) : List String :=
  let names := ds.map (·.name)
  names.foldl (init := []) (fun dups n =>
    if dups.contains n then dups
    else if (names.filter (· == n)).length > 1 then dups ++ [n]
    else dups)

/-- The line that the report prints for a property that finished. -/
def Outcome.line (o : Outcome) (name : String) : String :=
  if o.skipped then
    s!"  - SKIP {name}"
  else
    let counts := match o.counts with
      | some (ok, total) => s!" ({ok}/{total})"
      | none => ""
    let verdict :=
      if o.xfail then s!"  ? XFAIL{counts} {name}"
      else if o.passed then s!"  ✓ PASS{counts} {name}" else s!"  × FAIL{counts} {name}"
    match o.message with
    | some m => s!"{verdict}\n    {m}"
    | none => verdict

/-- The totals over a run, for the summary line. -/
structure Totals where
  passed  : Nat := 0
  failed  : Nat := 0
  skipped : Nat := 0
  /-- The number of known failures, which `Outcome.reconcile` matched against a
      `TestDecl.expect` that is not `mustHold`. The count is separate from `passed`, for the
      same reason as `skipped`: the run learned nothing from them, and one count would claim
      more than the run verified. -/
  xfailed : Nat := 0

/-- Adds one outcome to the totals. -/
def Totals.add (t : Totals) (o : Outcome) : Totals :=
  if o.skipped then { t with skipped := t.skipped + 1 }
  else if o.xfail then { t with xfailed := t.xfailed + 1 }
  else if o.passed then { t with passed := t.passed + 1 }
  else { t with failed := t.failed + 1 }

/-- Runs each property of the registry. It prints one heading for each group, and one line for
    each property when the property finishes. The result is the exit code: `0` when no property
    failed, and `1` otherwise.

    A skipped property never fails the run, but the report gives `SKIP` for it and not a pass,
    because a solver that is not present must not look like a pass. A known failure gets `XFAIL`
    for the same reason.

    The exit code needs neither of these two cases. `TestDecl.run` reconciled each verdict
    against the claim of its property, so `failed` counts exactly the properties whose result
    differs from the claim. -/
def runRegistry (ds : List TestDecl) (cfg : RunConfig) : IO UInt32 := do
  let dups := duplicateNames ds
  unless dups.isEmpty do
    IO.eprintln s!"error: {dups.length} property name(s) are registered twice: \
      {String.intercalate ", " dups}"
    IO.eprintln "Each `TestDecl.name` must be unique; rename one of them."
    return 1
  let mut tally : Totals := {}
  for (suite, props) in suiteGroups ds do
    IO.println suite
    for d in props do
      let o ← d.run cfg
      IO.println (o.line d.name)
      tally := tally.add o
  IO.println ""
  IO.println s!"{tally.passed} passed, {tally.failed} failed, \
    {tally.xfailed} known to fail, {tally.skipped} skipped (of {ds.length} run)"
  return if tally.failed == 0 then 0 else 1

/-- Runs each registered diagnostic, and prints its heading first. A diagnostic never changes
    the exit code. -/
def runDiagnostics (diags : List Diagnostic) (cfg : RunConfig) : IO Unit := do
  for d in diags do
    IO.println ""
    IO.println d.name
    d.run cfg

end StrataGenerators.Test
