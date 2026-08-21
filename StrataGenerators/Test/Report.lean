import StrataGenerators.Test.Types

/-!
# Reporting a registry

Grouping, printing and the exit code — the whole of a test driver that is not
Tyche or CLI parsing. Depends on `Plausible` only through `Types`, so a driver
built on this module carries no test-framework dependency at all.

The LSpec rendering of the same registry lives in
`StrataGenerators.Test.LSpecReport`. Both read the same `List TestDecl`, so the
two drivers this package ships cannot disagree about *what* is tested; they differ
only in how a verdict is printed and aggregated.
-/

namespace StrataGenerators.Test

/-- The registry grouped by `TestDecl.group` — the `area` of an `area: description`
    name — with groups in first-appearance order and properties in registration order
    within a group. Deterministic, so a report diff between two runs shows verdict
    changes and nothing else. -/
def suiteGroups (ds : List TestDecl) : List (String × List TestDecl) :=
  ds.foldl (init := []) (fun acc d =>
    let g := d.group
    if acc.any (·.1 == g) then
      acc.map (fun (s, xs) => if s == g then (s, xs ++ [d]) else (s, xs))
    else acc ++ [(g, [d])])

/-- Names carried by more than one property. Two properties sharing a name would
    silently collapse their Tyche panels and make a result line ambiguous, so a
    driver refuses to run when this is non-empty. The old front end had the same
    guard as a `#guard` over a hand-maintained list of names; here it is a fact
    about the registry itself, so it cannot be defeated by forgetting to add a
    name to the list. -/
def duplicateNames (ds : List TestDecl) : List String :=
  let names := ds.map (·.name)
  names.foldl (init := []) (fun dups n =>
    if dups.contains n then dups
    else if (names.filter (· == n)).length > 1 then dups ++ [n]
    else dups)

/-- The line a finished property prints. -/
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

/-- Totals over a run, for the summary line. -/
structure Totals where
  passed  : Nat := 0
  failed  : Nat := 0
  skipped : Nat := 0
  /-- Known failures: reconciled against a `TestDecl.expect` that is not `mustHold`.
      Counted apart from `passed` for the same reason `skipped` is — the run learned
      nothing from them, so folding them into the pass count would overstate what is
      actually verified. -/
  xfailed : Nat := 0

def Totals.add (t : Totals) (o : Outcome) : Totals :=
  if o.skipped then { t with skipped := t.skipped + 1 }
  else if o.xfail then { t with xfailed := t.xfailed + 1 }
  else if o.passed then { t with passed := t.passed + 1 }
  else { t with failed := t.failed + 1 }

/-- Run every property of the registry, printing one group per suite and one line
    per property as it completes, and return the exit code: `0` when nothing
    failed, `1` otherwise. A skipped property never fails the run, but it is
    reported as `SKIP` rather than as a pass — an absent solver must not read as
    green. A known failure is `XFAIL`, for the same reason.

    The exit code needs no knowledge of either: `TestDecl.run` has already reconciled
    every verdict against what its property claims, so `failed` counts exactly the
    properties whose result was not the one declared. -/
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

/-- Run every registered diagnostic, printing its heading first. Diagnostics never
    affect the exit code. -/
def runDiagnostics (diags : List Diagnostic) (cfg : RunConfig) : IO Unit := do
  for d in diags do
    IO.println ""
    IO.println d.name
    d.run cfg

end StrataGenerators.Test
