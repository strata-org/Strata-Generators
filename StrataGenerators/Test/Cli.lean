import StrataGenerators.Test.Types

/-!
# The driver command line

Shared by every driver, so the flags mean the same thing whichever one is run.

```
lake test -- [numTrials] [maxSize] [flags]
```

Positional arguments configure the Plausible run (`numTrials` = trials per
property, default 1000; `maxSize` = maximum generator size, default 5).

`maxSize` is the number a generator receives directly: a term depth, a statement
nesting level, a declaration count. Plausible ramps the size from 0 to this number
over the trials of a property, so a run tests the small shapes first and the
largest ones last. The number is small because these are *structural* bounds — a
depth-6 term or a 6-declaration program is already a large input, and the cost of
generating one grows with the bound rather than in proportion to it.

* `--quick` — a fast preset for a short cycle of work: 100 trials, maximum size
  2, and no Tyche pass. Use it to find a defect and the defaults to gate a merge.
  A positional argument has higher precedence, so `--quick 500` gives 500 trials
  and keeps the rest of the preset.
* `--no-tyche` — skip the Tyche visualization pass (on by default).
* `--tyche-out=PATH` — Tyche JSONL output path (default `tyche_output.jsonl`).
* `--tyche-samples=N` — samples per Tyche panel (default 1000).
* `--smt` — enable the `smt` gate, admitting the properties whose oracle is a live
  `cvc5`/`z3`. Off by default, so the suite needs no solver.
* `--only=SUBSTRING` — run only the properties whose name contains `SUBSTRING`.
  Repeatable; a property matching any of them runs. The rest are not reported at
  all, which is what makes iterating on one new property cheap.
* `--list` — print the registry (name, group, gate, expectation) and exit without running
  anything. The answer to "did my property get picked up?".
* `--known-failure=NAME` — treat `NAME` as known to fail for this run: suppress its
  counterexample and stop it gating the exit code. Repeatable. The permanent form is
  `knownFailure` at the property, which carries a reason; this flag is for the
  short cycle of work where you want the rest of the suite's colour while a defect is
  being triaged. Unlike `--only=`, it takes a **whole property name**, not a substring:
  a substring would silently claim that every property in a group must fail, and the
  ones that hold would then be reported as failures.

There is no `--suite=` flag: a report group *is* a name prefix, so `--only="lift:"`
selects the `lift` group exactly.
-/

namespace StrataGenerators.Test

/-- Everything a driver reads off the command line: the `RunConfig` every property
    sees, plus the driver-level options that no property needs to know about. -/
structure Cli where
  run          : RunConfig
  tycheEnabled : Bool
  tycheOut     : String
  tycheSamples : Nat
  /-- Name substrings to filter the registry by; empty means no filter. -/
  only         : List String
  /-- Whole property names to mark as known failures for this run only. -/
  knownFailures : List String
  /-- Print the registry and exit. -/
  listOnly     : Bool
  /-- Whether `--quick` was passed, so a driver can name the flag that actually
      held the Tyche pass off (reporting `--no-tyche` for a `--quick` run sends the
      reader looking for a flag they did not pass). -/
  quick        : Bool

/-- The number of trials `--quick` selects. -/
def quickNumTrials : Nat := 100

/-- The maximum generator size a run uses by default.

    A generator reads this number as its own bound — a term depth, a nesting level, a
    declaration count — so it is small. `TestScaffold`'s generators receive it unchanged. -/
def defaultMaxSize : Nat := 5

/-- The maximum generator size `--quick` selects. Two levels of structure: enough for a
    non-trivial shape, small enough that a full pass costs seconds. -/
def quickMaxSize : Nat := 2

/-- Parse `args`. See the module doc for the flags. -/
def parseCli (args : List String) : Cli :=
  let flags := args.filter (·.startsWith "--")
  let positional := args.filter (fun a => !a.startsWith "--")
  let flagValue (key : String) : Option String :=
    (flags.find? (·.startsWith key)).map (·.drop key.length |>.toString)
  let flagValues (key : String) : List String :=
    (flags.filter (·.startsWith key)).map (·.drop key.length |>.toString)
  let quick := flags.contains "--quick"
  { run :=
      { numTrials := (positional[0]? >>= String.toNat?).getD
                       (if quick then quickNumTrials else 1000)
        maxSize   := (positional[1]? >>= String.toNat?).getD
                       (if quick then quickMaxSize else defaultMaxSize)
        gates     := if flags.contains "--smt" then ["smt"] else [] }
    tycheEnabled := !flags.contains "--no-tyche" && !quick
    tycheOut     := (flagValue "--tyche-out=").getD "tyche_output.jsonl"
    tycheSamples := ((flagValue "--tyche-samples=").bind String.toNat?).getD 1000
    only          := flagValues "--only="
    knownFailures := flagValues "--known-failure="
    listOnly      := flags.contains "--list"
    quick         := quick }

/-- Whether `needle` occurs in `hay`. -/
private def contains (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

/-- Apply `--only` to the registry. An empty filter keeps everything. -/
def Cli.select (cli : Cli) (ds : List TestDecl) : List TestDecl :=
  ds.filter fun d => cli.only.isEmpty || cli.only.any (contains d.name)

/-- Apply `--known-failure=` to the registry, overriding each named property's
    `expect`. Matching is by whole name; see the module doc for why. -/
def Cli.markKnownFailures (cli : Cli) (ds : List TestDecl) : List TestDecl :=
  ds.map fun d =>
    if cli.knownFailures.contains d.name then
      knownFailure "marked as a known failure on the command line" d
    else d

/-- `--known-failure=` arguments that name no registered property. A driver refuses to
    run when this is non-empty: a mistyped name would otherwise silently do nothing, and
    the run would look like the suppression worked. -/
def Cli.unknownKnownFailures (cli : Cli) (ds : List TestDecl) : List String :=
  cli.knownFailures.filter fun n => !ds.any (fun d => d.name == n)

/-- The registry a driver actually runs: filtered by `--only`, then marked by
    `--known-failure=`. Both drivers and `Driver.setup` go through this, so `--list`
    shows the same expectations the run will use. -/
def Cli.resolve (cli : Cli) (ds : List TestDecl) : List TestDecl :=
  cli.markKnownFailures (cli.select ds)

private def pad (s : String) (n : Nat) : String :=
  s ++ "".pushn ' ' (n - min n s.length)

/-- Print the registry: what is registered, which group it reports under, whether a gate
    holds it back, and whether it is expected to fail. This is how a property author
    confirms their file was picked up, without waiting for a run — and the answer to
    "what is known to fail?", since the registry is where that is now recorded. -/
def listRegistry (ds : List TestDecl) : IO Unit := do
  IO.println s!"{ds.length} propert{if ds.length == 1 then "y" else "ies"} registered"
  for d in ds do
    let gate := match d.gate with | some g => s!"  [--{g}]" | none => ""
    let expect := match d.expect with
      | .mustHold => ""
      | .knownFailure r => s!"\n{pad "" 15}known failure: {r}"
    IO.println s!"  {pad d.group 12} {d.name}{gate}{expect}"
  let marked := ds.filter fun d => match d.expect with | .mustHold => false | _ => true
  unless marked.isEmpty do
    IO.println ""
    IO.println s!"{marked.length} of {ds.length} are expected to fail and do not gate the \
      exit code."

end StrataGenerators.Test
