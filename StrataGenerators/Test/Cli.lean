import StrataGenerators.Test.Types

/-!
# The driver command line

Shared by every driver, so the flags mean the same thing whichever one is run.

```
lake test -- [numTrials] [maxSize] [flags]
```

Positional arguments configure the Plausible run (`numTrials` = trials per
property, default 1000; `maxSize` = maximum generator size, default 100).

* `--quick` — a fast preset for a short cycle of work: 100 trials, maximum size
  40, and no Tyche pass. Use it to find a defect and the defaults to gate a merge.
  A positional argument has higher precedence, so `--quick 500` gives 500 trials
  and keeps the rest of the preset.
* `--no-tyche` — skip the Tyche visualization pass (on by default).
* `--tyche-out=PATH` — Tyche JSONL output path (default `tyche_output.jsonl`).
* `--tyche-samples=N` — samples per Tyche panel (default 1000).
* `--smt` — enable the `smt` gate, admitting the properties whose oracle is a live
  `cvc5`/`z3`. Off by default, so the suite needs no solver.
* `--seed=N` — give each property the seed `N`, and report the seed of each property that
  fails. The same command line then gets the same inputs, so a counterexample comes back.
  Without the flag, each run starts from the operating system. `IO.stdGenRef` gets its seed
  from `IO.getRandomBytes` at startup, so a failing input is gone at the end of the run.
  `N` also goes to the process-wide generator, which the self-driving `IO` properties and
  the Tyche pass use.

  1 seed serves each property, as `hspec` and `tasty-quickcheck` also do. Two properties of
  1 input type then get the same inputs, so a run with a seed covers less than a run
  without one. Use the flag to get a failure again, not to gate a merge.

  A property with its own seed from `@[strata_property (seed := …)]` keeps that seed and
  ignores the flag. `StrataGenerators.Test.TestDecl.effectiveSeed` tells you why the
  declaration wins.
* `--only=SUBSTRING` — run only the properties whose name contains `SUBSTRING`.
  Repeatable; a property matching any of them runs. The rest are not reported at
  all, which is what makes iterating on one new property cheap.
* `--list` — print the registry (name, group, gate, seed, expectation) and exit without
  running anything. The answer to "did my property get picked up?".
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
  /-- Arguments that the driver could not read. A driver stops instead of a run on a value
      that it dropped. A bad `--seed=` gives a run without a seed, and the header still shows
      a seed. The counterexample that the flag must find does not come back. -/
  errors       : List String := []

/-- The number of trials `--quick` selects. -/
def quickNumTrials : Nat := 100

/-- The maximum generator size `--quick` selects. -/
def quickMaxSize : Nat := 40

/-- Parse `args`. See the module doc for the flags. -/
def parseCli (args : List String) : Cli :=
  let flags := args.filter (·.startsWith "--")
  let positional := args.filter (fun a => !a.startsWith "--")
  let flagValue (key : String) : Option String :=
    (flags.find? (·.startsWith key)).map (·.drop key.length |>.toString)
  let flagValues (key : String) : List String :=
    (flags.filter (·.startsWith key)).map (·.drop key.length |>.toString)
  let quick := flags.contains "--quick"
  let seedArg := flagValue "--seed="
  let seed := seedArg.bind String.toNat?
  { run :=
      { numTrials := (positional[0]? >>= String.toNat?).getD
                       (if quick then quickNumTrials else 1000)
        maxSize   := (positional[1]? >>= String.toNat?).getD
                       (if quick then quickMaxSize else 100)
        gates     := if flags.contains "--smt" then ["smt"] else []
        seed      := seed }
    tycheEnabled := !flags.contains "--no-tyche" && !quick
    tycheOut     := (flagValue "--tyche-out=").getD "tyche_output.jsonl"
    tycheSamples := ((flagValue "--tyche-samples=").bind String.toNat?).getD 1000
    only          := flagValues "--only="
    knownFailures := flagValues "--known-failure="
    listOnly      := flags.contains "--list"
    quick         := quick
    errors        := match seedArg, seed with
                     | some a, none => [s!"--seed={a}: not a natural number"]
                     | _, _ => [] }

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
    let seed := match d.seed with | some s => s!"  [seed {s}]" | none => ""
    let expect := match d.expect with
      | .mustHold => ""
      | .knownFailure r => s!"\n{pad "" 15}known failure: {r}"
    IO.println s!"  {pad d.group 12} {d.name}{gate}{seed}{expect}"
  let marked := ds.filter fun d => match d.expect with | .mustHold => false | _ => true
  unless marked.isEmpty do
    IO.println ""
    IO.println s!"{marked.length} of {ds.length} are expected to fail and do not gate the \
      exit code."

end StrataGenerators.Test
