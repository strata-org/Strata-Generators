import StrataGenerators.Test.Types

/-!
# The command line of a driver

Each driver shares this module, so a flag means the same thing in each driver.

```
lake test -- [numTrials] [maxSize] [flags]
```

The positional arguments configure the Plausible run. `numTrials` is the number of trials for
each property, and its default is 1000. `maxSize` is the maximum generator size, and its
default is 100.

* `--quick` gives a fast preset for a short cycle of work: 100 trials, maximum size 40, and no
  Tyche pass. Use it to find a defect, and use the defaults to gate a merge. A positional
  argument has higher precedence, so `--quick 500` gives 500 trials and keeps the other parts
  of the preset.
* `--no-tyche` skips the Tyche visualization pass, which runs by default.
* `--tyche-out=PATH` gives the path of the Tyche JSONL output. The default is
  `tyche_output.jsonl`.
* `--tyche-samples=N` gives the number of samples for each Tyche panel. The default is 1000.
* `--smt` enables the `smt` gate. The gate admits the properties whose oracle is a live `cvc5`
  or `z3`. It is off by default, so the suite needs no solver.
* `--only=SUBSTRING` runs only the properties whose name holds `SUBSTRING`. You can give the
  flag more than one time, and a property that matches one of them runs. The report holds no
  other property, and this is what makes work on one new property cheap.
* `--list` prints the registry with the name, the group, the gate and the expectation of each
  property. The driver then stops and runs nothing. Use it to make sure that the harness found
  your property.
* `--known-failure=NAME` marks `NAME` as known to fail for this run. The report hides its
  counterexample, and the property stops gating the exit code. You can give the flag more than
  one time. The permanent form is `knownFailure` at the property, which also carries a reason.
  Use this flag for a short cycle of work, when you want the results of the other properties
  while someone triages a defect. Unlike `--only=`, this flag takes a **whole property name**
  and not a substring. A substring would claim that each property in a group must fail, and the
  report would then give a failure for each property in the group that holds.

There is no `--suite=` flag. A report group *is* a prefix of a name, so `--only="lift:"` selects
the `lift` group exactly.
-/

namespace StrataGenerators.Test

/-- Everything that a driver reads from the command line. It holds the `RunConfig` that each
    property sees, and the options of the driver that no property needs. -/
structure Cli where
  run          : RunConfig
  tycheEnabled : Bool
  tycheOut     : String
  tycheSamples : Nat
  /-- The substrings of a name that filter the registry. An empty list gives no filter. -/
  only         : List String
  /-- The whole names of the properties to mark as known failures, for this run only. -/
  knownFailures : List String
  /-- Print the registry and stop. -/
  listOnly     : Bool
  /-- Whether the command line held `--quick`. A driver can then name the flag that stopped
      the Tyche pass. A report of `--no-tyche` for a `--quick` run makes a reader look for a
      flag that they did not give. -/
  quick        : Bool

/-- The number of trials that `--quick` selects. -/
def quickNumTrials : Nat := 100

/-- The maximum generator size that `--quick` selects. -/
def quickMaxSize : Nat := 40

/-- Parses `args`. For the flags, see the documentation of this module. -/
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
                       (if quick then quickMaxSize else 100)
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

/-- Applies `--only` to the registry. An empty filter keeps each property. -/
def Cli.select (cli : Cli) (ds : List TestDecl) : List TestDecl :=
  ds.filter fun d => cli.only.isEmpty || cli.only.any (contains d.name)

/-- Applies `--known-failure=` to the registry. It replaces the `expect` field of each property
    that the flag names. The match is on the whole name, and the documentation of this module
    gives the reason. -/
def Cli.markKnownFailures (cli : Cli) (ds : List TestDecl) : List TestDecl :=
  ds.map fun d =>
    if cli.knownFailures.contains d.name then
      knownFailure "marked as a known failure on the command line" d
    else d

/-- The `--known-failure=` arguments that name no registered property. A driver refuses to run
    when this list is not empty. Without the check, a name with a spelling mistake does nothing,
    and the run looks as if the mark worked. -/
def Cli.unknownKnownFailures (cli : Cli) (ds : List TestDecl) : List String :=
  cli.knownFailures.filter fun n => !ds.any (fun d => d.name == n)

/-- The registry that a driver runs. It applies `--only` first, and then it applies
    `--known-failure=`. Both drivers and `Driver.setup` call this function, so `--list` shows
    the same expectations that the run uses. -/
def Cli.resolve (cli : Cli) (ds : List TestDecl) : List TestDecl :=
  cli.markKnownFailures (cli.select ds)

/-- Adds spaces to the end of `s` until the length of `s` is `n`. -/
private def pad (s : String) (n : Nat) : String :=
  s ++ "".pushn ' ' (n - min n s.length)

/-- Prints the registry: each registered property, its report group, the gate that holds it
    back, and whether it is expected to fail. The author of a property reads this output to make
    sure that the harness found the file, and no run is necessary. The output also says which
    properties are known to fail, because the registry records that. -/
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
