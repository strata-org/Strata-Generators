import StrataGenerators.Test.Types

/-!
# The command line of a driver

Each driver shares this module, so a flag means the same thing in each driver.

```
lake test -- [numTrials] [maxSize] [flags]
```

The positional arguments configure the run. `numTrials` is the number of the trials for each property, and
its default value is 1000. `maxSize` is the maximum size of a generator, and its default value is 5.

A generator receives `maxSize` directly, as the depth of a term, the level of the nesting of a statement, or
the number of the declarations. The harness raises the size from 0 up to that number over the trials of one
property, so a run tests a small shape first and the largest shape last. The number is small, because each of
those bounds is *structural*. A term of the depth 6 and a program of six declarations are already large
inputs, and the cost of one draw grows faster than the bound does.

* `--quick` gives a fast preset for a short cycle of work: 100 trials, the maximum size 2, and no pass for
  Tyche. Use it to find a defect, and use the default values to gate a merge. A positional argument has a
  higher precedence, so `--quick 500` gives 500 trials and keeps each other part of the preset.
* `--no-tyche` skips the pass that writes the visualizations for Tyche, which runs by default.
* `--tyche-out=PATH` gives the path of the JSONL output for Tyche. The default value is
  `tyche_output.jsonl`.
* `--tyche-samples=N` gives the number of the samples for each panel of Tyche. The default value is 1000.
* `--smt` enables the `smt` gate. That gate admits each property whose oracle is a live `cvc5` or `z3`. It is
  off by default, so the suite needs no solver.
* `--seed=N` gives each property the seed `N`, and reports the seed of each property that fails. The same
  command line then gets the same inputs, so a counterexample comes back. Without the flag, each run starts
  from the operating system. `IO.stdGenRef` gets its seed from `IO.getRandomBytes` at startup, so a failing
  input is gone at the end of the run. `N` also goes to the process-wide generator, which the self-driving
  `IO` properties and the Tyche pass use.

  1 seed serves each property, as `hspec` and `tasty-quickcheck` also do. Two properties of
  1 input type then get the same inputs, so a run with a seed covers less than a run
  without one. Use the flag to get a failure again, not to gate a merge.

  The seed alone does not fix the inputs, because the trial count and the maximum size also
  decide them. A failure therefore prints the whole command line that gives its inputs again.

  A property with its own seed from `@[strata_property (seed := …)]` keeps that seed, with
  its own trial count and maximum size, and ignores the flag and the positional arguments.
  `StrataGenerators.Test.TestDecl.runConfig` tells you why the declaration wins.
* `--only=SUBSTRING` runs only the properties whose name holds `SUBSTRING`. You can give the flag more than
  one time, and a property that matches one of them runs. The report holds no other property, and that is
  what makes work on one new property cheap.
* `--list` prints the registry, with the name, the group, the gate, the seed and the expectation of each
  property. The driver then stops, and it runs nothing. Use it to make sure that the harness found your property.
* `--known-failure=NAME` marks `NAME` as known to fail for this run. The report hides its counterexample, and
  the property stops gating the exit code. You can give the flag more than one time. The permanent form is
  `knownFailure` at the property, which also carries a reason. Use this flag for a short cycle of work, when
  you want the results of the other properties while someone triages a defect. Unlike `--only=`, this flag
  takes a **whole property name**, and not a substring. A substring would claim that each property of a group
  must fail, and the report would then give a failure for each property of the group that holds.

An argument that the driver cannot read is an error, and the driver stops. See `cliErrors`.

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
  /-- Arguments that the driver could not read. A driver stops instead of a run on a value
      that it dropped. For example, a bad `--seed=` gives a run without a seed, and the
      counterexample that the flag must find does not come back. -/
  errors       : List String := []

/-- The number of trials that `--quick` selects. -/
def quickNumTrials : Nat := 100

/-- The maximum size of a generator that `--quick` selects. Two levels of the structure are enough for a shape
    with real content, and a full pass at that size costs seconds. -/
def quickMaxSize : Nat := 2

/-- The flags that take no value. -/
private def switchFlags : List String := ["--quick", "--no-tyche", "--smt", "--list"]

/-- The flags that take a value after `=`, and whether the command line can give the flag more
    than one time. -/
private def valueFlags : List (String × Bool) :=
  [("--seed=", false), ("--tyche-out=", false), ("--tyche-samples=", false),
   ("--only=", true), ("--known-failure=", true)]

/-- The errors in `flags` and `positional`. Each argument that the driver cannot read is an error,
    and not a value that the driver drops. A dropped value gives a run that is different from the
    run that the user asked for, and the report does not show it. For example, `--seed 7` (with a
    space) gives 7 trials without a seed, and the user then expects a repeatable run. -/
private def cliErrors (flags positional : List String) : List String := Id.run do
  let mut errs : List String := []
  for f in flags do
    if switchFlags.contains f then continue
    if valueFlags.any (f.startsWith ·.1) then continue
    match valueFlags.find? (fun (k, _) => f.startsWith (k.dropEnd 1)) with
    | some (k, _) => errs := errs ++ [s!"`{f}`: write `{k}VALUE`, with `=` and no space"]
    | none => errs := errs ++ [s!"`{f}`: unknown flag"]
  for (k, repeatable) in valueFlags do
    let n := (flags.filter (·.startsWith k)).length
    if !repeatable && n > 1 then
      errs := errs ++ [s!"`{k}` occurs {n} times; give it one time"]
  for k in ["--seed=", "--tyche-samples="] do
    for f in flags.filter (·.startsWith k) do
      let v := (f.drop k.length).toString
      if v.toNat?.isNone then
        errs := errs ++ [s!"`{f}`: `{v}` is not a natural number"]
  let names := ["numTrials", "maxSize"]
  for (a, i) in positional.zipIdx do
    match names[i]? with
    | none => errs := errs ++ [s!"`{a}`: too many positional arguments; give at most \
        `numTrials` and `maxSize`"]
    | some name =>
      if a.toNat?.isNone then
        if a.startsWith "-" then
          errs := errs ++ [s!"`{a}`: unknown argument; a flag starts with `--`"]
        else
          errs := errs ++ [s!"`{a}`: `{name}` must be a natural number"]
      else if name == "numTrials" && a.toNat? == some 0 then
        errs := errs ++ [s!"`{a}`: `numTrials` must be at least 1; 0 trials tests nothing"]
  return errs

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
                       (if quick then quickNumTrials else defaultNumTrials)
        maxSize   := (positional[1]? >>= String.toNat?).getD
                       (if quick then quickMaxSize else defaultMaxSize)
        gates     := if flags.contains "--smt" then ["smt"] else []
        seed      := (flagValue "--seed=").bind String.toNat? }
    tycheEnabled := !flags.contains "--no-tyche" && !quick
    tycheOut     := (flagValue "--tyche-out=").getD "tyche_output.jsonl"
    tycheSamples := ((flagValue "--tyche-samples=").bind String.toNat?).getD 1000
    only          := flagValues "--only="
    knownFailures := flagValues "--known-failure="
    listOnly      := flags.contains "--list"
    quick         := quick
    errors        := cliErrors flags positional }

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
    let seed := match d.seed with
      | some p => s!"  [seed {p.seed}, {p.numTrials} trials, max size {p.maxSize}]"
      | none => ""
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
