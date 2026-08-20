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
* `--only=SUBSTRING` — run only the properties whose name contains `SUBSTRING`.
  Repeatable; a property matching any of them runs. The rest are not reported at
  all, which is what makes iterating on one new property cheap.
* `--list` — print the registry (name, group, gate) and exit without running anything.
  The answer to "did my property get picked up?".

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
  /-- Print the registry and exit. -/
  listOnly     : Bool
  /-- Whether `--quick` was passed, so a driver can name the flag that actually
      held the Tyche pass off (reporting `--no-tyche` for a `--quick` run sends the
      reader looking for a flag they did not pass). -/
  quick        : Bool

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
  { run :=
      { numTrials := (positional[0]? >>= String.toNat?).getD
                       (if quick then quickNumTrials else 1000)
        maxSize   := (positional[1]? >>= String.toNat?).getD
                       (if quick then quickMaxSize else 100)
        gates     := if flags.contains "--smt" then ["smt"] else [] }
    tycheEnabled := !flags.contains "--no-tyche" && !quick
    tycheOut     := (flagValue "--tyche-out=").getD "tyche_output.jsonl"
    tycheSamples := ((flagValue "--tyche-samples=").bind String.toNat?).getD 1000
    only         := flagValues "--only="
    listOnly     := flags.contains "--list"
    quick        := quick }

/-- Whether `needle` occurs in `hay`. -/
private def contains (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

/-- Apply `--only` to the registry. An empty filter keeps everything. -/
def Cli.select (cli : Cli) (ds : List TestDecl) : List TestDecl :=
  ds.filter fun d => cli.only.isEmpty || cli.only.any (contains d.name)

private def pad (s : String) (n : Nat) : String :=
  s ++ "".pushn ' ' (n - min n s.length)

/-- Print the registry: what is registered, which group it reports under, and whether
    a gate holds it back. This is how a property author confirms their file was picked
    up, without waiting for a run. -/
def listRegistry (ds : List TestDecl) : IO Unit := do
  IO.println s!"{ds.length} propert{if ds.length == 1 then "y" else "ies"} registered"
  for d in ds do
    let gate := match d.gate with | some g => s!"  [--{g}]" | none => ""
    IO.println s!"  {pad d.group 12} {d.name}{gate}"

end StrataGenerators.Test
