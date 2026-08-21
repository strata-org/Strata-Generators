import StrataGenerators.DistReport

/-!
# `dist-report` driver

Prints how often the shapes that the suite's properties discriminate on appear, per
property family and per tuning profile. `StrataGenerators.DistReport` says what each
column means, and `StrataGenerators.TuningProfiles` says what each profile tries to buy.

```bash
lake exe dist-report [samples] [maxSize] [--stmt] [--proc] [--cmd] [--expr] [--prog]
```

`samples` (default 200) is per profile per family, `maxSize` (default 100) is the
Plausible size the draws cycle through. With no family flag, all five run.

To compare a *property's* verdict across profiles, register it with
`TestDecl.underTunings` instead. `StrataTests/Stmt.lean` shows how.
-/

def main (args : List String) : IO UInt32 := do
  let flags := args.filter (·.startsWith "--")
  let positional := args.filter (fun a => !a.startsWith "--")
  let samples := (positional[0]? >>= String.toNat?).getD 200
  let maxSize := (positional[1]? >>= String.toNat?).getD 100
  let all := ["stmt", "proc", "cmd", "expr", "prog"]
  -- An unrecognised flag is an error rather than a no-op. If the driver ignores one, the output reads
  -- as though that family was measured when nothing was. A `--props` flag stayed documented but
  -- unbuilt for exactly that reason.
  let unknown := flags.filter (fun f => !all.any (fun n => f == s!"--{n}"))
  unless unknown.isEmpty do
    IO.eprintln s!"dist-report: unknown flag(s) {" ".intercalate unknown}; \
      expected any of {" ".intercalate (all.map (s!"--{·}"))}"
    return 1
  let asked := all.filter (fun f => flags.contains s!"--{f}")
  let families := if asked.isEmpty then all else asked
  StrataGenerators.DistReport.report samples maxSize families
  return 0
