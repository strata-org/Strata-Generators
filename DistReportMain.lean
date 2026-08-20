import StrataGenerators.DistReport

/-!
# `dist-report` driver

Prints, per property family and per tuning profile, how often the shapes the
suite's properties discriminate on actually appear — see
`StrataGenerators.DistReport` for what each column means and
`StrataGenerators.TuningProfiles` for what each profile is trying to buy.

```bash
lake exe dist-report [samples] [maxSize] [--stmt] [--proc] [--cmd] [--expr]
```

`samples` (default 200) is per profile per family, `maxSize` (default 100) is the
Plausible size the draws cycle through. With no family flag, all four run.

To compare a *property's* verdict across profiles, register it with
`TestDecl.underTunings` instead — see `StrataTests/Stmt.lean`.
-/

def main (args : List String) : IO UInt32 := do
  let flags := args.filter (·.startsWith "--")
  let positional := args.filter (fun a => !a.startsWith "--")
  let samples := (positional[0]? >>= String.toNat?).getD 200
  let maxSize := (positional[1]? >>= String.toNat?).getD 100
  let all := ["stmt", "proc", "cmd", "expr"]
  let asked := all.filter (fun f => flags.contains s!"--{f}")
  let families := if asked.isEmpty then all else asked
  StrataGenerators.DistReport.report samples maxSize families
  return 0
