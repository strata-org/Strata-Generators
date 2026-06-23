# `Strata.DL.Util.List` vs `Batteries.Data.List.Basic` Import Collision

## Status

**Resolved (June 2026).** The `public section` in `Strata.DL.Util.List` has been
removed, making `List.Forall₂` (and most other `List.*` names) module-private.
Files that need these names within Strata use `import all`. The collision with
`Batteries.Data.List.Basic` no longer fires because Strata's `List.Forall₂` is
no longer publicly exported.

`strata-generators` now imports `Batteries.Data.List.Basic` directly in
`HasTypeAGen.lean` to get `List.Forall₂` from Batteries (the same definition).

## The Original Problem

`Strata.DL.Util.List` defined `List.Forall₂` (and ~40 other `List.*` names)
inside a `public section`. `Batteries.Data.List.Basic` also defines
`List.Forall₂` inside an `@[expose] public section`. When both modules were
loaded into the same environment, Lean rejected the import:

```
import Batteries.Data.List.Basic failed, environment already contains
'List.Forall₂.below.casesOn' from Strata.DL.Util.List
```

## How It Was Fixed

The `public section` / `end` wrapper was removed from `Strata.DL.Util.List`.
Since the file uses `module`, all definitions became module-private by default.
Only `dedup`, `dedupTR`, `dedupTR.go`, and `dedup_eq_dedupTR` remain `public`
(required by the `@[csimp]` attribute and dot notation).

Internal Strata files that need the private names use `import all Strata.DL.Util.List`.

## Remaining `List.dedup` Collision

`List.dedup` is still public in Strata (needed for dot notation and `@[csimp]`).
`Mathlib.Data.List.Defs` also defines `List.dedup`. This collision fires if
Mathlib and Strata are both transitively imported in the same file.

In practice this means `HasTypeAGen/Core.lean` (which imports Strata) cannot
import `Basalt.Examples.ArbNat` (which pulls in Mathlib). The local copies of
`Nat.arbitrary`, `Char.arbitrary`, and `String.arbitrary` remain for this reason.

## Current Workaround

`HasTypeAGen/Core.lean` defines local copies of `Nat.arbitrary`,
`Char.arbitrary`, and `String.arbitrary` rather than importing from
`Basalt.Examples.*`, because those modules transitively import Mathlib which
collides with Strata's public `List.dedup`.

## When It Could Recur

The `List.dedup` collision will surface if:
1. A file that imports Strata also transitively imports `Mathlib.Data.List.Defs`
2. A direct Mathlib dependency is added to a file that also imports Strata

The `List.Forall₂` collision is permanently resolved (the name is now
module-private in Strata).
