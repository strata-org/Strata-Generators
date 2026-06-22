# `Strata.DL.Util.List` vs `Batteries.Data.List.Basic` Import Collision

## Status

**Latent (not currently triggered).** As of June 2026, the collision does not
fire in practice because the build graph no longer connects the two modules.
However, it is NOT fixed upstream — adding any transitive import path to
`Batteries.Data.List.Basic` in a file that also imports Strata will reproduce it.

## The Problem

`Strata.DL.Util.List` defines `List.Forall₂` (and ~40 other `List.*` names)
inside a `public section`. `Batteries.Data.List.Basic` also defines
`List.Forall₂` inside an `@[expose] public section`. When both modules are
loaded into the same environment, Lean rejects the import:

```
import Batteries.Data.List.Basic failed, environment already contains
'List.Forall₂.below.casesOn' from Strata.DL.Util.List
```

## Why It No Longer Fires

The collision requires `Batteries.Data.List.Basic` to be transitively imported
alongside a Strata module. The import chain that used to trigger it was:

```
Basalt (umbrella)
  → Basalt.Basic
    → Basalt.SPMF
      → Basalt.SPMF.Core
        → Mathlib.Topology.Instances.ENNReal.Lemmas
          → ... (deep Mathlib chain)
            → Batteries.Data.List.Basic   ← collision source
```

**Previously** (Basalt `ernest/combinators` branch, Lean 4.30.0-rc2):
`strata-generators` depended on the Basalt umbrella module, which pulled in
`SPMF.Core` → Mathlib → Batteries transitively.

**Now** (Basalt `lean-4.29` branch, Lean 4.29.0): `strata-generators` imports
only `Basalt.Gen`, `Basalt.IO`, and `Basalt.Combinators`. These modules depend
only on `Basalt.RandomChoice` — they have zero transitive dependency on Mathlib
or Batteries. So `Batteries.Data.List.Basic` never enters the environment.

The collision is unrelated to:
- The Lean toolchain version (4.29 vs 4.30)
- Batteries adopting the `module` system (that happened at Lean 4.25 but
  `List.Forall₂` remains in an `@[expose] public section` so it is still
  publicly exported)

## How Strata Exports `List.Forall₂`

`Strata.DL.Util.List` is a `module` file with a `public section` containing
`namespace List` and the `Forall₂` inductive. The export chain is:

```
Strata.DL.Util.List     (defines List.Forall₂ in public section)
        ↓ public import
LTyUnify.lean           (public import Strata.DL.Util.List)
        ↓ public import
Factory.lean            (public import Strata.DL.Lambda.LTyUnify)
        ↓ public import
LState.lean             (public import Strata.DL.Lambda.Factory)
        ↓ public import
LExprEval.lean          (public import Strata.DL.Lambda.LState)
```

Any file that imports along this chain gets `List.Forall₂` from Strata in its
environment.

## Reproducing the Collision

Add `import Batteries.Data.List.Basic` to any file that also transitively
imports `Strata.DL.Util.List`:

```lean
import Strata.DL.Lambda.LTyUnify
import Batteries.Data.List.Basic  -- ERROR: List.Forall₂.below.casesOn collision
```

## When It Could Recur

The collision will resurface if any of the following happens:
1. A new Basalt import is added that transitively depends on Mathlib/Batteries
   (e.g., importing `Basalt.SPMF` or `Basalt.Examples.ArbChar`)
2. A direct Mathlib dependency is added to `strata-generators`
3. Any other package that transitively imports `Batteries.Data.List.Basic` is
   added as a dependency

## Possible Long-Term Solutions

1. **Add Batteries as a Strata dependency** and delete the redundant `List.*`
   definitions from `Strata.DL.Util.List`. Cleanest fix, but conflicts with
   Strata's design goal to minimize dependencies.

2. **Make `List.*` definitions module-private in Strata** and rewrite all
   internal usages to avoid dot notation (use explicit `List.dedup l` via
   `import all`). Large refactor across Strata.

3. **New module system feature**: A hypothetical `import public Foo` that
   gives access to public definitions without re-exporting. Doesn't exist today.

## Toolchain Mismatch (Resolved)

Previously there was a secondary issue: `LExprEval.lean` used `grind` in
termination proofs that broke under Lean 4.30.0-rc2 (which had `grind` breaking
changes). This is now moot — all packages are on Lean 4.29.x where `grind`
works as expected.
