# Why `strata-generators` Cannot Import `Strata.DL.Lambda.LExprEval`

## The Problem

`strata-generators` depends on both Strata and Basalt. Basalt depends on
Mathlib/Batteries. When we try to import `Strata.DL.Lambda.LExprEval` in
the same file as Basalt-based code (e.g., `HasTypeAGen`), Lean rejects the
build with errors like:

```
import Strata.DL.Util.List failed, environment already contains
'List.nodup_dedup' from Mathlib.Data.List.Dedup
```

The collision is between `List.*` definitions in `Strata.DL.Util.List`
(e.g., `List.dedup`, `List.nodup_dedup`, `List.Forall₂`) and identically-named
definitions in Batteries/Mathlib.

## Why It Happens

`Strata.DL.Util.List` defines ~40 `List.*` names in a `public section`.
These propagate to external consumers through a chain of `public import`s:

```
Strata.DL.Util.List     (defines List.dedup, List.nodup_dedup, etc.)
        ↓ public import
LTyUnify.lean           (public import Strata.DL.Util.List)
        ↓ public import
Factory.lean            (public import Strata.DL.Lambda.LTyUnify)
        ↓ public import
LState.lean             (public import Strata.DL.Lambda.Factory)
        ↓ public import
LExprEval.lean          (public import Strata.DL.Lambda.LState)
        ↓ import (from strata-generators)
TycheMain.lean          ← collision with Batteries' List.*
```

## Why We Can't Fix It With Import Changes

Strata uses a `module` system where:

- `public import Foo` = access Foo's **public** definitions + re-export them
- `import all Foo` = access Foo's **module-private** definitions only
- `import Foo` = no-op for `module` files (gives nothing)

There is **no** "access public definitions without re-exporting" option.
`Factory.lean` needs `public import LTyUnify` to access public definitions
like `Subst` and `Constraints.unify`. This unavoidably re-exports everything
`LTyUnify` publicly imports — including `List.dedup` from `Strata.DL.Util.List`.

## Why Namespacing Doesn't Work

We tried wrapping `Strata.DL.Util.List`'s `namespace List` block inside
`namespace Strata` (making definitions like `Strata.List.dedup`). This breaks
dot notation: `l.dedup` where `l : List α` resolves against `_root_.List.dedup`,
not `Strata.List.dedup`. Lean's dot notation always resolves against the type's
own root namespace, regardless of `open` statements or current namespace context.

## The Strata Design Principle (Aspirational)

PR [#523](https://github.com/strata-org/Strata/pull/523) states:

> Namespace extensions kept private. Definitions that extend Lean or library
> namespaces (e.g. `BitVec.width`, `List.dedup`) stay private by default so
> Strata does not conflict with Batteries or Mathlib. Consumers that need
> these use `import all` to opt in explicitly.

This principle is **not currently enforced** for `Strata.DL.Util.List`. The
file uses `public section`, making all `List.*` definitions public. And
internal consumers use `public import` which re-exports them. Making the
definitions module-private (non-public section) would satisfy the principle
but breaks dot notation (`l.dedup`) which internal Strata code relies on.

## Toolchain Mismatch (Secondary Issue)

Even if the collision were resolved, `LExprEval.lean` uses `grind` in two
termination proofs that fail on Lean 4.30.0-rc2 (used by Basalt), while
Strata targets 4.29.1. The fix is `grind` → `simp_all` at lines 107 and 140.
`Strata.DL.Util.Maps` also has a `grind` failure at line 573.

## Current Workaround

`TycheMain.lean` defines a minimal CBV evaluator for closed terms (no free
variables, no operators) that covers beta reduction, if-then-else, and
equality. This is functionally equivalent to `LExpr.eval` for our use case
but doesn't test the actual Strata infrastructure.

## Possible Long-Term Solutions

1. **Add Batteries as a Strata dependency** and delete the redundant `List.*`
   definitions from `Strata.DL.Util.List`. Cleanest fix, but conflicts with
   Strata's design goal to minimize dependencies.

2. **New module system feature**: A hypothetical `import public Foo` that
   gives access to public definitions without re-exporting. Doesn't exist today.

3. **Two-binary approach**: Generate terms with `tyche-viz` (uses Basalt),
   serialize them as a `.lean` file using `repr`, then import that file in a
   separate `EvalTest.lean` that only imports Strata (no Basalt). Tests the
   real `LExpr.eval` but requires a two-step build pipeline.

4. **Make `List.*` definitions module-private in Strata** and rewrite all
   internal usages to avoid dot notation (use explicit `List.dedup l` via
   `import all`). Large refactor across Strata.
