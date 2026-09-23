# Replacing `SetGen` with Basalt's `SPMF`

Worktree `strata-generators-spmf`, branch `spmf-refactor`. `StrataGenerators/SetGen/` is gone; the
proofs read a generator as an `SPMF` — Basalt's sub-probability mass function — and speak about
`SPMF.support`.

## What had to happen upstream first

`SPMF` is `{μ : α → ℝ≥0∞ // ∑' a, μ a ≤ 1}`, so it drags in Mathlib, and Mathlib drags in Batteries.
Lean refuses to import two modules that declare the same constant, and Strata keeps Mathlib-free copies
of several ecosystem declarations in the root namespace. Importing Strata and Mathlib into one module
therefore failed *before any elaboration*:

```
error: import Strata.Util.ListUtils failed,
  environment already contains 'List.Forall₂.below.casesOn' from Batteries.Data.List.Basic
```

That is why `SetGen` was vendored Mathlib-free in the first place.

Dumping `env.constants` with each constant's defining module from two processes (one importing this
package, one importing `Basalt`) and intersecting on same-name/different-module gave 33 hits. The
auto-generated equation and congruence lemmas (`guard.eq_1`, `Fin.val.hcongr_2`, `List.dedup.eq_1`, …)
are *not* a problem — verified by importing the offending module pairs directly, Lean tolerates those.
Ten real declarations were, all in Strata, and upstream `main` now renames them:

| Before | After | Strata module |
|---|---|---|
| `List.Forall₂` (+ recursors) | `List.Rel₂` | `Strata/Util/ListUtils.lean` |
| `List.Disjoint` (+ its `Disjoint*` API) | `List.Disj` | `Strata/Util/ListUtils.lean` |
| `List.dedup`, `List.dedupTR` | `List.uniq`, `List.uniqTR` | `Strata/Util/ListUtils.lean` |
| `List.foldlIdx` | `List.foldlIdxVal` | `Strata/Util/ListUtils.lean` |
| `List.nodup_dedup` | `List.nodup_uniq` | `Strata/Util/ListUtilsProps.lean` |
| `List.Forall₂.length_eq` | `List.Rel₂.length_eq` | `Strata/Util/ListUtilsProps.lean` |
| `Reflexive`, `Transitive` | `IsReflexive`, `IsTransitive` | `Strata/Util/Relations.lean` |
| `Dense` | `IsDense` | `Strata/Util/RelationsProps.lean` |
| `String.IsSuffix` | `String.IsSuffixOf` | `Strata/DL/Util/StringGen.lean` |
| `List.reverse_injective` | `List.reverse_injective'` | `Strata/DL/Util/StringGen.lean` |

Each stays in its original namespace, so generalized field notation (`l.uniq`, `h.symm`,
`s.IsSuffixOf t`) is unaffected. The renames landed upstream in `e318079876`, which is the rev this
package pins, so `lakefile.toml` asks for `main` again and no fork is involved. (While the work was
still a fork, one thing was worth knowing: **editing `lakefile.toml` alone is not enough** — `lake
build` re-checks-out the manifest's rev and silently discards the working tree, so `lake-manifest.json`
has to move too.)

Two Mathlib-arrival consequences inside this package:

* `ProgramTuning.ProgIdx.alias` had to become `«alias»`: Mathlib makes `alias` a command keyword.
* `List.Nodup.map` now resolves to Mathlib's, which asks for `Function.Injective f` rather than the
  contrapositive; `oldVars_keys_nodup` was rewritten accordingly.

## The `SetGen` → upstream mapping

| Vendored | Replacement |
|---|---|
| `SetGen.Set`, its monad and `LawfulMonad` instances | Mathlib `Set` |
| `Gen Set`, `CCPO`, `MonoBind`, `pick_mem_iff`, `bot_bind` | `Basalt/SPMF/Core.lean` |
| all of `SetGen/Support.lean` | `Basalt/SPMF/Support.lean` |
| `SetGen.IsSoundAndComplete` (a class) | `IsSoundAndComplete` in `Basalt/Laws.lean` (a `def`) |
| `SetGen.support_frequency_reweight`, `…_congr_weights` | the `SPMF.` versions |
| `DatatypeGenProofs.mem_support_chooseNat_iff` | `SPMF.mem_support_chooseNat_iff` |

What stayed, in `StrataGenerators/GenSupport.lean`: `SPMF.mem_support_bot_iff`,
`weightedOptionGen` + its support lemma, `fix_congr`/`wellFounded_fix_congr`/`brecOn_congr`, and
`wellFounded_fix_rel` (new). It also `export`s the support API at the root, so the ~1500 existing
unqualified call sites need no `open` — an `open SPMF` would bring `SPMF.pure` into scope and make
every bare `pure` in a generator ambiguous with `Pure.pure`.

## Shape changes to expect when reading the diff

* `SetGen.support` was the identity, so `a ∈ g` and `a ∈ SetGen.support g` were interchangeable. Every
  raw membership now goes through `SPMF.support`, and the simp sets that mixed raw-membership lemmas
  with `mem_support_iff` (~120 sites) collapse onto the `SPMF.mem_support_*_iff` family.
* `support (pure a)` was definitionally an equation, so `rcases … rfl` worked on it. It no longer does:
  `mem_support_pure_iff` had to be added to 152 simp lists.
* `SetGen.mem_support_choose_iff` gave `lo ≤ a.down.val ∧ a.down.val ≤ hi`;
  `SPMF.mem_support_choose_iff` gives `True` (the bound already lives in the `ULift` subtype), so the
  witnesses that supplied that conjunction became `trivial`.
* `ListMap` is a semireducible `def`, so a `ListMap α β`-typed value does not match a
  `Set (List (α × β))` syntactically and the support lemmas do not fire. Those sites add `ListMap` to
  the simp set.
* Two proofs diverged at `whnf` because a `_` for a `LMonoTy` left a metavariable that let the unifier
  unfold `opsOfType`/`fvarsOfType` — at `SetGen` that was cheap, at `SPMF` it is not. Passing `τ`
  explicitly fixes both (`HasTypeAGenOpsConsistent`).

## Tuning: θ-invariance is a support equation now

`SetGen/Tuning.lean` proved `genFoo.tuned θ = genFoo` as an equality of *generators*, which holds only
because `Set` cannot see a weight. At `SPMF` a weight is part of the mass, so that statement is false
and the guarantee is an equality of **supports**: `Tuning.weight` clamps every weight to 1 or more, so
no branch becomes unreachable.

`StrataGenerators/TuningSupport.lean` is the new machinery: support congruences for `bind`, `map`,
`dite`, `ite`, `pick`, `oneOf`, `optionGen` and `mapM`; `support_frequency_congr_branches` (the site
lemma, weakened to branches that agree only in support, which is what a *recursive* generator needs);
`support_fix_congr_of_pointwise` (fixpoint induction, for `partial_fixpoint`); and a `support_congr`
tactic that walks a body down to its sites.

Reproved at support level: `genTree` (×2, `partial_fixpoint`), `genOptNat`, `genPrecondition`,
`genPreconditionW`, `genCmd`, `genCmds`, `genLMonoTy` (`Nat.brecOn`), and the whole `genStmt` mutual
block with its four corollaries (`WellFounded.fix`, via `wellFounded_fix_rel`).

**One gap: `genLExprBase_tuned_support_eq` is `sorry`.** It is the only `sorry` in the package. The
reason is in the comment at the theorem: `genLExprBase` matches on the depth *and* the target type
together and the equation compiler moves `bctx`/`τ` into `Nat.brecOn`'s motive, so `delta` leaves the
tuned side as `Nat.brecOn.go … (fun x f bctx τ => match x, τ with …)`, `dsimp only` reduces neither the
`brecOn.go` nor the matcher, and `split` splits only the shipping side. Closing it wants a support-level
congruence for `Nat.brecOn` — the analogue of `SPMF.support_wellFounded_fix_congr` — which means
relating two `Nat.below` bundles.

## Verification

`lake build` is green. `lake test -- --quick` fails the same 19 properties as `main` does (compared
run-for-run on a second run of each; the suite is not seed-deterministic, so a single run apart shows
spurious differences — `mono: output of monomorphization typechecks` differed on the first pair and
agreed on the second).

After merging `main` (Strata `e318079876`, which carries the renames above, and Basalt `c4b7ed20`) the
build is still green — 2047 jobs, one `sorry`, the one named above. None of the Basalt work since
`a9daf35525` touches what this package reads: `SPMF/Core.lean`, `SPMF/Support.lean`, `Laws.lean`'s
`IsSoundAndComplete` and `Tuning/Attr.lean` are unchanged or only extended. The churn there is in the
cost and mass-bound machinery (`SPMF/Cost.lean` → `SPMF/CostBound.lean`, the new `SPMF/Walk.lean`) and
in the executable interpretations (`IO.lean` drops `UniformIO` and its clamp for the new `Random.lean`
`stdChoose`; `Sized.lean` is new), and this package imports none of it.
