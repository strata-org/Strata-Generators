/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import Basalt.SPMF
import Basalt.Laws
import Basalt.Tactics
import Basalt.Combinators

open Lean.Order RandomChoice

/-!
# What this package adds to Basalt's `SPMF` support API

The proofs in this package read a generator as an `SPMF` — a sub-probability mass function — and
speak about `SPMF.support`, the set of values whose mass is not zero. Basalt owns that reading and
almost all of the lemmas about it: `Basalt/SPMF/Support.lean` has the `mem_support_*_iff` family for
every combinator this package draws from, `Basalt/Laws.lean` has `IsSoundAndComplete`, and
`Basalt/Tactics.lean` has `support_simp`, the packaged `simp only` set for support inversion.

This file holds the three things Basalt does not.

1. `SPMF.mem_support_bot_iff`, so that a `simp` set can discharge the branch of a generator that
   produces nothing.
2. `weightedOptionGen`, an `optionGen` whose `some`/`none` split is a two-branch `frequency` rather
   than a `RandomChoice.coin`, so that `@[tunable]` can see it.
3. `fix_congr`, `wellFounded_fix_congr` and `brecOn_congr`, which say that a fixpoint depends on its
   functional alone. They lift a per-site fact to a whole recursive generator, and they are not
   specific to any interpretation.

## History

This package used to carry a whole vendored interpretation, `SetGen`, which read a generator as a
plain `Set` — its support, with no probability. It existed because `SPMF` is built on Mathlib
(`ENNReal`, `tsum`) and, until Strata stopped declaring `List.Forall₂`, `List.Disjoint`, `List.dedup`
and friends in the root namespace, no module could import Strata and Mathlib at once. With that fixed
upstream, `SetGen` is gone and this package reasons at `SPMF` directly.

One consequence is worth knowing when reading old proofs. `SetGen.support` was the identity function,
so `a ∈ g` and `a ∈ SetGen.support g` were interchangeable, and a weight was invisible: a `frequency`
with positive weights was *equal* to the uniform `oneOf` over its branches. Neither holds at `SPMF`.
Membership must go through `SPMF.support`, and a reweighting preserves the support but not the
generator, so the tuning results in `StrataGenerators.TuningPrototypes` are stated as equalities of
supports.
-/

namespace SPMF

/-- The generator that produces nothing has an empty support. This is the `⊥` of the `CCPO`, which is
    what a `partial_fixpoint` generator denotes on a branch it cannot leave, and what `Gen`'s
    `Inhabited` instance gives. -/
@[simp]
theorem mem_support_bot_iff {α : Type u} (a : α) : a ∈ (default : SPMF α).support ↔ False := by
  simp only [SPMF.mem_support_iff, default, Bot.bot, ne_eq, iff_false, Decidable.not_not]
  rfl

/-- `mem_support_listOf` under its `Iff` name, for symmetry with the rest of the family. A list is in
    the support of `listOf g` exactly when each of its elements is in the support of `g`; `listOf`
    puts no bound on the length. -/
theorem mem_support_listOf_iff {g : SPMF α} {xs : List α} :
    xs ∈ (listOf g).support ↔ ∀ x ∈ xs, x ∈ g.support :=
  mem_support_listOf

/-- The `mpr` direction of `mem_support_listOf_iff`, named for use as a term. -/
theorem mem_support_listOf_of_forall {g : SPMF α} {xs : List α}
    (hxs : ∀ x ∈ xs, x ∈ g.support) : xs ∈ (listOf g).support :=
  mem_support_listOf_iff.mpr hxs

end SPMF

/-! ## The support API, unqualified

The proofs in this package name these lemmas without a prefix, and they long predate the move to
`SPMF`. Re-export them at the root so that no `open` is needed at each use site — an `open SPMF`
would also bring `SPMF.pure` into scope and make every bare `pure` in a generator ambiguous with
`Pure.pure`.

`SPMF.mem_support_iff` is deliberately *not* re-exported. It unfolds `a ∈ g.support` to `g a ≠ 0`,
which is the wrong direction for every proof here: these proofs invert a generator's support down to
its branches, and want the `mem_support_*_iff` family instead. -/

export SPMF (support support_bind mem_support_bind_iff support_pure mem_support_pure_iff support_map
  mem_support_map_iff mem_support_dite_iff mem_support_ite_iff support_choose mem_support_choose_iff
  mem_support_chooseNat_iff mem_support_chooseInt_iff support_pick mem_support_pick_iff support_oneOf
  mem_support_oneOf_iff support_frequency mem_support_frequency_iff support_elements
  mem_support_elements_iff support_vectorOf mem_support_vectorOf_iff support_listOfMaxLength
  mem_support_listOfMaxLength_iff support_listOf mem_support_listOf mem_support_listOf_iff
  mem_support_listOf_of_forall support_nonEmptyListOf mem_support_nonEmptylistOf support_coin
  mem_support_coin_iff support_biasedOptionGen mem_support_biasedOptionGen_iff support_optionGen
  mem_support_optionGen_iff mem_support_bot_iff mem_support_csup bind_congr_support bot_bind
  support_frequency_reweight support_frequency_congr_weights)

namespace StrataGenerators

/-- Like `Basalt.Combinators.biasedOptionGen`, but a `frequency` over two `Nat` weights decides the
`some`/`none` split. `biasedOptionGen` uses a rational `RandomChoice.coin`, and `@[tunable]` rewrites
only a `frequency`, so the attribute cannot expose that split. Reach for this combinator when the
*presence* of an optional clause is the knob you want; a function precondition is one such clause,
and `PrecondElim` is the pass that acts on it.

A tuning can address the split only if the tagged generator writes the split out in its own body:
`@[tunable]` collects the `frequency` calls in that body, and inlines only that declaration's own
compiler-generated auxiliaries. This combinator takes its weights as variables rather than as
literals, so the attribute rejects the combinator itself. `TuningPrototypes.genPreconditionW` writes
the two-branch `frequency` inline and then records by `rfl` that the result is this combinator at
weights 1 to 1, so the support lemma below still describes it.

Both weights must be positive for the support to match `optionGen`'s. `Tuning.weight` clamps every
weight to 1 or more, so a tuned generator that wraps this stays total for every runtime `θ`.

The `some` branch uses an explicit `bind`, as `biasedOptionGen` does, because `Lean.Order` has no
monotonicity lemma for `<$>`.

This combinator belongs in `Basalt.Combinators`, next to `biasedOptionGen`. It is here to avoid a
change to Basalt. -/
def weightedOptionGen [Gen G] (wSome wNone : Nat) (g : G α)
    (h : 0 < wSome + wNone := by omega) : G (Option α) :=
  frequency [
    (wSome, fun _ => do let x ← g; pure (some x)),
    (wNone, fun _ => pure none)
  ] (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)

/-- With both weights positive, `weightedOptionGen` reaches `none`, and it reaches `some a` exactly
when `g` reaches `a`. A weight therefore decides how often the generator returns `none`, and never
which values it can return. -/
@[simp]
theorem mem_support_weightedOptionGen_iff {wSome wNone : Nat} {g : SPMF α} {o : Option α}
    (hs : 0 < wSome) (hn : 0 < wNone) (h : 0 < wSome + wNone) :
    o ∈ (weightedOptionGen wSome wNone g h).support ↔
      o = none ∨ ∃ a ∈ g.support, o = some a := by
  unfold weightedOptionGen
  rw [SPMF.mem_support_frequency_iff]
  constructor
  · rintro ⟨w, gen, hmem, _, ha⟩
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at ha
      obtain ⟨a, ha', rfl⟩ := ha
      exact Or.inr ⟨a, ha', rfl⟩
    · rcases List.mem_cons.mp hmem' with heq | hnil
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        simp only [SPMF.mem_support_pure_iff] at ha
        exact Or.inl ha
      · simp at hnil
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · refine ⟨wNone, _, List.mem_cons_of_mem _ List.mem_cons_self, hn, ?_⟩
      simp only [SPMF.mem_support_pure_iff]
    · refine ⟨wSome, _, List.mem_cons_self, hs, ?_⟩
      simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff]
      exact ⟨a, ha, rfl⟩

/-! ## Fixpoints depend on their functional alone

Each lemma below turns a per-site fact — typically a reweighting of one `frequency` — into a fact
about a whole recursive generator. `@[tunable]` binds `θ` *outside* the fixpoint and re-proves
monotonicity for the rewritten functional, so `genFoo.tuned θ` and `genFoo` are one fixpoint over two
functionals that differ only inside their `frequency` sites. None of these lemmas is specific to an
interpretation; they belong upstream in Basalt. -/

/-- Two `Lean.Order.fix` terms over equal functionals are equal. The monotonicity proof is a `Prop`,
so proof irrelevance makes it immaterial. This is the lemma a `partial_fixpoint` generator needs. -/
theorem fix_congr {α : Sort u} [Lean.Order.CCPO α] {f g : α → α}
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) (h : f = g) :
    Lean.Order.fix f hf = Lean.Order.fix g hg := by
  subst h; rfl

/-- Two `WellFounded.fix` terms over equal functionals are equal. The accessibility argument is a
`Prop`, so only the functional matters.

The equation compiler uses `WellFounded.fix` for a generator with `termination_by`, and the members
of a `mutual` block share one such fix over a `PSum` of their argument tuples. This lemma is
therefore what lifts a per-site fact to a whole block. -/
theorem wellFounded_fix_congr {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
    (hwf : WellFounded r) {F F' : ∀ x, (∀ y, r y x → C y) → C x} (h : F = F') :
    WellFounded.fix hwf F = WellFounded.fix hwf F' := by
  subst h; rfl

/-- **A relation that a well-founded recursion preserves.** `wellFounded_fix_congr` needs the two step
functions to be *equal*; when they are not — a tuned generator differs from its untuned original in
its `frequency` weights — this is the tool that replaces it. Give a relation `R` on results, show that
the two step functions map `R`-related recursive bundles to `R`-related results, and conclude that the
two fixpoints are `R`-related everywhere.

`R` is indexed by the argument so that a `mutual` block, whose shared auxiliary recurses on a `PSum`
and whose result type is a `PSum.casesOn`, can state one relation per member. -/
theorem wellFounded_fix_rel {ι : Sort u} {r : ι → ι → Prop} (hwf : WellFounded r) {C : ι → Sort v}
    {F F' : ∀ x, (∀ y, r y x → C y) → C x} (R : ∀ x, C x → C x → Prop)
    (h : ∀ x (g g' : ∀ y, r y x → C y), (∀ y (hy : r y x), R y (g y hy) (g' y hy)) →
      R x (F x g) (F' x g')) :
    ∀ x, R x (WellFounded.fix hwf F x) (WellFounded.fix hwf F' x) := by
  intro x
  induction x using hwf.induction with
  | _ x ih =>
    rw [WellFounded.fix_eq, WellFounded.fix_eq]
    exact h x _ _ (fun y hy => ih y hy)

/-- Two `Nat.brecOn` terms over equal step functions are equal. The recursive results arrive in a
`Nat.below` bundle, which is one bound variable on both sides, so equality of the step functions is
enough.

The equation compiler uses `Nat.brecOn` for a generator that recurses structurally on a `Nat`, as
`genLMonoTy` and `genLExprBase` do. -/
theorem brecOn_congr {motive : Nat → Sort u}
    {F F' : (n : Nat) → @Nat.below motive n → motive n} (h : F = F') (n : Nat) :
    @Nat.brecOn motive n F = @Nat.brecOn motive n F' := by
  subst h; rfl

end StrataGenerators
