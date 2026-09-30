/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import StrataGenerators.BasaltCompat
import Basalt.Laws
import Basalt.Tactic.Support
import Basalt.Combinators

open Lean.Order RandomChoice

/-!
# What this package adds to Basalt's `SPMF` support API

The proofs in this package read a generator as an `SPMF` — a sub-probability mass function — and
speak about `SPMF.support`, the set of values whose mass is not zero. Basalt owns that reading:
`Basalt/SPMF/Support.lean` has the set-level `support_*` equalities and the monadic
`mem_support_*_iff` lemmas, `Basalt/Laws.lean` has `IsSoundAndComplete`, and
`Basalt/Tactic/Support.lean` has `support_simp`, the packaged `simp only` set for support inversion.

This file holds four things Basalt does not.

1. `SPMF.mem_support_bot_iff`, so that a `simp` set can discharge the branch of a generator that
   produces nothing.
2. The `mem_support_*_iff` family for the **choice** combinators — `oneOf`, `frequency`, `pick`,
   `elements`, `chooseNat`, `chooseInt`, `coin`, `biasedOptionGen`, `optionGen` — and the `support_*`
   equalities Basalt does not state for them. See `StrataGenerators.BasaltCompat`.
3. `weightedOptionGen`, an `optionGen` whose `some`/`none` split is a two-branch `frequency` rather
   than a `RandomChoice.coin`, so that `@[tunable]` can see it.
4. `wellFounded_fix_rel`, which lifts a relation between two step functions to a relation between
   their fixpoints. It carries a per-site fact up to a whole recursive generator, and it is not
   specific to any interpretation.

Two facts about `SPMF` shape every proof here. Membership goes through `SPMF.support`, never through
the generator itself; and a reweighting preserves the support but not the generator, so the tuning
results in `StrataGenerators.TuningPrototypes` are stated as equalities of supports.
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

The proofs in this package name these lemmas without a prefix. Re-export them at the root so that no
`open` is needed at each use site — an `open SPMF` would also bring `SPMF.pure` into scope and make
every bare `pure` in a generator ambiguous with `Pure.pure`.

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

/-! ## A relation a fixpoint preserves

The lemma below turns a per-site fact — typically a reweighting of one `frequency` — into a fact
about a whole recursive generator. `@[tunable]` binds `θ` *outside* the fixpoint and re-proves
monotonicity for the rewritten functional, so `genFoo.tuned θ` and `genFoo` are one fixpoint over two
functionals that differ only inside their `frequency` sites. The lemma is not specific to an
interpretation; it belongs upstream in Basalt. -/

/-- **A relation that a well-founded recursion preserves.** The two step functions of a tuned
generator and its untuned original are not *equal* — they differ in their `frequency` weights — so
`congrArg` does not apply. Give a relation `R` on results instead, show that the two step functions
map `R`-related recursive bundles to `R`-related results, and conclude that the two fixpoints are
`R`-related everywhere.

The equation compiler uses `WellFounded.fix` for a generator with `termination_by`, and the members
of a `mutual` block share one such fix over a `PSum` of their argument tuples. This lemma is
therefore what lifts a per-site fact to a whole block.

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

end StrataGenerators
