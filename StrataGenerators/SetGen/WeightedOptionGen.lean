/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.SetGen.Support
import Basalt.Combinators

open RandomChoice
open scoped SetGen.Set

/-!
# `weightedOptionGen`: a tunable option combinator

`Basalt.Combinators.biasedOptionGen`/`optionGen` decide the `some`/`none` split with a rational
`RandomChoice.coin`, which is *not* a `frequency` site — so `tunable def` (which only rewrites
`frequency`) cannot expose that split as a tunable knob.

`weightedOptionGen` is a drop-in with the same support but a `frequency`-based split over two `Nat`
weights, so a `tunable def` that inlines it (or writes the two-branch `frequency` directly) records
a tunable site and a `Tuning` can bias the `some` rate at runtime. This is the combinator to reach
for when the *presence* of an optional clause (e.g. a function precondition, for `PrecondElim`)
is what you want to tune.

Both weights must be positive for the support to match `optionGen`'s (`none` and every `some a`
reachable); `Tuning.weight` clamps to ≥ 1, so a `tunable def` wrapping this stays total for every
runtime `θ`, exactly as the `frequency`-site story guarantees elsewhere.

Meant to live in `Basalt.Combinators` next to `biasedOptionGen`; kept here for now to avoid a Basalt
change (see the tuning-for-SetGen PR).
-/

namespace SetGen

/-- Like `biasedOptionGen`, but the `some`/`none` split is a `frequency` over `Nat` weights rather
than a rational `coin` — so a `tunable def` inlining this split exposes the bias as a tunable site.
`some <$> g` is written with an explicit `bind` (as in `biasedOptionGen`) because `Lean.Order` has
no monotonicity lemma for `<$>`. -/
def weightedOptionGen [Gen G] (wSome wNone : Nat) (g : G α)
    (h : 0 < wSome + wNone := by omega) : G (Option α) :=
  frequency [
    (wSome, fun _ => do let x ← g; pure (some x)),
    (wNone, fun _ => pure none)
  ] (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)

/-- Support of `weightedOptionGen`, given positive weights: `none` is reachable (via the `wNone`
branch) and `some a` exactly when `a ∈ support g` (via the `wSome` branch). Identical to
`SetGen.mem_support_biasedOptionGen_iff`, so a generator's soundness/completeness proof ports by
swapping which option-support lemma it cites. -/
@[simp]
theorem mem_support_weightedOptionGen_iff {wSome wNone : Nat} {g : Set α} {o : Option α}
    (hs : 0 < wSome) (hn : 0 < wNone) (h : 0 < wSome + wNone) :
    o ∈ support (weightedOptionGen wSome wNone g h) ↔
      o = none ∨ ∃ a ∈ support g, o = some a := by
  unfold weightedOptionGen
  rw [mem_support_frequency_iff]
  constructor
  · rintro ⟨w, gen, hmem, _, ha⟩
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      simp only [mem_support_bind_iff, mem_support_pure_iff] at ha
      obtain ⟨a, ha', rfl⟩ := ha
      exact Or.inr ⟨a, ha', rfl⟩
    · rcases List.mem_cons.mp hmem' with heq | hnil
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        simp only [mem_support_pure_iff] at ha
        exact Or.inl ha
      · simp at hnil
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · refine ⟨wNone, _, List.mem_cons_of_mem _ List.mem_cons_self, hn, ?_⟩
      simp only [mem_support_pure_iff]
    · refine ⟨wSome, _, List.mem_cons_self, hs, ?_⟩
      simp only [mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨a, ha, rfl⟩

end SetGen
