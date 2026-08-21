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

`Basalt.Combinators.optionGen` and `biasedOptionGen` decide the `some` or `none` split with a
rational `RandomChoice.coin`. A coin is not a `frequency` site, and `@[tunable]` rewrites only a
`frequency`, so the attribute cannot expose that split.

`weightedOptionGen` has the same support and splits on two `Nat` weights instead. Reach for it when
the *presence* of an optional clause is the knob you want. A function precondition is one such
clause, and `PrecondElim` is the pass that acts on it.

A tuning can address the split only if the tagged generator writes the split out in its own body.
`@[tunable]` collects the `frequency` calls in that body, and it inlines only that declaration's own
compiler-generated auxiliaries. This combinator takes its weights as variables rather than as
literals, so the attribute rejects the combinator itself.
`TuningPrototypes.genPreconditionW` writes the two-branch `frequency` inline. It then records by
`rfl` that the result is this combinator at weights 1 to 1, so the support lemma below still
describes it.

Both weights must be positive for the support to match `optionGen`'s. `Tuning.weight` clamps every
weight to 1 or more, so a tuned generator that wraps this stays total for every runtime `θ`.

This combinator belongs in `Basalt.Combinators`, next to `biasedOptionGen`. It is here to avoid a
change to Basalt.
-/

namespace SetGen

/-- Like `biasedOptionGen`, but a `frequency` over two `Nat` weights decides the split. A
`@[tunable]` generator that inlines this split therefore exposes the bias as a site.

The `some` branch uses an explicit `bind`, as `biasedOptionGen` does, because `Lean.Order` has no
monotonicity lemma for `<$>`. -/
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
