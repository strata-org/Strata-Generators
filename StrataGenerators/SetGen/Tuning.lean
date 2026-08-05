/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.SetGen.Support
import StrataGenerators.SetGen.Classes

open RandomChoice
open scoped SetGen.Set

/-!
# Tuning support for `Set`-based generators

Basalt's tuning infrastructure has two halves:

* the data and the `tunable def` command (`Basalt.Tuning` / `Basalt.Tuning.Macro`) — `Tuning`,
  `Site`, `Tuning.weight`, `Tuning.weight_pos`, and the macro that threads a `Tuning` through a
  generator's `frequency` sites. All of it is generic over `[Gen G]`, with no `SPMF` dependency, so
  it applies to any `Gen`, including `SetGen.Set` (see `StrataGenerators.SetGen.Core`), with no
  changes. `tunable def genFoo … : SetGen.Set α := …` already elaborates, emitting
  `genFoo.tuned/.defaults/.sites/.tuned_defaults`.

* the proof-side reweight lemmas, which in Basalt live in `Basalt.SPMF.Support` and `Basalt.Laws`
  and are stated for `SPMF`. This file ports exactly those to `SetGen.Set`, reusing the existing
  `SetGen.support_frequency` / `SetGen.support_oneOf` characterizations:

  - `SetGen.support_frequency_reweight` — replacing a uniform `oneOf` by a `frequency` over the same
    branches (with positive weights) leaves the support unchanged;
  - `SetGen.support_frequency_congr_weights` — changing the weights of a `frequency` in place (the
    shape a `tunable def` rewrite takes) leaves the support unchanged;
  - `SetGen.IsSoundAndComplete.of_support_eq` — soundness-and-completeness transfers along a support
    equation, so a `tunable def`'s `tuned_support` fact lifts an untuned `IsSoundAndComplete` to the
    tuned generator in one step.

`Tuning.weight_pos` (from `Basalt.Tuning`) discharges the positivity hypotheses of the first two for
*every* runtime `θ`, exactly as it does on the `SPMF` side, so there is no weighting a user can
supply that fails them.
-/

namespace SetGen

section reweight

variable {α : Type}

/-- Reweighting a uniform choice preserves its support. Replacing `oneOf gs` by a `frequency` over
the same branches leaves the set of reachable values unchanged, provided every weight is positive.

Ported from `SPMF.support_frequency_reweight` to `SetGen.Set`. -/
theorem support_frequency_reweight
    {gs : List (Unit → Set α)} {gs' : List (Nat × (Unit → Set α))}
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1)
    (hne : gs ≠ []) (h_pos : 0 < List.sum (List.map Prod.fst gs')) :
    support (frequency gs' h_pos) = support (oneOf gs hne) := by
  subst hsnd
  rw [support_frequency, support_oneOf]
  ext a
  simp only [Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    exact ⟨g, ⟨(w, g), hmem, rfl⟩, ha⟩
  · rintro ⟨g, ⟨⟨w, g'⟩, hmem, hg⟩, ha⟩
    cases hg
    exact ⟨w, g', hmem, hpos _ hmem, ha⟩

/-- The same, between two `frequency`s. This is the shape a tuning rewrite has: `tunable def`
replaces literal weights by `Tuning.weight θ i d` in place, so both sides are already `frequency`s
and only the weights differ.

Ported from `SPMF.support_frequency_congr_weights` to `SetGen.Set`. -/
theorem support_frequency_congr_weights
    {gs gs' : List (Nat × (Unit → Set α))}
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    support (frequency gs' h') = support (frequency gs h) := by
  rw [support_frequency, support_frequency]
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    have : g ∈ gs.map Prod.snd := hsnd ▸ List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
    obtain ⟨⟨w', g'⟩, hmem', hg⟩ := List.mem_map.mp this
    cases hg
    exact ⟨w', g', hmem', hpos' _ hmem', ha⟩
  · rintro ⟨w, g, hmem, _, ha⟩
    have : g ∈ gs'.map Prod.snd := hsnd ▸ List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
    obtain ⟨⟨w', g'⟩, hmem', hg⟩ := List.mem_map.mp this
    cases hg
    exact ⟨w', g', hmem', hpos _ hmem', ha⟩

end reweight

/-- Soundness-and-completeness transfers along a support equation. Given a proof that the tuned
generator has the same support as the untuned one (`SetGen.support_frequency_congr_weights` supplies
exactly this, per site), an `IsSoundAndComplete` for the untuned generator lifts to the tuned one.

Ported from `IsSoundAndComplete.of_support_eq` (`Basalt.Laws`) to `SetGen.Set`; here
`IsSoundAndComplete` is a class, so this is a derived instance-producing lemma. -/
theorem IsSoundAndComplete.of_support_eq {g g' : Set α} {P : α → Prop}
    (h : support g' = support g) (hg : IsSoundAndComplete g P) :
    IsSoundAndComplete g' P where
  support_iff a := by rw [h]; exact hg.support_iff a

end SetGen
