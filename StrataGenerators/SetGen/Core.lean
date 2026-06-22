/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein

Vendored from https://github.com/hgoldstein95/basalt (SetGen branch, not yet on `main`).
-/
import StrataGenerators.SetGen.Defs
import Basalt.Gen

open Lean.Order RandomChoice
open scoped SetGen.Set

/-!
# Set-Based Generator Interpretation

This file establishes a `Gen` instance for `Set`, providing a simple interpretation of generators
in terms of their support (the set of values they can produce). This is a simplified version of the
`SPMF` interpretation that tracks only reachability, not probabilities.

## Main Definitions

- `Gen Set` — The `Gen` instance for `Set`.
-/

namespace SetGen

section operations

/-- The bottom element is the empty set. -/
instance : Inhabited (Set α) where
  default := ∅

noncomputable instance : RandomChoice Set where
  choose lo hi _ := {a | lo ≤ a.down.val ∧ a.down.val ≤ hi}

end operations

section operation_uses

@[simp] theorem pick_mem_iff {x y : Set α} (a : α) :
    a ∈ (pick (fun () => x) (fun () => y) : Set α) ↔ a ∈ x ∨ a ∈ y := by
  simp only [RandomChoice.pick, Bind.bind, RandomChoice.choose]
  constructor
  · rintro ⟨n, ⟨hlo, hhi⟩, ha⟩
    by_cases h : n.down.val == 0
    · left; simpa [h] using ha
    · right; simpa [h] using ha
  · intro h
    cases h with
    | inl hx => exact ⟨⟨⟨0, Nat.zero_le _, Nat.zero_le _⟩⟩, ⟨Nat.zero_le _, Nat.zero_le _⟩, by simpa⟩
    | inr hy => exact ⟨⟨⟨1, Nat.zero_le _, Nat.le_refl _⟩⟩, ⟨Nat.zero_le _, Nat.le_refl _⟩, by simpa⟩

@[simp] theorem mem_choose {lo hi : Nat} {h : lo ≤ hi}
    {a : ULift {x : Nat // lo ≤ x ∧ x ≤ hi}} :
    a ∈ (choose lo hi h : Set (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) ↔ lo ≤ a.down.val ∧ a.down.val ≤ hi := Iff.rfl

@[simp] theorem mem_dite {p : Prop} [Decidable p] {t : p → Set α} {e : ¬p → Set α} :
    a ∈ (dite p t e : Set α) ↔ (∃ h : p, a ∈ t h) ∨ (∃ h : ¬p, a ∈ e h) := by
  by_cases hp : p <;> simp_all

theorem bot_mem_iff (a : α) : a ∈ (default : Set α) ↔ False := by
  simp [default, Inhabited.default]

end operation_uses

section order

instance : Lean.Order.PartialOrder (Set α) where
  rel s t := ∀ a, a ∈ s → a ∈ t
  rel_refl := fun _ h => h
  rel_trans h₁ h₂ := fun a ha => h₂ a (h₁ a ha)
  rel_antisymm h₁ h₂ := Set.ext (fun a => ⟨h₁ a, h₂ a⟩)

noncomputable instance : CCPO (Set α) where
  has_csup := by
    intros c _
    refine ⟨{a | ∃ s, c s ∧ a ∈ s}, ?_⟩
    intro x
    constructor
    · intro h_sup_le y hy a ha
      exact h_sup_le a ⟨y, hy, ha⟩
    · intro h_ub a ⟨y, hy, ha⟩
      exact h_ub y hy a ha

instance : MonoBind Set where
  bind_mono_left {_ _} {p₁ p₂ f} h := by
    intro b hb
    obtain ⟨a, ha, hfa⟩ := hb
    exact ⟨a, h a ha, hfa⟩
  bind_mono_right {_ _} {p f₁ f₂} h := by
    intro b hb
    obtain ⟨a, ha, hfa⟩ := hb
    exact ⟨a, ha, h a b hfa⟩

end order

section equations

@[simp]
theorem bot_bind (f : α → Set β) : (default : Set α) >>= f = default := by
  ext b
  simp only [default, Inhabited.default, Bind.bind, EmptyCollection.emptyCollection]
  exact ⟨fun ⟨_, h, _⟩ => h, False.elim⟩

end equations

end SetGen
