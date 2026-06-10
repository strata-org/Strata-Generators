/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein

Vendored from https://github.com/hgoldstein95/basalt (SetGen branch, not yet on `main`).
-/
import StrataGenerators.SetGen.Core

open Lean.Order RandomChoice
open scoped SetGen.Set

/-!
# SetGen Support

This file sets up basic definitions for working with the support of `Set`-based generators.
Since a `Set α` *is* its own support, these lemmas characterize membership after monadic operations.

## Main Definitions

- `SetGen.support` — The support of a `Set`-based generator is the set itself.
-/

namespace SetGen

section support

/-- The support of a `Set`-based generator is the set itself. -/
def support (s : Set α) : Set α := s

theorem mem_support_iff (s : Set α) (a : α) : a ∈ support s ↔ a ∈ s := Iff.rfl

@[simp]
theorem support_bind {x : Set α} {f : α → Set β} :
    support (x >>= f) = {b | ∃ a ∈ support x, b ∈ support (f a)} := by
  ext b; exact Iff.rfl

@[simp]
theorem mem_support_bind_iff {x : Set α} {f : α → Set β} :
    b ∈ support (x >>= f) ↔ ∃ a ∈ support x, b ∈ support (f a) := Iff.rfl

@[simp]
theorem support_pure :
    support (Pure.pure a : Set _) = {a} := rfl

@[simp]
theorem mem_support_pure_iff :
    b ∈ support (pure a : Set _) ↔ b = a := Iff.rfl

@[simp]
theorem support_map {x : Set α} {f : α → β} :
    support (f <$> x) = {b | ∃ a ∈ support x, b = f a} := by
  ext b; simp only [support, Set.fmap_eq_image, Membership.mem, Set.Mem, Set.image]
  exact ⟨fun ⟨a, ha, hb⟩ => ⟨a, ha, hb.symm⟩, fun ⟨a, ha, hb⟩ => ⟨a, ha, hb.symm⟩⟩

@[simp]
theorem mem_support_map_iff {x : Set α} {f : α → β} :
    b ∈ support (f <$> x) ↔ ∃ a ∈ support x, b = f a := by
  simp only [support, Set.fmap_eq_image, Membership.mem, Set.Mem, Set.image]
  exact ⟨fun ⟨a, ha, hb⟩ => ⟨a, ha, hb.symm⟩, fun ⟨a, ha, hb⟩ => ⟨a, ha, hb.symm⟩⟩

@[simp] theorem mem_support_dite_iff {p : Prop} [Decidable p]
    {t : p → Set α} {e : ¬p → Set α} :
    a ∈ support (dite p t e) ↔ (∃ h : p, a ∈ support (t h)) ∨ (∃ h : ¬p, a ∈ support (e h)) := by
  simp only [support]; by_cases hp : p <;> simp_all

theorem mem_support_ite_iff {p : Prop} [Decidable p]
    {t e : Set α} :
    a ∈ support (ite p t e) ↔ (p ∧ a ∈ support t) ∨ (¬p ∧ a ∈ support e) := by
  simp only [support]; by_cases hp : p <;> simp_all

@[simp]
theorem support_choose :
    support (choose lo hi h : Set (ULift Nat)) = {a | lo ≤ a.down ∧ a.down ≤ hi} := rfl

@[simp]
theorem mem_support_choose_iff :
    a ∈ support (choose lo hi h : Set (ULift Nat)) ↔ lo ≤ a.down ∧ a.down ≤ hi := Iff.rfl

@[simp]
theorem support_pick {x y : Set α} :
    support (pick (fun () => x) (fun () => y)) = support x ∪ support y := by
  ext a; simp [support, Set.mem_union_iff, pick_mem_iff]

@[simp]
theorem mem_support_pick_iff {x y : Set α} :
    a ∈ support (pick (fun () => x) (fun () => y)) ↔ a ∈ support x ∨ a ∈ support y := by
  simp [support, pick_mem_iff]

-- @[simp]
-- theorem support_oneOf
--     {gs : List (Unit → Set α)}
--     (hne : gs ≠ []) :
--     support (oneOf gs) = {a | ∃ g ∈ gs, a ∈ (g ()).support} := by
--   sorry

theorem bind_congr_support {x : Set α} (h : ∀ a ∈ support x, f a = g a) :
    (x >>= f) = (x >>= g) := by
  ext b; simp only [Set.bind_def', support] at *
  constructor
  · rintro ⟨a, ha, hb⟩; exact ⟨a, ha, h a ha ▸ hb⟩
  · rintro ⟨a, ha, hb⟩; exact ⟨a, ha, (h a ha).symm ▸ hb⟩

theorem mem_support_csup {c : Set α → Prop} (hc : chain c) {a : α} :
    a ∈ support (CCPO.csup hc) ↔ ∃ s, c s ∧ a ∈ support s := by
  simp only [support]
  constructor
  · intro ha
    have hub : ∀ s, c s → s ⊑ ({a | ∃ t, c t ∧ a ∈ t} : Set α) :=
      fun s hs a ha => ⟨s, hs, ha⟩
    have hle : CCPO.csup hc ⊑ ({a | ∃ t, c t ∧ a ∈ t} : Set α) :=
      (csup_le hc hub : CCPO.csup hc ⊑ _)
    exact hle a ha
  · intro ⟨s, hs, ha⟩
    exact le_csup hc hs a ha

end support

end SetGen
