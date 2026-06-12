/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein

Vendored from https://github.com/hgoldstein95/basalt (SetGen branch, not yet on `main`).
-/
import StrataGenerators.SetGen.Core
import Basalt.Combinators

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

/-- The support of `oneOf gs` is exactly the union of the support of all the generators in `gs` -/
@[simp]
theorem support_oneOf
    {gs : List (Unit → Set α)}
    (hne : gs ≠ []) :
    support (oneOf gs) = {a | ∃ g ∈ gs, a ∈ g ()} := by
  simp only [oneOf, support_bind, support_map, support_choose]
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  . -- ∃ i ∈ [0, gs.length -1], a ∈ (gs[i]! ()).support → ∃ g ∈ gs, a ∈ (g ()).support
    intro h
    obtain ⟨ i, h_idx, ha ⟩ := h
    obtain ⟨ n, ⟨ h_lowerbound, h_upperbound ⟩, hi ⟩ := h_idx
    have h_pos : 0 < gs.length := by
      rw [List.length_pos_iff]
      assumption
    have h_lt : i < gs.length := by omega
    refine ⟨ gs[i], ?_, ?_ ⟩
    . -- Goal: `gs[i] ∈ gs`
      apply List.getElem_mem
    . -- Goal: `a ∈ (gs[i] ()).support`
      -- To do this, rewrite `gs[i]!` in terms of `gs[i]`
      rw [getElem!_pos gs i h_lt] at ha
      assumption
  . -- ∃ g ∈ gs, a ∈ (g ()).support → ∃ i ∈ [0, gs.length - 1], a ∈ (gs[i]! ()).support
    intros h
    obtain ⟨ g, hg, ha ⟩ := h
    obtain ⟨ i, hi, heq ⟩ := List.mem_iff_getElem.mp hg
    refine ⟨ i, ?_, ?_ ⟩
    . -- 0 ≤ i ≤ gs.length - 1
      exists ⟨ i ⟩
      dsimp
      constructor
      . apply Set.mem_setOf_eq.mpr
        constructor <;> (dsimp; omega)
      . rfl
    . -- a ∈ (gs[i]! ()).support
      rw [getElem!_pos gs i hi]
      subst heq
      assumption

/-- Any element in the support of `oneOf gs` is in the support of some
    generator in `gs` -/
@[simp]
theorem mem_support_oneOf_iff
    {gs : List (Unit → Set α)}
    (hne : gs ≠ []) :
    a ∈ support (oneOf gs) ↔ ∃ g ∈ gs, a ∈ support (g ()) := by
  simp only [support, oneOf, Set.mem_bind, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨idx, ⟨n, hn, rfl⟩, ha⟩
    have h_pos : 0 < gs.length := List.length_pos_iff.mpr hne
    have h_lt : n.down < gs.length := by
      exact Nat.lt_of_le_of_lt hn.2 (by omega)
    exact ⟨gs[n.down], List.getElem_mem h_lt, by rwa [getElem!_pos gs n.down h_lt] at ha⟩
  · rintro ⟨g, hg, ha⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have h_pos : 0 < gs.length := List.length_pos_iff.mpr hne
    refine ⟨i, ⟨⟨i⟩, ⟨Nat.zero_le _, ?_⟩, rfl⟩, by rwa [getElem!_pos gs i hi]⟩
    show i ≤ gs.length - 1; omega

/-- If `n < sum (fst <$> gs)`, then `frequencyAux default gs n` picks a sub-generator
    from `gs` that has non-zero weight `w` -/
private theorem frequencyAux_mem
    {gs : List (Nat × (Unit → Set α))}
    {n : Nat}
    (h : n < List.sum (List.map Prod.fst gs)) :
    ∃ w g, ⟨w, g⟩ ∈ gs ∧ 0 < w ∧ (frequencyAux default gs n).snd = g () := by
  induction gs generalizing n with
  | nil => contradiction
  | cons hd tl ih =>
    unfold frequencyAux
    obtain ⟨w, g⟩ := hd
    split
    · exact ⟨w, g, .head tl, by omega, rfl⟩
    · have h_remaining : n - w < List.sum (List.map Prod.fst tl) := by
        simp only [List.map_cons, List.sum_cons] at h; omega
      obtain ⟨w', g', hmem, hpos, heq⟩ := ih h_remaining
      exact ⟨w', g', List.mem_cons_of_mem _ hmem, hpos, heq⟩


/-- If a weighted generator `(w, g) ∈ gs` where the weight `w` is non-zero,
    then `frequencyAux default gs n` produces `(w, g)` if `n < sum (fst <$> gs)` -/
private theorem frequencyAux_n_exists
    {gs : List (Nat × (Unit → Set α))}
    {w : Nat} {g : Unit → Set α}
    (hmem : (w, g) ∈ gs)
    (hnonzero : 0 < w) :
    ∃ n, n < List.sum (List.map Prod.fst gs) ∧
      (frequencyAux default gs n).snd = g () := by
  induction gs with
  | nil => contradiction
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | h_tl
    · refine ⟨0, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]; omega
      · unfold frequencyAux; simp [hnonzero]
    · obtain ⟨n, hn, heq⟩ := ih h_tl
      obtain ⟨w', _⟩ := hd
      refine ⟨w' + n, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]; omega
      · unfold frequencyAux
        have : ¬ (w' + n < w') := by omega
        simp [this, heq]

/-- Any element in the support of `frequency gs` is in the support
    of some generator in `gs` with non-zero weight -/
@[simp]
theorem mem_support_frequency_iff
    {gs : List (Nat × (Unit → Set α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) :
    a ∈ support (frequency gs h_pos) ↔
      ∃ w g, ⟨w, g⟩ ∈ gs ∧ 0 < w ∧ a ∈ support (g ()) := by
  simp only [support, frequency, Set.mem_bind, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨idx, ⟨n, hn, rfl⟩, ha⟩
    have h_lt : n.down < List.sum (List.map Prod.fst gs) := by
      exact Nat.lt_of_le_of_lt hn.2 (by omega)
    obtain ⟨w, g, hmem, hpos, heq⟩ := frequencyAux_mem h_lt
    exact ⟨w, g, hmem, hpos, heq ▸ ha⟩
  · rintro ⟨w, g, hmem, hpos, ha⟩
    obtain ⟨n, hn_lt, hn_eq⟩ := frequencyAux_n_exists hmem hpos
    refine ⟨n, ⟨⟨n⟩, ⟨Nat.zero_le _, ?_⟩, rfl⟩, hn_eq ▸ ha⟩
    show n ≤ (List.map Prod.fst gs).sum - 1; omega

/-- If the sum of weights in `gs` is non-zero, then the support of `frequency gs`
    is exactly the union of the support of the generators in `gs` with non-zero weights -/
@[simp]
theorem support_frequency
    {gs : List (Nat × (Unit → Set α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) :
    support (frequency gs h_pos) = {a | ∃ w g, ⟨ w, g ⟩ ∈ gs ∧ 0 < w ∧ a ∈ (g ())} := by
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  · -- a ∈ support (frequency gs h_pos) -> ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support
    intro h
    simp only [frequency, support_bind, support_map, support_choose] at h
    -- `i` is the weight value picked inside `frequency`
    obtain ⟨i, h_idx, ha⟩ := h
    obtain ⟨n, ⟨_, _⟩, hi⟩ := h_idx
    have h_lt : i < List.sum (List.map Prod.fst gs) := by omega
    obtain ⟨w, g, _, _, heq⟩ := frequencyAux_mem h_lt
    rw [heq] at ha
    refine ⟨w, g, ?_, ?_, ?_⟩ <;> assumption
  · -- ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support -> a ∈ support (frequency gs h_pos)
    simp only [frequency, support_bind, support_map, support_choose]
    intro ⟨w, g, hwg_mem, hwt, ha⟩
    obtain ⟨n, hn_lt, hn_eq⟩ := frequencyAux_n_exists hwg_mem hwt
    simp only [Set.mem_setOf_eq]
    apply Exists.intro n
    constructor
    · -- ∃ a, (0 ≤ a.down ∧ a.down ≤ total - 1) ∧ n = a.down
      apply Exists.intro (ULift.up n)
      constructor
      · -- 0 ≤ n ∧ n ≤ total - 1
        constructor
        · -- 0 ≤ n
          omega
        · -- n ≤ total - 1
          show n ≤ (List.map Prod.fst gs).sum - 1
          omega
      · -- n = (ULift.up n).down
        rfl
    · -- a ∈ (frequencyAux default gs n).snd.support
      rw [hn_eq]
      assumption

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
