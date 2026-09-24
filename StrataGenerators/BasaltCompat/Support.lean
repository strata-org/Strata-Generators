/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import Basalt.SPMF.Support
import StrataGenerators.BasaltCompat.Combinators

open Lean.Order RandomChoice

/-!
# Support lemmas that Basalt no longer ships

Basalt's `lean-4.29` reorganization narrowed `Basalt/SPMF/Support.lean` to the host constructs
(`bind`, `pure`, `map`, `ite`, `dite`, `choose`) and to the list combinators whose support the
observation walk bridges. Everything else it used to state — the membership forms of
`support_oneOf` and `support_frequency`, and the support of `elements`, `RandomChoice.pick`,
`chooseNat`, `chooseInt`, `RandomChoice.coin`, `biasedOptionGen` and `optionGen` — is now meant to
be recomputed per site by `sound_bound` / `complete_bound`.

The proofs in this package invert support directly, at every combinator, in a few hundred places.
This file keeps that API alive by re-deriving each dropped lemma from the ones Basalt kept, so that
the reorganization is a change to this one file rather than to every proof. Nothing here is new
mathematics: every statement is the one Basalt used to prove, and every proof goes through
`support_oneOf`, `support_frequency` or `support_choose`.

`StrataGenerators.GenSupport` re-exports these names unqualified, next to the ones Basalt still
owns.
-/

namespace SPMF

/-! ### Membership forms of the two set-level laws Basalt kept

`oneOf` is universe-polymorphic in the drawn type and `frequency` is not — `frequency` is fixed at
`Type` upstream — so the two statements below are, too. -/

universe u

/-- Membership form of `support_oneOf`. -/
@[simp]
theorem mem_support_oneOf_iff {α : Type u} {a : α}
    {gs : List (Unit → SPMF α)}
    (hne : gs ≠ []) :
    a ∈ support (oneOf gs hne) ↔ ∃ g ∈ gs, a ∈ (g ()).support := by
  simp [support_oneOf]

/-- Membership form of `support_frequency`. -/
@[simp]
theorem mem_support_frequency_iff {α : Type} {a : α}
    {gs : List (Nat × (Unit → SPMF α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) :
    a ∈ (frequency gs h_pos).support ↔ ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support := by
  simp [support_frequency]

/-! ### `pick`

Basalt now defines `RandomChoice.pick x y` as `oneOf [x, y]` and deprecates it, so both statements
below are `support_oneOf` at a two-element list. They name the deprecated combinator on purpose —
that is the point of stating them — so the deprecation linter is off for the two declarations, as it
is at Basalt's own `RandomChoice.monotone_pick`. -/

set_option linter.deprecated false in
@[simp]
theorem support_pick {α : Type u}
    {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).support = x.support ∪ y.support := by
  rw [RandomChoice.pick, support_oneOf (by simp)]
  ext a
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨g, (rfl | rfl), ha⟩
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (ha | ha)
    · exact ⟨_, Or.inl rfl, ha⟩
    · exact ⟨_, Or.inr rfl, ha⟩

set_option linter.deprecated false in
@[simp]
theorem mem_support_pick_iff {α : Type u} {a : α}
    {x y : SPMF α} :
    a ∈ (pick (fun () => x) (fun () => y)).support ↔ a ∈ x.support ∨ a ∈ y.support := by
  rw [support_pick]; exact Set.mem_union _ _ _

/-! ### `elements`, `chooseNat`, `chooseInt` -/

/-- The support of `elements xs` is exactly the set of elements of `xs`. -/
@[simp]
theorem support_elements {α : Type}
    {xs : List α}
    (hne : xs ≠ []) :
    support (elements xs hne) = { x | x ∈ xs } := by
  have hlen : 0 < xs.length := List.length_pos_iff.mpr hne
  simp only [elements, support_bind, support_map, support_choose]
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨i, hge, hle⟩, ⟨j, -, hj⟩, ha⟩
    simp only [mem_support_pure_iff] at ha
    exact ha ▸ List.getElem_mem _
  · intro hmem
    obtain ⟨i, hlt, heq⟩ := List.mem_iff_getElem.mp hmem
    have hle : i ≤ xs.length - 1 := by omega
    refine ⟨⟨i, Nat.zero_le _, hle⟩, ⟨⟨⟨i, Nat.zero_le _, hle⟩⟩, trivial, rfl⟩, ?_⟩
    simp only [mem_support_pure_iff]
    exact heq.symm

/-- Membership form of `support_elements`. -/
@[simp]
theorem mem_support_elements_iff {α : Type} {a : α}
    {xs : List α}
    (hne : xs ≠ []) :
    a ∈ support (elements xs hne) ↔ a ∈ xs := by
  simp [support_elements]

@[simp]
theorem mem_support_chooseNat_iff {lo hi : Nat} {h : lo ≤ hi} {n : Nat} :
    n ∈ (chooseNat lo hi h : SPMF Nat).support ↔ lo ≤ n ∧ n ≤ hi := by
  unfold chooseNat
  simp only [mem_support_map_iff, mem_support_choose_iff, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.down.property
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨n, h1, h2⟩⟩, rfl⟩

@[simp]
theorem mem_support_chooseInt_iff {lo hi : Int} {h : lo ≤ hi} {n : Int} :
    n ∈ (chooseInt lo hi h : SPMF Int).support ↔ lo ≤ n ∧ n ≤ hi := by
  unfold chooseInt
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_chooseNat_iff]
  constructor
  · rintro ⟨k, ⟨-, hk⟩, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(n - lo).toNat, ⟨Nat.zero_le _, by omega⟩, by omega⟩

/-! ### `RandomChoice.coin` and the two option generators -/

/-- The support of `RandomChoice.coin r` holds both outcomes exactly when the bias is strictly
between 0 and 1; otherwise it holds only one. -/
@[simp]
theorem support_coin {r : Rat} (h0 : 0 < r) (h1 : r < 1) :
    SPMF.support (RandomChoice.coin r) = {true, false} := by
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr h0
  have hden : r.num < (r.den : ℤ) := Rat.num_lt_denom_iff.mpr h1
  have hden_pos : 0 < r.den := r.den_pos
  ext b
  simp only [RandomChoice.coin, mem_support_bind_iff, mem_support_choose_iff, true_and,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  refine iff_of_true ?_ (by cases b <;> simp)
  cases b
  · refine ⟨⟨⟨r.den - 1, Nat.zero_le _, by omega⟩⟩, ?_⟩
    rw [if_neg (by simp only [Nat.cast_pred hden_pos]; omega)]
    exact mem_support_pure_iff.mpr rfl
  · refine ⟨⟨⟨0, Nat.zero_le _, by omega⟩⟩, ?_⟩
    rw [if_pos (by simpa using hnum)]
    exact mem_support_pure_iff.mpr rfl

@[simp]
theorem mem_support_coin_iff {r : Rat} {b : Bool} (h0 : 0 < r) (h1 : r < 1) :
    b ∈ SPMF.support (RandomChoice.coin r) ↔ b = true ∨ b = false := by
  rw [support_coin h0 h1, Set.mem_insert_iff, Set.mem_singleton_iff]

@[simp]
theorem support_biasedOptionGen {α : Type} {r : Rat}
    {g : SPMF α}
    (h0 : 0 < r) (h1 : r < 1) :
    support (biasedOptionGen r g) = { none } ∪ { some x | x ∈ g.support } := by
  ext o
  simp only [biasedOptionGen, mem_support_bind_iff, mem_support_coin_iff h0 h1,
    Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, -, ho⟩
    cases c
    · simp only [Bool.false_eq_true, if_false, mem_support_pure_iff] at ho
      exact Or.inl ho
    · simp only [if_true, mem_support_bind_iff, mem_support_pure_iff] at ho
      obtain ⟨a, ha, rfl⟩ := ho
      exact Or.inr ⟨a, ha, rfl⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨false, Or.inr rfl, by simp⟩
    · exact ⟨true, Or.inl rfl, by
        simp only [if_true, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨a, ha, rfl⟩⟩

@[simp]
theorem mem_support_biasedOptionGen_iff {α : Type} {r : Rat} {x : Option α}
    {g : SPMF α} (h0 : 0 < r) (h1 : r < 1) :
    x ∈ (biasedOptionGen r g).support ↔ x = none ∨ (∃ a ∈ g.support, x = some a) := by
  rw [support_biasedOptionGen h0 h1]
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  exact or_congr_right ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩⟩

@[simp]
theorem support_optionGen {α : Type}
    {g : SPMF α} :
    support (optionGen g) = {none} ∪ {some x | x ∈ g.support} := by
  unfold optionGen
  apply support_biasedOptionGen <;> norm_num

@[simp]
theorem mem_support_optionGen_iff {α : Type} {x : Option α}
    {g : SPMF α} :
    x ∈ support (optionGen g) ↔ x = none ∨ (∃ a ∈ g.support, x = some a) := by
  unfold optionGen
  apply mem_support_biasedOptionGen_iff <;> norm_num

end SPMF
