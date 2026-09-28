/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import StrataGenerators.BasaltCompat.Defs
import Basalt.SPMF.Support

open Lean.Order RandomChoice

/-!
# What the Basalt library used to export

Basalt's `SPMF` support API was reorganised around the **observation walk**: a judgment about a
generator is proved by `walk`, which recurses on the generator's syntax and applies one `@[gen_rule]`
lemma per combinator. Two consequences for a caller:

* `Basalt/SPMF/Support.lean` keeps the set-level equalities `support_oneOf` and `support_frequency`,
  and the monadic membership lemmas (`mem_support_bind_iff`, `mem_support_pure_iff`,
  `mem_support_map_iff`, `mem_support_choose_iff`, `mem_support_dite_iff`, `mem_support_ite_iff`).
  It no longer states a **membership** form for a choice combinator, and states nothing at all for
  `RandomChoice.pick`, `elements`, `chooseNat`, `chooseInt` or `RandomChoice.coin`.
* `biasedOptionGen` and `optionGen` left the library for `BasaltTest/OptionGen.lean`, where they are
  fixtures that pin the walk's behaviour on a combinator with no law.

This file restores exactly what this package draws on, and nothing else.

## Why a membership form and not the walk

The proofs in this package are **inversions**. They take a hypothesis `e ∈ support (genFoo …)` apart
into one case per branch of `genFoo`, with `rcases` on the result of a `simp only` over this family,
and then reason per branch. `rcases` needs an `Iff` whose right-hand side is a disjunction of branch
conditions; a set equality does not serve, and neither does a walk, which proves a judgment rather
than decomposing a hypothesis.

Where a proof establishes a judgment rather than inverting one — `IsSoundFor`, `IsCompleteFor` — the
walk is the better tool and this package uses it. `genLExprBase_termDepth_bound` in
`StrataGenerators.HasTypeAGen` is the worked example.

No lemma below adds an assumption. Each is the membership form of an equality Basalt still proves, or
is derived from `support_bind`, `support_map` and `support_choose`, which Basalt still states. Several
proofs are Basalt's own, carried over unchanged.
-/

namespace SPMF

/-! ## The choice combinators, branch by branch -/

/-- Membership form of `support_oneOf`. -/
@[simp]
theorem mem_support_oneOf_iff {gs : List (Unit → SPMF α)} (hne : gs ≠ []) {a : α} :
    a ∈ (oneOf gs hne).support ↔ ∃ g ∈ gs, a ∈ (g ()).support := by
  simp [support_oneOf]

/-- Membership form of `support_frequency`. A branch of weight `0` is unreachable, which is the
`0 < w` conjunct. -/
@[simp]
theorem mem_support_frequency_iff {gs : List (Nat × (Unit → SPMF α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) {a : α} :
    a ∈ (frequency gs h_pos).support ↔ ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support := by
  simp [support_frequency]

section pick
set_option linter.deprecated false

/-- `RandomChoice.pick x y` is `oneOf [x, y]`, so its support is the union of the two branches'. -/
@[simp]
theorem support_pick {x y : SPMF α} :
    (pick (fun () => x) (fun () => y)).support = x.support ∪ y.support := by
  unfold RandomChoice.pick
  rw [support_oneOf]
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left]

/-- Membership form of `support_pick`. -/
@[simp]
theorem mem_support_pick_iff {x y : SPMF α} {a : α} :
    a ∈ (pick (fun () => x) (fun () => y)).support ↔ a ∈ x.support ∨ a ∈ y.support := by
  simp

end pick

/-- The support of `elements xs` is exactly the elements of `xs`. Basalt's own proof. -/
@[simp]
theorem support_elements {xs : List α} (hne : xs ≠ []) :
    support (elements xs hne) = {x | x ∈ xs} := by
  simp only [elements, support_bind, support_map, support_choose]
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨⟨i, ⟨hi_gt, hi_lt⟩⟩, h_idx, ha⟩ := h
    obtain ⟨⟨n, ⟨hgt, hlt⟩⟩, ⟨h_lowerbound, h_upperbound⟩, hi⟩ := h_idx
    have h_pos : 0 < xs.length := by
      rw [List.length_pos_iff]
      assumption
    have h_lt : i < xs.length := by omega
    dsimp at ha
    simp only [mem_support_pure_iff] at ha
    apply List.mem_of_getElem (id (Eq.symm ha))
  · intro hmem
    obtain ⟨i, hlt, heq⟩ := List.mem_iff_getElem.mp hmem
    have hle : i ≤ xs.length - 1 := by omega
    exists ⟨i, ⟨by omega, hle⟩⟩
    constructor
    · exists ⟨i, ⟨by omega, hle⟩⟩
    · dsimp
      simp only [mem_support_pure_iff]
      apply (Eq.symm heq)

/-- Membership form of `support_elements`. -/
@[simp]
theorem mem_support_elements_iff {xs : List α} (hne : xs ≠ []) {a : α} :
    a ∈ support (elements xs hne) ↔ a ∈ xs := by
  simp [support_elements]

/-- `chooseNat lo hi` reaches exactly the naturals in `[lo, hi]`. Basalt's own proof. -/
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

/-- `chooseInt lo hi` reaches exactly the integers in `[lo, hi]`. Basalt's own proof. -/
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

/-- A coin reaches both outcomes exactly when its bias is strictly between 0 and 1; at a bias of 0 or
of 1 it reaches one. Basalt's own proof. -/
@[simp]
theorem support_coin {r : Rat} (h0 : 0 < r) (h1 : r < 1) :
    SPMF.support (RandomChoice.coin r) = {true, false} := by
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr h0
  have hden : r.num < (r.den : ℤ) := Rat.num_lt_denom_iff.mpr h1
  simp [coin, support_bind, support_choose, support_pure]
  ext b
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro _
    cases b <;> simp
  · intro h
    cases b
    · exists r.den - 1
      constructor
      · apply le_refl
      · right
        constructor <;> try rfl
        have hden_pos : 0 < r.den := r.den_pos
        omega
    · exists 0
      constructor
      · apply Nat.zero_le
      · left
        constructor <;> try rfl
        omega

/-- Membership form of `support_coin`. Basalt's own proof. -/
@[simp]
theorem mem_support_coin_iff {r : Rat} {b : Bool} (h0 : 0 < r) (h1 : r < 1) :
    b ∈ SPMF.support (RandomChoice.coin r) ↔ b = true ∨ b = false := by
  rw [support_coin h0 h1, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- `biasedOptionGen r g` reaches `none`, and it reaches `some a` exactly when `g` reaches `a`.
Basalt's own proof. -/
@[simp]
theorem support_biasedOptionGen {r : Rat} {g : SPMF α} (h0 : 0 < r) (h1 : r < 1) :
    support (biasedOptionGen r g) = {none} ∪ {some x | x ∈ g.support} := by
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr h0
  have hden : r.num < (r.den : ℤ) := Rat.num_lt_denom_iff.mpr h1
  have hden_pos : 0 < r.den := r.den_pos
  simp [biasedOptionGen, coin, support_bind, support_choose]
  ext a
  simp [Set.mem_setOf_eq]
  constructor <;> intros h
  · obtain ⟨a, hge, h⟩ := h
    rcases h with ⟨hle, rfl⟩ | ⟨hlt, ha⟩
    · left; rfl
    · obtain ⟨a', ⟨hmem, rfl⟩⟩ := ha
      right; exists a'
  · rcases h with rfl | ⟨x, ⟨hmem, rfl⟩⟩
    · exists r.den - 1
      constructor <;> try omega
      left
      constructor <;> try rfl
      omega
    · exists 0
      constructor <;> try omega
      right
      constructor
      · omega
      · exists x

/-- Membership form of `support_biasedOptionGen`. Basalt's own proof. -/
@[simp]
theorem mem_support_biasedOptionGen_iff {r : Rat} {g : SPMF α} {x : Option α}
    (h0 : 0 < r) (h1 : r < 1) :
    x ∈ (biasedOptionGen r g).support ↔ x = none ∨ (∃ a ∈ g.support, x = some a) := by
  unfold biasedOptionGen
  simp
  constructor <;> intro h
  · rcases h with ⟨hmem, rfl⟩ | ⟨hmem, a, ha, rfl⟩
    · left; rfl
    · right; exists a
  · rcases h with rfl | ⟨a, hmem, rfl⟩
    · left
      constructor
      · apply (mem_support_coin_iff h0 h1).mpr
        right; rfl
      · rfl
    · right
      constructor
      · apply (mem_support_coin_iff h0 h1).mpr
        left; rfl
      · exists a

/-- `optionGen` is `biasedOptionGen` at the bias `1/2`. Basalt's own proof. -/
@[simp]
theorem support_optionGen {g : SPMF α} :
    support (optionGen g) = {none} ∪ {some x | x ∈ g.support} := by
  unfold optionGen
  apply support_biasedOptionGen <;> norm_num

/-- Membership form of `support_optionGen`. Basalt's own proof. -/
@[simp]
theorem mem_support_optionGen_iff {g : SPMF α} {x : Option α} :
    x ∈ support (optionGen g) ↔ x = none ∨ (∃ a ∈ g.support, x = some a) := by
  unfold optionGen
  apply mem_support_biasedOptionGen_iff <;> norm_num

end SPMF
