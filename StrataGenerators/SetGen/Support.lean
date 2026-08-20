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
    support (choose lo hi h : Set (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) =
      {a | lo ≤ a.down.val ∧ a.down.val ≤ hi} := rfl

@[simp]
theorem mem_support_choose_iff :
    a ∈ support (choose lo hi h : Set (ULift {x : Nat // lo ≤ x ∧ x ≤ hi})) ↔
      lo ≤ a.down.val ∧ a.down.val ≤ hi := Iff.rfl

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
    support (oneOf gs hne) = {a | ∃ g ∈ gs, a ∈ g ()} := by
  simp only [oneOf]
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  . intro h
    obtain ⟨ ⟨i, ⟨hi_gt, hi_lt⟩⟩, h_idx, ha ⟩ := h
    obtain ⟨ ⟨n, ⟨hgt, hlt⟩⟩, ⟨h_lowerbound, h_upperbound⟩, hi ⟩ := h_idx
    have h_pos : 0 < gs.length := List.length_pos_iff.mpr hne
    have h_lt : i < gs.length := by omega
    refine ⟨ gs[i], ?_, ?_ ⟩
    . apply List.getElem_mem
    . dsimp at ha
      assumption
  . intros h
    obtain ⟨ g, hg, ha ⟩ := h
    obtain ⟨ i, hi, heq ⟩ := List.mem_iff_getElem.mp hg
    have hle : i ≤ gs.length - 1 := by omega
    refine ⟨ ⟨i, Nat.zero_le _, hle⟩, ?_, ?_ ⟩
    . exact ⟨⟨⟨i, Nat.zero_le _, hle⟩⟩, ⟨⟨Nat.zero_le _, hle⟩, rfl⟩⟩
    . dsimp
      subst heq
      assumption

/-- Any element in the support of `oneOf gs` is in the support of some
    generator in `gs` -/
@[simp]
theorem mem_support_oneOf_iff
    {gs : List (Unit → Set α)}
    (hne : gs ≠ []) :
    a ∈ support (oneOf gs hne) ↔ ∃ g ∈ gs, a ∈ support (g ()) := by
  rw [show support (oneOf gs hne) = _ from support_oneOf hne]
  simp only [Set.mem_setOf_eq, support]

/-- If `n < sum (fst <$> gs)`, then `Helpers.frequencySelect gs n` picks a sub-generator
    from `gs` that has non-zero weight `w` -/
private theorem frequencySelect_mem
    {gs : List (Nat × (Unit → Set α))}
    {n : Nat}
    (h : n < List.sum (List.map Prod.fst gs)) :
    ∃ w g, ⟨w, g⟩ ∈ gs ∧ 0 < w ∧ Helpers.frequencySelect gs n h = g () := by
  induction gs generalizing n with
  | nil => contradiction
  | cons hd tl ih =>
    unfold Helpers.frequencySelect
    obtain ⟨w, g⟩ := hd
    split
    · exact ⟨w, g, .head tl, by omega, rfl⟩
    · have h_remaining : n - w < List.sum (List.map Prod.fst tl) := by
        simp only [List.map_cons, List.sum_cons] at h; omega
      obtain ⟨w', g', hmem, hpos, heq⟩ := ih h_remaining
      exact ⟨w', g', List.mem_cons_of_mem _ hmem, hpos, heq⟩


/-- If a weighted generator `(w, g) ∈ gs` where the weight `w` is non-zero,
    then there exists `n` such that `Helpers.frequencySelect gs n` produces `g ()` -/
private theorem frequencySelect_n_exists
    {gs : List (Nat × (Unit → Set α))}
    {w : Nat} {g : Unit → Set α}
    (hmem : (w, g) ∈ gs)
    (hnonzero : 0 < w) :
    ∃ n, ∃ (h : n < List.sum (List.map Prod.fst gs)),
      Helpers.frequencySelect gs n h = g () := by
  induction gs with
  | nil => contradiction
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | h_tl
    · refine ⟨0, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]; omega
      · unfold Helpers.frequencySelect; simp [hnonzero]
    · obtain ⟨n, hn, heq⟩ := ih h_tl
      obtain ⟨w', _⟩ := hd
      refine ⟨w' + n, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]; omega
      · unfold Helpers.frequencySelect
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
  simp only [support, frequency, Helpers.frequencyAux, Set.mem_bind, Set.fmap_eq_image,
             Set.mem_image]
  constructor
  · rintro ⟨idx, ⟨n, hn, rfl⟩, ha⟩
    have h_lt : n.down.val < List.sum (List.map Prod.fst gs) := by
      exact Nat.lt_of_le_of_lt hn.2 (by omega)
    simp only [dif_pos h_lt] at ha
    obtain ⟨w, g, hmem, hpos, heq⟩ := frequencySelect_mem h_lt
    exact ⟨w, g, hmem, hpos, heq ▸ ha⟩
  · rintro ⟨w, g, hmem, hpos, ha⟩
    obtain ⟨n, hn_lt, hn_eq⟩ := frequencySelect_n_exists hmem hpos
    have hle : n ≤ (List.map Prod.fst gs).sum - 1 := by omega
    refine ⟨⟨n, Nat.zero_le _, hle⟩, ⟨⟨⟨n, Nat.zero_le _, hle⟩⟩, ⟨Nat.zero_le _, hle⟩, rfl⟩, ?_⟩
    simp only [dif_pos hn_lt, hn_eq]
    exact ha

/-- If the sum of weights in `gs` is non-zero, then the support of `frequency gs`
    is exactly the union of the support of the generators in `gs` with non-zero weights -/
@[simp]
theorem support_frequency
    {gs : List (Nat × (Unit → Set α))}
    (h_pos : 0 < List.sum (List.map Prod.fst gs)) :
    support (frequency gs h_pos) = {a | ∃ w g, ⟨ w, g ⟩ ∈ gs ∧ 0 < w ∧ a ∈ (g ())} := by
  ext a
  exact mem_support_frequency_iff h_pos


/-- The support of `elements xs` is exactly the elements of `xs` -/
@[simp]
theorem support_elements
    [Inhabited α]
    {xs : List α}
    (hne : xs ≠ []) :
    support (elements xs hne : Set α) = {a | a ∈ xs} := by
  simp only [elements, support_bind, support_map, support_choose]
  ext a
  dsimp only [Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨⟨i, ⟨hi_gt, hi_lt⟩⟩, h_idx, ha⟩ := h
    obtain ⟨⟨n, ⟨hgt, hlt⟩⟩, ⟨h_lowerbound, h_upperbound⟩, hi⟩ := h_idx
    have h_pos : 0 < xs.length := List.length_pos_iff.mpr hne
    have h_lt : i < xs.length := by omega
    dsimp at ha
    simp at ha
    exact List.mem_of_getElem (id (Eq.symm ha))
  · intro hmem
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    have hle : i ≤ xs.length - 1 := by omega
    exact ⟨⟨i, Nat.zero_le _, hle⟩,
      ⟨⟨⟨i, Nat.zero_le _, hle⟩⟩, ⟨⟨Nat.zero_le _, hle⟩, rfl⟩⟩,
      by dsimp; simp; exact heq.symm⟩

/-- `a` is in the support of `elements xs` if and only if `a ∈ xs` -/
@[simp]
theorem mem_support_elements_iff
    [Inhabited α]
    {xs : List α}
    (hne : xs ≠ []) :
    a ∈ support (elements xs hne : Set α) ↔ a ∈ xs := by
  rw [support_elements hne]
  rfl

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

-- ── vectorOf / listOfMaxLength support ────────────────────────────────
-- Ported to `SetGen.Set` from the `SPMF`-based lemmas in `Basalt.Combinators`.

/-- `vectorOf 0 g` produces the empty list. (`Basalt.Combinators` ships
    `vectorOf_succ` but not the base case, which we need below.) -/
@[simp] theorem vectorOf_zero [Gen G] (g : G α) : vectorOf 0 g = pure [] := rfl

/-- `xs ∈ support (vectorOf n g)` iff `xs` has length exactly `n` and every
    element is in `support g`. -/
@[simp]
theorem mem_support_vectorOf_iff {n : Nat} {g : Set α} {xs : List α} :
    xs ∈ support (vectorOf n g) ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ support g := by
  induction n generalizing xs with
  | zero =>
    simp only [vectorOf_zero, mem_support_pure_iff]
    constructor
    · rintro rfl; exact ⟨rfl, by simp⟩
    · rintro ⟨hlen, _⟩; exact List.length_eq_zero_iff.mp hlen
  | succ n ih =>
    rw [vectorOf_succ]
    simp only [mem_support_bind_iff, mem_support_pure_iff]
    constructor
    · rintro ⟨x, hx, tl, htl, rfl⟩
      obtain ⟨hlen, hmem⟩ := ih.mp htl
      refine ⟨by simp [hlen], ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hmem y hy
    · rintro ⟨hlen, hmem⟩
      match xs, hlen, hmem with
      | x :: tl, hlen, hmem =>
        refine ⟨x, hmem x List.mem_cons_self, tl, ?_, rfl⟩
        exact ih.mpr ⟨by simpa using hlen, fun y hy => hmem y (List.mem_cons_of_mem _ hy)⟩

theorem support_vectorOf {n : Nat} {g : Set α} :
    support (vectorOf n g) = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ support g} := by
  ext xs; exact mem_support_vectorOf_iff

/-- The support of `listOfMaxLength n g` is the set of all lists of length at
    most `n` whose every element is in `support g`. -/
theorem support_listOfMaxLength {n : Nat} {g : Set α} :
    support (listOfMaxLength n g) = {xs | xs.length ≤ n ∧ ∀ x ∈ xs, x ∈ support g} := by
  ext xs
  simp only [listOfMaxLength, mem_support_bind_iff, mem_support_map_iff,
             mem_support_choose_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, ⟨u, ⟨_, hk_hi⟩, rfl⟩, hxs⟩
    obtain ⟨hlen, hmem⟩ := mem_support_vectorOf_iff.mp hxs
    exact ⟨by omega, hmem⟩
  · rintro ⟨hlen, hmem⟩
    refine ⟨⟨xs.length, Nat.zero_le _, hlen⟩,
            ⟨⟨⟨xs.length, Nat.zero_le _, hlen⟩⟩, ⟨Nat.zero_le _, hlen⟩, rfl⟩,
            mem_support_vectorOf_iff.mpr ⟨rfl, hmem⟩⟩

/-- `xs ∈ support (listOfMaxLength n g)` iff `xs` has length at most `n` and every
    element is in `support g`. -/
@[simp]
theorem mem_support_listOfMaxLength_iff {n : Nat} {g : Set α} {xs : List α} :
    xs ∈ support (listOfMaxLength n g) ↔ xs.length ≤ n ∧ ∀ x ∈ xs, x ∈ support g := by
  rw [support_listOfMaxLength]; rfl

/-- Every element of a list in the support of `listOf g` is in `support g`.
    (`listOf` either returns `[]` or draws a head from `g` and recurses; the head
    is in `support g` and the tail is again in `support (listOf g)`.) This is the
    forward direction needed to read off per-character facts about a generated
    identifier's tail run. -/
theorem mem_support_listOf {g : Set α} {xs : List α}
    (hxs : xs ∈ support (listOf g)) :
    ∀ x ∈ xs, x ∈ support g := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
    rw [support, listOf] at hxs
    simp only [pick_mem_iff, Set.mem_bind, Set.mem_pure] at hxs
    rcases hxs with h | ⟨z, hz, zs, hzs, heq⟩
    · cases h
    · -- `y :: ys = z :: zs`, so `y = z ∈ support g` and `ys = zs ∈ support (listOf g)`
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hz
      · exact ih (by rw [support]; exact hzs) x hx

/-- Converse of `mem_support_listOf`. If each element of a list is in `support g`,
    then the list is in `support (listOf g)`.

    `listOf` does a `pick` between two branches: the branch for `[]`, and the branch
    that draws one element and then calls itself. To show that the generator reaches
    a given list, follow the recursive branch one time for each element, then follow
    the branch for `[]`. No branch puts a bound on the length. Therefore the support
    of `listOf g` is all of the lists over `support g`. `listOfMaxLength` is
    different, because it has a bound on the length.

    `support_listOf` in `Basalt.SPMF.Support` gives this direction for the `SPMF`
    interpretation. This lemma gives it for `SetGen.Set`. The support lemma for
    `genIdentName` needs this direction, because the run of characters after the
    first character of a name is a `listOf`. -/
theorem mem_support_listOf_of_forall {g : Set α} {xs : List α}
    (hxs : ∀ x ∈ xs, x ∈ support g) :
    xs ∈ support (listOf g) := by
  induction xs with
  | nil =>
    -- The `[]` branch of the `pick` returns `pure []`.
    rw [support, listOf]
    simp [pick_mem_iff]
  | cons y ys ih =>
    -- Follow the recursive branch: draw `y` from `g`, then `ys` from `listOf g`.
    rw [support, listOf]
    simp only [pick_mem_iff, Set.mem_bind, Set.mem_pure]
    refine Or.inr ⟨y, hxs y List.mem_cons_self, ys, ?_, rfl⟩
    exact ih (fun x hx => hxs x (List.mem_cons_of_mem y hx))

/-- **Support of `listOf`, in both directions.** `xs ∈ support (listOf g)` holds
    exactly when each element of `xs` is in `support g`. There is no bound on the
    length. The proof puts `mem_support_listOf` together with
    `mem_support_listOf_of_forall`. -/
theorem mem_support_listOf_iff {g : Set α} {xs : List α} :
    xs ∈ support (listOf g) ↔ ∀ x ∈ xs, x ∈ support g :=
  ⟨mem_support_listOf, mem_support_listOf_of_forall⟩

/-- Set form of `mem_support_listOf_iff`. -/
theorem support_listOf {g : Set α} :
    support (listOf g) = {xs | ∀ x ∈ xs, x ∈ support g} := by
  ext xs; exact mem_support_listOf_iff

-- ── coin / biasedOptionGen / optionGen support ───────────────────────────
-- Ported to `SetGen.Set` from the `SPMF`-based lemmas in `Basalt.SPMF.Support`.

/-- The support of `coin r` is all of `Bool` when the bias is strictly between 0
    and 1: `true` is reachable because `0 < r.num`, and `false` because
    `r.num < r.den`. The rational arithmetic is quarantined here, exactly as in
    the `SPMF` version. -/
@[simp]
theorem mem_support_coin_iff {r : Rat} {b : Bool} (h0 : 0 < r) (h1 : r < 1) :
    b ∈ support (RandomChoice.coin r : Set Bool) ↔ b = true ∨ b = false := by
  have hnum : (0 : Int) < r.num := Rat.intCast_pos.mp h0
  have hden : r.num < (r.den : Int) := by
    have h1' := h1
    rw [Rat.lt_iff] at h1'
    simpa using h1'
  have hden_pos : 0 < r.den := r.den_pos
  unfold RandomChoice.coin
  simp only [mem_support_bind_iff, mem_support_choose_iff, mem_support_ite_iff,
             mem_support_pure_iff]
  constructor
  · rintro _; cases b <;> simp
  · rintro _
    cases b
    · -- `false`: reachable via the maximal index `r.den - 1` (where `r.num ≤ idx`)
      refine ⟨⟨⟨r.den - 1, ?_, ?_⟩⟩, ⟨?_, ?_⟩, Or.inr ⟨?_, rfl⟩⟩ <;> dsimp only <;> omega
    · -- `true`: reachable via the minimal index `0` (where `idx < r.num`)
      refine ⟨⟨⟨0, ?_, ?_⟩⟩, ⟨?_, ?_⟩, Or.inl ⟨?_, rfl⟩⟩ <;> dsimp only <;> omega

/-- Support of `biasedOptionGen`: `none` is reachable (via the `false` coin
    branch, needing `r < 1`) and `some x` is reachable exactly when `x ∈ support g`
    (via the `true` branch, needing `0 < r`). -/
@[simp]
theorem mem_support_biasedOptionGen_iff {r : Rat} {g : Set α} {o : Option α}
    (h0 : 0 < r) (h1 : r < 1) :
    o ∈ support (biasedOptionGen r g) ↔ o = none ∨ ∃ a ∈ support g, o = some a := by
  unfold biasedOptionGen
  simp only [mem_support_bind_iff, mem_support_coin_iff h0 h1, mem_support_ite_iff,
             mem_support_pure_iff]
  constructor
  · rintro ⟨b, _, ho⟩
    rcases ho with ⟨_, a, ha, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨false, Or.inr rfl, Or.inr ⟨by simp, rfl⟩⟩
    · exact ⟨true, Or.inl rfl, Or.inl ⟨rfl, a, ha, rfl⟩⟩

/-- Support of `optionGen` (the unbiased 1/2 instance). Hypothesis-free: the
    `0 < 1/2` / `1/2 < 1` obligations discharge by `norm_num`. -/
@[simp]
theorem mem_support_optionGen_iff {g : Set α} {o : Option α} :
    o ∈ support (optionGen g) ↔ o = none ∨ ∃ a ∈ support g, o = some a := by
  unfold optionGen
  exact mem_support_biasedOptionGen_iff (r := 1/2) (by decide +kernel) (by decide +kernel)

end support

end SetGen
