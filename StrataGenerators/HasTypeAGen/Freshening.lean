import StrataGenerators.HasTypeAGen.Core

/-!
# Freshening coverage lemmas

Supporting lemmas for `freshenBoundVars` (`StrataGenerators/HasTypeAGen/Core.lean`),
culminating in `freshenBoundVars_disjoint`: the freshened bound variables and the
free variables of the freshened body are disjoint from the caller's in-use set.

The chain of reasoning is:

1. `freshNameSupply_length` — the supply has `26 * (n / 26 + 2)` names, hence `≥ n`.
2. `freshNameSupply_nodup` — the supply is duplicate-free. This is the string/char
   combinatorial core: names are `⟨letter⟩ ++ suffix`, and both components are
   recoverable from the name (`mkName_inj`), so distinct `(letter, suffix)` pairs
   give distinct names.
3. `freshNames_covers` — filtering the (`Nodup`) supply by `· ∉ allTypeVarsInUse`
   leaves at least `conflictingTyVars.length` names, so the `zip` building the
   renaming substitution truncates nothing.
4. `freshenBoundVars_disjoint` — the payoff.

This file is deliberately kept in its own module (rather than appended to
`Core.lean`) and imports nothing beyond `HasTypeAGen.Core`; in particular no
Mathlib and no `Batteries.Data.List.Basic` — see the import note atop
`StrataGenerators/HasTypeAGen.lean` about the `List.Forall₂` clash.
-/

open Lambda

namespace Freshening

-- ── Generic list helpers ──────────────────────────────────────────────
-- `List.Nodup` is *definitionally* `List.Pairwise (· ≠ ·)` here
-- (`List.nodup_iff_pairwise_ne` is `Iff.rfl`), which the first lemma exploits.

/-- `filter` preserves `Nodup`. (Lean core has no `List.Nodup.filter`.) -/
theorem nodup_filter {α} (p : α → Bool) {l : List α} (h : l.Nodup) :
    (l.filter p).Nodup := List.Pairwise.filter (R := (· ≠ ·)) p h

/-- `map` preserves `Nodup` when the function is injective on the list. -/
theorem nodup_map_of_injOn {α β} {f : α → β} {l : List α}
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hnotin, hrest⟩ := h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy) hrest⟩
    intro hmem
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
    exact hnotin (hinj a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hfb.symm ▸ hb)

/-- Hand-rolled `Nodup` for `flatMap` (Lean core has no `List.nodup_flatMap`):
    the index list is `Nodup`, each block is `Nodup`, and distinct indices give
    disjoint blocks. -/
theorem nodup_flatMap {α β} {f : α → List β} {l : List α}
    (hl : l.Nodup)
    (hb : ∀ a ∈ l, (f a).Nodup)
    (hd : ∀ a ∈ l, ∀ a' ∈ l, a ≠ a' → ∀ b ∈ f a, b ∉ f a') :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hnotin, hrest⟩ := hl
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hb a List.mem_cons_self, ?_, ?_⟩
    · exact ih hrest (fun x hx => hb x (List.mem_cons_of_mem _ hx))
        (fun x hx y hy hne => hd x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hne)
    · intro b hbmem b' hb'mem
      obtain ⟨a', ha'mem, hb'⟩ := List.mem_flatMap.mp hb'mem
      have hne : a ≠ a' := fun heq => hnotin (heq ▸ ha'mem)
      intro heq
      exact hd a List.mem_cons_self a' (List.mem_cons_of_mem _ ha'mem) hne b hbmem (heq ▸ hb')

-- ── String / Char / Nat.repr injectivity ──────────────────────────────

/-- A single-character string prepended to a suffix determines both components. -/
theorem mkName_inj {c c' : Char} {s s' : String}
    (h : String.append (Char.toString c) s = String.append (Char.toString c') s') :
    c = c' ∧ s = s' := by
  have h' : (Char.toString c).toList ++ s.toList = (Char.toString c').toList ++ s'.toList := by
    rw [← String.toList_append, ← String.toList_append]
    exact congrArg String.toList h
  rw [show (Char.toString c).toList = [c] from String.toList_singleton c,
      show (Char.toString c').toList = [c'] from String.toList_singleton c'] at h'
  simp only [List.cons_append, List.cons.injEq] at h'
  exact ⟨h'.1, String.toList_inj.mp h'.2⟩

theorem singleton_inj {a b : Char} (h : String.singleton a = String.singleton b) : a = b := by
  have := String.toList_inj.mpr h
  rw [String.toList_singleton, String.toList_singleton] at this
  exact (List.cons.inj this).1

/-- `Char.ofNat (97 + ·)` is injective on `[0, 26)` — the lowercase alphabet. -/
theorem char_ofNat_inj {a b : Nat} (ha : a < 26) (hb : b < 26)
    (h : Char.ofNat (97 + a) = Char.ofNat (97 + b)) : a = b := by
  have key : ∀ a < 26, ∀ b < 26, Char.ofNat (97 + a) = Char.ofNat (97 + b) → a = b := by decide
  exact key a ha b hb h

theorem digitChar_inj {a b : Nat} (ha : a < 10) (hb : b < 10)
    (h : Nat.digitChar a = Nat.digitChar b) : a = b := by
  have key : ∀ a < 10, ∀ b < 10, Nat.digitChar a = Nat.digitChar b → a = b := by decide
  exact key a ha b hb h

/-- Decimal representation is injective. Needed so that distinct numeric suffixes
    give distinct suffix strings. -/
theorem repr_inj : ∀ (n m : Nat), n.repr = m.repr → n = m := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m h
    rcases Nat.lt_or_ge n 10 with hn | hn <;> rcases Nat.lt_or_ge m 10 with hm | hm
    · rw [Nat.repr_of_lt hn, Nat.repr_of_lt hm] at h
      exact digitChar_inj hn hm (singleton_inj h)
    · -- `n < 10 ≤ m`: the representations have different lengths.
      have h1 : n.repr.length ≤ 1 := (Nat.length_repr_le_iff (by omega)).mpr (by omega)
      have h2 : ¬ (m.repr.length ≤ 1) := fun hc =>
        absurd ((Nat.length_repr_le_iff (k := 1) (by omega)).mp hc) (by omega)
      rw [h] at h1; omega
    · have h1 : m.repr.length ≤ 1 := (Nat.length_repr_le_iff (by omega)).mpr (by omega)
      have h2 : ¬ (n.repr.length ≤ 1) := fun hc =>
        absurd ((Nat.length_repr_le_iff (k := 1) (by omega)).mp hc) (by omega)
      rw [← h] at h1; omega
    · rw [Nat.repr_of_ge hn, Nat.repr_of_ge hm] at h
      have hdiv : (n / 10).repr = (m / 10).repr := by
        have h' : (n/10).repr.toList ++ (String.singleton (Nat.digitChar (n % 10))).toList
                = (m/10).repr.toList ++ (String.singleton (Nat.digitChar (m % 10))).toList := by
          rw [← String.toList_append, ← String.toList_append, h]
        exact String.toList_inj.mp
          (List.append_inj' h' (by simp [String.toList_singleton])).1
      have hq : n / 10 = m / 10 := ih (n/10) (Nat.div_lt_self (by omega) (by omega)) (m/10) hdiv
      have hmod : n % 10 = m % 10 := by
        rw [hq] at h
        exact digitChar_inj (by omega) (by omega)
          (singleton_inj ((String.append_right_inj _).mp h))
      omega

theorem toString_succ_inj {i j : Nat} (h : toString (i + 1) = toString (j + 1)) : i = j := by
  have := repr_inj (i + 1) (j + 1) (by simpa using h)
  omega

-- ── `freshNameSupply` structure ───────────────────────────────────────

/-- The block of 26 names contributed by one suffix: `a<suffix>, …, z<suffix>`. -/
def block (suffix : String) : List TyIdentifier :=
  (List.range 26).map (fun c => String.append (Char.toString (Char.ofNat (97 + c))) suffix)

/-- The list of suffixes used by `freshNameSupply n`: `"" , "1", …, "n/26+1"`. -/
def suffixes (n : Nat) : List String :=
  "" :: (List.range (n / 26 + 1)).map (fun i => toString (i + 1))

/-- `freshNameSupply` as a `flatMap` of 26-name blocks over the suffix list.
    The inner `flatMap` of `Core.lean` emits singletons, so it is really a `map`. -/
theorem freshNameSupply_eq (n : Nat) :
    freshNameSupply n = (suffixes n).flatMap block := by
  unfold freshNameSupply block suffixes
  show List.flatMap (fun suffix =>
        List.flatMap (fun c => [(Char.ofNat (97 + c)).toString.append suffix]) (List.range 26))
      ("" :: List.map (fun i => toString (i + 1)) (List.range (n / 26 + 1))) = _
  congr 1

theorem block_length (suffix : String) : (block suffix).length = 26 := by
  simp [block]

theorem block_nodup (suffix : String) : (block suffix).Nodup := by
  unfold block
  apply nodup_map_of_injOn _ List.nodup_range
  intro a ha b hb heq
  rw [List.mem_range] at ha hb
  exact char_ofNat_inj ha hb (mkName_inj heq).1

/-- Blocks for distinct suffixes are disjoint: the suffix is recoverable from a name. -/
theorem block_disjoint {s s' : String} (hne : s ≠ s') :
    ∀ x ∈ block s, x ∉ block s' := by
  intro x hx hx'
  unfold block at hx hx'
  obtain ⟨c, _, hc⟩ := List.mem_map.mp hx
  obtain ⟨c', _, hc'⟩ := List.mem_map.mp hx'
  exact hne (mkName_inj (hc.trans hc'.symm)).2

-- ── Counting: filtering a `Nodup` list by "not in `s`" ────────────────

/-- Filtering a **duplicate-free** list `l` by `· ∉ s` removes at most `s.length`
    elements. `Nodup` is essential: each element of `s` can knock out at most one
    element of `l`. -/
theorem length_filter_notMem_ge {α} [DecidableEq α] (l s : List α) (h : l.Nodup) :
    l.length - s.length ≤ (l.filter (fun x => decide (x ∉ s))).length := by
  have hsplit := List.length_eq_countP_add_countP (fun x => decide (x ∉ s)) (l := l)
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at hsplit
  -- The discarded elements all lie in `s`, and are distinct, so there are `≤ s.length` of them.
  have hsub : (l.filter (fun a => decide ¬(decide (a ∉ s) = true))) ⊆ s := by
    intro x hx
    rw [List.mem_filter] at hx
    simpa using hx.2
  have := List.subset_nodup_length (nodup_filter _ h) hsub
  omega

-- ── `zip`-based lookup coverage ───────────────────────────────────────

/-- A successful `lookup` witnesses membership of the whole pair. -/
theorem lookup_mem {α β} [BEq α] [LawfulBEq α] (l : List (α × β)) (a : α) (b : β)
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    rw [List.lookup_cons] at h
    by_cases hk : a == k
    · simp only [hk, Option.some.injEq] at h
      have : a = k := by simpa using hk
      subst this; subst h; exact List.mem_cons_self
    · simp only [hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- `lookup` commutes with mapping over the values of an association list. -/
theorem lookup_map_snd {α β γ} [BEq α] (f : β → γ) (l : List (α × β)) (a : α) :
    (l.map (fun p => (p.1, f p.2))).lookup a = (l.lookup a).map f := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.lookup_cons]
    by_cases hk : a == k
    · simp [hk]
    · simp [hk, ih]

/-- If the key list is no longer than the value list, `zip` truncates no key:
    every key has a `lookup`, and the result comes from the value list. -/
theorem lookup_zip_of_length_le {α β} [BEq α] [LawfulBEq α]
    (l1 : List α) (l2 : List β) (hlen : l1.length ≤ l2.length) (v : α) (hv : v ∈ l1) :
    ∃ w ∈ l2, (l1.zip l2).lookup v = some w := by
  induction l1 generalizing l2 with
  | nil => simp at hv
  | cons a rest ih =>
    cases l2 with
    | nil => simp at hlen
    | cons b l2rest =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      by_cases hab : v == a
      · exact ⟨b, List.mem_cons_self, by simp [hab]⟩
      · simp only [hab]
        have hv' : v ∈ rest := by
          rcases List.mem_cons.mp hv with h | h
          · exact absurd (by simp [h]) hab
          · exact h
        obtain ⟨w, hw, hlk⟩ := ih l2rest (by simp at hlen; omega) hv'
        exact ⟨w, List.mem_cons_of_mem _ hw, hlk⟩

-- ── Substitution plumbing ─────────────────────────────────────────────

/-- `HMap.find?` on a *reversed* association list is the first-match lookup on the original:
    `HMap.ofList` keeps the *last* binding for a key, which is the *first* binding in the
    reversed list — exactly what `List.lookup` returns. This is the bridge every
    construction that has to hand an assoc list to an opaque `HMap` scope goes through. -/
theorem find?_ofList_reverse {α β} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (l : List (α × β)) (x : α) :
    Strata.Util.HMap.find? (Strata.Util.HMap.ofList l.reverse) x = l.lookup x := by
  simp only [Strata.Util.HMap.find?, Strata.Util.HMap.ofList, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.ofList_eq_insertMany_empty, Std.HashMap.getElem?_insertMany_list,
    Std.HashMap.getElem?_empty, Option.or_none]
  rw [List.findSomeRev?_eq_findSome?_reverse, List.reverse_reverse]
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.findSome?_cons, List.lookup_cons]
    by_cases hk : k = x
    · subst hk; simp
    · have h1 : (k == x) = false := by simp [hk]
      have h2 : (x == k) = false := by simp [Ne.symm hk]
      simp only [h1, Bool.false_eq_true, if_false, h2, ih]

/-- `HMaps.find?` on a `substScope` is just `List.lookup` on the association list
    it was built from. `substScope` reverses before `HMap.ofList` precisely so
    that the binding the hash map keeps (the *last* one for a key) is the binding
    `List.lookup` finds (the *first* one). -/
theorem find?_substScope_eq_lookup (m : List (TyIdentifier × LMonoTy)) (x : TyIdentifier) :
    Strata.Util.HMaps.find? (substScope m) x = m.lookup x := by
  rw [substScope, Strata.Util.HMaps.find?_single_scope]
  exact find?_ofList_reverse m x

/-- Each element's free type variables are among the whole list's.

    Upstream proves this as `LMonoTys.freeVars_mem_subset`, but that lives in
    `Strata.DL.Lambda.LTyProps`, whose theorems are not `public` under Strata's
    module system and hence invisible here, so we reprove it. -/
theorem freeVars_mem_of_mem {ty : LMonoTy} {tys : List LMonoTy} (ht : ty ∈ tys)
    {v : TyIdentifier} (hv : v ∈ LMonoTy.freeVars ty) : v ∈ LMonoTys.freeVars tys := by
  induction tys with
  | nil => cases ht
  | cons x rest ih =>
    rw [LMonoTys.freeVars_of_cons, List.mem_append]
    rcases List.mem_cons.mp ht with heq | hmem
    · exact Or.inl (heq ▸ hv)
    · exact Or.inr (ih hmem)

/-- If `v` is free in a list of monotypes, some element of the list has it free.

    Upstream proves this as `LMonoTys.freeVars_exists`, in the non-`public`
    `Strata.DL.Lambda.LTyProps`, so it is reproved here (like `freeVars_mem_of_mem`). -/
theorem exists_of_freeVars_mem {v : TyIdentifier} {tys : List LMonoTy}
    (hv : v ∈ LMonoTys.freeVars tys) : ∃ ty ∈ tys, v ∈ LMonoTy.freeVars ty := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons t rest ih =>
    rw [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    rcases hv with h | h
    · exact ⟨t, List.mem_cons_self, h⟩
    · obtain ⟨ty, hty, hv'⟩ := ih h
      exact ⟨ty, List.mem_cons_of_mem _ hty, hv'⟩

/-- Every free variable of `LMonoTy.subst S mty` either comes from a value that `S`
    maps something to, or is a free variable of `mty` that `S` leaves alone. -/
theorem freeVars_subst_cases (S : Subst) (mty : LMonoTy) (tv : TyIdentifier)
    (h : tv ∈ LMonoTy.freeVars (LMonoTy.subst S mty)) :
    (∃ x t, Strata.Util.HMaps.find? S x = some t ∧ tv ∈ LMonoTy.freeVars t)
      ∨ (tv ∈ LMonoTy.freeVars mty ∧ Strata.Util.HMaps.find? S tv = none) := by
  induction mty with
  | ftvar x =>
    rw [LMonoTy.subst_unfold] at h
    simp only at h
    generalize hf : Strata.Util.HMaps.find? S x = fo at h
    cases fo with
    | none =>
      simp only [LMonoTy.freeVars, List.mem_singleton] at h
      subst h
      exact Or.inr ⟨by simp [LMonoTy.freeVars], hf⟩
    | some t => exact Or.inl ⟨x, t, hf, h⟩
  | bitvec n =>
    rw [LMonoTy.subst_unfold] at h
    simp only [LMonoTy.freeVars] at h
    exact absurd h (by simp)
  | tcons name args ih =>
    rw [LMonoTy.subst_unfold] at h
    simp only [LMonoTy.freeVars] at h
    have hex : ∃ a ∈ args, tv ∈ LMonoTy.freeVars (LMonoTy.subst S a) := by
      clear ih
      -- Restate `h` in the `map`-shaped form that `subst_unfold` now produces (and
      -- drop the original), so the inner induction hypothesis is a one-argument
      -- statement about `arest`.
      have hfv : tv ∈ LMonoTys.freeVars (args.map (LMonoTy.subst S)) := h
      clear h
      induction args with
      | nil => simp [LMonoTys.freeVars] at hfv
      | cons a arest iha =>
        simp only [List.map_cons, LMonoTys.freeVars_of_cons, List.mem_append] at hfv
        rcases hfv with ha | hrest
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨a', hm, hf⟩ := iha hrest
          exact ⟨a', List.mem_cons_of_mem _ hm, hf⟩
    obtain ⟨a, ham, haf⟩ := hex
    rcases ih a ham haf with hl | ⟨hb, hn⟩
    · exact Or.inl hl
    · refine Or.inr ⟨?_, hn⟩
      simp only [LMonoTy.freeVars]
      exact freeVars_mem_of_mem ham hb

theorem suffixes_nodup (n : Nat) : (suffixes n).Nodup := by
  unfold suffixes
  rw [List.nodup_cons]
  refine ⟨?_, nodup_map_of_injOn ?_ List.nodup_range⟩
  · intro hmem
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hmem
    -- `toString (i+1)` is nonempty, so it cannot be `""`.
    have : (toString (i + 1)).length = 0 := by rw [hi]; rfl
    have hpos : 0 < (Nat.repr (i + 1)).length := Nat.length_repr_pos
    simp only [Nat.toString_eq_repr] at this
    omega
  · intro a _ b _ heq
    exact toString_succ_inj heq

end Freshening

-- ── The four target lemmas ────────────────────────────────────────────

open Freshening in
/-- The supply contains `26 * (n / 26 + 2)` names — in particular at least `n`. -/
theorem freshNameSupply_length (n : Nat) :
    (freshNameSupply n).length = 26 * (n / 26 + 2) := by
  rw [freshNameSupply_eq, List.length_flatMap]
  unfold suffixes
  simp only [List.map_cons, List.map_map, List.sum_cons]
  rw [show (List.map ((fun s => (block s).length) ∘ fun i => toString (i + 1))
        (List.range (n / 26 + 1))) = List.replicate (n / 26 + 1) 26 from ?_]
  · simp only [List.sum_replicate_nat, block_length]
    omega
  · rw [List.eq_replicate_iff]
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hb
    exact hi ▸ block_length _

/-- Corollary of `freshNameSupply_length`: the supply has at least `n` names. -/
theorem freshNameSupply_length_ge (n : Nat) : n ≤ (freshNameSupply n).length := by
  rw [freshNameSupply_length]; omega

open Freshening in
/-- The supply is duplicate-free. -/
theorem freshNameSupply_nodup (n : Nat) : (freshNameSupply n).Nodup := by
  rw [freshNameSupply_eq]
  refine nodup_flatMap (suffixes_nodup n) (fun s _ => block_nodup s) ?_
  intro s _ s' _ hne
  exact block_disjoint hne

open Freshening in
/-- **Coverage.** Filtering the (duplicate-free) supply by "not already in use"
    still leaves at least one fresh name per conflicting bound variable, so the
    `zip` in `freshenBoundVars` truncates nothing.

    The quantities here mirror `freshenBoundVars` exactly (`Core.lean`). -/
theorem freshNames_covers (boundVars varsAlreadyInUse : List TyIdentifier) :
    let conflictingTyVars := boundVars.filter (· ∈ varsAlreadyInUse)
    let allTypeVarsInUse := varsAlreadyInUse ++ conflictingTyVars
    let numFreshNames := allTypeVarsInUse.length + conflictingTyVars.length + 1
    conflictingTyVars.length ≤
      ((freshNameSupply numFreshNames).filter (· ∉ allTypeVarsInUse)).length := by
  intro conflictingTyVars allTypeVarsInUse numFreshNames
  have hlen := freshNameSupply_length_ge numFreshNames
  have hkey := length_filter_notMem_ge (freshNameSupply numFreshNames) allTypeVarsInUse
    (freshNameSupply_nodup numFreshNames)
  show conflictingTyVars.length ≤ _
  have hnum : numFreshNames = allTypeVarsInUse.length + conflictingTyVars.length + 1 := rfl
  omega

open Freshening in
/-- The disjointness argument for `freshenBoundVars`, abstracted over the actual
    fresh-name list. Only two properties of `freshNames` matter: its members avoid
    `varsInUse`, and it is long enough to cover every conflicting bound variable.

    `hclosed` is needed for the second conjunct: a free variable of `monoTy` outside
    `boundVars` would survive the renaming unchanged and could collide. -/
private theorem disjoint_core (boundVars varsInUse freshNames : List TyIdentifier) (monoTy : LMonoTy)
    (hclosed : ∀ v ∈ monoTy.freeVars, v ∈ boundVars)
    (hfnotin : ∀ w ∈ freshNames, w ∉ varsInUse)
    (hcov : (boundVars.filter (fun x => decide (x ∈ varsInUse))).length ≤ freshNames.length) :
    (∀ v ∈ boundVars.map (fun v =>
        (((boundVars.filter (fun x => decide (x ∈ varsInUse))).zip freshNames).lookup v).getD v),
        v ∉ varsInUse) ∧
    (∀ v ∈ (LMonoTy.subst
        (substScope (((boundVars.filter (fun x => decide (x ∈ varsInUse))).zip freshNames).map
          (fun p => (p.1, LMonoTy.ftvar p.2)))) monoTy).freeVars, v ∉ varsInUse) := by
  have hmap : ∀ v ∈ boundVars,
      (((boundVars.filter (fun x => decide (x ∈ varsInUse))).zip freshNames).lookup v).getD v
        ∉ varsInUse := by
    intro v hv
    by_cases hvin : v ∈ varsInUse
    · have hvconf : v ∈ boundVars.filter (fun x => decide (x ∈ varsInUse)) :=
        List.mem_filter.mpr ⟨hv, by simpa using hvin⟩
      obtain ⟨w, hw, hlk⟩ := lookup_zip_of_length_le _ _ hcov v hvconf
      rw [hlk]
      exact hfnotin w hw
    · cases hlk : (((boundVars.filter (fun x => decide (x ∈ varsInUse))).zip freshNames).lookup v) with
      | none => simpa using hvin
      | some w =>
        simp only [Option.getD_some]
        exact hfnotin w (List.of_mem_zip (lookup_mem _ _ _ hlk)).2
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨b, hb, hbv⟩ := List.mem_map.mp hv
    exact hbv ▸ hmap b hb
  · rcases freeVars_subst_cases _ _ _ hv with ⟨x, t, hfind, htv⟩ | ⟨hfv, hnone⟩
    · rw [find?_substScope_eq_lookup, lookup_map_snd] at hfind
      cases hlk : (((boundVars.filter (fun x => decide (x ∈ varsInUse))).zip freshNames).lookup x) with
      | none => rw [hlk] at hfind; exact absurd hfind (by simp)
      | some w =>
        rw [hlk] at hfind
        simp only [Option.map_some, Option.some.injEq] at hfind
        have hwfresh : w ∈ freshNames := (List.of_mem_zip (lookup_mem _ _ _ hlk)).2
        rw [← hfind] at htv
        simp only [LMonoTy.freeVars, List.mem_singleton] at htv
        exact htv ▸ hfnotin w hwfresh
    · rw [find?_substScope_eq_lookup, lookup_map_snd] at hnone
      have hlknone : (((boundVars.filter (fun x => decide (x ∈ varsInUse))).zip freshNames).lookup v) = none := by
        cases hlk : (((boundVars.filter (fun x => decide (x ∈ varsInUse))).zip freshNames).lookup v) with
        | none => rfl
        | some w => rw [hlk] at hnone; exact absurd hnone (by simp)
      have := hmap v (hclosed v hfv)
      rw [hlknone] at this
      simpa using this

open Freshening in
/-- **Main result.** The bound variables and body produced by `freshenBoundVars`
    are both disjoint from the caller's in-use variable set. -/
theorem freshenBoundVars_disjoint
    (boundVars : List TyIdentifier) (monoTy : LMonoTy) (varsAlreadyInUse : List TyIdentifier)
    (hclosed : ∀ v ∈ monoTy.freeVars, v ∈ boundVars)
    (freshBoundVars : List TyIdentifier) (freshMonoTy : LMonoTy)
    (hfresh : freshenBoundVars boundVars monoTy varsAlreadyInUse = (freshBoundVars, freshMonoTy)) :
    (∀ v ∈ freshBoundVars, v ∉ varsAlreadyInUse) ∧
    (∀ v ∈ freshMonoTy.freeVars, v ∉ varsAlreadyInUse) := by
  unfold freshenBoundVars at hfresh
  simp only [Prod.mk.injEq] at hfresh
  obtain ⟨hbv, hmt⟩ := hfresh
  subst hbv; subst hmt
  have hcov := freshNames_covers boundVars varsAlreadyInUse
  simp only at hcov
  refine disjoint_core boundVars varsAlreadyInUse _ monoTy hclosed ?_ hcov
  intro w hw
  have := (List.mem_filter.mp hw).2
  simp only [decide_eq_true_eq] at this
  intro hc
  exact this (List.mem_append_left _ hc)

-- Axiom audit — all four results use only the standard axioms (verified output):
--   'freshNameSupply_length'       depends on axioms: [propext, Quot.sound]
--   'freshNameSupply_nodup'        depends on axioms: [propext, Classical.choice, Quot.sound]
--   'freshNames_covers'            depends on axioms: [propext, Classical.choice, Quot.sound]
--   'freshenBoundVars_disjoint'    depends on axioms: [propext, Classical.choice, Quot.sound]
-- Uncomment to re-check:
-- #print axioms freshNameSupply_length
-- #print axioms freshNameSupply_nodup
-- #print axioms freshNames_covers
-- #print axioms freshenBoundVars_disjoint
