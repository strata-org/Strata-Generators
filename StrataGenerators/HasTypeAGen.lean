import StrataGenerators.SetGen
import StrataGenerators.HasTypeAGen.Core
import StrataGenerators.HasTypeAGen.IndirSupport
-- The coverage lemmas for `freshenBoundVars`. `schemeInstAt_freshening_disjoint` below uses them to
-- derive the well-formedness conditions of `SchemeInstAt`. The imported file imports only
-- `HasTypeAGen.Core`, so there is no cycle.
import StrataGenerators.HasTypeAGen.Freshening
import Strata.DL.Lambda.LTyUnify
-- `LTyUnifyProps` gives the substitution lemmas of Strata. Each result below about the unifier
-- states *matching* completeness, and not most generality. Nothing here proves that
-- `Constraints.unify` gives a most general unifier, and the substitution that it gives therefore has
-- the name `Su` and not `mgu`.
import Strata.DL.Lambda.LTyUnifyProps
-- This file does NOT import `Batteries.Data.List.Basic`. That module defines its own
-- `List.Forall₂`, which collides with the `List.Forall₂` of Strata on the generated
-- `List.Forall₂.below.casesOn` symbol. Strata and the Lean core library give each `List` lemma that
-- this file uses.

-- Mathlib marks `Nat.le_refl` with `@[refl]`. This attribute does the same, so that the file needs
-- no dependency on Mathlib.
attribute [refl] Nat.le_refl

open Lambda RandomChoice ArbNat ArbChar ArbString SetGen

/-!
# A generator of well-typed terms that satisfy `HasTypeA`

This module holds a random generator of well-typed Strata `LExpr` terms. Each generated term satisfies
the `HasTypeA` relation. The generator uses the `SetGen` semantics of Basalt. The `LExprParams` are
`LExprParams.mono ⟨Unit, Unit⟩`, which is unit metadata, unit identifier metadata and monotype
annotations.

## Contents

- `HasTypeA'`: the typing judgement `HasTypeA`, at these `LExprParams`.
- `genLMonoTy`: a generator of a monotype.
- `genLMonoTy_mem_*`: the lemmas about the types that `genLMonoTy` can generate.
- `genLExpr`: a generator of a well-typed `LExpr` at a given type and depth budget.
- The soundness of `genLExpr`, which says that each generated expression is well-typed.
- An `SetGen.IsSoundAndComplete` instance for `genLMonoTy`.
-/

-- ── bvarsOfType spec ──────────────────────────────────────────────────

/-- The result of `bvarsOfType.go` holds the index `i` if and only if `bctx` has the type `τ` at the
    position `i - base`. -/
private theorem bvarsOfType_go_spec (τ : LMonoTy) :
    ∀ (bctx : BVarCtx) (base i : Nat),
      i ∈ bvarsOfType.go τ bctx base ↔
        ∃ k, k < bctx.length ∧ i = base + k ∧ bctx[k]? = some τ := by
  intro bctx
  induction bctx with
  | nil => simp [bvarsOfType.go]
  | cons τ' rest ih =>
    intro base i
    simp only [bvarsOfType.go]
    split
    · rename_i heq
      have hτeq : τ' = τ := beq_iff_eq.mp heq
      simp only [List.mem_cons]; rw [ih]
      constructor
      · rintro (rfl | ⟨k, hk, rfl, hget⟩)
        · exact ⟨0, by simp, by omega, by simp [hτeq]⟩
        · exact ⟨k + 1, by simp; omega, by omega,
            by simp [List.getElem?_cons_succ]; exact hget⟩
      · rintro ⟨k, hk, hx, hget⟩
        match k with
        | 0 => simp at hget; left; omega
        | k + 1 =>
          right; exact ⟨k, by simp at hk; omega, by omega,
            by simp [List.getElem?_cons_succ] at hget; exact hget⟩
    · rename_i heq
      have hτne : τ' ≠ τ := fun h => absurd (beq_iff_eq.mpr h) heq
      rw [ih]
      constructor
      · rintro ⟨k, hk, rfl, hget⟩
        exact ⟨k + 1, by simp; omega, by omega,
          by simp [List.getElem?_cons_succ]; exact hget⟩
      · rintro ⟨k, hk, hx, hget⟩
        match k with
        | 0 =>
          simp at hget
          exact absurd hget hτne
        | k + 1 =>
          exact ⟨k, by simp at hk; omega, by omega,
            by simp [List.getElem?_cons_succ] at hget; exact hget⟩

/-- `i ∈ bvarsOfType bctx τ` iff `bctx[i]? = some τ`. -/
private theorem bvarsOfType_mem_iff (bctx : BVarCtx) (τ : LMonoTy) (i : Nat) :
    i ∈ bvarsOfType bctx τ ↔ bctx[i]? = some τ := by
  unfold bvarsOfType
  rw [bvarsOfType_go_spec]
  constructor
  · rintro ⟨k, _, rfl, hget⟩; simpa using hget
  · intro hget
    have hlt : i < bctx.length := by
      rw [List.getElem?_eq_some_iff] at hget; exact hget.1
    exact ⟨i, hlt, by omega, hget⟩

-- ── pick* support characterization ────────────────────────────────────

private theorem list_map_ne_nil_of_length_pos {α β : Type} {xs : List α} {f : α → β}
    (h : xs.length > 0) : xs.map f ≠ [] := by
  intro heq
  have : (xs.map f).length = 0 := by rw [heq]; rfl
  rw [List.length_map] at this
  omega

/-- The support of `pickBVar` holds an expression if and only if the expression is `.bvar () i` for an
    index `i` of `bvarsOfType bctx τ`. -/
private theorem mem_support_pickBVar_iff {bctx : BVarCtx} {τ : LMonoTy}
    {hv : (bvarsOfType bctx τ).length > 0} {e : LExpr'} :
    e ∈ (pickBVar (G := SetGen.Set) bctx τ hv) ↔
      ∃ i ∈ bvarsOfType bctx τ, e = .bvar () i := by
  change e ∈ SetGen.support (pickBVar (G := SetGen.Set) bctx τ hv) ↔ _
  simp only [pickBVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos hv), List.mem_map]
  constructor
  · rintro ⟨i, hmem, rfl⟩; exact ⟨i, hmem, rfl⟩
  · rintro ⟨i, hmem, rfl⟩; exact ⟨i, hmem, rfl⟩

/-- The support of `pickFVar` holds an expression if and only if the expression is
    `.fvar () ⟨name, ()⟩ (some τ)` for a name of `fvarsOfType fctx τ`. -/
private theorem mem_support_pickFVar_iff {fctx : FVarCtx} {τ : LMonoTy}
    {hv : (fvarsOfType fctx τ).length > 0} {e : LExpr'} :
    e ∈ (pickFVar (G := SetGen.Set) fctx τ hv) ↔
      ∃ name ∈ fvarsOfType fctx τ, e = .fvar () ⟨name, ()⟩ (some τ) := by
  change e ∈ SetGen.support (pickFVar (G := SetGen.Set) fctx τ hv) ↔ _
  simp only [pickFVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos hv), List.mem_map]
  constructor
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩

/-- The support of `pickOp` holds an expression if and only if the expression is
    `.op () ⟨name, ()⟩ (some τ)` for a name of `opsOfType octx τ`. -/
private theorem mem_support_pickOp_iff {octx : OpCtx} {τ : LMonoTy}
    {hv : (opsOfType octx τ).length > 0} {e : LExpr'} :
    e ∈ (pickOp (G := SetGen.Set) octx τ hv) ↔
      ∃ name ∈ opsOfType octx τ, e = .op () ⟨name, ()⟩ (some τ) := by
  change e ∈ SetGen.support (pickOp (G := SetGen.Set) octx τ hv) ↔ _
  simp only [pickOp, mem_support_elements_iff (list_map_ne_nil_of_length_pos hv), List.mem_map]
  constructor
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩

-- ── pickBVar soundness/completeness ───────────────────────────────────

/-- Soundness of `pickBVar`: every generated bvar expression is well-typed. -/
private theorem pickBVar_sound (bctx : BVarCtx) (τ : LMonoTy)
    (hv : (bvarsOfType bctx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (pickBVar (G := SetGen.Set) bctx τ hv)) :
    HasTypeA' bctx e τ := by
  have := mem_support_pickBVar_iff.mp he
  obtain ⟨i, hmem, rfl⟩ := this
  exact .bvar ((bvarsOfType_mem_iff bctx τ i).mp hmem)

/-- Completeness of `pickBVar`: any bvar with the right type is in the support. -/
private theorem pickBVar_complete (bctx : BVarCtx) (τ : LMonoTy) (i : Nat)
    (hget : bctx[i]? = some τ)
    (hv : (bvarsOfType bctx τ).length > 0) :
    .bvar () i ∈ SetGen.support (pickBVar (G := SetGen.Set) bctx τ hv) := by
  exact mem_support_pickBVar_iff.mpr ⟨i, (bvarsOfType_mem_iff bctx τ i).mpr hget, rfl⟩

-- ── pickFVar soundness/completeness ───────────────────────────────────

/-- `x ∈ fvarsOfType fctx τ` iff `(x, τ) ∈ fctx`. -/
private theorem fvarsOfType_mem_iff (fctx : FVarCtx) (τ : LMonoTy) (x : String) :
    x ∈ fvarsOfType fctx τ ↔ (x, τ) ∈ fctx := by
  simp only [fvarsOfType, List.mem_filterMap]
  constructor
  · rintro ⟨⟨y, ty⟩, hmem, hif⟩
    simp only at hif
    split at hif
    · rename_i heq
      have := beq_iff_eq.mp heq
      simp at hif; subst hif; subst this; exact hmem
    · simp at hif
  · intro hmem
    refine ⟨(x, τ), hmem, ?_⟩
    simp only
    split
    · simp
    · rename_i hne; exact absurd (beq_iff_eq.mpr rfl) hne

/-- Soundness of `pickFVar`: every generated fvar expression is well-typed. -/
private theorem pickFVar_sound (fctx : FVarCtx) (τ : LMonoTy)
    (hv : (fvarsOfType fctx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (pickFVar (G := SetGen.Set) fctx τ hv)) :
    HasTypeA' bctx e τ := by
  have := mem_support_pickFVar_iff.mp he
  obtain ⟨_, _, rfl⟩ := this
  exact .fvar

/-- Completeness of `pickFVar`: any fvar with the right type is in the support. -/
private theorem pickFVar_complete (fctx : FVarCtx) (τ : LMonoTy) (x : String)
    (hmem : (x, τ) ∈ fctx)
    (hv : (fvarsOfType fctx τ).length > 0) :
    .fvar () ⟨x, ()⟩ (some τ) ∈ SetGen.support (pickFVar (G := SetGen.Set) fctx τ hv) := by
  exact mem_support_pickFVar_iff.mpr ⟨x, (fvarsOfType_mem_iff fctx τ x).mpr hmem, rfl⟩

-- ── pickOp soundness/completeness ─────────────────────────────────────

/-- `x ∈ opsOfType octx τ` if and only if `(x, τ) ∈ octx.ops`.

    `opsOfType` reads the index. Therefore the proof first uses the `agrees` invariant,
    in the form `opsOfType_eq_scan`, to get the scan that `agrees` specifies. The other
    steps of the proof then apply to the scan. -/
private theorem opsOfType_mem_iff (octx : OpCtx) (τ : LMonoTy) (x : String) :
    x ∈ opsOfType octx τ ↔ (x, τ) ∈ octx.ops := by
  simp only [opsOfType_eq_scan, opsOfTypeList, List.mem_filterMap]
  constructor
  · rintro ⟨⟨y, ty⟩, hmem, hif⟩
    simp only at hif
    split at hif
    · rename_i heq
      have := beq_iff_eq.mp heq
      simp at hif; subst hif; subst this; exact hmem
    · simp at hif
  · intro hmem
    refine ⟨(x, τ), hmem, ?_⟩
    simp only
    split
    · simp
    · rename_i hne; exact absurd (beq_iff_eq.mpr rfl) hne

/-- Soundness of `pickOp`: every generated op expression is well-typed. -/
private theorem pickOp_sound (octx : OpCtx) (τ : LMonoTy)
    (hv : (opsOfType octx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (pickOp (G := SetGen.Set) octx τ hv)) :
    HasTypeA' bctx e τ := by
  have := mem_support_pickOp_iff.mp he
  obtain ⟨_, _, rfl⟩ := this
  exact .op

/-- Completeness of `pickOp`: any op with the right type is in the support. -/
private theorem pickOp_complete (octx : OpCtx) (τ : LMonoTy) (x : String)
    (hmem : (x, τ) ∈ octx.ops)
    (hv : (opsOfType octx τ).length > 0) :
    .op () ⟨x, ()⟩ (some τ) ∈ SetGen.support (pickOp (G := SetGen.Set) octx τ hv) := by
  exact mem_support_pickOp_iff.mpr ⟨x, (opsOfType_mem_iff octx τ x).mpr hmem, rfl⟩

namespace SetGen

/-- Membership in `oneOf` without a `support` wrapper. `support` is the identity on a `Set`, so this
    statement agrees with `mem_support_oneOf_iff`. It lets `simp` unfold `oneOf` after `mem_support_iff`
    removes the `support` wrapper. -/
@[simp] theorem mem_oneOf_iff {gs : List (Unit → Set α)} (hne : gs ≠ []) (a : α) :
    a ∈ (oneOf gs hne : Set α) ↔ ∃ g ∈ gs, a ∈ g () :=
  mem_support_oneOf_iff hne

end SetGen

-- ── genLMonoTy support ────────────────────────────────────────────────

/-- Each `ftvar` name of a type is a member of `tvars`. -/
def allFtvarsIn (tvars : List TyIdentifier) : LMonoTy → Prop
  | .ftvar name => name ∈ tvars
  | .tcons _ args => ∀ a ∈ args, allFtvarsIn tvars a
  | .bitvec _ => True

/-- Soundness of `pickTyVar`: any type in the support is `.ftvar name` for some `name ∈ tvars`. -/
private theorem pickTyVar_mem (tvars : List TyIdentifier) (h : tvars.length > 0) (τ : LMonoTy)
    (hτ : τ ∈ SetGen.support (pickTyVar (G := SetGen.Set) tvars h)) :
    ∃ name, name ∈ tvars ∧ τ = .ftvar name := by
  have hne : tvars ≠ [] := List.ne_nil_of_length_pos h
  simp only [pickTyVar, mem_support_map_iff,
             mem_support_elements_iff hne] at hτ
  assumption

/-- Completeness of `pickTyVar`: `.ftvar name` is in the support for any `name ∈ tvars`. -/
private theorem pickTyVar_complete (tvars : List TyIdentifier)
    (h : tvars.length > 0) (name : TyIdentifier)
    (hmem : name ∈ tvars) :
    LMonoTy.ftvar name ∈ SetGen.support (pickTyVar (G := SetGen.Set) tvars h) := by
  have hne : tvars ≠ [] := List.ne_nil_of_length_pos h
  simp only [pickTyVar, mem_support_map_iff,
             mem_support_elements_iff hne]
  exact ⟨name, hmem, rfl⟩

/-- `allFtvarsIn` is vacuously true for `.bool` (no ftvars). -/
private theorem allFtvarsIn_bool (tvars : List TyIdentifier) :
    allFtvarsIn tvars .bool := by simp [allFtvarsIn, LMonoTy.bool]
/-- `allFtvarsIn` is vacuously true for `.int` (no ftvars). -/
private theorem allFtvarsIn_int (tvars : List TyIdentifier) :
    allFtvarsIn tvars .int := by simp [allFtvarsIn, LMonoTy.int]
/-- `allFtvarsIn` is vacuously true for `.string` (no ftvars). -/
private theorem allFtvarsIn_string (tvars : List TyIdentifier) :
    allFtvarsIn tvars .string := by simp [allFtvarsIn, LMonoTy.string]
/-- `allFtvarsIn` is vacuously true for `.real` (no ftvars). -/
private theorem allFtvarsIn_real (tvars : List TyIdentifier) :
    allFtvarsIn tvars .real := by simp [allFtvarsIn, LMonoTy.real]
/-- `allFtvarsIn` is vacuously true for `.bitvec n` (no ftvars). -/
private theorem allFtvarsIn_bitvec (tvars : List TyIdentifier) (n : Nat) :
    allFtvarsIn tvars (.bitvec n) := by simp [allFtvarsIn]
/-- Introduce `allFtvarsIn` for an ftvar from list membership. -/
private theorem allFtvarsIn_ftvar {tvars : List TyIdentifier} {name : TyIdentifier}
    (h : name ∈ tvars) : allFtvarsIn tvars (.ftvar name) := by
  unfold allFtvarsIn; exact h
/-- Eliminate `allFtvarsIn` for an ftvar to list membership. -/
private theorem allFtvarsIn_ftvar_inv {tvars : List TyIdentifier} {name : TyIdentifier}
    (h : allFtvarsIn tvars (.ftvar name)) : name ∈ tvars := by
  unfold allFtvarsIn at h; exact h
/-- `allFtvarsIn` is vacuously true for `.regex` (no ftvars). -/
private theorem allFtvarsIn_regex (tvars : List TyIdentifier) :
    allFtvarsIn tvars .regex := by simp [allFtvarsIn, LMonoTy.regex]
/-- `allFtvarsIn` for an arrow type splits into a conjunction over its components. -/
private theorem allFtvarsIn_arrow {tvars : List TyIdentifier} {τ₁ τ₂ : LMonoTy} :
    allFtvarsIn tvars (.arrow τ₁ τ₂) ↔ allFtvarsIn tvars τ₁ ∧ allFtvarsIn tvars τ₂ := by
  simp [allFtvarsIn, LMonoTy.arrow]
/-- `allFtvarsIn` for a map type splits into a conjunction over its components. -/
private theorem allFtvarsIn_map {tvars : List TyIdentifier} {τ₁ τ₂ : LMonoTy} :
    allFtvarsIn tvars (.map τ₁ τ₂) ↔ allFtvarsIn tvars τ₁ ∧ allFtvarsIn tvars τ₂ := by
  simp [allFtvarsIn, LMonoTy.map]
/-- `allFtvarsIn` for a seq type is equivalent to the inner type. -/
private theorem allFtvarsIn_seq {tvars : List TyIdentifier} {τ : LMonoTy} :
    allFtvarsIn tvars (.seq τ) ↔ allFtvarsIn tvars τ := by
  simp [allFtvarsIn, LMonoTy.seq]

/-- Every natural number is in the support of `Nat.arbitrary` at `SetGen.Set`. -/
private theorem Nat_arbitrary_support_set (n : Nat) :
    n ∈ SetGen.support (Nat.arbitrary (G := SetGen.Set)) := by
  induction n with
  | zero =>
    simp only [SetGen.support]
    rw [Nat.arbitrary]
    simp [pick_mem_iff]
  | succ n ih =>
    simp only [SetGen.support] at ih ⊢
    rw [Nat.arbitrary]
    simp only [pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
    right
    exact ⟨n, ih, rfl⟩

/-- Each type in the support of `pickBitvecWidth` is `.bitvec n`. There is no limit on the width `n`. -/
private theorem pickBitvecWidth_mem (τ : LMonoTy)
    (hτ : τ ∈ SetGen.support (pickBitvecWidth (G := SetGen.Set))) :
    ∃ n, τ = .bitvec n := by
  simp only [pickBitvecWidth, mem_support_map_iff] at hτ
  obtain ⟨n, _, rfl⟩ := hτ
  exact ⟨n, rfl⟩

/-- Completeness of `pickBitvecWidth`: `.bitvec n` is in the support for *any*
    width `n`. -/
private theorem pickBitvecWidth_complete (n : Nat) :
    LMonoTy.bitvec n ∈ SetGen.support (pickBitvecWidth (G := SetGen.Set)) := by
  simp only [pickBitvecWidth, mem_support_map_iff]
  exact ⟨n, Nat_arbitrary_support_set n, rfl⟩

-- ── The structural facts about `inGenLMonoTySupport` ─────────────────
--
-- `inGenLMonoTySupport tvars n τ = true` is the decidable form of the statement "`τ` is generable at a
-- depth that is not more than `n`, and `tvars` holds each of its `ftvar` names". Therefore it gives
-- the bound on the depth and the condition on the `ftvar` names, and it grows with the depth index.
-- Each proof below follows the shape of the `inGenLMonoTySupport` definition itself, either by
-- `fun_induction` or by structural recursion on `τ`, because neither `monoTyDepth` nor
-- `inGenLMonoTySupport` reduces on a `tcons` whose head is a variable.

/-- `inGenLMonoTySupport` at the index `n` says that `monoTyDepth` is not more than `n`. -/
theorem inGenLMonoTySupport_depth (tvars : List TyIdentifier) (n : Nat) (τ : LMonoTy)
    (h : inGenLMonoTySupport tvars n τ = true) : monoTyDepth τ ≤ n := by
  fun_induction inGenLMonoTySupport tvars n τ <;>
    simp_all [monoTyDepth] <;> omega

/-- `inGenLMonoTySupport` says that `tvars` declares each `ftvar` name. -/
theorem inGenLMonoTySupport_ftvars (tvars : List TyIdentifier) (n : Nat) (τ : LMonoTy)
    (h : inGenLMonoTySupport tvars n τ = true) : allFtvarsIn tvars τ := by
  fun_induction inGenLMonoTySupport tvars n τ <;>
    simp_all [allFtvarsIn, nullaryBaseTypeNames]

/-- `inGenLMonoTySupport` stays true at a larger depth index. -/
theorem inGenLMonoTySupport_mono (tvars : List TyIdentifier) (n n' : Nat) (τ : LMonoTy)
    (hle : n ≤ n') (h : inGenLMonoTySupport tvars n τ = true) :
    inGenLMonoTySupport tvars n' τ = true := by
  induction τ generalizing n n' with
  | ftvar name => simpa [inGenLMonoTySupport] using h
  | bitvec w => simp [inGenLMonoTySupport]
  | tcons name args ih =>
    match n, n', args with
    | _, _, [] => rw [inGenLMonoTySupport] at h ⊢; exact h
    | 0, _, (_ :: _) => unfold inGenLMonoTySupport at h; split at h <;> simp_all
    | k+1, 0, _ => omega
    | k+1, j+1, [a] =>
      by_cases hs : name = "Sequence"
      · subst hs; simp only [inGenLMonoTySupport] at h ⊢
        exact ih a (by simp) k j (by omega) h
      · unfold inGenLMonoTySupport at h; split at h <;> simp_all
    | k+1, j+1, [a, b] =>
      by_cases ha : name = "arrow"
      · subst ha; simp only [inGenLMonoTySupport, Bool.and_eq_true] at h ⊢
        exact ⟨ih a (by simp) k j (by omega) h.1, ih b (by simp) k j (by omega) h.2⟩
      · by_cases hm : name = "Map"
        · subst hm; simp only [inGenLMonoTySupport, Bool.and_eq_true] at h ⊢
          exact ⟨ih a (by simp) k j (by omega) h.1, ih b (by simp) k j (by omega) h.2⟩
        · unfold inGenLMonoTySupport at h; split at h <;> simp_all
    | k+1, j+1, (a :: b :: c :: rest) => unfold inGenLMonoTySupport at h; split at h <;> simp_all


/-- The support of `pickBaseType` holds exactly `bool`, `int`, `string`, `real`, `regex`, and
    `bitvec n` at each width `n`. -/
private theorem pickBaseType_mem (tvars : List TyIdentifier) (τ : LMonoTy)
    (hτ : τ ∈ SetGen.support (pickBaseType (G := SetGen.Set))) :
    inGenLMonoTySupport tvars 0 τ = true := by
  rw [pickBaseType, mem_support_oneOf_iff] at hτ
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
             SetGen.support, pickBitvecWidth] at hτ
  rcases hτ with rfl | (rfl | (rfl | (rfl | (rfl | hbv))))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · obtain ⟨n, rfl⟩ := pickBitvecWidth_mem τ hbv; rfl

/-- Completeness of `pickBaseType`: every base type is in the support (for bitvec,
    at any width). -/
private theorem pickBaseType_complete_bool :
    LMonoTy.bool ∈ SetGen.support (pickBaseType (G := SetGen.Set)) := by
  rw [pickBaseType, mem_support_oneOf_iff]
  exact ⟨fun () => pure .bool, by simp, rfl⟩

private theorem pickBaseType_complete_int :
    LMonoTy.int ∈ SetGen.support (pickBaseType (G := SetGen.Set)) := by
  rw [pickBaseType, mem_support_oneOf_iff]
  exact ⟨fun () => pure .int, by simp, rfl⟩

private theorem pickBaseType_complete_string :
    LMonoTy.string ∈ SetGen.support (pickBaseType (G := SetGen.Set)) := by
  rw [pickBaseType, mem_support_oneOf_iff]
  exact ⟨fun () => pure .string, by simp, rfl⟩

private theorem pickBaseType_complete_real :
    LMonoTy.real ∈ SetGen.support (pickBaseType (G := SetGen.Set)) := by
  rw [pickBaseType, mem_support_oneOf_iff]
  exact ⟨fun () => pure .real, by simp, rfl⟩

private theorem pickBaseType_complete_regex :
    LMonoTy.regex ∈ SetGen.support (pickBaseType (G := SetGen.Set)) := by
  rw [pickBaseType, mem_support_oneOf_iff]
  exact ⟨fun () => pure .regex, by simp, rfl⟩

private theorem pickBaseType_complete_bitvec (n : Nat) :
    LMonoTy.bitvec n ∈ SetGen.support (pickBaseType (G := SetGen.Set)) := by
  rw [pickBaseType, mem_support_oneOf_iff]
  exact ⟨fun () => pickBitvecWidth, by simp, pickBitvecWidth_complete n⟩


/-- Support characterization of `genLMonoTy` at depth 0. -/
private theorem genLMonoTy_zero_mem (tvars : List TyIdentifier) (τ : LMonoTy) :
    τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars 0) ↔
      inGenLMonoTySupport tvars 0 τ = true := by
  simp only [genLMonoTy, mem_support_dite_iff, mem_support_pick_iff]
  constructor
  · rintro (⟨htv, (hbase | hftv)⟩ | ⟨htv, hbase⟩)
    · exact pickBaseType_mem tvars τ hbase
    · obtain ⟨name, hmem, rfl⟩ := pickTyVar_mem tvars htv _ hftv
      simpa [inGenLMonoTySupport, List.contains_iff_mem] using hmem
    · exact pickBaseType_mem tvars τ hbase
  · intro h
    match τ with
    | .bitvec w =>
      by_cases htv : tvars.length > 0
      · exact Or.inl ⟨htv, Or.inl (pickBaseType_complete_bitvec w)⟩
      · exact Or.inr ⟨htv, pickBaseType_complete_bitvec w⟩
    | .ftvar name =>
      have hmem : name ∈ tvars := by
        simpa [inGenLMonoTySupport, List.contains_iff_mem] using h
      exact Or.inl ⟨List.length_pos_of_mem hmem, Or.inr (pickTyVar_complete tvars _ name hmem)⟩
    | .tcons name [] =>
      have hmem : name ∈ nullaryBaseTypeNames := by
        simpa [inGenLMonoTySupport, List.contains_iff_mem] using h
      simp only [nullaryBaseTypeNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
      by_cases htv : tvars.length > 0
      · refine Or.inl ⟨htv, Or.inl ?_⟩
        rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact pickBaseType_complete_bool | exact pickBaseType_complete_int
            | exact pickBaseType_complete_string | exact pickBaseType_complete_real
            | exact pickBaseType_complete_regex
      · refine Or.inr ⟨htv, ?_⟩
        rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact pickBaseType_complete_bool | exact pickBaseType_complete_int
            | exact pickBaseType_complete_string | exact pickBaseType_complete_real
            | exact pickBaseType_complete_regex
    | .tcons name (_ :: _) =>
      exact absurd h (by unfold inGenLMonoTySupport; simp)

/-- Support characterization of `genLMonoTy` at depth `n + 1` (inductive step). -/
private theorem genLMonoTy_succ_mem (tvars : List TyIdentifier) (n : Nat) (τ : LMonoTy)
    (ih : ∀ τ, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) ↔
      inGenLMonoTySupport tvars n τ = true) :
    τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars (n + 1)) ↔
      inGenLMonoTySupport tvars (n + 1) τ = true := by
  have hfreq : ∀ (x y : Unit → SetGen.Set LMonoTy)
      (h : 0 < List.sum (List.map Prod.fst [(9, x), (1, y)])),
      τ ∈ SetGen.support (frequency [(9, x), (1, y)] h) ↔
        τ ∈ SetGen.support (x ()) ∨ τ ∈ SetGen.support (y ()) := by
    intro x y h
    rw [mem_support_frequency_iff]
    constructor
    · rintro ⟨w, g, hg, hpos, hmem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inl hmem
      · exact Or.inr hmem
    · rintro (hmem | hmem)
      · exact ⟨9, x, by simp, by omega, hmem⟩
      · exact ⟨1, y, by simp, by omega, hmem⟩
  simp only [genLMonoTy, mem_support_dite_iff, hfreq, mem_support_oneOf_iff,
             List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
             mem_support_bind_iff]
  constructor
  · intro he
    rcases he with (⟨htv, (hbase | (⟨τ₁, hτ₁, τ₂, hτ₂, rfl⟩ |
                    (⟨τ₁, hτ₁, τ₂, hτ₂, rfl⟩ | (⟨τ₁, hτ₁, rfl⟩ | hftv))))⟩ |
                    ⟨htv, (hbase | (⟨τ₁, hτ₁, τ₂, hτ₂, rfl⟩ |
                    (⟨τ₁, hτ₁, τ₂, hτ₂, rfl⟩ | ⟨τ₁, hτ₁, rfl⟩)))⟩)
    · exact inGenLMonoTySupport_mono tvars 0 (n + 1) τ (Nat.zero_le _) (pickBaseType_mem tvars τ hbase)
    · simp only [inGenLMonoTySupport, LMonoTy.arrow, Bool.and_eq_true]
      exact ⟨(ih τ₁).mp hτ₁, (ih τ₂).mp hτ₂⟩
    · simp only [inGenLMonoTySupport, LMonoTy.map, Bool.and_eq_true]
      exact ⟨(ih τ₁).mp hτ₁, (ih τ₂).mp hτ₂⟩
    · simp only [inGenLMonoTySupport, LMonoTy.seq]
      exact (ih τ₁).mp hτ₁
    · obtain ⟨name, hmem, rfl⟩ := pickTyVar_mem tvars htv _ hftv
      simpa [inGenLMonoTySupport, List.contains_iff_mem] using hmem
    · exact inGenLMonoTySupport_mono tvars 0 (n + 1) τ (Nat.zero_le _) (pickBaseType_mem tvars τ hbase)
    · simp only [inGenLMonoTySupport, LMonoTy.arrow, Bool.and_eq_true]
      exact ⟨(ih τ₁).mp hτ₁, (ih τ₂).mp hτ₂⟩
    · simp only [inGenLMonoTySupport, LMonoTy.map, Bool.and_eq_true]
      exact ⟨(ih τ₁).mp hτ₁, (ih τ₂).mp hτ₂⟩
    · simp only [inGenLMonoTySupport, LMonoTy.seq]
      exact (ih τ₁).mp hτ₁
  · intro h
    by_cases htv : tvars.length > 0
    · left; refine ⟨htv, ?_⟩
      match τ with
      | .bitvec w => exact Or.inl (pickBaseType_complete_bitvec w)
      | .ftvar name =>
        have hmem : name ∈ tvars := by
          simpa [inGenLMonoTySupport, List.contains_iff_mem] using h
        exact Or.inr (Or.inr (Or.inr (Or.inr (pickTyVar_complete tvars htv name hmem))))
      | .tcons name [] =>
        have hmem : name ∈ nullaryBaseTypeNames := by
          simpa [inGenLMonoTySupport, List.contains_iff_mem] using h
        simp only [nullaryBaseTypeNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
        refine Or.inl ?_
        rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact pickBaseType_complete_bool | exact pickBaseType_complete_int
            | exact pickBaseType_complete_string | exact pickBaseType_complete_real
            | exact pickBaseType_complete_regex
      | .tcons name [a] =>
        by_cases hs : name = "Sequence"
        · subst hs
          simp only [inGenLMonoTySupport] at h
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, (ih a).mpr h, rfl⟩)))
        · exact absurd h (by unfold inGenLMonoTySupport; simp [hs])
      | .tcons name [a, b] =>
        by_cases ha : name = "arrow"
        · subst ha
          simp only [inGenLMonoTySupport, Bool.and_eq_true] at h
          exact Or.inr (Or.inl ⟨a, (ih a).mpr h.1, b, (ih b).mpr h.2, rfl⟩)
        · by_cases hm : name = "Map"
          · subst hm
            simp only [inGenLMonoTySupport, Bool.and_eq_true] at h
            exact Or.inr (Or.inr (Or.inl ⟨a, (ih a).mpr h.1, b, (ih b).mpr h.2, rfl⟩))
          · exact absurd h (by unfold inGenLMonoTySupport; simp [ha, hm])
      | .tcons name (_ :: _ :: _ :: _) => exact absurd h (by unfold inGenLMonoTySupport; simp)
    · right; refine ⟨htv, ?_⟩
      match τ with
      | .bitvec w => exact Or.inl (pickBaseType_complete_bitvec w)
      | .ftvar name =>
        have hmem : name ∈ tvars := by
          simpa [inGenLMonoTySupport, List.contains_iff_mem] using h
        exact absurd (List.length_pos_of_mem hmem) htv
      | .tcons name [] =>
        have hmem : name ∈ nullaryBaseTypeNames := by
          simpa [inGenLMonoTySupport, List.contains_iff_mem] using h
        simp only [nullaryBaseTypeNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
        refine Or.inl ?_
        rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact pickBaseType_complete_bool | exact pickBaseType_complete_int
            | exact pickBaseType_complete_string | exact pickBaseType_complete_real
            | exact pickBaseType_complete_regex
      | .tcons name [a] =>
        by_cases hs : name = "Sequence"
        · subst hs
          simp only [inGenLMonoTySupport] at h
          exact Or.inr (Or.inr (Or.inr ⟨a, (ih a).mpr h, rfl⟩))
        · exact absurd h (by unfold inGenLMonoTySupport; simp [hs])
      | .tcons name [a, b] =>
        by_cases ha : name = "arrow"
        · subst ha
          simp only [inGenLMonoTySupport, Bool.and_eq_true] at h
          exact Or.inr (Or.inl ⟨a, (ih a).mpr h.1, b, (ih b).mpr h.2, rfl⟩)
        · by_cases hm : name = "Map"
          · subst hm
            simp only [inGenLMonoTySupport, Bool.and_eq_true] at h
            exact Or.inr (Or.inr (Or.inl ⟨a, (ih a).mpr h.1, b, (ih b).mpr h.2, rfl⟩))
          · exact absurd h (by unfold inGenLMonoTySupport; simp [ha, hm])
      | .tcons name (_ :: _ :: _ :: _) => exact absurd h (by unfold inGenLMonoTySupport; simp)

/-- The Boolean `inGenLMonoTySupport` decides membership in the support of `genLMonoTy`. It holds when
    the type has a simple structure, a depth that is not more than `n`, and only `ftvar` names from
    `tvars`. -/
theorem genLMonoTy_support (tvars : List TyIdentifier) (n : Nat) (τ : LMonoTy) :
    τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) ↔
      inGenLMonoTySupport tvars n τ = true := by
  induction n generalizing τ with
  | zero => exact genLMonoTy_zero_mem tvars τ
  | succ n ih => exact genLMonoTy_succ_mem tvars n τ ih

/-- The Boolean filter `inGenLMonoTySupport` is exactly `genLMonoTy`'s support. -/
theorem inGenLMonoTySupport_sound (tvars : List TyIdentifier) :
    ∀ (n : Nat) (τ : LMonoTy), inGenLMonoTySupport tvars n τ = true →
      τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) :=
  fun n τ h => (genLMonoTy_support tvars n τ).mpr h


-- ── A generable type: `∃ m, τ ∈ support (genLMonoTy tvars m)` ────────
--
-- Many statements below are indexed by the fact that `genLMonoTy tvars` can give `τ` at some fuel.
-- Such a `τ` is built from the base types, a `bitvec` of any width, an `arrow`, a `Map`, a `Sequence`,
-- and an `ftvar` that comes from `tvars`. Each use writes the statement out, and no definition hides
-- it.
--
-- The existential over the fuel is necessary. The term generator can pass a target type to itself at a
-- fuel that is below the depth of the type. An `app` at the fuel `n + 1` recurses on a function of the
-- type `τ' → τ` at the fuel `n`, and `τ' → τ` can have the depth `n + 1`. Therefore a statement that
-- pins the fuel is false for that recursion.
--
-- The introduction lemmas, the inversion lemmas and the eliminators for this statement are below.
-- The name of each one starts with `genLMonoTy_mem_`.

/-- A type that is generable at the fuel `m` is also generable at each larger fuel. -/
theorem genLMonoTy_mem_mono {tvars : List TyIdentifier} {m m' : Nat} {τ : LMonoTy}
    (hle : m ≤ m') (h : τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m') := by
  rw [genLMonoTy_support] at h ⊢
  exact inGenLMonoTySupport_mono tvars m m' τ hle h

/-- The fuel that membership in the support of `genLMonoTy` gives is an upper limit on
    `monoTyDepth`. -/
theorem genLMonoTy_mem_depth {tvars : List TyIdentifier} {m : Nat} {τ : LMonoTy}
    (h : τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    monoTyDepth τ ≤ m :=
  inGenLMonoTySupport_depth tvars m τ ((genLMonoTy_support tvars m τ).mp h)

/-- `tvars` declares each `ftvar` name of a generable type. -/
theorem genLMonoTy_mem_ftvars {tvars : List TyIdentifier} {m : Nat} {τ : LMonoTy}
    (h : τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    allFtvarsIn tvars τ :=
  inGenLMonoTySupport_ftvars tvars m τ ((genLMonoTy_support tvars m τ).mp h)

-- The introduction lemmas, one for each shape of a generable type. `tvars` and `w` are implicit, so a
-- proof can apply a lemma with no explicit argument.

theorem genLMonoTy_mem_bool {tvars : List TyIdentifier} :
    ∃ m, LMonoTy.bool ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) :=
  ⟨0, (genLMonoTy_support _ _ _).mpr rfl⟩
theorem genLMonoTy_mem_int {tvars : List TyIdentifier} :
    ∃ m, LMonoTy.int ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) :=
  ⟨0, (genLMonoTy_support _ _ _).mpr rfl⟩
theorem genLMonoTy_mem_string {tvars : List TyIdentifier} :
    ∃ m, LMonoTy.string ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) :=
  ⟨0, (genLMonoTy_support _ _ _).mpr rfl⟩
theorem genLMonoTy_mem_real {tvars : List TyIdentifier} :
    ∃ m, LMonoTy.real ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) :=
  ⟨0, (genLMonoTy_support _ _ _).mpr rfl⟩
theorem genLMonoTy_mem_regex {tvars : List TyIdentifier} :
    ∃ m, LMonoTy.regex ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) :=
  ⟨0, (genLMonoTy_support _ _ _).mpr rfl⟩
theorem genLMonoTy_mem_bitvec {tvars : List TyIdentifier} {w : Nat} :
    ∃ m, LMonoTy.bitvec w ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) :=
  ⟨0, (genLMonoTy_support _ _ _).mpr rfl⟩
theorem genLMonoTy_mem_ftvar {tvars : List TyIdentifier} {name : TyIdentifier}
    (h : name ∈ tvars) :
    ∃ m, LMonoTy.ftvar name ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) :=
  ⟨0, (genLMonoTy_support _ _ _).mpr
    (by simpa [inGenLMonoTySupport, List.contains_iff_mem] using h)⟩

theorem genLMonoTy_mem_arrow {tvars : List TyIdentifier} {τ₁ τ₂ : LMonoTy}
    (h₁ : ∃ m, τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (h₂ : ∃ m, τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    ∃ m, LMonoTy.arrow τ₁ τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
  obtain ⟨m₁, hm₁⟩ := h₁; obtain ⟨m₂, hm₂⟩ := h₂
  have b₁ := (genLMonoTy_support tvars m₁ τ₁).mp hm₁
  have b₂ := (genLMonoTy_support tvars m₂ τ₂).mp hm₂
  refine ⟨max m₁ m₂ + 1, (genLMonoTy_support _ _ _).mpr ?_⟩
  simp only [inGenLMonoTySupport, LMonoTy.arrow, Bool.and_eq_true]
  exact ⟨inGenLMonoTySupport_mono tvars m₁ (max m₁ m₂) τ₁ (by omega) b₁,
         inGenLMonoTySupport_mono tvars m₂ (max m₁ m₂) τ₂ (by omega) b₂⟩

theorem genLMonoTy_mem_map {tvars : List TyIdentifier} {τ₁ τ₂ : LMonoTy}
    (h₁ : ∃ m, τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (h₂ : ∃ m, τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    ∃ m, LMonoTy.map τ₁ τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
  obtain ⟨m₁, hm₁⟩ := h₁; obtain ⟨m₂, hm₂⟩ := h₂
  have b₁ := (genLMonoTy_support tvars m₁ τ₁).mp hm₁
  have b₂ := (genLMonoTy_support tvars m₂ τ₂).mp hm₂
  refine ⟨max m₁ m₂ + 1, (genLMonoTy_support _ _ _).mpr ?_⟩
  simp only [inGenLMonoTySupport, LMonoTy.map, Bool.and_eq_true]
  exact ⟨inGenLMonoTySupport_mono tvars m₁ (max m₁ m₂) τ₁ (by omega) b₁,
         inGenLMonoTySupport_mono tvars m₂ (max m₁ m₂) τ₂ (by omega) b₂⟩

theorem genLMonoTy_mem_seq {tvars : List TyIdentifier} {τ : LMonoTy}
    (h : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    ∃ m, LMonoTy.seq τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
  obtain ⟨m, hm⟩ := h
  have b := (genLMonoTy_support tvars m τ).mp hm
  refine ⟨m + 1, (genLMonoTy_support _ _ _).mpr ?_⟩
  simp only [inGenLMonoTySupport, LMonoTy.seq]
  exact b

theorem genLMonoTy_mem_arrow_inv {tvars : List TyIdentifier} {τ₁ τ₂ : LMonoTy}
    (h : ∃ m, LMonoTy.arrow τ₁ τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    (∃ m, τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) ∧
      (∃ m, τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) := by
  obtain ⟨m, hm⟩ := h
  have b := (genLMonoTy_support tvars m (.arrow τ₁ τ₂)).mp hm
  match m with
  | 0 => exact absurd b (by unfold inGenLMonoTySupport; simp [LMonoTy.arrow])
  | k + 1 =>
    simp only [inGenLMonoTySupport, LMonoTy.arrow, Bool.and_eq_true] at b
    exact ⟨⟨k, (genLMonoTy_support tvars k τ₁).mpr b.1⟩,
           ⟨k, (genLMonoTy_support tvars k τ₂).mpr b.2⟩⟩

theorem genLMonoTy_mem_map_inv {tvars : List TyIdentifier} {τ₁ τ₂ : LMonoTy}
    (h : ∃ m, LMonoTy.map τ₁ τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    (∃ m, τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) ∧
      (∃ m, τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) := by
  obtain ⟨m, hm⟩ := h
  have b := (genLMonoTy_support tvars m (.map τ₁ τ₂)).mp hm
  match m with
  | 0 => exact absurd b (by unfold inGenLMonoTySupport; simp [LMonoTy.map])
  | k + 1 =>
    simp only [inGenLMonoTySupport, LMonoTy.map, Bool.and_eq_true] at b
    exact ⟨⟨k, (genLMonoTy_support tvars k τ₁).mpr b.1⟩,
           ⟨k, (genLMonoTy_support tvars k τ₂).mpr b.2⟩⟩

theorem genLMonoTy_mem_seq_inv {tvars : List TyIdentifier} {τ : LMonoTy}
    (h : ∃ m, LMonoTy.seq τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
  obtain ⟨m, hm⟩ := h
  have b := (genLMonoTy_support tvars m (.seq τ)).mp hm
  match m with
  | 0 => exact absurd b (by unfold inGenLMonoTySupport; simp [LMonoTy.seq])
  | k + 1 =>
    simp only [inGenLMonoTySupport, LMonoTy.seq] at b
    exact ⟨k, (genLMonoTy_support tvars k τ).mpr b⟩

/-- **An induction principle for a generable type.** To use it, write
    `refine genLMonoTy_mem_rec (motive := …) ?bool … ?seq h`, and then give each case. The proof is by
    structural recursion on `τ`, which follows the shape of `inGenLMonoTySupport`. -/
@[elab_as_elim]
theorem genLMonoTy_mem_rec {tvars : List TyIdentifier} {motive : LMonoTy → Prop}
    (bool : motive .bool) (int : motive .int) (string : motive .string)
    (real : motive .real) (regex : motive .regex)
    (bitvec : ∀ w, motive (.bitvec w))
    (ftvar : ∀ name, name ∈ tvars → motive (.ftvar name))
    (arrow : ∀ τ₁ τ₂,
      (∃ m, τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      (∃ m, τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      motive τ₁ → motive τ₂ → motive (.arrow τ₁ τ₂))
    (map : ∀ τ₁ τ₂,
      (∃ m, τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      (∃ m, τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      motive τ₁ → motive τ₂ → motive (.map τ₁ τ₂))
    (seq : ∀ τ,
      (∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      motive τ → motive (.seq τ))
    {τ : LMonoTy}
    (h : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) : motive τ := by
  revert h
  induction τ with
  | ftvar name =>
    intro h
    exact ftvar name (allFtvarsIn_ftvar_inv (genLMonoTy_mem_ftvars (Classical.choose_spec h)))
  | bitvec w => intro _; exact bitvec w
  | tcons name args ih =>
    intro h
    match args with
    | [] =>
      obtain ⟨m, hm⟩ := h
      have hmem : name ∈ nullaryBaseTypeNames := by
        simpa [inGenLMonoTySupport, List.contains_iff_mem]
          using (genLMonoTy_support tvars m (.tcons name [])).mp hm
      simp only [nullaryBaseTypeNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact bool
          | exact int
          | exact string
          | exact real
          | exact regex
    | [a] =>
      by_cases hs : name = "Sequence"
      · subst hs
        have ha : ∃ m, a ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) :=
          genLMonoTy_mem_seq_inv h
        exact seq a ha (ih a (by simp) ha)
      · obtain ⟨m, hm⟩ := h
        exact absurd ((genLMonoTy_support tvars m _).mp hm)
          (by unfold inGenLMonoTySupport; simp [hs])
    | [a, b] =>
      by_cases ha : name = "arrow"
      · subst ha
        obtain ⟨h1, h2⟩ := genLMonoTy_mem_arrow_inv h
        exact arrow a b h1 h2 (ih a (by simp) h1) (ih b (by simp) h2)
      · by_cases hm : name = "Map"
        · subst hm
          obtain ⟨h1, h2⟩ := genLMonoTy_mem_map_inv h
          exact map a b h1 h2 (ih a (by simp) h1) (ih b (by simp) h2)
        · obtain ⟨mm, hm'⟩ := h
          exact absurd ((genLMonoTy_support tvars mm _).mp hm')
            (by unfold inGenLMonoTySupport; simp [ha, hm])
    | (_ :: _ :: _ :: _) =>
      obtain ⟨m, hm⟩ := h
      exact absurd ((genLMonoTy_support tvars m _).mp hm)
        (by unfold inGenLMonoTySupport; simp)


/-- **A case-analysis principle for a generable type.** It has the same shape as
    `genLMonoTy_mem_rec`, and it gives no inductive hypothesis. It has no `tcons` case and no datatype
    case, so a structural match on a generable type needs no final arm for the other cases. -/
@[elab_as_elim]
theorem genLMonoTy_mem_cases {tvars : List TyIdentifier} {motive : LMonoTy → Prop}
    (bool : motive .bool) (int : motive .int) (string : motive .string)
    (real : motive .real) (regex : motive .regex)
    (bitvec : ∀ w, motive (.bitvec w))
    (ftvar : ∀ name, name ∈ tvars → motive (.ftvar name))
    (arrow : ∀ τ₁ τ₂,
      (∃ m, τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      (∃ m, τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      motive (.arrow τ₁ τ₂))
    (map : ∀ τ₁ τ₂,
      (∃ m, τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      (∃ m, τ₂ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      motive (.map τ₁ τ₂))
    (seq : ∀ τ,
      (∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) → motive (.seq τ))
    {τ : LMonoTy}
    (h : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) : motive τ :=
  genLMonoTy_mem_rec bool int string real regex bitvec ftvar
    (fun τ₁ τ₂ h₁ h₂ _ _ => arrow τ₁ τ₂ h₁ h₂)
    (fun τ₁ τ₂ h₁ h₂ _ _ => map τ₁ τ₂ h₁ h₂)
    (fun τ h _ => seq τ h) h

/-- **The support of `genGenerableTy` is exactly the support of `genLMonoTy`.**

    This equality is what lets each proof use the type generator that reads the context in place of
    `genLMonoTy`. `genGenerableTy` is a `frequency` of two branches. Branch (a) is `elements` over the
    types from the context, after the filter `inGenLMonoTySupport tvars n`. Branch (b) is
    `genLMonoTy tvars n` itself. The support of a `frequency` is the union of the supports of its
    branches that have a positive weight. Branch (a) is a subset of branch (b), and branch (b) stays.
    Therefore the union is the support of `genLMonoTy`. Only the *distribution* changes. -/
@[simp]
theorem genGenerableTy_support (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) :
    τ ∈ SetGen.support (genGenerableTy (G := SetGen.Set) fctx octx tvars bctx n) ↔
      τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) := by
  rw [genGenerableTy]
  split
  · rename_i hg
    rw [mem_support_frequency_iff]
    constructor
    · rintro ⟨w, g, hg', _, hmem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hg'
      rcases hg' with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · -- drawn from the filtered context types: sound by `inGenLMonoTySupport_sound`
        rw [mem_support_elements_iff] at hmem
        exact inGenLMonoTySupport_sound tvars n τ (List.mem_filter.mp hmem).2
      · exact hmem
    · -- the retained `genLMonoTy` branch has positive weight
      intro hmem
      exact ⟨1, fun () => genLMonoTy tvars n, by simp, by omega, hmem⟩
  · rfl

/-- **The support of `genAppArgTy` is exactly the support of `genLMonoTy`.**

    The argument is the same as for `genGenerableTy_support`, one level further. The filtered branch
    draws the argument type `σ` of a generable function type `σ → τ`, so that both positions of an
    application are inhabitable. Each such `σ` passes `inGenLMonoTySupport tvars n`, and it is
    therefore in the support of `genLMonoTy`. The `genLMonoTy` branch that stays gives the other
    direction, and the fallback branch reduces to `genGenerableTy_support`. -/
@[simp]
theorem genAppArgTy_support (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ σ : LMonoTy) :
    σ ∈ SetGen.support (genAppArgTy (G := SetGen.Set) fctx octx tvars bctx n τ) ↔
      σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) := by
  rw [genAppArgTy]
  split
  · rename_i hg
    rw [mem_support_frequency_iff]
    constructor
    · rintro ⟨w, g, hg', _, hmem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hg'
      rcases hg' with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · -- drawn from the argument types of generable function types: each passed
        -- `inGenLMonoTySupport`, so it is sound by `inGenLMonoTySupport_sound`
        rw [mem_support_elements_iff] at hmem
        exact inGenLMonoTySupport_sound tvars n σ (List.mem_filter.mp hmem).2
      · exact hmem
    · -- the retained `genLMonoTy` branch has positive weight
      intro hmem
      exact ⟨1, fun () => genLMonoTy tvars n, by simp, by omega, hmem⟩
  · exact genGenerableTy_support fctx octx tvars bctx n σ

-- ── Soundness for genLExpr ────────────────────────────────────────────

-- In Strata, `LMonoTy.bool`, `.int` and `.arrow` are each an `abbrev` for a `tcons`. An example is
-- `abbrev LMonoTy.arrow τ₁ τ₂ := .tcons "arrow" [τ₁, τ₂]`. `genLExpr` matches on a pattern, so the
-- equational lemmas that Lean generates for it name the expanded constructor, which is
-- `LMonoTy.tcons "arrow" [τ₁, τ₂]`, and not the abbreviation. A hypothesis about `genLExpr` can hold
-- the abbreviation instead. `simp only [genLExpr]` then tries to match the expanded form against the
-- abbreviation in the hypothesis. The two terms are definitionally equal, but `simp` and `rw` need
-- syntactic equality. The rewrite lemmas below normalize each abbreviation, so that an equational
-- lemma can match.
/-- Normalize `.bool` abbreviation so `simp [genLExpr]` equation lemmas can match. -/
private theorem norm_bool : LMonoTy.bool = LMonoTy.tcons "bool" [] := rfl
/-- Normalize `.int` abbreviation so `simp [genLExpr]` equation lemmas can match. -/
private theorem norm_int : LMonoTy.int = LMonoTy.tcons "int" [] := rfl
/-- Normalize `.string` abbreviation so `simp [genLExpr]` equation lemmas can match. -/
private theorem norm_string : LMonoTy.string = LMonoTy.tcons "string" [] := rfl
/-- Normalize `.real` abbreviation so `simp [genLExpr]` equation lemmas can match. -/
private theorem norm_real : LMonoTy.real = LMonoTy.tcons "real" [] := rfl
/-- Normalize `.arrow` abbreviation so `simp [genLExpr]` equation lemmas can match. -/
private theorem norm_arrow (τ₁ τ₂ : LMonoTy) :
    LMonoTy.arrow τ₁ τ₂ = LMonoTy.tcons "arrow" [τ₁, τ₂] := rfl


set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- Each expression in the support of `genLExprBase` is well-typed. The fallback for a type that the
    generator does not handle is the empty generator, because `default` is `∅`. Therefore the statement
    holds at each `τ`, and not only at a generable one. At a type that the generator does not handle, the
    support is empty and the statement says nothing.

    In an Indir branch, the spine is well-typed because the `.op` node has the type of its annotation,
    and each argument comes from `genLExprBase` at the smaller depth. The recursive call of this theorem
    gives the type of each argument. The IndirPoly branch is the same, and the recursive call also gives
    the fallback. -/
theorem genLExprBase_sound (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (e : LExpr')
    (he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth τ)) :
    HasTypeA' bctx e τ := by
  rw [genLExprBase.eq_def] at he
  split at he
  case h_1 τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.arrow τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_arrow] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff,
      mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, h⟩) | ((⟨_, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩))
    all_goals first
      | exact pickBVar_sound bctx _ _ _ h
      | exact pickFVar_sound fctx _ _ _ h
      | exact pickOp_sound octx _ _ _ h
      | exact absurd h (by simp)
  case h_2 n τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) (.arrow τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_arrow] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (4, fun () => genAbs (G := SetGen.Set) (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.arrow τ₁ τ₂)) (genLExprBase fctx octx pctx tvars bctx n) (.arrow τ₁ τ₂)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))
                              (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.arrow τ₁ τ₂)).length > 0 then pickBVar bctx (.arrow τ₁ τ₂) hv
           else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0 then pickFVar fctx (.arrow τ₁ τ₂) hf
           else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (2, fun () =>
           if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0 then pickOp octx (.arrow τ₁ τ₂) ho
           else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.arrow τ₁ τ₂)).length > 0
           then genIndir octx (.arrow τ₁ τ₂) (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.arrow τ₁ τ₂)
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))) ]
      ) (by show 0 < 4+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genAbs, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨body, hbody, rfl⟩ := he
      exact .abs (genLExprBase_sound fctx octx pctx tvars (τ₁ :: bctx) n _ _ hbody)
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickBVar_sound bctx _ _ _ h
      · exact .abs (genLExprBase_sound fctx octx pctx tvars (τ₁ :: bctx) n _ _ hbody)
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickFVar_sound fctx _ _ _ h
      · exact .abs (genLExprBase_sound fctx octx pctx tvars (τ₁ :: bctx) n _ _ hbody)
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickOp_sound octx _ _ _ h
      · exact .abs (genLExprBase_sound fctx octx pctx tvars (τ₁ :: bctx) n _ _ hbody)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_3 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .bool) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_bool] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with (rfl | rfl) | ((⟨_, h⟩ | ⟨_, rfl | rfl⟩) | ((⟨_, h⟩ | ⟨_, rfl | rfl⟩) | (⟨_, h⟩ | ⟨_, rfl | rfl⟩)))
    all_goals first
      | exact (by unfold LExpr.boolConst; exact .const)
      | exact pickBVar_sound bctx .bool _ _ h
      | exact pickFVar_sound fctx .bool _ _ h
      | exact pickOp_sound octx .bool _ _ h
  case h_4 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .bool) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_bool] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genBoolConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .bool) (genLExprBase fctx octx pctx tvars bctx n) .bool),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .bool)),
         (2, fun () => genEq (genGenerableTy fctx octx tvars bctx n) (genLExprBase fctx octx pctx tvars bctx n)),
         (2, fun () => genQuant .all (genGenerableTy fctx octx tvars bctx n)
           (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n)
           (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n .bool)),
         (2, fun () => genQuant .exist (genGenerableTy fctx octx tvars bctx n)
           (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n)
           (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n .bool)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .bool).length > 0 then pickBVar bctx .bool hv
           else genBoolConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .bool).length > 0 then pickFVar fctx .bool hf
           else genBoolConst),
         (2, fun () =>
           if ho : (opsOfType octx .bool).length > 0 then pickOp octx .bool ho
           else genBoolConst),
         (4, fun () =>
           if hi : (findOpsInCtx octx .bool).length > 0
           then genIndir octx .bool (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .bool),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .bool
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .bool)) ]
      ) (by show 0 < 1+1+2+2+2+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genBoolConst, genApp, genIte, genEq, genQuant, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with rfl | rfl
      all_goals exact (by unfold LExpr.boolConst; exact .const)
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · obtain ⟨τ', _, e₁, he₁, e₂, he₂, rfl⟩ := he
      exact .eq (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he₁)
                 (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he₂)
    · obtain ⟨τ', _, τ_tr, _, tr, htr, body, hbody, rfl⟩ := he
      exact .quant (genLExprBase_sound fctx octx pctx tvars (τ' :: bctx) n _ _ htr)
                    (genLExprBase_sound fctx octx pctx tvars (τ' :: bctx) n _ _ hbody)
    · obtain ⟨τ', _, τ_tr, _, tr, htr, body, hbody, rfl⟩ := he
      exact .quant (genLExprBase_sound fctx octx pctx tvars (τ' :: bctx) n _ _ htr)
                    (genLExprBase_sound fctx octx pctx tvars (τ' :: bctx) n _ _ hbody)
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickBVar_sound bctx .bool _ _ h
      all_goals exact (by unfold LExpr.boolConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickFVar_sound fctx .bool _ _ h
      all_goals exact (by unfold LExpr.boolConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickOp_sound octx .bool _ _ h
      all_goals exact (by unfold LExpr.boolConst; exact .const)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_5 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .int) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_int] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩) | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩)))
    all_goals first
      | exact (by unfold LExpr.intConst; exact .const)
      | exact pickBVar_sound bctx .int _ _ h
      | exact pickFVar_sound fctx .int _ _ h
      | exact pickOp_sound octx .int _ _ h
  case h_6 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .int) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_int] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genIntConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .int) (genLExprBase fctx octx pctx tvars bctx n) .int),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .int)
                              (genLExprBase fctx octx pctx tvars bctx n .int)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .int).length > 0 then pickBVar bctx .int hv
           else genIntConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .int).length > 0 then pickFVar fctx .int hf
           else genIntConst),
         (2, fun () =>
           if ho : (opsOfType octx .int).length > 0 then pickOp octx .int ho
           else genIntConst),
         (4, fun () =>
           if hi : (findOpsInCtx octx .int).length > 0
           then genIndir octx .int (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .int),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .int
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .int)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genIntConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩
      all_goals exact (by unfold LExpr.intConst; exact .const)
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickBVar_sound bctx .int _ _ h
      all_goals exact (by unfold LExpr.intConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickFVar_sound fctx .int _ _ h
      all_goals exact (by unfold LExpr.intConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickOp_sound octx .int _ _ h
      all_goals exact (by unfold LExpr.intConst; exact .const)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_7 name =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.ftvar name)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))
    all_goals first
      | exact pickBVar_sound bctx _ _ _ h
      | exact pickFVar_sound fctx _ _ _ h
      | exact pickOp_sound octx _ _ _ h
      | exact absurd h (by simp)
  case h_8 n name =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) (.ftvar name)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx octx tvars bctx n (.ftvar name)) (genLExprBase fctx octx pctx tvars bctx n) (.ftvar name)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))
                              (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else if hf : (fvarsOfType fctx (.ftvar name)).length > 0 then pickFVar fctx (.ftvar name) hf
           else if ho : (opsOfType octx (.ftvar name)).length > 0 then pickOp octx (.ftvar name) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.ftvar name)).length > 0 then pickFVar fctx (.ftvar name) hf
           else if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType octx (.ftvar name)).length > 0 then pickOp octx (.ftvar name) ho
           else if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.ftvar name)).length > 0
           then genIndir octx (.ftvar name) (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n (.ftvar name)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.ftvar name)
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickFVar_sound fctx _ _ _ h
        | exact pickOp_sound octx _ _ _ h
        | exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickFVar_sound fctx _ _ _ h
        | exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickOp_sound octx _ _ _ h
        | exact absurd h (by simp)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_9 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .string) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_string] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨k, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)))
    all_goals first
      | exact (by unfold LExpr.strConst; exact .const)
      | exact pickBVar_sound bctx .string _ _ h
      | exact pickFVar_sound fctx .string _ _ h
      | exact pickOp_sound octx .string _ _ h
  case h_10 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .string) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_string] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genStrConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .string) (genLExprBase fctx octx pctx tvars bctx n) .string),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .string)
                              (genLExprBase fctx octx pctx tvars bctx n .string)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .string).length > 0 then pickBVar bctx .string hv
           else genStrConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .string).length > 0 then pickFVar fctx .string hf
           else genStrConst),
         (2, fun () =>
           if ho : (opsOfType octx .string).length > 0 then pickOp octx .string ho
           else genStrConst),
         (4, fun () =>
           if hi : (findOpsInCtx octx .string).length > 0
           then genIndir octx .string (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .string),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .string
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .string)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genStrConst, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨s, _, rfl⟩ := he
      exact (by unfold LExpr.strConst; exact .const)
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickBVar_sound bctx .string _ _ h
      · exact (by unfold LExpr.strConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickFVar_sound fctx .string _ _ h
      · exact (by unfold LExpr.strConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickOp_sound octx .string _ _ h
      · exact (by unfold LExpr.strConst; exact .const)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_11 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .real) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_real] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨r, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩) | ((⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩)))
    all_goals first
      | exact (by unfold LExpr.realConst; exact .const)
      | exact pickBVar_sound bctx .real _ _ h
      | exact pickFVar_sound fctx .real _ _ h
      | exact pickOp_sound octx .real _ _ h
  case h_12 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .real) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_real] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genRealConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .real) (genLExprBase fctx octx pctx tvars bctx n) .real),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .real)
                              (genLExprBase fctx octx pctx tvars bctx n .real)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .real).length > 0 then pickBVar bctx .real hv
           else genRealConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .real).length > 0 then pickFVar fctx .real hf
           else genRealConst),
         (2, fun () =>
           if ho : (opsOfType octx .real).length > 0 then pickOp octx .real ho
           else genRealConst),
         (4, fun () =>
           if hi : (findOpsInCtx octx .real).length > 0
           then genIndir octx .real (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .real),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .real
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .real)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genRealConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨r, _, rfl⟩ := he
      exact (by unfold LExpr.realConst; exact .const)
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · exact pickBVar_sound bctx .real _ _ h
      · exact (by unfold LExpr.realConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · exact pickFVar_sound fctx .real _ _ h
      · exact (by unfold LExpr.realConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · exact pickOp_sound octx .real _ _ h
      · exact (by unfold LExpr.realConst; exact .const)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_13 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.bitvec n)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨k, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)))
    all_goals first
      | exact (by unfold LExpr.bitvecConst; exact .const)
      | exact pickBVar_sound bctx _ _ _ h
      | exact pickFVar_sound fctx _ _ _ h
      | exact pickOp_sound octx _ _ _ h
  case h_14 m n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (m + 1) (.bitvec n)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genBitvecConst (G := SetGen.Set) n),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx m (.bitvec n)) (genLExprBase fctx octx pctx tvars bctx m) (.bitvec n)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx m .bool)
                              (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))
                              (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.bitvec n)).length > 0 then pickBVar bctx (.bitvec n) hv
           else genBitvecConst n),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.bitvec n)).length > 0 then pickFVar fctx (.bitvec n) hf
           else genBitvecConst n),
         (2, fun () =>
           if ho : (opsOfType octx (.bitvec n)).length > 0 then pickOp octx (.bitvec n) ho
           else genBitvecConst n),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.bitvec n)).length > 0
           then genIndir octx (.bitvec n) (genLExprBase fctx octx pctx tvars bctx m) hi
           else genLExprBase fctx octx pctx tvars bctx m (.bitvec n)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.bitvec n)
             (genLExprBase fctx octx pctx tvars bctx m)
             (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genBitvecConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨k, _, rfl⟩ := he
      exact (by unfold LExpr.bitvecConst; exact .const)
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx m _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx m _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx m _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx m _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx m _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickBVar_sound bctx _ _ _ h
      · exact (by unfold LExpr.bitvecConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickFVar_sound fctx _ _ _ h
      · exact (by unfold LExpr.bitvecConst; exact .const)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickOp_sound octx _ _ _ h
      · exact (by unfold LExpr.bitvecConst; exact .const)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx m σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx m _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx m σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx m _ a ha) e he
  case h_15 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .regex) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))
    all_goals first
      | exact pickBVar_sound bctx _ _ _ h
      | exact pickFVar_sound fctx _ _ _ h
      | exact pickOp_sound octx _ _ _ h
      | exact absurd h (by simp)
  case h_16 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .regex) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx octx tvars bctx n .regex) (genLExprBase fctx octx pctx tvars bctx n) .regex),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .regex)
                              (genLExprBase fctx octx pctx tvars bctx n .regex)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else if hf : (fvarsOfType fctx .regex).length > 0 then pickFVar fctx .regex hf
           else if ho : (opsOfType octx .regex).length > 0 then pickOp octx .regex ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx .regex).length > 0 then pickFVar fctx .regex hf
           else if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else default),
         (2, fun () =>
           if ho : (opsOfType octx .regex).length > 0 then pickOp octx .regex ho
           else if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx octx .regex).length > 0
           then genIndir octx .regex (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .regex),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .regex
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .regex)) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickFVar_sound fctx _ _ _ h
        | exact pickOp_sound octx _ _ _ h
        | exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickFVar_sound fctx _ _ _ h
        | exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickOp_sound octx _ _ _ h
        | exact absurd h (by simp)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_17 τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.map τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))
    all_goals first
      | exact pickBVar_sound bctx _ _ _ h
      | exact pickFVar_sound fctx _ _ _ h
      | exact pickOp_sound octx _ _ _ h
      | exact absurd h (by simp)
  case h_18 n τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) (.map τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx octx tvars bctx n (.map τ₁ τ₂)) (genLExprBase fctx octx pctx tvars bctx n) (.map τ₁ τ₂)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))
                              (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0 then pickFVar fctx (.map τ₁ τ₂) hf
           else if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0 then pickOp octx (.map τ₁ τ₂) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0 then pickFVar fctx (.map τ₁ τ₂) hf
           else if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0 then pickOp octx (.map τ₁ τ₂) ho
           else if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.map τ₁ τ₂)).length > 0
           then genIndir octx (.map τ₁ τ₂) (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.map τ₁ τ₂)
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickFVar_sound fctx _ _ _ h
        | exact pickOp_sound octx _ _ _ h
        | exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickFVar_sound fctx _ _ _ h
        | exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickOp_sound octx _ _ _ h
        | exact absurd h (by simp)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_19 τ₁ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.seq τ₁)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))
    all_goals first
      | exact pickBVar_sound bctx _ _ _ h
      | exact pickFVar_sound fctx _ _ _ h
      | exact pickOp_sound octx _ _ _ h
      | exact absurd h (by simp)
  case h_20 n τ₁ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) (.seq τ₁)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx octx tvars bctx n (.seq τ₁)) (genLExprBase fctx octx pctx tvars bctx n) (.seq τ₁)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.seq τ₁))
                              (genLExprBase fctx octx pctx tvars bctx n (.seq τ₁))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.seq τ₁)).length > 0 then pickBVar bctx (.seq τ₁) hv
           else if hf : (fvarsOfType fctx (.seq τ₁)).length > 0 then pickFVar fctx (.seq τ₁) hf
           else if ho : (opsOfType octx (.seq τ₁)).length > 0 then pickOp octx (.seq τ₁) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.seq τ₁)).length > 0 then pickFVar fctx (.seq τ₁) hf
           else if hv : (bvarsOfType bctx (.seq τ₁)).length > 0 then pickBVar bctx (.seq τ₁) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType octx (.seq τ₁)).length > 0 then pickOp octx (.seq τ₁) ho
           else if hv : (bvarsOfType bctx (.seq τ₁)).length > 0 then pickBVar bctx (.seq τ₁) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.seq τ₁)).length > 0
           then genIndir octx (.seq τ₁) (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n (.seq τ₁)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.seq τ₁)
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n (.seq τ₁))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', _, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hfn)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_sound fctx octx pctx tvars bctx n _ _ hc)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ ht)
                  (genLExprBase_sound fctx octx pctx tvars bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickFVar_sound fctx _ _ _ h
        | exact pickOp_sound octx _ _ _ h
        | exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickFVar_sound fctx _ _ _ h
        | exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      all_goals first
        | exact pickBVar_sound bctx _ _ _ h
        | exact pickOp_sound octx _ _ _ h
        | exact absurd h (by simp)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_21 =>
    -- The other type constructors. This branch gives one of the three leaves from the context, which
    -- are a bound variable, a free variable and an operator of arity 0 at the type `τ`. It is the same
    -- as the `.regex` case at the depth 0, so the same `pick*_sound` lemmas discharge it. Each leaf
    -- holds the annotation `τ`, so it is well-typed at `τ`. This case gives a leaf only at each depth,
    -- and that is what keeps the proof of this arm free of induction.
    simp only [mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))
    all_goals first
      | exact pickBVar_sound bctx _ _ _ h
      | exact pickFVar_sound fctx _ _ _ h
      | exact pickOp_sound octx _ _ _ h
      | exact absurd h (by simp)
  termination_by (depth, sizeOf τ)
  decreasing_by all_goals simp_wf; omega

-- ── The support of `Nat.arbitrary` at `SetGen.Set` ───────────────────
--
-- `Nat_arbitrary_support_set` is earlier in this file, beside `pickBitvecWidth`, which draws its width
-- from `Nat.arbitrary`.

/-- Every integer is reachable via `pick` between `(k : Int)` and `-(k+1)`. -/
private theorem Int_cover (z : Int) :
    (∃ k : Nat, k ∈ SetGen.support (Nat.arbitrary (G := SetGen.Set)) ∧ (↑k : Int) = z) ∨
    (∃ k : Nat, k ∈ SetGen.support (Nat.arbitrary (G := SetGen.Set)) ∧ (-(↑k + 1 : Int)) = z) := by
  cases z with
  | ofNat n => left; exact ⟨n, Nat_arbitrary_support_set n, rfl⟩
  | negSucc n => right; exact ⟨n, Nat_arbitrary_support_set n, by simp [Int.negSucc_eq]⟩

-- The support lemmas below follow the ones in `Basalt.Examples.ArbString`, and they hold for
-- `SetGen.Set` in place of `SPMF`.

/-- Every alphanumeric character is in the support of `Char.arbitrary` at `SetGen.Set`. -/
private theorem Char_arbitrary_support_set (c : Char) (hc : c ∈ alphanumChars) :
    c ∈ SetGen.support (Char.arbitrary (G := SetGen.Set)) := by
  simp only [Char.arbitrary]
  rw [mem_support_elements_iff (show alphanumChars ≠ [] from by decide +kernel)]
  exact hc

/-- Every alphanumeric char-list is in the support of `genAlphanumList` at `SetGen.Set`. -/
private theorem genAlphanumList_support_set (cs : List Char)
    (hcs : ∀ c ∈ cs, c ∈ alphanumChars) :
    cs ∈ SetGen.support (genAlphanumList (G := SetGen.Set)) := by
  induction cs with
  | nil =>
    rw [SetGen.support, genAlphanumList, listOf]
    simp [pick_mem_iff]
  | cons c cs ih =>
    rw [SetGen.support, genAlphanumList, listOf]
    simp only [pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
    right
    refine ⟨c, ?_, cs, ?_, rfl⟩
    · exact Char_arbitrary_support_set c (hcs c List.mem_cons_self)
    · exact ih (fun c' hc' => hcs c' (List.mem_cons_of_mem c hc'))

/-- Every alphanumeric string is in the support of `String.arbitrary` at `SetGen.Set`. -/
private theorem String_arbitrary_support_set (s : String)
    (hs : ∀ c ∈ s.toList, c ∈ alphanumChars) :
    s ∈ SetGen.support (String.arbitrary (G := SetGen.Set)) := by
  simp only [String.arbitrary, mem_support_map_iff]
  refine ⟨s.toList, genAlphanumList_support_set s.toList hs, ?_⟩
  exact String.ofList_toList.symm

-- ── The support of each adversarial primitive generator ──────────────
--
-- `genStrConst` and `genBitvecConst` draw from `StrataGenerators.PrimitiveGens`, which gives a
-- non-ASCII string and a bitvector with a bias toward a boundary value. Therefore the agreement
-- property for SMT can reach the cases about the overflow of a bitvector, and the cases about a string
-- and UTF-8. The lemmas below follow the two lemmas above, with `interestingChars` in the place of
-- `alphanumChars`.

open StrataGenerators.PrimitiveGens in
/-- Each character of `interestingChars` is in the support of
    `genInterestingChar`. -/
private theorem genInterestingChar_support_set (c : Char) (hc : c ∈ interestingChars) :
    c ∈ SetGen.support (genInterestingChar (G := SetGen.Set)) := by
  simp only [genInterestingChar]
  rw [mem_support_elements_iff interestingChars_ne_nil]
  exact hc

open StrataGenerators.PrimitiveGens in
/-- Each list of characters from `interestingChars` is in the support of
    `listOf genInterestingChar`. This lemma mirrors
    `genAlphanumList_support_set`. -/
private theorem genInterestingCharList_support_set (cs : List Char)
    (hcs : ∀ c ∈ cs, c ∈ interestingChars) :
    cs ∈ SetGen.support (listOf (genInterestingChar (G := SetGen.Set))) := by
  induction cs with
  | nil =>
    rw [SetGen.support, listOf]
    simp [pick_mem_iff]
  | cons c cs ih =>
    rw [SetGen.support, listOf]
    simp only [pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
    right
    refine ⟨c, ?_, cs, ?_, rfl⟩
    · exact genInterestingChar_support_set c (hcs c List.mem_cons_self)
    · exact ih (fun c' hc' => hcs c' (List.mem_cons_of_mem c hc'))

open StrataGenerators.PrimitiveGens in
/-- Each string over `interestingChars` is in the support of `genInterestingString`, at **each** length.
    The empty string is included.

    The `listOf` tail branch, which has the weight 1, is the witness, and that is why the branch exists.
    The main branch limits the length to `strMaxLen`. That branch alone therefore makes this lemma false,
    and it forces a limit on the length into `AllTypesSimple.strConst`. -/
private theorem genInterestingString_support_set (s : String)
    (hs : ∀ c ∈ s.toList, c ∈ interestingChars) :
    s ∈ SetGen.support (genInterestingString (G := SetGen.Set)) := by
  rw [genInterestingString, mem_support_frequency_iff]
  refine ⟨1, fun _ => String.ofList <$> listOf genInterestingChar,
    by simp, Nat.one_pos, ?_⟩
  rw [mem_support_map_iff]
  refine ⟨s.toList, genInterestingCharList_support_set s.toList hs, ?_⟩
  exact String.ofList_toList.symm

open StrataGenerators.PrimitiveGens in
/-- Each natural number is in the support of `natArbGeom`. `natArbGeom` is the geometric generator,
    which is a `pick` between `0` and `(· + 1)`. The completeness tail of `genRat` uses it. -/
private theorem natArbGeom_support_set (n : Nat) :
    n ∈ SetGen.support (natArbGeom (G := SetGen.Set)) := by
  induction n with
  | zero =>
    simp only [SetGen.support]
    rw [natArbGeom]
    simp [pick_mem_iff]
  | succ n ih =>
    simp only [SetGen.support] at ih ⊢
    rw [natArbGeom]
    simp only [pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
    right
    exact ⟨n, ih, rfl⟩

open StrataGenerators.PrimitiveGens in
/-- **Each** rational is in the support of `genRat`.

    The tail branch, which has no bound, gives this result. The bounded branch samples uniformly from a
    window, and few of its draws are therefore `0`. A window alone is not complete. The tail reaches each
    `r` through `Rat.mkRat_self : mkRat r.num r.den = r`. The proof splits on the sign of `r.num`, so a
    negative rational outside the window is also reachable. -/
private theorem genRat_support_set (r : Rat) :
    r ∈ SetGen.support (genRat (G := SetGen.Set)) := by
  rw [genRat, mem_support_frequency_iff]
  refine ⟨1, fun _ => do
    let n ← natArbGeom
    let d ← natArbGeom
    pick (fun _ => pure (mkRat (n : Int) d)) (fun _ => pure (mkRat (-(n : Int)) d)),
    by simp, Nat.one_pos, ?_⟩
  simp only [SetGen.Set.mem_bind, mem_support_iff, pick_mem_iff, SetGen.Set.mem_pure]
  refine ⟨r.num.natAbs, natArbGeom_support_set _, r.den, natArbGeom_support_set _, ?_⟩
  rcases Int.natAbs_eq r.num with h | h
  · left; rw [← h]; exact (Rat.mkRat_self r).symm
  · right
    have hneg : -((r.num.natAbs : Int)) = r.num := by omega
    rw [hneg]; exact (Rat.mkRat_self r).symm

/-- Each `n` in the range `[lo, hi]` is in the support of `chooseNat lo hi` at `SetGen.Set`. This lemma
    is the `SetGen` form of a lemma of Basalt. It proves only the direction that the lemmas below need,
    which goes from membership in the range to membership in the support. -/
private theorem chooseNat_support_set {lo hi n : Nat} (h : lo ≤ hi)
    (hn : lo ≤ n ∧ n ≤ hi) :
    n ∈ SetGen.support (chooseNat (G := SetGen.Set) lo hi h) := by
  simp only [chooseNat, SetGen.mem_support_map_iff]
  exact ⟨ULift.up ⟨n, hn⟩, by simp [hn], rfl⟩

open StrataGenerators.PrimitiveGens in
/-- **Each** `BitVec w` is in the support of `genBiasedBitVec w`.

    The uniform fallback branch of `genBiasedBitVec` gives this result. The pool of boundary values is a
    *bias*, and not a restriction, so the generator stays complete. The witness is the second branch,
    which has the weight 1, at `k = bv.toNat`. That value is in range, because `bv.isLt` says that `2^w`
    bounds `BitVec.toNat`. This is why the upper limit of the fallback must be `2^w - 1`, and nothing
    smaller. A smaller limit leaves most values of `bv` with no witness. -/
private theorem genBiasedBitVec_support_set {w : Nat} (bv : BitVec w) :
    bv ∈ SetGen.support (genBiasedBitVec (G := SetGen.Set) w) := by
  rw [genBiasedBitVec, mem_support_frequency_iff]
  refine ⟨1, fun _ => BitVec.ofNat w <$> chooseNat 0 (2 ^ w - 1) (Nat.zero_le _),
    by simp, Nat.one_pos, ?_⟩
  rw [mem_support_map_iff]
  refine ⟨bv.toNat, chooseNat_support_set _ ⟨Nat.zero_le _, ?_⟩, by simp⟩
  exact Nat.le_sub_one_of_lt bv.isLt

-- ── emptyNames predicate ──────────────────────────────────────────────

/-- Each binder name in the expression is the empty string. -/
def emptyNames : LExpr' → Prop
  | .boolConst () _                  => True
  | .intConst () _                   => True
  | .bvar () _                       => True
  | .fvar () _ _                     => True
  | .op () _ _                       => True
  | .abs () name _ body              => name = "" ∧ emptyNames body
  | .app () fn arg                   => emptyNames fn ∧ emptyNames arg
  | .ite () c t e                    => emptyNames c ∧ emptyNames t ∧ emptyNames e
  | .eq () e₁ e₂                     => emptyNames e₁ ∧ emptyNames e₂
  | .quant () _ name _ tr body       => name = "" ∧ emptyNames tr ∧ emptyNames body
  | .const () _                      => True

-- ── termDepth measure ─────────────────────────────────────────────────

/-- The depth of the tree of a term, which is the smallest `depth` parameter at which `genLExpr` can
    give the term. The value agrees with the fuel that the generator uses, for four reasons:
    - Each leaf expression has the depth 0. A leaf is a bound variable, a free variable, an operator or
      a constant.
    - Each compound constructor adds 1. Such a constructor is `abs`, `app`, `ite`, `eq` or `quant`.
    - The generator recurses at `depth - 1` for each child.
    - The `quant` case also adds `monoTyDepth τ`, because the generator calls `genLMonoTy` at
      `depth - 1`, and that call needs `monoTyDepth τ ≤ depth - 1`. -/
def termDepth (bctx : BVarCtx) : LExpr' → Nat
  | .boolConst () _       => 0
  | .intConst () _        => 0
  | .bvar () _            => 0
  | .fvar () _ _          => 0
  | .op () _ _            => 0
  | .abs () _ (some τ₁) body => termDepth (τ₁ :: bctx) body + 1
  | .app () fn arg        => max (termDepth bctx fn) (termDepth bctx arg) + 1
  | .ite () c t e         => max (termDepth bctx c) (max (termDepth bctx t) (termDepth bctx e)) + 1
  | .eq () e₁ e₂          => max (termDepth bctx e₁) (termDepth bctx e₂) + 1
  | .quant () _ _ (some τ) tr body =>
      max (monoTyDepth τ) (max (termDepth (τ :: bctx) tr) (termDepth (τ :: bctx) body)) + 1
  | _                     => 0

/-- Each type annotation in an expression is simple, it has a bounded depth, and each of its `ftvar`
    names comes from `tvars`. The parameter `n` falls by 1 at each compound level of the expression,
    which agrees with the fuel that the generator uses. At the level `n + 1`, each intermediate type
    from `genLMonoTy n` has a depth that is not more than `n`, and each subexpression satisfies
    `AllTypesSimple n`. -/
inductive AllTypesSimple (tvars : List TyIdentifier) : Nat → BVarCtx → LExpr' → Prop where
  | boolConst   : AllTypesSimple tvars n bctx (.boolConst () b)
  | intConst    : AllTypesSimple tvars n bctx (.intConst () k)
  | strConst    : (∀ c ∈ s.toList, c ∈ StrataGenerators.PrimitiveGens.interestingChars) →
                  AllTypesSimple tvars n bctx (.strConst () s)
  | realConst   : (r : Rat) →
                  AllTypesSimple tvars n bctx (.realConst () r)
  | bitvecConst : (w : Nat) → (bv : BitVec w) →
                  AllTypesSimple tvars n bctx (.bitvecConst () w bv)
  | bvar      : AllTypesSimple tvars n bctx (.bvar () i)
  | fvar      : AllTypesSimple tvars n bctx (.fvar () x (some τ))
  | op        : AllTypesSimple tvars n bctx (.op () o (some τ))
  | abs       : τ₁ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) →
                AllTypesSimple tvars n (τ₁ :: bctx) body →
                AllTypesSimple tvars (n + 1) bctx (.abs () "" (some τ₁) body)
  | app       : (τ' : LMonoTy) →
                HasTypeA' bctx arg τ' →
                τ' ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) →
                AllTypesSimple tvars n bctx fn → AllTypesSimple tvars n bctx arg →
                AllTypesSimple tvars (n + 1) bctx (.app () fn arg)
  | ite       : AllTypesSimple tvars n bctx c → AllTypesSimple tvars n bctx t →
                AllTypesSimple tvars n bctx e →
                AllTypesSimple tvars (n + 1) bctx (.ite () c t e)
  | eq        : (τ' : LMonoTy) →
                HasTypeA' bctx e₁ τ' → HasTypeA' bctx e₂ τ' →
                τ' ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) →
                AllTypesSimple tvars n bctx e₁ → AllTypesSimple tvars n bctx e₂ →
                AllTypesSimple tvars (n + 1) bctx (.eq () e₁ e₂)
  | quant     : τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) →
                (τ_tr : LMonoTy) →
                τ_tr ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) →
                HasTypeA' (τ :: bctx) tr τ_tr →
                AllTypesSimple tvars n (τ :: bctx) tr →
                AllTypesSimple tvars n (τ :: bctx) body →
                AllTypesSimple tvars (n + 1) bctx (.quant () k "" (some τ) tr body)

-- ── termDepth bound for genLExpr ──────────────────────────────────────

open StrataGenerators.IndirSupport in
/-- The `termDepth` of an application spine. The spine adds one level for each argument, above the
    largest depth of the head and of the arguments. Therefore a full application of an operator of the
    arity `k` costs `k` levels, and not one. -/
theorem termDepth_mkApps_le (bctx : BVarCtx) (base : LExpr') (args : List LExpr')
    (d : Nat) (hbase : termDepth bctx base ≤ d)
    (hargs : ∀ a ∈ args, termDepth bctx a ≤ d) :
    termDepth bctx (mkApps base args) ≤ d + args.length := by
  -- The induction is on `args`, and it generalizes the head *and* the bound. After the first
  -- argument, the head is `.app base a` at the bound `d + 1`, and each remaining argument still has the
  -- bound `d`, which is not more than `d + 1`.
  induction args generalizing base d with
  | nil => simpa [mkApps] using hbase
  | cons a rest ih =>
    have hstep : termDepth bctx (LExpr.app () base a) ≤ d + 1 := by
      show max (termDepth bctx base) (termDepth bctx a) + 1 ≤ d + 1
      have := hargs a (by simp)
      omega
    have hrest : ∀ x ∈ rest, termDepth bctx x ≤ d + 1 :=
      fun x hx => Nat.le_trans (hargs x (by simp [hx])) (by omega)
    -- `foldl_cons` gives `mkApps base (a :: rest) = mkApps (.app base a) rest`. The proof rewrites
    -- with that equation and does not unfold `mkApps`, so that the conclusion of the recursive call is
    -- *syntactically* about the same term.
    have hfold : mkApps base (a :: rest) = mkApps (LExpr.app () base a) rest := by
      simp only [mkApps, List.foldl_cons]
    rw [hfold, List.length_cons]
    have hih := ih (LExpr.app () base a) (d + 1) hstep hrest
    -- `hih : … ≤ (d + 1) + rest.length`; the goal is `… ≤ d + (rest.length + 1)`.
    omega

open StrataGenerators.IndirSupport in
/-- The depth budget that the generator needs at the index `depth`, when each level can emit an
    application spine of an arity up to `K`. -/
abbrev genDepthBudget (K depth : Nat) : Nat := depthBudget K depth

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
open StrataGenerators.IndirSupport in
/-- The `termDepth` of each expression in the support of `genLExprBase` at the depth `depth` is not
    more than `depthBudget K depth`. Here `K` is `max (opCtxArity octx) maxNumArgs`, and it is 1 or
    more. `K` is the largest arity that one level can emit.

    ## Why the bound is `depthBudget K depth` and not `depth`

    `termDepth` charges **one level for each `app` node**. Therefore a full application of an operator
    of the arity `k` is a spine of `k` nested `app` nodes, and it costs `k`. At `depth = 1`, the Indir
    branch can emit `Int.Add #1 #2`, with two leaf arguments from `genLExprBase` at the depth 0. The
    `termDepth` of that term is 2, which is more than 1. Therefore a bound of `depth` alone is false for
    this generator.

    `depthBudget K depth` is the honest bound. Its value is `depth * K`, and the definition is
    recursive, so that the arithmetic in the proof stays linear. Each of the `depth` levels can spend up
    to `K` on a spine. The two limits on the arity are real. `findOpsInCtx_length_le` bounds the
    monomorphic rule by `opCtxArity octx`, which comes from the nesting of the arrows in the context.
    `findPolymorphicOps_length_le` bounds the polymorphic rule by `maxNumArgs`, because
    `findPolymorphicOps` skips a scheme of a larger arity.

    ### The consequence for `genLExprBase_complete`

    The premise `hdepth : termDepth bctx e ≤ depth` of `genLExprBase_complete` is enough for
    completeness, and it describes the terms that the *structural* rules reach. It does not describe
    reachability exactly, because the support is strictly larger than `{e | termDepth e ≤ depth}`.
    Completeness is therefore a statement in one direction, and this theorem is its weaker companion. -/
theorem genLExprBase_termDepth_bound (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx)
    (depth : Nat) (K : Nat)
    (hK : 1 ≤ K) (hKops : opCtxArity octx ≤ K) (hKpoly : 3 ≤ K)
    -- Each argument type of the two Indir rules must be generable, at each target type. The recursion
    -- bounds the depth of an argument by an application of this theorem at the type of that argument,
    -- and this theorem is indexed by generability.
    --
    -- This is a side condition, and not a theorem. `findOpsInCtx` reads an argument type directly from
    -- an arrow type of `octx`, and `findPolymorphicOps` builds one when it substitutes a sampled type
    -- into a scheme. Nothing in the generator holds either one to a generable type. Therefore an
    -- unusual entry of `octx`, such as a `tcons "Foo"` that the generator does not handle, can make a
    -- rule ask for an argument type that is not generable. For `coreMonoOps` and `corePolyOps` the
    -- condition is cheap to discharge, because each of their argument types is built from `int`,
    -- `bool`, `string`, `real`, `regex`, `Sequence`, `Map` and an arrow.
    --
    -- The condition quantifies over the binder context `bc` as well as the target type `σ`. The `abs`
    -- branch and the `quant` branch recurse under an extended binder context, and `bc` goes into
    -- `generableTypesFromCtx`, and therefore into the sampled types of the polymorphic rule.
    (hSimpleArgs : ∀ bc σ m,
      (∀ (name : String) (argTys : List LMonoTy),
        (name, argTys) ∈ findOpsInCtx octx σ →
        ∀ σ' ∈ argTys, ∃ k, σ' ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars k)) ∧
      (∀ (sampledTys : List LMonoTy) (name : String) (argTys : List LMonoTy),
        (name, argTys) ∈ findPolymorphicOps pctx σ
          (generableTypesFromCtx bc fctx octx) sampledTys m →
        ∀ σ' ∈ argTys, ∃ k, σ' ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars k)))
    (τ : LMonoTy) (hτ : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (e : LExpr')
    (he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth τ)) :
    termDepth bctx e ≤ depthBudget K depth := by
  match depth with
  | 0 =>
    revert he
    refine genLMonoTy_mem_cases ?bool ?int ?string ?real ?regex ?bitvec ?ftvar ?arrow ?map ?seq hτ
    case bool =>
      intro he
      rw [norm_bool] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff,
        mem_support_iff, SetGen.mem_dite] at he
      rcases he with (rfl | rfl) | ((⟨_, h⟩ | ⟨_, rfl | rfl⟩) | ((⟨_, h⟩ | ⟨_, rfl | rfl⟩) | (⟨_, h⟩ | ⟨_, rfl | rfl⟩)))
      all_goals first | rfl | (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl))
    case int =>
      intro he
      rw [norm_int] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      rcases he with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ((⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩) | ((⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩)))
      all_goals first | rfl | (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl))
    case string =>
      intro he
      rw [norm_string] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩) | ((⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩)))
      all_goals first | rfl | (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl))
    case real =>
      intro he
      rw [norm_real] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩) | ((⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩)))
      all_goals first | rfl | (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl))
    case bitvec =>
      intro w he
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩) | ((⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩)))
      all_goals first | rfl | (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl))
    case arrow =>
      intro τ₁ τ₂ hs₁ hs₂ he
      rw [norm_arrow] at he; simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff,
        mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
      rcases he with (⟨_, h⟩ | ⟨_, h⟩) | ((⟨_, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩))

      all_goals (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | exact absurd h (by simp))
    case ftvar =>
      intro name hname he
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
                 bot_mem_iff] at he
      rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
        ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
         (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))

      all_goals (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | exact absurd h (by simp))
    case regex =>
      intro he
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
                 bot_mem_iff] at he
      rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
        ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
         (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))

      all_goals (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | exact absurd h (by simp))
    case map =>
      intro τ₁ τ₂ hs₁ hs₂ he
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff,
        mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
      rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
        ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
         (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))

      all_goals (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | exact absurd h (by simp))
    case seq =>
      intro τ₁ hs he
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
                 bot_mem_iff] at he
      rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
        ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
         (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))

      all_goals (
        first
        | (rw [mem_support_pickBVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickFVar_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | (rw [mem_support_pickOp_iff] at h
           obtain ⟨_, _, rfl⟩ := h; rfl)
        | exact absurd h (by simp))
  | n + 1 =>
    revert he
    refine genLMonoTy_mem_cases ?bool ?int ?string ?real ?regex ?bitvec ?ftvar ?arrow ?map ?seq hτ
    case bool =>
      intro he
      rw [norm_bool] at he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genBoolConst, genApp, genIte, genEq, genQuant, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      · rcases he with rfl | rfl; all_goals exact Nat.zero_le _
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ genLMonoTy_mem_bool) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ he'
        omega
      · obtain ⟨τ', hτ'm, e₁, he₁, e₂, he₂, rfl⟩ := he
        show termDepth bctx (.eq () e₁ e₂) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genGenerableTy_support _ _ _ _ _ _).mp hτ'm⟩ _ he₁
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genGenerableTy_support _ _ _ _ _ _).mp hτ'm⟩ _ he₂
        omega
      · obtain ⟨τ', hτ'm, τ_tr, hτ_tr_m, tr, htr, body, hbody, rfl⟩ := he
        show termDepth bctx (.quant () .all "" (some τ') tr body) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars (τ' :: bctx) n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genGenerableTy_support _ _ _ _ _ _).mp hτ_tr_m⟩ _ htr
        have := genLExprBase_termDepth_bound fctx octx pctx tvars (τ' :: bctx) n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hbody
        have := genLMonoTy_mem_depth ((genGenerableTy_support _ _ _ _ _ _).mp hτ'm)
        have := le_depthBudget_self K hK n
        omega
      · obtain ⟨τ', hτ'm, τ_tr, hτ_tr_m, tr, htr, body, hbody, rfl⟩ := he
        show termDepth bctx (.quant () .exist "" (some τ') tr body) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars (τ' :: bctx) n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genGenerableTy_support _ _ _ _ _ _).mp hτ_tr_m⟩ _ htr
        have := genLExprBase_termDepth_bound fctx octx pctx tvars (τ' :: bctx) n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hbody
        have := genLMonoTy_mem_depth ((genGenerableTy_support _ _ _ _ _ _).mp hτ'm)
        have := le_depthBudget_self K hK n
        omega

      -- Five goals remain: the three leaf `pick*` branches, the Indir branch and the IndirPoly
      -- branch. A `first` combinator discharges them, and not positional bullets, because the order of
      -- the goals changes with the type case. A positional script assigns them to the wrong goals
      -- without a message.
      all_goals (
        first
        | (rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
           · first
             | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
             | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
             | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
           all_goals simp [termDepth])
        -- The Indir branch and the IndirPoly branch.
        | (rcases he with ⟨_, he⟩ | ⟨_, he⟩
           · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
               (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
               (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
                 hKpoly hSimpleArgs σ hσ a ha)
               (fun nm annot args hall =>
                 termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
               _ e he) ?_
             simp only [depthBudget]; omega
           · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
               (depthBudget_mono_le K (by omega)))
        -- The IndirPoly branch. The pair of `refine` and `exact` appears two times, and the second
        -- time is after a normalization step with `mem_support_iff`. In some type cases the `simp only`
        -- above already unfolds `he` to `support …`, and in others it leaves `e ∈ g ()`. `simp only`
        -- gives an error, and not a no-op, when it has nothing to rewrite.
        | (simp only [mem_support_iff] at he
           refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
             (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
             (hSimpleArgs bctx _ 3).2
             (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs σ hσ a ha)
             (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
               hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
             (fun nm annot args hall =>
               termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
             e he) ?_
           simp only [depthBudget]; omega)
        | (refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
             (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
             (hSimpleArgs bctx _ 3).2
             (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs σ hσ a ha)
             (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
               hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
             (fun nm annot args hall =>
               termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
             e he) ?_
           simp only [depthBudget]; omega))
    case int =>
      intro he
      rw [norm_int] at he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genIntConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      · rcases he with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩; all_goals simp [termDepth]
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ genLMonoTy_mem_int) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_int _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_int _ he'
        omega

      all_goals (
        first
        | (
          rcases he with ⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩
          · first
            | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
          all_goals simp [termDepth]
  )
        -- The Indir branch and the IndirPoly branch.
        | (rcases he with ⟨_, he⟩ | ⟨_, he⟩
           · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
               (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
               (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
                 hKpoly hSimpleArgs σ hσ a ha)
               (fun nm annot args hall =>
                 termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
               _ e he) ?_
             simp only [depthBudget]; omega
           · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
               (depthBudget_mono_le K (by omega)))
        | (first | simp only [mem_support_iff] at he | skip
           refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
             (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
             (hSimpleArgs bctx _ 3).2
             (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs σ hσ a ha)
             (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
               hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
             (fun nm annot args hall =>
               termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
             e he) ?_
           simp only [depthBudget]; omega)
        )
    case string =>
      intro he
      rw [norm_string] at he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genStrConst, genApp, genIte, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      · obtain ⟨_, _, rfl⟩ := he; simp [termDepth]
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ genLMonoTy_mem_string) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_string _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_string _ he'
        omega

      all_goals (
        first
        | (
          rcases he with ⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩
          · first
            | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
          · simp [termDepth]
  )
        -- The Indir branch and the IndirPoly branch.
        | (rcases he with ⟨_, he⟩ | ⟨_, he⟩
           · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
               (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
               (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
                 hKpoly hSimpleArgs σ hσ a ha)
               (fun nm annot args hall =>
                 termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
               _ e he) ?_
             simp only [depthBudget]; omega
           · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
               (depthBudget_mono_le K (by omega)))
        | (first | simp only [mem_support_iff] at he | skip
           refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
             (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
             (hSimpleArgs bctx _ 3).2
             (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs σ hσ a ha)
             (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
               hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
             (fun nm annot args hall =>
               termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
             e he) ?_
           simp only [depthBudget]; omega)
        )
    case real =>
      intro he
      rw [norm_real] at he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genRealConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      · obtain ⟨_, _, rfl⟩ := he; simp [termDepth]
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ genLMonoTy_mem_real) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_real _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_real _ he'
        omega

      all_goals (
        first
        | (
          rcases he with ⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩
          · first
            | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
          · simp [termDepth]
  )
        -- The Indir branch and the IndirPoly branch.
        | (rcases he with ⟨_, he⟩ | ⟨_, he⟩
           · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
               (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
               (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
                 hKpoly hSimpleArgs σ hσ a ha)
               (fun nm annot args hall =>
                 termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
               _ e he) ?_
             simp only [depthBudget]; omega
           · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
               (depthBudget_mono_le K (by omega)))
        | (first | simp only [mem_support_iff] at he | skip
           refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
             (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
             (hSimpleArgs bctx _ 3).2
             (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs σ hσ a ha)
             (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
               hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
             (fun nm annot args hall =>
               termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
             e he) ?_
           simp only [depthBudget]; omega)
        )
    case bitvec =>
      intro w he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genBitvecConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      · obtain ⟨_, _, rfl⟩ := he; simp [termDepth]
      · obtain ⟨τ', hτ'n, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _
          (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'n⟩
            genLMonoTy_mem_bitvec) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'n⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bitvec _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bitvec _ he'
        omega

      all_goals (
        first
        | (
          rcases he with ⟨_, h⟩ | ⟨_, ⟨_, _, rfl⟩⟩
          · first
            | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
          · simp [termDepth]
  )
        -- The Indir branch and the IndirPoly branch.
        | (rcases he with ⟨_, he⟩ | ⟨_, he⟩
           · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
               (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
               (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
                 hKpoly hSimpleArgs σ hσ a ha)
               (fun nm annot args hall =>
                 termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
               _ e he) ?_
             simp only [depthBudget]; omega
           · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
               (depthBudget_mono_le K (by omega)))
        | (first | simp only [mem_support_iff] at he | skip
           refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
             (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
             (hSimpleArgs bctx _ 3).2
             (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs σ hσ a ha)
             (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
               hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
             (fun nm annot args hall =>
               termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
             e he) ?_
           simp only [depthBudget]; omega)
        )
    case arrow =>
      intro τ₁ τ₂ hs₁ hs₂ he
      rw [norm_arrow] at he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genAbs, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
      · obtain ⟨body, hbody, rfl⟩ := he
        show termDepth bctx (.abs () "" (some τ₁) body) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars (τ₁ :: bctx) n K hK hKops hKpoly hSimpleArgs _ hs₂ _ hbody
        omega
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ (genLMonoTy_mem_arrow hs₁ hs₂)) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow hs₁ hs₂) _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow hs₁ hs₂) _ he'
        omega

      all_goals (
        first
        | (
          rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
          · first
            | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
            | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
          · show termDepth bctx (.abs () "" (some τ₁) body) ≤ depthBudget K (n + 1); unfold termDepth
            simp only [depthBudget]
            have := genLExprBase_termDepth_bound fctx octx pctx tvars (τ₁ :: bctx) n K hK hKops hKpoly hSimpleArgs _ hs₂ _ hbody
            omega
  )
        -- The Indir branch and the IndirPoly branch.
        | (rcases he with ⟨_, he⟩ | ⟨_, he⟩
           · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
               (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
               (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
                 hKpoly hSimpleArgs σ hσ a ha)
               (fun nm annot args hall =>
                 termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
               _ e he) ?_
             simp only [depthBudget]; omega
           · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
               (depthBudget_mono_le K (by omega)))
        | (first | simp only [mem_support_iff] at he | skip
           refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
             (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
             (hSimpleArgs bctx _ 3).2
             (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
               hKpoly hSimpleArgs σ hσ a ha)
             (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
               hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
             (fun nm annot args hall =>
               termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
             e he) ?_
           simp only [depthBudget]; omega)
        )
    case ftvar =>
      intro name hname he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ (genLMonoTy_mem_ftvar hname)) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_ftvar hname) _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_ftvar hname) _ he'
        omega
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      -- The Indir branch and the IndirPoly branch.
      · rcases he with ⟨_, he⟩ | ⟨_, he⟩
        · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
            (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
            (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
              hKpoly hSimpleArgs σ hσ a ha)
            (fun nm annot args hall =>
              termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
            _ e he) ?_
          simp only [depthBudget]; omega
        · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
            hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
            (depthBudget_mono_le K (by omega))
      · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
          (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
          (hSimpleArgs bctx _ 3).2
          (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
            hKpoly hSimpleArgs σ hσ a ha)
          (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
            hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
          (fun nm annot args hall =>
            termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
          e he) ?_
        simp only [depthBudget]; omega
    case regex =>
      intro he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ genLMonoTy_mem_regex) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_regex _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_regex _ he'
        omega
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      -- The Indir branch and the IndirPoly branch.
      · rcases he with ⟨_, he⟩ | ⟨_, he⟩
        · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
            (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
            (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
              hKpoly hSimpleArgs σ hσ a ha)
            (fun nm annot args hall =>
              termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
            _ e he) ?_
          simp only [depthBudget]; omega
        · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
            hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
            (depthBudget_mono_le K (by omega))
      · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
          (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
          (hSimpleArgs bctx _ 3).2
          (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
            hKpoly hSimpleArgs σ hσ a ha)
          (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
            hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
          (fun nm annot args hall =>
            termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
          e he) ?_
        simp only [depthBudget]; omega
    case map =>
      intro τ₁ τ₂ hs₁ hs₂ he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ (genLMonoTy_mem_map hs₁ hs₂)) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_map hs₁ hs₂) _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_map hs₁ hs₂) _ he'
        omega
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      -- The Indir branch and the IndirPoly branch.
      · rcases he with ⟨_, he⟩ | ⟨_, he⟩
        · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
            (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
            (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
              hKpoly hSimpleArgs σ hσ a ha)
            (fun nm annot args hall =>
              termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
            _ e he) ?_
          simp only [depthBudget]; omega
        · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
            hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
            (depthBudget_mono_le K (by omega))
      · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
          (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
          (hSimpleArgs bctx _ 3).2
          (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
            hKpoly hSimpleArgs σ hσ a ha)
          (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
            hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
          (fun nm annot args hall =>
            termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
          e he) ?_
        simp only [depthBudget]; omega
    case seq =>
      intro τ₁ hs he
      simp only [genLExprBase] at he
      rw [mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp only [genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
        SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
      · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
        show termDepth bctx (.app () fn arg) ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_arrow ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ (genLMonoTy_mem_seq hs)) _ hfn
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ ⟨_, (genAppArgTy_support _ _ _ _ _ _ _).mp hτ'm⟩ _ harg
        omega
      · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
        show termDepth bctx (.ite () c t e') ≤ depthBudget K (n + 1); unfold termDepth
        simp only [depthBudget]
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ genLMonoTy_mem_bool _ hc
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_seq hs) _ ht
        have := genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly hSimpleArgs _ (genLMonoTy_mem_seq hs) _ he'
        omega
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
        all_goals first
          | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.zero_le _)
          | exact absurd h (by simp)
      -- The Indir branch and the IndirPoly branch.
      · rcases he with ⟨_, he⟩ | ⟨_, he⟩
        · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndir_measure_le
            (m := termDepth bctx) octx _ _ (depthBudget K n) (hSimpleArgs bctx _ 3).1
            (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
              hKpoly hSimpleArgs σ hσ a ha)
            (fun nm annot args hall =>
              termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
            _ e he) ?_
          simp only [depthBudget]; omega
        · exact Nat.le_trans (genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
            hKpoly hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) e he)
            (depthBudget_mono_le K (by omega))
      · refine Nat.le_trans (StrataGenerators.IndirSupport.genIndirPolyCore_measure_le
          (m := termDepth bctx) fctx octx pctx bctx _ _ _ 3 (depthBudget K n) (depthBudget K n)
          (hSimpleArgs bctx _ 3).2
          (fun σ hσ a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops
            hKpoly hSimpleArgs σ hσ a ha)
          (fun a ha => genLExprBase_termDepth_bound fctx octx pctx tvars bctx n K hK hKops hKpoly
            hSimpleArgs _ (by first
              | exact genLMonoTy_mem_bool
              | exact genLMonoTy_mem_int
              | exact genLMonoTy_mem_string
              | exact genLMonoTy_mem_real
              | exact genLMonoTy_mem_regex
              | exact genLMonoTy_mem_bitvec
              | exact genLMonoTy_mem_ftvar hname
              | exact genLMonoTy_mem_arrow hs₁ hs₂
              | exact genLMonoTy_mem_map hs₁ hs₂
              | exact genLMonoTy_mem_seq hs
              | assumption) a ha)
          (fun nm annot args hall =>
            termDepth_mkApps_le bctx _ args _ (by simp [termDepth]) hall)
          e he) ?_
        simp only [depthBudget]; omega
  termination_by (depth, sizeOf τ)
  decreasing_by all_goals simp_wf; omega

-- ── Completeness for genLExpr ─────────────────────────────────────────

/-- An inversion lemma. If `.eq () e₁ e₂` has the type `τ`, then `τ` is `.bool`. -/
private theorem eq_hasType_bool {bctx : BVarCtx} {τ : LMonoTy} {e₁ e₂ : LExpr'}
    (h : HasTypeA' bctx (.eq () e₁ e₂) τ) : τ = .bool := by cases h with | eq _ _ => rfl

/-- An inversion lemma. If `.quant () k name (some qty) tr body` has the type `τ`, then `τ` is
    `.bool`. -/
private theorem quant_hasType_bool {bctx : BVarCtx} {τ : LMonoTy} {k name qty tr body}
    (h : HasTypeA' bctx (.quant () k name (some qty) tr body) τ) : τ = .bool := by
  cases h with | quant _ _ => rfl

/-- A predicate that says two things. Each free-variable name of the expression is in `fctx`, at the
    correct type. Each operator name of the expression is in the factory `F`. -/
def allVarsInCtx (fctx : FVarCtx) (octx : OpCtx) : LExpr' → Prop
  | .boolConst () _              => True
  | .intConst () _               => True
  | .bvar () _                   => True
  | .fvar () x (some τ)         => (x.name, τ) ∈ fctx
  | .fvar () _ none              => True
  | .op () o (some τ)           => (o.name, τ) ∈ octx.ops
  | .op () _ none                => True
  | .abs () _ _ body             => allVarsInCtx fctx octx body
  | .app () fn arg               => allVarsInCtx fctx octx fn ∧ allVarsInCtx fctx octx arg
  | .ite () c t e                => allVarsInCtx fctx octx c ∧ allVarsInCtx fctx octx t ∧ allVarsInCtx fctx octx e
  | .eq () e₁ e₂                 => allVarsInCtx fctx octx e₁ ∧ allVarsInCtx fctx octx e₂
  | .quant () _ _ _ tr body      => allVarsInCtx fctx octx tr ∧ allVarsInCtx fctx octx body
  | .const () _                  => True

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- Completeness of `genLExprBase`. Each well-typed expression whose `termDepth` is inside the depth
    budget is in the support. The premise `hdepth` describes the terms that the structural rules
    reach. -/
theorem genLExprBase_complete (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (e : LExpr')
    (hwt : HasTypeA' bctx e τ)
    (hnames : emptyNames e)
    (hvars : allVarsInCtx fctx octx e)
    (hats : AllTypesSimple tvars depth bctx e)
    (hdepth : termDepth bctx e ≤ depth) :
    e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth τ) := by
  match depth with
  | 0 =>
    revert hwt
    refine genLMonoTy_mem_cases ?bool ?int ?string ?real ?regex ?bitvec ?ftvar ?arrow ?map ?seq hτ
    case bool =>
      intro hwt
      rw [norm_bool]
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_pure,
        mem_support_iff, SetGen.mem_dite]
      cases hats with
      | @boolConst _ _ b =>
        cases hwt with
        | const =>
          left
          cases b with
          | true => left; rfl
          | false => right; rfl
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.int])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.string])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.real])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool])
      | bvar =>
        cases hwt with
        | bvar hget =>
          right; left; left
          have hlen : (bvarsOfType bctx .bool).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .bool _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx .bool _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .bool).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .bool _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx .bool _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .bool).length > 0 := by
            have := (opsOfType_mem_iff octx .bool _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx .bool _ hmem hlen⟩
    case int =>
      intro hwt
      rw [norm_int]
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
        mem_support_iff, SetGen.mem_dite]
      cases hats with
      | intConst =>
        cases hwt with
        | const =>
          left
          have hic := Int_cover (by assumption : Int)
          rcases hic with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
          · left; exact ⟨k, hk, rfl⟩
          · right; exact ⟨k, hk, rfl⟩
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.int])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.string])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.real])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int])
      | bvar =>
        cases hwt with
        | bvar hget =>
          right; left; left
          have hlen : (bvarsOfType bctx .int).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .int _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx .int _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .int).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .int _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx .int _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .int).length > 0 := by
            have := (opsOfType_mem_iff octx .int _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx .int _ hmem hlen⟩
    case string =>
      intro hwt
      rw [norm_string]
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
        mem_support_iff, SetGen.mem_dite]
      cases hats with
      | strConst halpha =>
        cases hwt with
        | const =>
          left
          exact ⟨_, genInterestingString_support_set _ halpha, by simp [LExpr.strConst]⟩
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.string])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.string])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string, LMonoTy.real])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string])
      | bvar =>
        cases hwt with
        | bvar hget =>
          right; left; left
          have hlen : (bvarsOfType bctx .string).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .string _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx .string _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .string).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .string _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx .string _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .string).length > 0 := by
            have := (opsOfType_mem_iff octx .string _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx .string _ hmem hlen⟩
    case real =>
      intro hwt
      rw [norm_real]
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
        mem_support_iff, SetGen.mem_dite]
      cases hats with
      | realConst r =>
        cases hwt with
        | const =>
          left
          exact ⟨r, genRat_support_set r, rfl⟩
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.real])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.real])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string, LMonoTy.real])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.real])
      | bvar =>
        cases hwt with
        | bvar hget =>
          right; left; left
          have hlen : (bvarsOfType bctx .real).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .real _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx .real _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .real).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .real _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx .real _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .real).length > 0 := by
            have := (opsOfType_mem_iff octx .real _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx .real _ hmem hlen⟩
    case bitvec =>
      intro w hwt
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
        mem_support_iff, SetGen.mem_dite]
      cases hats with
      | bitvecConst _ _ =>
        cases hwt with
        | const =>
          left
          exact ⟨_, genBiasedBitVec_support_set _, rfl⟩
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.real])
      | bvar =>
        cases hwt with
        | bvar hget =>
          right; left; left
          have hlen : (bvarsOfType bctx (.bitvec w)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.bitvec w) _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx (.bitvec w) _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.bitvec w)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.bitvec w) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx (.bitvec w) _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.bitvec w)).length > 0 := by
            have := (opsOfType_mem_iff octx (.bitvec w) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx (.bitvec w) _ hmem hlen⟩
    case arrow =>
      intro τ₁ τ₂ hs₁ hs₂ hwt
      rw [norm_arrow]
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff,
        mem_support_iff, SetGen.mem_dite, bot_mem_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.arrow])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.arrow])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string, LMonoTy.arrow])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.real, LMonoTy.arrow])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.arrow])
      | bvar =>
        cases hwt with
        | bvar hget =>
          left; left
          have hlen : (bvarsOfType bctx (.arrow τ₁ τ₂)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.arrow τ₁ τ₂) _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx (.arrow τ₁ τ₂) _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.arrow τ₁ τ₂) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx (.arrow τ₁ τ₂) _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.arrow τ₁ τ₂)).length > 0 := by
            have := (opsOfType_mem_iff octx (.arrow τ₁ τ₂) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx (.arrow τ₁ τ₂) _ hmem hlen⟩
    case ftvar =>
      intro name hname hwt
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite, bot_mem_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.bool] at h)
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.int] at h)
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.string] at h)
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.real] at h)
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty] at h)
      | bvar =>
        cases hwt with
        | bvar hget =>
          left; left
          have hlen : (bvarsOfType bctx (.ftvar name)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.ftvar name) _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx (.ftvar name) _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.ftvar name)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.ftvar name) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx (.ftvar name) _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.ftvar name)).length > 0 := by
            have := (opsOfType_mem_iff octx (.ftvar name) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx (.ftvar name) _ hmem hlen⟩
    case regex =>
      intro hwt
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite, bot_mem_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.bool, LMonoTy.regex] at h)
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.int, LMonoTy.regex] at h)
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.string, LMonoTy.regex] at h)
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.real, LMonoTy.regex] at h)
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.regex] at h)
      | bvar =>
        cases hwt with
        | bvar hget =>
          left; left
          have hlen : (bvarsOfType bctx .regex).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .regex _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx .regex _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .regex).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .regex _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx .regex _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .regex).length > 0 := by
            have := (opsOfType_mem_iff octx .regex _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx .regex _ hmem hlen⟩
    case map =>
      intro τ₁ τ₂ hs₁ hs₂ hwt
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff,
        mem_support_iff, SetGen.mem_dite, bot_mem_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.map])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.map])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string, LMonoTy.map])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.real, LMonoTy.map])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.map])
      | bvar =>
        cases hwt with
        | bvar hget =>
          left; left
          have hlen : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.map τ₁ τ₂) _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx (.map τ₁ τ₂) _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.map τ₁ τ₂) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx (.map τ₁ τ₂) _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.map τ₁ τ₂)).length > 0 := by
            have := (opsOfType_mem_iff octx (.map τ₁ τ₂) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx (.map τ₁ τ₂) _ hmem hlen⟩
    case seq =>
      intro τ₁ hs hwt
      simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite, bot_mem_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.bool, LMonoTy.seq] at h)
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.int, LMonoTy.seq] at h)
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.string, LMonoTy.seq] at h)
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.real, LMonoTy.seq] at h)
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.seq] at h)
      | bvar =>
        cases hwt with
        | bvar hget =>
          left; left
          have hlen : (bvarsOfType bctx (.seq τ₁)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.seq τ₁) _).mpr hget
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickBVar_complete bctx (.seq τ₁) _ hget hlen⟩
      | fvar =>
        cases hwt with
        | fvar =>
          right; left; left
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.seq τ₁)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.seq τ₁) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickFVar_complete fctx (.seq τ₁) _ hmem hlen⟩
      | op =>
        cases hwt with
        | op =>
          right; right; left
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.seq τ₁)).length > 0 := by
            have := (opsOfType_mem_iff octx (.seq τ₁) _).mpr hmem
            exact List.length_pos_of_mem this
          exact ⟨hlen, pickOp_complete octx (.seq τ₁) _ hmem hlen⟩
  | n + 1 =>
    revert hwt
    refine genLMonoTy_mem_cases ?bool ?int ?string ?real ?regex ?bitvec ?ftvar ?arrow ?map ?seq hτ
    case bool =>
      intro hwt
      rw [norm_bool]; simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | boolConst =>
        cases hwt with
        | const =>
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [genBoolConst, pick_mem_iff, SetGen.Set.mem_pure]
          cases (by assumption : Bool) <;> simp [LExpr.boolConst]
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.int])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.string])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.real])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool])
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow, LMonoTy.bool])
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | eq τ' he1w he2w hmem' hats1 hats2 =>
        cases hwt with
        | eq hwt1 hwt2 =>
          have hτeq := HasTypeA_unique he1w hwt1
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          simp only [genEq, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genGenerableTy_support _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hwt1 hnames.1 hvars.1 hats1 (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hwt2 hnames.2 hvars.2 hats2 (by omega), rfl⟩
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' .bool) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ genLMonoTy_mem_bool) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | quant hmem' τ_tr hmem_tr htrw htr_ats hbody_ats =>
        cases hwt with
        | quant htrw' hbodyw =>
          have hτ_tr_eq := HasTypeA_unique htrw htrw'
          subst hτ_tr_eq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          rename_i k
          cases k with
          | all =>
            refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
            simp only [genQuant, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
            refine ⟨_, (genGenerableTy_support _ _ _ _ _ _).mpr <| hmem',
                   _, (genGenerableTy_support _ _ _ _ _ _).mpr <| hmem_tr,
                   _, genLExprBase_complete fctx octx pctx tvars (_ :: bctx) n τ_tr ⟨_, hmem_tr⟩ _ htrw' hnames.2.1 hvars.1 htr_ats (by omega),
                   _, genLExprBase_complete fctx octx pctx tvars (_ :: bctx) n .bool genLMonoTy_mem_bool _ hbodyw hnames.2.2 hvars.2 hbody_ats (by omega), rfl⟩
          | exist =>
            refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
            simp only [genQuant, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
            refine ⟨_, (genGenerableTy_support _ _ _ _ _ _).mpr <| hmem',
                   _, (genGenerableTy_support _ _ _ _ _ _).mpr <| hmem_tr,
                   _, genLExprBase_complete fctx octx pctx tvars (_ :: bctx) n τ_tr ⟨_, hmem_tr⟩ _ htrw' hnames.2.1 hvars.1 htr_ats (by omega),
                   _, genLExprBase_complete fctx octx pctx tvars (_ :: bctx) n .bool genLMonoTy_mem_bool _ hbodyw hnames.2.2 hvars.2 hbody_ats (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), by omega, ?_⟩
          have hlen : (bvarsOfType bctx .bool).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .bool _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx .bool _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .bool).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .bool _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx .bool _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .bool).length > 0 := by
            have := (opsOfType_mem_iff octx .bool _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx .bool _ hmem hlen
    case int =>
      intro hwt
      rw [norm_int]
      simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | intConst =>
        cases hwt with
        | const =>
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [mem_support_iff, genIntConst, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          have hic := Int_cover (by assumption : Int)
          rcases hic with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
          · left; exact ⟨k, hk, rfl⟩
          · right; exact ⟨k, hk, rfl⟩
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.int])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.string])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.real])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int])
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow, LMonoTy.int])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.int])
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.int])
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' .int) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ genLMonoTy_mem_int) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .int genLMonoTy_mem_int _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .int genLMonoTy_mem_int _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hlen : (bvarsOfType bctx .int).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .int _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx .int _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .int).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .int _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx .int _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .int).length > 0 := by
            have := (opsOfType_mem_iff octx .int _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx .int _ hmem hlen
    case string =>
      intro hwt
      rw [norm_string]
      simp only [genLExprBase]; rw [mem_support_frequency_iff]
      cases hats with
      | strConst halpha =>
        cases hwt with
        | const =>
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [genStrConst, SetGen.Set.mem_bind, SetGen.Set.mem_pure, mem_support_iff]
          exact ⟨_, genInterestingString_support_set _ halpha, by simp [LExpr.strConst]⟩
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.string])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.string])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string, LMonoTy.real])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string])
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow, LMonoTy.string])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.string])
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.string])
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' .string) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ genLMonoTy_mem_string) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .string genLMonoTy_mem_string _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .string genLMonoTy_mem_string _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hlen : (bvarsOfType bctx .string).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .string _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx .string _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .string).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .string _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx .string _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .string).length > 0 := by
            have := (opsOfType_mem_iff octx .string _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx .string _ hmem hlen
    case real =>
      intro hwt
      rw [norm_real]
      simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | realConst r =>
        cases hwt with
        | const =>
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [mem_support_iff, genRealConst, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          exact ⟨r, genRat_support_set r, rfl⟩
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.real])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.real])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string, LMonoTy.real])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.real])
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow, LMonoTy.real])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.real])
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.real])
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' .real) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ genLMonoTy_mem_real) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .real genLMonoTy_mem_real _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .real genLMonoTy_mem_real _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hlen : (bvarsOfType bctx .real).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .real _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx .real _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .real).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .real _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx .real _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .real).length > 0 := by
            have := (opsOfType_mem_iff octx .real _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx .real _ hmem hlen
    case bitvec =>
      intro w hwt
      simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | bitvecConst _ _ =>
        cases hwt with
        | const =>
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [genBitvecConst, SetGen.Set.mem_bind, SetGen.Set.mem_pure, mem_support_iff]
          exact ⟨_, genBiasedBitVec_support_set _, rfl⟩
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.string] at h)
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.real] at h)
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt) (by intro h; simp [LMonoTy.bool] at h)
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt) (by intro h; simp [LMonoTy.bool] at h)
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' (.bitvec w))
                   (genLMonoTy_mem_arrow ⟨_, hmem'⟩ genLMonoTy_mem_bitvec) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.bitvec w) genLMonoTy_mem_bitvec _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.bitvec w) genLMonoTy_mem_bitvec _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hlen : (bvarsOfType bctx (.bitvec w)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.bitvec w) _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx (.bitvec w) _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem' : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.bitvec w)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.bitvec w) _).mpr hmem'
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx (.bitvec w) _ hmem' hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
          have hmem' : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.bitvec w)).length > 0 := by
            have := (opsOfType_mem_iff octx (.bitvec w) _).mpr hmem'
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx (.bitvec w) _ hmem' hlen
    case arrow =>
      intro τ₁ τ₂ hs₁ hs₂ hwt
      rw [norm_arrow]
      simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.arrow])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.arrow])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string, LMonoTy.arrow])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.real, LMonoTy.arrow])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.arrow])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.arrow])
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.arrow])
      | abs _ hbody_ats =>
        cases hwt with
        | abs hbody_wt =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [genAbs, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars (τ₁ :: bctx) n τ₂ hs₂ _ hbody_wt
            hnames.2 hvars hbody_ats (by omega), rfl⟩
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' (.arrow τ₁ τ₂)) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ (genLMonoTy_mem_arrow hs₁ hs₂)) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ₁ τ₂) (genLMonoTy_mem_arrow hs₁ hs₂) _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ₁ τ₂) (genLMonoTy_mem_arrow hs₁ hs₂) _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hlen : (bvarsOfType bctx (.arrow τ₁ τ₂)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.arrow τ₁ τ₂) _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx (.arrow τ₁ τ₂) _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.arrow τ₁ τ₂) _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx (.arrow τ₁ τ₂) _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.arrow τ₁ τ₂)).length > 0 := by
            have := (opsOfType_mem_iff octx (.arrow τ₁ τ₂) _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx (.arrow τ₁ τ₂) _ hmem hlen
    case ftvar =>
      intro name hname hwt
      simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.bool] at h)
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.int] at h)
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.string] at h)
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.real] at h)
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty] at h)
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt) (by intro h; simp [LMonoTy.bool] at h)
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt) (by intro h; simp [LMonoTy.bool] at h)
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' (.ftvar name)) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ (genLMonoTy_mem_ftvar hname)) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.ftvar name) (genLMonoTy_mem_ftvar hname) _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.ftvar name) (genLMonoTy_mem_ftvar hname) _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          have hlen : (bvarsOfType bctx (.ftvar name)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.ftvar name) _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx (.ftvar name) _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.ftvar name)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.ftvar name) _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx (.ftvar name) _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.ftvar name)).length > 0 := by
            have := (opsOfType_mem_iff octx (.ftvar name) _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx (.ftvar name) _ hmem hlen
    case regex =>
      intro hwt
      simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.bool, LMonoTy.regex] at h)
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.int, LMonoTy.regex] at h)
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.string, LMonoTy.regex] at h)
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.real, LMonoTy.regex] at h)
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.regex] at h)
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow, LMonoTy.regex])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt) (by intro h; simp [LMonoTy.bool, LMonoTy.regex] at h)
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt) (by intro h; simp [LMonoTy.bool, LMonoTy.regex] at h)
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' .regex) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ genLMonoTy_mem_regex) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .regex genLMonoTy_mem_regex _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n .regex genLMonoTy_mem_regex _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          have hlen : (bvarsOfType bctx .regex).length > 0 := by
            have := (bvarsOfType_mem_iff bctx .regex _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx .regex _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx .regex).length > 0 := by
            have := (fvarsOfType_mem_iff fctx .regex _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx .regex _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx .regex).length > 0 := by
            have := (opsOfType_mem_iff octx .regex _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx .regex _ hmem hlen
    case map =>
      intro τ₁ τ₂ hs₁ hs₂ hwt
      simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.bool, LMonoTy.map])
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.int, LMonoTy.map])
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.string, LMonoTy.map])
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.real, LMonoTy.map])
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const)
          (by simp [LConst.ty, LMonoTy.map])
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow, LMonoTy.map])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.map])
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt)
          (by simp [LMonoTy.bool, LMonoTy.map])
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' (.map τ₁ τ₂)) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ (genLMonoTy_mem_map hs₁ hs₂)) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.map τ₁ τ₂) (genLMonoTy_mem_map hs₁ hs₂) _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.map τ₁ τ₂) (genLMonoTy_mem_map hs₁ hs₂) _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          have hlen : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.map τ₁ τ₂) _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx (.map τ₁ τ₂) _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.map τ₁ τ₂) _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx (.map τ₁ τ₂) _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.map τ₁ τ₂)).length > 0 := by
            have := (opsOfType_mem_iff octx (.map τ₁ τ₂) _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx (.map τ₁ τ₂) _ hmem hlen
    case seq =>
      intro τ₁ hs hwt
      simp only [genLExprBase]
      rw [mem_support_frequency_iff]
      cases hats with
      | boolConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.bool, LMonoTy.seq] at h)
      | intConst =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.int, LMonoTy.seq] at h)
      | strConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.string, LMonoTy.seq] at h)
      | realConst _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.real, LMonoTy.seq] at h)
      | bitvecConst _ _ =>
        exact absurd (HasTypeA_unique hwt .const) (by intro h; simp [LConst.ty, LMonoTy.seq] at h)
      | abs _ _ =>
        exact absurd (LExpr.HasTypeA_to_typeCheck hwt)
          (by simp [LExpr.typeCheck, bind, Option.bind]
              split <;> simp_all [LMonoTy.arrow, LMonoTy.seq])
      | eq _ _ _ _ _ _ =>
        exact absurd (eq_hasType_bool hwt) (by intro h; simp [LMonoTy.bool, LMonoTy.seq] at h)
      | quant _ _ _ _ _ _ =>
        exact absurd (quant_hasType_bool hwt) (by intro h; simp [LMonoTy.bool, LMonoTy.seq] at h)
      | app τ' hargw hmem' hfn_ats harg_ats =>
        cases hwt with
        | app hfnw hargw' =>
          have hτeq := HasTypeA_unique hargw hargw'
          subst hτeq
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .head _, by omega, ?_⟩
          simp only [genApp, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨τ', (genAppArgTy_support _ _ _ _ _ _ _).mpr <| hmem',
                 _, genLExprBase_complete fctx octx pctx tvars bctx n τ' ⟨_, hmem'⟩ _ hargw' hnames.2 hvars.2 harg_ats (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.arrow τ' (.seq τ₁)) (genLMonoTy_mem_arrow ⟨_, hmem'⟩ (genLMonoTy_mem_seq hs)) _ hfnw hnames.1 hvars.1 hfn_ats (by omega), rfl⟩
      | ite hc ht he_ =>
        cases hwt with
        | ite hcw htw hew =>
          simp [termDepth] at hdepth
          simp only [emptyNames] at hnames
          simp only [allVarsInCtx] at hvars
          refine ⟨_, _, .tail _ (.head _), by omega, ?_⟩
          simp only [genIte, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
          refine ⟨_, genLExprBase_complete fctx octx pctx tvars bctx n .bool genLMonoTy_mem_bool _ hcw hnames.1 hvars.1 hc (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.seq τ₁) (genLMonoTy_mem_seq hs) _ htw hnames.2.1 hvars.2.1 ht (by omega),
                 _, genLExprBase_complete fctx octx pctx tvars bctx n (.seq τ₁) (genLMonoTy_mem_seq hs) _ hew hnames.2.2 hvars.2.2 he_ (by omega), rfl⟩
      | bvar =>
        cases hwt with
        | bvar hget =>
          refine ⟨_, _, .tail _ (.tail _ (.head _)), by omega, ?_⟩
          have hlen : (bvarsOfType bctx (.seq τ₁)).length > 0 := by
            have := (bvarsOfType_mem_iff bctx (.seq τ₁) _).mpr hget
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickBVar_complete bctx (.seq τ₁) _ hget hlen
      | fvar =>
        cases hwt with
        | fvar =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, ?_⟩
          have hmem : (_, _) ∈ fctx := hvars
          have hlen : (fvarsOfType fctx (.seq τ₁)).length > 0 := by
            have := (fvarsOfType_mem_iff fctx (.seq τ₁) _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickFVar_complete fctx (.seq τ₁) _ hmem hlen
      | op =>
        cases hwt with
        | op =>
          refine ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
          have hmem : (_, _) ∈ octx.ops := hvars
          have hlen : (opsOfType octx (.seq τ₁)).length > 0 := by
            have := (opsOfType_mem_iff octx (.seq τ₁) _).mpr hmem
            exact List.length_pos_of_mem this
          exact dif_pos hlen ▸ pickOp_complete octx (.seq τ₁) _ hmem hlen
  termination_by (depth, sizeOf τ)
  decreasing_by all_goals simp_wf; omega

-- ── IsSoundAndComplete for genLMonoTy ─────────────────────────────────

/-- `genLMonoTy tvars n` is sound and complete against the decidable filter
    `inGenLMonoTySupport tvars n`. -/
instance {tvars : List TyIdentifier} {n : Nat} :
    SetGen.IsSoundAndComplete
      (genLMonoTy (G := SetGen.Set) tvars n)
      (fun τ => inGenLMonoTySupport tvars n τ = true) where
  support_iff τ := genLMonoTy_support tvars n τ

-- ── Quick test ────────────────────────────────────────────────────────

-- This `ToFormat` instance lets the code print a generated `LExpr`. The metadata type is `Unit`.
open Std in
instance : ToFormat Unit where
  format _ := .nil

-- Print five random expressions. Two examples of the output are:
-- (if (if #true then #true else #true) then #true else #true)
-- ((λ (bvar:bool) #true) ((λ (bvar:bool) %0) #true))
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  IO.println <| Std.format (← genClosedLExpr [] 3) |>.pretty : IO Unit)

-- A draw with a bound variable of the type `ftvar "a"`, which reaches the `ftvar` case.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  IO.println <| Std.format (← genLExpr [] [] [] ["a"] [.ftvar "a"] 3 (.ftvar "a")) |>.pretty : IO Unit)

-- A draw with polymorphic operators, which reaches the IndirPoly rule.
-- id : ∀ a. a → a
-- const : ∀ a b. a → b → a
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let pctx : PolyOpCtx := [
    ("id", .forAll ["a"] (.arrow (.ftvar "a") (.ftvar "a"))),
    ("const", .forAll ["a", "b"] (.arrow (.ftvar "a") (.arrow (.ftvar "b") (.ftvar "a"))))
  ]
  IO.println <| Std.format (← genLExpr [] [] pctx [] [] 3 .bool) |>.pretty : IO Unit)

-- ── Indir rule soundness ─────────────────────────────────────────────

/-- If `argsForResult fullTy τ` is `some args`, then `fullTy` is the arrow type that `args` and `τ`
    build, which is `args.foldr (fun σ acc => .arrow σ acc) τ`. -/
theorem argsForResult_eq (fullTy τ : LMonoTy) (args : List LMonoTy)
    (h : argsForResult fullTy τ = some args) :
    fullTy = args.foldr (fun σ acc => LMonoTy.arrow σ acc) τ := by
  unfold argsForResult at h
  split at h
  · rename_i σ rest
    split at h
    · rename_i args' hrest
      simp at h; subst h
      simp only [List.foldr]
      show LMonoTy.arrow σ rest = LMonoTy.arrow σ (List.foldr _ τ args')
      congr 1
      exact argsForResult_eq rest τ args' hrest
    · simp at h
  · split at h
    · rename_i heq
      have heq' := beq_iff_eq.mp heq
      simp at h; subst h; simp [heq']
    · simp at h
  termination_by sizeOf fullTy

/-- `mkApps` keeps the typing, by one use of the `app` rule for each argument. -/
theorem mkApps_hasType (bctx : BVarCtx) (base : LExpr') (args : List LExpr')
    (argTys : List LMonoTy) (τ : LMonoTy)
    (hbase : HasTypeA' bctx base (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))
    (hargs : List.Forall₂ (HasTypeA' bctx) args argTys) :
    HasTypeA' bctx (mkApps base args) τ := by
  induction hargs generalizing base with
  | nil => exact hbase
  | cons harg _ ih => exact ih _ (LExpr.HasTypeA.app hbase harg)

-- **The matching completeness of `Constraints.unify` comes from Strata.** The theorem is
-- `Lambda.Constraints_unify_matching_complete`, in `Strata.DL.Lambda.LTyUnifyProps`.
-- `unifyTypes_matching_complete` below uses it directly.

/-- The `unifyTypes` wrapper of the generator is also matching-complete. The proof takes the
    `.ok` and `.error` adapter apart, and it then applies `Constraints_unify_matching_complete`. -/
theorem unifyTypes_matching_complete
    (pat τ : LMonoTy) (S : Lambda.Subst)
    (hdisj  : ∀ v ∈ pat.freeVars, v ∉ τ.freeVars)
    (hmatch : LMonoTy.subst S pat = τ) :
    ∃ Su : Lambda.Subst,
      unifyTypes pat τ = some Su ∧
      LMonoTy.subst Su pat = τ := by
  obtain ⟨si, hunify, hpat⟩ :=
    Constraints_unify_matching_complete pat τ S hdisj hmatch
  exact ⟨si.subst, by simp only [unifyTypes, hunify], hpat⟩

/-- A scope from `z` whose keys are not free in `t` changes nothing. The statement is
    `subst (substScope z ++ Su) t = subst Su t`. The proof uses
    `agree_on_freeVars_implies_subst_eq`. At each free variable of `t`, the new scope gives `none` for
    its `find?`, so both substitutions read the same binding of `Su`.

    The new scope comes as an association list, and `substScope` pushes it, because a scope of a `Subst`
    is a hash map and a list literal cannot write it. `Freshening.find?_substScope_eq_lookup` turns the
    hypothesis about `List.lookup` into the fact about `find?` that the proof needs. -/
theorem subst_substScope_noop (z : List (TyIdentifier × LMonoTy)) (Su : Lambda.Subst)
    (t : LMonoTy) (hz : ∀ v ∈ t.freeVars, z.lookup v = none) :
    LMonoTy.subst (substScope z ++ Su) t = LMonoTy.subst Su t := by
  apply agree_on_freeVars_implies_subst_eq
  intro v hv
  have hnone : Strata.Util.HMap.find? (Strata.Util.HMap.ofList z.reverse) v = none := by
    rw [← Strata.Util.HMaps.find?_single_scope]
    exact (Freshening.find?_substScope_eq_lookup z v).trans (hz v hv)
  simp only [LMonoTy.subst_unfold, substScope, List.cons_append, List.nil_append,
    Strata.Util.HMaps.find?, hnone]

/-- If `v` is free in `t`, and `Su` binds no value to `v`, then `v` is also free in `subst Su t`. The
    proof is by structural induction on `t`.

    The role of this lemma is to show that a sampled type variable in the remaining suffix, which is a
    variable that `Su` leaves open, would also occur in the target type. The disjointness from the
    rename makes that impossible. -/
theorem mem_freeVars_subst_of_find?_none (Su : Lambda.Subst) (t : LMonoTy)
    (v : TyIdentifier) (hv : v ∈ t.freeVars) (hnone : Strata.Util.HMaps.find? Su v = none) :
    v ∈ (LMonoTy.subst Su t).freeVars := by
  induction t with
  | ftvar w =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv
    rw [LMonoTy.subst_unfold]
    simp only [hnone, LMonoTy.freeVars, List.mem_singleton]
  | bitvec n => simp only [LMonoTy.freeVars, List.not_mem_nil] at hv
  | tcons name args ih =>
    rw [LMonoTy.subst_unfold]
    have hsub : ∀ (a : LMonoTy), a ∈ args → v ∈ a.freeVars →
        v ∈ LMonoTys.freeVars (args.map (LMonoTy.subst Su)) :=
      fun a ha hva => Freshening.freeVars_mem_of_mem (List.mem_map_of_mem ha) (ih a ha hva)
    have hex : ∃ a ∈ args, v ∈ a.freeVars := by
      clear hsub ih hnone
      induction args with
      | nil =>
        exact absurd hv (by
          rw [show (LMonoTy.tcons name []).freeVars = ([] : List TyIdentifier) from rfl]
          exact List.not_mem_nil)
      | cons hd tl iht =>
        rw [show (LMonoTy.tcons name (hd :: tl)).freeVars
            = hd.freeVars ++ LMonoTys.freeVars tl from rfl] at hv
        rcases List.mem_append.mp hv with h | h
        · exact ⟨hd, List.mem_cons_self, h⟩
        · obtain ⟨a, ha, hva⟩ := iht (by
            rw [show (LMonoTy.tcons name tl).freeVars = LMonoTys.freeVars tl from rfl]; exact h)
          exact ⟨a, List.mem_cons_of_mem _ ha, hva⟩
    obtain ⟨a, ha, hva⟩ := hex
    exact hsub a ha hva

/-- **Two matchers of the same pattern agree at each variable of that pattern.**

    This is the converse of `agree_on_freeVars_implies_subst_eq`. A substitution is a homomorphism.
    Therefore two substitutions that send `t` to the *same* type must send each variable of `t` to the
    same type. The proof is by structural induction on `t`, and the `tcons` case uses
    `List.map_inj_left` on the argument lists.

    This lemma gives the **uniqueness of a matcher**, which `SchemeInstAt` needs. It says nothing about
    most generality, and it needs no theory of a unifier. Two matchers of the same matching problem
    must agree at each variable of the pattern. That fact is what reconciles the unifier output `Su` of
    the generator with the matcher `Sm` of a caller, at each *determined* variable, and it needs no
    result about a most general unifier. -/
theorem subst_agree_of_subst_eq {S₁ S₂ : Lambda.Subst} (t : LMonoTy)
    (h : LMonoTy.subst S₁ t = LMonoTy.subst S₂ t) :
    ∀ v ∈ t.freeVars, LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v) := by
  induction t with
  | ftvar w =>
    intro v hv
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv
    exact h
  | bitvec n => intro v hv; simp only [LMonoTy.freeVars, List.not_mem_nil] at hv
  | tcons name args ih =>
    intro v hv
    rw [LMonoTy.subst_unfold, LMonoTy.subst_unfold] at h
    simp only [LMonoTy.tcons.injEq, true_and] at h
    obtain ⟨a, ha, hva⟩ :=
      Freshening.exists_of_freeVars_mem (show v ∈ LMonoTys.freeVars args from hv)
    exact ih a ha (List.map_inj_left.mp h a ha) v hva

/-- **A sample does no harm to `guard2`.**

    The generator extends the substitution `Su` of the unifier with a scope. That scope binds each
    *open* renamed variable, which is a variable of `findFreeTyVars freshBoundVars Su`, to a random
    sample. `Su` is a matcher for the suffix, and it is not known to be most general.

    The extension does not change the remaining suffix. Such a variable in the suffix would also occur
    in `subst Su leftoverSuffix`, which is `τ`, because `Su` leaves the variable open. The hypothesis
    `hdisjBV` says that each renamed bound variable is not free in `τ`, so that is impossible.
    Therefore the extended substitution still sends the suffix to `τ` itself. This fact is what lets the
    sampling case discharge `guard2` from the conclusion of the matching theorem. -/
theorem extended_subst_guard2 (freshBoundVars : List TyIdentifier) (Su : Lambda.Subst)
    (sampledTys : List LMonoTy) (leftoverSuffix τ : LMonoTy)
    (hSu : LMonoTy.subst Su leftoverSuffix = τ)
    (hdisjBV : ∀ v ∈ freshBoundVars, v ∉ τ.freeVars) :
    LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars Su).zip sampledTys) ++ Su)
      leftoverSuffix = τ := by
  rw [subst_substScope_noop]
  · exact hSu
  · intro v hv
    -- `lookup v = none`. A lookup that gives a value would make `v` a key of the `zip`, and `v` would
    -- then be a renamed bound variable that `Su` leaves open.
    rcases hlk : ((findFreeTyVars freshBoundVars Su).zip sampledTys).lookup v with _ | t
    · rfl
    exfalso
    have hvin : v ∈ findFreeTyVars freshBoundVars Su :=
      (List.of_mem_zip (Freshening.lookup_mem _ _ _ hlk)).1
    unfold findFreeTyVars at hvin
    rw [List.mem_filter] at hvin
    obtain ⟨hbv, hfind⟩ := hvin
    have hnone : Strata.Util.HMaps.find? Su v = none := by simpa using hfind
    have hmemτ : v ∈ (LMonoTy.subst Su leftoverSuffix).freeVars :=
      mem_freeVars_subst_of_find?_none Su leftoverSuffix v hv hnone
    rw [hSu] at hmemτ
    exact hdisjBV v hbv hmemτ

/-- **The bridge from `Sm` to `Su` on the applied prefix.**

    The generator instantiates the applied prefix with its own unifier output, extended by the samples.
    A caller who reasons from the typing judgement instantiates the prefix with a matcher `Sm`. This
    lemma says that the two agree, if the split point is **determined**. The hypothesis `hdet` gives
    that condition: each type variable of the applied prefix also occurs in the remaining suffix.

    Under `hdet`, each prefix variable `v` has two properties:
    - `Su` determines `v`. If it did not, then `v` would also occur in `subst Su suffix`, which is `τ`,
      and the disjointness from the rename makes that impossible. Therefore the scope of the samples
      never applies to the prefix.
    - `Sm v` equals `Su v`, because `Sm` and `Su` are matchers of the *same* matching problem, and they
      therefore agree at each variable of the suffix.

    The proof needs no most general unifier and no limit on the domain of `Su`. The determinacy
    condition is the exact boundary of the statement. At a split point where a variable of the scheme is
    absent from the remaining suffix, the generator picks the instance of that variable by a *random
    sample*, and no theorem can force the sample to agree with the choice of `Sm`. To reach that case
    from a premise at the level of the specification, a proof needs either a limit on the domain of
    `Su`, in the form `keys Su ⊆ FV(suffix) ∪ FV(τ)`, or an existentially bound list of sampled types.
    Strata proves the domain limit inside its own unification proof, and its public theorem does not
    give it. Read the note on `SchemeInstAt`. -/
theorem extended_subst_prefix_of_determined (schemeArgTys : List LMonoTy)
    (retTy τ : LMonoTy) (k : Nat) (Sm Su : Lambda.Subst)
    (freshBoundVars : List TyIdentifier) (sampledTys : List LMonoTy)
    (hdisjSuffix : ∀ v ∈ ((schemeArgTys.drop k).foldr
      (fun σ acc => LMonoTy.arrow σ acc) retTy).freeVars, v ∉ τ.freeVars)
    (hmatch : LMonoTy.subst Sm
      ((schemeArgTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ)
    (hSu : LMonoTy.subst Su
      ((schemeArgTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ)
    (hdet : ∀ σ ∈ schemeArgTys.take k, ∀ v ∈ σ.freeVars,
      v ∈ ((schemeArgTys.drop k).foldr
        (fun σ acc => LMonoTy.arrow σ acc) retTy).freeVars) :
    (schemeArgTys.take k).map (LMonoTy.subst Sm)
      = (schemeArgTys.take k).map (LMonoTy.subst
          (substScope ((findFreeTyVars freshBoundVars Su).zip sampledTys) ++ Su)) := by
  -- The two matchers agree at each free variable of the remaining suffix.
  have hagree : ∀ v ∈ ((schemeArgTys.drop k).foldr
      (fun σ acc => LMonoTy.arrow σ acc) retTy).freeVars,
      LMonoTy.subst Sm (.ftvar v) = LMonoTy.subst Su (.ftvar v) :=
    subst_agree_of_subst_eq _ (hmatch.trans hSu.symm)
  -- `Su` determines each variable of the suffix. An open one would also occur in
  -- `subst Su suffix`, which is `τ`, and the disjointness from the rename makes that impossible.
  have hdetermined : ∀ v ∈ ((schemeArgTys.drop k).foldr
      (fun σ acc => LMonoTy.arrow σ acc) retTy).freeVars,
      Strata.Util.HMaps.find? Su v ≠ none := by
    intro v hv hnone
    exact hdisjSuffix v hv (hSu ▸ mem_freeVars_subst_of_find?_none Su _ v hv hnone)
  apply List.map_congr_left
  intro σ hσ
  -- The scope of the samples never applies to a prefix type. Its keys are the variables that `Su`
  -- leaves open, and `Su` determines each prefix variable.
  have hnoop : LMonoTy.subst
      (substScope ((findFreeTyVars freshBoundVars Su).zip sampledTys) ++ Su) σ
      = LMonoTy.subst Su σ := by
    apply subst_substScope_noop
    intro v hv
    rcases hlk : ((findFreeTyVars freshBoundVars Su).zip sampledTys).lookup v with _ | t
    · rfl
    exfalso
    have hvin : v ∈ findFreeTyVars freshBoundVars Su :=
      (List.of_mem_zip (Freshening.lookup_mem _ _ _ hlk)).1
    unfold findFreeTyVars at hvin
    rw [List.mem_filter] at hvin
    exact hdetermined v (hdet σ hσ v hv) (by simpa using hvin.2)
  rw [hnoop]
  exact agree_on_freeVars_implies_subst_eq (fun v hv => hagree v (hdet σ hσ v hv))

/-- **The forward construction of a candidate of `findPolymorphicOps`.**

    This lemma is the existence direction of `findPolymorphicOps_instanceR`. From a scheme in `pctx`, a
    split point `k`, the results of the rename and of the decomposition, and the two guards of the
    `do` block as hypotheses, the pair `(name, concreteArgTys)` is a member of `findPolymorphicOps`. The
    proof only follows the `flatMap`, the `filterMap` and the two guards. The caller discharges the two
    guard hypotheses with `unifyTypes_matching_complete`. -/
theorem findPolymorphicOps_complete
    (pctx : PolyOpCtx) (τ : LMonoTy) (generableTys sampledTys : List LMonoTy)
    (name : String) (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (hmem : (name, LTy.forAll boundVars monoTy) ∈ pctx)
    (freshBoundVars : List TyIdentifier) (freshMonoTy : LMonoTy)
    (argTys : List LMonoTy) (retTy : LMonoTy) (subst : Lambda.Subst)
    (concreteArgTys : List LMonoTy) (k : Nat) (maxNumArgs : Nat)
    (hfresh : freshenBoundVars boundVars monoTy
      ((LMonoTy.freeVars τ ++ generableTys.flatMap LMonoTy.freeVars).eraseDups)
      = (freshBoundVars, freshMonoTy))
    (hdec : decomposeArrow freshMonoTy = (argTys, retTy))
    (harity : argTys.length ≤ maxNumArgs)
    (hk : k < argTys.length + 1)
    (hunify : unifyTypes
      ((argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) τ = some subst)
    (hguard1 : (findFreeTyVars freshBoundVars subst).isEmpty = true
      ∨ (generableTys ≠ []))
    (hguard2 : LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars subst).zip sampledTys) ++ subst)
      ((argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ)
    (hcat : concreteArgTys = (argTys.take k).map
      (LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars subst).zip sampledTys) ++ subst))) :
    (name, concreteArgTys) ∈ findPolymorphicOps pctx τ generableTys sampledTys maxNumArgs := by
  unfold findPolymorphicOps
  rw [List.mem_flatMap]
  refine ⟨(name, LTy.forAll boundVars monoTy), hmem, ?_⟩
  simp only [hfresh, hdec]
  rw [if_neg (by omega), List.mem_filterMap]
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  -- Discharge the `do` block over `Option`. First resolve the bind of the unification, and then both
  -- guards.
  rw [hunify]
  simp only [bind, Option.bind, guard, pure]
  rw [if_pos (by
    rcases hguard1 with h | h
    · simp [h]
    · simp [List.isEmpty_iff, h])]
  rw [if_pos (by rw [beq_iff_eq]; exact hguard2)]
  rw [hcat]

/-- The inversion of `mkApps_hasType`. A well-typed application spine `mkApps base args : τ` gives a
    list of argument types `argTys`. Then `base` has the curried arrow type `argTys.foldr arrow τ`, and
    each argument is well-typed at its own type in `argTys`.

    `isPolyApp_of_hasType` uses this lemma to recover, from a typing derivation, the concrete argument
    types that `findPolymorphicOps` gave. The `.app` rule of the typing judgement removes one arrow for
    each applied argument, and the induction builds `argTys` from the outermost argument. -/
theorem mkApps_hasType_inv (bctx : BVarCtx) (base : LExpr') (args : List LExpr')
    (τ : LMonoTy)
    (hwt : HasTypeA' bctx (mkApps base args) τ) :
    ∃ argTys : List LMonoTy,
      HasTypeA' bctx base (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) ∧
      List.Forall₂ (HasTypeA' bctx) args argTys := by
  induction args generalizing base with
  | nil =>
    -- `mkApps base [] = base`, so `base` has the type `τ`, and there is no arrow to remove.
    exact ⟨[], hwt, .nil⟩
  | cons a as ih =>
    -- `mkApps base (a :: as) = mkApps (.app () base a) as`.
    obtain ⟨argTys', hbase', hargs'⟩ := ih (.app () base a) hwt
    -- Invert the application at the head. Then `base` has the type `aty → (argTys'.foldr arrow τ)`,
    -- and `a` has the type `aty`. The type `aty` stays implicit, and unification finds it from `hfn`
    -- against the goal.
    cases hbase' with
    | app hfn harg => exact ⟨_ :: argTys', hfn, .cons harg hargs'⟩

/-- `argTys.foldr arrow τ` is injective in `argTys` **when the two lists have the same length**. It is
    not injective without that condition, because `[a].foldr arrow (b → c)` and `[a, b].foldr arrow c`
    are the same type.

    `isPolyApp_of_hasType` uses this lemma to identify the argument types from the typing derivation
    with the concrete argument types that `findPolymorphicOps` gives. Both lists fold to the same
    annotation, and both have the length of the argument list. -/
theorem foldr_arrow_inj_of_length_eq (as bs : List LMonoTy) (τ : LMonoTy)
    (hlen : as.length = bs.length)
    (heq : as.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
         = bs.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) :
    as = bs := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons b bs => simp at hlen
  | cons a as ih => cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.foldr_cons] at heq
      -- The goal is `arrow a (…) = arrow b (…)`, and `arrow` is `tcons "arrow" [·, ·]`. Unfold it, and
      -- then the injectivity of `tcons` splits the goal into the head and the tail.
      simp only [LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq, and_true,
        true_and] at heq
      obtain ⟨hhd, htl⟩ := heq
      subst hhd
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [ih bs hlen htl]

/-- Membership in `List.mapM f l` at `SetGen.Set`. The list `args` is in the support if and only if each
    of its elements is in the support of `f` at the input at the same position. -/
private theorem mem_mapM_iff (f : LMonoTy → SetGen.Set LExpr')
    (argTys : List LMonoTy) (args : List LExpr') :
    args ∈ (List.mapM (m := SetGen.Set) f argTys) ↔
    List.Forall₂ (fun arg σ => arg ∈ f σ) args argTys := by
  induction argTys generalizing args with
  | nil =>
    simp only [List.mapM_nil, SetGen.Set.mem_pure]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | cons σ rest ih =>
    simp only [List.mapM_cons, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
    constructor
    · rintro ⟨x, hx, tl, htl, rfl⟩
      exact .cons hx ((ih _).mp htl)
    · intro h
      match args, h with
      | _ :: _, .cons harg htail =>
        exact ⟨_, harg, _, (ih _).mpr htail, rfl⟩

/-- If `findOpsInCtx octx τ` holds `(name, argTys)`, then `octx.ops` holds
    `(name, argTys.foldr arrow τ)`, and `argTys` has one element or more. -/
private theorem findOpsInCtx_mem {octx : OpCtx} {τ : LMonoTy}
    {name : String} {argTys : List LMonoTy}
    (h : (name, argTys) ∈ findOpsInCtx octx τ) :
    (name, argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) ∈ octx.ops ∧ argTys ≠ [] := by
  simp only [findOpsInCtx, List.mem_filterMap] at h
  obtain ⟨⟨n, ty⟩, hmem, hfilt⟩ := h
  simp only at hfilt
  split at hfilt
  · rename_i arg args hargs
    simp only [Option.some.injEq, Prod.mk.injEq] at hfilt
    obtain ⟨rfl, rfl⟩ := hfilt
    refine ⟨?_, List.cons_ne_nil _ _⟩
    have heq := argsForResult_eq ty τ (arg :: args) hargs
    rw [heq] at hmem
    exact hmem
  · simp at hfilt

-- ── Well-kindedness of the generated types ──────────────────────────

/-- The arities that a context must register for the eight type constructors that a generable type can
    name. Each type that the generators build is generable, so this predicate is the whole content of the
    `signatureWellKinded` field of the typing specification of a function and of a procedure. Such a
    field asks that each type of the signature is well-kinded in the context `C`, which means that each
    type constructor is applied at the arity that `C.knownTypes` records for it.

    A bitvector needs no entry, because `.bitvec n` is its own `LMonoTy` constructor and it gives no
    pair to `getTypeConsArities`. `coreContextSimpleTyArities` discharges this predicate for the Strata
    Core context. -/
structure SimpleTyArities (C : LContext CoreLParams) : Prop where
  bool : C.knownTypes["bool"]? = some 0
  int : C.knownTypes["int"]? = some 0
  string : C.knownTypes["string"]? = some 0
  real : C.knownTypes["real"]? = some 0
  regex : C.knownTypes["regex"]? = some 0
  arrow : C.knownTypes["arrow"]? = some 2
  map : C.knownTypes["Map"]? = some 2
  seq : C.knownTypes["Sequence"]? = some 1

/-- **A generable type is well-kinded in each context that registers the arities.** The proof is by
    induction on the type. Each constructor gives exactly one pair to `getTypeConsArities`, at its own
    arity, together with the pairs of its arguments. -/
theorem genLMonoTy_mem_wellKindedTy {C : LContext CoreLParams} (hC : SimpleTyArities C)
    {tvars : List TyIdentifier} :
    ∀ {ty : LMonoTy},
      (∃ m, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      C.WellKindedTy ty := by
  intro ty hTy
  -- The hypothesis is an `∃`, so `induction … using` cannot see the target. A `refine` against the
  -- eliminator can see it.
  refine genLMonoTy_mem_rec (motive := fun ty => C.WellKindedTy ty)
    ?bool ?int ?string ?real ?regex ?bitvec ?ftvar ?arrow ?map ?seq hTy
  all_goals unfold LContext.WellKindedTy LMonoTy.WellKinded
  case bool | int | string | real | regex =>
    intro ref n hn
    simp only [LMonoTy.bool, LMonoTy.int, LMonoTy.string, LMonoTy.real, LMonoTy.regex,
      getTypeConsArities, List.flatMap_nil, List.length_nil, List.mem_singleton,
      Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    first
      | exact hC.bool | exact hC.int | exact hC.string | exact hC.real | exact hC.regex
  case bitvec => intro w ref n hn; simp [getTypeConsArities] at hn
  case ftvar => intro name _ ref n hn; simp [getTypeConsArities] at hn
  case arrow =>
    intro τ₁ τ₂ _ _ ih₁ ih₂ ref n hn
    simp only [LMonoTy.arrow, getTypeConsArities, List.length_cons, List.length_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append,
      Prod.mk.injEq] at hn
    rcases hn with ⟨rfl, rfl⟩ | hn | hn
    · exact hC.arrow
    · exact ih₁ ref n hn
    · exact ih₂ ref n hn
  case map =>
    intro τ₁ τ₂ _ _ ih₁ ih₂ ref n hn
    simp only [LMonoTy.map, getTypeConsArities, List.length_cons, List.length_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append,
      Prod.mk.injEq] at hn
    rcases hn with ⟨rfl, rfl⟩ | hn | hn
    · exact hC.map
    · exact ih₁ ref n hn
    · exact ih₂ ref n hn
  case seq =>
    intro τ _ ih ref n hn
    simp only [LMonoTy.seq, getTypeConsArities, List.length_cons, List.length_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
      Prod.mk.injEq] at hn
    rcases hn with ⟨rfl, rfl⟩ | hn
    · exact hC.seq
    · exact ih ref n hn

-- ── How a generator can change the context ──────────────────────────
--
-- Only two statement generators change `C`. `genFuncDeclStmt` calls `addFactoryFunction`, which leaves
-- `knownTypes` as it is. `genTypeDeclStmt` calls `addKnownTypeWithError`, which *adds* one name and
-- fails on a name that is already present. Both therefore keep each existing entry of the known types,
-- and that is all that `SimpleTyArities` and `WellKindedTy` read.

/-- A successful `Identifiers.addWithError` inserts a *new* key only. Therefore each entry that is
    already present keeps its value. -/
theorem Identifiers.addWithError_mono {IDMeta} [DecidableEq IDMeta]
    {m m' : Identifiers IDMeta} {x : Identifier IDMeta} {f : Strata.Message}
    (h : Identifiers.addWithError m x f = .ok m') :
    ∀ (n : String) (v : IDMeta), m[n]? = some v → m'[n]? = some v := by
  intro n v hn
  unfold Identifiers.addWithError at h
  rcases hcti : Std.HashMap.containsThenInsertIfNew m x.name x.metadata with ⟨b, m2⟩
  rw [hcti] at h
  simp only at h
  have hm2 : m2 = m.insertIfNew x.name x.metadata := by
    rw [← Std.HashMap.containsThenInsertIfNew_snd (m := m) (k := x.name) (v := x.metadata), hcti]
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h
    subst h; subst hm2
    rw [Std.HashMap.getElem?_insertIfNew]
    have hmem : n ∈ m := Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [hn]; rfl)
    split
    · rename_i hc
      obtain ⟨hbeq, hnotmem⟩ := hc
      rw [beq_iff_eq] at hbeq
      subst hbeq
      exact absurd hmem hnotmem
    · exact hn

/-- A declaration of a new type constructor keeps each arity that is already registered. -/
theorem addKnownTypeWithError_mono {C C' : LContext CoreLParams} {k : KnownType}
    {f : Strata.Message} (h : C.addKnownTypeWithError k f = .ok C') :
    ∀ (n : String) (v : Nat), C.knownTypes[n]? = some v → C'.knownTypes[n]? = some v := by
  intro n v hn
  dsimp only [LContext.addKnownTypeWithError, bind, Except.instMonad, Except.bind] at h
  split at h
  · simp at h
  · rename_i ks hadd
    simp only [Except.ok.injEq] at h
    subst h
    exact Identifiers.addWithError_mono hadd n v hn

/-- A declaration of a function does not change the table of the known types. -/
@[simp] theorem addFactoryFunction_knownTypes {C : LContext CoreLParams}
    (fn : LFunc CoreLParams) : (C.addFactoryFunction fn).knownTypes = C.knownTypes := by
  simp only [LContext.addFactoryFunction]; split <;> rfl

/-- `SimpleTyArities` transports along a known-type extension. -/
theorem simpleTyArities_mono {C C' : LContext CoreLParams}
    (h : ∀ (n : String) (v : Nat), C.knownTypes[n]? = some v → C'.knownTypes[n]? = some v)
    (hC : SimpleTyArities C) : SimpleTyArities C' :=
  { bool := h _ _ hC.bool, int := h _ _ hC.int, string := h _ _ hC.string
    real := h _ _ hC.real, regex := h _ _ hC.regex, arrow := h _ _ hC.arrow
    map := h _ _ hC.map, seq := h _ _ hC.seq }

-- ── `Map.values` under `insert` ──────────────────────────────────────

theorem Map.values_eq_map_snd {α β : Type} (m : Map α β) : m.values = m.map Prod.snd := by
  induction m with
  | nil => rfl
  | cons p m ih => cases p; simp [Map.values, ih]

/-- An `insert` adds the new value only to the values of a map. -/
theorem mem_values_insert {α β : Type} [DecidableEq α] (m : Map α β) (a : α) (b : β) {v : β}
    (h : v ∈ (Map.insert m a b).values) : v = b ∨ v ∈ m.values := by
  induction m with
  | nil =>
    simp only [Map.insert, Map.values_eq_map_snd, List.map_cons, List.map_nil,
      List.mem_singleton] at h
    exact Or.inl h
  | cons p m ih =>
    obtain ⟨k, w⟩ := p
    rw [Map.values_eq_map_snd] at h ⊢
    simp only [Map.insert] at h
    split at h
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr (List.mem_cons_self ..)
      · rw [← Map.values_eq_map_snd] at h
        rcases ih h with rfl | h'
        · exact Or.inl rfl
        · rw [Map.values_eq_map_snd] at h'
          exact Or.inr (List.mem_cons_of_mem _ h')

-- ── The same closure results, for `LContext.WellKindedTy` ───────────
--
-- One route to the `WellKindedTy` obligation of the `init` rules goes through generability, which is
-- the type vocabulary of the *generator*, and it then applies `genLMonoTy_mem_wellKindedTy`. That route
-- stops as soon as a context holds a type that the generator did not build. The most important such
-- type is the `tcons` of a datatype, which a generated block of datatypes gives to `octx` through the
-- operators of its constructors. That type is well-kinded in the context that registers the block, and
-- the type generator cannot give it.
--
-- `LContext.WellKindedTy` is itself closed under each operation that a generator performs on a type of
-- the context. Therefore the results below are the ones to state the discipline of the statement
-- generators against. They give the generability forms through `genLMonoTy_mem_wellKindedTy`, and they
-- stay true at the level of a program.

/-- `C.WellKindedTy` reads `C.knownTypes` only. Therefore it stays true after each extension of the
    table of the known types that keeps the existing entries. -/
theorem wellKindedTy_mono {C C' : LContext CoreLParams}
    (h : ∀ (n : String) (k : Nat), C.knownTypes[n]? = some k → C'.knownTypes[n]? = some k)
    {ty : LMonoTy} (hty : C.WellKindedTy ty) : C'.WellKindedTy ty :=
  fun ref n hn => h ref n (hty ref n hn)

/-- The arity pairs of the result type of an `arrow` are also arity pairs of the arrow. -/
theorem wellKindedTy_arrow_right {C : LContext CoreLParams} {a b : LMonoTy}
    (h : C.WellKindedTy (.arrow a b)) : C.WellKindedTy b := by
  intro ref n hn
  refine h ref n ?_
  simp only [LMonoTy.arrow, getTypeConsArities, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr hn)

/-- Each syntactic subtype of a well-kinded type is well-kinded. `syntacticSubtypes` goes into the two
    components of an `arrow` only, and the arity pairs of those components are also arity pairs of the
    arrow. -/
theorem wellKindedTy_syntacticSubtypes {C : LContext CoreLParams} :
    ∀ (ty : LMonoTy), C.WellKindedTy ty → ∀ σ ∈ syntacticSubtypes ty, C.WellKindedTy σ := by
  intro ty
  induction ty using syntacticSubtypes.induct with
  | case1 a b ih₁ ih₂ =>
    intro hty σ hσ
    simp only [syntacticSubtypes, List.mem_cons, List.mem_append] at hσ
    have harities : ∀ ref n, (ref, n) ∈ getTypeConsArities a ∨ (ref, n) ∈ getTypeConsArities b →
        (ref, n) ∈ getTypeConsArities (LMonoTy.tcons "arrow" [a, b]) := by
      intro ref n hn
      simp only [getTypeConsArities, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.mem_append]
      exact Or.inr hn
    rcases hσ with rfl | hσ | hσ
    · exact hty
    · exact ih₁ (fun ref n hn => hty ref n (harities ref n (Or.inl hn))) σ hσ
    · exact ih₂ (fun ref n hn => hty ref n (harities ref n (Or.inr hn))) σ hσ
  | case2 ty _ =>
    intro hty σ hσ
    simp only [syntacticSubtypes, List.mem_singleton] at hσ
    exact hσ ▸ hty

/-- `addNewTypes` keeps well-kindedness. It adds the result type of an `arrow` that the list already
    holds, and nothing else. -/
theorem wellKindedTy_addNewTypes {C : LContext CoreLParams} (fuel : Nat) (tys : List LMonoTy)
    (hAll : ∀ σ ∈ tys, C.WellKindedTy σ) :
    ∀ σ ∈ addNewTypes fuel tys, C.WellKindedTy σ := by
  induction fuel generalizing tys with
  | zero => simpa [addNewTypes] using hAll
  | succ n ih =>
    simp only [addNewTypes]
    split
    · exact hAll
    · apply ih
      intro σ hσ
      rcases List.mem_append.mp hσ with hOld | hNew
      · exact hAll σ hOld
      · simp only [List.mem_filterMap] at hNew
        obtain ⟨ty, hty_mem, hty_eq⟩ := hNew
        split at hty_eq
        · rename_i argTy retTy
          split at hty_eq
          · simp only [Option.some.injEq] at hty_eq; subst hty_eq
            exact wellKindedTy_arrow_right (hAll _ hty_mem)
          · simp at hty_eq
        · simp at hty_eq

/-- **Each type that the call generator can sample is well-kinded in `C`**, if each type in the variable
    contexts and in the operator context is. `generableTypesFromCtx` takes a syntactic subtype of a type
    of the context, and the result type of an `arrow`, and nothing else. `C.WellKindedTy` is closed under
    both operations. This lemma is the `WellKindedTy` form of `generableTypesFromCtx_simple`, and it also
    holds when the constructor operators of a datatype block are in `octx`. -/
theorem generableTypesFromCtx_wellKinded {C : LContext CoreLParams}
    (bctx : BVarCtx) (fctx : FVarCtx) (octx : OpCtx)
    (hBctx : ∀ τ ∈ bctx, C.WellKindedTy τ)
    (hFctx : ∀ p ∈ fctx, C.WellKindedTy p.2)
    (hOctx : ∀ p ∈ octx.ops, C.WellKindedTy p.2) :
    ∀ σ ∈ generableTypesFromCtx bctx fctx octx, C.WellKindedTy σ := by
  intro σ hσ
  unfold generableTypesFromCtx at hσ
  refine wellKindedTy_addNewTypes _ _ ?_ σ hσ
  intro τ hτ
  rw [dedupTys_eq] at hτ
  have hτ' := List.mem_eraseDups.mp hτ
  rw [List.mem_flatMap] at hτ'
  obtain ⟨ty, hty_mem, hty_sub⟩ := hτ'
  have hty_wk : C.WellKindedTy ty := by
    have hty_mem' := hty_mem
    simp only [List.mem_append, List.mem_map] at hty_mem'
    rcases hty_mem' with (hb | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact hBctx ty hb
    · exact hFctx p hp
    · exact hOctx p hp
  exact wellKindedTy_syntacticSubtypes ty hty_wk τ hty_sub

/-- **`LMonoTy.subst` keeps well-kindedness** when each type in the range of the substitution is
    well-kinded. A substitution rewrites an `ftvar`, which gives no arity pair, and it leaves each type
    constructor at its original number of arguments. -/
theorem subst_wellKinded {C : LContext CoreLParams} (S : Lambda.Subst)
    (hSubst : ∀ v t, Strata.Util.HMaps.find? S v = some t → C.WellKindedTy t) :
    ∀ (ty : LMonoTy), C.WellKindedTy ty → C.WellKindedTy (LMonoTy.subst S ty) := by
  intro ty
  induction ty with
  | ftvar f =>
    intro _
    simp only [LMonoTy.subst_unfold]
    split
    · exact hSubst _ _ ‹_›
    · intro ref n hn; simp [getTypeConsArities] at hn
  | bitvec n =>
    intro _
    simp only [LMonoTy.subst_unfold]
    intro ref m hm; simp [getTypeConsArities] at hm
  | tcons name args ih =>
    intro hty
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    intro ref n hn
    simp only [getTypeConsArities, List.length_map, List.mem_cons, List.mem_flatMap,
      List.mem_map] at hn
    rcases hn with hhead | ⟨_, ⟨a, ha, rfl⟩, hn⟩
    · exact hty ref n (by simp only [getTypeConsArities, List.mem_cons]; exact Or.inl hhead)
    · refine ih a ha (fun ref' n' hn' => hty ref' n' ?_) ref n hn
      simp only [getTypeConsArities, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨a, ha, hn'⟩

/-- **The soundness of the monomorphic Indir rule**, for an arbitrary argument generator. The hypothesis
    `hArg` says that `genArg σ` gives a term of the type `σ` only. Then the full application that
    `genIndir` builds has the type `τ`.

    The statement holds for an arbitrary `genArg`, because `genLExpr` instantiates it *two* ways. At the
    depth floor it uses `genLExprBase`, and above the floor it uses `genLExpr` itself, so that a factory
    application can nest. -/
theorem genIndir_sound (octx : OpCtx) (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → HasTypeA' bctx a σ)
    (h : (findOpsInCtx octx τ).length > 0)
    (e : LExpr')
    (he : e ∈ SetGen.support (genIndir (G := SetGen.Set) octx τ genArg h)) :
    HasTypeA' bctx e τ := by
  unfold genIndir at he
  simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
  obtain ⟨entry, hentry_mem, args, hargs, rfl⟩ := he
  rw [← mem_support_iff, mem_support_elements_iff] at hentry_mem
  have hbase : HasTypeA' bctx (.op () ⟨entry.1, ()⟩ _)
      (entry.2.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) := .op
  have hforall₂ := (mem_mapM_iff genArg entry.2 args).mp hargs
  have hargs_typed : List.Forall₂ (HasTypeA' bctx) args entry.2 := by
    suffices hsuff : ∀ (tys : List LMonoTy) (es : List LExpr'),
        List.Forall₂ (fun arg σ => arg ∈ (genArg σ)) es tys →
        List.Forall₂ (HasTypeA' bctx) es tys from
      hsuff entry.2 args hforall₂
    intro tys es hf₂
    induction hf₂ with
    | nil => exact .nil
    | @cons a ty _ _ hmem _ ih => exact .cons (hArg ty a hmem) ih
  exact mkApps_hasType bctx _ args entry.2 τ hbase hargs_typed

/-- The soundness of `genIndirPoly`. Each generated expression is well-typed.

    The proof uses one structural fact: `genIndirPoly` gives either the `genLExprBase` fallback, when no
    candidate matches, or a spine `mkApps (.op () ⟨name, ()⟩ (some fullArrowTy)) args`, where
    `fullArrowTy` is `concreteArgTys.foldr arrow τ`.

    For the spine, the proof has three steps:
    - `HasTypeA.op` reads the annotation, and it gives the type `fullArrowTy` to the `.op` node.
    - `genArg` generates each argument at a concrete type, and the hypothesis `hArg` gives the type of
      that argument. At the depth floor the caller discharges `hArg` with the soundness of
      `genLExprBase`. Above the floor it uses the inductive hypothesis of the soundness of `genLExpr`,
      and that is what makes a *nested* factory application sound.
    - `mkApps_hasType` folds the applications, and the result type is `τ`.

    The fallback branch goes to `genLExprBase` at the same depth, so the soundness of `genLExprBase`
    discharges it directly, for each `genArg`. -/
theorem genIndirPoly_sound (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → HasTypeA' bctx a σ)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs genArg)) :
    HasTypeA' bctx e τ := by
  -- `genIndirPoly` is the wrapper around `genIndirPolyCore`, so the result for an arbitrary argument
  -- generator applies directly. `hArg` gives the soundness of `genArg`, and the fallback is
  -- `genLExprBase` at the same depth, which `genLExprBase_sound` handles.
  exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx τ
    genArg _ maxNumArgs hArg
    (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx depth τ a ha) e he

/-- The soundness of `genLExpr`. Each generated expression is well-typed. The proof joins the soundness
    of the Indir rule and of the IndirPoly rule with the soundness of `genLExprBase`. -/
theorem genLExpr_sound (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat)
    (τ : LMonoTy) (maxNumArgs : Nat)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs)) :
    HasTypeA' bctx e τ := by
  -- The induction is on the depth index. `genLExpr` is structurally recursive on that index, because
  -- each *argument* of an Indir rule comes from `genLExpr` at the smaller index. Therefore the soundness
  -- of the argument generator at the smaller index is the inductive hypothesis. Both branches then have
  -- one shape, and they differ only in the `hArg` that they give.
  induction depth generalizing τ e with
  | zero =>
    -- At the depth floor, each argument comes from `genLExprBase` at the depth 0.
    have hArg : ∀ σ a, a ∈ SetGen.support
        (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 σ) → HasTypeA' bctx a σ :=
      fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx 0 σ a ha
    unfold genLExpr at he
    simp only [mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨hpos, he⟩ | ⟨_, he⟩
    · -- Monomorphic Indir candidates: two-element frequency, then a binary pick
      rw [← mem_support_iff, mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact genLExprBase_sound fctx octx pctx tvars bctx 0 τ e he
      rw [mem_support_pick_iff] at he
      rcases he with he | he
      · exact genIndir_sound octx bctx τ _ hArg hpos e he
      · exact genIndirPoly_sound fctx octx pctx tvars bctx 0 τ _ _ hArg e he
    · rw [pick_mem_iff] at he
      rcases he with he | he
      · exact genLExprBase_sound fctx octx pctx tvars bctx 0 τ e he
      · exact genIndirPoly_sound fctx octx pctx tvars bctx 0 τ _ _ hArg e he
  | succ n ih =>
    -- Above the floor, each argument comes from `genLExpr` at `n`, and `ih` is its soundness. This case
    -- is the one that makes a nested factory application sound.
    have hArg : ∀ σ a, a ∈ SetGen.support
        (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx n σ maxNumArgs) →
        HasTypeA' bctx a σ :=
      fun σ a ha => ih σ a ha
    unfold genLExpr at he
    simp only [mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨hpos, he⟩ | ⟨_, he⟩
    · rw [← mem_support_iff, mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact genLExprBase_sound fctx octx pctx tvars bctx (n + 1) τ e he
      rw [mem_support_pick_iff] at he
      rcases he with he | he
      · exact genIndir_sound octx bctx τ _ hArg hpos e he
      · exact genIndirPoly_sound fctx octx pctx tvars bctx (n + 1) τ _ _ hArg e he
    · rw [pick_mem_iff] at he
      rcases he with he | he
      · exact genLExprBase_sound fctx octx pctx tvars bctx (n + 1) τ e he
      · exact genIndirPoly_sound fctx octx pctx tvars bctx (n + 1) τ _ _ hArg e he

-- ── No-free-variables guarantees for the empty fvar context ────────────

namespace Lambda.LExpr

private theorem fvarsOfType_subset_keys (fctx : FVarCtx) (τ : LMonoTy) (name : String)
    (h : name ∈ fvarsOfType fctx τ) :
    (⟨name, ()⟩ : Lambda.Identifier Unit) ∈ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) := by
  simp only [fvarsOfType, List.mem_filterMap] at h
  obtain ⟨⟨x, ty⟩, hmem, hif⟩ := h
  simp only at hif
  split at hif
  · rename_i heq
    simp at hif; subst hif
    exact List.mem_map.mpr ⟨(x, ty), hmem, rfl⟩
  · simp at hif

private theorem getVars_fvar_subset (fctx : FVarCtx) (τ : LMonoTy) (name : String)
    (h : name ∈ fvarsOfType fctx τ) :
    LExpr.getVars (LExpr.fvar () ⟨name, ()⟩ (some τ) : LExpr') ⊆
      fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) := by
  intro y hy
  simp only [LExpr.getVars, List.mem_singleton] at hy
  subst hy
  exact fvarsOfType_subset_keys fctx τ name h

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- Each free variable of an expression in the support of `genLExprBase` comes from the context `fctx`.
    The only source of a free variable is `pickFVar`, which draws each name from `fctx`.

    In an Indir branch, the head is an `.op` node and holds no free variable, and each argument comes
    from `genLExprBase` at the smaller depth. The recursive call of this theorem therefore bounds the
    free variables of each argument. The IndirPoly branch is the same, and it includes the fallback. -/
theorem genLExprBase_fvars_subset (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth τ)) :
    LExpr.getVars e ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) := by
  rw [genLExprBase.eq_def] at he
  split at he
  case h_1 τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.arrow τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_arrow] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, h⟩) | ((⟨hf, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩))
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact h.elim
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name hmem
    · exact h.elim
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact h.elim
  case h_3 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .bool) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_bool] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (rfl | rfl) | ((⟨_, h⟩ | ⟨_, rfl | rfl⟩) | ((⟨hf, h⟩ | ⟨_, rfl | rfl⟩) | (⟨_, h⟩ | ⟨_, rfl | rfl⟩)))
    · simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name hmem
    · simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · simp [LExpr.getVars]
  case h_5 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .int) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_int] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩)))
    · simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name hmem
    · simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · simp [LExpr.getVars]
  case h_9 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .string) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_string] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨k, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)))
    · simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name hmem
    · simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
  case h_11 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .real) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_real] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨r, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩)))
    · simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name hmem
    · simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
  case h_13 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.bitvec n)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨k, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)))
    · simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name hmem
    · simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · simp [LExpr.getVars]
  case h_4 n =>
    -- bool, depth n+1
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .bool) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_bool] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genBoolConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .bool) (genLExprBase fctx octx pctx tvars bctx n) .bool),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .bool)),
         (2, fun () => genEq (genGenerableTy fctx octx tvars bctx n) (genLExprBase fctx octx pctx tvars bctx n)),
         (2, fun () => genQuant .all (genGenerableTy fctx octx tvars bctx n)
           (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n)
           (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n .bool)),
         (2, fun () => genQuant .exist (genGenerableTy fctx octx tvars bctx n)
           (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n)
           (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n .bool)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .bool).length > 0 then pickBVar bctx .bool hv
           else genBoolConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .bool).length > 0 then pickFVar fctx .bool hf
           else genBoolConst),
         (2, fun () =>
           if ho : (opsOfType octx .bool).length > 0 then pickOp octx .bool ho
           else genBoolConst),
         (4, fun () =>
           if hi : (findOpsInCtx octx .bool).length > 0
           then genIndir octx .bool (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .bool),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .bool
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .bool)) ]
      ) (by show 0 < 1+1+2+2+2+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genBoolConst, genApp, genIte, genEq, genQuant, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with rfl | rfl <;> simp [LExpr.getVars]
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · obtain ⟨τ', hτ'm, e₁, he₁, e₂, he₂, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he₁,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he₂⟩
    · obtain ⟨τ', hτ'm, τ_tr, hτ_tr_m, tr, htr, body, hbody, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars (τ' :: bctx) n _ _ htr,
         genLExprBase_fvars_subset fctx octx pctx tvars (τ' :: bctx) n _ _ hbody⟩
    · obtain ⟨τ', hτ'm, τ_tr, hτ_tr_m, tr, htr, body, hbody, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars (τ' :: bctx) n _ _ htr,
         genLExprBase_fvars_subset fctx octx pctx tvars (τ' :: bctx) n _ _ hbody⟩
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
      · simp [LExpr.getVars]
    · rcases he with ⟨hf, h⟩ | ⟨_, rfl | rfl⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name hmem
      · simp [LExpr.getVars]
      · simp [LExpr.getVars]
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
      · simp [LExpr.getVars]
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_6 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .int) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_int] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genIntConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .int) (genLExprBase fctx octx pctx tvars bctx n) .int),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .int)
                              (genLExprBase fctx octx pctx tvars bctx n .int)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .int).length > 0 then pickBVar bctx .int hv
           else genIntConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .int).length > 0 then pickFVar fctx .int hf
           else genIntConst),
         (2, fun () =>
           if ho : (opsOfType octx .int).length > 0 then pickOp octx .int ho
           else genIntConst),
         (4, fun () =>
           if hi : (findOpsInCtx octx .int).length > 0
           then genIndir octx .int (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .int),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .int
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .int)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genIntConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩ <;> simp [LExpr.getVars]
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
      · simp [LExpr.getVars]
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name hmem
      · simp [LExpr.getVars]
      · simp [LExpr.getVars]
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
      · simp [LExpr.getVars]
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_10 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .string) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_string] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genStrConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .string) (genLExprBase fctx octx pctx tvars bctx n) .string),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .string)
                              (genLExprBase fctx octx pctx tvars bctx n .string)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .string).length > 0 then pickBVar bctx .string hv
           else genStrConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .string).length > 0 then pickFVar fctx .string hf
           else genStrConst),
         (2, fun () =>
           if ho : (opsOfType octx .string).length > 0 then pickOp octx .string ho
           else genStrConst),
         (4, fun () =>
           if hi : (findOpsInCtx octx .string).length > 0
           then genIndir octx .string (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .string),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .string
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .string)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genStrConst, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨s, _, rfl⟩ := he; simp [LExpr.getVars]
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name hmem
      · simp [LExpr.getVars]
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_12 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .real) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_real] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genRealConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .real) (genLExprBase fctx octx pctx tvars bctx n) .real),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .real)
                              (genLExprBase fctx octx pctx tvars bctx n .real)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .real).length > 0 then pickBVar bctx .real hv
           else genRealConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .real).length > 0 then pickFVar fctx .real hf
           else genRealConst),
         (2, fun () =>
           if ho : (opsOfType octx .real).length > 0 then pickOp octx .real ho
           else genRealConst),
         (4, fun () =>
           if hi : (findOpsInCtx octx .real).length > 0
           then genIndir octx .real (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .real),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .real
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .real)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genRealConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨r, _, rfl⟩ := he; simp [LExpr.getVars]
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name hmem
      · simp [LExpr.getVars]
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_14 m n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (m + 1) (.bitvec n)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genBitvecConst (G := SetGen.Set) n),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx m (.bitvec n)) (genLExprBase fctx octx pctx tvars bctx m) (.bitvec n)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx m .bool)
                              (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))
                              (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.bitvec n)).length > 0 then pickBVar bctx (.bitvec n) hv
           else genBitvecConst n),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.bitvec n)).length > 0 then pickFVar fctx (.bitvec n) hf
           else genBitvecConst n),
         (2, fun () =>
           if ho : (opsOfType octx (.bitvec n)).length > 0 then pickOp octx (.bitvec n) ho
           else genBitvecConst n),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.bitvec n)).length > 0
           then genIndir octx (.bitvec n) (genLExprBase fctx octx pctx tvars bctx m) hi
           else genLExprBase fctx octx pctx tvars bctx m (.bitvec n)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.bitvec n)
             (genLExprBase fctx octx pctx tvars bctx m)
             (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genBitvecConst, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨k, _, rfl⟩ := he; simp [LExpr.getVars]
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx m _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx m _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx m _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx m _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx m _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name hmem
      · simp [LExpr.getVars]
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp [LExpr.getVars]
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx m σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx m _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx m σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx m _ a ha) e he
  case h_2 n τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) (.arrow τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_arrow] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (4, fun () => genAbs (G := SetGen.Set) (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.arrow τ₁ τ₂)) (genLExprBase fctx octx pctx tvars bctx n) (.arrow τ₁ τ₂)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))
                              (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.arrow τ₁ τ₂)).length > 0 then pickBVar bctx (.arrow τ₁ τ₂) hv
           else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0 then pickFVar fctx (.arrow τ₁ τ₂) hf
           else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (2, fun () =>
           if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0 then pickOp octx (.arrow τ₁ τ₂) ho
           else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.arrow τ₁ τ₂)).length > 0
           then genIndir octx (.arrow τ₁ τ₂) (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.arrow τ₁ τ₂)
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))) ]
      ) (by show 0 < 4+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genAbs, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨body, hbody, rfl⟩ := he
      simp only [LExpr.getVars]
      exact genLExprBase_fvars_subset fctx octx pctx tvars (τ₁ :: bctx) n _ _ hbody
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp only [LExpr.getVars]
        exact genLExprBase_fvars_subset fctx octx pctx tvars (τ₁ :: bctx) n _ _ hbody
    · rcases he with ⟨hf, h⟩ | ⟨_, body, hbody, rfl⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name, hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name hmem
      · simp only [LExpr.getVars]
        exact genLExprBase_fvars_subset fctx octx pctx tvars (τ₁ :: bctx) n _ _ hbody
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · simp only [LExpr.getVars]
        exact genLExprBase_fvars_subset fctx octx pctx tvars (τ₁ :: bctx) n _ _ hbody
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_7 name =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.ftvar name)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact absurd h (by simp)
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact absurd h (by simp)
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · exact absurd h (by simp)
  case h_8 n name =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) (.ftvar name)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx octx tvars bctx n (.ftvar name)) (genLExprBase fctx octx pctx tvars bctx n) (.ftvar name)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))
                              (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else if hf : (fvarsOfType fctx (.ftvar name)).length > 0 then pickFVar fctx (.ftvar name) hf
           else if ho : (opsOfType octx (.ftvar name)).length > 0 then pickOp octx (.ftvar name) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.ftvar name)).length > 0 then pickFVar fctx (.ftvar name) hf
           else if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType octx (.ftvar name)).length > 0 then pickOp octx (.ftvar name) ho
           else if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.ftvar name)).length > 0
           then genIndir octx (.ftvar name) (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n (.ftvar name)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.ftvar name)
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name' hmem
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name' hmem
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_15 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 .regex) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact absurd h (by simp)
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact absurd h (by simp)
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · exact absurd h (by simp)
  case h_16 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .regex) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx octx tvars bctx n .regex) (genLExprBase fctx octx pctx tvars bctx n) .regex),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .regex)
                              (genLExprBase fctx octx pctx tvars bctx n .regex)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else if hf : (fvarsOfType fctx .regex).length > 0 then pickFVar fctx .regex hf
           else if ho : (opsOfType octx .regex).length > 0 then pickOp octx .regex ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx .regex).length > 0 then pickFVar fctx .regex hf
           else if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else default),
         (2, fun () =>
           if ho : (opsOfType octx .regex).length > 0 then pickOp octx .regex ho
           else if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx octx .regex).length > 0
           then genIndir octx .regex (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n .regex),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx .regex
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n .regex)) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name' hmem
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name' hmem
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_17 τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.map τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact absurd h (by simp)
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact absurd h (by simp)
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · exact absurd h (by simp)
  case h_18 n τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) (.map τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx octx tvars bctx n (.map τ₁ τ₂)) (genLExprBase fctx octx pctx tvars bctx n) (.map τ₁ τ₂)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))
                              (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0 then pickFVar fctx (.map τ₁ τ₂) hf
           else if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0 then pickOp octx (.map τ₁ τ₂) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0 then pickFVar fctx (.map τ₁ τ₂) hf
           else if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0 then pickOp octx (.map τ₁ τ₂) ho
           else if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.map τ₁ τ₂)).length > 0
           then genIndir octx (.map τ₁ τ₂) (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.map τ₁ τ₂)
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name' hmem
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name' hmem
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_19 τ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 (.seq τ)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact absurd h (by simp)
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · exact absurd h (by simp)
    · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
    · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
      exact getVars_fvar_subset fctx _ name' hmem
    · exact absurd h (by simp)
  case h_20 n τ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) (.seq τ)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx octx tvars bctx n (.seq τ)) (genLExprBase fctx octx pctx tvars bctx n) (.seq τ)),
         (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.seq τ))
                              (genLExprBase fctx octx pctx tvars bctx n (.seq τ))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.seq τ)).length > 0 then pickBVar bctx (.seq τ) hv
           else if hf : (fvarsOfType fctx (.seq τ)).length > 0 then pickFVar fctx (.seq τ) hf
           else if ho : (opsOfType octx (.seq τ)).length > 0 then pickOp octx (.seq τ) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.seq τ)).length > 0 then pickFVar fctx (.seq τ) hf
           else if hv : (bvarsOfType bctx (.seq τ)).length > 0 then pickBVar bctx (.seq τ) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType octx (.seq τ)).length > 0 then pickOp octx (.seq τ) ho
           else if hv : (bvarsOfType bctx (.seq τ)).length > 0 then pickBVar bctx (.seq τ) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx octx (.seq τ)).length > 0
           then genIndir octx (.seq τ) (genLExprBase fctx octx pctx tvars bctx n) hi
           else genLExprBase fctx octx pctx tvars bctx n (.seq τ)),
         (4, fun () =>
           genIndirPolyCore fctx octx pctx bctx (.seq τ)
             (genLExprBase fctx octx pctx tvars bctx n)
             (genLExprBase fctx octx pctx tvars bctx n (.seq τ))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hfn,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      simp only [LExpr.getVars]
      exact List.append_subset.mpr
        ⟨List.append_subset.mpr
          ⟨genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ hc,
           genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ ht⟩,
         genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ _ he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name' hmem
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
        exact getVars_fvar_subset fctx _ name' hmem
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars]
      · rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars]
      · exact absurd h (by simp)
    -- The Indir branch.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- The IndirPoly branch.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_21 =>
    -- The other type constructors give one of the three leaves from the context, as the `.regex` case
    -- at the depth 0 does. A bound-variable leaf and an operator leaf hold no free variable, and the
    -- name of a free-variable leaf comes from `fctx`.
    simp only [mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))
    all_goals first
      | (rw [mem_support_pickBVar_iff] at h; obtain ⟨i, _, rfl⟩ := h; simp [LExpr.getVars])
      | (rw [mem_support_pickOp_iff] at h; obtain ⟨nm, _, rfl⟩ := h; simp [LExpr.getVars])
      | (rw [mem_support_pickFVar_iff] at h; obtain ⟨name', hmem, rfl⟩ := h
         exact getVars_fvar_subset fctx _ name' hmem)
      | exact absurd h (by simp)
  termination_by depth
  decreasing_by all_goals simp_wf; omega

set_option maxHeartbeats 1600000 in
/-- With an empty context of free variables, each expression in the support of `genLExprBase` holds no
    free variable. This is a special case of `genLExprBase_fvars_subset`. -/
theorem genLExprBase_no_fvars (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) [] octx pctx tvars bctx depth τ)) :
    LExpr.getVars e = [] := by
  have h := genLExprBase_fvars_subset [] octx pctx tvars bctx depth τ e he
  simpa using List.subset_nil.mp h

private theorem mkApps_fvars_subset (base : LExpr') (args : List LExpr')
    (keys : List (Lambda.Identifier Unit))
    (hbase : LExpr.getVars base ⊆ keys) (hargs : ∀ a ∈ args, LExpr.getVars a ⊆ keys) :
    LExpr.getVars (mkApps base args) ⊆ keys := by
  induction args generalizing base with
  | nil => simpa [mkApps] using hbase
  | cons a rest ih =>
    simp only [mkApps, List.foldl_cons]
    apply ih
    · simp only [LExpr.getVars]
      exact List.append_subset.mpr ⟨hbase, hargs a (by simp)⟩
    · intro x hx; exact hargs x (by simp [hx])

private theorem mkApps_no_fvars (base : LExpr') (args : List LExpr')
    (hbase : LExpr.getVars base = []) (hargs : ∀ a ∈ args, LExpr.getVars a = []) :
    LExpr.getVars (mkApps base args) = [] := by
  have h := mkApps_fvars_subset base args []
    (by rw [hbase]; exact List.Subset.refl _)
    (by intro a ha; rw [hargs a ha]; exact List.Subset.refl _)
  simpa using List.subset_nil.mp h

/-- Each free variable of each argument that `mapM genArg` gives comes from `fctx`, if the hypothesis
    `hArg` says the same about each `genArg σ`.

    The statement holds for an arbitrary `genArg`, for the same reason as the soundness of `genIndir`.
    `genLExpr` instantiates it with `genLExprBase` at the depth floor, and with itself at the smaller
    depth index above the floor. -/
private theorem mapM_genArg_fvars_subset (fctx : FVarCtx)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) →
      LExpr.getVars a ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)))
    (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set) genArg argTys)) :
    ∀ a ∈ args, LExpr.getVars a ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) := by
  induction argTys generalizing args with
  | nil =>
    simp only [List.mapM_nil, SetGen.Set.mem_pure] at hargs
    subst hargs; intro a ha; simp at ha
  | cons σ rest ih =>
    simp only [List.mapM_cons, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at hargs
    obtain ⟨x, hx, tl, htl, rfl⟩ := hargs
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hrest
    · exact hArg σ a hx
    · exact ih tl htl a hrest

/-- Each free variable of each argument that `mapM (genLExprBase fctx …)` gives comes from `fctx`. This
    is a special case of `mapM_genArg_fvars_subset`. -/
private theorem mapM_genLExprBase_fvars_subset (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set)
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth) argTys)) :
    ∀ a ∈ args, LExpr.getVars a ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) :=
  mapM_genArg_fvars_subset fctx _
    (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx depth σ a ha) argTys args hargs

/-- With an empty context of free variables, each argument that `mapM (genLExprBase [] …)` gives holds no
    free variable. -/
private theorem mapM_genLExprBase_no_fvars (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set)
      (genLExprBase (G := SetGen.Set) [] octx pctx tvars bctx depth) argTys)) :
    ∀ a ∈ args, LExpr.getVars a = [] := by
  intro a ha
  have h := mapM_genLExprBase_fvars_subset [] octx pctx tvars bctx depth argTys args hargs a ha
  simpa using List.subset_nil.mp h

/-- Each free variable of an expression in the support of `genIndirPoly` comes from the context
    `fctx`. -/
theorem genIndirPoly_fvars_subset (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) →
      LExpr.getVars a ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)))
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs genArg)) :
    LExpr.getVars e ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) := by
  -- As in the soundness proof, `genIndirPoly` is the wrapper around `genIndirPolyCore`, so the lemma for
  -- an arbitrary argument generator applies. `genLExprBase_fvars_subset` discharges the fallback.
  exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx τ _
    genArg _ maxNumArgs hArg
    (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx depth τ a ha) e he

/-- With an empty context of free variables, each expression in the support of `genIndirPoly` holds no
    free variable. -/
theorem genIndirPoly_no_fvars (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → LExpr.getVars a = [])
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) [] octx pctx tvars bctx depth τ maxNumArgs genArg)) :
    LExpr.getVars e = [] := by
  have h := genIndirPoly_fvars_subset [] octx pctx tvars bctx depth τ maxNumArgs genArg
    (fun σ a ha => by rw [hArg σ a ha]; exact List.nil_subset _) e he
  simpa using List.subset_nil.mp h

/-- Each free variable of an expression in the support of `genLExpr` comes from the context `fctx`. -/
theorem genLExpr_fvars_subset (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ)) :
    LExpr.getVars e ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) := by
  -- The induction is on the depth index, as in the soundness proof. Each argument of an Indir rule comes
  -- from `genLExpr` at `n`, so the inductive hypothesis is the `hArg` that the two lemmas above need.
  induction depth generalizing τ e with
  | zero =>
    have hArg : ∀ σ a, a ∈ SetGen.support
        (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0 σ) →
        LExpr.getVars a ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) :=
      fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx 0 σ a ha
    unfold genLExpr at he
    simp only [mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨hpos, he⟩ | ⟨_, he⟩
    · rw [← mem_support_iff, mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx 0 τ e he
      rw [mem_support_pick_iff] at he
      rcases he with he | he
      · unfold genIndir at he
        simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
        obtain ⟨entry, hentry_mem, args, hargs, rfl⟩ := he
        exact mkApps_fvars_subset _ args _
          (by simp only [LExpr.getVars]; exact List.nil_subset _)
          (mapM_genArg_fvars_subset fctx _ hArg _ args hargs)
      · exact genIndirPoly_fvars_subset fctx octx pctx tvars bctx 0 τ _ _ hArg e he
    · rw [pick_mem_iff] at he
      rcases he with he | he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx 0 τ e he
      · exact genIndirPoly_fvars_subset fctx octx pctx tvars bctx 0 τ _ _ hArg e he
  | succ n ih =>
    have hArg : ∀ σ a, a ∈ SetGen.support
        (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx n σ) →
        LExpr.getVars a ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) :=
      fun σ a ha => ih σ a ha
    unfold genLExpr at he
    simp only [mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨hpos, he⟩ | ⟨_, he⟩
    · rw [← mem_support_iff, mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx (n + 1) τ e he
      rw [mem_support_pick_iff] at he
      rcases he with he | he
      · unfold genIndir at he
        simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
        obtain ⟨entry, hentry_mem, args, hargs, rfl⟩ := he
        exact mkApps_fvars_subset _ args _
          (by simp only [LExpr.getVars]; exact List.nil_subset _)
          (mapM_genArg_fvars_subset fctx _ hArg _ args hargs)
      · exact genIndirPoly_fvars_subset fctx octx pctx tvars bctx (n + 1) τ _ _ hArg e he
    · rw [pick_mem_iff] at he
      rcases he with he | he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx (n + 1) τ e he
      · exact genIndirPoly_fvars_subset fctx octx pctx tvars bctx (n + 1) τ _ _ hArg e he

/-- With an empty context of free variables, each expression in the support of `genLExpr` holds no free
    variable. -/
theorem genLExpr_no_fvars (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) [] octx pctx tvars bctx depth τ)) :
    LExpr.getVars e = [] := by
  have h := genLExpr_fvars_subset [] octx pctx tvars bctx depth τ e he
  simpa using List.subset_nil.mp h

end Lambda.LExpr

-- ── Completeness for genIndirPoly and genLExpr ─────────────────────────

/-- A type `σ` is in the support of the sampling step for one type variable inside `genIndirPoly`. That
    step draws a random index into `generableTys`, or it draws a base type with `pickBaseType` when the
    list is empty.

    For an empty list, the side condition is membership in the support of `pickBaseType`, because the
    generator samples any ground base type there. -/
private theorem single_sample_mem (generableTys : List LMonoTy) (σ : LMonoTy)
    (hpos : generableTys.length > 0 → σ ∈ generableTys)
    (hneg : ¬(generableTys.length > 0) →
      σ ∈ SetGen.support (pickBaseType (G := SetGen.Set))) :
    σ ∈ ((fun (_ : Unit) =>
      if hg : generableTys.length > 0 then
        elements generableTys (by apply List.ne_nil_of_length_pos; assumption)
      else pickBaseType) () : SetGen.Set LMonoTy) := by
  by_cases hg : generableTys.length > 0
  · simp only [dif_pos hg]
    rw [← mem_support_iff, mem_support_elements_iff]
    exact hpos hg
  · simp only [dif_neg hg]
    exact hneg hg

set_option linter.unusedVariables false in
/-- Each element of the sampling step in `genIndirPoly` is a member of `generableTys` when that list is
    not empty, and a base type from `pickBaseType` when it is empty. Therefore a valid list of sampled
    types is in the support of the sampling step.

    The statement holds for an arbitrary number `k` of samples, and not for the literal 3. The generator
    draws `maxNumArgs` samples, and `maxNumArgs` is a parameter. A fixed `k := 3` would therefore
    specialize each statement below it to the largest arity of the current factory. The proof is by
    induction on `k`. -/
private theorem sampledTys_mem_support (generableTys : List LMonoTy)
    (k : Nat) (sampledTys : List LMonoTy)
    (hLen : sampledTys.length = k)
    (hValid : ∀ σ ∈ sampledTys,
      (generableTys.length > 0 → σ ∈ generableTys) ∧
      (¬(generableTys.length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set)))) :
    sampledTys ∈ ((List.replicate k ()).mapM (fun _ =>
      if hg : generableTys.length > 0 then
        elements generableTys (by apply List.ne_nil_of_length_pos; assumption)
      else pickBaseType) : SetGen.Set (List LMonoTy)) := by
  induction k generalizing sampledTys with
  | zero =>
    match sampledTys, hLen with
    | [], _ => simp only [List.replicate, List.mapM_nil, SetGen.Set.mem_pure]
  | succ k ih =>
    match sampledTys, hLen with
    | a :: rest, hLen' =>
      have hrest : rest.length = k := by simpa using hLen'
      simp only [List.replicate, List.mapM_cons, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
      refine ⟨a, single_sample_mem generableTys a (hValid a (by simp)).1
                  (hValid a (by simp)).2,
              rest, ih rest hrest (fun σ hσ => hValid σ (by simp [hσ])), rfl⟩

/-- The completeness of `genIndirPoly`. Take an expression of the form
    `mkApps (.op () ⟨name, ()⟩ (some fullArrowTy)) args`, where `(name, concreteArgTys)` is a valid entry
    of `findPolymorphicOps` at some list of sampled types, and each argument is in the support of
    `genLExprBase`. Then the expression is in the support of `genIndirPoly`. -/
theorem genIndirPoly_complete (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat)
    (sampledTys : List LMonoTy)
    (hSampledLen : sampledTys.length = maxNumArgs)
    (hSampledValid : ∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set))))
    (name : String) (concreteArgTys : List LMonoTy)
    (hEntry : (name, concreteArgTys) ∈ findPolymorphicOps pctx τ
      (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (args : List LExpr')
    (hArgs : List.Forall₂ (fun arg σ => arg ∈ (genArg σ)) args concreteArgTys) :
    let fullArrowTy := concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
    mkApps (.op () ⟨name, ()⟩ (some fullArrowTy)) args ∈
      SetGen.support
        (genIndirPoly (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs
          genArg) := by
  simp only [SetGen.support]
  -- `genIndirPoly` is a wrapper, so the proof also unfolds the core, which holds the `mapM` of the
  -- samples and the `dite` over the candidates.
  unfold genIndirPoly genIndirPolyCore
  simp only [SetGen.Set.mem_bind, SetGen.Set.mem_pure, SetGen.mem_dite]
  -- The list of sampled types is the witness for the `mapM` of the samples.
  refine ⟨sampledTys, sampledTys_mem_support _ _ _ hSampledLen hSampledValid, ?_⟩
  -- Take the branch of the `dite` for a list of candidates that is not empty.
  have hOpsPos : (findPolymorphicOps pctx τ (generableTypesFromCtx bctx fctx octx)
      sampledTys maxNumArgs).length > 0 :=
    List.length_pos_of_mem hEntry
  left
  refine ⟨hOpsPos, ?_⟩
  -- `elements` draws the candidate, so give `(name, concreteArgTys)` as the entry that it draws, and
  -- then the arguments and the two equations.
  refine ⟨(name, concreteArgTys), ?_, args, ?_, ?_⟩
  · -- (name, concreteArgTys) ∈ elements ops _
    rw [← mem_support_iff, mem_support_elements_iff]
    exact hEntry
  · -- args ∈ concreteArgTys.mapM genArg
    exact (mem_mapM_iff genArg concreteArgTys args).mpr hArgs
  · -- The expression equals mkApps ...
    rfl

/-- **The support of the base generator is a part of the support of `genLExpr`, at the same depth.**

    `genLExpr` offers `genLExprBase … depth τ` as a branch in *both* arms of its `dite`. It has the
    weight 1 in the `frequency` list when there is a monomorphic Indir candidate, and it is the left part
    of the `pick` in the other arm. Therefore `genLExpr` can give each term that the base generator can
    give, and there is no side condition on the depth or on the context.

    This fact lets the premise for each argument of `isPolyApp_of_hasType` be the plain bundle for the
    completeness of `genLExprBase`, although `genLExpr` draws each argument from *itself* at the smaller
    index. The bundle is keyed to the argument budget `depth - 1`, and not to `depth`. -/
theorem genLExprBase_mem_genLExpr (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat) (e : LExpr')
    (he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth τ)) :
    e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs) := by
  simp only [SetGen.support]
  unfold genLExpr
  simp only [SetGen.mem_dite]
  by_cases hops : (findOpsInCtx octx τ).length > 0
  · refine Or.inl ⟨hops, ?_⟩
    rw [← mem_support_iff, mem_support_frequency_iff]
    exact ⟨1, _, List.mem_cons_self, by omega, he⟩
  · exact Or.inr ⟨hops, (pick_mem_iff _).mpr (Or.inl he)⟩

/-- **The bridge for the argument position.**

    `genLExpr` draws each argument of an Indir rule from `genLExprBase` at the depth 0 when it is at the
    depth floor, and from *itself* at `n` above the floor. This lemma proves membership in that generator,
    which the argument clause of `IsPolyApp` states, from the ordinary bundle for the completeness of
    `genLExprBase`. The bundle must be keyed to the **argument budget** `depth - 1`, and not to `depth`.

    The value `depth - 1` is exact. An argument of a factory application does get one unit of depth less
    than the application itself, because the node of the spine takes one unit. At the floor, `depth - 1`
    is 0, and the argument generator is the base generator. Above the floor,
    `genLExprBase_mem_genLExpr` lifts the output of the base generator into `genLExpr` at `n`, and that is
    where a nested factory application becomes reachable. -/
theorem mem_genArg_of_baseComplete (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (σ : LMonoTy)
    (maxNumArgs : Nat)
    (hσ : ∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (arg : LExpr')
    (hwt : HasTypeA' bctx arg σ)
    (hnames : emptyNames arg)
    (hvars : allVarsInCtx fctx octx arg)
    (hats : AllTypesSimple tvars (depth - 1) bctx arg)
    (hdepth : termDepth bctx arg ≤ depth - 1) :
    arg ∈ (match (motive := Nat → LMonoTy → SetGen.Set LExpr') depth with
           | 0 => genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0
           | n + 1 => fun σ' =>
               genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx n σ' maxNumArgs) σ := by
  cases depth with
  | zero =>
    exact genLExprBase_complete fctx octx pctx tvars bctx 0 σ hσ arg hwt hnames hvars hats hdepth
  | succ n =>
    simp only [Nat.succ_sub_one] at hats hdepth
    exact genLExprBase_mem_genLExpr fctx octx pctx tvars bctx n σ maxNumArgs arg
      (genLExprBase_complete fctx octx pctx tvars bctx n σ hσ arg hwt hnames hvars hats hdepth)

/-- The expression is a valid application of a polymorphic operator that `genIndirPoly` can reach. There
    are sampled types, an operator entry of `pctx` that unifies with the target type, and arguments that
    are each in the support of `genLExprBase`. -/
def IsPolyApp (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat) (e : LExpr') : Prop :=
  ∃ (sampledTys : List LMonoTy) (name : String)
    (concreteArgTys : List LMonoTy) (args : List LExpr'),
    -- One sample for each possible type variable, which is `maxNumArgs` samples. That is the number that
    -- `genIndirPoly` draws. The number is not the literal 3, because 3 is only the largest arity of the
    -- current factory, and `maxNumArgs` is a parameter of the generator.
    sampledTys.length = maxNumArgs ∧
    (∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set)))) ∧
    (name, concreteArgTys) ∈ findPolymorphicOps pctx τ
      (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs ∧
    -- Each argument comes from the generator that `genLExpr` uses in the argument position at this
    -- depth. That generator is `genLExprBase` at the depth 0 at the floor, and `genLExpr` at `n` above
    -- the floor. The second case is the one that admits a *nested* factory application.
    List.Forall₂ (fun arg σ =>
      arg ∈ (match (motive := Nat → LMonoTy → SetGen.Set LExpr') depth with
             | 0 => genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0
             | n + 1 => fun σ' =>
                 genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx n σ' maxNumArgs) σ)
      args concreteArgTys ∧
    e = mkApps (.op () ⟨name, ()⟩
      (some (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) args

/-- **The backward direction for the polymorphic case, at the level of the specification.**

    This theorem derives `IsPolyApp` from the *typing judgement* for a full or partial application spine
    over a polymorphic operator. It takes one explicit side condition, `hEntry`, which says that the
    unification search of the generator gives the matching entry of `findPolymorphicOps`.

    The hypothesis `hEntry` therefore holds the one ingredient about unification, which is that the
    `unify` of Strata succeeds at the split point. The proof *derives* each other part from `HasTypeA'`,
    in three steps:

    - The **argument types** come from an inversion of the application spine with
      `mkApps_hasType_inv`. The derivation forces the annotation of the operator to be
      `argTys.foldr arrow τ`, and it gives the type of each argument.
    - The proof **identifies** those argument types with the `concreteArgTys` of the entry, through the
      injectivity of `foldr arrow` at an equal length. Both lists fold to the *same* annotation on the
      `.op` node, and both have the length of the argument list.
    - The **generability of each argument**, which is the fourth part of `IsPolyApp`, comes from the type
      of that argument through the completeness of `genLExprBase`. This step is why the theorem needs
      `HasTypeA'`.

    The premises about the recursive completeness of each argument, which are the same bundle that the
    completeness of `genLExprBase` needs, are true hypotheses. The generability of an argument does not
    follow from its type alone. -/
theorem isPolyApp_of_hasType (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (name : String) (annot : LMonoTy) (args : List LExpr')
    -- The expression is a spine over an `.op` node that holds the annotation `annot`.
    (hwt : HasTypeA' bctx (mkApps (.op () ⟨name, ()⟩ (some annot)) args) τ)
    -- The side condition about unification. The search of the generator over the split points finds this
    -- operator at the argument types that the typing derivation gives.
    (sampledTys : List LMonoTy) (concreteArgTys : List LMonoTy)
    (hLen : sampledTys.length = maxNumArgs)
    (hValid : ∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set))))
    (hEntry : (name, concreteArgTys) ∈ findPolymorphicOps pctx τ
      (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs)
    (hAnnot : annot = concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
    (hArgLen : args.length = concreteArgTys.length)
    -- The premises about the recursive completeness of each argument. There is one bundle for the
    -- completeness of `genLExprBase` for each argument, keyed by position against `concreteArgTys`.
    --
    -- The depth budget here is `depth - 1`, and not `depth`. `genLExpr` is recursive, so each argument
    -- comes from the generator at the *smaller* index. An argument of a factory application therefore has
    -- one unit of depth less than the application itself, because the node of the spine takes one unit.
    (hArgsComplete : List.Forall₂
      (fun arg σ => (∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) ∧
        emptyNames arg ∧ allVarsInCtx fctx octx arg ∧
        AllTypesSimple tvars (depth - 1) bctx arg ∧ termDepth bctx arg ≤ depth - 1)
      args concreteArgTys) :
    IsPolyApp fctx octx pctx tvars bctx depth τ maxNumArgs
      (mkApps (.op () ⟨name, ()⟩ (some annot)) args) := by
  -- Invert the spine, which gives the argument types `argTys` and the type of each argument.
  obtain ⟨argTys, hbase, hargsTyped⟩ := mkApps_hasType_inv bctx _ args τ hwt
  -- The `.op` node has the type of its annotation, so `annot` is `argTys.foldr arrow τ`.
  cases hbase with
  | op =>
    -- Identify the `argTys` from the typing derivation with the `concreteArgTys` of the entry. Both fold
    -- with `τ` to `annot`, and both have the length of the argument list.
    have hlenTyped : args.length = argTys.length := hargsTyped.length_eq
    have hArgTysEq : argTys = concreteArgTys := by
      apply foldr_arrow_inj_of_length_eq argTys concreteArgTys τ
      · omega
      · rw [← hAnnot]
    subst hArgTysEq
    -- Derive the generability of each argument from its type. The goal is about the generator that
    -- `genLExpr` uses in the argument position, so each argument goes through
    -- `mem_genArg_of_baseComplete`, and not through `genLExprBase_complete` directly.
    have hArgsGen : List.Forall₂
        (fun arg σ =>
          arg ∈ (match (motive := Nat → LMonoTy → SetGen.Set LExpr') depth with
                 | 0 => genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0
                 | n + 1 => fun σ' =>
                     genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx n σ'
                       maxNumArgs) σ)
        args argTys := by
      -- Join the type of each argument with the completeness premise for that argument.
      clear hEntry hwt hAnnot hArgLen hlenTyped
      induction hargsTyped with
      | nil => exact .nil
      | @cons arg σ restA restT hargWt hrestWt ih =>
        cases hArgsComplete with
        | @cons _ _ _ _ hpre hrestPre =>
          obtain ⟨hσ, hnames, hvars, hats, hdepth⟩ := hpre
          exact .cons
            (mem_genArg_of_baseComplete fctx octx pctx tvars bctx depth σ maxNumArgs hσ arg
              hargWt hnames hvars hats hdepth)
            (ih hrestPre)
    -- Build the existential of `IsPolyApp`.
    exact ⟨sampledTys, name, argTys, args, hLen, hValid, hEntry, hArgsGen, by rw [hAnnot]⟩

-- ── The well-formedness conditions for `freshenBoundVars` ────────────
--
-- The two disjointness conditions of `SchemeInstAt` are *consequences* of `freshenBoundVars`. Therefore
-- this section derives them from `freshenBoundVars_disjoint`, which is in
-- `HasTypeAGen/Freshening.lean`.
--
-- One true input remains, which is the **closedness of the scheme**. The body of the scheme must name no
-- type variable outside its own binders. Closedness is a property of the entry of `pctx`, and not of
-- `freshenBoundVars`. It holds for each real scheme, such as an entry of `corePolyOps`. It also holds for
-- `factoryPolyOps`, because each entry there has the form `∀ fn.typeArgs. …`.

/-- Both components of `decomposeArrow` mention only the type variables that are
    already free in the type that `decomposeArrow` breaks into parts. The free
    variables of the return type are free in the initial type. The free variables of
    each argument type are also free in the initial type. -/
theorem decomposeArrow_freeVars_subset (t : LMonoTy) :
    (∀ v ∈ (decomposeArrow t).2.freeVars, v ∈ t.freeVars) ∧
    (∀ σ ∈ (decomposeArrow t).1, ∀ v ∈ σ.freeVars, v ∈ t.freeVars) := by
  fun_induction decomposeArrow t with
  | case1 σ rest args ret hrec ih =>
    obtain ⟨ihret, iharg⟩ := ih
    rw [hrec] at ihret iharg
    refine ⟨?_, ?_⟩
    · intro v hv
      show v ∈ LMonoTys.freeVars [σ, rest]
      simp only [LMonoTys.freeVars_of_cons]
      exact List.mem_append_right _ (List.mem_append_left _ (ihret v hv))
    · intro σ' hσ' v hv
      simp only [List.mem_cons] at hσ'
      show v ∈ LMonoTys.freeVars [σ, rest]
      simp only [LMonoTys.freeVars_of_cons]
      rcases hσ' with rfl | hmem
      · exact List.mem_append_left _ hv
      · exact List.mem_append_right _ (List.mem_append_left _ (iharg σ' hmem v hv))
  | case2 ty hne => exact ⟨fun v hv => hv, fun σ hσ => absurd hσ (by simp)⟩

/-- `l.foldr` makes a right-nested arrow type from the argument types in `l` and the
    base type `t`. If a type variable is free in that arrow type, then it is free in
    one of the argument types in `l`, or it is free in `t`. -/
theorem mem_freeVars_foldr_arrow (l : List LMonoTy) (t : LMonoTy) (v : TyIdentifier)
    (h : v ∈ (l.foldr (fun σ acc => LMonoTy.arrow σ acc) t).freeVars) :
    (∃ σ ∈ l, v ∈ σ.freeVars) ∨ v ∈ t.freeVars := by
  induction l with
  | nil => exact Or.inr h
  | cons a rest ih =>
    simp only [List.foldr_cons] at h
    show (∃ σ ∈ a :: rest, v ∈ σ.freeVars) ∨ v ∈ t.freeVars
    have h' : v ∈ LMonoTys.freeVars [a, rest.foldr (fun σ acc => LMonoTy.arrow σ acc) t] := h
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at h'
    rcases h' with ha | hrest
    · exact Or.inl ⟨a, List.mem_cons_self, ha⟩
    · simp only [LMonoTys.freeVars, List.not_mem_nil, or_false] at hrest
      rcases ih hrest with ⟨σ, hσ, hv⟩ | ht
      · exact Or.inl ⟨σ, List.mem_cons_of_mem _ hσ, hv⟩
      · exact Or.inr ht

/-- **The two well-formedness conditions, derived.**

    `hclosed` is the only input. It gives *scheme closedness*: each type variable of
    the scheme body is one of the binders of that scheme. `freshenBoundVars` gets a
    `varsInUse` set that contains `FV(τ)`. Therefore the fresh bound variables are
    disjoint from `FV(τ)`, and the remaining arrow suffix is also disjoint from
    `FV(τ)`.

    These two conditions are the conjuncts that `SchemeInstAt` demanded as premises
    before. The proof has three steps:
    - `freshenBoundVars_disjoint` gives the disjointness for `freshBoundVars` and for
      `FV(freshMonoTy)`.
    - `decomposeArrow_freeVars_subset` and `mem_freeVars_foldr_arrow` move the second
      result to the `drop k` suffix. The variables of that suffix are a subset of the
      variables of `freshMonoTy`.
    - `List.mem_eraseDups` shows that `FV(τ)` is a part of the `varsInUse` set that
      the generator gives to `freshenBoundVars`. -/
theorem schemeInstAt_freshening_disjoint
    (fctx : FVarCtx) (octx : OpCtx) (bctx : BVarCtx) (τ : LMonoTy)
    (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (freshBoundVars : List TyIdentifier) (freshMonoTy : LMonoTy)
    (schemeArgTys : List LMonoTy) (retTy : LMonoTy) (k : Nat)
    (hclosed : ∀ v ∈ monoTy.freeVars, v ∈ boundVars)
    (hfresh : freshenBoundVars boundVars monoTy
      ((LMonoTy.freeVars τ ++ (generableTypesFromCtx bctx fctx octx).flatMap
        LMonoTy.freeVars).eraseDups) = (freshBoundVars, freshMonoTy))
    (hdec : decomposeArrow freshMonoTy = (schemeArgTys, retTy)) :
    (∀ v ∈ ((schemeArgTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc)
      retTy).freeVars, v ∉ τ.freeVars) ∧
    (∀ v ∈ freshBoundVars, v ∉ τ.freeVars) := by
  obtain ⟨hbv, hbody⟩ :=
    freshenBoundVars_disjoint boundVars monoTy _ hclosed freshBoundVars freshMonoTy hfresh
  -- The `varsInUse` set that the generator gives to `freshenBoundVars` contains `FV(τ)`.
  have hτsub : ∀ v ∈ τ.freeVars, v ∈
      ((LMonoTy.freeVars τ ++ (generableTypesFromCtx bctx fctx octx).flatMap
        LMonoTy.freeVars).eraseDups) :=
    fun v hv => List.mem_eraseDups.mpr (List.mem_append_left _ hv)
  refine ⟨?_, fun v hv hc => hbv v hv (hτsub v hc)⟩
  -- The suffix conjunct: each variable of the suffix is free in `freshMonoTy`.
  intro v hv hc
  have hsub : v ∈ freshMonoTy.freeVars := by
    obtain ⟨hret, harg⟩ := decomposeArrow_freeVars_subset freshMonoTy
    rw [hdec] at hret harg
    rcases mem_freeVars_foldr_arrow _ _ v hv with ⟨σ, hσ, hvσ⟩ | hvret
    · exact harg σ (List.mem_of_mem_drop hσ) v hvσ
    · exact hret v hvret
  exact hbody v hsub (hτsub v hc)

/-- **A witness, at the level of the specification, that the annotation is an instance of a scheme.**

    This predicate holds one existential: the annotation of the `.op` node is a true instance of a scheme
    of `pctx`, at some split point. It is the declarative form of the generator-internal `hEntry`. Each
    witness of the rename and of the decomposition is existentially bound, and an equation pins it.
    Therefore a caller gives only the *scheme*, the *split point* `k`, and the *matcher* `Sm`.

    **No part of the predicate names `Su`.** The matcher condition and the condition on the applied prefix
    both use the substitution `Sm` of the caller. Neither `unifyTypes`, nor its output `Su`, nor the
    sampled types of the generator occurs here. `isPolyApp_of_hasType_specShaped` bridges `Sm` to the `Su`
    of the unifier inside its own proof. It uses `extended_subst_prefix_of_determined` for the applied
    prefix, and `unifyTypes_matching_complete` with `extended_subst_guard2` for the suffix. Therefore
    nothing internal to the generator appears in this predicate, and a caller who reasons from the typing
    judgement can discharge each part.

    **The price is the determinacy of the split point.** A form that does not name `Su` must exclude the
    case of a *sample*. At a split point where a variable of the scheme is absent from the remaining
    suffix, the generator instantiates that variable by a random sample, and no hypothesis about `Sm` can
    force the sample to agree. The determinacy part of the predicate says that each variable of the prefix
    is also a variable of the suffix, and that is the exact restriction. It is a decidable property of the
    scheme and of the split point, so a caller settles it by `decide` or by `simp`. It always holds at
    `k = 0`, where the term applies no argument. It also holds at a full application whenever the result
    type of the scheme names each variable that its inputs name, as in
    `Sequence.append : ∀a. Seq a → Seq a → Seq a`. It fails exactly where a variable of the applied prefix
    is absent from the remaining suffix, as in `Sequence.length : ∀a. Seq a → int` at `k = 1`, which is
    where the generator picks the instance of that variable by a sample. For such a case, use the `hEntry`
    form, `genLExpr_complete_poly_specShaped`, which covers the case of a sample and takes a
    generator-internal premise. `extended_subst_prefix_of_determined` says what a proof needs to remove the
    restriction, which is a limit on the domain of `Su`.

    The intended way to discharge this predicate is from an `OpsConsistentR F e` of the caller, whose
    `.op_in` constructor holds exactly this witness. `schemeInstAt_of_opsConsistentR` in
    `HasTypeAGenOpsConsistent.lean` does that.

    **The well-formedness conditions for `freshenBoundVars` are not premises.** One condition says that
    each fresh bound variable is not free in `τ`, and the other says the same for the remaining arrow
    suffix. Both are consequences of `freshenBoundVars`, and `schemeInstAt_freshening_disjoint` derives
    them. In their place, this predicate takes the weaker structural condition `hclosed`: the body of the
    scheme names no type variable outside its own binders. -/
def SchemeInstAt (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (bctx : BVarCtx) (τ : LMonoTy) (name : String)
    (concreteArgTys : List LMonoTy) (maxNumArgs : Nat) : Prop :=
  ∃ (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (freshBoundVars : List TyIdentifier) (freshMonoTy : LMonoTy)
    (schemeArgTys : List LMonoTy) (retTy : LMonoTy) (k : Nat) (Sm : Lambda.Subst),
    (name, LTy.forAll boundVars monoTy) ∈ pctx ∧
    freshenBoundVars boundVars monoTy
      ((LMonoTy.freeVars τ ++ (generableTypesFromCtx bctx fctx octx).flatMap
        LMonoTy.freeVars).eraseDups) = (freshBoundVars, freshMonoTy) ∧
    decomposeArrow freshMonoTy = (schemeArgTys, retTy) ∧
    schemeArgTys.length ≤ maxNumArgs ∧
    k < schemeArgTys.length + 1 ∧
    -- **The closedness of the scheme.** The body of the scheme names no type variable outside its own
    -- binders. `schemeInstAt_freshening_disjoint` *derives* the two disjointness conditions from this
    -- one. Closedness is a property of the entry of `pctx`, and not of the generator. It holds for each
    -- real scheme, such as an entry of `corePolyOps` or of `factoryPolyOps`.
    (∀ v ∈ monoTy.freeVars, v ∈ boundVars) ∧
    -- The matcher, at the level of the specification. It does not name `Su`.
    LMonoTy.subst Sm
      ((schemeArgTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ ∧
    -- **The determinacy of the split point.** Each type variable of the applied prefix also occurs in
    -- the remaining suffix. Therefore the target type `τ` fixes the whole instance, and a random sample
    -- of the generator cannot disagree with `Sm`. `extended_subst_prefix_of_determined` says why this is
    -- the exact boundary of a predicate that does not name `Su`.
    (∀ σ ∈ schemeArgTys.take k, ∀ v ∈ σ.freeVars,
      v ∈ ((schemeArgTys.drop k).foldr
        (fun σ acc => LMonoTy.arrow σ acc) retTy).freeVars) ∧
    -- The applied prefix gives the argument types under the *same* matcher. This part names neither
    -- `unifyTypes` nor `Su`.
    concreteArgTys = (schemeArgTys.take k).map (LMonoTy.subst Sm)

/-- **The backward direction with no `hEntry`.**

    This theorem derives `IsPolyApp` from the typing judgement and a *witness at the level of the
    specification* that the annotation is an instance of a scheme. It takes no hypothesis about membership
    in `findPolymorphicOps`. The proof *builds* that membership with `findPolymorphicOps_complete`, and it
    discharges the two guards with `unifyTypes_matching_complete` and with `extended_subst_guard2`. The
    theorem covers both cases: the fully determined case, and the case of a sample, where a variable of
    the scheme is absent from the result suffix.

    The premises are three bundles at the level of the specification:
    - `hInst : SchemeInstAt …` is the witness for the instance of the scheme, which gives the scheme in
      `pctx`, the split point and the matcher `Sm`. It replaces the generator-internal `hEntry`. Each
      witness of the rename and of the decomposition is existentially bound inside it, and the matcher
      condition uses `Sm` only. The intended source of this premise is an `OpsConsistentR F e` of the
      caller.
    - `hgen` says that the list of generable types is not empty, which is a cheap fact about the context.
    - `hArgsComplete` is the bundle for the recursive completeness of each argument, as in
      `isPolyApp_of_hasType`. The premises `hAnnot` and `hArgLen` give the shape facts that the typing
      hypothesis forces. -/
theorem isPolyApp_of_hasType_specShaped
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (name : String) (annot : LMonoTy) (args : List LExpr')
    (hwt : HasTypeA' bctx (mkApps (.op () ⟨name, ()⟩ (some annot)) args) τ)
    (sampledTys : List LMonoTy) (concreteArgTys : List LMonoTy)
    (hLen : sampledTys.length = maxNumArgs)
    (hValid : ∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set))))
    (hAnnot : annot = concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
    (hArgLen : args.length = concreteArgTys.length)
    -- The depth budget is `depth - 1`, because each argument comes from the generator at the smaller
    -- index.
    (hArgsComplete : List.Forall₂
      (fun arg σ => (∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) ∧
        emptyNames arg ∧ allVarsInCtx fctx octx arg ∧
        AllTypesSimple tvars (depth - 1) bctx arg ∧ termDepth bctx arg ≤ depth - 1)
      args concreteArgTys)
    (hgen : generableTypesFromCtx bctx fctx octx ≠ [])
    (hInst : SchemeInstAt fctx octx pctx bctx τ name concreteArgTys maxNumArgs) :
    IsPolyApp fctx octx pctx tvars bctx depth τ maxNumArgs
      (mkApps (.op () ⟨name, ()⟩ (some annot)) args) := by
  obtain ⟨boundVars, monoTy, freshBoundVars, freshMonoTy, schemeArgTys, retTy, k, Sm,
    hmem, hfresh, hdec, harity, hk, hclosed, hmatch, hdet, hprefix⟩ := hInst
  -- The proof *derives* the two well-formedness conditions from the closedness of the scheme, and it
  -- does not assume them. `freshenBoundVars` cannot add a variable that is free in `τ`, because it gets a
  -- `varsInUse` set that holds each free variable of `τ`.
  obtain ⟨hdisjSuffix, hdisjBV⟩ :=
    schemeInstAt_freshening_disjoint fctx octx bctx τ boundVars monoTy freshBoundVars
      freshMonoTy schemeArgTys retTy k hclosed hfresh hdec
  -- Get the unifier from the matching-completeness theorem of Strata.
  obtain ⟨Su, hunify, _hSupat⟩ :=
    unifyTypes_matching_complete _ τ Sm hdisjSuffix hmatch
  -- Discharge `guard2` for the extension with the samples, through `extended_subst_guard2`.
  have hg2 : LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars Su).zip sampledTys) ++ Su)
      ((schemeArgTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ :=
    extended_subst_guard2 freshBoundVars Su sampledTys _ τ _hSupat hdisjBV
  -- Bridge the matcher `Sm` of the caller to the `Su` of the generator, on the applied prefix. The
  -- determinacy hypothesis `hdet` is what makes this step hold with no further condition.
  have hcat : concreteArgTys = (schemeArgTys.take k).map
      (LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars Su).zip sampledTys) ++ Su)) :=
    hprefix.trans (extended_subst_prefix_of_determined schemeArgTys retTy τ k Sm Su
      freshBoundVars sampledTys hdisjSuffix hmatch _hSupat hdet)
  -- Build the membership in `findPolymorphicOps`.
  have hEntry : (name, concreteArgTys) ∈ findPolymorphicOps pctx τ
      (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs :=
    findPolymorphicOps_complete pctx τ _ sampledTys name boundVars monoTy hmem
      freshBoundVars freshMonoTy schemeArgTys retTy Su concreteArgTys k maxNumArgs
      hfresh hdec harity hk hunify (Or.inr hgen) hg2 hcat
  -- Apply the backward direction in its `hEntry` form.
  exact isPolyApp_of_hasType fctx octx pctx tvars bctx depth τ name annot args hwt
    sampledTys concreteArgTys hLen hValid hEntry hAnnot hArgLen hArgsComplete

/-- The completeness of `genLExpr`. An expression is in the support if it satisfies the conditions for the
    completeness of `genLExprBase`, or if it is a valid application of a polymorphic operator, which
    `IsPolyApp` states.

    The first case also covers the monomorphic Indir rule. The application rule of `genLExprBase` reaches
    each such expression, because the Indir rule changes the distribution and not the support. -/
theorem genLExpr_complete (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (maxNumArgs : Nat)
    (e : LExpr')
    (he : (HasTypeA' bctx e τ ∧ emptyNames e ∧ allVarsInCtx fctx octx e ∧
            AllTypesSimple tvars depth bctx e ∧ termDepth bctx e ≤ depth)
          ∨ IsPolyApp fctx octx pctx tvars bctx depth τ maxNumArgs e) :
    e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs) := by
  simp only [SetGen.support]
  unfold genLExpr
  simp only [SetGen.mem_dite]
  -- `genLExprBase` has the weight 1 in the `frequency` of two elements. Both it and `genIndirPoly` are
  -- reachable in each branch of the `dite`. In the branch with monomorphic candidates, the proof gives the
  -- witness for the `frequency` through `mem_support_frequency_iff`. The base rule has the weight 1, and
  -- the `pick` between the two Indir rules has the weight 9.
  rcases he with ⟨hwt, hnames, hvars, hats, hdepth⟩ | ⟨sampledTys, name, concreteArgTys, args, hLen, hValid, hEntry, hArgs, rfl⟩
  · -- Case 1: route through genLExprBase (reachable in both dite branches)
    have hbase := genLExprBase_complete fctx octx pctx tvars bctx depth τ hτ e hwt hnames hvars hats hdepth
    by_cases hops : (findOpsInCtx octx τ).length > 0
    · refine Or.inl ⟨hops, ?_⟩
      rw [← mem_support_iff, mem_support_frequency_iff]
      exact ⟨1, _, List.mem_cons_self, by omega, hbase⟩
    · exact Or.inr ⟨hops, (pick_mem_iff _).mpr (Or.inl hbase)⟩
  · -- Case 2: route through genIndirPoly (reachable in both dite branches)
    -- The argument clause of `IsPolyApp` is about exactly the generator that `genLExpr` uses in the
    -- argument position at this depth. Therefore it *is* the witness for `genArg` that the completeness of
    -- `genIndirPoly` needs.
    have hindirpoly := genIndirPoly_complete fctx octx pctx tvars bctx depth τ
      maxNumArgs sampledTys hLen hValid name concreteArgTys hEntry _ args hArgs
    by_cases hops : (findOpsInCtx octx τ).length > 0
    · refine Or.inl ⟨hops, ?_⟩
      rw [← mem_support_iff, mem_support_frequency_iff]
      refine ⟨9, _, List.mem_cons_of_mem _ List.mem_cons_self, by omega, ?_⟩
      rw [mem_support_pick_iff]
      exact Or.inr hindirpoly
    · exact Or.inr ⟨hops, (pick_mem_iff _).mpr (Or.inr hindirpoly)⟩

/-- **The completeness of the polymorphic case, at the level of the specification.**

    This theorem restates `genLExpr_complete`. Its polymorphic case comes from the *typing judgement*
    `HasTypeA'`, and not from the generator-internal `IsPolyApp`. The polymorphic case has three premises:

    - `hwt` says that the term is a well-typed spine over an `.op` node of `pctx`.
    - `hEntry` is the side condition about unification at the split point.
    - The bundle for the recursive completeness of each argument.

    The proof *derives* `IsPolyApp` with `isPolyApp_of_hasType`, and it then applies `genLExpr_complete`.

    ### Which theorem to use

    This theorem and `genLExpr_complete_poly_fullySpecShaped` have the *same* conclusion, and they differ
    in one premise:

    | | this theorem | `…_fullySpecShaped` |
    |---|---|---|
    | premise about unification | `hEntry`, a membership in `findPolymorphicOps` | `hInst : SchemeInstAt …` and `hgen` |
    | that premise is | **internal to the generator** | at the level of the **specification** |

    Both proofs are free of `sorry`, and both need the same axioms. Strata proves the matching
    completeness of its unifier, which `…_fullySpecShaped` uses. The choice is therefore only about which
    premise you prefer to give.

    **Use this theorem when you can discharge `hEntry` yourself.** Membership in `findPolymorphicOps` is a
    decidable membership in a list, so `decide` or `simp [findPolymorphicOps]` proves it for a concrete
    context, target type and list of sampled types.

    **Use `…_fullySpecShaped` when you want no generator internals in the hypotheses.** That form is the
    honest statement that each well-typed spine is reachable. -/
theorem genLExpr_complete_poly_specShaped
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (name : String) (annot : LMonoTy) (args : List LExpr')
    (hwt : HasTypeA' bctx (mkApps (.op () ⟨name, ()⟩ (some annot)) args) τ)
    (sampledTys : List LMonoTy) (concreteArgTys : List LMonoTy)
    (hLen : sampledTys.length = maxNumArgs)
    (hValid : ∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set))))
    (hEntry : (name, concreteArgTys) ∈ findPolymorphicOps pctx τ
      (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs)
    (hAnnot : annot = concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
    (hArgLen : args.length = concreteArgTys.length)
    -- The depth budget is `depth - 1`, because each argument comes from the generator at the smaller
    -- index.
    (hArgsComplete : List.Forall₂
      (fun arg σ => (∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) ∧
        emptyNames arg ∧ allVarsInCtx fctx octx arg ∧
        AllTypesSimple tvars (depth - 1) bctx arg ∧ termDepth bctx arg ≤ depth - 1)
      args concreteArgTys) :
    (mkApps (.op () ⟨name, ()⟩ (some annot)) args)
      ∈ SetGen.support
        (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs) :=
  genLExpr_complete fctx octx pctx tvars bctx depth τ hτ maxNumArgs _
    (Or.inr (isPolyApp_of_hasType fctx octx pctx tvars bctx depth τ name annot args
      hwt sampledTys concreteArgTys hLen hValid hEntry hAnnot hArgLen hArgsComplete))

/-- **The completeness of the polymorphic case with no `hEntry`.**

    This theorem is like `genLExpr_complete_poly_specShaped`, and it takes no hypothesis about membership
    in `findPolymorphicOps`. In its place it takes the witness of `isPolyApp_of_hasType_specShaped`, at the
    level of the specification. This is the strongest form of the result: each well-typed spine over a
    scheme of `pctx` is reachable, if it satisfies the side conditions about recursive completeness and the
    closedness of the scheme, and no generator internal appears in the hypotheses. The proof *derives* the
    well-formedness conditions for `freshenBoundVars`, and it does not assume them. For the details, read
    `schemeInstAt_freshening_disjoint`.

    ### Which theorem to use

    This theorem and `genLExpr_complete_poly_specShaped` have the *same* conclusion, and they differ in one
    premise:

    | | this theorem | `…_specShaped` |
    |---|---|---|
    | premise about unification | `hInst : SchemeInstAt …` and `hgen` | `hEntry`, a membership in `findPolymorphicOps` |
    | that premise is | at the level of the **specification** | **internal to the generator** |
    | split points covered | the determined ones only | each one, including the case of a sample |

    Both proofs are free of `sorry`, and both need the same axioms. To remove `hEntry`, the proof *builds*
    that membership itself, and it therefore uses the matching completeness of the unifier of Strata. Strata
    proves that theorem, so it needs no further axiom.

    **Use this theorem for the honest statement at the level of the specification**, which names no
    `findPolymorphicOps` in its hypotheses.

    **Use `…_specShaped`** when you prefer to give `hEntry` yourself. It is a decidable membership in a
    list, so `decide` or `simp [findPolymorphicOps]` settles it for concrete arguments. It is also the route
    that reaches a split point where the generator takes a *sample*, which the determinacy condition of
    `SchemeInstAt` excludes.

    The intended source of `SchemeInstAt` is an `OpsConsistentR F e` of the caller, whose `.op_in`
    constructor holds exactly this witness. `schemeInstAt_of_opsConsistentR` performs that step, and
    `genLExpr_complete_poly_opsConsistentR` is this theorem with the premise already discharged. Both are
    in `HasTypeAGenOpsConsistent.lean`, where the `OpsConsistentR` judgement is available. -/
theorem genLExpr_complete_poly_fullySpecShaped
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (name : String) (annot : LMonoTy) (args : List LExpr')
    (hwt : HasTypeA' bctx (mkApps (.op () ⟨name, ()⟩ (some annot)) args) τ)
    (sampledTys : List LMonoTy) (concreteArgTys : List LMonoTy)
    (hLen : sampledTys.length = maxNumArgs)
    (hValid : ∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set))))
    (hAnnot : annot = concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
    (hArgLen : args.length = concreteArgTys.length)
    -- The depth budget is `depth - 1`, because each argument comes from the generator at the smaller
    -- index.
    (hArgsComplete : List.Forall₂
      (fun arg σ => (∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) ∧
        emptyNames arg ∧ allVarsInCtx fctx octx arg ∧
        AllTypesSimple tvars (depth - 1) bctx arg ∧ termDepth bctx arg ≤ depth - 1)
      args concreteArgTys)
    (hgen : generableTypesFromCtx bctx fctx octx ≠ [])
    (hInst : SchemeInstAt fctx octx pctx bctx τ name concreteArgTys maxNumArgs) :
    (mkApps (.op () ⟨name, ()⟩ (some annot)) args)
      ∈ SetGen.support
        (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs) :=
  genLExpr_complete fctx octx pctx tvars bctx depth τ hτ maxNumArgs _
    (Or.inr (isPolyApp_of_hasType_specShaped fctx octx pctx tvars bctx depth τ
      name annot args hwt sampledTys concreteArgTys hLen hValid hAnnot hArgLen
      hArgsComplete hgen hInst))


-- ── A polymorphic application at each position of a subterm ──────────
--
-- `IsPolyApp` describes a polymorphic application at the **root** of the generated term. Therefore
-- `genLExpr_complete`, whose polymorphic case is `IsPolyApp`, says nothing about such an application under
-- an `ite` arm or under a binder body. The results below state where the polymorphic case can appear.
--
-- The key step is `genLExprBase_complete_polyApp`, which says that a polymorphic application is in the
-- support of **`genLExprBase`** itself, and not only in the support of `genLExpr`. Each structural rule,
-- which is `ite`, `abs`, `quant` and `app`, recurses into `genLExprBase`. Therefore the polymorphic case
-- composes into each of those positions, and the three corollaries below give three of them.
--
-- Each statement below is at the `bool` target, where the list of branches is longest and the arithmetic
-- of the witness is hardest. The IndirPoly entry is the *last* element of the branch list of each type.
-- Therefore the other nine type cases differ only in the length of the `.tail` chain, which is the number
-- of `right` steps below, and nothing else in the argument changes.

open StrataGenerators.IndirSupport in
set_option maxHeartbeats 800000 in
/-- **The key step: a polymorphic factory application is in the support of `genLExprBase` itself.**

    The conclusion is about `genLExprBase … (n + 1) .bool`. Therefore it composes with each structural
    rule. Wherever `genLExprBase` recurses, which is an `ite` arm, an `abs` body, a `quant` body, and the
    function and the argument of an application, *this* result is available at that position.

    The premises are the premises for the completeness of `genIndirPoly`, with the argument generator fixed
    to `genLExprBase` at `n`, which is the generator that the branch uses. -/
theorem genLExprBase_complete_polyApp (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat)
    (sampledTys : List LMonoTy)
    (hSampledLen : sampledTys.length = 3)
    (hSampledValid : ∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set))))
    (name : String) (concreteArgTys : List LMonoTy)
    (hEntry : (name, concreteArgTys) ∈ findPolymorphicOps pctx .bool
      (generableTypesFromCtx bctx fctx octx) sampledTys 3)
    (args : List LExpr')
    (hArgs : List.Forall₂
      (fun arg σ => arg ∈ SetGen.support
        (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx n σ)) args concreteArgTys) :
    mkApps (.op () ⟨name, ()⟩
      (some (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) .bool))) args
      ∈ SetGen.support
        (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .bool) := by
  -- First, the term is in the support of `genIndirPolyCore`, at the argument generator that the branch
  -- gives.
  have hcore : mkApps (.op () ⟨name, ()⟩
      (some (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) LMonoTy.bool))) args
      ∈ SetGen.support (genIndirPolyCore (G := SetGen.Set) fctx octx pctx bctx .bool
          (genLExprBase fctx octx pctx tvars bctx n)
          (genLExprBase fctx octx pctx tvars bctx n .bool) 3) := by
    simp only [SetGen.support]
    unfold genIndirPolyCore
    simp only [SetGen.Set.mem_bind, SetGen.Set.mem_pure, SetGen.mem_dite]
    refine ⟨sampledTys, sampledTys_mem_support _ _ _ hSampledLen hSampledValid, ?_⟩
    left
    refine ⟨List.length_pos_of_mem hEntry, (name, concreteArgTys), ?_, args, ?_, rfl⟩
    · rw [← mem_support_iff, mem_support_elements_iff]; exact hEntry
    · rw [← mem_support_iff]
      exact (StrataGenerators.IndirSupport.mem_mapM_iff' _ concreteArgTys args).mpr hArgs
  -- Second, that branch is the last entry of the `frequency` list of `genLExprBase` at the `bool` target
  -- and the depth `n + 1`, with the weight 4. The witness must *name* the generator, because the
  -- membership goal alone does not determine a metavariable there.
  rw [norm_bool]
  simp only [genLExprBase]
  rw [mem_support_frequency_iff]
  refine ⟨4, fun () => genIndirPolyCore fctx octx pctx bctx LMonoTy.bool
    (genLExprBase fctx octx pctx tvars bctx n)
    (genLExprBase fctx octx pctx tvars bctx n LMonoTy.bool) 3, ?_, by omega, hcore⟩
  simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false]
  -- The IndirPoly entry is the last element of the list of eleven branches.
  right; right; right; right; right; right; right; right; right; right
  trivial

/-- **A polymorphic application under an `ite` arm.**

    This corollary joins `genLExprBase_complete_polyApp` with the structural `ite` rule, which draws both
    arms from `genLExprBase` at `n`. -/
theorem genLExprBase_polyApp_under_ite (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat)
    (c : LExpr') (hc : c ∈ SetGen.support
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx n .bool))
    (polyApp : LExpr')
    (hpoly : polyApp ∈ SetGen.support
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx n .bool))
    (elseArm : LExpr') (helse : elseArm ∈ SetGen.support
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx n .bool)) :
    (.ite () c polyApp elseArm : LExpr')
      ∈ SetGen.support
        (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .bool) := by
  rw [norm_bool]
  simp only [genLExprBase]
  rw [mem_support_frequency_iff]
  refine ⟨2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n LMonoTy.bool)
    (genLExprBase fctx octx pctx tvars bctx n LMonoTy.bool)
    (genLExprBase fctx octx pctx tvars bctx n LMonoTy.bool), ?_, by omega, ?_⟩
  · simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false]
    right; right; left; trivial
  · simp only [genIte, mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
    exact ⟨c, hc, polyApp, hpoly, elseArm, helse, rfl⟩

/-- **A polymorphic application under a `quant` body.**

    The `quant` rule generates its body with `genLExprBase` at `n`, in the *extended* binder context
    `τ' :: bctx`. Therefore `genLExprBase_complete_polyApp` applies there, with that extended context. -/
theorem genLExprBase_polyApp_under_quant (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat) (k : QuantifierKind)
    (τ' : LMonoTy)
    (hτ'gen : τ' ∈ SetGen.support
      (genGenerableTy (G := SetGen.Set) fctx octx tvars bctx n))
    (τ_tr : LMonoTy)
    (hτ_tr_gen : τ_tr ∈ SetGen.support
      (genGenerableTy (G := SetGen.Set) fctx octx tvars bctx n))
    (tr : LExpr') (htr : tr ∈ SetGen.support
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars (τ' :: bctx) n τ_tr))
    (body : LExpr') (hbody : body ∈ SetGen.support
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars (τ' :: bctx) n .bool)) :
    (.quant () k "" (some τ') tr body : LExpr')
      ∈ SetGen.support
        (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx (n + 1) .bool) := by
  rw [norm_bool]
  simp only [genLExprBase]
  rw [mem_support_frequency_iff]
  cases k with
  | all =>
    refine ⟨2, fun () => genQuant .all (genGenerableTy fctx octx tvars bctx n)
      (fun t => genLExprBase fctx octx pctx tvars (t :: bctx) n)
      (fun t => genLExprBase fctx octx pctx tvars (t :: bctx) n LMonoTy.bool), ?_, by omega, ?_⟩
    · simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false]
      right; right; right; right; left; trivial
    · simp only [genQuant, mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
      exact ⟨τ', hτ'gen, τ_tr, hτ_tr_gen, tr, htr, body, hbody, rfl⟩
  | exist =>
    refine ⟨2, fun () => genQuant .exist (genGenerableTy fctx octx tvars bctx n)
      (fun t => genLExprBase fctx octx pctx tvars (t :: bctx) n)
      (fun t => genLExprBase fctx octx pctx tvars (t :: bctx) n LMonoTy.bool), ?_, by omega, ?_⟩
    · simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false]
      right; right; right; right; right; left; trivial
    · simp only [genQuant, mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
      exact ⟨τ', hτ'gen, τ_tr, hτ_tr_gen, tr, htr, body, hbody, rfl⟩

-- ── Completeness with an existential depth ───────────────────────────
--
-- `genLExprBase_complete` and `genLExpr_complete` take an explicit `depth`, and their premise
-- `hdepth : termDepth bctx e ≤ depth` ties the caller to the fuel accounting of the generator. A caller
-- who only wants the statement "this well-typed term is reachable at some depth" should not have to
-- compute that value.
--
-- The corollaries below quantify the depth existentially. They are strictly weaker than the originals,
-- because `termDepth bctx e` is itself the witness. They are therefore corollaries, and not new
-- arguments.
--
-- These forms are useful because the companion bound of the depth-indexed statement is not tight. That
-- bound reads `termDepth e ≤ depthBudget K depth`, and not `≤ depth`, because a full application of an
-- operator of the arity `k` costs `k` levels of `termDepth`. Therefore `hdepth` is *sufficient* for
-- reachability, and it does not *describe* reachability. A statement that names no depth is free of that
-- constant, and also of each future change to `K`.
--
-- One premise is NOT dropped. `AllTypesSimple` is existentially quantified, and it is not removed. It
-- does not follow from `HasTypeA'`, because it also fixes the width of a bitvector, the alphabet of a
-- string, and the shape of a rational that the constant generators give. Only the *index* is existential.
--
-- The other direction admits no such treatment. An existential over the conclusion of the bound on the
-- depth, in the form `∃ d, termDepth bctx e ≤ d`, says nothing. It is `⟨termDepth bctx e, Nat.le_refl _⟩`
-- and it reads no part of the generator, so it holds for a term that no depth can give. The quantitative
-- link from the fuel to the output must stay indexed by the depth.

/-- The index of `AllTypesSimple` is an *upper* limit on the depth of each type in a term. Therefore a
    term that satisfies the predicate at the index `n` also satisfies it at `n + 1`. Each case is
    structural, and the only content is the arithmetic on the side conditions about `monoTyDepth`. -/
theorem allTypesSimple_mono (tvars : List TyIdentifier) (n : Nat) (bctx : BVarCtx)
    (e : LExpr') (h : AllTypesSimple tvars n bctx e) :
    AllTypesSimple tvars (n + 1) bctx e := by
  induction h with
  | boolConst => exact .boolConst
  | intConst => exact .intConst
  | strConst h => exact .strConst h
  | realConst r => exact .realConst r
  | bitvecConst w bv => exact .bitvecConst w bv
  | bvar => exact .bvar
  | fvar => exact .fvar
  | op => exact .op
  | abs hmem _ ih => exact .abs (genLMonoTy_mem_mono (Nat.le_succ _) hmem) ih
  | app τ' hwt hmem _ _ ih1 ih2 =>
      exact .app τ' hwt (genLMonoTy_mem_mono (Nat.le_succ _) hmem) ih1 ih2
  | ite _ _ _ ih1 ih2 ih3 => exact .ite ih1 ih2 ih3
  | eq τ' h1 h2 hmem _ _ ih1 ih2 =>
      exact .eq τ' h1 h2 (genLMonoTy_mem_mono (Nat.le_succ _) hmem) ih1 ih2
  | quant hmem τtr hmemtr hwt _ _ ih1 ih2 =>
      exact .quant (genLMonoTy_mem_mono (Nat.le_succ _) hmem) τtr
        (genLMonoTy_mem_mono (Nat.le_succ _) hmemtr) hwt ih1 ih2

/-- `AllTypesSimple` also holds at each larger index, by repeated use of `allTypesSimple_mono`. This is
    what lets one witness depth serve a whole term in the corollaries below. That witness is the maximum
    of the index for the depth of a type and the depth of the term. -/
theorem allTypesSimple_mono_le (tvars : List TyIdentifier) (m n : Nat) (bctx : BVarCtx)
    (e : LExpr') (hmn : m ≤ n) (h : AllTypesSimple tvars m bctx e) :
    AllTypesSimple tvars n bctx e := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · exact allTypesSimple_mono tvars k bctx e (ih (by omega))
    · rwa [(by omega : m = k + 1)] at h

/-- **Completeness of `genLExprBase` with an existential depth.** Each well-typed term whose annotations
    are simple at *some* index is reachable at *some* depth. The caller therefore computes no `termDepth`.

    The witness is `max m (termDepth bctx e)`. That value is large enough for the depth of the tree of the
    term, and `allTypesSimple_mono_le` makes it large enough for the index `m` of the annotations. -/
theorem genLExprBase_complete_exists (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (τ : LMonoTy)
    (hτ : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (e : LExpr')
    (hwt : HasTypeA' bctx e τ)
    (hnames : emptyNames e)
    (hvars : allVarsInCtx fctx octx e)
    (hats : ∃ m, AllTypesSimple tvars m bctx e) :
    ∃ depth, e ∈ SetGen.support
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth τ) := by
  obtain ⟨m, hm⟩ := hats
  refine ⟨max m (termDepth bctx e), ?_⟩
  exact genLExprBase_complete fctx octx pctx tvars bctx (max m (termDepth bctx e)) τ hτ e hwt
    hnames hvars (allTypesSimple_mono_le tvars m _ bctx e (by omega) hm) (by omega)

/-- **Completeness of `genLExpr` with an existential depth.** This corollary is the `genLExpr` form of
    `genLExprBase_complete_exists`, and it goes through the base case of `genLExpr_complete`.

    It lifts the base case only. The argument clause of `IsPolyApp` is about the generator that the depth
    selects, which is `genLExprBase` at the depth 0 at the floor and `genLExpr` at `n` above the floor. A
    larger `depth` therefore *changes which generator the clause names*, and it does not only relax a
    numeric bound. Monotonicity is therefore not free here, as it is for `AllTypesSimple` and for
    `termDepth`, and this corollary makes no claim about it. Such a claim needs its own lemma about the
    monotonicity of the support of `genLExpr`. For the polymorphic case, use
    `genLExprBase_complete_polyApp`, which places the application inside `genLExprBase` and therefore at
    each position of a subterm, or use one of the wrappers at the level of the specification. -/
theorem genLExpr_complete_exists (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (τ : LMonoTy)
    (hτ : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (maxNumArgs : Nat) (e : LExpr')
    (hwt : HasTypeA' bctx e τ)
    (hnames : emptyNames e)
    (hvars : allVarsInCtx fctx octx e)
    (hats : ∃ m, AllTypesSimple tvars m bctx e) :
    ∃ depth, e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs) := by
  obtain ⟨m, hm⟩ := hats
  refine ⟨max m (termDepth bctx e), ?_⟩
  exact genLExpr_complete fctx octx pctx tvars bctx (max m (termDepth bctx e)) τ hτ maxNumArgs e
    (Or.inl ⟨hwt, hnames, hvars,
      allTypesSimple_mono_le tvars m _ bctx e (by omega) hm, by omega⟩)
