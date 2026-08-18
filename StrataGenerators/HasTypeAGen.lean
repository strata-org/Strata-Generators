import StrataGenerators.SetGen
import StrataGenerators.HasTypeAGen.Core
import StrataGenerators.HasTypeAGen.IndirSupport
-- Coverage lemmas for `freshenBoundVars`, which include `freshenBoundVars_disjoint`.
-- `schemeInstAt_freshening_disjoint` below uses these lemmas. It *derives* the
-- well-formedness conditions that `SchemeInstAt` took as premises before, so callers
-- no longer supply them. This file imports only `HasTypeAGen.Core`, so there is no
-- cycle.
import StrataGenerators.HasTypeAGen.Freshening
import Strata.DL.Lambda.LTyUnify
-- `LTyUnifyProps` is imported for Strata's substitution lemmas. Note the unifier
-- results below are stated as *matching* completeness, not most-generality: nothing
-- here proves `Constraints.unify` returns a most general unifier, which is why the
-- substitution it returns is named `Su` rather than `mgu`. Imports cleanly (no
-- Mathlib/Batteries `List.Forall₂` clash — verified).
import Strata.DL.Lambda.LTyUnifyProps
-- NOTE: `Batteries.Data.List.Basic` intentionally NOT imported here. It defines
-- its own `List.Forall₂`, which clashes with Strata's now-public `List.Forall₂`
-- (`Strata.DL.Util.List`, reached transitively via `LTyUnify`) on the generated
-- `List.Forall₂.below.casesOn` symbol. The `List` lemmas this file uses
-- (`mem_cons`, `length_pos_of_mem`, …) are available transitively via Strata / Lean core.

-- Mathlib registers Nat.le_refl with @[refl]
-- Adding this annotation avoids us needing to depend on Mathlib
attribute [refl] Nat.le_refl

open Lambda RandomChoice ArbNat ArbChar ArbString SetGen

/-!
# Generator of well-typed terms satisfying `HasTypeA`

A Basalt `SetGen`-based random generator for well-typed Strata `LExpr`s
that satisfy the `HasTypeA` relation.
We work with the `LExprParams` instantiation `LExprParams.mono ⟨Unit, Unit⟩` (unit
metadata and identifier-metadata, monotype annotations).

## Contents

- `HasTypeA'` — the typing judgement `HasTypeA`, with `LExprParams` instantiated
- `genLMonoTy` — generates mono-types (bool, int, arrow)
- `genLMonoTy_mem_*` — lemmas about the types that `genLMonoTy` can generate
- `genLExpr` — generates well-typed `LExpr`s for a given type and depth budget
- Soundness of `genLExpr` (every generated expression is well-typed)
- `SetGen.IsSoundAndComplete` instance for `genLMonoTy`
-/

-- ── bvarsOfType spec ──────────────────────────────────────────────────

/-- Characterization of `bvarsOfType.go`: index `i` is in the result iff
    it corresponds to a position in `bctx` with type `τ`, offset by `base`. -/
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

/-- Support characterization of `pickBVar`: an expression is in the support iff it's
    `.bvar () i` for some `i ∈ bvarsOfType bctx τ`. -/
private theorem mem_support_pickBVar_iff {bctx : BVarCtx} {τ : LMonoTy}
    {hv : (bvarsOfType bctx τ).length > 0} {e : LExpr'} :
    e ∈ (pickBVar (G := SetGen.Set) bctx τ hv) ↔
      ∃ i ∈ bvarsOfType bctx τ, e = .bvar () i := by
  change e ∈ SetGen.support (pickBVar (G := SetGen.Set) bctx τ hv) ↔ _
  simp only [pickBVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos hv), List.mem_map]
  constructor
  · rintro ⟨i, hmem, rfl⟩; exact ⟨i, hmem, rfl⟩
  · rintro ⟨i, hmem, rfl⟩; exact ⟨i, hmem, rfl⟩

/-- Support characterization of `pickFVar`: an expression is in the support iff it's
    `.fvar () ⟨name, ()⟩ (some τ)` for some `name ∈ fvarsOfType fctx τ`. -/
private theorem mem_support_pickFVar_iff {fctx : FVarCtx} {τ : LMonoTy}
    {hv : (fvarsOfType fctx τ).length > 0} {e : LExpr'} :
    e ∈ (pickFVar (G := SetGen.Set) fctx τ hv) ↔
      ∃ name ∈ fvarsOfType fctx τ, e = .fvar () ⟨name, ()⟩ (some τ) := by
  change e ∈ SetGen.support (pickFVar (G := SetGen.Set) fctx τ hv) ↔ _
  simp only [pickFVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos hv), List.mem_map]
  constructor
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩

/-- Support characterization of `pickOp`: an expression is in the support iff it's
    `.op () ⟨name, ()⟩ (some τ)` for some `name ∈ opsOfType octx τ`. -/
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

/-- Raw-membership (non-`support`-wrapped) characterization of `oneOf`, mirroring
    `pick_mem_iff`. Since `support` is the identity on `Set`, this coincides with
    `mem_support_oneOf_iff` and lets `simp` unfold `oneOf` even after the ambient
    `support` wrapper has already been stripped by `mem_support_iff`. -/
@[simp] theorem mem_oneOf_iff {gs : List (Unit → Set α)} (hne : gs ≠ []) (a : α) :
    a ∈ (oneOf gs hne : Set α) ↔ ∃ g ∈ gs, a ∈ g () :=
  mem_support_oneOf_iff hne

end SetGen

-- ── genLMonoTy support ────────────────────────────────────────────────

/-- All ftvar names in a type belong to `tvars`. -/
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

/-- Every type in the support of `pickBitvecWidth` is `.bitvec n` for some width
    `n`. Widths are unconstrained. -/
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

-- ── Structural facts about `inGenLMonoTySupport` ─────────────────────
-- `inGenLMonoTySupport tvars n τ = true` is the decidable statement "`τ` is
-- generable at depth ≤ `n`, and `tvars` holds all of its ftvars". Therefore it
-- gives the depth bound and the ftvar condition, and it is
-- monotone in the depth index. Each is proved by following the shape of the
-- `inGenLMonoTySupport` definition itself (`fun_induction`, or structural
-- recursion on `τ`), because `monoTyDepth`/`inGenLMonoTySupport` do not reduce on a
-- `tcons` with a variable head.

/-- `inGenLMonoTySupport` at index `n` bounds `monoTyDepth` by `n`. -/
theorem inGenLMonoTySupport_depth (tvars : List TyIdentifier) (n : Nat) (τ : LMonoTy)
    (h : inGenLMonoTySupport tvars n τ = true) : monoTyDepth τ ≤ n := by
  fun_induction inGenLMonoTySupport tvars n τ <;>
    simp_all [monoTyDepth] <;> omega

/-- `inGenLMonoTySupport` implies every ftvar name is declared in `tvars`. -/
theorem inGenLMonoTySupport_ftvars (tvars : List TyIdentifier) (n : Nat) (τ : LMonoTy)
    (h : inGenLMonoTySupport tvars n τ = true) : allFtvarsIn tvars τ := by
  fun_induction inGenLMonoTySupport tvars n τ <;>
    simp_all [allFtvarsIn, nullaryBaseTypeNames]

/-- `inGenLMonoTySupport` is monotone in the depth index. -/
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


/-- Characterization of `pickBaseType` support: produces exactly
    `bool`, `int`, `string`, `real`, `regex`, and `bitvec n` for any width `n`. -/
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

/-- Full support characterization of `genLMonoTy`: membership is decided by the
    Boolean `inGenLMonoTySupport` (simple structure, depth ≤ `n`, ftvars ⊆ `tvars`). -/
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


-- ── Generable types: `∃ m, τ ∈ support (genLMonoTy tvars m)` ─────────
--
-- The proofs below index many statements by "`genLMonoTy tvars` can produce `τ` at
-- some fuel". Such a `τ` is built from the base types, a `bitvec` of any width,
-- `arrow`/`Map`/`Sequence`, and `ftvar`s that come from `tvars`. The statement is
-- written out at each use, and not behind a definition.
--
-- The existential over the fuel is necessary. The term generator can pass a target
-- type to itself at a fuel below the depth of the type: an `app` at fuel `n+1`
-- recurses on a function of type `τ' → τ` at fuel `n`, and `τ' → τ` can have depth
-- `n+1`. Therefore a statement that pins the fuel is false for that recursion.
--
-- The intro, inversion, and eliminator lemmas for this statement are below. Their
-- names start with `genLMonoTy_mem_`.

/-- Depth-monotonicity of `genLMonoTy`'s support: a type generable at fuel `m` is
    generable at any larger fuel. -/
theorem genLMonoTy_mem_mono {tvars : List TyIdentifier} {m m' : Nat} {τ : LMonoTy}
    (hle : m ≤ m') (h : τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m') := by
  rw [genLMonoTy_support] at h ⊢
  exact inGenLMonoTySupport_mono tvars m m' τ hle h

/-- The fuel witnessed by `genLMonoTy` membership bounds `monoTyDepth`. -/
theorem genLMonoTy_mem_depth {tvars : List TyIdentifier} {m : Nat} {τ : LMonoTy}
    (h : τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    monoTyDepth τ ≤ m :=
  inGenLMonoTySupport_depth tvars m τ ((genLMonoTy_support tvars m τ).mp h)

/-- Every ftvar name of a generable type is declared in `tvars`. -/
theorem genLMonoTy_mem_ftvars {tvars : List TyIdentifier} {m : Nat} {τ : LMonoTy}
    (h : τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    allFtvarsIn tvars τ :=
  inGenLMonoTySupport_ftvars tvars m τ ((genLMonoTy_support tvars m τ).mp h)

-- Intro lemmas, one for each shape of generable type. `tvars` (and `w`) are
-- implicit, so a proof can apply them without an explicit argument.

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

/-- **Induction principle for a generable type.** Apply it with
    `refine genLMonoTy_mem_rec (motive := …) ?bool … ?seq h`, and then give each case.
    Proved by structural recursion on `τ`, which follows the shape of
    `inGenLMonoTySupport`. -/
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


/-- **Case-analysis principle for a generable type.** The same shape as
    `genLMonoTy_mem_rec`, but with no induction hypothesis.
    Because it has no `tcons` or datatype case, a structural match on a generable type
    needs no catch-all arm. -/
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

/-- **Support of `genGenerableTy` is exactly that of `genLMonoTy`.**

    This is what makes the context-aware type selection a drop-in replacement in
    the proofs. `genGenerableTy` is a `frequency` whose branches are (a) `elements`
    over the context-derived types *filtered* by `inGenLMonoTySupport tvars n`, and (b)
    `genLMonoTy tvars n` itself. Support of a `frequency` is the union of its
    positive-weight branches' supports, branch (a) ⊆ branch (b) by
    `inGenLMonoTySupport_sound`, and branch (b) is retained — so the union collapses to
    `genLMonoTy`'s support. Only the *distribution* changes, not the support. -/
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

/-- **Support of `genAppArgTy` is exactly that of `genLMonoTy`.**

    Same drop-in argument as `genGenerableTy_support`, one level further: the
    filtered branch draws argument types `σ` of *generable function types*
    `σ → τ` (so that both positions of an application are inhabitable), each of
    which passed `inGenLMonoTySupport tvars n` and is therefore in `genLMonoTy`'s
    support; the retained `genLMonoTy` branch supplies the converse; and the
    fallback branch reduces to `genGenerableTy_support`. -/
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

-- `LMonoTy.bool`, `.int`, `.arrow` are abbreviations for `.tcons "bool" []` etc.
-- In Strata, they're defined as abbreviations via the `abbrev` keyword,
-- e.g. `abbrev LMonoTy.arrow τ₁ τ₂ := .tcons "arrow" [τ₁, τ₂]`.
-- Now, when we define `genLExpr` via pattern-matching,
-- Lean's automatically generated equational lemmas are defined in terms of the expanded constructor,
-- i.e. `LmonoTy.tcons "arrow" [τ₁, τ₂]` instead of `LMonoTy.arrow τ₁ τ₂`.
-- Thus, when we have a hypothesis that mentions `genLExpr`, e.g. `he : e ∈ support (genLExpr fctx octx tvars bctx 0 (LMonoTy.arrow τ₁ τ₂))`,
-- when we try to naively do `simp only [genLExpr]`,
-- Lean tries to match `LMonoTy.tcons "arrow" [τ₁, τ₂]` against the subterm `LMonoTy.arrow τ₁ τ₂` in the hypothesis.
-- Even though the two terms are definitionally equal, the `simp/rw` tactics require syntactic equality,
-- so we have to add the following rewrite lemmas which normalize the abbreviation,
-- so that the equation lemmas can match.
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
/-- Every expression in the support of `genLExpr fctx octx tvars bctx depth τ` is
    well-typed. With the unhandled-type fallback producing the empty generator
    (`default = ∅`), this holds for ALL `τ`, and not only for generable ones: at a
    type the generator does not handle, the support is empty, so the claim is
    vacuous. -/
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
    -- Indir branch: the operator spine is well-typed because the op node
    -- types at its annotation and every argument comes from `genLExprBase … n`,
    -- whose soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the fallback also handled by the
    -- recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx m σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx m _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
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
    -- Indir branch: the spine is well-typed because the op node types at
    -- its annotation and each argument comes from `genLExprBase … n`, whose
    -- soundness is this theorem's own recursive call.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_hasType octx bctx _ _
          (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_sound fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, with the no-candidate fallback likewise
    -- discharged by the recursive call.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx _ _ _ _
        (fun σ a ha => genLExprBase_sound fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx n _ a ha) e he
  case h_21 =>
    -- Other type constructors (datatypes, abstract types, aliases). The branch is
    -- the three context leaves — bvar / fvar / nullary op of type `τ` — exactly as
    -- the *depth-0* `.regex` case (`h_15`), so the same `pick*_sound` lemmas
    -- discharge it. Each leaf carries the annotation `τ`, so it is well-typed at `τ`.
    -- (The `n + 1` regex arm `h_16` is no longer an analogue: every named
    -- `n + 1` case has Indir/IndirPoly branches. This case stays leaf-only at both
    -- depths, which is what keeps the discharge non-inductive.)
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

-- ── Nat.arbitrary support for SetGen.Set ──────────────────────────────
-- (`Nat_arbitrary_support_set` is defined earlier, alongside `pickBitvecWidth`,
-- which now draws its width from `Nat.arbitrary`.)

/-- Every integer is reachable via `pick` between `(k : Int)` and `-(k+1)`. -/
private theorem Int_cover (z : Int) :
    (∃ k : Nat, k ∈ SetGen.support (Nat.arbitrary (G := SetGen.Set)) ∧ (↑k : Int) = z) ∨
    (∃ k : Nat, k ∈ SetGen.support (Nat.arbitrary (G := SetGen.Set)) ∧ (-(↑k + 1 : Int)) = z) := by
  cases z with
  | ofNat n => left; exact ⟨n, Nat_arbitrary_support_set n, rfl⟩
  | negSucc n => right; exact ⟨n, Nat_arbitrary_support_set n, by simp [Int.negSucc_eq]⟩

-- These support lemmas mirror those in `Basalt.Examples.ArbString`
-- (`Char.arbitrary_support`, `genCharList_support`, `String.arbitrary_support`)
-- but are restated for `SetGen.Set` rather than `SPMF`.

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

-- ── Support lemmas for the adversarial primitive generators ────────────
-- `genStrConst` and `genBitvecConst` draw from `StrataGenerators.PrimitiveGens`,
-- which gives non-ASCII strings and boundary-biased bitvectors. Thus the
-- SMT-agreement property can reach the cases about bitvector overflow, and about
-- strings and UTF-8. These lemmas mirror the `Char_arbitrary` and
-- `String_arbitrary` lemmas above, with `interestingChars` in the place of
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
/-- Each string over `interestingChars` is in the support of
    `genInterestingString`, at **any** length, and this includes `""`.

    The `listOf` tail with weight 1 is the witness, and this lemma is why that
    branch exists. The primary branch limits the length to `strMaxLen`. Therefore
    that branch alone makes this lemma false, and it forces a bound on length into
    `AllTypesSimple.strConst`. -/
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
/-- Each natural number is in the support of `natArbGeom`. `natArbGeom` is the
    geometric generator, a `pick` between `0` and `(· + 1)`, that supports the
    completeness tail of `genRat`. -/
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

    The unbounded tail branch gives this result. The bounded branch samples
    uniformly from a window, which is why about 1.5% of its draws are `0`, and not
    the about 46% that a draw from `Nat.arbitrary` gives. But a window alone is not
    complete. The tail reaches each `r` through
    `Rat.mkRat_self : mkRat r.num r.den = r`. The proof splits on the sign of
    `r.num`, so a negative rational outside the window is also reachable. -/
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

/-- Each `n` in `[lo, hi]` is in the support of `chooseNat lo hi` at `SetGen.Set`.
    This lemma is the `SetGen` analogue of `SPMF.mem_support_chooseNat_iff` from
    Basalt. It proves only the direction that the lemmas below need, which is from
    membership in the list to membership in the support. -/
private theorem chooseNat_support_set {lo hi n : Nat} (h : lo ≤ hi)
    (hn : lo ≤ n ∧ n ≤ hi) :
    n ∈ SetGen.support (chooseNat (G := SetGen.Set) lo hi h) := by
  simp only [chooseNat, SetGen.mem_support_map_iff]
  exact ⟨ULift.up ⟨n, hn⟩, by simp [hn], rfl⟩

open StrataGenerators.PrimitiveGens in
/-- **Each** `BitVec w` is in the support of `genBiasedBitVec w`.

    The uniform fallback branch in `genBiasedBitVec` gives this result. The boundary
    pool is a *bias*, and not a restriction, so the generator stays complete. The
    witness is the second branch, which has weight 1, at `k = bv.toNat`. That value
    is in range, because `2^w` bounds `BitVec.toNat`, by `bv.isLt`. This is exactly
    why the upper bound of the fallback must be `2^w - 1`, and nothing smaller. A
    tighter bound leaves most values of `bv` without a witness. -/
private theorem genBiasedBitVec_support_set {w : Nat} (bv : BitVec w) :
    bv ∈ SetGen.support (genBiasedBitVec (G := SetGen.Set) w) := by
  rw [genBiasedBitVec, mem_support_frequency_iff]
  refine ⟨1, fun _ => BitVec.ofNat w <$> chooseNat 0 (2 ^ w - 1) (Nat.zero_le _),
    by simp, Nat.one_pos, ?_⟩
  rw [mem_support_map_iff]
  refine ⟨bv.toNat, chooseNat_support_set _ ⟨Nat.zero_le _, ?_⟩, by simp⟩
  exact Nat.le_sub_one_of_lt bv.isLt

-- ── emptyNames predicate ──────────────────────────────────────────────

/-- All binder names in the expression are empty strings. -/
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

/-- The tree depth of a term: the minimum `depth` parameter for which
    `genLExpr` can produce the term. This coincides with the generator's
    fuel consumption because:
    - Leaf expressions (bvar, fvar, op, const) have depth 0.
    - Each compound constructor (abs, app, ite, eq, quant) adds 1.
    - The generator recurses at `depth - 1` for each child.
    - The `quant` case also incorporates `monoTyDepth τ` since the generator
      calls `genLMonoTy (depth - 1)` which requires `monoTyDepth τ ≤ depth - 1`. -/
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

/-- All type annotations occurring in an expression are simple, have depth bounded
    appropriately, and have all ftvar names drawn from `tvars`.
    The `n` parameter decreases by 1 at each compound expression level,
    matching the generator's fuel consumption. At level `n+1`, intermediate types
    produced by `genLMonoTy n` have depth ≤ `n`, and sub-expressions need `AllTypesSimple n`. -/
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
/-- The `termDepth` of an application spine: one level per argument, over the
    maximum of the head's and the arguments' own depths.

    This is the fact that forces `genLExprBase_termDepth_bound`'s statement to
    change (see the comment on that theorem): a fully-applied operator
    of arity `k` costs `k` levels of `termDepth`, not one. -/
theorem termDepth_mkApps_le (bctx : BVarCtx) (base : LExpr') (args : List LExpr')
    (d : Nat) (hbase : termDepth bctx base ≤ d)
    (hargs : ∀ a ∈ args, termDepth bctx a ≤ d) :
    termDepth bctx (mkApps base args) ≤ d + args.length := by
  -- Induct on `args`, generalizing both the head *and* the bound: after consuming
  -- one argument the head is `.app base a` at bound `d + 1`, while the remaining
  -- arguments are still bounded by `d ≤ d + 1`.
  induction args generalizing base d with
  | nil => simpa [mkApps] using hbase
  | cons a rest ih =>
    have hstep : termDepth bctx (LExpr.app () base a) ≤ d + 1 := by
      show max (termDepth bctx base) (termDepth bctx a) + 1 ≤ d + 1
      have := hargs a (by simp)
      omega
    have hrest : ∀ x ∈ rest, termDepth bctx x ≤ d + 1 :=
      fun x hx => Nat.le_trans (hargs x (by simp [hx])) (by omega)
    -- `mkApps base (a :: rest) = mkApps (.app base a) rest` by `foldl_cons`; rewrite
    -- with that identity rather than unfolding `mkApps`, so the recursive call's
    -- conclusion is *syntactically* about the same term.
    have hfold : mkApps base (a :: rest) = mkApps (LExpr.app () base a) rest := by
      simp only [mkApps, List.foldl_cons]
    rw [hfold, List.length_cons]
    have hih := ih (LExpr.app () base a) (d + 1) hstep hrest
    -- `hih : … ≤ (d + 1) + rest.length`; the goal is `… ≤ d + (rest.length + 1)`.
    omega

open StrataGenerators.IndirSupport in
/-- The depth budget the merged generator needs at index `depth`, given that each
    level may emit an application spine of arity up to `K`. -/
abbrev genDepthBudget (K depth : Nat) : Nat := depthBudget K depth

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
open StrataGenerators.IndirSupport in
/-- Every expression in the support of `genLExprBase` at depth `depth` has
    `termDepth` bounded by `depthBudget K depth`, where
    `K = max (opCtxArity octx) maxNumArgs` (at least 1) is the largest arity any
    single level can emit.

    ## Why the bound is `depthBudget K depth` and not `depth`

    Formerly this theorem read `termDepth bctx e ≤ depth`, and that was correct
    because every `genLExprBase` branch emitted exactly one constructor per level.
    Folding the Indir/IndirPoly rules into `genLExprBase` breaks it — and breaks it
    *semantically*, not just in the proof:

    `termDepth` charges **one level per `app` node** (`termDepth (.app f a) =
    max … + 1`), so a fully-applied operator of arity `k` is a spine of `k` nested
    `app` nodes and costs `k`. At `depth = 1` the new Indir branch can emit
    `Int.Add #1 #2` — two leaf arguments from `genLExprBase … 0` — whose
    `termDepth` is `2 > 1`. So the old statement is **false** for the merged
    generator, and re-proving it is not an option; it has to be restated.

    `depthBudget K depth` (`= depth * K`, written recursively to keep the proof's
    arithmetic linear) is the honest replacement: each of the `depth` levels may
    spend up to `K` on a spine. The arity ceilings are real —
    `findOpsInCtx_length_le` bounds the monomorphic rule by `opCtxArity octx`
    (derived from the context's own arrow nesting) and
    `findPolymorphicOps_length_le` bounds the polymorphic rule by `maxNumArgs`
    (`findPolymorphicOps` skips wider schemes outright).

    For the concrete `corePartialOps`/`corePolyOps` vocabularies `K = 3`, so a
    depth-3 draw is bounded by 9 rather than 3.

    ### Consequence for `genLExprBase_complete`

    `genLExprBase_complete`'s `hdepth : termDepth bctx e ≤ depth` precondition is
    **unchanged**, and remains sufficient: it characterizes the terms the
    *structural* rules reach. What is no longer true is the old converse reading —
    that `hdepth` exactly characterizes reachability. The support is now strictly
    larger than `{e | termDepth e ≤ depth}`, so completeness stays a genuine
    one-directional statement and this theorem is its (weaker) companion bound. -/
theorem genLExprBase_termDepth_bound (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx)
    (depth : Nat) (K : Nat)
    (hK : 1 ≤ K) (hKops : opCtxArity octx ≤ K) (hKpoly : 3 ≤ K)
    -- The Indir rules' argument types must be generable, at every target type: the
    -- recursion bounds an argument's depth by applying this theorem at that argument's
    -- type, and this theorem is indexed by generability.
    --
    -- This is a side condition, and not a theorem. `findOpsInCtx` reads argument types
    -- straight off the arrow types of `octx`, and `findPolymorphicOps` makes them when
    -- it substitutes sampled types into a scheme. Nothing in the generator holds either
    -- one to a generable type. Therefore an unusual `octx` entry (for example, a
    -- `tcons "Foo"` that the generator does not handle) can make the rules ask for an
    -- argument type that is not generable. For `coreMonoOps` and `corePolyOps` the
    -- condition is cheap to discharge, because all of their argument types are built
    -- from `int`/`bool`/`string`/`real`/`regex`/`Sequence`/`Map`/arrows.
    --
    -- Quantified over the binder context `bc` as well as the target type `σ`:
    -- `abs`/`quant` branches recurse under an extended binder context, and `bc` feeds
    -- `generableTypesFromCtx`, hence the polymorphic rule's sampled types.
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

      -- Five residual goals: the three leaf `pick*` branches plus the
      -- Indir and IndirPoly branches. They are dispatched by a `first`-combinator
      -- rather than positional bullets, because the goal order varies by type case
      -- and a positional script silently mis-assigns them.
      all_goals (
        first
        | (rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
           · first
             | (rw [mem_support_pickBVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
             | (rw [mem_support_pickFVar_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
             | (rw [mem_support_pickOp_iff] at h; obtain ⟨_, _, rfl⟩ := h; simp [termDepth])
           all_goals simp [termDepth])
        -- Indir / IndirPoly branches: each emits an application spine, costing
        -- one `termDepth` level per argument on top of the argument depth at `n`. The
        -- arity ceilings (`opCtxArity octx ≤ K` for the monomorphic rule, `3 ≤ K` for
        -- `maxNumArgs`) are what let a spine fit inside one `K`-sized budget level.
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
        -- IndirPoly. The `refine`/`exact` pair is given twice, once behind a
        -- `mem_support_iff` normalization step: in some type cases the per-branch
        -- `simp only` above already unfolded `he` to `support …`, in others it left
        -- `e ∈ g ()`, and `simp only` errors rather than no-ops when it has nothing
        -- to rewrite.
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
        -- Indir / IndirPoly branches: each emits an application spine, costing
        -- one `termDepth` level per argument on top of the argument depth at `n`. The
        -- arity ceilings (`opCtxArity octx ≤ K` monomorphically, `3 ≤ K` for
        -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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
        -- Indir / IndirPoly branches: each emits an application spine, costing
        -- one `termDepth` level per argument on top of the argument depth at `n`. The
        -- arity ceilings (`opCtxArity octx ≤ K` monomorphically, `3 ≤ K` for
        -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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
        -- Indir / IndirPoly branches: each emits an application spine, costing
        -- one `termDepth` level per argument on top of the argument depth at `n`. The
        -- arity ceilings (`opCtxArity octx ≤ K` monomorphically, `3 ≤ K` for
        -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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
        -- Indir / IndirPoly branches: each emits an application spine, costing
        -- one `termDepth` level per argument on top of the argument depth at `n`. The
        -- arity ceilings (`opCtxArity octx ≤ K` monomorphically, `3 ≤ K` for
        -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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
        -- Indir / IndirPoly branches: each emits an application spine, costing
        -- one `termDepth` level per argument on top of the argument depth at `n`. The
        -- arity ceilings (`opCtxArity octx ≤ K` monomorphically, `3 ≤ K` for
        -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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
      -- Indir / IndirPoly branches: each emits an application spine, costing
      -- one `termDepth` level per argument on top of the argument depth at `n`. The
      -- arity ceilings (`opCtxArity octx ≤ K` monomorphically, `3 ≤ K` for
      -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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
      -- Indir / IndirPoly branches: each emits an application spine, costing
      -- one `termDepth` level per argument on top of the argument depth at `n`. The
      -- arity ceilings (`opCtxArity octx ≤ K` monomorphically, `3 ≤ K` for
      -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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
      -- Indir / IndirPoly branches: each emits an application spine, costing
      -- one `termDepth` level per argument on top of the argument depth at `n`. The
      -- arity ceilings (`opCtxArity octx ≤ K` monomorphically, `3 ≤ K` for
      -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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
      -- Indir / IndirPoly branches: each emits an application spine, costing
      -- one `termDepth` level per argument on top of the argument depth at `n`. The
      -- arity ceilings (`opCtxArity octx ≤ K` for the monomorphic rule, `3 ≤ K` for
      -- `maxNumArgs`) are what let a whole spine fit in one `K`-sized budget level.
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

/-- Inversion lemma: if `.eq () e₁ e₂` has type `τ`, then `τ = .bool`. -/
private theorem eq_hasType_bool {bctx : BVarCtx} {τ : LMonoTy} {e₁ e₂ : LExpr'}
    (h : HasTypeA' bctx (.eq () e₁ e₂) τ) : τ = .bool := by cases h with | eq _ _ => rfl

/-- Inversion lemma: if `.quant () k name (some qty) tr body` has type `τ`, then `τ = .bool`. -/
private theorem quant_hasType_bool {bctx : BVarCtx} {τ : LMonoTy} {k name qty tr body}
    (h : HasTypeA' bctx (.quant () k name (some qty) tr body) τ) : τ = .bool := by
  cases h with | quant _ _ => rfl

/-- Predicate asserting that all fvar names in the expression are in `fctx`
    (with the correct type) and all op names are in the factory `F`. -/
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
/-- Completeness of `genLExpr`: every well-typed expression whose `termDepth`
    fits within the depth budget is in the support. The `hdepth` precondition
    is tight: the generator provably never produces
    terms exceeding the depth budget (see `genLExprBase_termDepth_bound`),
    so this precondition exactly characterizes reachability. -/
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

/-- `genLMonoTy tvars n` is sound and complete with respect to the decidable
    filter `inGenLMonoTySupport tvars n`. -/
instance {tvars : List TyIdentifier} {n : Nat} :
    SetGen.IsSoundAndComplete
      (genLMonoTy (G := SetGen.Set) tvars n)
      (fun τ => inGenLMonoTySupport tvars n τ = true) where
  support_iff τ := genLMonoTy_support tvars n τ

-- ── Quick test ────────────────────────────────────────────────────────

-- We need this `ToFormat` instance in order to pretty-print the generated `LExpr`s
-- before (since our metadata type is `Unit`)
open Std in
instance : ToFormat Unit where
  format _ := .nil

-- Print 5 randomly generated expressions
-- Some example generated exprs:
-- (if (if #true then #true else #true) then #true else #true)
-- ((λ (bvar:bool) #true) ((λ (bvar:bool) %0) #true))
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  IO.println <| Std.format (← genClosedLExpr [] 3) |>.pretty : IO Unit)

-- Test with a bound variable of type `ftvar "a"` to exercise the ftvar case
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  IO.println <| Std.format (← genLExpr [] [] [] ["a"] [.ftvar "a"] 3 (.ftvar "a")) |>.pretty : IO Unit)

-- Test with polymorphic operators (IndirPoly rule)
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

/-- If `argsForResult fullTy τ = some args`, then
    `fullTy = args.foldr (fun σ acc => .arrow σ acc) τ`. -/
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

/-- Helper: `mkApps` preserves typing via iterated `app` rule. -/
theorem mkApps_hasType (bctx : BVarCtx) (base : LExpr') (args : List LExpr')
    (argTys : List LMonoTy) (τ : LMonoTy)
    (hbase : HasTypeA' bctx base (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))
    (hargs : List.Forall₂ (HasTypeA' bctx) args argTys) :
    HasTypeA' bctx (mkApps base args) τ := by
  induction hargs generalizing base with
  | nil => exact hbase
  | cons harg _ ih => exact ih _ (LExpr.HasTypeA.app hbase harg)

-- **Matching-completeness of `Constraints.unify` now comes from upstream.** This repo used
-- to state `Constraints_unify_matching_complete` here with a `sorry`, together with a long
-- note on why the hypotheses are exactly `hdisj` + `hmatch` and why the third
-- "result leaves `τ` fixed" conclusion is not part of the interface. That obligation is
-- discharged on `strata-org/Strata` `main` (`Lambda.Constraints_unify_matching_complete`,
-- in `Strata.DL.Lambda.LTyUnifyProps`, with the identical statement), so the local copy is
-- gone and `unifyTypes_matching_complete` below consumes the upstream theorem directly.
-- (The old local statement's rationale is in this file's git history.)

/-- The generator's `unifyTypes` wrapper (`Core.lean`) inherits matching-
    completeness from upstream's `Constraints_unify_matching_complete` by unwrapping the
    `.ok`/`.error` adapter. -/
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

/-- Prepending a scope built from `z`, whose keys avoid `FV(t)`, is a no-op:
    `subst (substScope z ++ Su) t = subst Su t`. Proved via
    `agree_on_freeVars_implies_subst_eq` — on each free variable of `t` the prepended scope
    doesn't fire (its `find?` is `none`), so both substitutions look up the same binding in
    `Su`.

    The new scope is given as an association list and pushed with `substScope`, because a
    `Subst` scope is now an opaque `Strata.Util.HMap` and cannot be written as a list
    literal. `Freshening.find?_substScope_eq_lookup` turns the `List.lookup` hypothesis into
    the `find?` fact the proof needs. -/
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

/-- If `v` is free in `t` and `Su` does not bind `v`, then `v` survives into
    `subst Su t`. Structural induction on `t`. Used to show the sampled type
    variables (those `Su` leaves undetermined) that occur in the leftover suffix
    would leak into the target — contradicting freshening disjointness. -/
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

/-- **Matchers of the same pattern agree pointwise on its variables.**

    The converse of `agree_on_freeVars_implies_subst_eq`: substitution is a
    homomorphism, so if two substitutions send `t` to the *same* type they must send
    each variable of `t` to the same type. Structural induction on `t`; the `tcons`
    case is `List.map_inj_left` on the argument lists.

    This is the **matching-uniqueness** ingredient the `SchemeInstAt` reformulation
    needs. It is worth noting what it is *not*: it says nothing about most-generality
    (`Subst.absorbs`), and it needs no unifier theory at all. Two matchers of the same
    matching problem are forced to agree on the pattern's variables, full stop — which
    is exactly why the generator's unifier output `Su` can be reconciled with a
    caller's matcher `Sm` on the *determined* variables without any MGU result. -/
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

/-- **Sampling is harmless for `guard2`.** The generator extends the unifier's
    substitution `Su` (a matcher for the suffix — not known to be *most general*)
    with a scope binding the *undetermined* freshened variables
    (`findFreeTyVars freshBoundVars Su`) to random samples. That extension does not
    perturb the leftover suffix: any such variable occurring in the suffix would (as
    `Su` leaves it unbound) survive into `subst Su leftoverSuffix = τ`, contradicting
    freshening disjointness (`hdisjBV`: freshened bound vars avoid `FV(τ)`). Hence the
    extended substitution still maps the suffix to the literal `τ`. This is what lets
    the sampling fragment discharge `guard2` from the matching theorem's conclusion. -/
theorem extended_subst_guard2 (freshBoundVars : List TyIdentifier) (Su : Lambda.Subst)
    (sampledTys : List LMonoTy) (leftoverSuffix τ : LMonoTy)
    (hSu : LMonoTy.subst Su leftoverSuffix = τ)
    (hdisjBV : ∀ v ∈ freshBoundVars, v ∉ τ.freeVars) :
    LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars Su).zip sampledTys) ++ Su)
      leftoverSuffix = τ := by
  rw [subst_substScope_noop]
  · exact hSu
  · intro v hv
    -- `lookup v = none`: a successful lookup would make `v` a key of the `zip`, hence a
    -- freshened bound variable that `Su` leaves unbound.
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

/-- **The `Sm`-to-`Su` bridge on the applied prefix.**

    The generator instantiates the applied prefix `schemeArgTys.take k` with its own
    *unifier output* extended by samples; a caller reasoning from the typing judgment
    instantiates it with a matcher `Sm`. This lemma says the two agree — provided the
    split point is **determined**: every type variable of the applied prefix also
    occurs in the leftover suffix (`hdet`).

    That proviso is what makes the reconciliation unconditional. Under it, each prefix
    variable `v`:
    - is *determined* by `Su` — otherwise `v` would survive into
      `subst Su suffix = τ` (`mem_freeVars_subst_of_find?_none`), contradicting
      freshening disjointness — so the sampled scope never fires on the prefix
      (`subst_substScope_noop`), and
    - satisfies `Sm v = Su v`, because `Sm` and `Su` are matchers of the *same*
      matching problem (`subst · suffix = τ`) and so agree on the suffix's variables
      (`subst_agree_of_subst_eq`).

    No most-generality (`Subst.absorbs`) and no bound on `Su`'s domain is needed. The
    determinacy proviso is exactly the boundary: for a split point where a scheme
    variable *vanishes* from the leftover suffix (the sampling fragment, e.g.
    `Sequence.map`'s element type at full saturation) the generator picks that
    variable's instance by *random sampling*, and no theorem can force the sample to
    equal `Sm`'s choice. Reaching that fragment from a spec-level premise needs either
    a domain bound on `Su` (`keys Su ⊆ FV(suffix) ∪ FV(τ)`, which upstream's
    `Constraints.unifyCore_matching_complete` proves internally but its public wrapper
    `Constraints_unify_matching_complete` does not expose) or an existentially bound
    `sampledTys`; see the note on `SchemeInstAt`. -/
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
  -- Both matchers agree pointwise on the free variables of the leftover suffix.
  have hagree : ∀ v ∈ ((schemeArgTys.drop k).foldr
      (fun σ acc => LMonoTy.arrow σ acc) retTy).freeVars,
      LMonoTy.subst Sm (.ftvar v) = LMonoTy.subst Su (.ftvar v) :=
    subst_agree_of_subst_eq _ (hmatch.trans hSu.symm)
  -- Every suffix variable is *determined* by `Su`: an undetermined one would survive
  -- into `subst Su suffix = τ`, contradicting freshening disjointness.
  have hdetermined : ∀ v ∈ ((schemeArgTys.drop k).foldr
      (fun σ acc => LMonoTy.arrow σ acc) retTy).freeVars,
      Strata.Util.HMaps.find? Su v ≠ none := by
    intro v hv hnone
    exact hdisjSuffix v hv (hSu ▸ mem_freeVars_subst_of_find?_none Su _ v hv hnone)
  apply List.map_congr_left
  intro σ hσ
  -- The sampled scope never fires on a prefix type: its keys are the variables `Su`
  -- leaves undetermined, and every prefix variable is determined.
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

/-- **Forward construction of a `findPolymorphicOps` candidate (bridge,
    plumbing only).**

    The existence-direction mirror of `findPolymorphicOps_instanceR`: given a scheme
    in `pctx`, a split point `k`, the freshening/decomposition results, and the two
    `do`-block guards *as hypotheses*, `(name, concreteArgTys)` is a member of
    `findPolymorphicOps`. It is pure `flatMap`/`filterMap`/`guard` plumbing. The guard
    hypotheses (`hunify`, `hguard2`) are discharged by the caller
    (`isPolyApp_of_hasType`) via `unifyTypes_matching_complete`. -/
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
  -- Discharge the `Option` `do`-block: resolve the unify bind, then both guards.
  rw [hunify]
  simp only [bind, Option.bind, guard, pure]
  rw [if_pos (by
    rcases hguard1 with h | h
    · simp [h]
    · simp [List.isEmpty_iff, h])]
  rw [if_pos (by rw [beq_iff_eq]; exact hguard2)]
  rw [hcat]

/-- Inversion of `mkApps_hasType`: a well-typed left-nested application spine
    `mkApps base args : τ` decomposes into a list of argument types `argTys` such
    that `base` has the curried arrow type `argTys.foldr arrow τ` and each `argᵢ`
    is well-typed at `argTys[i]`.

    This is the converse used by `isPolyApp_of_hasType` to recover, from
    a typing derivation, the concrete argument types that `findPolymorphicOps` must
    have produced. The `.app` rule (`HasTypeA.app`) peels one arrow per applied
    argument; `argTys` is built outermost-first as the induction returns. -/
theorem mkApps_hasType_inv (bctx : BVarCtx) (base : LExpr') (args : List LExpr')
    (τ : LMonoTy)
    (hwt : HasTypeA' bctx (mkApps base args) τ) :
    ∃ argTys : List LMonoTy,
      HasTypeA' bctx base (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) ∧
      List.Forall₂ (HasTypeA' bctx) args argTys := by
  induction args generalizing base with
  | nil =>
    -- `mkApps base [] = base`, so `base : τ`; no arrows to peel.
    exact ⟨[], hwt, .nil⟩
  | cons a as ih =>
    -- `mkApps base (a :: as) = mkApps (.app () base a) as`.
    obtain ⟨argTys', hbase', hargs'⟩ := ih (.app () base a) hwt
    -- Invert the head application: `base : aty → (argTys'.foldr arrow τ)` and `a : aty`.
    -- The binder type `aty` is left implicit; unification fills it from `hfn`
    -- against the goal `(?aty :: argTys').foldr arrow τ = arrow ?aty (…)`.
    cases hbase' with
    | app hfn harg => exact ⟨_ :: argTys', hfn, .cons harg hargs'⟩

/-- `argTys.foldr arrow τ` is injective in `argTys` **once the lengths agree**.
    (It is not injective without the length constraint: e.g.
    `[a].foldr arrow (b → c) = [a, b].foldr arrow c`.) Used by
    `isPolyApp_of_hasType` to identify the typing-derived argument types with the
    concrete argument types `findPolymorphicOps` emits — both fold to the same
    annotation and have the same length (`= args.length`). -/
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
      -- `arrow a (…) = arrow b (…)`; `arrow` is `tcons "arrow" [·, ·]`, so unfold
      -- and use `tcons` injectivity to split head and tail equalities.
      simp only [LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq, and_true,
        true_and] at heq
      obtain ⟨hhd, htl⟩ := heq
      subst hhd
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [ih bs hlen htl]

/-- Membership in `List.mapM f l` on `SetGen.Set`: `args` is in the support
    iff each element is pointwise in the support of `f` at the corresponding input. -/
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

/-- If `(name, argTys) ∈ findOpsInCtx octx τ`, then
    `(name, argTys.foldr arrow τ) ∈ octx.ops`, and `argTys` has one element or more. -/
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

/-- The arities an ambient context must register for the eight type constructors that a
    generable type can mention. Every type the generators build is generable, so this is
    the whole content of the `signatureWellKinded` fields of `Core.TypeSpec.FuncHasType'`
    and `Core.TypeSpec.ProcHasType'`: those fields ask that each signature type be
    well-kinded in `C`, i.e. that each type constructor be applied at the arity
    `C.knownTypes` records for it.

    `bitvec` needs no entry: `.bitvec n` is its own `LMonoTy` constructor and contributes no
    `getTypeConsArities` pair. `coreContextSimpleTyArities` discharges this for the Strata
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

/-- **A generable type is well-kinded in any context that registers the arities.**
    Induction on the type: each constructor contributes exactly one
    `getTypeConsArities` pair at its own arity, plus the pairs of its arguments. -/
theorem genLMonoTy_mem_wellKindedTy {C : LContext CoreLParams} (hC : SimpleTyArities C)
    {tvars : List TyIdentifier} :
    ∀ {ty : LMonoTy},
      (∃ m, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) →
      C.WellKindedTy ty := by
  intro ty hTy
  -- The hypothesis is an `∃`, so `induction … using` cannot see the target. A
  -- `refine` against the eliminator can.
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

-- ── How the generators may change the ambient context ───────────────
--
-- Only two statement generators touch `C`: `genFuncDeclStmt` (`addFactoryFunction`,
-- which leaves `knownTypes` alone) and `genTypeDeclStmt` (`addKnownTypeWithError`, which
-- *adds* one name and fails on a clash). Both therefore leave every existing known-type
-- entry in place, which is all `SimpleTyArities` and `WellKindedTy` read.

/-- A successful `Identifiers.addWithError` only inserts a *new* key, so every entry
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

/-- Declaring a new type constructor leaves every already-registered arity in place. -/
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

/-- Declaring a function does not touch the known-type table. -/
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

/-- An `insert` adds at most the inserted value to a map's values. -/
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

-- ── Closure of generability under the generators' type operations ────

/-- `LMonoTy.subst` keeps a type generable if the substitution maps every type
    variable to a generable type. -/
theorem genLMonoTy_mem_subst {tvars : List TyIdentifier} (S : Lambda.Subst) (ty : LMonoTy)
    (hTy : ∃ m, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (hSubst : ∀ v t, Strata.Util.HMaps.find? S v = some t →
      ∃ m, t ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    ∃ m, LMonoTy.subst S ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
  -- `LMonoTy.subst_unfold` is the one-level unfolding that hides the `hasEmptyScopes`
  -- short-circuit, so each case reduces exactly as a structural recursion would.
  refine genLMonoTy_mem_rec
    (motive := fun ty => ∃ m, LMonoTy.subst S ty ∈
      SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    ?bool ?int ?string ?real ?regex ?bitvec ?ftvar ?arrow ?map ?seq hTy
  case bool => simp only [LMonoTy.bool, LMonoTy.subst_unfold, List.map_nil]; exact genLMonoTy_mem_bool
  case int => simp only [LMonoTy.int, LMonoTy.subst_unfold, List.map_nil]; exact genLMonoTy_mem_int
  case string => simp only [LMonoTy.string, LMonoTy.subst_unfold, List.map_nil]; exact genLMonoTy_mem_string
  case real => simp only [LMonoTy.real, LMonoTy.subst_unfold, List.map_nil]; exact genLMonoTy_mem_real
  case regex => simp only [LMonoTy.regex, LMonoTy.subst_unfold, List.map_nil]; exact genLMonoTy_mem_regex
  case bitvec => intro w; simp only [LMonoTy.subst_unfold]; exact genLMonoTy_mem_bitvec
  case ftvar =>
    intro name hname
    simp only [LMonoTy.subst_unfold]
    split
    · exact hSubst _ _ ‹_›
    · exact genLMonoTy_mem_ftvar hname
  case arrow =>
    intro τ₁ τ₂ _ _ ih₁ ih₂
    rw [LMonoTy.arrow, LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    simp only [List.map_cons, List.map_nil]
    exact genLMonoTy_mem_arrow ih₁ ih₂
  case map =>
    intro τ₁ τ₂ _ _ ih₁ ih₂
    rw [LMonoTy.map, LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    simp only [List.map_cons, List.map_nil]
    exact genLMonoTy_mem_map ih₁ ih₂
  case seq =>
    intro τ _ ih₁
    rw [LMonoTy.seq, LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    simp only [List.map_cons, List.map_nil]
    exact genLMonoTy_mem_seq ih₁

/-- Every syntactic subtype of a generable type is itself generable. -/
private theorem syntacticSubtypes_mem_genLMonoTy {tvars : List TyIdentifier}
    (ty : LMonoTy) (hTy : ∃ m, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (σ : LMonoTy) (hσ : σ ∈ syntacticSubtypes ty) :
    ∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
  revert hσ
  refine genLMonoTy_mem_rec
    (motive := fun ty => σ ∈ syntacticSubtypes ty →
      ∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    ?bool ?int ?string ?real ?regex ?bitvec ?ftvar ?arrow ?map ?seq hTy
  case bool =>
    intro hσ
    simp [syntacticSubtypes, LMonoTy.bool] at hσ
    subst hσ; exact genLMonoTy_mem_bool
  case int =>
    intro hσ
    simp [syntacticSubtypes, LMonoTy.int] at hσ
    subst hσ; exact genLMonoTy_mem_int
  case string =>
    intro hσ
    simp [syntacticSubtypes, LMonoTy.string] at hσ
    subst hσ; exact genLMonoTy_mem_string
  case real =>
    intro hσ
    simp [syntacticSubtypes, LMonoTy.real] at hσ
    subst hσ; exact genLMonoTy_mem_real
  case regex =>
    intro hσ
    simp [syntacticSubtypes, LMonoTy.regex] at hσ
    subst hσ; exact genLMonoTy_mem_regex
  case bitvec =>
    intro w hσ
    simp [syntacticSubtypes] at hσ
    subst hσ; exact genLMonoTy_mem_bitvec
  case ftvar =>
    intro name hname hσ
    simp [syntacticSubtypes] at hσ
    subst hσ; exact genLMonoTy_mem_ftvar hname
  case arrow =>
    intro τ₁ τ₂ h₁ h₂ ih₁ ih₂ hσ
    simp [syntacticSubtypes, LMonoTy.arrow] at hσ
    rcases hσ with rfl | hσ₁ | hσ₂
    · exact genLMonoTy_mem_arrow h₁ h₂
    · exact ih₁ hσ₁
    · exact ih₂ hσ₂
  case map =>
    intro τ₁ τ₂ h₁ h₂ ih₁ ih₂ hσ
    simp [syntacticSubtypes, LMonoTy.map] at hσ
    subst hσ; exact genLMonoTy_mem_map h₁ h₂
  case seq =>
    intro τ h₁ ih₁ hσ
    simp [syntacticSubtypes, LMonoTy.seq] at hσ
    subst hσ; exact genLMonoTy_mem_seq h₁

/-- `addNewTypes` keeps the property that every element of the list is generable. -/
private theorem addNewTypes_mem_genLMonoTy {tvars : List TyIdentifier} (fuel : Nat) (tys : List LMonoTy)
    (hAll : ∀ σ ∈ tys, ∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    ∀ σ ∈ addNewTypes fuel tys,
      ∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
  induction fuel generalizing tys with
  | zero => simp [addNewTypes]; exact hAll
  | succ n ih =>
    simp only [addNewTypes]
    split
    · exact hAll
    · apply ih
      intro σ hσ
      rcases List.mem_append.mp hσ with hOld | hNew
      · exact hAll σ hOld
      · simp [List.mem_filterMap] at hNew
        obtain ⟨ty, hty_mem, hty_eq⟩ := hNew
        split at hty_eq
        · rename_i argTy retTy
          split at hty_eq
          · simp at hty_eq; subst hty_eq
            have harrow : ∃ m, LMonoTy.arrow argTy retTy ∈
                SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := hAll _ hty_mem
            exact (genLMonoTy_mem_arrow_inv harrow).2
          · simp at hty_eq
        · simp at hty_eq

/-- Every type in `generableTypesFromCtx` is generable, if every type in the
    bound-variable, free-variable, and operator contexts is generable. -/
theorem generableTypesFromCtx_mem_genLMonoTy {tvars : List TyIdentifier}
    (bctx : BVarCtx) (fctx : FVarCtx) (octx : OpCtx)
    (hBctx : ∀ τ ∈ bctx, ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (hFctx : ∀ p ∈ fctx, ∃ m, p.2 ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (hOctx : ∀ p ∈ octx.ops, ∃ m, p.2 ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) :
    ∀ σ ∈ generableTypesFromCtx bctx fctx octx,
      ∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
  intro σ hσ
  unfold generableTypesFromCtx at hσ
  apply addNewTypes_mem_genLMonoTy _ _ _ σ hσ
  intro τ hτ
  -- `generableTypesFromCtx` uses `dedupTys`, which has a linear cost. `dedupTys_eq`
  -- gives `List.eraseDups`, and the membership lemma applies to that function.
  rw [dedupTys_eq] at hτ
  have hτ' := List.mem_eraseDups.mp hτ
  rw [List.mem_flatMap] at hτ'
  obtain ⟨ty, hty_mem, hty_sub⟩ := hτ'
  have hty_gen : ∃ m, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m) := by
    have hty_mem' := hty_mem
    simp only [List.mem_append, List.mem_map] at hty_mem'
    rcases hty_mem' with (hb | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact hBctx ty hb
    · exact hFctx p hp
    · exact hOctx p hp
  exact syntacticSubtypes_mem_genLMonoTy ty hty_gen τ hty_sub

-- ── The same closure results, directly for `LContext.WellKindedTy` ───
--
-- The lemmas above route through `SimpleType`, which is the *generator's* type
-- vocabulary: it is closed under the operations below, and `simpleType_wellKindedTy`
-- turns it into the `WellKindedTy` obligation upstream's rules impose. That route
-- breaks down as soon as a context holds a type the generator did not build — most
-- importantly a datatype's own `tcons`, which a generated `MutualDatatype` block
-- contributes to `octx` through its constructor operators. Such a type is perfectly
-- well-kinded in the context that registers the block, but it is not a `SimpleType`.
--
-- `LContext.WellKindedTy` (upstream, `LExprTypeEnv.lean`) is itself closed under every
-- operation the generators perform on context types, so the results below are the ones
-- to state the statement generators' discipline against. They subsume the `SimpleType`
-- versions via `simpleType_wellKindedTy`, and unlike them they stay true at the program
-- level.

/-- `C.WellKindedTy` reads nothing but `C.knownTypes`, so it transports along any
    extension of the known-type table that leaves existing entries in place. -/
theorem wellKindedTy_mono {C C' : LContext CoreLParams}
    (h : ∀ (n : String) (k : Nat), C.knownTypes[n]? = some k → C'.knownTypes[n]? = some k)
    {ty : LMonoTy} (hty : C.WellKindedTy ty) : C'.WellKindedTy ty :=
  fun ref n hn => h ref n (hty ref n hn)

/-- The arity pairs of an `arrow`'s result type are among the arrow's own. -/
theorem wellKindedTy_arrow_right {C : LContext CoreLParams} {a b : LMonoTy}
    (h : C.WellKindedTy (.arrow a b)) : C.WellKindedTy b := by
  intro ref n hn
  refine h ref n ?_
  simp only [LMonoTy.arrow, getTypeConsArities, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr hn)

/-- Every syntactic subtype of a well-kinded type is well-kinded: `syntacticSubtypes`
    descends only into an `arrow`'s two components, whose arity pairs are among the
    arrow's own. -/
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

/-- `addNewTypes` preserves well-kindedness: the only types it adds are `arrow` result
    types of types already in the list. -/
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

/-- **Every type the call generator can sample is well-kinded in `C`**, given that the
    types recorded in the variable and operator contexts are. `generableTypesFromCtx`
    only takes syntactic subtypes of context types and `arrow` result types, and
    `C.WellKindedTy` is closed under both. This is the `WellKindedTy` analogue of
    `generableTypesFromCtx_simple`, and unlike that lemma it survives a datatype block's
    constructor operators landing in `octx`. -/
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

/-- **`LMonoTy.subst` preserves well-kindedness** when every type in the substitution's
    range is well-kinded: substitution rewrites `ftvar`s (which contribute no arity pairs
    at all) and leaves every type-constructor name applied at its original argument
    count. -/
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

/-- **Soundness of the monomorphic Indir rule**, parametric in the argument
    generator. Given that `genArg σ` only produces terms of type `σ` (`hArg`), a
    fully-applied operator assembled by `genIndir` has type `τ`.

    Stated for an arbitrary `genArg` because `genLExpr` instantiates it *both* with
    `genLExprBase` (at the depth floor) and with `genLExpr` itself (above it, so
    that factory applications nest). The body is the argument that used to be
    inlined in `genLExpr_sound`. -/
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

/-- Soundness of `genIndirPoly`: every generated expression is well-typed.

    The proof exploits the key structural invariant: `genIndirPoly` always
    produces either a `genLExprBase` fallback (when no candidates match) or
    `mkApps (.op () ⟨name, ()⟩ (some fullArrowTy)) args` where
    `fullArrowTy = concreteArgTys.foldr arrow τ`.

    For the latter case:
    - `HasTypeA.op` gives the op node type `fullArrowTy` (reads the annotation).
    - Each argument is generated by `genArg` at a concrete type `σᵢ`; by the
      hypothesis `hArg`, that argument has type `σᵢ`. (At the depth floor the
      caller discharges `hArg` with `genLExprBase_sound`; above it, with the
      induction hypothesis of `genLExpr_sound` — which is what makes *nested*
      factory applications sound.)
    - `mkApps_hasType` folds the applications to obtain result type `τ`.

    Note the fallback branch still goes to `genLExprBase … depth` and so is
    discharged by `genLExprBase_sound` directly, independently of `genArg`. -/
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
  -- `genIndirPoly` is now the thin wrapper around `genIndirPolyCore`, so the
  -- generator-parametric result applies directly: `genArg` soundness is `hArg`,
  -- and the fallback is `genLExprBase … depth`, handled by `genLExprBase_sound`.
  exact StrataGenerators.IndirSupport.genIndirPolyCore_hasType fctx octx pctx bctx τ
    genArg _ maxNumArgs hArg
    (fun a ha => genLExprBase_sound fctx octx pctx tvars bctx depth τ a ha) e he

/-- Soundness of `genLExpr`: every generated expression is well-typed.
    This combines the soundness of the Indir and IndirPoly rules with
    `genLExprBase_sound`. -/
theorem genLExpr_sound (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat)
    (τ : LMonoTy) (maxNumArgs : Nat)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs)) :
    HasTypeA' bctx e τ := by
  -- Induction on the depth index. `genLExpr` is structurally recursive on it (the
  -- Indir/IndirPoly *arguments* are drawn from `genLExpr … n`), so soundness of the
  -- argument generator at the smaller index is exactly the induction hypothesis.
  -- Both branches then share one shape, differing only in which `hArg` they supply.
  induction depth generalizing τ e with
  | zero =>
    -- Depth floor: arguments come from `genLExprBase … 0`.
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
    -- Above the floor: arguments come from `genLExpr … n`; `ih` is its soundness.
    -- This is the case that makes nested factory applications sound.
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
/-- Every free variable appearing in an expression from `genLExprBase`'s support
    is drawn from the fvar context `fctx` (the only source of fvars is `pickFVar`,
    which draws names from `fctx`). -/
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx m σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx m _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
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
    -- Indir branch: the head is an `.op` node (no free variables) and each
    -- argument comes from `genLExprBase … n`, so this theorem's own recursive call
    -- bounds their free variables.
    · rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact StrataGenerators.IndirSupport.genIndir_getVars_subset octx _ _ _
          (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha) _ e he
      · exact genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ e he
    -- IndirPoly branch: same, fallback included.
    · exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx _ _ _ _ _
        (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n σ a ha)
        (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx n _ a ha) e he
  case h_21 =>
    -- Other type constructors: the three context leaves, as in the depth-0 `.regex`
    -- case `h_15` (not the `n + 1` arm, which has Indir/IndirPoly branches).
    -- A bvar/op leaf has no free variables; an fvar leaf's name comes from `fctx`.
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
/-- With an empty fvar context, every expression in `genLExprBase`'s support has
    no free variables (a specialization of `genLExprBase_fvars_subset`). -/
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

/-- Every argument produced by `mapM genArg` has all its free variables drawn from
    `fctx`, provided each `genArg σ` does (`hArg`).

    Parametric in `genArg` for the same reason as `genIndir_sound`: `genLExpr`
    instantiates it with `genLExprBase` at the depth floor and with itself above
    at the smaller depth index. -/
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

/-- Every argument produced by `mapM (genLExprBase fctx …)` has all its free
    variables drawn from `fctx`. Specialization of `mapM_genArg_fvars_subset`. -/
private theorem mapM_genLExprBase_fvars_subset (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set)
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth) argTys)) :
    ∀ a ∈ args, LExpr.getVars a ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) :=
  mapM_genArg_fvars_subset fctx _
    (fun σ a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx depth σ a ha) argTys args hargs

/-- Every argument produced by `mapM (genLExprBase [] …)` over an empty fvar
    context has no free variables. -/
private theorem mapM_genLExprBase_no_fvars (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set)
      (genLExprBase (G := SetGen.Set) [] octx pctx tvars bctx depth) argTys)) :
    ∀ a ∈ args, LExpr.getVars a = [] := by
  intro a ha
  have h := mapM_genLExprBase_fvars_subset [] octx pctx tvars bctx depth argTys args hargs a ha
  simpa using List.subset_nil.mp h

/-- Every free variable in an expression from `genIndirPoly`'s support is drawn
    from the fvar context `fctx`. -/
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
  -- As with `genIndirPoly_sound`: `genIndirPoly` is now the wrapper around
  -- `genIndirPolyCore`, so the generator-parametric lemma applies, with
  -- `genLExprBase_fvars_subset` discharging the fallback.
  exact StrataGenerators.IndirSupport.genIndirPolyCore_getVars_subset fctx octx pctx bctx τ _
    genArg _ maxNumArgs hArg
    (fun a ha => genLExprBase_fvars_subset fctx octx pctx tvars bctx depth τ a ha) e he

/-- With an empty fvar context, every expression in `genIndirPoly`'s support has
    no free variables. -/
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

/-- Every free variable in an expression from `genLExpr`'s support is drawn from
    the fvar context `fctx`. -/
theorem genLExpr_fvars_subset (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ)) :
    LExpr.getVars e ⊆ fctx.map (fun p => (⟨p.1, ()⟩ : Lambda.Identifier Unit)) := by
  -- Induction on the depth index, mirroring `genLExpr_sound`: the Indir/IndirPoly
  -- arguments come from `genLExpr … n`, so the induction hypothesis is exactly the
  -- `hArg` the parametric lemmas need.
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

/-- With an empty fvar context, every expression in `genLExpr`'s support has
    no free variables. -/
theorem genLExpr_no_fvars (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) [] octx pctx tvars bctx depth τ)) :
    LExpr.getVars e = [] := by
  have h := genLExpr_fvars_subset [] octx pctx tvars bctx depth τ e he
  simpa using List.subset_nil.mp h

end Lambda.LExpr

-- ── Completeness for genIndirPoly and genLExpr ─────────────────────────

/-- A type `σ` is in the support of the per-element type-sampling action
    used inside `genIndirPoly` (choose a random index into `generableTys`, or
    draw an arbitrary base type via `pickBaseType` when the list is empty).

    The empty-context side condition is membership in `pickBaseType`'s support
    rather than the former `σ = .bool`: the generator now samples any ground base
    type there, so pinning `σ` to `.bool` would no longer describe it. -/
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
/-- Each element of the type-sampling step in `genIndirPoly` is either a member
    of `generableTys` (when non-empty) or an arbitrary base type drawn from
    `pickBaseType` (when empty). This lemma establishes that a valid `sampledTys`
    list is in the support of the sampling computation.

    Stated for an arbitrary sample count `k` rather than the literal `3`: the
    generator draws `maxNumArgs` samples and `maxNumArgs` is a parameter, so
    pinning `k := 3` would specialize every downstream statement to the current
    Strata factory's maximum arity. The proof is an induction on `k`; the previous
    version destructured a three-element list explicitly, which is what forced the
    literal into the completeness chain. -/
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

/-- Completeness of `genIndirPoly`: if an expression can be assembled as
    `mkApps (.op () ⟨name, ()⟩ (some fullArrowTy)) args` where
    `(name, concreteArgTys)` is a valid entry in `findPolymorphicOps` for
    appropriate `sampledTys`, and each argument is in `genLExprBase`'s
    support, then the expression is in `genIndirPoly`'s support. -/
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
  -- `genIndirPoly` is now a wrapper, so unfold the core too (it is where the
  -- sampling `mapM` and the candidate `dite` actually live).
  unfold genIndirPoly genIndirPolyCore
  simp only [SetGen.Set.mem_bind, SetGen.Set.mem_pure, SetGen.mem_dite]
  -- Exhibit sampledTys as the witness for the type-sampling mapM
  refine ⟨sampledTys, sampledTys_mem_support _ _ _ hSampledLen hSampledValid, ?_⟩
  -- Take the positive branch of the dite (ops.length > 0)
  have hOpsPos : (findPolymorphicOps pctx τ (generableTypesFromCtx bctx fctx octx)
      sampledTys maxNumArgs).length > 0 :=
    List.length_pos_of_mem hEntry
  left
  refine ⟨hOpsPos, ?_⟩
  -- The candidate is chosen by `elements`, so exhibit `(name, concreteArgTys)` as
  -- the picked entry (a member of `ops`), then the args and the two equalities.
  refine ⟨(name, concreteArgTys), ?_, args, ?_, ?_⟩
  · -- (name, concreteArgTys) ∈ elements ops _
    rw [← mem_support_iff, mem_support_elements_iff]
    exact hEntry
  · -- args ∈ concreteArgTys.mapM genArg
    exact (mem_mapM_iff genArg concreteArgTys args).mpr hArgs
  · -- The expression equals mkApps ...
    rfl

/-- **The base generator's support is contained in `genLExpr`'s, at the same depth.**

    `genLExpr` offers `genLExprBase … depth τ` as one of its branches in *both*
    arms of its `dite`: at weight 1 in the `frequency` list when there are
    monomorphic Indir candidates, and as the left component of the `pick`
    otherwise. So anything the base generator can produce, `genLExpr` can produce
    too — with no depth or context side-conditions.

    This is what lets the per-argument premises of `isPolyApp_of_hasType` be stated
    as the plain `genLExprBase_complete` bundle even though `genLExpr` draws
    arguments from *itself* at the smaller index. See the comment on
    `isPolyApp_of_hasType`'s `hArgsComplete` for why the bundle is keyed to the
    argument budget `depth - 1` rather than `depth`. -/
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

/-- **The argument-position bridge.**

    `genLExpr` draws its Indir/IndirPoly arguments from `genLExprBase … 0` at the
    depth floor and from *itself* at `n` above it (`Core.lean`'s `genArg`). This
    lemma discharges membership in that depth-`match` generator — which is exactly
    `IsPolyApp`'s argument clause — from the ordinary `genLExprBase_complete`
    bundle, provided the bundle is keyed to the **argument budget** `depth - 1`
    rather than to `depth`.

    The `depth - 1` is not slack in the statement: an argument of a factory
    application really does get one less unit of depth than the application
    itself, because the spine node consumes one. At the floor (`depth = 0`),
    `depth - 1 = 0` and the argument generator is the base generator directly.
    Above the floor, `genLExprBase_mem_genLExpr` lifts the base generator's output
    into `genLExpr … n`, which is where nested factory applications become
    reachable. -/
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

/-- An expression is a valid polymorphic operator application reachable by
    `genIndirPoly`: there exist sampled types, an operator entry in `pctx` that
    unifies with the target, and arguments each in `genLExprBase`'s support. -/
def IsPolyApp (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat) (e : LExpr') : Prop :=
  ∃ (sampledTys : List LMonoTy) (name : String)
    (concreteArgTys : List LMonoTy) (args : List LExpr'),
    -- One sample per potential type variable, i.e. `maxNumArgs` of them — the same
    -- count `genIndirPoly` draws. Not fixed at 3: that is merely the current Strata
    -- factory's maximum arity, and `maxNumArgs` is a generator parameter.
    sampledTys.length = maxNumArgs ∧
    (∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SetGen.support (pickBaseType (G := SetGen.Set)))) ∧
    (name, concreteArgTys) ∈ findPolymorphicOps pctx τ
      (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs ∧
    -- The arguments come from whatever `genLExpr` uses in argument position at this
    -- depth: `genLExprBase … 0` at the floor, and `genLExpr … n` above it. The
    -- second case is what admits *nested* factory applications; it is
    -- the clause a fully inductive completeness statement will build on (part B).
    List.Forall₂ (fun arg σ =>
      arg ∈ (match (motive := Nat → LMonoTy → SetGen.Set LExpr') depth with
             | 0 => genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0
             | n + 1 => fun σ' =>
                 genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx n σ' maxNumArgs) σ)
      args concreteArgTys ∧
    e = mkApps (.op () ⟨name, ()⟩
      (some (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) args

/-- **Spec-shaped backward direction for the polymorphic case.**

    Derives `IsPolyApp` from the *typing judgment* for a saturated/partial
    application spine over a polymorphic operator, given a single explicit
    side-condition (`hEntry`) that the generator's unification search would have
    produced the corresponding `findPolymorphicOps` entry.

    This isolates the split-point unification ingredient — that Strata's `unify`
    *succeeds* there — into the hypothesis `hEntry`, and *derives* everything else from
    `HasTypeA'`. (`hEntry` no longer marks a gap: upstream proves matching-completeness as
    `Constraints_unify_matching_complete`, which is what `…_fullySpecShaped` uses to
    discharge it; keeping it as a hypothesis here just avoids the detour.)

    - **Argument types** come from inverting the application spine
      (`mkApps_hasType_inv`): the derivation forces the op annotation to be
      `argTys.foldr arrow τ` and each `argᵢ : argTysᵢ`.
    - **Identification** of those typing-derived `argTys` with the entry's
      `concreteArgTys` is by length-matched injectivity of `foldr arrow`
      (`foldr_arrow_inj_of_length_eq`); both fold to the *same* annotation carried
      by the op node, and both have length `args.length`.
    - **Argument generability** (`IsPolyApp`'s fourth conjunct) is `derived` from
      argument typing via `genLExprBase_complete` — this is why `HasTypeA'` is
      load-bearing rather than decorative.

    The per-argument recursive-completeness premises (`hargWt`/`hargNames`/… , the
    same bundle `genLExprBase_complete` needs) are genuine hypotheses: an argument's
    generability cannot follow from its type alone. -/
theorem isPolyApp_of_hasType (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (name : String) (annot : LMonoTy) (args : List LExpr')
    -- The expression is a spine over an op node carrying annotation `annot`:
    (hwt : HasTypeA' bctx (mkApps (.op () ⟨name, ()⟩ (some annot)) args) τ)
    -- THE unification side-condition: the generator's split-point
    -- search finds this operator at the typing-derived argument types.
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
    -- Per-argument recursive-completeness premises (the `genLExprBase_complete`
    -- bundle, one per argument), keyed by position against `concreteArgTys`.
    --
    -- NOTE: the depth budget here is `depth - 1`, not `depth`. Because
    -- `genLExpr` is recursive, arguments are drawn from the generator at the
    -- *smaller* index, so an argument of a factory application has one less unit
    -- of depth than the application itself — the spine node consumes one. See
    -- `mem_genArg_of_baseComplete`.
    (hArgsComplete : List.Forall₂
      (fun arg σ => (∃ m, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m)) ∧
        emptyNames arg ∧ allVarsInCtx fctx octx arg ∧
        AllTypesSimple tvars (depth - 1) bctx arg ∧ termDepth bctx arg ≤ depth - 1)
      args concreteArgTys) :
    IsPolyApp fctx octx pctx tvars bctx depth τ maxNumArgs
      (mkApps (.op () ⟨name, ()⟩ (some annot)) args) := by
  -- Invert the spine: recover argument types `argTys` and per-arg typings.
  obtain ⟨argTys, hbase, hargsTyped⟩ := mkApps_hasType_inv bctx _ args τ hwt
  -- The op node types at its annotation, so `annot = argTys.foldr arrow τ`.
  cases hbase with
  | op =>
    -- Identify the typing-derived `argTys` with the entry's `concreteArgTys`:
    -- both fold (with `τ`) to `annot`, and both have length `args.length`.
    have hlenTyped : args.length = argTys.length := hargsTyped.length_eq
    have hArgTysEq : argTys = concreteArgTys := by
      apply foldr_arrow_inj_of_length_eq argTys concreteArgTys τ
      · omega
      · rw [← hAnnot]
    subst hArgTysEq
    -- Derive argument generability from argument typing. The target is the
    -- depth-`match` generator `genLExpr` uses in argument position, so each argument
    -- goes through `mem_genArg_of_baseComplete` rather than `genLExprBase_complete`
    -- directly.
    have hArgsGen : List.Forall₂
        (fun arg σ =>
          arg ∈ (match (motive := Nat → LMonoTy → SetGen.Set LExpr') depth with
                 | 0 => genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx 0
                 | n + 1 => fun σ' =>
                     genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx n σ'
                       maxNumArgs) σ)
        args argTys := by
      -- Zip the per-arg typings with the per-arg completeness premises.
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
    -- Package the `IsPolyApp` existential.
    exact ⟨sampledTys, name, argTys, args, hLen, hValid, hEntry, hArgsGen, by rw [hAnnot]⟩

-- ── Derived well-formedness for `freshenBoundVars` ─────────────
--
-- `SchemeInstAt` carried the two disjointness conditions as premises before, and
-- callers supplied them. These conditions are *consequences* of `freshenBoundVars`.
-- Therefore this section derives them from `freshenBoundVars_disjoint`, which is in
-- `HasTypeAGen/Freshening.lean`.
--
-- One true input remains: **scheme closedness**. The body of the scheme must not
-- mention a type variable outside its own binders. Closedness is a property of the
-- `pctx` entry and not of `freshenBoundVars`. Also, closedness holds for each real
-- scheme. For an example, see `corePolyOps`. It also holds for `factoryPolyOps`,
-- because each entry of `factoryPolyOps` has the form `∀ fn.typeArgs. …`.

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

/-- **Spec-level scheme-instance witness.**

    Bundles "the op node's annotation is a genuine instance of a `pctx` scheme at
    some split point" into a single existential — the declarative content that
    replaces the generator-internal `hEntry`. All of the freshening/decomposition
    witnesses (`freshBoundVars`, `freshMonoTy`, `schemeArgTys`, `retTy`) are existentially
    bound and pinned by `rfl`-shaped equalities, so a caller supplies only the *scheme*
    (`boundVars`, `monoTy`), *split point* `k`, and *matcher* `Sm`.

    **Every conjunct is now `Su`-free.** Both the matcher condition (`hmatch`) and the
    applied-prefix condition are stated in terms of the caller's substitution `Sm`;
    neither `unifyTypes` nor its output `Su` nor the generator's `sampledTys` appears
    anywhere in this predicate. `isPolyApp_of_hasType_specShaped` bridges `Sm` to the
    unifier's `Su` internally (`extended_subst_prefix_of_determined` for the applied
    prefix, `unifyTypes_matching_complete` + `extended_subst_guard2` for the suffix),
    so nothing generator-internal leaks out. Earlier the applied-prefix conjunct read
    `∀ Su, unifyTypes suffix τ = some Su → …`, which no caller reasoning from the
    typing judgment could discharge; that is the whole point of the reformulation.

    **The price is split determinacy.** The `Su`-free form has to rule out the
    *sampling* fragment: at a split point where a scheme variable vanishes from the
    leftover suffix, the generator instantiates it by random sampling, and no
    hypothesis about `Sm` can force the sample to agree. The determinacy conjunct
    (prefix variables ⊆ suffix variables) is exactly that restriction; it is a
    decidable property of the scheme and split point, so a caller settles it by
    `decide`/`simp`. It always holds at `k = 0` (nothing applied), and it holds at *full*
    saturation whenever the scheme's return type mentions every variable its inputs do —
    e.g. `Sequence.append : ∀a. Seq a → Seq a → Seq a` at every split point. It fails
    exactly where a variable of the applied prefix is absent from the leftover suffix
    (`Sequence.length : ∀a. Seq a → int` at `k = 1`), which is where the generator picks
    that variable's instance by sampling. For those, use the `hEntry` form
    (`genLExpr_complete_poly_specShaped`), which covers the sampling fragment at the cost
    of a generator-internal premise. See
    `extended_subst_prefix_of_determined` for what would be needed to lift the
    restriction (a domain bound on `Su`, proved but not exposed upstream).

    Discharging `SchemeInstAt` from a caller's `OpsConsistentR F e` (which carries
    exactly this scheme-instance witness in its `.op_in` constructor) is the intended
    route: see `schemeInstAt_of_opsConsistentR` in `HasTypeAGenOpsConsistent.lean`.

    **Well-formedness for `freshenBoundVars` is no longer a premise.** Before, this
    predicate carried two disjointness conjuncts, and callers supplied them. The first
    conjunct said that the fresh bound variables avoid `FV(τ)`. The second said the
    same for the remaining arrow suffix. Both conjuncts are consequences of
    `freshenBoundVars`, and `schemeInstAt_freshening_disjoint` now derives them. In
    their place, this predicate has the structural condition `hclosed`, which is
    weaker: the scheme body mentions no type variable outside its own binders. -/
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
    -- **Scheme closedness**: the scheme body mentions no type variable outside its
    -- own binders. This condition replaces the two disjointness premises that this
    -- predicate carried before. `schemeInstAt_freshening_disjoint` now *derives*
    -- those two premises from this condition. Closedness is a property of the `pctx`
    -- entry and not of the generator. Also, closedness holds for each real scheme.
    -- It holds for `corePolyOps`. It also holds for `factoryPolyOps`, because each
    -- entry of `factoryPolyOps` has the form `∀ fn.typeArgs. …`.
    (∀ v ∈ monoTy.freeVars, v ∈ boundVars) ∧
    -- the matcher (spec-level; no `Su`):
    LMonoTy.subst Sm
      ((schemeArgTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ ∧
    -- **Split determinacy**: every type variable of the applied prefix also occurs in
    -- the leftover suffix, so the target `τ` pins down the whole instance and the
    -- generator's random sampling cannot disagree with `Sm`. See
    -- `extended_subst_prefix_of_determined` for why this is the exact boundary of what
    -- a `Su`-free predicate can claim.
    (∀ σ ∈ schemeArgTys.take k, ∀ v ∈ σ.freeVars,
      v ∈ ((schemeArgTys.drop k).foldr
        (fun σ acc => LMonoTy.arrow σ acc) retTy).freeVars) ∧
    -- the applied prefix instantiates to the argument types under the *same* matcher
    -- (spec-level; no `unifyTypes`, no `Su`):
    concreteArgTys = (schemeArgTys.take k).map (LMonoTy.subst Sm)

/-- **Fully spec-shaped backward direction: `hEntry` eliminated.**

    Derives `IsPolyApp` from the typing judgment plus a *spec-level scheme-instance
    witness* — no `findPolymorphicOps`-membership hypothesis. The membership is
    *constructed* internally by `findPolymorphicOps_complete`, with its two guards
    discharged by `unifyTypes_matching_complete` (upstream's matching-completeness) and
    `extended_subst_guard2` (sampling is harmless). Covers both fragments: the
    fully-determined case and the sampling case (a scheme variable absent from the
    return suffix).

    The premises are now just three spec-level bundles:
    - `hInst : SchemeInstAt …` — the scheme-instance witness (scheme ∈ `pctx`, split
      point, matcher `Sm`), replacing the generator-internal `hEntry`. All freshening/
      decomposition witnesses are existentially bound inside it; the matcher is stated
      against `Sm` (no `Su`). Intended to be discharged from a caller's
      `OpsConsistentR F e`.
    - `hgen` — the generable-types context is non-empty (a cheap context fact).
    - the per-argument recursive-completeness bundle (`hArgsComplete`), as in
      `isPolyApp_of_hasType`; plus the `hAnnot`/`hArgLen` shape facts forced by `hwt`. -/
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
    -- Depth budget is `depth - 1`: arguments come from the generator at
    -- the smaller index (see `isPolyApp_of_hasType` / `mem_genArg_of_baseComplete`).
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
  -- The proof *derives* the two well-formedness conditions from scheme closedness,
  -- and does not assume them. `freshenBoundVars` cannot add a variable that clashes
  -- with `FV(τ)`, because it gets a `varsInUse` set that contains `FV(τ)`.
  obtain ⟨hdisjSuffix, hdisjBV⟩ :=
    schemeInstAt_freshening_disjoint fctx octx bctx τ boundVars monoTy freshBoundVars
      freshMonoTy schemeArgTys retTy k hclosed hfresh hdec
  -- Obtain the unifier from upstream's matching-completeness theorem.
  obtain ⟨Su, hunify, _hSupat⟩ :=
    unifyTypes_matching_complete _ τ Sm hdisjSuffix hmatch
  -- Discharge `guard2` for the sampled extension via `extended_subst_guard2`.
  have hg2 : LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars Su).zip sampledTys) ++ Su)
      ((schemeArgTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ :=
    extended_subst_guard2 freshBoundVars Su sampledTys _ τ _hSupat hdisjBV
  -- Bridge the caller's matcher `Sm` to the generator's `Su` on the applied prefix.
  -- Determinacy (`hdet`) is what makes this unconditional; see
  -- `extended_subst_prefix_of_determined`.
  have hcat : concreteArgTys = (schemeArgTys.take k).map
      (LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars Su).zip sampledTys) ++ Su)) :=
    hprefix.trans (extended_subst_prefix_of_determined schemeArgTys retTy τ k Sm Su
      freshBoundVars sampledTys hdisjSuffix hmatch _hSupat hdet)
  -- Construct the `findPolymorphicOps` membership.
  have hEntry : (name, concreteArgTys) ∈ findPolymorphicOps pctx τ
      (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs :=
    findPolymorphicOps_complete pctx τ _ sampledTys name boundVars monoTy hmem
      freshBoundVars freshMonoTy schemeArgTys retTy Su concreteArgTys k maxNumArgs
      hfresh hdec harity hk hunify (Or.inr hgen) hg2 hcat
  -- Reuse the `hEntry`-form backward direction.
  exact isPolyApp_of_hasType fctx octx pctx tvars bctx depth τ name annot args hwt
    sampledTys concreteArgTys hLen hValid hEntry hAnnot hArgLen hArgsComplete

/-- Completeness of `genLExpr`: an expression is in the support if it satisfies
    EITHER the `genLExprBase` completeness conditions OR it is a valid
    polymorphic operator application (`IsPolyApp`).

    The monomorphic Indir path is subsumed by Case 1: those expressions are
    reachable via the App rule in `genLExprBase` (the Indir rule is a
    distribution optimization, not a coverage extension). -/
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
  -- `genLExprBase` sits at weight 1 in the two-element `frequency`; both it and
  -- `genIndirPoly` are reachable regardless of the `dite` branch. In the
  -- Indir-candidates branch we exhibit the `frequency` witness explicitly via
  -- `mem_support_frequency_iff` (weight 1 for the base rule; weight 9's binary
  -- `pick` for the Indir/IndirPoly rules).
  rcases he with ⟨hwt, hnames, hvars, hats, hdepth⟩ | ⟨sampledTys, name, concreteArgTys, args, hLen, hValid, hEntry, hArgs, rfl⟩
  · -- Case 1: route through genLExprBase (reachable in both dite branches)
    have hbase := genLExprBase_complete fctx octx pctx tvars bctx depth τ hτ e hwt hnames hvars hats hdepth
    by_cases hops : (findOpsInCtx octx τ).length > 0
    · refine Or.inl ⟨hops, ?_⟩
      rw [← mem_support_iff, mem_support_frequency_iff]
      exact ⟨1, _, List.mem_cons_self, by omega, hbase⟩
    · exact Or.inr ⟨hops, (pick_mem_iff _).mpr (Or.inl hbase)⟩
  · -- Case 2: route through genIndirPoly (reachable in both dite branches)
    -- `IsPolyApp`'s argument clause is stated against exactly the generator
    -- `genLExpr` uses in argument position at this depth, so it *is* the `genArg`
    -- witness `genIndirPoly_complete` wants.
    have hindirpoly := genIndirPoly_complete fctx octx pctx tvars bctx depth τ
      maxNumArgs sampledTys hLen hValid name concreteArgTys hEntry _ args hArgs
    by_cases hops : (findOpsInCtx octx τ).length > 0
    · refine Or.inl ⟨hops, ?_⟩
      rw [← mem_support_iff, mem_support_frequency_iff]
      refine ⟨9, _, List.mem_cons_of_mem _ List.mem_cons_self, by omega, ?_⟩
      rw [mem_support_pick_iff]
      exact Or.inr hindirpoly
    · exact Or.inr ⟨hops, (pick_mem_iff _).mpr (Or.inr hindirpoly)⟩

/-- **Spec-shaped completeness for the polymorphic case.**

    A restatement of `genLExpr_complete` whose polymorphic disjunct is driven by
    the *typing judgment* `HasTypeA'` rather than by the generator-internal
    `IsPolyApp`. The polymorphic branch's premises are:

    - `hwt` — the term is a well-typed spine over a `pctx`-op node (spec-shaped);
    - `hEntry` — the split-point unification side-condition (see
      `isPolyApp_of_hasType`; discharged from upstream's
      `Constraints_unify_matching_complete` in the `…_fullySpecShaped` variant);
    - the per-argument recursive-completeness bundle.

    `IsPolyApp` is *derived* internally via `isPolyApp_of_hasType`, then discharged
    through the existing `genLExpr_complete`.

    ### Which one should I use?

    This theorem and `genLExpr_complete_poly_fullySpecShaped` have the *same*
    conclusion and differ in exactly one premise — with a consequence for their
    axiom footprints that is the main thing to weigh:

    | | this theorem | `…_fullySpecShaped` |
    |---|---|---|
    | unification premise | `hEntry` (a `findPolymorphicOps` membership) | `hInst : SchemeInstAt …` + `hgen` |
    | that premise is | a **generator internal** | **spec-level** (scheme, split point, matcher) |
    | axioms | `propext`, `Classical.choice`, `Quot.sound` | the same |

    Both are `sorry`-free and have the *same* axiom footprint: matching-completeness of
    Strata's unifier (`Constraints_unify_matching_complete`), which `…_fullySpecShaped`
    consumes, is proved upstream. The choice is therefore purely about which premise you
    would rather supply.

    **Prefer this one when you can discharge `hEntry` yourself.** `findPolymorphicOps`
    membership is a decidable list membership, so for a concrete `pctx`/`τ`/`sampledTys` it
    is provable by `decide` or by `simp [findPolymorphicOps]`.

    **Prefer `…_fullySpecShaped` when you want no generator internals in the
    hypotheses** — the honest "every well-typed spine is reachable" statement. -/
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
    -- Depth budget is `depth - 1`: arguments come from the generator at
    -- the smaller index (see `isPolyApp_of_hasType` / `mem_genArg_of_baseComplete`).
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

/-- **Fully spec-shaped polymorphic completeness: no `hEntry`.**

    Like `genLExpr_complete_poly_specShaped`, but the generator-internal
    `findPolymorphicOps`-membership hypothesis is *eliminated* — replaced by the
    spec-level scheme-instance witness of `isPolyApp_of_hasType_specShaped`. This is
    the strongest form of the result: every well-typed spine over a `pctx` scheme
    (meeting the recursive-completeness side conditions and scheme closedness) is
    reachable, with no generator internals in the hypotheses. The proof *derives* the
    well-formedness conditions for `freshenBoundVars` and does not assume them. For
    the details, see `schemeInstAt_freshening_disjoint`.

    ### Which one should I use?

    This theorem and `genLExpr_complete_poly_specShaped` have the *same* conclusion
    and differ in exactly one premise. The trade:

    | | this theorem | `…_specShaped` |
    |---|---|---|
    | unification premise | `hInst : SchemeInstAt …` + `hgen` | `hEntry` (a `findPolymorphicOps` membership) |
    | that premise is | **spec-level** (scheme, split point, matcher) | a **generator internal** |
    | split points covered | determined ones only (see `SchemeInstAt`) | all, including sampling |
    | axioms | `propext`, `Classical.choice`, `Quot.sound` | the same |

    Both are `sorry`-free and share the same axiom footprint. Eliminating `hEntry` means
    *constructing* that membership internally, which consumes
    `Constraints_unify_matching_complete` — matching-completeness of Strata's unifier, which
    is **proved upstream** (`Strata.DL.Lambda.LTyUnifyProps`), so it costs no extra axiom.

    **Prefer this one for the honest specification-level statement**, i.e. when the point is
    that no `findPolymorphicOps` reference appears in the hypotheses.

    **Prefer `…_specShaped`** if you would rather supply `hEntry` yourself — it is a
    decidable list membership, so `decide` or `simp [findPolymorphicOps]` settles it for
    concrete arguments, and it is the route that reaches the *sampling* split points
    `SchemeInstAt`'s determinacy conjunct excludes.

    `SchemeInstAt` is the intended discharge point for a caller's `OpsConsistentR F e`,
    whose `.op_in` constructor carries exactly this witness. That discharge is
    `schemeInstAt_of_opsConsistentR`, and
    `genLExpr_complete_poly_opsConsistentR` is this theorem with the premise already
    discharged — both in `HasTypeAGenOpsConsistent.lean`, which is where the
    `OpsConsistentR` judgment is available. -/
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
    -- Depth budget is `depth - 1`: arguments come from the generator at
    -- the smaller index (see `isPolyApp_of_hasType` / `mem_genArg_of_baseComplete`).
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


-- ── Polymorphic applications at every subterm position ────────────────
--
-- Formerly, `genLExpr_complete` had the shape
--
--     (base conditions) ∨ IsPolyApp …
--
-- and that disjunction *was* the positional incompleteness. `IsPolyApp` describes
-- a polymorphic application at the **root** of the generated term, so the theorem
-- said nothing about one sitting under an `ite` arm or a binder body. The scope
-- decision — factory applications at *every* subterm position — is therefore a
-- claim about where the polymorphic case may appear, and these results discharge it.
--
-- The key step is `genLExprBase_complete_polyApp`: a polymorphic application is in
-- **`genLExprBase`'s** own support, not merely `genLExpr`'s. Since the structural
-- rules (`ite`, `abs`, `quant`, `app`) all recurse into `genLExprBase`, the
-- polymorphic case then composes into each of those positions; the corollaries
-- below spell out three of them.
--
-- Scope note: these are stated at the `bool` target, the case where the
-- `frequency` branch list is longest and the witness arithmetic hardest. Because
-- the IndirPoly entry is the *last* element of every per-type branch list, the
-- other nine type cases differ only in the length of the `.tail` chain
-- (equivalently, the number of `right`s below); nothing else in the argument
-- changes.

open StrataGenerators.IndirSupport in
set_option maxHeartbeats 800000 in
/-- **The key step: a polymorphic factory application is in
    `genLExprBase`'s own support** — the statement the two-disjunct
    `genLExpr_complete` could not make.

    Its conclusion is about `genLExprBase … (n + 1) .bool`, so it composes with the
    structural rules: wherever `genLExprBase` recurses (an `ite` arm, an
    `abs`/`quant` body, `genApp`'s function or argument), *this* is available at
    that position. Formerly no such theorem existed, because `genLExprBase` had
    no rule that could instantiate a `∀`-scheme.

    Premises are `genIndirPoly_complete`'s, with the argument generator fixed to
    `genLExprBase … n` — which is what the new branch actually uses. -/
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
  -- First: the term is in `genIndirPolyCore`'s support at the argument generator
  -- the new branch supplies.
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
  -- Second: that branch is the last entry of `genLExprBase`'s `bool`/`n+1`
  -- `frequency` list, at weight 4. The generator has to be *named* in the witness:
  -- as a metavariable it is not determined by the membership goal alone.
  rw [norm_bool]
  simp only [genLExprBase]
  rw [mem_support_frequency_iff]
  refine ⟨4, fun () => genIndirPolyCore fctx octx pctx bctx LMonoTy.bool
    (genLExprBase fctx octx pctx tvars bctx n)
    (genLExprBase fctx octx pctx tvars bctx n LMonoTy.bool) 3, ?_, by omega, hcore⟩
  simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false]
  -- The IndirPoly entry is the final element of the eleven-branch list.
  right; right; right; right; right; right; right; right; right; right
  trivial

/-- **A polymorphic application under an `ite` arm.**

    Composition of `genLExprBase_complete_polyApp` with the structural `ite` rule,
    which draws both arms from `genLExprBase … n`. Formerly the analogous
    statement was unprovable: `genLExprBase` could not instantiate a `∀`-scheme, so
    no polymorphic call was reachable here at any depth — measured 0/400 on
    `corePartialOps`/`corePolyOps` for every target type tried. -/
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

    The `quant` rule generates its body via `genLExprBase … n` in the *extended*
    binder context `τ' :: bctx`, so `genLExprBase_complete_polyApp` applies there
    with `bctx := τ' :: bctx`. This is the binder case the scope decision calls out
    specifically. -/
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

-- ── Existential-depth completeness ────────────────────────────────────
--
-- `genLExprBase_complete` and `genLExpr_complete` are indexed by an explicit
-- `depth`, and their `hdepth : termDepth bctx e ≤ depth` premise ties the caller to
-- the generator's fuel accounting. A caller who only wants "this well-typed term is
-- reachable *somehow*" should not have to compute that.
--
-- The corollaries below quantify the depth existentially instead. They are strictly
-- weaker than the depth-indexed originals — `termDepth bctx e` is itself the witness
-- — so they are corollaries, not new arguments, and they cost nothing to maintain.
--
-- Why this is worth having: the depth-indexed statement's companion
-- bound (`genLExprBase_termDepth_bound`) is no longer tight. It reads
-- `termDepth e ≤ depthBudget K depth` rather than `≤ depth`, because a
-- fully-applied operator of arity `k` costs `k` levels of `termDepth`. So `hdepth`
-- is still *sufficient* for reachability but no longer *characterizes* it, and a
-- statement that never mentions a particular depth is insulated from that constant
-- — including from any future change to `K`.
--
-- Note what is NOT dropped: `AllTypesSimple` is existentially quantified, not
-- removed. It is not derivable from `HasTypeA'`, since it additionally pins down
-- bitvector widths, string alphabets, and the rational shapes the constant
-- generators actually emit. Only the *index* is existential.
--
-- The dual direction admits no such treatment: existentially quantifying
-- `termDepth_bound`'s conclusion (`∃ d, termDepth bctx e ≤ d`) is vacuous — it is
-- `⟨termDepth bctx e, Nat.le_refl _⟩` without inspecting the generator at all, and
-- holds for terms no depth can produce. The quantitative fuel-to-output link has to
-- stay depth-indexed; see `genLExprBase_termDepth_bound`.

/-- `AllTypesSimple`'s index is an *upper* bound on the type depths appearing in a
    term, so it is monotone: a term valid at index `n` is valid at `n + 1`. Every
    case is structural; the only real content is the `omega` on the
    `monoTyDepth τ ≤ n` side conditions. -/
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

/-- `AllTypesSimple` is monotone at `≤`, by iterating `allTypesSimple_mono`. This is
    what lets a single witness depth serve a whole term in the corollaries below:
    take the `max` of the type-depth index and the term depth. -/
theorem allTypesSimple_mono_le (tvars : List TyIdentifier) (m n : Nat) (bctx : BVarCtx)
    (e : LExpr') (hmn : m ≤ n) (h : AllTypesSimple tvars m bctx e) :
    AllTypesSimple tvars n bctx e := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · exact allTypesSimple_mono tvars k bctx e (ih (by omega))
    · rwa [(by omega : m = k + 1)] at h

/-- **Existential-depth completeness for `genLExprBase`.** Every well-typed term
    whose annotations are simple at *some* index is reachable at *some* depth — no
    `termDepth` computation required of the caller.

    The witness is `max m (termDepth bctx e)`: big enough for the term's own tree
    depth, and (via `allTypesSimple_mono_le`) at least the annotation index `m`. -/
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

/-- **Existential-depth completeness for `genLExpr`.** The `genLExpr`-level
    counterpart of `genLExprBase_complete_exists`, routed through
    `genLExpr_complete`'s base-conditions disjunct.

    Only the base disjunct is lifted, deliberately. `IsPolyApp`'s argument clause is
    stated against the depth-`match` generator (`genLExprBase … 0` at the floor,
    `genLExpr … n` above it), so raising `depth` *changes which generator the clause
    refers to* rather than merely relaxing a numeric bound. Monotonicity therefore
    does not come for free the way it does for `AllTypesSimple`/`termDepth`, and no
    claim is made here either way — it would need its own support-monotonicity lemma
    for `genLExpr`. For the polymorphic case use `genLExprBase_complete_polyApp`
    (which places it inside `genLExprBase`, hence at every subterm position) or the
    `…_specShaped` wrappers. -/
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
