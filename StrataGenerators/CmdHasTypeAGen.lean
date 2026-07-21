import StrataGenerators.SetGen
import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString

/-!
# Generator of well-typed commands satisfying `CmdHasTypeA`

A Basalt `SetGen`-based random generator for well-typed Strata imperative
commands (`Cmd Expression`) that satisfy the `CmdHasTypeA` relation.

## Contents

- Support characterization: `genCmd_support_iff`
- Full soundness: `genCmd_sound`
- Full completeness: `genCmd_complete`
- Per-constructor soundness and completeness lemmas

## Approach

The generator works with a flat `VarCtx` (list of name-type pairs). The full
soundness theorem is stated compositionally: it takes expression-level soundness
(`genLExpr` produces well-typed expressions) and freshness properties of
`genFreshName` as hypotheses, then concludes that every generated command
satisfies `CmdHasTypeA`.
-/

-- ── VarCtx ↔ TContext correspondence ─────────────────────────────────

/-- A `VarCtx` corresponds to a `TContext` if every lookup agrees: entries in
    `ctx` map to monomorphic types `forAll [] mty` in `Γ`, and variables not
    in `ctx` are absent from `Γ`. -/
def VarCtxCorresponds (ctx : VarCtx) (Γ : TContext Unit) : Prop :=
  (∀ (x : Identifier Unit) mty, List.Mem (x, mty) ctx →
    Γ.types.find? x = some (.forAll [] mty)) ∧
  (∀ (x : Identifier Unit), VarCtx.isFresh ctx x = true →
    Γ.types.find? x = none)

-- ── Per-constructor soundness ────────────────────────────────────────

/-- Soundness of assert: if `e` has type `bool` (in the empty bvar context),
    then `.assert "" e default` satisfies `CmdHasTypeA C Γ _ Γ`. -/
theorem genAssertCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.assert "" e default) Γ :=
  CmdHasType'.assert Γ "" e default hwt

/-- Soundness of assume: if `e` has type `bool`, then `.assume "" e default`
    satisfies `CmdHasTypeA C Γ _ Γ`. -/
theorem genAssumeCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.assume "" e default) Γ :=
  CmdHasType'.assume Γ "" e default hwt

/-- Soundness of cover: if `e` has type `bool`, then `.cover "" e default`
    satisfies `CmdHasTypeA C Γ _ Γ`. -/
theorem genCoverCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.cover "" e default) Γ :=
  CmdHasType'.cover Γ "" e default hwt

/-- Soundness of set_det: if `x` has monotype `mty` in `Γ` and `e` has type
    `mty`, then `.set x (det e) default` satisfies `CmdHasTypeA C Γ _ Γ`. -/
theorem genSetDet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfind : Γ.types.find? x = some (.forAll [] mty))
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e mty) :
    CmdHasTypeA C Γ (.set x (.det e) default) Γ :=
  CmdHasType'.set_det Γ x mty e default hfind hwt

/-- Soundness of set_nondet: if `x` has monotype `mty` in `Γ`,
    then `.set x nondet default` satisfies `CmdHasTypeA C Γ _ Γ`. -/
theorem genSetNondet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfind : Γ.types.find? x = some (.forAll [] mty)) :
    CmdHasTypeA C Γ (.set x .nondet default) Γ :=
  CmdHasType'.set_nondet Γ x mty default hfind

/-- A monomorphic type scheme `∀ []. mty` (no bound variables) is trivially
    `RigidAnnotCompat` with itself: opening with an empty list of type arguments
    yields `mty` unchanged (the empty substitution is the identity), so the
    compatibility check reduces to reflexivity. -/
private theorem rigidAnnotCompat_forAll_nil (mty : LMonoTy) :
    ∀ {aliases rigidVars},
    RigidAnnotCompat aliases rigidVars ((LTy.forAll [] mty).openFull []) mty := by
  intro aliases rigidVars
  have h : (LTy.forAll [] mty).openFull [] = mty := by
    simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
    exact LMonoTy.subst_emptyS Subst.hasEmptyScopes_emptyScope
  rw [h]; exact RigidAnnotCompat.of_eq

/-- Soundness of init_det: if `x` is fresh in `Γ`, `x ∉ vars(e)`, and `e`
    has type `mty`, then `init x (.forAll [] mty) (det e) default` is well-typed
    with output context `{Γ with types := Γ.types.insert x (.forAll [] mty)}`. -/
theorem genInitDet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfresh : Γ.types.find? x = none)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e mty)
    (hnovar : x ∉ HasVarsPure.getVars (P := Expression) e) :
    CmdHasTypeA C Γ (.init x (.forAll [] mty) (.det e) default)
      { Γ with types := Γ.types.insert x (.forAll [] mty) } :=
  CmdHasType'.init_det Γ x (.forAll [] mty) e mty [] default hfresh hnovar rfl (rigidAnnotCompat_forAll_nil mty) hwt

/-- Soundness of init_nondet: if `x` is fresh in `Γ`,
    then `init x (.forAll [] mty) nondet default` is well-typed. -/
theorem genInitNondet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfresh : Γ.types.find? x = none) :
    CmdHasTypeA C Γ (.init x (.forAll [] mty) .nondet default)
      { Γ with types := Γ.types.insert x (.forAll [] mty) } :=
  CmdHasType'.init_nondet Γ x (.forAll [] mty) mty [] default hfresh rfl (rigidAnnotCompat_forAll_nil mty)

-- ── Support characterization of genCmd ──────────────────────────────

/-- Full support characterization of `genCmd`: a result is in the support iff
    it comes from one of the sub-generators. This is the combined
    soundness/completeness theorem at the syntactic level (before interpreting
    against `CmdHasTypeA`). -/
theorem genCmd_support_iff
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (r : GenCmdResult) :
    r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) ↔
    (r ∈ SetGen.support (genInitDet (G := SetGen.Set) fctx octx tvars ctx depth depth) ∨
     r ∈ SetGen.support (genInitNondet (G := SetGen.Set) tvars ctx depth) ∨
     (∃ h : ctx.length > 0, r ∈ SetGen.support (genSetDet (G := SetGen.Set) fctx octx tvars ctx depth h)) ∨
     (∃ h : ctx.length > 0, r ∈ SetGen.support (genSetNondet (G := SetGen.Set) ctx h)) ∨
     r ∈ SetGen.support (genAssertCmd (G := SetGen.Set) fctx octx tvars ctx depth) ∨
     r ∈ SetGen.support (genAssumeCmd (G := SetGen.Set) fctx octx tvars ctx depth) ∨
     r ∈ SetGen.support (genCoverCmd (G := SetGen.Set) fctx octx tvars ctx depth)) := by
  simp only [genCmd, mem_support_dite_iff]
  constructor
  · intro hr
    rcases hr with ⟨h, hr⟩ | ⟨hne, hr⟩
    · rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)] at hr
      obtain ⟨w, g, hg, _, hr⟩ := hr
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ <;>
        subst heq <;>
        first
        | exact Or.inl hr
        | exact Or.inr (Or.inl hr)
        | exact Or.inr (Or.inr (Or.inl ⟨h, hr⟩))
        | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hr⟩)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
    · rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)] at hr
      obtain ⟨w, g, hg, _, hr⟩ := hr
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ <;>
        subst heq <;>
        first
        | exact Or.inl hr
        | exact Or.inr (Or.inl hr)
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
  · intro hr
    rcases hr with hr | (hr | (⟨h, hr⟩ | (⟨h, hr⟩ | (hr | (hr | hr)))))
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .head _, by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨3, _, .head _, by omega, hr⟩⟩
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨1, _, .tail _ (.head _), by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨1, _, .tail _ (.head _), by omega, hr⟩⟩
    · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨3, _, .tail _ (.tail _ (.head _)), by omega, hr⟩⟩
    · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩⟩
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.head _)), by omega, hr⟩⟩
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩⟩
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, hr⟩⟩

-- ── Freshness proof for genFreshName ────────────────────────────────

/-- If no entry in `ctx` has key equal to `x`, then `find?` returns `none`. -/
private theorem VarCtx.find?_none_of_ne_all (ctx : VarCtx) (x : Identifier Unit)
    (h : ∀ entry : Identifier Unit × LMonoTy, List.Mem entry ctx → entry.1 ≠ x) :
    VarCtx.find? ctx x = none := by
  unfold VarCtx.find?
  apply Map.find?_none_of_not_mem_keys'
  intro hmem
  rw [Map.keys_eq_map_fst] at hmem
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
  exact h entry hentry heq

/-- Strings of different lengths are unequal. -/
private theorem String.ne_of_length_ne {s₁ s₂ : String} (h : s₁.length ≠ s₂.length) :
    s₁ ≠ s₂ := fun heq => absurd (congrArg String.length heq) h

/-- The foldl-max accumulator is monotonically non-decreasing. -/
private theorem foldl_max_length_ge_init (xs : List String) (init : Nat) :
    init ≤ xs.foldl (fun acc n => max acc n.length) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- The foldl-max result is at least as large as the length of any member. -/
private theorem foldl_max_length_ge_of_mem (xs : List String) (nm : String)
    (h : nm ∈ xs) (init : Nat) :
    nm.length ≤ xs.foldl (fun acc n => max acc n.length) init := by
  induction xs generalizing init with
  | nil => exact absurd h (by exact List.not_mem_nil)
  | cons hd tl ih =>
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_length_ge_init tl _)
    | tail _ hmem => exact ih hmem _

/-- Any name strictly longer than every name in `ctx` is fresh in `ctx`. -/
private theorem isFresh_of_maxlen_lt (ctx : VarCtx) (s : String)
    (h : (VarCtx.names ctx).foldl (fun acc nm => max acc nm.length) 0 < s.length) :
    VarCtx.isFresh ctx ⟨s, ()⟩ = true := by
  unfold VarCtx.isFresh
  have hfind : VarCtx.find? ctx ⟨s, ()⟩ = none := by
    apply VarCtx.find?_none_of_ne_all
    intro entry hmem
    -- Identifiers are equal iff their names are; derive name inequality by length.
    have hname_ne : entry.1.name ≠ s := by
      apply String.ne_of_length_ne
      have hname_mem : entry.1.name ∈ VarCtx.names ctx :=
        List.mem_map.mpr ⟨entry, hmem, rfl⟩
      have hle := foldl_max_length_ge_of_mem (VarCtx.names ctx) entry.1.name hname_mem 0
      omega
    intro heq
    exact hname_ne (congrArg Identifier.name heq)
  simp [hfind]

/-- `fallbackFreshName ctx` has length one greater than the longest context name. -/
private theorem fallbackFreshName_length (ctx : VarCtx) :
    (fallbackFreshName ctx).length =
      (VarCtx.names ctx).foldl (fun acc nm => max acc nm.length) 0 + 1 := by
  simp [fallbackFreshName, String.length_ofList, List.length_replicate]

/-- `dodgeKeyword` never shortens its argument: it either returns it unchanged or
    appends `_`. -/
private theorem length_le_dodgeKeyword (s : String) :
    s.length ≤ (dodgeKeyword s).length := by
  unfold dodgeKeyword
  split
  · simp [String.length_append]
  · exact Nat.le_refl _

/-- `fallbackFreshName ctx` is fresh in `ctx` because it is strictly longer
    than every name in the context. -/
private theorem fallbackFreshName_isFresh (ctx : VarCtx) :
    VarCtx.isFresh ctx ⟨fallbackFreshName ctx, ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  rw [fallbackFreshName_length]; omega

/-- `dodgeKeyword (fallbackFreshName ctx)` is also fresh: `dodgeKeyword` only ever
    lengthens the already-long-enough fallback name, so it too exceeds every
    context name in length. -/
private theorem dodgeKeyword_fallbackFreshName_isFresh (ctx : VarCtx) :
    VarCtx.isFresh ctx ⟨dodgeKeyword (fallbackFreshName ctx), ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  have h := length_le_dodgeKeyword (fallbackFreshName ctx)
  rw [fallbackFreshName_length] at h
  omega

/-- Every name in the support of `genFreshName ctx` is fresh in `ctx` (i.e. its
    identifier `⟨name, ()⟩` is absent from the context). -/
theorem genFreshName_produces_fresh (ctx : VarCtx) :
    ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
      VarCtx.isFresh ctx ⟨name, ()⟩ = true := by
  intro name hmem
  simp only [genFreshName, mem_support_bind_iff] at hmem
  obtain ⟨s, _, hname⟩ := hmem
  simp only [mem_support_ite_iff, mem_support_pure_iff] at hname
  rcases hname with ⟨hfresh, rfl⟩ | ⟨_, rfl⟩
  · exact hfresh
  · exact dodgeKeyword_fallbackFreshName_isFresh ctx

/-- **Keyword-freedom of `genFreshName`.** Every name in the support of
    `genFreshName ctx` is a non-keyword: both exit paths (the dodged random
    candidate and the dodged fallback) pass through `dodgeKeyword`, which never
    returns a reserved Core keyword. So the variable names `genInitDet` /
    `genInitNondet` bind in `init` commands are never reserved words the Core
    parser would reject in identifier position. -/
theorem genFreshName_not_keyword (ctx : VarCtx) :
    ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
      isReservedKeyword name = false := by
  intro name hmem
  simp only [genFreshName, mem_support_bind_iff] at hmem
  obtain ⟨s, _, hname⟩ := hmem
  simp only [mem_support_ite_iff, mem_support_pure_iff] at hname
  rcases hname with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact StrataGenerators.Function.dodgeKeyword_not_keyword s
  · exact StrataGenerators.Function.dodgeKeyword_not_keyword _

-- ── Full soundness of genCmd ─────────────────────────────────────────

/-- Predicate asserting that `genLExpr` is sound at type `τ`: every expression
    in the generator's support is well-typed. This is proved as `genLExpr_sound`
    in `HasTypeAGen.lean`; we take it as a hypothesis here. -/
def GenLExprSound (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : Prop :=
  ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ) →
    LExpr.HasTypeA (T := LExprParams') [] e τ

/-- Predicate asserting that fresh names generated by `genFreshName` do not
    appear as free variables in any expression generated by `genLExpr`.
    This is a consequence of the generator's structure (fvars are drawn from
    `fctx` via `pickFVar`, and fresh names are random strings unlikely to
    collide) but has not yet been proved as a standalone theorem. -/
def FreshNamesDisjointFromExprs (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (ctx : VarCtx) (depth : Nat) : Prop :=
  ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
    ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ) →
      (⟨name, ()⟩ : Identifier Unit) ∉ HasVarsPure.getVars (P := Expression) e

/-- Full soundness of `genCmd`: every result in the generator's support produces
    a well-typed command. The output context `Γ'` satisfies `CmdHasTypeA C Γ cmd Γ'`.

    The freshness-in-Γ condition is derived from the proven `genFreshName_produces_fresh`
    and `hCorr`. The only unproven hypothesis is `hDisjoint`, which asserts that
    fresh names do not collide with free variables in generated expressions. -/
theorem genCmd_sound
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (hCorr : VarCtxCorresponds ctx Γ)
    (hExprSound : GenLExprSound fctx octx tvars depth)
    (hDisjoint : FreshNamesDisjointFromExprs fctx octx tvars ctx depth)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth)) :
    ∃ Γ', CmdHasTypeA C Γ r.cmd Γ' := by
  rw [genCmd_support_iff] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, e, he, rfl⟩ := hr
    have hfreshΓ := hCorr.2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    have hnovar := hDisjoint name hname mty e he
    have hwt := hExprSound mty e he
    exact ⟨_, CmdHasType'.init_det Γ ⟨name, ()⟩ _ e mty [] default hfreshΓ hnovar rfl (rigidAnnotCompat_forAll_nil mty) hwt⟩
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, _, rfl⟩ := hr
    have hfreshΓ := hCorr.2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    exact ⟨_, CmdHasType'.init_nondet Γ ⟨name, ()⟩ _ mty [] default hfreshΓ rfl (rigidAnnotCompat_forAll_nil mty)⟩
  · -- set_det
    simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, e, he, rfl⟩ := hr
    have hfind := hCorr.1 name mty hmem
    have hwt := hExprSound mty e he
    exact ⟨Γ, CmdHasType'.set_det Γ name mty e default hfind hwt⟩
  · -- set_nondet
    simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, rfl⟩ := hr
    have hfind := hCorr.1 name mty hmem
    exact ⟨Γ, CmdHasType'.set_nondet Γ name mty default hfind⟩
  · -- assert
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨e, he, rfl⟩ := hr
    have hwt := hExprSound .bool e he
    exact ⟨Γ, CmdHasType'.assert Γ "" e default hwt⟩
  · -- assume
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨e, he, rfl⟩ := hr
    have hwt := hExprSound .bool e he
    exact ⟨Γ, CmdHasType'.assume Γ "" e default hwt⟩
  · -- cover
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨e, he, rfl⟩ := hr
    have hwt := hExprSound .bool e he
    exact ⟨Γ, CmdHasType'.cover Γ "" e default hwt⟩

-- ── Full completeness of genCmd ──────────────────────────────────────

/-- Predicate asserting that `genLExpr` is complete at type `τ`: every well-typed
    expression satisfying the generator's side conditions is in the support.
    This is proved as `genLExprBase_complete` in `HasTypeAGen.lean` (which
    requires Mathlib); we take it as a hypothesis here. -/
def GenLExprComplete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : Prop :=
  ∀ τ e, LExpr.HasTypeA (T := LExprParams') [] e τ →
    e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ)

/-- Full completeness of `genCmd` with respect to `CmdHasTypeA`: if a command
    is well-typed and its sub-components are reachable by the respective
    sub-generators, then it is in `genCmd`'s support.

    The proof proceeds by inversion on the `CmdHasTypeA` derivation. The
    hypotheses capture what the generator requires beyond well-typedness:
    - `hExprComplete`: well-typed expressions are in `genLExpr`'s support
    - `hNameReach`: the name of any init/set target is reachable
    - `hTyReach`: the type of any init target is in `genLMonoTy`'s support
    - `hVarInCtx`: the target of any set command exists in `ctx`

    The generator fixes labels to `""` and metadata to `default`; the
    conclusion states that the generator produces a command with the same
    *expression* and *variable* content (but possibly different label/metadata). -/
theorem genCmd_complete
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ Γ' : TContext Unit)
    (cmd : Cmd Expression)
    (hwt : CmdHasTypeA C Γ cmd Γ')
    (hExprComplete : GenLExprComplete fctx octx tvars depth)
    (hNameReach : ∀ x : Identifier Unit,
      (∃ xty eOrNd md, cmd = .init x xty eOrNd md) →
      x.name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx))
    (hTyReach : ∀ (mty : LMonoTy),
      mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth))
    (hVarInCtx : ∀ (x : Identifier Unit) (mty : LMonoTy),
      Γ.types.find? x = some (.forAll [] mty) →
      List.Mem (x, mty) ctx) :
    ∃ r : GenCmdResult,
      r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) ∧
      CmdHasTypeA C Γ r.cmd Γ' := by
  cases hwt with
  | init_det x xty e mty tys md hfresh hnovar _ _ hexpr =>
    have hname := hNameReach x ⟨xty, .det e, md, rfl⟩
    have hmty := hTyReach mty
    have he := hExprComplete mty e hexpr
    have hinSupport : (⟨.init x (.forAll [] mty) (.det e) default, ctx.insert ⟨x.name, ()⟩ mty⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inl (by
        simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨x.name, hname, mty, hmty, e, he, rfl⟩))
    exact ⟨_, hinSupport, CmdHasType'.init_det _ x _ e mty [] default hfresh hnovar rfl (rigidAnnotCompat_forAll_nil mty) hexpr⟩
  | init_nondet x xty mty tys md hfresh _ _ =>
    have hname := hNameReach x ⟨xty, .nondet, md, rfl⟩
    have hmty := hTyReach mty
    have hinSupport : (⟨.init x (.forAll [] mty) .nondet default, ctx.insert ⟨x.name, ()⟩ mty⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inl (by
        simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨x.name, hname, mty, hmty, rfl⟩)))
    exact ⟨_, hinSupport, CmdHasType'.init_nondet _ x _ mty [] default hfresh rfl (rigidAnnotCompat_forAll_nil mty)⟩
  | set_det x mty e md hfind hexpr =>
    have hentry := hVarInCtx x mty hfind
    have he := hExprComplete mty e hexpr
    have hinSupport : (⟨.set x (.det e) default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inl ⟨List.length_pos_of_mem hentry, by
        simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_elements_iff]
        exact ⟨(x, mty), hentry, e, he, rfl⟩⟩)))
    exact ⟨_, hinSupport, CmdHasType'.set_det _ x mty e default hfind hexpr⟩
  | set_nondet x mty md hfind =>
    have hentry := hVarInCtx x mty hfind
    have hinSupport : (⟨.set x .nondet default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨List.length_pos_of_mem hentry, by
        simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_elements_iff]
        exact ⟨(x, mty), hentry, rfl⟩⟩))))
    exact ⟨_, hinSupport, CmdHasType'.set_nondet _ x mty default hfind⟩
  | assert l e md hexpr =>
    have he := hExprComplete .bool e hexpr
    have hinSupport : (⟨.assert "" e default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨e, he, rfl⟩))))))
    exact ⟨_, hinSupport, CmdHasType'.assert _ "" e default hexpr⟩
  | assume l e md hexpr =>
    have he := hExprComplete .bool e hexpr
    have hinSupport : (⟨.assume "" e default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨e, he, rfl⟩)))))))
    exact ⟨_, hinSupport, CmdHasType'.assume _ "" e default hexpr⟩
  | cover l e md hexpr =>
    have he := hExprComplete .bool e hexpr
    have hinSupport : (⟨.cover "" e default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
        simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨e, he, rfl⟩)))))))
    exact ⟨_, hinSupport, CmdHasType'.cover _ "" e default hexpr⟩

-- ── Chained typing for command sequences ────────────────────────────

/-- Well-typedness for a sequence of commands: each command is typed from one
    context to the next, forming a chain `Γ₀ → Γ₁ → ... → Γₙ`. -/
inductive CmdsHasTypeA (C : LContext CoreLParams) :
    TContext Unit → List (Cmd Expression) → TContext Unit → Prop where
  | nil : ∀ Γ, CmdsHasTypeA C Γ [] Γ
  | cons : ∀ Γ Γ' Γ'' cmd cmds,
      CmdHasTypeA C Γ cmd Γ' →
      CmdsHasTypeA C Γ' cmds Γ'' →
      CmdsHasTypeA C Γ (cmd :: cmds) Γ''

/-- A uniform soundness environment packages the hypotheses needed to prove
    `genCmd_sound` at *any* context reachable during sequence generation.
    This bundles:
    - A way to produce a `TContext` from any `VarCtx`
    - Correspondence between them
    - Expression-level soundness (context-independent)
    - Disjointness of fresh names from expression fvars at every reachable context -/
structure GenCmdSoundEnv (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (C : LContext CoreLParams) where
  /-- Produce the semantic `TContext` for any flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The correspondence holds for every context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- Expression soundness (does not depend on the variable context). -/
  exprSound : GenLExprSound fctx octx tvars depth
  /-- Fresh names do not appear as free variables in generated expressions. -/
  freshDisjoint : ∀ ctx, FreshNamesDisjointFromExprs fctx octx tvars ctx depth
  /-- The `TContext` produced for `ctx.insert x mty` equals the insertion
      into the `TContext` for `ctx`. This ensures the output `Γ'` from an `init`
      command matches what `toTCtx` produces for the extended `VarCtx`. -/
  toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
    toTCtx (ctx.insert x mty) =
      { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }

/-- Lifted soundness of `genCmd` using a `GenCmdSoundEnv`: every result in the
    generator's support produces a command typed from `env.toTCtx ctx` to
    `env.toTCtx r.outCtx`. This follows the same case analysis as `genCmd_sound`
    but additionally shows the output context matches `toTCtx` applied to the
    generator's output `VarCtx`. -/
theorem genCmd_sound_env
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams)
    (env : GenCmdSoundEnv fctx octx tvars depth C)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth)) :
    CmdHasTypeA C (env.toTCtx ctx) r.cmd (env.toTCtx r.outCtx) := by
  rw [genCmd_support_iff] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, e, he, rfl⟩ := hr
    have hfreshΓ := (env.corr ctx).2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    have hnovar := (env.freshDisjoint ctx) name hname mty e he
    have hwt := env.exprSound mty e he
    rw [env.toTCtx_insert]
    exact CmdHasType'.init_det _ ⟨name, ()⟩ _ e mty [] default hfreshΓ hnovar rfl (rigidAnnotCompat_forAll_nil mty) hwt
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, _, rfl⟩ := hr
    have hfreshΓ := (env.corr ctx).2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    rw [env.toTCtx_insert]
    exact CmdHasType'.init_nondet _ ⟨name, ()⟩ _ mty [] default hfreshΓ rfl (rigidAnnotCompat_forAll_nil mty)
  · -- set_det
    simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, e, he, rfl⟩ := hr
    have hfind := (env.corr ctx).1 name mty hmem
    have hwt := env.exprSound mty e he
    exact CmdHasType'.set_det _ name mty e default hfind hwt
  · -- set_nondet
    simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, rfl⟩ := hr
    have hfind := (env.corr ctx).1 name mty hmem
    exact CmdHasType'.set_nondet _ name mty default hfind
  · -- assert
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨e, he, rfl⟩ := hr
    exact CmdHasType'.assert _ "" e default (env.exprSound .bool e he)
  · -- assume
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨e, he, rfl⟩ := hr
    exact CmdHasType'.assume _ "" e default (env.exprSound .bool e he)
  · -- cover
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨e, he, rfl⟩ := hr
    exact CmdHasType'.cover _ "" e default (env.exprSound .bool e he)

/-- Soundness of `genCmds`: every command sequence in the generator's support
    satisfies the chained `CmdsHasTypeA` relation.

    The proof proceeds by induction on the fuel `n`. At each step, we use
    `genCmd_sound_env` to type the head command, then invoke the inductive
    hypothesis on the tail with the updated context. -/
theorem genCmds_sound
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (n : Nat)
    (C : LContext CoreLParams)
    (env : GenCmdSoundEnv fctx octx tvars depth C)
    (result : List (Cmd Expression) × VarCtx)
    (hr : result ∈ SetGen.support (genCmds (G := SetGen.Set) fctx octx tvars ctx depth n)) :
    CmdsHasTypeA C (env.toTCtx ctx) result.1 (env.toTCtx result.2) := by
  induction n generalizing ctx result with
  | zero =>
    simp only [genCmds, mem_support_pure_iff] at hr
    subst hr
    exact CmdsHasTypeA.nil _
  | succ n ih =>
    simp only [genCmds, mem_support_bind_iff] at hr
    obtain ⟨⟨cmd, ctx'⟩, hcmd, rest_hr⟩ := hr
    dsimp only [GenCmdResult.outCtx, GenCmdResult.cmd] at rest_hr
    obtain ⟨⟨cmds, ctx''⟩, hcmds, hpure⟩ := rest_hr
    simp only [mem_support_pure_iff] at hpure
    have heq : result = (cmd :: cmds, ctx'') := by
      cases hpure; rfl
    subst heq
    have htyCmd := genCmd_sound_env fctx octx tvars ctx depth C env ⟨cmd, ctx'⟩ hcmd
    exact CmdsHasTypeA.cons _ _ _ cmd cmds htyCmd (ih ctx' (cmds, ctx'') hcmds)

-- ── Quick test ────────────────────────────────────────────────────────

open Std in
instance instToFormatUnitCmdHasTypeAGen : ToFormat Unit where
  format _ := .nil

#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨cmd, _⟩ ← genCmd [] [] [] [] 2
  IO.println <| Std.format cmd |>.pretty : IO Unit)

#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨cmd, ctx'⟩ ← genCmd [] [] [] [(⟨"x", ()⟩, .int), (⟨"y", ()⟩, .bool)] 2
  IO.println <| s!"{Std.format cmd |>.pretty} -- ctx: {ctx'}" : IO Unit)
