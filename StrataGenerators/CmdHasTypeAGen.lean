import StrataGenerators.SetGen
import StrataGenerators.CmdHasTypeAGen.Core

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen

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
satisfies `CmdHasTypeA`. This avoids the `List.Forall₂` import conflict with
Mathlib (where `genLExpr_sound` is proved).
-/

-- ── VarCtx ↔ TContext correspondence ─────────────────────────────────

/-- A `VarCtx` corresponds to a `TContext` if every lookup agrees: entries in
    `ctx` map to monomorphic types `forAll [] mty` in `Γ`, and variables not
    in `ctx` are absent from `Γ`. -/
def VarCtxCorresponds (ctx : VarCtx) (Γ : TContext Unit) : Prop :=
  (∀ x mty, (x, mty) ∈ ctx →
    Γ.types.find? (⟨x, ()⟩ : Identifier Unit) = some (.forAll [] mty)) ∧
  (∀ x, VarCtx.isFresh ctx x = true →
    Γ.types.find? (⟨x, ()⟩ : Identifier Unit) = none)

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

-- ── Auxiliary lemma for List.getD ────────────────────────────────────

/-- If `idx < xs.length`, then `xs.getD idx d` is a member of `xs`. -/
private theorem List.getD_mem_of_lt {xs : List α} {idx : Nat} {d : α}
    (h : idx < xs.length) : xs.getD idx d ∈ xs := by
  simp only [List.getD]
  have hget := List.getElem?_eq_getElem h
  rw [hget]
  exact List.getElem_mem h

-- ── Full soundness of genCmd ─────────────────────────────────────────

/-- Predicate asserting that `genLExpr` is sound at type `τ`: every expression
    in the generator's support is well-typed. This is proved as `genLExpr_sound`
    in `HasTypeAGen.lean` (which requires Mathlib); we take it as a hypothesis
    here to avoid the `List.Forall₂` import conflict. -/
def GenLExprSound (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : Prop :=
  ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ) →
    LExpr.HasTypeA (T := LExprParams') [] e τ

/-- Predicate asserting that `genFreshName` produces names that are fresh in the
    `TContext` (when `VarCtxCorresponds` holds) and that do not appear as free
    variables in any expression generated by `genLExpr`. -/
def GenFreshNameSound (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (Γ : TContext Unit) (depth : Nat) : Prop :=
  ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
    (Γ.types.find? (⟨name, ()⟩ : Identifier Unit) = none) ∧
    (∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ) →
      (⟨name, ()⟩ : Identifier Unit) ∉ HasVarsPure.getVars (P := Expression) e)

/-- Full soundness of `genCmd`: every result in the generator's support produces
    a well-typed command. The output context `Γ'` satisfies `CmdHasTypeA C Γ cmd Γ'`.

    This theorem is stated compositionally:
    - `hExprSound` asserts expression-level soundness (proved in `HasTypeAGen.lean`)
    - `hFresh` asserts freshness properties of `genFreshName`
    - `hCorr` asserts that the flat `VarCtx` corresponds to the semantic `TContext`

    Under these hypotheses, every generated command is well-typed. -/
theorem genCmd_sound
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (hCorr : VarCtxCorresponds ctx Γ)
    (hExprSound : GenLExprSound fctx octx tvars depth)
    (hFresh : GenFreshNameSound fctx octx tvars ctx Γ depth)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth)) :
    -- TODO: change this from Γ' to r.ctx
    ∃ Γ', CmdHasTypeA C Γ r.cmd Γ' := by
  rw [genCmd_support_iff] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, e, he, rfl⟩ := hr
    have ⟨hfreshΓ, hnovar⟩ := hFresh name hname
    have hwt := hExprSound mty e he
    exact ⟨_, CmdHasType'.init_det Γ ⟨name, ()⟩ _ e mty [] default hfreshΓ (hnovar mty e he) rfl (rigidAnnotCompat_forAll_nil mty) hwt⟩
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, _, rfl⟩ := hr
    have ⟨hfreshΓ, _⟩ := hFresh name hname
    exact ⟨_, CmdHasType'.init_nondet Γ ⟨name, ()⟩ _ mty [] default hfreshΓ rfl (rigidAnnotCompat_forAll_nil mty)⟩
  · -- set_det
    simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_choose_iff] at hr
    obtain ⟨idx, ⟨_, hidx⟩, e, he, rfl⟩ := hr
    have hlt : idx.down < ctx.length := by omega
    have hmem := List.getD_mem_of_lt (d := ("", LMonoTy.bool)) hlt
    have hfind := hCorr.1 (ctx.getD idx.down ("", .bool)).1 (ctx.getD idx.down ("", .bool)).2 hmem
    have hwt := hExprSound (ctx.getD idx.down ("", .bool)).2 e he
    exact ⟨Γ, CmdHasType'.set_det Γ ⟨(ctx.getD idx.down ("", .bool)).1, ()⟩
      (ctx.getD idx.down ("", .bool)).2 e default hfind hwt⟩
  · -- set_nondet
    simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_choose_iff] at hr
    obtain ⟨idx, ⟨_, hidx⟩, rfl⟩ := hr
    have hlt : idx.down < ctx.length := by omega
    have hmem := List.getD_mem_of_lt (d := ("", LMonoTy.bool)) hlt
    have hfind := hCorr.1 (ctx.getD idx.down ("", .bool)).1 (ctx.getD idx.down ("", .bool)).2 hmem
    exact ⟨Γ, CmdHasType'.set_nondet Γ ⟨(ctx.getD idx.down ("", .bool)).1, ()⟩
      (ctx.getD idx.down ("", .bool)).2 default hfind⟩
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
      ∃ idx, idx < ctx.length ∧
        ctx.getD idx ("", .bool) = (x.name, mty)) :
    ∃ r : GenCmdResult,
      r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) ∧
      CmdHasTypeA C Γ r.cmd Γ' := by
  cases hwt with
  | init_det x xty e mty tys md hfresh hnovar _ _ hexpr =>
    have hname := hNameReach x ⟨xty, .det e, md, rfl⟩
    have hmty := hTyReach mty
    have he := hExprComplete mty e hexpr
    have hinSupport : (⟨.init x (.forAll [] mty) (.det e) default, (x.name, mty) :: ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inl (by
        simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨x.name, hname, mty, hmty, e, he, rfl⟩))
    exact ⟨_, hinSupport, CmdHasType'.init_det _ x _ e mty [] default hfresh hnovar rfl (rigidAnnotCompat_forAll_nil mty) hexpr⟩
  | init_nondet x xty mty tys md hfresh _ _ =>
    have hname := hNameReach x ⟨xty, .nondet, md, rfl⟩
    have hmty := hTyReach mty
    have hinSupport : (⟨.init x (.forAll [] mty) .nondet default, (x.name, mty) :: ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inl (by
        simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨x.name, hname, mty, hmty, rfl⟩)))
    exact ⟨_, hinSupport, CmdHasType'.init_nondet _ x _ mty [] default hfresh rfl (rigidAnnotCompat_forAll_nil mty)⟩
  | set_det x mty e md hfind hexpr =>
    have ⟨idx, hidx, hentry⟩ := hVarInCtx x mty hfind
    have he := hExprComplete mty e hexpr
    have hinSupport : (⟨.set x (.det e) default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inl ⟨by omega, by
        simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_choose_iff]
        refine ⟨⟨⟨idx, Nat.zero_le _, (by omega : idx ≤ ctx.length - 1)⟩⟩,
          ⟨Nat.zero_le _, (by omega : idx ≤ ctx.length - 1)⟩, e, ?_, ?_⟩
        · simp only [hentry]; exact he
        · simp only [hentry]⟩)))
    exact ⟨_, hinSupport, CmdHasType'.set_det _ x mty e default hfind hexpr⟩
  | set_nondet x mty md hfind =>
    have ⟨idx, hidx, hentry⟩ := hVarInCtx x mty hfind
    have hinSupport : (⟨.set x .nondet default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by
        simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_choose_iff]
        refine ⟨⟨⟨idx, Nat.zero_le _, (by omega : idx ≤ ctx.length - 1)⟩⟩,
          ⟨Nat.zero_le _, (by omega : idx ≤ ctx.length - 1)⟩, ?_⟩
        simp only [hentry]⟩))))
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
    - Freshness at every reachable context -/
structure GenCmdSoundEnv (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (C : LContext CoreLParams) where
  /-- Produce the semantic `TContext` for any flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The correspondence holds for every context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- Expression soundness (does not depend on the variable context). -/
  exprSound : GenLExprSound fctx octx tvars depth
  /-- Freshness holds at every context. -/
  freshSound : ∀ ctx, GenFreshNameSound fctx octx tvars ctx (toTCtx ctx) depth
  /-- The `TContext` produced for `(name, mty) :: ctx` equals the insertion
      into the `TContext` for `ctx`. This ensures the output `Γ'` from an `init`
      command matches what `toTCtx` produces for the extended `VarCtx`. -/
  toTCtx_cons : ∀ ctx name mty,
    toTCtx ((name, mty) :: ctx) =
      { toTCtx ctx with types := (toTCtx ctx).types.insert ⟨name, ()⟩ (.forAll [] mty) }

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
    have ⟨hfreshΓ, hnovar⟩ := (env.freshSound ctx) name hname
    have hwt := env.exprSound mty e he
    rw [env.toTCtx_cons]
    exact CmdHasType'.init_det _ ⟨name, ()⟩ _ e mty [] default hfreshΓ (hnovar mty e he) rfl (rigidAnnotCompat_forAll_nil mty) hwt
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, _, rfl⟩ := hr
    have ⟨hfreshΓ, _⟩ := (env.freshSound ctx) name hname
    rw [env.toTCtx_cons]
    exact CmdHasType'.init_nondet _ ⟨name, ()⟩ _ mty [] default hfreshΓ rfl (rigidAnnotCompat_forAll_nil mty)
  · -- set_det
    simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_choose_iff] at hr
    obtain ⟨idx, ⟨_, hidx⟩, e, he, rfl⟩ := hr
    have hlt : idx.down < ctx.length := by omega
    have hmem := List.getD_mem_of_lt (d := ("", LMonoTy.bool)) hlt
    have hfind := (env.corr ctx).1 (ctx.getD idx.down ("", .bool)).1
      (ctx.getD idx.down ("", .bool)).2 hmem
    have hwt := env.exprSound (ctx.getD idx.down ("", .bool)).2 e he
    exact CmdHasType'.set_det _ ⟨(ctx.getD idx.down ("", .bool)).1, ()⟩
      (ctx.getD idx.down ("", .bool)).2 e default hfind hwt
  · -- set_nondet
    simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_choose_iff] at hr
    obtain ⟨idx, ⟨_, hidx⟩, rfl⟩ := hr
    have hlt : idx.down < ctx.length := by omega
    have hmem := List.getD_mem_of_lt (d := ("", LMonoTy.bool)) hlt
    have hfind := (env.corr ctx).1 (ctx.getD idx.down ("", .bool)).1
      (ctx.getD idx.down ("", .bool)).2 hmem
    exact CmdHasType'.set_nondet _ ⟨(ctx.getD idx.down ("", .bool)).1, ()⟩
      (ctx.getD idx.down ("", .bool)).2 default hfind
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
instance : ToFormat Unit where
  format _ := .nil

#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨cmd, _⟩ ← genCmd [] [] [] [] 2
  IO.println <| Std.format cmd |>.pretty : IO Unit)

#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨cmd, ctx'⟩ ← genCmd [] [] [] [("x", .int), ("y", .bool)] 2
  IO.println <| s!"{Std.format cmd |>.pretty} -- ctx: {ctx'}" : IO Unit)
