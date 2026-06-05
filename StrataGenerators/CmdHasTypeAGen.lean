import StrataGenerators.SetGen
import StrataGenerators.CmdHasTypeAGen.Core

open Lambda RandomChoice Core Imperative TypeSpec SetGen

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
  CmdHasType'.init_det Γ x (.forAll [] mty) e mty default hfresh hnovar hwt

/-- Soundness of init_nondet: if `x` is fresh in `Γ`,
    then `init x (.forAll [] mty) nondet default` is well-typed. -/
theorem genInitNondet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfresh : Γ.types.find? x = none) :
    CmdHasTypeA C Γ (.init x (.forAll [] mty) .nondet default)
      { Γ with types := Γ.types.insert x (.forAll [] mty) } :=
  CmdHasType'.init_nondet Γ x (.forAll [] mty) mty default hfresh

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
  simp only [genCmd, mem_support_dite_iff, mem_support_pick_iff]
  constructor
  · intro hr
    rcases hr with ⟨h, hr⟩ | ⟨hne, hr⟩
    · rcases hr with hr | (hr | (hr | (hr | (hr | (hr | hr)))))
      · exact Or.inl hr
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr (Or.inl ⟨h, hr⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hr⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
    · rcases hr with hr | (hr | (hr | (hr | hr)))
      · exact Or.inl hr
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
  · intro hr
    rcases hr with hr | (hr | (⟨h, hr⟩ | (⟨h, hr⟩ | (hr | (hr | hr)))))
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, Or.inl hr⟩
      · exact Or.inr ⟨h, Or.inl hr⟩
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, Or.inr (Or.inl hr)⟩
      · exact Or.inr ⟨h, Or.inr (Or.inl hr)⟩
    · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inl hr))⟩
    · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inl hr)))⟩
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))⟩
      · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inl hr))⟩
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))⟩
      · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inr (Or.inl hr)))⟩
    · by_cases h : ctx.length > 0
      · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))⟩
      · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inr (Or.inr hr)))⟩

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
  ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth τ) →
    LExpr.HasTypeA (T := LExprParams') [] e τ

/-- Predicate asserting that `genFreshName` produces names that are fresh in the
    `TContext` (when `VarCtxCorresponds` holds) and that do not appear as free
    variables in any expression generated by `genLExpr`. -/
def GenFreshNameSound (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (Γ : TContext Unit) (depth : Nat) : Prop :=
  ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
    (Γ.types.find? (⟨name, ()⟩ : Identifier Unit) = none) ∧
    (∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth τ) →
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
    ∃ Γ', CmdHasTypeA C Γ r.cmd Γ' := by
  rw [genCmd_support_iff] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, e, he, rfl⟩ := hr
    have ⟨hfreshΓ, hnovar⟩ := hFresh name hname
    have hwt := hExprSound mty e he
    exact ⟨_, CmdHasType'.init_det Γ ⟨name, ()⟩ _ e mty default hfreshΓ (hnovar mty e he) hwt⟩
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, _, rfl⟩ := hr
    have ⟨hfreshΓ, _⟩ := hFresh name hname
    exact ⟨_, CmdHasType'.init_nondet Γ ⟨name, ()⟩ _ mty default hfreshΓ⟩
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

/-- Full completeness of `genCmd`: every well-typed command form that the
    generator could produce is actually in its support.

    Specifically, the support includes:
    - Every `assert/assume/cover` with any boolean expression from `genLExpr`
    - Every `set x (det e)` / `set x nondet` for any `x` in `ctx`
    - Every `init x τ (det e)` / `init x τ nondet` for any fresh name from `genFreshName`

    This is the converse of `genCmd_sound`: if a command is well-typed and
    structurally matches what the generator can produce (correct labels, metadata,
    names from `genFreshName`, expressions from `genLExpr`), it is in the support. -/
theorem genCmd_complete_assert
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth .bool)) :
    GenCmdResult.mk (.assert "" e default) ctx ∈
      SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  rw [genCmd_support_iff]
  right; right; right; right; left
  simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨e, he, rfl⟩

/-- Full completeness: any assume command with a reachable boolean expression
    is in `genCmd`'s support. -/
theorem genCmd_complete_assume
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth .bool)) :
    GenCmdResult.mk (.assume "" e default) ctx ∈
      SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  rw [genCmd_support_iff]
  right; right; right; right; right; left
  simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨e, he, rfl⟩

/-- Full completeness: any cover command with a reachable boolean expression
    is in `genCmd`'s support. -/
theorem genCmd_complete_cover
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth .bool)) :
    GenCmdResult.mk (.cover "" e default) ctx ∈
      SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  rw [genCmd_support_iff]
  right; right; right; right; right; right
  simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨e, he, rfl⟩

/-- Full completeness: any deterministic set command for a valid context entry
    with a reachable expression is in `genCmd`'s support. -/
theorem genCmd_complete_set_det
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (h : ctx.length > 0)
    (idx : Nat) (hidx : idx < ctx.length)
    (name : String) (mty : LMonoTy)
    (hentry : ctx.getD idx ("", .bool) = (name, mty))
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth mty)) :
    GenCmdResult.mk (.set ⟨name, ()⟩ (.det e) default) ctx ∈
      SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  rw [genCmd_support_iff]
  right; right; left
  refine ⟨h, ?_⟩
  simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_choose_iff]
  refine ⟨⟨idx⟩, ⟨Nat.zero_le _, (by omega : idx ≤ ctx.length - 1)⟩, e, ?_, ?_⟩
  · simp only [hentry]; exact he
  · simp only [hentry]

/-- Full completeness: any nondet set command for a valid context entry
    is in `genCmd`'s support. -/
theorem genCmd_complete_set_nondet
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (h : ctx.length > 0)
    (idx : Nat) (hidx : idx < ctx.length)
    (name : String) (mty : LMonoTy)
    (hentry : ctx.getD idx ("", .bool) = (name, mty)) :
    GenCmdResult.mk (.set ⟨name, ()⟩ .nondet default) ctx ∈
      SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  rw [genCmd_support_iff]
  right; right; right; left
  refine ⟨h, ?_⟩
  simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_choose_iff]
  refine ⟨⟨idx⟩, ⟨Nat.zero_le _, (by omega : idx ≤ ctx.length - 1)⟩, ?_⟩
  simp only [hentry]

/-- Full completeness: any deterministic init command with a fresh name from
    `genFreshName`, a type from `genLMonoTy`, and a reachable expression
    is in `genCmd`'s support. -/
theorem genCmd_complete_init_det
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (name : String)
    (hname : name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx))
    (mty : LMonoTy)
    (hmty : mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth))
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth mty)) :
    GenCmdResult.mk (.init ⟨name, ()⟩ (.forAll [] mty) (.det e) default)
      ((name, mty) :: ctx) ∈
      SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  rw [genCmd_support_iff]
  left
  simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨name, hname, mty, hmty, e, he, rfl⟩

/-- Full completeness: any nondet init command with a fresh name from
    `genFreshName` and a type from `genLMonoTy` is in `genCmd`'s support. -/
theorem genCmd_complete_init_nondet
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (name : String)
    (hname : name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx))
    (mty : LMonoTy)
    (hmty : mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth)) :
    GenCmdResult.mk (.init ⟨name, ()⟩ (.forAll [] mty) .nondet default)
      ((name, mty) :: ctx) ∈
      SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  rw [genCmd_support_iff]
  right; left
  simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨name, hname, mty, hmty, rfl⟩

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
