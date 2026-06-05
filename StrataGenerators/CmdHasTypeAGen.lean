import StrataGenerators.SetGen
import StrataGenerators.CmdHasTypeAGen.Core

open Lambda RandomChoice Core Imperative TypeSpec SetGen

/-!
# Generator of well-typed commands satisfying `CmdHasTypeA`

A Basalt `SetGen`-based random generator for well-typed Strata imperative
commands (`Cmd Expression`) that satisfy the `CmdHasTypeA` relation.

## Contents

- Soundness theorems for each command form (assert, assume, cover, set, init)
- Completeness theorems showing reachability of each command form
- Embedding theorems connecting sub-generators to the top-level `genCmd`

## Approach

The generator works with a flat `VarCtx` (list of name-type pairs). Soundness
theorems show that each generated command satisfies `CmdHasTypeA` given
appropriate preconditions on the typing context. The expression-level
soundness (`genLExpr_sound`) is proved separately in `HasTypeAGen.lean`;
here we state the command-level theorems parametrically: given that the
expression has the right type, the command is well-typed.
-/

-- ── Soundness ────────────────────────────────────────────────────────

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

-- ── Completeness: sub-generator support ──────────────────────────────

/-- Completeness for assert: any well-typed boolean expression reachable by
    `genLExpr` yields an assert command in the support of `genAssertCmd`. -/
theorem genAssertCmd_complete
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth .bool)) :
    GenCmdResult.mk (.assert "" e default) ctx ∈
      SetGen.support (genAssertCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨e, he, rfl⟩

/-- Completeness for assume: any well-typed boolean expression reachable by
    `genLExpr` yields an assume command in the support of `genAssumeCmd`. -/
theorem genAssumeCmd_complete
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth .bool)) :
    GenCmdResult.mk (.assume "" e default) ctx ∈
      SetGen.support (genAssumeCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨e, he, rfl⟩

/-- Completeness for cover: any well-typed boolean expression reachable by
    `genLExpr` yields a cover command in the support of `genCoverCmd`. -/
theorem genCoverCmd_complete
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth .bool)) :
    GenCmdResult.mk (.cover "" e default) ctx ∈
      SetGen.support (genCoverCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨e, he, rfl⟩

/-- Completeness for set_det: choosing variable at index `idx` with type `mty`,
    and generating expression `e` of that type, is in the support. -/
theorem genSetDet_complete
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (h : ctx.length > 0)
    (idx : Nat) (hidx : idx < ctx.length)
    (name : String) (mty : LMonoTy)
    (hentry : ctx.getD idx ("", .bool) = (name, mty))
    (e : Expression.Expr)
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars [] depth mty)) :
    GenCmdResult.mk (.set ⟨name, ()⟩ (.det e) default) ctx ∈
      SetGen.support (genSetDet (G := SetGen.Set) fctx octx tvars ctx depth h) := by
  simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_choose_iff]
  refine ⟨⟨idx⟩, ⟨Nat.zero_le _, (by omega : idx ≤ ctx.length - 1)⟩, e, ?_, ?_⟩
  · simp only [hentry]; exact he
  · simp only [hentry]

/-- Completeness for set_nondet: choosing any valid variable index yields a
    nondet-assignment command in the support of `genSetNondet`. -/
theorem genSetNondet_complete
    (ctx : VarCtx)
    (h : ctx.length > 0)
    (idx : Nat) (hidx : idx < ctx.length)
    (name : String) (mty : LMonoTy)
    (hentry : ctx.getD idx ("", .bool) = (name, mty)) :
    GenCmdResult.mk (.set ⟨name, ()⟩ .nondet default) ctx ∈
      SetGen.support (genSetNondet (G := SetGen.Set) ctx h) := by
  simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_choose_iff]
  refine ⟨⟨idx⟩, ⟨Nat.zero_le _, (by omega : idx ≤ ctx.length - 1)⟩, ?_⟩
  simp only [hentry]

-- ── Completeness: embedding into genCmd ──────────────────────────────

/-- Any assert result in `genAssertCmd`'s support is also in `genCmd`'s support. -/
theorem genCmd_reaches_assert
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genAssertCmd (G := SetGen.Set) fctx octx tvars ctx depth)) :
    r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  simp only [genCmd, mem_support_dite_iff, mem_support_pick_iff]
  by_cases h : ctx.length > 0
  · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))⟩
  · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inl hr))⟩

/-- Any assume result in `genAssumeCmd`'s support is also in `genCmd`'s support. -/
theorem genCmd_reaches_assume
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genAssumeCmd (G := SetGen.Set) fctx octx tvars ctx depth)) :
    r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  simp only [genCmd, mem_support_dite_iff, mem_support_pick_iff]
  by_cases h : ctx.length > 0
  · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))⟩
  · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inr (Or.inl hr)))⟩

/-- Any cover result in `genCoverCmd`'s support is also in `genCmd`'s support. -/
theorem genCmd_reaches_cover
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCoverCmd (G := SetGen.Set) fctx octx tvars ctx depth)) :
    r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars ctx depth) := by
  simp only [genCmd, mem_support_dite_iff, mem_support_pick_iff]
  by_cases h : ctx.length > 0
  · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))⟩
  · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inr (Or.inr hr)))⟩

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
