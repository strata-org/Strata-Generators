import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.HasTypeAGen.IndirSupport

/-!
# Coverage probabilities for factory operators in generated expressions

The support proofs in this package read a generator as an `SPMF` and speak only about
`SPMF.support`: which draws are *possible*. This module reads `genLExprBase` as a measure and
speaks about `SPMF.prob`: how *often* a draw is a factory operator.

At a position whose type is headed by a declared type constructor (`IsDeclaredTyShaped`),
`genLExprBase_prob_rootFactoryOp_ge` gives `2/14` as a lower bound on the probability that a draw is
a factory operator at the root. `genLExprBase_prob_rootFactoryApp_ge` gives `4/14` times the `Indir`
branch's mass as a lower bound on the probability that it is a factory operator *applied* to
arguments.

The statement generator's expected loop count and loop coverage are in
`StrataGenerators.SizeDistributionLoops` and `StrataGenerators.SizeDistributionStmt`.

**Why a mass factor.** A sub-draw can fail: the `Indir` branch draws an argument for every input of
the chosen operator, and an argument draw can have empty support. So the bound in (2b) carries the
branch's own mass, and an acceptance-rate result would be needed to remove it.
-/

namespace StrataGenerators.Expectations

open Lambda Core Imperative RandomChoice SPMF NNReal ENNReal
open StrataGenerators StrataGenerators.Stmt StrataGenerators.IndirSupport

/-- A uniform choice over a non-empty list is a distribution: it has mass `1`. -/
theorem mass_elements {α : Type} {xs : List α} (hne : xs ≠ []) :
    (elements xs hne : SPMF α).mass = 1 := by
  rw [← expect_one, expect_elements, List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
  exact ENNReal.div_self (by simpa using hne) (by simp)

/-- A generator all of whose draws lie in `E` puts its whole mass on `E`. -/
theorem prob_eq_mass_of_subset {α : Type} {p : SPMF α} {E : Set α}
    (h : ∀ a ∈ support p, a ∈ E) : prob p E = p.mass := by
  unfold prob
  rw [← expect_one p]
  exact expect_congr_support fun a ha => by simp [Set.indicator, h a ha]

-- ── (2) Coverage: factory operators in a generated expression ────────────

/-- The event: the root of the expression is a factory operator, applied to a (possibly empty)
list of arguments. `pickOp` draws the empty case, a bare operator reference. -/
def RootFactoryOp : Set LExpr' :=
  {e | ∃ nm mty args, e = mkApps (LExpr.op () nm mty) args}

/-- The event: the root is a factory operator applied to at least one argument. This is the shape
the `Indir` and `IndirPoly` rules produce, and the one the ADT-law properties read. -/
def RootFactoryApp : Set LExpr' :=
  {e | ∃ nm mty args, args ≠ [] ∧ e = mkApps (LExpr.op () nm mty) args}

/-- Every candidate of `findOpsInCtx` takes at least one argument: the `filterMap` keeps only a
`some (arg :: args)`. This is why an `Indir` draw is an application and not a bare reference. -/
theorem findOpsInCtx_argTys_ne_nil (octx : OpCtx) (τ : LMonoTy) {nm : String}
    {argTys : List LMonoTy} (h : (nm, argTys) ∈ findOpsInCtx octx τ) : argTys ≠ [] := by
  simp only [findOpsInCtx, List.mem_filterMap] at h
  obtain ⟨⟨name, ty⟩, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact List.cons_ne_nil _ _
  · simp at h

/-- `pickOp` draws a bare factory operator, always. -/
theorem pickOp_prob_rootFactoryOp (octx : OpCtx) (τ : LMonoTy)
    (ho : (opsOfType octx τ).length > 0) :
    prob (pickOp (G := SPMF) octx τ ho) RootFactoryOp = 1 := by
  have hsub : ∀ e ∈ support (pickOp (G := SPMF) octx τ ho), e ∈ RootFactoryOp := by
    intro e he
    rw [pickOp, mem_support_elements_iff] at he
    simp only [List.mem_map] at he
    obtain ⟨nm, -, rfl⟩ := he
    exact ⟨⟨nm, ()⟩, some τ, [], rfl⟩
  rw [prob_eq_mass_of_subset hsub]
  rw [pickOp, mass_elements]

/-- Every `Indir` draw is a factory application. -/
theorem genIndir_prob_rootFactoryApp (octx : OpCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SPMF LExpr') (h : (findOpsInCtx octx τ).length > 0) :
    prob (genIndir (G := SPMF) octx τ genArg h) RootFactoryApp
      = (genIndir (G := SPMF) octx τ genArg h).mass := by
  refine prob_eq_mass_of_subset fun e he => ?_
  obtain ⟨name, argTys, args, hmem, hrel, rfl⟩ := genIndir_shape octx τ genArg h e he
  refine ⟨_, _, args, ?_, rfl⟩
  intro hnil
  subst hnil
  cases hrel
  exact findOpsInCtx_argTys_ne_nil octx τ hmem rfl

/-- `τ` is none of the shapes `genLExprBase` handles specially — so it is headed by a declared type
constructor. This is the case the factory branches exist for: a datatype-typed position, where the
only ways to build a term are a variable in scope and a constructor of the datatype. The ten
conjuncts are exactly the side conditions of `genLExprBase`'s catch-all equation. -/
def IsDeclaredTyShaped (τ : LMonoTy) : Prop :=
  (∀ τ₁ τ₂, τ = .tcons "arrow" [τ₁, τ₂] → False) ∧ (τ = .tcons "bool" [] → False) ∧
  (τ = .tcons "int" [] → False) ∧ (∀ name, τ = .ftvar name → False) ∧
  (τ = .tcons "string" [] → False) ∧ (τ = .tcons "real" [] → False) ∧
  (∀ w, τ = .bitvec w → False) ∧ (τ = .tcons "regex" [] → False) ∧
  (∀ τ₁ τ₂, τ = .tcons "Map" [τ₁, τ₂] → False) ∧ (∀ τ', τ = .tcons "Sequence" [τ'] → False)

/-- A declared nullary type constructor is one of these. Instantiating the two bounds below, so they
are visibly not vacuous. -/
theorem isDeclaredTyShaped_tcons (nm : String) (args : List LMonoTy)
    (h : nm ∉ ["arrow", "bool", "int", "string", "real", "regex", "Map", "Sequence"]) :
    IsDeclaredTyShaped (.tcons nm args) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  refine ⟨fun _ _ hc => ?_, fun hc => ?_, fun hc => ?_, fun _ hc => ?_, fun hc => ?_, fun hc => ?_,
    fun _ hc => ?_, fun hc => ?_, fun _ _ hc => ?_, fun _ hc => ?_⟩
  · exact h.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact LMonoTy.noConfusion hc
  · exact h.2.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.2.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact LMonoTy.noConfusion hc
  · exact h.2.2.2.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.2.2.2.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.2.2.2.2.2.2 (LMonoTy.tcons.injEq .. ▸ hc).1

/-- **(2a) A factory-operator coverage bound.** At a declared-type-constructor position with a
factory operator of that type in scope, at least `2/14` of the draws are a factory operator at the
root. The `2` is the `pickOp` branch's weight and `14` the total. No mass hypothesis is needed:
`elements` over a non-empty list is a genuine distribution, so this bound is unconditional. -/
theorem genLExprBase_prob_rootFactoryOp_ge (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy)
    (hτ : IsDeclaredTyShaped τ)
    (hv : (bvarsOfType bctx τ).length = 0) (hf : (fvarsOfType fctx τ).length = 0)
    (ho : (opsOfType octx τ).length > 0) :
    2 / 14 ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) τ)
      RootFactoryOp := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hτ
  rw [genLExprBase, prob_frequency]
  · have hden : ((2 + (2 + (2 + (4 + 4))) : ℕ) : ℝ≥0∞) = 14 := by norm_num
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hden, add_zero,
      dif_neg (by omega : ¬ (bvarsOfType bctx τ).length > 0),
      dif_neg (by omega : ¬ (fvarsOfType fctx τ).length > 0), dif_pos ho,
      pickOp_prob_rootFactoryOp, Nat.cast_ofNat, mul_one]
    refine ENNReal.div_le_div_right ?_ _
    iterate 2 refine le_trans ?_ le_add_self
    exact le_self_add
  all_goals assumption

/-- **(2b) A factory-application coverage bound.** The `Indir` branch's weight share `4/14` times
that branch's own mass. The mass factor is irreducible here: the branch draws an argument for every
input of the chosen operator, and an argument draw can fail — that is the acceptance-rate question,
and it is separate from the weight. -/
theorem genLExprBase_prob_rootFactoryApp_ge (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy)
    (hτ : IsDeclaredTyShaped τ) (hi : (findOpsInCtx octx τ).length > 0) :
    4 * (genIndir (G := SPMF) octx τ
          (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) hi).mass / 14
      ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) τ) RootFactoryApp := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hτ
  rw [genLExprBase, prob_frequency]
  · have hden : ((2 + (2 + (2 + (4 + 4))) : ℕ) : ℝ≥0∞) = 14 := by norm_num
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hden, add_zero,
      dif_pos hi, genIndir_prob_rootFactoryApp, Nat.cast_ofNat]
    refine ENNReal.div_le_div_right ?_ _
    iterate 3 refine le_trans ?_ le_add_self
    exact le_self_add
  all_goals assumption

/-- The side condition is satisfiable: a declared type constructor satisfies it. -/
example : IsDeclaredTyShaped (.tcons "MyList" [.int]) :=
  isDeclaredTyShaped_tcons "MyList" [.int] (by decide)

end StrataGenerators.Expectations
