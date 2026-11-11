import StrataGenerators.PalkaAblation.Gen
import Basalt

/-!
# Factory calls with and without the Indir/IndirPoly rules: the bounds

**What is removed.** Only the two branches that apply a factory operator to arguments read off its
signature (Indir and IndirPoly, Pałka et al.'s rules). The generator without the Pałka rule keeps the rest,
including `genAppArgTy` and `genGenerableTy`, which draw argument types from the context's
generable types (also after Pałka et al.). The upper bound `off_call_le` is used with the guess
probability bounded by `1`, so it does not depend on how `genAppArgTy` guesses: it holds for any
argument-type generator, including a blind one.

The event `OpCall name k`: the root of the term is the operator `name` applied to exactly `k`
arguments. For every operator context:

* **Indir/IndirPoly on (`genLExprBase`).** `on_call_ge`: if `(name, as)` is an Indir
  candidate at `r`, then at every depth `n + 1` the full call is made with probability at least
  `4/24 · |candidates at r|⁻¹ · ∏ massFloor aᵢ`. `massFloor` is a per-type lower bound on the
  generator's mass, proven at every depth (`mass_bool`, `mass_int`, …).
* **Indir/IndirPoly off (`genLExprBaseW … 0 0`).** `off_call_le`: if `name` is an operator
  only at its type `a₁ → ⋯ → aₘ → r`, then at every depth the full call is made with probability
  at most `offChain`, which is `1/3 · pickShare` for the innermost bare operator, times one
  application-branch share (`appShare`) and one argument-type guess (`γ`) per argument. It is
  assembled from `off_succ_le_app` (only the application branch can produce an application),
  `offApp_le` (one application rule) and `off_op_le` (the innermost operator).
  `off_eq_zero_of_lt`: below the arity the probability is `0`.
* **`genLExpr`.** `genLExpr_call_ge`: at every depth, at least
  `9/20 · |candidates|⁻¹ · ∏ (massFloor aᵢ / 10)`.

Most per-site decompositions of a `frequency` are done by Basalt's `walk`, with one fact per
branch. The upper bounds pass `obs_le_iSup` for each sub-generator, so that a branch whose root is
not an application walks to a supremum of indicators that `simp` reduces to `0`.
-/

open Lambda RandomChoice
open scoped ENNReal
open SPMF (prob expect mass)

namespace StrataGenerators.PalkaAblation

/-! ## Termination of the leaf generators -/

theorem natArbitrary_terminates : IsAlmostSurelyTerminating (ArbNat.Nat.arbitrary : SPMF Nat) := by
  mass_fixpoint using SPMF.LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.div_eq_inv_mul, mul_add]

theorem natArbGeom_terminates :
    IsAlmostSurelyTerminating (StrataGenerators.PrimitiveGens.natArbGeom : SPMF Nat) := by
  mass_fixpoint using SPMF.LfpIsOne.affine (m := 1 / 2) (by norm_num)
  simp [ENNReal.div_eq_inv_mul, mul_add]

theorem genIntConst_mass : 1 ≤ mass (genIntConst : SPMF LExpr') := by
  rw [SPMF.mass_eq_obs]
  walk [natArbitrary_terminates.obs]
  norm_num [ENNReal.div_self]

theorem genBoolConst_mass : 1 ≤ mass (genBoolConst : SPMF LExpr') := by
  rw [SPMF.mass_eq_obs]
  walk
  norm_num [ENNReal.div_self]

theorem genStrConst_mass : 1 ≤ mass (genStrConst : SPMF LExpr') := by
  rw [SPMF.mass_eq_obs]
  walk
  norm_num [ENNReal.div_self]

theorem genRealConst_mass : 1 ≤ mass (genRealConst : SPMF LExpr') := by
  rw [SPMF.mass_eq_obs]
  walk [natArbGeom_terminates.obs]
  norm_num [ENNReal.div_self]

theorem genBitvecConst_mass (w : Nat) : 1 ≤ mass (genBitvecConst w : SPMF LExpr') := by
  rw [SPMF.mass_eq_obs]
  walk
  norm_num [ENNReal.div_self]


/-- Closes the arithmetic a mass walk leaves at a constant-typed site. -/
macro "mass_arith" : tactic => `(tactic| first
  | (norm_num [ENNReal.div_self]; done)
  | (norm_num [ENNReal.div_self]; exact ENNReal.div_le_of_le_mul (by norm_num)))

theorem prob_eq_obs {α : Type} (p : SPMF α) (E : Set α) :
    prob p E = SPMF.expectObs.spec p (E.indicator 1) := rfl

theorem zero_le_obs {α : Type} (g : SPMF α) (φ : α → ℝ≥0∞) : 0 ≤ SPMF.expectObs.spec g φ :=
  zero_le

section mass
variable (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)

/-- At `bool`: the constant and the three variable/operator branches (whose fallback is a constant) always succeed: `7` of `24`. -/
theorem mass_bool (bctx : BVarCtx) : ∀ n,
    7 / 24 ≤ mass (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n .bool)
  | 0 => by
    unfold LMonoTy.bool; rw [genLExprBase.eq_3, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1)]
    mass_arith
  | n + 1 => by
    unfold LMonoTy.bool; rw [genLExprBase.eq_4, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun b τ => zero_le_obs (genLExprBase (G := SPMF) fctx octx pctx tvars b n τ) (fun _ => 1),
      zero_le_obs (genGenerableTy (G := SPMF) fctx octx tvars bctx n) (fun _ => 1),
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun τ => zero_le_obs (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ) (fun _ => 1),
      fun τ h => zero_le_obs (genIndir (G := SPMF) octx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) h) (fun _ => 1),
      fun τ fb => zero_le_obs (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) fb) (fun _ => 1)]
    mass_arith

/-- At `int`: `7` of `18`, as at `bool`. -/
theorem mass_int (bctx : BVarCtx) : ∀ n,
    7 / 18 ≤ mass (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n .int)
  | 0 => by
    unfold LMonoTy.int; rw [genLExprBase.eq_5, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1)]
    mass_arith
  | n + 1 => by
    unfold LMonoTy.int; rw [genLExprBase.eq_6, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun b τ => zero_le_obs (genLExprBase (G := SPMF) fctx octx pctx tvars b n τ) (fun _ => 1),
      zero_le_obs (genGenerableTy (G := SPMF) fctx octx tvars bctx n) (fun _ => 1),
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun τ => zero_le_obs (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ) (fun _ => 1),
      fun τ h => zero_le_obs (genIndir (G := SPMF) octx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) h) (fun _ => 1),
      fun τ fb => zero_le_obs (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) fb) (fun _ => 1)]
    mass_arith

/-- At `string`: `7` of `18`. -/
theorem mass_string (bctx : BVarCtx) : ∀ n,
    7 / 18 ≤ mass (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n .string)
  | 0 => by
    unfold LMonoTy.string; rw [genLExprBase.eq_9, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1)]
    mass_arith
  | n + 1 => by
    unfold LMonoTy.string; rw [genLExprBase.eq_10, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun b τ => zero_le_obs (genLExprBase (G := SPMF) fctx octx pctx tvars b n τ) (fun _ => 1),
      zero_le_obs (genGenerableTy (G := SPMF) fctx octx tvars bctx n) (fun _ => 1),
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun τ => zero_le_obs (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ) (fun _ => 1),
      fun τ h => zero_le_obs (genIndir (G := SPMF) octx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) h) (fun _ => 1),
      fun τ fb => zero_le_obs (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) fb) (fun _ => 1)]
    mass_arith

/-- At `real`: `7` of `18`. -/
theorem mass_real (bctx : BVarCtx) : ∀ n,
    7 / 18 ≤ mass (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n .real)
  | 0 => by
    unfold LMonoTy.real; rw [genLExprBase.eq_11, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1)]
    mass_arith
  | n + 1 => by
    unfold LMonoTy.real; rw [genLExprBase.eq_12, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun b τ => zero_le_obs (genLExprBase (G := SPMF) fctx octx pctx tvars b n τ) (fun _ => 1),
      zero_le_obs (genGenerableTy (G := SPMF) fctx octx tvars bctx n) (fun _ => 1),
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun τ => zero_le_obs (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ) (fun _ => 1),
      fun τ h => zero_le_obs (genIndir (G := SPMF) octx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) h) (fun _ => 1),
      fun τ fb => zero_le_obs (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) fb) (fun _ => 1)]
    mass_arith

/-- At `bitvec w`: `7` of `18`. -/
theorem mass_bitvec (bctx : BVarCtx) (w : Nat) : ∀ n,
    7 / 18 ≤ mass (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n (.bitvec w))
  | 0 => by
    rw [genLExprBase.eq_13, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1)]
    mass_arith
  | n + 1 => by
    rw [genLExprBase.eq_14, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun b τ => zero_le_obs (genLExprBase (G := SPMF) fctx octx pctx tvars b n τ) (fun _ => 1),
      zero_le_obs (genGenerableTy (G := SPMF) fctx octx tvars bctx n) (fun _ => 1),
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun τ => zero_le_obs (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ) (fun _ => 1),
      fun τ h => zero_le_obs (genIndir (G := SPMF) octx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) h) (fun _ => 1),
      fun τ fb => zero_le_obs (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) fb) (fun _ => 1)]
    mass_arith

/-- At `regex`, given a nullary regex operator: the two branches that fall back to an operator succeed, `4` of `17`. -/
theorem mass_regex (bctx : BVarCtx) (ho : (opsOfType octx .regex).length > 0) : ∀ n,
    4 / 17 ≤ mass (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n .regex)
  | 0 => by
    unfold LMonoTy.regex; rw [genLExprBase.eq_15, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1), ho]
    simp only [List.sum_cons, List.sum_nil, dite_eq_ite, gt_iff_lt, ho, if_true, ite_self]
    mass_arith
  | n + 1 => by
    unfold LMonoTy.regex; rw [genLExprBase.eq_16, SPMF.mass_eq_obs]
    walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun b τ => zero_le_obs (genLExprBase (G := SPMF) fctx octx pctx tvars b n τ) (fun _ => 1),
      zero_le_obs (genGenerableTy (G := SPMF) fctx octx tvars bctx n) (fun _ => 1),
      zero_le_obs (default : SPMF LExpr') (fun _ => 1),
      fun τ => zero_le_obs (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ) (fun _ => 1),
      fun τ h => zero_le_obs (genIndir (G := SPMF) octx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) h) (fun _ => 1),
      fun τ fb => zero_le_obs (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
        (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) fb) (fun _ => 1), ho]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dite_eq_ite, gt_iff_lt,
      ho, if_true, ite_self]
    norm_num
    refine ENNReal.div_le_div_right ?_ _
    calc (4 : ℝ≥0∞) = 2 + (0 + 2) := by norm_num
      _ ≤ _ := by gcongr; exact zero_le

/-- A lower bound on `genLExprBase`'s mass at each type, at every depth (`0` where none is
proven). -/
noncomputable def massFloor (octx : OpCtx) : LMonoTy → ℝ≥0∞
  | .tcons "bool" [] => 7 / 24
  | .tcons "int" [] => 7 / 18
  | .tcons "string" [] => 7 / 18
  | .tcons "real" [] => 7 / 18
  | .bitvec _ => 7 / 18
  | .tcons "regex" [] => if (opsOfType octx .regex).length > 0 then 4 / 17 else 0
  | _ => 0

theorem massFloor_le (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) :
    massFloor octx τ ≤ mass (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n τ) := by
  unfold massFloor
  split
  · exact mass_bool fctx octx pctx tvars bctx n
  · exact mass_int fctx octx pctx tvars bctx n
  · exact mass_string fctx octx pctx tvars bctx n
  · exact mass_real fctx octx pctx tvars bctx n
  · exact mass_bitvec fctx octx pctx tvars bctx _ n
  · split
    · exact mass_regex fctx octx pctx tvars bctx ‹_› n
    · exact zero_le
  · exact zero_le

end mass


/-! ## The event: a call of a factory operator -/

/-- The event "the root of the term is the operator `name` applied to exactly `k` arguments", with
any type annotation on the operator: `.op name _` for `k = 0`, and `.app g x` with `g` such a
term for `k - 1` otherwise. -/
def OpCall (name : String) : Nat → Set LExpr'
  | 0 => {e | ∃ ty, e = .op () ⟨name, ()⟩ ty}
  | k + 1 => {e | ∃ g x, e = .app () g x ∧ g ∈ OpCall name k}

section opCallSimp
variable {name : String} {k : Nat} {m : Unit}

@[simp] theorem OpCall_succ_ind_const (c) : (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.const m c : LExpr') = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_succ_ind_op (o) (ty) : (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.op m o ty : LExpr') = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_succ_ind_bvar (i) : (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.bvar m i : LExpr') = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_succ_ind_fvar (x) (ty) : (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.fvar m x ty : LExpr') = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_succ_ind_abs (x ty) (e : LExpr') : (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.abs m x ty e) = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_succ_ind_quant (q x ty) (t e : LExpr') : (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.quant m q x ty t e) = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_succ_ind_ite (c t e : LExpr') : (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.ite m c t e) = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_succ_ind_eq (a b : LExpr') : (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.eq m a b) = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_succ_ind_app (g x : LExpr') :
    (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.app m g x) = (OpCall name k).indicator (1 : LExpr' → ℝ≥0∞) g := by
  by_cases h : g ∈ OpCall name k <;> simp [OpCall, h]

@[simp] theorem OpCall_zero_ind_const (c) : (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.const m c : LExpr') = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_zero_ind_bvar (i) : (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.bvar m i : LExpr') = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_zero_ind_fvar (x) (ty) : (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.fvar m x ty : LExpr') = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_zero_ind_abs (x ty) (e : LExpr') : (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.abs m x ty e) = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_zero_ind_quant (q x ty) (t e : LExpr') : (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.quant m q x ty t e) = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_zero_ind_ite (c t e : LExpr') : (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.ite m c t e) = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_zero_ind_eq (a b : LExpr') : (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.eq m a b) = 0 := by
  simp [OpCall]
@[simp] theorem OpCall_zero_ind_app (g x : LExpr') : (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.app m g x) = 0 := by
  simp [OpCall]

@[simp] theorem OpCall_succ_ind_intConst (i : Int) :
    (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.intConst m i) = 0 := OpCall_succ_ind_const _
@[simp] theorem OpCall_succ_ind_boolConst (b : Bool) :
    (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.boolConst m b) = 0 := OpCall_succ_ind_const _
@[simp] theorem OpCall_succ_ind_strConst (x : String) :
    (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.strConst m x) = 0 := OpCall_succ_ind_const _
@[simp] theorem OpCall_succ_ind_realConst (r : Rat) :
    (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.rationalConst m r) = 0 := OpCall_succ_ind_const _
@[simp] theorem OpCall_succ_ind_bitvecConst (w : Nat) (b : BitVec w) :
    (OpCall name (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.bitvecConst m w b) = 0 :=
  OpCall_succ_ind_const _
@[simp] theorem OpCall_zero_ind_intConst (i : Int) :
    (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.intConst m i) = 0 := OpCall_zero_ind_const _
@[simp] theorem OpCall_zero_ind_boolConst (b : Bool) :
    (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.boolConst m b) = 0 := OpCall_zero_ind_const _
@[simp] theorem OpCall_zero_ind_strConst (x : String) :
    (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.strConst m x) = 0 := OpCall_zero_ind_const _
@[simp] theorem OpCall_zero_ind_realConst (r : Rat) :
    (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.rationalConst m r) = 0 := OpCall_zero_ind_const _
@[simp] theorem OpCall_zero_ind_bitvecConst (w : Nat) (b : BitVec w) :
    (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.bitvecConst m w b) = 0 :=
  OpCall_zero_ind_const _

@[simp] theorem OpCall_zero_ind_op (nm : String) (ty) :
    (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.op m ⟨nm, ()⟩ ty)
      = if nm = name then 1 else 0 := by
  by_cases h : nm = name <;> simp [OpCall, h]

end opCallSimp

theorem obs_default_le {α : Type} (p : α → ℝ≥0∞) :
    SPMF.expectObs.spec (default : SPMF α) p ≤ 0 := by
  simp [SPMF.expectObs, SPMF.expect, SPMF.default_apply]

/-- **Drawing the arguments of a call.** Starting from a call `g` with `k` arguments, drawing one
argument per type of `l` and applying `g` to them all gives a call with `k + |l|` arguments
exactly when every draw succeeds. -/
theorem prob_mapM_mkApps (gen : LMonoTy → SPMF LExpr') (name : String) :
    ∀ (l : List LMonoTy) (g : LExpr') (k : Nat), g ∈ OpCall name k →
      prob (do let xs ← l.mapM gen; pure (mkApps g xs)) (OpCall name (k + l.length))
        = (l.map fun a => mass (gen a)).prod
  | [], g, k, hg => by classical simp [SPMF.prob_pure, mkApps, hg]
  | a :: l, g, k, hg => by
    have ih := fun x => prob_mapM_mkApps gen name l (.app () g x) (k + 1) ⟨g, x, rfl, hg⟩
    simp only [mkApps] at ih ⊢
    simp only [List.mapM_cons, bind_assoc, pure_bind, List.foldl_cons, List.length_cons,
      List.map_cons, List.prod_cons, show k + (l.length + 1) = k + 1 + l.length by omega]
    rw [SPMF.prob_bind]
    simp only [ih, SPMF.expect_const]

/-- **The Indir rule, bounded below.** If `(name, argTys)` is a candidate of `findOpsInCtx` at
`τ`, the rule calls `name` with all `|argTys|` arguments with probability at least
`|candidates|⁻¹ · ∏ Pr(argument i succeeds)`. -/
theorem prob_genIndir_call_ge (octx : OpCtx) (τ : LMonoTy) (genArg : LMonoTy → SPMF LExpr')
    (h : (findOpsInCtx octx τ).length > 0) {name : String} {argTys : List LMonoTy}
    (hmem : (name, argTys) ∈ findOpsInCtx octx τ) :
    ((findOpsInCtx octx τ).length : ℝ≥0∞)⁻¹ * (argTys.map fun a => mass (genArg a)).prod
      ≤ prob (genIndir (G := SPMF) octx τ genArg h) (OpCall name argTys.length) := by
  have hcall := prob_mapM_mkApps genArg name argTys
    (.op () ⟨name, ()⟩ (some (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) 0 ⟨_, rfl⟩
  rw [Nat.zero_add] at hcall
  have hne : findOpsInCtx octx τ ≠ [] := List.ne_nil_of_length_pos h
  unfold genIndir
  rw [SPMF.prob_bind]
  unfold SPMF.prob at hcall ⊢
  rw [SPMF.expect_elements hne, div_eq_mul_inv, mul_comm]
  gcongr
  rw [← hcall]
  exact List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => _) hmem)


theorem obs_le_of_prob_le {α : Type} {p : SPMF α} {E : Set α} {B : ℝ≥0∞} (h : prob p E ≤ B) :
    SPMF.expectObs.spec p (E.indicator 1) ≤ B := h

theorem le_obs_of_le_prob {α : Type} {p : SPMF α} {E : Set α} {B : ℝ≥0∞} (h : B ≤ prob p E) :
    B ≤ SPMF.expectObs.spec p (E.indicator 1) := h

/-- One summand `c · B` of a weighted average over total weight `W ≤ 24` gives `c/24 · B`. -/
theorem le_div_of_term {B S : ℝ≥0∞} {c W : ℕ} (hW : W ≤ 24) (h : (c : ℝ≥0∞) * B ≤ S) :
    (c : ℝ≥0∞) / 24 * B ≤ S / (W : ℝ≥0∞) := by
  calc (c : ℝ≥0∞) / 24 * B = (c : ℝ≥0∞) * B / 24 := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
    _ ≤ S / 24 := ENNReal.div_le_div_right h _
    _ ≤ S / (W : ℝ≥0∞) := ENNReal.div_le_div_left (by exact_mod_cast hW) _

/-- Picks one summand out of a right-nested sum. -/
macro "term_le_sum" : tactic => `(tactic|
  repeat (first | exact le_rfl | exact le_self_add | refine le_trans ?_ le_add_self))

/-- **The Indir branch's share.** At every type, the Indir branch of `genLExprBase` (weight `4`) is
taken with probability at least `1/6` (the largest total weight of a site is `24`, at `bool`). -/
theorem genLExprBase_prob_ge_indir (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) (E : Set LExpr')
    (hi : (findOpsInCtx octx τ).length > 0) {B : ℝ≥0∞}
    (hB : B ≤ prob (genIndir (G := SPMF) octx τ
      (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) hi) E) :
    ((4 : ℕ) : ℝ≥0∞) / 24 * B
      ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) τ) E := by
  rw [genLExprBase.eq_def, prob_eq_obs]
  split <;> (try simp only [Nat.succ.injEq] at *) <;> (try subst_vars)
  all_goals first
    | (exfalso; omega)
    | (walk [natArbitrary_terminates.obs, natArbGeom_terminates.obs,
        fun φ => zero_le_obs (default : SPMF LExpr') φ,
        fun m b τ φ => zero_le_obs (genLExprBase (G := SPMF) fctx octx pctx tvars b m τ) φ,
        fun m φ => zero_le_obs (genGenerableTy (G := SPMF) fctx octx tvars bctx m) φ,
        fun m τ φ => zero_le_obs (genAppArgTy (G := SPMF) fctx octx tvars bctx m τ) φ,
        fun h => le_obs_of_le_prob (h := hB) (p := genIndir (G := SPMF) octx _ _ h),
        fun m τ fb φ => zero_le_obs (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
          (genLExprBase (G := SPMF) fctx octx pctx tvars bctx m) fb) φ]
       try delta LMonoTy.arrow LMonoTy.bool LMonoTy.int LMonoTy.string LMonoTy.real
       simp only [dif_pos hi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
       exact le_div_of_term (by norm_num) (by term_le_sum))


/-! ## The generator without the Pałka rule: an upper bound -/

theorem obs_le_iSup {α : Type} (g : SPMF α) (p : α → ℝ≥0∞) :
    SPMF.expectObs.spec g p ≤ ⨆ a, p a := SPMF.expect_le_iSup

section noPalka
variable (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)

/-- The generator without the Pałka rule: `genLExprBase` without its Indir and IndirPoly branches. -/
noncomputable abbrev genOff (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) : SPMF LExpr' :=
  genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx n τ

/-- The application branch of the generator without the Pałka rule, at type `τ`. -/
noncomputable abbrev offApp (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) : SPMF LExpr' :=
  genApp (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ)
    (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx n) τ

/-- Whether a type is an arrow. -/
def isArrow : LMonoTy → Bool
  | .tcons "arrow" [_, _] => true
  | _ => false

/-- The application branch's share of its site, in the generator without the Pałka rule: `1/13`
at an arrow,
at most `1/9` elsewhere (`1/16` at `bool`, `1/10` at `int`, …, `0` at a declared type). -/
noncomputable def appShare (τ : LMonoTy) : ℝ≥0∞ := if isArrow τ then 1 / 13 else 1 / 9

theorem div_le_inv_mul {P : ℝ≥0∞} {c W : ℕ} (h : c ≤ W) : P / (W : ℝ≥0∞) ≤ (c : ℝ≥0∞)⁻¹ * P := by
  rw [div_eq_mul_inv, mul_comm]
  gcongr

theorem off_succ_le_app (bctx : BVarCtx) (n k : Nat) (name : String) (τ : LMonoTy) :
    prob (genOff fctx octx pctx tvars bctx (n + 1) τ) (OpCall name (k + 1))
      ≤ appShare τ * prob (offApp fctx octx pctx tvars bctx n τ) (OpCall name (k + 1)) := by
  unfold offApp
  generalize hA : genApp (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ)
    (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx n) τ = A
  revert hA
  unfold genOff
  rw [genLExprBaseW.eq_def, prob_eq_obs]
  split <;> (try simp only [Nat.succ.injEq] at *) <;> (try subst_vars)
  all_goals first
    | (exfalso; omega)
    | (intro hA
       try simp only [LMonoTy.arrow, LMonoTy.bool, LMonoTy.int, LMonoTy.string, LMonoTy.real,
         LMonoTy.regex, LMonoTy.map, LMonoTy.seq] at hA ⊢
       try (first | rw [hA] | simp only [hA])
       walk [obs_le_of_prob_le (le_refl (prob A (OpCall name (k + 1)))),
        fun p => obs_le_iSup (ArbNat.Nat.arbitrary : SPMF Nat) p,
        fun p => obs_le_iSup (StrataGenerators.PrimitiveGens.genInterestingString : SPMF String) p,
        fun p => obs_le_iSup (StrataGenerators.PrimitiveGens.genRat : SPMF Rat) p,
        fun w p => obs_le_iSup (StrataGenerators.PrimitiveGens.genBiasedBitVec w : SPMF (BitVec w)) p,
        fun m p => obs_le_iSup (genGenerableTy (G := SPMF) fctx octx tvars bctx m) p,
        fun b m τ p => obs_le_iSup (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 b m τ) p,
        fun m τ h p => obs_le_iSup (genIndir (G := SPMF) octx τ
          (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx m) h) p,
        fun m τ fb p => obs_le_iSup (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
          (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx m) fb) p,
        fun p => obs_default_le (α := LExpr') p]
       simp [Function.comp_def, appShare, isArrow]
       try exact div_le_inv_mul (by norm_num))

/-- At depth `0` every draw is a leaf, never an application. -/
theorem off_zero_succ (bctx : BVarCtx) (k : Nat) (name : String) (τ : LMonoTy) :
    prob (genOff fctx octx pctx tvars bctx 0 τ) (OpCall name (k + 1)) = 0 := by
  refine le_antisymm ?_ zero_le
  unfold genOff
  rw [genLExprBaseW.eq_def, prob_eq_obs]
  split
  all_goals first
    | (exfalso; omega)
    | (walk [fun p => obs_le_iSup (ArbNat.Nat.arbitrary : SPMF Nat) p,
        fun p => obs_le_iSup (StrataGenerators.PrimitiveGens.genInterestingString : SPMF String) p,
        fun p => obs_le_iSup (StrataGenerators.PrimitiveGens.genRat : SPMF Rat) p,
        fun w p => obs_le_iSup (StrataGenerators.PrimitiveGens.genBiasedBitVec w : SPMF (BitVec w)) p,
        fun m p => obs_le_iSup (genGenerableTy (G := SPMF) fctx octx tvars bctx m) p,
        fun m τ p => obs_le_iSup (genAppArgTy (G := SPMF) fctx octx tvars bctx m τ) p,
        fun b m τ p => obs_le_iSup (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 b m τ) p,
        fun m τ h p => obs_le_iSup (genIndir (G := SPMF) octx τ
          (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx m) h) p,
        fun m τ fb p => obs_le_iSup (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
          (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx m) fb) p,
        fun p => obs_default_le (α := LExpr') p]
       simp [Function.comp_def])

/-- **One application rule.** `g x` is a call with `k + 1` arguments iff `g` is a call with `k`;
the function position is drawn at `τ' → τ` for the guessed argument type `τ'`. -/
theorem offApp_le (bctx : BVarCtx) (n k : Nat) (name : String) (τ : LMonoTy) :
    prob (offApp fctx octx pctx tvars bctx n τ) (OpCall name (k + 1))
      ≤ expect (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ)
          (fun τ' => prob (genOff fctx octx pctx tvars bctx n (.arrow τ' τ)) (OpCall name k)) := by
  have key : ∀ τ' (arg : LExpr'),
      prob (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx n (.arrow τ' τ) >>= fun fn =>
          pure (LExpr.app () fn arg)) (OpCall name (k + 1))
        = prob (genOff fctx octx pctx tvars bctx n (.arrow τ' τ)) (OpCall name k) := by
    intro τ' arg
    unfold SPMF.prob
    rw [SPMF.expect_bind]
    congr 1; funext fn
    rw [SPMF.expect_pure, OpCall_succ_ind_app]
  unfold offApp genApp
  rw [SPMF.prob_bind]
  refine SPMF.expect_mono fun τ' => ?_
  rw [SPMF.prob_bind]
  simp only [key, SPMF.expect_const]
  exact mul_le_of_le_one_left' (SPMF.mass_le_one _)

/-- The share of `name` among the operators of type `σ`: what `pickOp` draws. -/
noncomputable def pickShare (octx : OpCtx) (name : String) (σ : LMonoTy) : ℝ≥0∞ :=
  ((opsOfType octx σ).count name : ℝ≥0∞) / (opsOfType octx σ).length

theorem sum_ind_op_eq_count (l : List String) (name : String) (σ : LMonoTy) :
    (l.map fun nm => (OpCall name 0).indicator (1 : LExpr' → ℝ≥0∞)
        (LExpr.op () ⟨nm, ()⟩ (some σ))).sum = (l.count name : ℝ≥0∞) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons, beq_iff_eq]
    split <;> simp_all [OpCall, add_comm]

/-- **The innermost function position.** At an arrow type, a draw is the bare operator `name`
only through the operator branch: share at most `1/3` (the `oneOf` at depth `0`; `2/13` above),
times `pickShare`. -/
theorem off_op_le (bctx : BVarCtx) (name : String) (a b : LMonoTy) : ∀ n,
    prob (genOff fctx octx pctx tvars bctx n (.tcons "arrow" [a, b])) (OpCall name 0)
      ≤ 1 / 3 * pickShare octx name (.tcons "arrow" [a, b])
  | 0 => by
    unfold genOff
    rw [genLExprBaseW.eq_1, prob_eq_obs]
    walk [fun p => obs_le_iSup (ArbNat.Nat.arbitrary : SPMF Nat) p,
        fun p => obs_le_iSup (StrataGenerators.PrimitiveGens.genInterestingString : SPMF String) p,
        fun p => obs_le_iSup (StrataGenerators.PrimitiveGens.genRat : SPMF Rat) p,
        fun w p => obs_le_iSup (StrataGenerators.PrimitiveGens.genBiasedBitVec w : SPMF (BitVec w)) p,
        fun m p => obs_le_iSup (genGenerableTy (G := SPMF) fctx octx tvars bctx m) p,
        fun m τ p => obs_le_iSup (genAppArgTy (G := SPMF) fctx octx tvars bctx m τ) p,
        fun b m τ p => obs_le_iSup (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 b m τ) p,
        fun m τ h p => obs_le_iSup (genIndir (G := SPMF) octx τ
          (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx m) h) p,
        fun m τ fb p => obs_le_iSup (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
          (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx m) fb) p,
        fun p => obs_default_le (α := LExpr') p]
    simp [Function.comp_def, sum_ind_op_eq_count]
    simp only [pickShare]
    delta LMonoTy.arrow
    split_ifs <;> [skip; simp]
    rw [ENNReal.div_eq_inv_mul]
  | n + 1 => by
    unfold genOff
    rw [genLExprBaseW.eq_2, prob_eq_obs]
    walk [fun p => obs_le_iSup (ArbNat.Nat.arbitrary : SPMF Nat) p,
        fun p => obs_le_iSup (StrataGenerators.PrimitiveGens.genInterestingString : SPMF String) p,
        fun p => obs_le_iSup (StrataGenerators.PrimitiveGens.genRat : SPMF Rat) p,
        fun w p => obs_le_iSup (StrataGenerators.PrimitiveGens.genBiasedBitVec w : SPMF (BitVec w)) p,
        fun m p => obs_le_iSup (genGenerableTy (G := SPMF) fctx octx tvars bctx m) p,
        fun m τ p => obs_le_iSup (genAppArgTy (G := SPMF) fctx octx tvars bctx m τ) p,
        fun b m τ p => obs_le_iSup (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 b m τ) p,
        fun m τ h p => obs_le_iSup (genIndir (G := SPMF) octx τ
          (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx m) h) p,
        fun m τ fb p => obs_le_iSup (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
          (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx m) fb) p,
        fun p => obs_default_le (α := LExpr') p]
    simp [Function.comp_def, sum_ind_op_eq_count]
    simp only [pickShare]
    delta LMonoTy.arrow
    split_ifs <;> [skip; simp]
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc]
    gcongr
    rw [ENNReal.inv_mul_le_iff (by norm_num) (by norm_num), ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
    norm_num

/-- An expectation of a function supported on one point. -/
theorem expect_of_single {α : Type} [DecidableEq α] (p : SPMF α) (φ : α → ℝ≥0∞) (a : α)
    (h : ∀ x, x ≠ a → φ x = 0) : expect p φ = φ a * prob p {a} := by
  have : φ = fun x => if x = a then φ a else 0 := by
    funext x; by_cases hx : x = a <;> simp [hx, h]
  rw [this]
  have := SPMF.expect_ite_eq p a
  rw [show (fun x => if x = a then φ a else 0) = fun x => φ a * (if x = a then 1 else 0) by
    funext x; split <;> simp, SPMF.expect_mul_left, SPMF.expect_ite_eq, SPMF.prob_singleton]
  simp

/-! ### The chain over the argument positions

Fix the operator `name` with curried type `mkArrow' r as` (arguments `as`, result `r`). After `k`
of its arguments it has type `tyAfter r as k`. -/

/-- The type of `name` applied to its first `k` arguments. -/
def tyAfter (r : LMonoTy) (as : List LMonoTy) (k : Nat) : LMonoTy := LMonoTy.mkArrow' r (as.drop k)

theorem tyAfter_succ {r : LMonoTy} {as : List LMonoTy} {k : Nat} (hk : k < as.length) :
    tyAfter r as k = .tcons "arrow" [as[k], tyAfter r as (k + 1)] := by
  simp only [tyAfter, List.drop_eq_getElem_cons hk, LMonoTy.mkArrow'_cons]
  rfl

/-- The upper bound on the probability that the generator without the Pałka rule makes a call with `k` arguments, given a
bound `γ τ a` on the probability that `genAppArgTy` guesses `a` at target `τ`: the innermost
bare operator, then one application rule per argument. -/
noncomputable def offChain (γ : LMonoTy → LMonoTy → ℝ≥0∞) (ps : ℝ≥0∞) (r : LMonoTy)
    (as : List LMonoTy) : Nat → ℝ≥0∞
  | 0 => 1 / 3 * ps
  | k + 1 => appShare (tyAfter r as (k + 1)) * γ (tyAfter r as (k + 1)) (as.getD k .bool)
      * offChain γ ps r as k

/-- **The generator without the Pałka rule, bounded.** If `name` is an operator only at its type
`mkArrow' r as` (with `as ≠ []`), and `γ` bounds `genAppArgTy`'s guesses, then at every depth the
generator without the Pałka rule makes a full call of `name` with probability at most `offChain … |as|`. -/
theorem off_call_le (bctx : BVarCtx) (name : String) (r : LMonoTy) (as : List LMonoTy)
    (has : as ≠ []) (hps : ∀ σ, σ ≠ LMonoTy.mkArrow' r as → pickShare octx name σ = 0)
    (γ : LMonoTy → LMonoTy → ℝ≥0∞)
    (hγ : ∀ n τ a, prob (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ) {a} ≤ γ τ a) :
    ∀ k, k ≤ as.length →
      (∀ n a b, LMonoTy.tcons "arrow" [a, b] ≠ tyAfter r as k →
          prob (genOff fctx octx pctx tvars bctx n (.tcons "arrow" [a, b])) (OpCall name k) = 0)
      ∧ (∀ n σ, σ ≠ tyAfter r as k → 0 < k →
          prob (genOff fctx octx pctx tvars bctx n σ) (OpCall name k) = 0)
      ∧ ∀ n, prob (genOff fctx octx pctx tvars bctx n (tyAfter r as k)) (OpCall name k)
          ≤ offChain γ (pickShare octx name (LMonoTy.mkArrow' r as)) r as k := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : tyAfter r as 0 = .tcons "arrow" [as[0]'(List.length_pos_iff.2 has),
        tyAfter r as 1] := tyAfter_succ _
    refine ⟨fun n a b hne => le_antisymm ?_ zero_le, fun _ _ _ h => absurd h (by omega),
      fun n => ?_⟩
    · refine (off_op_le fctx octx pctx tvars bctx name a b n).trans (le_of_eq ?_)
      rw [hps _ (by simpa [tyAfter] using hne), mul_zero]
    · rw [h0]
      refine (off_op_le fctx octx pctx tvars bctx name _ _ n).trans (le_of_eq ?_)
      rw [← h0]; simp [offChain, tyAfter]
  | succ k ih =>
    intro hk
    obtain ⟨ihArrow, -, ihBound⟩ := ih (by omega)
    have hk' : k < as.length := by omega
    have hsplit := tyAfter_succ (r := r) (as := as) hk'
    -- The integrand of the application rule is supported on the guess `as[k]`.
    have hsupp : ∀ n σ, ∀ τ', τ' ≠ as[k] → prob (genOff fctx octx pctx tvars bctx n (.arrow τ' σ))
        (OpCall name k) = 0 ∨ LMonoTy.arrow τ' σ = tyAfter r as k := by
      intro n σ τ' _
      by_cases h : LMonoTy.arrow τ' σ = tyAfter r as k
      · exact Or.inr h
      · exact Or.inl (ihArrow n τ' σ h)
    have hzero : ∀ n σ, σ ≠ tyAfter r as (k + 1) →
        prob (genOff fctx octx pctx tvars bctx n σ) (OpCall name (k + 1)) = 0 := by
      intro n σ hσ
      refine le_antisymm ?_ zero_le
      cases n with
      | zero => exact (off_zero_succ fctx octx pctx tvars bctx k name σ).le
      | succ n =>
        refine (off_succ_le_app fctx octx pctx tvars bctx n k name σ).trans ?_
        refine (mul_le_mul_right (offApp_le fctx octx pctx tvars bctx n k name σ) _).trans
          (le_of_eq ?_)
        rw [show (fun τ' => prob (genOff fctx octx pctx tvars bctx n (.arrow τ' σ))
            (OpCall name k)) = fun _ => 0 from funext fun τ' => ihArrow n τ' σ (by
              intro h; apply hσ; rw [hsplit] at h
              simp only [LMonoTy.tcons.injEq, List.cons.injEq] at h
              exact h.2.2.1), SPMF.expect_const, mul_zero, mul_zero]
    refine ⟨fun n a b hne => hzero n _ hne, fun n σ hσ _ => hzero n σ hσ, fun n => ?_⟩
    cases n with
    | zero => rw [off_zero_succ]; exact zero_le
    | succ n =>
      refine (off_succ_le_app fctx octx pctx tvars bctx n k name _).trans ?_
      refine (mul_le_mul_right (offApp_le fctx octx pctx tvars bctx n k name _) _).trans ?_
      rw [expect_of_single _ (fun τ' => prob (genOff fctx octx pctx tvars bctx n
          (.arrow τ' (tyAfter r as (k + 1)))) (OpCall name k)) as[k] (fun τ' hτ' => ihArrow n τ' _ (by
        intro h; apply hτ'; rw [hsplit] at h
        simp only [LMonoTy.tcons.injEq, List.cons.injEq] at h
        exact h.2.1))]
      rw [show LMonoTy.arrow as[k] (tyAfter r as (k + 1)) = tyAfter r as k from hsplit.symm]
      simp only [offChain, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
      calc appShare (tyAfter r as (k + 1)) * (prob (genOff fctx octx pctx tvars bctx n
              (tyAfter r as k)) (OpCall name k) * prob (genAppArgTy (G := SPMF) fctx octx tvars
              bctx n (tyAfter r as (k + 1))) {as[k]})
          ≤ appShare (tyAfter r as (k + 1)) * (offChain γ _ r as k * γ (tyAfter r as (k + 1)) as[k]) := by
            gcongr
            · exact ihBound n
            · exact hγ _ _ _
        _ = _ := by ring

/-- **Below the arity, the generator without the Pałka rule cannot make the call at all**: a call with `k`
arguments needs `k` nested application rules, each of which uses one unit of depth. -/
theorem off_eq_zero_of_lt (bctx : BVarCtx) (name : String) :
    ∀ k n τ, n < k → 0 < k →
      prob (genOff fctx octx pctx tvars bctx n τ) (OpCall name k) = 0
  | 0, _, _, _, hk => absurd hk (by omega)
  | k + 1, 0, τ, _, _ => off_zero_succ fctx octx pctx tvars bctx k name τ
  | k + 1, n + 1, τ, hn, _ => by
    refine le_antisymm ?_ zero_le
    refine (off_succ_le_app fctx octx pctx tvars bctx n k name τ).trans ?_
    refine (mul_le_mul_right (offApp_le fctx octx pctx tvars bctx n k name τ) _).trans
      (le_of_eq ?_)
    rw [show (fun τ' => prob (genOff fctx octx pctx tvars bctx n (.arrow τ' τ)) (OpCall name k))
        = fun _ => 0 from funext fun τ' =>
          off_eq_zero_of_lt bctx name k n _ (by omega) (by omega),
      SPMF.expect_const, mul_zero, mul_zero]

end noPalka

/-! ## Pałka et al.'s rule on: a lower bound -/

theorem prod_map_le_prod_map {α : Type} (l : List α) {f g : α → ℝ≥0∞} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul' (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- **`genLExprBase` makes factory calls.** If `(name, as)` is an Indir candidate at `r`, then at
every depth `n + 1` `genLExprBase` makes a full call of `name` with probability at least
`4/24 · |candidates|⁻¹ · ∏ massFloor aᵢ`. -/
theorem on_call_ge (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) {name : String} {as : List LMonoTy}
    {r : LMonoTy} (hmem : (name, as) ∈ findOpsInCtx octx r) :
    ((4 : ℕ) : ℝ≥0∞) / 24 * (((findOpsInCtx octx r).length : ℝ≥0∞)⁻¹
        * (as.map (massFloor octx)).prod)
      ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) r)
          (OpCall name as.length) := by
  have hi : (findOpsInCtx octx r).length > 0 := List.length_pos_iff.2 (List.ne_nil_of_mem hmem)
  refine genLExprBase_prob_ge_indir fctx octx pctx tvars bctx n r _ hi ?_
  refine le_trans ?_ (prob_genIndir_call_ge octx r _ hi hmem)
  gcongr
  exact prod_map_le_prod_map _ fun a _ => massFloor_le fctx octx pctx tvars bctx n a

/-! ## `genLExpr` -/

section genLExpr
variable (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)

/-- The argument generator `genLExpr` hands its Indir rules (with the default `retryCont := id`). -/
noncomputable def genLExprArg (bctx : BVarCtx) : Nat → LMonoTy → SPMF LExpr'
  | 0 => genLExprBase (G := SPMF) fctx octx pctx tvars bctx 0
  | n + 1 => fun σ => genLExpr (G := SPMF) fctx octx pctx tvars bctx n σ

/-- **`genLExpr`'s Indir rule's share**: `9/10 · 1/2`. -/
theorem genLExpr_prob_ge_indir (bctx : BVarCtx) (d : Nat) (τ : LMonoTy) (E : Set LExpr')
    (hi : (findOpsInCtx octx τ).length > 0) {B : ℝ≥0∞}
    (hB : B ≤ prob (genIndir (G := SPMF) octx τ (genLExprArg fctx octx pctx tvars bctx d) hi) E) :
    9 / 20 * B ≤ prob (genLExpr (G := SPMF) fctx octx pctx tvars bctx d τ) E := by
  have key : prob (genLExpr (G := SPMF) fctx octx pctx tvars bctx d τ) E
      = (prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx d τ) E
          + 9 * ((prob (genIndir (G := SPMF) octx τ (genLExprArg fctx octx pctx tvars bctx d) hi) E
            + prob (genIndirPoly (G := SPMF) fctx octx pctx tvars bctx d τ 3
                (genLExprArg fctx octx pctx tvars bctx d)) E) / 2)) / 10 := by
    unfold genLExpr
    rw [dif_pos hi, SPMF.prob_frequency]
    cases d <;>
    · simp only [genLExprArg, id, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        SPMF.prob_oneOf]
      norm_num
  rw [key]
  calc 9 / 20 * B = 9 * (B / 2) / 10 := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, show (20 : ℝ≥0∞) = 2 * 10 by norm_num,
          ENNReal.mul_inv (by simp) (by simp)]
        ring
    _ ≤ 9 * ((prob (genIndir (G := SPMF) octx τ (genLExprArg fctx octx pctx tvars bctx d) hi) E
            + prob (genIndirPoly (G := SPMF) fctx octx pctx tvars bctx d τ 3
                (genLExprArg fctx octx pctx tvars bctx d)) E) / 2) / 10 := by
        gcongr; exact hB.trans le_self_add
    _ ≤ _ := by gcongr; exact le_add_self

/-- `genLExpr` succeeds at least as often as a tenth of `genLExprBase`. -/
theorem one_div_mul_le_div_add (P X W : ℝ≥0∞) : 1 / W * P ≤ (P + X) / W := by
  rw [one_div, ENNReal.div_eq_inv_mul]
  gcongr
  exact le_self_add

theorem genLExpr_mass_ge (bctx : BVarCtx) (d : Nat) (τ : LMonoTy) :
    1 / 10 * mass (genLExprBase (G := SPMF) fctx octx pctx tvars bctx d τ)
      ≤ mass (genLExpr (G := SPMF) fctx octx pctx tvars bctx d τ) := by
  rw [← SPMF.expect_one, ← SPMF.expect_one]
  unfold genLExpr
  dsimp only
  by_cases hi : (findOpsInCtx octx τ).length > 0
  · rw [dif_pos hi, SPMF.expect_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
      add_zero]
    refine le_trans (le_of_eq ?_) (one_div_mul_le_div_add _ _ _)
    norm_num
  · rw [dif_neg hi, SPMF.expect_oneOf (by simp)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.length_cons, List.length_nil]
    refine le_trans ?_ (one_div_mul_le_div_add _ _ _)
    gcongr
    norm_num

theorem genLExprArg_mass_ge (bctx : BVarCtx) (d : Nat) (τ : LMonoTy) :
    1 / 10 * massFloor octx τ ≤ mass (genLExprArg fctx octx pctx tvars bctx d τ) := by
  cases d with
  | zero =>
    exact (mul_le_of_le_one_left' (by norm_num)).trans
      (massFloor_le fctx octx pctx tvars bctx 0 τ)
  | succ d =>
    exact (mul_le_mul_right (massFloor_le fctx octx pctx tvars bctx d τ) _).trans
      (genLExpr_mass_ge fctx octx pctx tvars bctx d τ)

/-- **`genLExpr` makes factory calls**, at every depth `d`: with probability at least
`9/20 · |candidates|⁻¹ · ∏ (massFloor aᵢ / 10)`. -/
theorem genLExpr_call_ge (bctx : BVarCtx) (d : Nat) {name : String} {as : List LMonoTy}
    {r : LMonoTy} (hmem : (name, as) ∈ findOpsInCtx octx r) :
    9 / 20 * (((findOpsInCtx octx r).length : ℝ≥0∞)⁻¹
        * (as.map fun a => 1 / 10 * massFloor octx a).prod)
      ≤ prob (genLExpr (G := SPMF) fctx octx pctx tvars bctx d r) (OpCall name as.length) := by
  have hi : (findOpsInCtx octx r).length > 0 := List.length_pos_iff.2 (List.ne_nil_of_mem hmem)
  refine genLExpr_prob_ge_indir fctx octx pctx tvars bctx d r _ hi ?_
  refine le_trans ?_ (prob_genIndir_call_ge octx r _ hi hmem)
  gcongr
  exact prod_map_le_prod_map _ fun a _ => genLExprArg_mass_ge fctx octx pctx tvars bctx d a

end genLExpr

end StrataGenerators.PalkaAblation
