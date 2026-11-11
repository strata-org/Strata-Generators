import StrataGenerators.PalkaAblation.Bounds

/-!
# Pałka et al.'s rule vs. the STLC application rule, over a class of factory functions

`Bounds.lean` compares the two generators one operator at a time. Here the event is a full call of
*any* operator of a class `C`: the operators returning `r` whose arity lies in `[k + 1, M]` and
whose arguments are all base types (`bool`, `int`, `string`, `real`, bitvectors).

* `off_callIn_le`: the ablated generator (`genLExprBase` without its Indir and IndirPoly branches,
  i.e. with only the STLC application rule left) makes such a call with probability at most
  `1/9 · (1/13)^k`. A call with at least `k + 1` arguments needs `k + 1` nested application
  rules, and each is chosen with share at most `1/9` (`1/13` at an arrow type).
* `on_callIn_ge`: `genLExprBase` makes one with probability at least
  `1/6 · |C|/F · (7/24)^M`, where `F` is the number of operators returning `r`. Its Indir branch
  (share `1/6`) picks an operator of `C` with probability `|C|/F`, and each of its at most `M`
  base-typed arguments succeeds with probability at least `7/24`.
* `palka_more_frequent`: so Pałka et al.'s rule wins whenever `C` makes up a large enough fraction
  of the operators returning `r`: `6 · 24^M · F < 9 · 13^k · 7^M · |C|`.
* `palka_more_frequent_three`: the case of exactly three arguments. More than one in six of the
  operators returning `r` is enough.
* `palka_more_frequent_three_four`: three or four arguments. More than six in eleven is enough.
* `genLExpr_below_arity`: at every depth below an operator's arity, the ablated generator never
  calls it, while `genLExpr` does with positive probability.

None of this depends on a particular factory: every statement quantifies over the operator context,
the depth `n + 1`, and the variable contexts. Nothing is computed, so no `native_decide`.

The number of operators matters only as the fraction `|C|/F`: Pałka et al.'s rule picks uniformly
among the `F` operators returning `r`, so adding operators outside `C` dilutes it, while the
STLC rule's bound does not depend on the operators at all.
-/

namespace StrataGenerators.PalkaAblation

open Lambda
open scoped ENNReal
open SPMF (prob expect mass)

/-! ## The event: an application spine of length at least `k` -/

/-- The root of the term is at least `k` nested applications: `.app (.app (⋯) _) _`. -/
def Spine : Nat → Set LExpr'
  | 0 => Set.univ
  | k + 1 => {e | ∃ g x, e = .app () g x ∧ g ∈ Spine k}

section spineSimp
variable {k : Nat} {m : Unit}

@[simp] theorem Spine_succ_ind_const (c) : (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.const m c : LExpr') = 0 := by
  simp [Spine]
@[simp] theorem Spine_succ_ind_op (o) (ty) : (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.op m o ty : LExpr') = 0 := by
  simp [Spine]
@[simp] theorem Spine_succ_ind_bvar (i) : (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.bvar m i : LExpr') = 0 := by
  simp [Spine]
@[simp] theorem Spine_succ_ind_fvar (x) (ty) : (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.fvar m x ty : LExpr') = 0 := by
  simp [Spine]
@[simp] theorem Spine_succ_ind_abs (x ty) (e : LExpr') : (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.abs m x ty e) = 0 := by
  simp [Spine]
@[simp] theorem Spine_succ_ind_quant (q x ty) (t e : LExpr') : (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.quant m q x ty t e) = 0 := by
  simp [Spine]
@[simp] theorem Spine_succ_ind_ite (c t e : LExpr') : (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.ite m c t e) = 0 := by
  simp [Spine]
@[simp] theorem Spine_succ_ind_eq (a b : LExpr') : (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.eq m a b) = 0 := by
  simp [Spine]
@[simp] theorem Spine_succ_ind_app (g x : LExpr') :
    (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.app m g x) = (Spine k).indicator (1 : LExpr' → ℝ≥0∞) g := by
  by_cases h : g ∈ Spine k <;> simp [Spine, h]

@[simp] theorem Spine_succ_ind_intConst (i : Int) :
    (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.intConst m i) = 0 := Spine_succ_ind_const _
@[simp] theorem Spine_succ_ind_boolConst (b : Bool) :
    (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.boolConst m b) = 0 := Spine_succ_ind_const _
@[simp] theorem Spine_succ_ind_strConst (x : String) :
    (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.strConst m x) = 0 := Spine_succ_ind_const _
@[simp] theorem Spine_succ_ind_rationalConst (r : Rat) :
    (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.rationalConst m r) = 0 := Spine_succ_ind_const _
@[simp] theorem Spine_succ_ind_bitvecConst (w : Nat) (b : BitVec w) :
    (Spine (k + 1)).indicator (1 : LExpr' → ℝ≥0∞) (LExpr.bitvecConst m w b) = 0 :=
  Spine_succ_ind_const _

end spineSimp

/-- A spine of length `k` is also one of every smaller length. -/
theorem Spine_anti : ∀ {j k : Nat}, j ≤ k → Spine k ⊆ Spine j
  | 0, _, _ => Set.subset_univ _
  | j + 1, 0, h => absurd h (by omega)
  | j + 1, k + 1, h => by
    rintro e ⟨g, x, rfl, hg⟩
    exact ⟨g, x, rfl, Spine_anti (by omega) hg⟩

/-- A call with `k` arguments is a spine of length `k`. -/
theorem OpCall_subset_Spine (name : String) : ∀ k, OpCall name k ⊆ Spine k
  | 0 => Set.subset_univ _
  | k + 1 => by
    rintro e ⟨g, x, rfl, hg⟩
    exact ⟨g, x, rfl, OpCall_subset_Spine name k hg⟩

/-! ## The ablated generator: an upper bound -/

section ablated
variable (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)

/-- At depth `n + 1`, an application at the root comes only from the application branch. -/
theorem off_succ_le_app_spine (bctx : BVarCtx) (n k : Nat) (τ : LMonoTy) :
    prob (genOff fctx octx pctx tvars bctx (n + 1) τ) (Spine (k + 1))
      ≤ appShare τ * prob (offApp fctx octx pctx tvars bctx n τ) (Spine (k + 1)) := by
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
       walk [obs_le_of_prob_le (le_refl (prob A (Spine (k + 1)))),
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
theorem off_zero_spine (bctx : BVarCtx) (k : Nat) (τ : LMonoTy) :
    prob (genOff fctx octx pctx tvars bctx 0 τ) (Spine (k + 1)) = 0 := by
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

/-- One application rule: `g x` is a spine of length `k + 1` iff `g` is one of length `k`. -/
theorem offApp_le_spine (bctx : BVarCtx) (n k : Nat) (τ : LMonoTy) :
    prob (offApp fctx octx pctx tvars bctx n τ) (Spine (k + 1))
      ≤ expect (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ)
          (fun τ' => prob (genOff fctx octx pctx tvars bctx n (.arrow τ' τ)) (Spine k)) := by
  have key : ∀ τ' (arg : LExpr'),
      prob (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx n (.arrow τ' τ) >>= fun fn =>
          pure (LExpr.app () fn arg)) (Spine (k + 1))
        = prob (genOff fctx octx pctx tvars bctx n (.arrow τ' τ)) (Spine k) := by
    intro τ' arg
    unfold SPMF.prob
    rw [SPMF.expect_bind]
    congr 1; funext fn
    rw [SPMF.expect_pure, Spine_succ_ind_app]
  unfold offApp genApp
  rw [SPMF.prob_bind]
  refine SPMF.expect_mono fun τ' => ?_
  rw [SPMF.prob_bind]
  simp only [key, SPMF.expect_const]
  exact mul_le_of_le_one_left' (SPMF.mass_le_one _)

theorem prob_le_one' {α : Type} (p : SPMF α) (E : Set α) : prob p E ≤ 1 :=
  (SPMF.prob_le_mass _ _).trans (SPMF.mass_le_one _)

theorem appShare_arrow (a b : LMonoTy) : appShare (.arrow a b) = 1 / 13 := by
  simp [appShare, isArrow, LMonoTy.arrow]

/-- **The ablated generator rarely builds long spines.** At every depth and type, the root is
`k + 1` nested applications with probability at most `appShare τ · (1/13)^k`. -/
theorem off_spine_le (bctx : BVarCtx) : ∀ n k τ,
    prob (genOff fctx octx pctx tvars bctx n τ) (Spine (k + 1)) ≤ appShare τ * (1 / 13) ^ k
  | 0, k, τ => by rw [off_zero_spine]; exact zero_le
  | n + 1, 0, τ => by
    refine (off_succ_le_app_spine fctx octx pctx tvars bctx n 0 τ).trans ?_
    rw [pow_zero, mul_one]
    exact mul_le_of_le_one_right' (prob_le_one' _ _)
  | n + 1, k + 1, τ => by
    calc prob (genOff fctx octx pctx tvars bctx (n + 1) τ) (Spine (k + 1 + 1))
        ≤ appShare τ * prob (offApp fctx octx pctx tvars bctx n τ) (Spine (k + 1 + 1)) :=
          off_succ_le_app_spine fctx octx pctx tvars bctx n (k + 1) τ
      _ ≤ appShare τ * expect (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ)
            (fun _ => (1 / 13 : ℝ≥0∞) * (1 / 13) ^ k) := by
          gcongr
          refine (offApp_le_spine fctx octx pctx tvars bctx n (k + 1) τ).trans ?_
          refine SPMF.expect_mono fun τ' => ?_
          have := off_spine_le bctx n k (.arrow τ' τ)
          rwa [appShare_arrow] at this
      _ ≤ appShare τ * (1 / 13) ^ (k + 1) := by
          gcongr
          rw [SPMF.expect_const, pow_succ']
          exact mul_le_of_le_one_left' (SPMF.mass_le_one _)

end ablated

/-! ## The class of operators and its calls -/

/-- Whether a type is a base type with a literal generator: `bool`, `int`, `string`, `real`, or a
bitvector type. -/
def isBaseTy : LMonoTy → Bool
  | .tcons "bool" [] => true
  | .tcons "int" [] => true
  | .tcons "string" [] => true
  | .tcons "real" [] => true
  | .bitvec _ => true
  | _ => false

theorem massFloor_ge_of_isBaseTy (octx : OpCtx) {a : LMonoTy} (h : isBaseTy a = true) :
    7 / 24 ≤ massFloor octx a := by
  unfold isBaseTy at h
  split at h <;> simp only [Bool.false_eq_true] at h <;> simp only [massFloor]
  all_goals first
    | exact le_rfl
    | exact ENNReal.div_le_div_left (by norm_num) _

/-- The operators returning `r` with between `lo` and `hi` arguments, all of base type. -/
def classOps (octx : OpCtx) (r : LMonoTy) (lo hi : Nat) : List (String × List LMonoTy) :=
  (findOpsInCtx octx r).filter fun p =>
    decide (lo ≤ p.2.length) && decide (p.2.length ≤ hi) && p.2.all isBaseTy

/-- The event "the root is a full call of an operator of `C`". -/
def CallIn (C : List (String × List LMonoTy)) : Set LExpr' :=
  {e | ∃ p ∈ C, e ∈ OpCall p.1 p.2.length}

theorem CallIn_classOps_subset_Spine (octx : OpCtx) (r : LMonoTy) (lo hi : Nat) :
    CallIn (classOps octx r lo hi) ⊆ Spine lo := by
  rintro e ⟨p, hp, he⟩
  simp only [classOps, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact Spine_anti hp.2.1.1 (OpCall_subset_Spine p.1 _ he)

/-- **The STLC rule, over the class.** Every operator of `classOps octx r (k + 1) hi` has at least
`k + 1` arguments, so the ablated generator calls one with probability at most `1/9 · (1/13)^k`. -/
theorem off_callIn_le (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (r : LMonoTy) (k hi : Nat) :
    prob (genOff fctx octx pctx tvars bctx n r) (CallIn (classOps octx r (k + 1) hi))
      ≤ 1 / 9 * (1 / 13) ^ k := by
  refine (SPMF.prob_mono (CallIn_classOps_subset_Spine octx r (k + 1) hi)).trans ?_
  refine (off_spine_le fctx octx pctx tvars bctx n k r).trans ?_
  gcongr
  unfold appShare
  split
  · exact ENNReal.div_le_div_left (by norm_num) _
  · exact le_rfl

/-! ## Pałka et al.'s rule: a lower bound -/

theorem sum_map_filter_le {α : Type} (l : List α) (P : α → Bool) (f : α → ℝ≥0∞) :
    ((l.filter P).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : P a
    · simp only [List.filter_cons, h, ↓reduceIte, List.map_cons, List.sum_cons]
      gcongr
    · simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      exact ih.trans le_add_self

theorem length_mul_le_sum {α : Type} (l : List α) (f : α → ℝ≥0∞) {c : ℝ≥0∞}
    (h : ∀ a ∈ l, c ≤ f a) : (l.length : ℝ≥0∞) * c ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, Nat.cast_succ, List.map_cons, List.sum_cons, add_mul, one_mul]
    rw [add_comm]
    gcongr
    · exact h a (by simp)
    · exact ih fun b hb => h b (by simp [hb])

theorem pow_length_le_prod {α : Type} (l : List α) (f : α → ℝ≥0∞) {c : ℝ≥0∞}
    (h : ∀ a ∈ l, c ≤ f a) : c ^ l.length ≤ (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, pow_succ', List.map_cons, List.prod_cons]
    exact mul_le_mul' (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- **The Indir rule, over the class.** If every operator of the sublist `C` of candidates has
`∏ Pr(argument i succeeds) ≥ c`, the rule calls one of them with probability at least
`|C|/F · c`. -/
theorem prob_genIndir_callIn_ge (octx : OpCtx) (τ : LMonoTy) (genArg : LMonoTy → SPMF LExpr')
    (h : (findOpsInCtx octx τ).length > 0) (P : String × List LMonoTy → Bool) {c : ℝ≥0∞}
    (hc : ∀ p ∈ (findOpsInCtx octx τ).filter P, c ≤ (p.2.map fun a => mass (genArg a)).prod) :
    ((((findOpsInCtx octx τ).filter P).length : ℝ≥0∞) * c) / (findOpsInCtx octx τ).length
      ≤ prob (genIndir (G := SPMF) octx τ genArg h) (CallIn ((findOpsInCtx octx τ).filter P)) := by
  have hne : findOpsInCtx octx τ ≠ [] := List.ne_nil_of_length_pos h
  unfold genIndir
  rw [SPMF.prob_bind]
  unfold SPMF.prob
  rw [SPMF.expect_elements hne]
  gcongr
  refine le_trans ?_ (sum_map_filter_le _ P _)
  refine length_mul_le_sum _ _ fun p hp => ?_
  obtain ⟨name, as⟩ := p
  have hcall := prob_mapM_mkApps genArg name as
    (.op () ⟨name, ()⟩ (some (as.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) 0
    (show _ ∈ OpCall name 0 from ⟨_, rfl⟩)
  rw [Nat.zero_add] at hcall
  unfold SPMF.prob at hcall
  refine (hc _ hp).trans (le_of_eq_of_le hcall.symm ?_)
  have hsub : OpCall name as.length ⊆ CallIn ((findOpsInCtx octx τ).filter P) :=
    fun e he => ⟨(name, as), hp, he⟩
  refine SPMF.expect_mono fun e => ?_
  exact Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le) e

/-- **Pałka et al.'s rule, over the class.** `genLExprBase` calls an operator of
`classOps octx r lo hi` with probability at least `1/6 · |C|/F · (7/24)^hi`. -/
theorem on_callIn_ge (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (r : LMonoTy) (lo hi : Nat)
    (hF : (findOpsInCtx octx r).length > 0) :
    ((4 : ℕ) : ℝ≥0∞) / 24 * ((((classOps octx r lo hi).length : ℝ≥0∞) * (7 / 24) ^ hi)
        / (findOpsInCtx octx r).length)
      ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) r)
          (CallIn (classOps octx r lo hi)) := by
  refine genLExprBase_prob_ge_indir fctx octx pctx tvars bctx n r _ hF ?_
  refine prob_genIndir_callIn_ge octx r _ hF _ fun p hp => ?_
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨-, ⟨-, hlen⟩, hbase⟩ := hp
  calc (7 / 24 : ℝ≥0∞) ^ hi ≤ (7 / 24) ^ p.2.length :=
        pow_le_pow_of_le_one zero_le (ENNReal.div_le_of_le_mul (by norm_num)) hlen
    _ ≤ _ := pow_length_le_prod _ _ fun a ha =>
        (massFloor_ge_of_isBaseTy octx (hbase a ha)).trans
          (massFloor_le fctx octx pctx tvars bctx n a)

/-! ## The comparison -/

/-- The arithmetic of the comparison: `1/9 · (1/13)^k < 4/24 · (|C| · (7/24)^M) / F` whenever
`6 · 24^M · F < 9 · 13^k · 7^M · |C|`. -/
theorem compare_bounds (k M F C : Nat) (hF : 0 < F)
    (h : 6 * 24 ^ M * F < 9 * 13 ^ k * 7 ^ M * C) :
    (1 / 9 : ℝ≥0∞) * (1 / 13) ^ k < ((4 : ℕ) : ℝ≥0∞) / 24 * (((C : ℝ≥0∞) * (7 / 24) ^ M) / F) := by
  have hF' : (F : ℝ≥0∞) ≠ 0 := by exact_mod_cast hF.ne'
  rw [← ENNReal.toReal_lt_toReal (by simp [ENNReal.mul_eq_top])
    (by simp [ENNReal.mul_eq_top, ENNReal.div_eq_top, hF'])]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hr : ((6 * 24 ^ M * F : ℕ) : ℝ) < ((9 * 13 ^ k * 7 ^ M * C : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hr
  rw [div_pow, div_pow, one_pow]
  rw [show (1 : ℝ) / 9 * (1 / 13 ^ k) = 1 / (9 * 13 ^ k) by field_simp,
    show ((4 : ℕ) : ℝ) / 24 * (C * (7 ^ M / 24 ^ M) / F) = 4 * C * 7 ^ M / (24 * 24 ^ M * F) by
      push_cast; field_simp]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Pałka et al.'s rule calls the operators of a class more often than the STLC rule.**
Let `C` be the operators returning `r` with between `k + 1` and `M` arguments, all of base type,
and `F` all operators returning `r`. If `6 · 24^M · F < 9 · 13^k · 7^M · |C|`, i.e. `C` is a
large enough fraction of the operators returning `r`, then at every depth `n + 1` and in every
variable context, `genLExprBase` makes a full call of an operator of `C` strictly more often than
the same generator with its Indir and IndirPoly branches removed (only the STLC application rule
left). -/
theorem palka_more_frequent (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (r : LMonoTy) (k M : Nat)
    (hmany : 6 * 24 ^ M * (findOpsInCtx octx r).length
      < 9 * 13 ^ k * 7 ^ M * (classOps octx r (k + 1) M).length) :
    prob (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx (n + 1) r)
        (CallIn (classOps octx r (k + 1) M))
      < prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) r)
          (CallIn (classOps octx r (k + 1) M)) := by
  have hF : 0 < (findOpsInCtx octx r).length := by
    rcases Nat.eq_zero_or_pos (findOpsInCtx octx r).length with h0 | h0
    · have : (classOps octx r (k + 1) M).length = 0 := by
        simp [classOps, List.eq_nil_of_length_eq_zero h0]
      rw [this] at hmany; omega
    · exact h0
  calc _ ≤ 1 / 9 * (1 / 13) ^ k := off_callIn_le fctx octx pctx tvars bctx (n + 1) r k M
    _ < _ := compare_bounds k M _ _ hF hmany
    _ ≤ _ := on_callIn_ge fctx octx pctx tvars bctx n r (k + 1) M hF

/-- **Three arguments.** If more than one in six of the operators returning `r` take exactly
three arguments, all of base type, Pałka et al.'s rule calls those operators strictly more often
than the STLC rule, at every depth `n + 1` and in every variable context. -/
theorem palka_more_frequent_three (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (r : LMonoTy)
    (hmany : (findOpsInCtx octx r).length < 6 * (classOps octx r 3 3).length) :
    prob (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx (n + 1) r)
        (CallIn (classOps octx r 3 3))
      < prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) r)
          (CallIn (classOps octx r 3 3)) :=
  palka_more_frequent fctx octx pctx tvars bctx n r 2 3 (by norm_num; omega)

/-- **Three or four arguments.** If more than six in eleven of the operators returning `r` take
three or four arguments, all of base type, Pałka et al.'s rule calls those operators strictly more
often than the STLC rule, at every depth `n + 1` and in every variable context. -/
theorem palka_more_frequent_three_four (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (r : LMonoTy)
    (hmany : 6 * (findOpsInCtx octx r).length < 11 * (classOps octx r 3 4).length) :
    prob (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx (n + 1) r)
        (CallIn (classOps octx r 3 4))
      < prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) r)
          (CallIn (classOps octx r 3 4)) :=
  palka_more_frequent fctx octx pctx tvars bctx n r 2 4 (by norm_num; omega)

/-! ## Below the arity, only Pałka et al.'s rule makes the call -/

/-- **Below its arity, only the Indir rules make the call.** For an Indir candidate
`(name, as)` at `r` whose argument types all have a positive mass floor (in particular, all base
types), and every depth `d` below its arity, the ablated generator never makes the call, while
`genLExpr` makes it with positive probability. -/
theorem genLExpr_below_arity (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) {name : String} {as : List LMonoTy}
    {r : LMonoTy} (hmem : (name, as) ∈ findOpsInCtx octx r)
    (hpos : ∀ a ∈ as, 0 < massFloor octx a) {d : Nat} (hd : d < as.length) :
    prob (genLExprBaseW (G := SPMF) fctx octx pctx tvars 0 0 bctx d r) (OpCall name as.length) = 0
      ∧ 0 < prob (genLExpr (G := SPMF) fctx octx pctx tvars bctx d r) (OpCall name as.length) := by
  refine ⟨off_eq_zero_of_lt fctx octx pctx tvars bctx name _ _ _ hd (by omega), ?_⟩
  refine lt_of_lt_of_le ?_ (genLExpr_call_ge fctx octx pctx tvars bctx d hmem)
  refine ENNReal.mul_pos (by norm_num) (ENNReal.mul_pos (ENNReal.inv_ne_zero.2
    (ENNReal.natCast_ne_top _)) ?_).ne'
  refine List.prod_ne_zero fun h0 => ?_
  obtain ⟨a, ha, h⟩ := List.mem_map.1 h0
  exact (ENNReal.mul_pos (by norm_num) (hpos a ha).ne').ne' h

end StrataGenerators.PalkaAblation
