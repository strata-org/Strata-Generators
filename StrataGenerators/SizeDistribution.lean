import StrataGenerators.HasTypeAGen
import Basalt.Walk.Entry
import Basalt.Walk.Sound

/-!
# Shared lemmas for the size-distribution proofs

Lower bounds on `SPMF.prob` for the choice combinators (`frequency`, `oneOf`, `elements`), the
`ennr` closing tactic, and the probability that a type draw is `bool`. The statement-level results
are in `StrataGenerators.SizeDistributionStmt` and `StrataGenerators.SizeDistributionLoops`.
-/

open Lambda RandomChoice SPMF NNReal ENNReal

namespace StrataGenerators.SizeDistribution

/-- Close an inequality between two closed `ℝ≥0∞` expressions built from numerals, `+`, `*`, `/`,
`⁻¹` and powers, by moving it to `ℝ`. -/
macro "ennr" : tactic => `(tactic| (
  rw [← ENNReal.toReal_le_toReal (by simp [ENNReal.div_eq_top, ENNReal.mul_eq_top])
    (by simp [ENNReal.div_eq_top, ENNReal.mul_eq_top])]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_one, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_add,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  norm_num))

/-- `a/b · c/d = ac/bd` for a finite non-zero `b`. The statement-level bounds are products of one
branch-weight share and one or two uniform body-length shares; this is what collects such a product
into a single closed-form fraction in the size. -/
theorem div_mul_div (a c d : ℝ≥0∞) {b : ℝ≥0∞} (hb : b ≠ 0) (hb' : b ≠ ⊤) :
    a / b * (c / d) = a * c / (b * d) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hb) (Or.inl hb')]
  ring

/-- Finish a closed-form identity between two fractions built from numerals and
`(n : ℝ≥0∞) + k`. -/
macro "frac_eq" : tactic => `(tactic|
  (rw [ENNReal.div_eq_div_iff (by first | finiteness | positivity | norm_num)
      (by first | finiteness | positivity | norm_num)
      (by first | finiteness | positivity | norm_num)
      (by first | finiteness | positivity | norm_num)]
   ring))

/-- A lower bound on the mass of one identifier draw (`genIdentName`, `genFreshName`,
`genFreshLabel`): its terminating branch. The generators are `partial_fixpoint`, so this is all the
mass that is proved. -/
noncomputable def nameMass : ℝ≥0∞ := 1 / 2

theorem prob_frequency_ge {α} (gs : List (Nat × (Unit → SPMF α))) (h : 0 < (gs.map Prod.fst).sum)
    (i : Nat) (hi : i < gs.length) (E : Set α) :
    ((gs[i].1 : ℝ≥0∞) / (((gs.map Prod.fst).sum : ℕ) : ℝ≥0∞)) * prob (gs[i].2 ()) E
      ≤ prob (frequency gs h) E := by
  rw [prob_frequency, ← ENNReal.mul_div_right_comm]
  refine ENNReal.div_le_div_right ?_ _
  refine List.le_sum_of_mem ?_
  exact List.mem_map.mpr ⟨gs[i], List.getElem_mem hi, rfl⟩

theorem prob_oneOf_ge {α} (gs : List (Unit → SPMF α)) (h : gs ≠ [])
    (i : Nat) (hi : i < gs.length) (E : Set α) :
    (1 / (gs.length : ℝ≥0∞)) * prob (gs[i] ()) E ≤ prob (oneOf gs h) E := by
  rw [prob_oneOf, ← ENNReal.mul_div_right_comm, one_mul]
  refine ENNReal.div_le_div_right ?_ _
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨gs[i], List.getElem_mem hi, rfl⟩)

theorem sum_zipWith_le {α} {E : Set α} {lbs : List ℝ≥0∞} {gs : List (Nat × (Unit → SPMF α))}
    (h : List.Forall₂ (fun lb g => lb ≤ prob (g.2 ()) E) lbs gs) :
    (List.zipWith (fun lb g => (g.1 : ℝ≥0∞) * lb) lbs gs).sum
      ≤ (gs.map fun p => (p.1 : ℝ≥0∞) * prob (p.2 ()) E).sum := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
    gcongr

/-- A lower bound on a weighted choice from a lower bound on each branch. -/
theorem prob_frequency_ge_of_forall₂ {α} (gs : List (Nat × (Unit → SPMF α)))
    (h : 0 < (gs.map Prod.fst).sum) (E : Set α) (lbs : List ℝ≥0∞)
    (hlb : List.Forall₂ (fun lb g => lb ≤ prob (g.2 ()) E) lbs gs) :
    (List.zipWith (fun lb g => (g.1 : ℝ≥0∞) * lb) lbs gs).sum
        / (((gs.map Prod.fst).sum : ℕ) : ℝ≥0∞)
      ≤ prob (frequency gs h) E := by
  rw [prob_frequency]
  exact ENNReal.div_le_div_right (sum_zipWith_le hlb) _

theorem sum_le_of_forall₂ {α} {E : Set α} {lbs : List ℝ≥0∞} {gs : List (Unit → SPMF α)}
    (h : List.Forall₂ (fun lb g => lb ≤ prob (g ()) E) lbs gs) :
    lbs.sum ≤ (gs.map fun g => prob (g ()) E).sum := by
  induction h with
  | nil => simp
  | cons hab _ ih => simp only [List.sum_cons, List.map_cons]; gcongr

/-- A lower bound on a uniform choice from a lower bound on each branch. -/
theorem prob_oneOf_ge_of_forall₂ {α} (gs : List (Unit → SPMF α)) (h : gs ≠ []) (E : Set α)
    (lbs : List ℝ≥0∞) (hlb : List.Forall₂ (fun lb g => lb ≤ prob (g ()) E) lbs gs) :
    lbs.sum / (gs.length : ℝ≥0∞) ≤ prob (oneOf gs h) E := by
  rw [prob_oneOf]
  exact ENNReal.div_le_div_right (sum_le_of_forall₂ hlb) _

theorem prob_elements_of_forall {α} {xs : List α} (hne : xs ≠ []) {E : Set α}
    (h : ∀ x ∈ xs, x ∈ E) : prob (elements xs hne : SPMF α) E = 1 := by
  unfold prob
  rw [expect_elements]
  have : xs.map (E.indicator 1) = xs.map (fun _ => (1 : ℝ≥0∞)) :=
    List.map_congr_left fun x hx => by simp [Set.indicator, h x hx]
  rw [this, List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
  exact ENNReal.div_self (by simpa using hne) (ENNReal.natCast_ne_top _)



theorem prob_pickBaseType_bool : 1 / 6 ≤ prob (pickBaseType (G := SPMF)) {LMonoTy.bool} := by
  unfold pickBaseType
  refine le_trans ?_ (prob_oneOf_ge_of_forall₂ _ _ _ [1, 0, 0, 0, 0, 0] ?_)
  · ennr
  · simp only [List.forall₂_cons, List.Forall₂.nil, and_true, zero_le, and_true]
    exact (prob_pure_of_mem (Set.mem_singleton _)).ge

/-- `genLMonoTy` draws `bool` with probability at least `1/12`, at every depth. -/
theorem prob_genLMonoTy_bool (tvars : List TyIdentifier) (n : Nat) :
    1 / 12 ≤ prob (genLMonoTy (G := SPMF) tvars n) {LMonoTy.bool} := by
  have hb := prob_pickBaseType_bool
  cases n with
  | zero =>
    rw [genLMonoTy]; split
    · refine le_trans ?_ (prob_oneOf_ge_of_forall₂ _ _ _ [1/6, 0] ?_)
      · ennr
      · simpa using hb
    · exact le_trans (by ennr) hb
  | succ n =>
    rw [genLMonoTy]; split
    all_goals
      refine le_trans ?_ (prob_frequency_ge_of_forall₂ _ _ _ [1/6, 0] ?_)
      · simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
          List.map_cons, List.map_nil, mul_zero, add_zero, Nat.cast_ofNat]
        ennr
      · simpa using hb

end StrataGenerators.SizeDistribution
