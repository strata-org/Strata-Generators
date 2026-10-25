import StrataGenerators.HasTypeAGen
import Basalt.Walk.Entry
import Basalt.Walk.Sound

/-!
# How the size parameter shapes the distribution of `genLExprBase`

The support proofs in this package say which expressions `genLExprBase … size τ` *can* produce. This
module reads the same generator as a measure (`SPMF.prob`) and answers two questions about the
size parameter:

1. **For a given size, what does the distribution look like?** Which root forms (constant, variable,
   `ite`, `eq`, quantifier, application, …) have probability zero, and which have a guaranteed
   positive share?
2. **What is the threshold for a good size?** The least size at which a single draw can exhibit every
   form of the simply-typed fragment, and a guaranteed probability that it does.

## Results, for the `bool` target

| size | root form      | statement                                       | where |
|------|----------------|-------------------------------------------------|-------|
| 0    | any compound   | probability `0` (any type, any context)         | `prob_compound_size_zero` |
| any  | constant       | `≥ 1/24 ≈ 4.2e-2`                               | `prob_const_ge` |
| ≥ 1  | `ite`          | `≥ 343/165888 ≈ 2.1e-3`                         | `prob_ite_ge` |
| ≥ 1  | `eq`           | `≥ 49/829440 ≈ 5.9e-5`                          | `prob_eq_ge` |
| ≥ 1  | `∀`            | `≥ 49/99532800 ≈ 4.9e-7`                        | `prob_forall_ge` |
| 1    | application    | probability `0` (closed setting)                | `prob_closed_app_size_one` |
| ≥ 2  | application    | `≥ 7/1244160 ≈ 5.6e-6`                          | `prob_app_ge` |

Every lower bound holds in **every** context — any free variables, any factory, any binders — which
is why the constants are small: they are what survives the worst case of each type draw (`1/120`,
`prob_genGenerableTy_bool`) and of each sub-draw's mass (`7/24`, `mass_bool_ge`).

So the application form is the one that needs the most size: `app` needs a function-typed subterm,
and at size 0 in the closed setting there is none (`closed_zero_arrow_empty`). For the root form
alone, **size 2 is the threshold**: below it some form has probability `0`, from it every form has a
positive, size-independent lower bound.

## Coverage of the whole fragment

`Covers e` says every one of the seven forms `const, bvar, abs, quant, app, ite, eq` occurs
*somewhere* in `e`. Then:

* `prob_covers_eq_zero`: at size `≤ 2` the probability is **exactly `0`**, at every type and in
  every context whose factory has no operator of positive arity. The proof is a counting argument:
  without the `Indir` rules the size bounds the height (`height_le`), and a term of height `≤ 2` has
  at most four compound nodes (`card_compoundOf_le_four`), one short of the five compound forms.
* `prob_covers_ge`: at every size `≥ 3` the probability is **at least `coverBound > 0`**, in every
  context, witnessed by the shape `ite (eq _ _) (app (λ:bool. #0) c) (∀:bool. _)`.

So **size 3 is the sharp coverage threshold**: it is the least size at which the generator can
exhibit the whole fragment in one draw, and from there on it does so with a probability bounded away
from `0` uniformly in the size. The bound itself, `coverBound ≈ 5.6e-19`, is a single-witness
product and is very far from tight; the zero side of the threshold is exact.

## `genLExpr` and `genClosedLExpr`

`genLExpr` keeps `genLExprBase` as a branch of weight at least `1/10` (`prob_genLExpr_ge`), and
without a factory of positive arity its support is inside `genLExprBase`'s
(`genLExpr_support_sub`). So every result above transfers: the lower bounds at a factor of `1/10`
in every context, the zero sides under the same factory hypothesis.
`genClosedLExpr_coverage_threshold` is the closed top-level generator's coverage threshold with
**no hypotheses**: probability `0` below size `3`, at least `coverBound / 120` from size `3` on.

Commands, statements, procedures and whole programs are in
`StrataGenerators.SizeDistributionStmt` and `StrataGenerators.SizeDistributionProgram`.

## Why only lower bounds

As in `StrataGenerators/Expectations.lean` on the `prob-props` branch: the leaf generators can fail,
so sub-draws have mass `< 1` that nothing here computes exactly. Every bound is a product of a
branch weight and lower bounds on the masses of the sub-draws it needs.
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

theorem prob_bind_ge {α β} {x : SPMF α} {f : α → SPMF β} {E : Set β} (F : Set α) {d : ℝ≥0∞}
    (hd : ∀ a ∈ F, d ≤ prob (f a) E) : prob x F * d ≤ prob (x >>= f) E := by
  rw [prob_bind, mul_comm, prob, ← expect_mul_left]
  refine expect_mono fun a => ?_
  by_cases ha : a ∈ F
  · simpa [Set.indicator, ha] using hd a ha
  · simp [Set.indicator, ha]

theorem prob_pure_of_mem {α} {a : α} {E : Set α} (h : a ∈ E) :
    prob (Pure.pure a : SPMF α) E = 1 := by
  classical
  rw [prob_pure]; simp [h]

theorem prob_univ {α} (p : SPMF α) : prob p Set.univ = p.mass := by
  rw [← expect_one]; unfold prob; congr 1; funext a; simp


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


inductive Form | const | op | bvar | fvar | abs | quant | app | ite | eq
  deriving DecidableEq, Repr

def rootForm : LExpr' → Form
  | .const .. => .const
  | .op .. => .op
  | .bvar .. => .bvar
  | .fvar .. => .fvar
  | .abs .. => .abs
  | .quant .. => .quant
  | .app .. => .app
  | .ite .. => .ite
  | .eq .. => .eq

def IsForm (F : Form) : Set LExpr' := {e | rootForm e = F}

theorem prob_pickBVar (bctx : BVarCtx) (τ : LMonoTy) (hv) :
    prob (pickBVar (G := SPMF) bctx τ hv) (IsForm .bvar) = 1 := by
  unfold pickBVar
  refine prob_elements_of_forall _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl

theorem prob_pickBVar_univ (bctx : BVarCtx) (τ : LMonoTy) (hv) :
    prob (pickBVar (G := SPMF) bctx τ hv) Set.univ = 1 := by
  unfold pickBVar; exact prob_elements_of_forall _ fun _ _ => trivial

theorem prob_pickFVar_univ (fctx : FVarCtx) (τ : LMonoTy) (hv) :
    prob (pickFVar (G := SPMF) fctx τ hv) Set.univ = 1 := by
  unfold pickFVar; exact prob_elements_of_forall _ fun _ _ => trivial

theorem prob_pickOp_univ (octx : OpCtx) (τ : LMonoTy) (hv) :
    prob (pickOp (G := SPMF) octx τ hv) Set.univ = 1 := by
  unfold pickOp; exact prob_elements_of_forall _ fun _ _ => trivial

theorem prob_genBoolConst : prob (genBoolConst (G := SPMF)) (IsForm .const) = 1 := by
  simp only [genBoolConst, prob_oneOf, List.map_cons, List.map_nil,
    prob_pure_of_mem (show LExpr.boolConst () true ∈ IsForm .const from rfl),
    prob_pure_of_mem (show LExpr.boolConst () false ∈ IsForm .const from rfl)]
  norm_num; exact ENNReal.div_self (by norm_num) (by norm_num)

theorem prob_genBoolConst_univ : prob (genBoolConst (G := SPMF)) Set.univ = 1 :=
  le_antisymm (by rw [prob_univ]; exact mass_le_one _)
    (prob_genBoolConst ▸ prob_mono (Set.subset_univ _))


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

/-- The context-reading type draw of `genEq` and `genQuant` picks `bool` with probability at least
`1/120`, whatever the contexts hold: the `genLMonoTy` fallback keeps weight `1` of `10`. -/
theorem prob_genGenerableTy_bool (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat) :
    1 / 120 ≤ prob (genGenerableTy (G := SPMF) fctx octx tvars bctx n) {LMonoTy.bool} := by
  have hb := prob_genLMonoTy_bool tvars n
  unfold genGenerableTy; dsimp only; split
  · refine le_trans ?_ (prob_frequency_ge_of_forall₂ _ _ _ [0, 1/12] ?_)
    · simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
        List.map_cons, List.map_nil, mul_zero, zero_add, add_zero, Nat.cast_ofNat]
      ennr
    · simpa using hb
  · exact le_trans (by ennr) hb

/-- The argument-type draw of `genApp` picks `bool` with probability at least `1/120`. -/
theorem prob_genAppArgTy_bool (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) :
    1 / 120 ≤ prob (genAppArgTy (G := SPMF) fctx octx tvars bctx n τ) {LMonoTy.bool} := by
  have hb := prob_genLMonoTy_bool tvars n
  unfold genAppArgTy; dsimp only; split
  · refine le_trans ?_ (prob_frequency_ge_of_forall₂ _ _ _ [0, 1/12] ?_)
    · simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
        List.map_cons, List.map_nil, mul_zero, zero_add, add_zero, Nat.cast_ofNat]
      ennr
    · simpa using hb
  · exact prob_genGenerableTy_bool fctx octx tvars bctx n

-- ── Events ──────────────────────────────────────────────────────────

def IteOf (Ec Et Ee : Set LExpr') : Set LExpr' :=
  {x | ∃ c t e, x = .ite () c t e ∧ c ∈ Ec ∧ t ∈ Et ∧ e ∈ Ee}
def EqOf (E₁ E₂ : Set LExpr') : Set LExpr' :=
  {x | ∃ a b, x = .eq () a b ∧ a ∈ E₁ ∧ b ∈ E₂}
def QuantOf (k : QuantifierKind) (τ : LMonoTy) (Eb : Set LExpr') : Set LExpr' :=
  {x | ∃ tr b, x = .quant () k "" (some τ) tr b ∧ b ∈ Eb}
def AppOf (Ef Ea : Set LExpr') : Set LExpr' :=
  {x | ∃ f a, x = .app () f a ∧ f ∈ Ef ∧ a ∈ Ea}
def AbsOf (τ : LMonoTy) (Eb : Set LExpr') : Set LExpr' :=
  {x | ∃ b, x = .abs () "" (some τ) b ∧ b ∈ Eb}

-- ── The combinators ─────────────────────────────────────────────────

theorem prob_genIte (A B C : SPMF LExpr') (Ec Et Ee : Set LExpr') :
    prob A Ec * (prob B Et * prob C Ee) ≤ prob (genIte A B C) (IteOf Ec Et Ee) := by
  unfold genIte
  refine prob_bind_ge Ec fun c hc => ?_
  refine prob_bind_ge Et fun t ht => ?_
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_ge Ee fun e he => ?_)
  refine (prob_pure_of_mem ?_).ge; exact ⟨c, t, e, rfl, hc, ht, he⟩

theorem prob_genEq (T : SPMF LMonoTy) (G : LMonoTy → SPMF LExpr') (τ : LMonoTy)
    (E₁ E₂ : Set LExpr') :
    prob T {τ} * (prob (G τ) E₁ * prob (G τ) E₂) ≤ prob (genEq T G) (EqOf E₁ E₂) := by
  unfold genEq
  refine prob_bind_ge {τ} fun σ hσ => ?_
  rw [Set.mem_singleton_iff.mp hσ]
  refine prob_bind_ge E₁ fun a ha => ?_
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_ge E₂ fun b hb => ?_)
  refine (prob_pure_of_mem ?_).ge; exact ⟨a, b, rfl, ha, hb⟩

theorem prob_genQuant (k : QuantifierKind) (T : SPMF LMonoTy)
    (Gtr : LMonoTy → LMonoTy → SPMF LExpr') (Gb : LMonoTy → SPMF LExpr') (τ τtr : LMonoTy)
    (Eb : Set LExpr') :
    prob T {τ} * (prob T {τtr} * (prob (Gtr τ τtr) Set.univ * prob (Gb τ) Eb))
      ≤ prob (genQuant k T Gtr Gb) (QuantOf k τ Eb) := by
  unfold genQuant
  refine prob_bind_ge {τ} fun σ hσ => ?_
  rw [Set.mem_singleton_iff.mp hσ]
  refine prob_bind_ge {τtr} fun σ' hσ' => ?_
  rw [Set.mem_singleton_iff.mp hσ']
  refine prob_bind_ge Set.univ fun tr _ => ?_
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_ge Eb fun b hb => ?_)
  refine (prob_pure_of_mem ?_).ge; exact ⟨tr, b, rfl, hb⟩

theorem prob_genApp (T : SPMF LMonoTy) (G : LMonoTy → SPMF LExpr') (τ τ' : LMonoTy)
    (Ef Ea : Set LExpr') :
    prob T {τ'} * (prob (G τ') Ea * prob (G (.arrow τ' τ)) Ef)
      ≤ prob (genApp T G τ) (AppOf Ef Ea) := by
  unfold genApp
  refine prob_bind_ge {τ'} fun σ hσ => ?_
  rw [Set.mem_singleton_iff.mp hσ]
  refine prob_bind_ge Ea fun a ha => ?_
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_ge Ef fun f hf => ?_)
  refine (prob_pure_of_mem ?_).ge; exact ⟨f, a, rfl, hf, ha⟩

theorem prob_genAbs (B : SPMF LExpr') (τ : LMonoTy) (Eb : Set LExpr') :
    prob B Eb ≤ prob (genAbs B τ) (AbsOf τ Eb) := by
  unfold genAbs
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_ge Eb fun b hb => ?_)
  refine (prob_pure_of_mem ?_).ge; exact ⟨b, rfl, hb⟩

variable (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)

theorem bool_leaf_univ (bctx : BVarCtx) :
    (1 ≤ prob (if hv : (bvarsOfType bctx LMonoTy.bool).length > 0 then pickBVar (G := SPMF) bctx LMonoTy.bool hv
      else genBoolConst) Set.univ) ∧
    (1 ≤ prob (if hf : (fvarsOfType fctx LMonoTy.bool).length > 0 then pickFVar (G := SPMF) fctx LMonoTy.bool hf
      else genBoolConst) Set.univ) ∧
    (1 ≤ prob (if ho : (opsOfType octx LMonoTy.bool).length > 0 then pickOp (G := SPMF) octx LMonoTy.bool ho
      else genBoolConst) Set.univ) := by
  refine ⟨?_, ?_, ?_⟩ <;> split
  · exact (prob_pickBVar_univ _ _ _).ge
  · exact prob_genBoolConst_univ.ge
  · exact (prob_pickFVar_univ _ _ _).ge
  · exact prob_genBoolConst_univ.ge
  · exact (prob_pickOp_univ _ _ _).ge
  · exact prob_genBoolConst_univ.ge

/-- The mass of the `bool` arm is at least `7/24` at every depth and in every context. -/
theorem mass_bool_ge (n : Nat) (bctx : BVarCtx) :
    7 / 24 ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n (.tcons "bool" [])) Set.univ := by
  obtain ⟨h1, h2, h3⟩ := bool_leaf_univ fctx octx bctx
  cases n with
  | zero =>
    rw [genLExprBase]
    refine le_trans ?_ (prob_oneOf_ge_of_forall₂ _ _ _ [1, 1, 1, 1] ?_)
    · ennr
    · simp only [List.forall₂_cons, List.Forall₂.nil, and_true]
      exact ⟨prob_genBoolConst_univ.ge, h1, h2, h3⟩
  | succ n =>
    rw [genLExprBase]
    refine le_trans ?_ (prob_frequency_ge_of_forall₂ _ _ _ [1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0] ?_)
    · ennr
    · simp only [List.forall₂_cons, List.Forall₂.nil, and_true, zero_le, true_and]
      exact ⟨prob_genBoolConst_univ.ge, h1, h2, h3⟩

/-- Peel branch `i` of the `frequency` at the head of an unfolded arm and close with `t`. -/
macro "arm " i:num ", " t:term : tactic => `(tactic| (
  rw [genLExprBase]
  refine le_trans ?_ (prob_frequency_ge _ _ $i (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  exact mul_le_mul' (le_of_eq (by norm_num)) $t))

local notation "Gb" bctx:max n:max τ:max => genLExprBase (G := SPMF) fctx octx pctx tvars bctx n τ

theorem bool_ite_ge (n : Nat) (bctx : BVarCtx) (Ec Et Ee : Set LExpr') :
    2 / 24 * (prob (Gb bctx n LMonoTy.bool) Ec * (prob (Gb bctx n LMonoTy.bool) Et *
      prob (Gb bctx n LMonoTy.bool) Ee))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (IteOf Ec Et Ee) := by
  show _ ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) (.tcons "bool" [])) _
  rw [genLExprBase]
  refine le_trans ?_ (prob_frequency_ge _ _ 2 (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  exact mul_le_mul' (le_of_eq (by norm_num)) (prob_genIte _ _ _ _ _ _)

theorem bool_eq_ge (n : Nat) (bctx : BVarCtx) (E₁ E₂ : Set LExpr') :
    2 / 24 * (1 / 120 * (prob (Gb bctx n LMonoTy.bool) E₁ * prob (Gb bctx n LMonoTy.bool) E₂))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (EqOf E₁ E₂) := by
  show _ ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) (.tcons "bool" [])) _
  arm 3, le_trans (mul_le_mul' (prob_genGenerableTy_bool fctx octx tvars bctx n) le_rfl)
    (prob_genEq _ _ LMonoTy.bool _ _)

theorem bool_forall_ge (n : Nat) (bctx : BVarCtx) (Eb : Set LExpr') :
    2 / 24 * (1 / 120 * (1 / 120 * (7 / 24 * prob (Gb (LMonoTy.bool :: bctx) n LMonoTy.bool) Eb)))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (QuantOf .all LMonoTy.bool Eb) := by
  have hT := prob_genGenerableTy_bool fctx octx tvars bctx n
  have hq := prob_genQuant .all (genGenerableTy (G := SPMF) fctx octx tvars bctx n)
    (fun τ' => genLExprBase (G := SPMF) fctx octx pctx tvars (τ' :: bctx) n)
    (fun τ' => genLExprBase (G := SPMF) fctx octx pctx tvars (τ' :: bctx) n LMonoTy.bool)
    LMonoTy.bool LMonoTy.bool Eb
  have hm : 7 / 24 ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars (LMonoTy.bool :: bctx) n
      LMonoTy.bool) Set.univ := mass_bool_ge fctx octx pctx tvars n _
  show _ ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) (.tcons "bool" [])) _
  arm 4, le_trans (mul_le_mul' hT (mul_le_mul' hT (mul_le_mul' hm le_rfl))) hq

theorem bool_exists_ge (n : Nat) (bctx : BVarCtx) (Eb : Set LExpr') :
    2 / 24 * (1 / 120 * (1 / 120 * (7 / 24 * prob (Gb (LMonoTy.bool :: bctx) n LMonoTy.bool) Eb)))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (QuantOf .exist LMonoTy.bool Eb) := by
  have hT := prob_genGenerableTy_bool fctx octx tvars bctx n
  have hq := prob_genQuant .exist (genGenerableTy (G := SPMF) fctx octx tvars bctx n)
    (fun τ' => genLExprBase (G := SPMF) fctx octx pctx tvars (τ' :: bctx) n)
    (fun τ' => genLExprBase (G := SPMF) fctx octx pctx tvars (τ' :: bctx) n LMonoTy.bool)
    LMonoTy.bool LMonoTy.bool Eb
  have hm : 7 / 24 ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars (LMonoTy.bool :: bctx) n
      LMonoTy.bool) Set.univ := mass_bool_ge fctx octx pctx tvars n _
  show _ ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) (.tcons "bool" [])) _
  arm 5, le_trans (mul_le_mul' hT (mul_le_mul' hT (mul_le_mul' hm le_rfl))) hq

theorem bool_app_ge (n : Nat) (bctx : BVarCtx) (Ef Ea : Set LExpr') :
    1 / 24 * (1 / 120 * (prob (Gb bctx n LMonoTy.bool) Ea *
      prob (Gb bctx n (LMonoTy.arrow LMonoTy.bool LMonoTy.bool)) Ef))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (AppOf Ef Ea) := by
  show _ ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) (.tcons "bool" [])) _
  arm 1, le_trans (mul_le_mul' (prob_genAppArgTy_bool fctx octx tvars bctx n _) le_rfl)
    (prob_genApp _ _ _ LMonoTy.bool _ _)

theorem arrow_abs_ge (n : Nat) (bctx : BVarCtx) (τ₁ τ₂ : LMonoTy) (Eb : Set LExpr') :
    4 / 21 * prob (Gb (τ₁ :: bctx) n τ₂) Eb
      ≤ prob (Gb bctx (n + 1) (LMonoTy.arrow τ₁ τ₂)) (AbsOf τ₁ Eb) := by
  show _ ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) (.tcons "arrow" [τ₁, τ₂])) _
  arm 0, prob_genAbs _ _ _

theorem bool_const_ge (n : Nat) (bctx : BVarCtx) :
    1 / 24 ≤ prob (Gb bctx n LMonoTy.bool) (IsForm .const) := by
  show _ ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n (.tcons "bool" [])) _
  cases n with
  | zero =>
    rw [genLExprBase]
    refine le_trans ?_ (prob_oneOf_ge _ _ 0 (by simp) _)
    simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, prob_genBoolConst]
    ennr
  | succ n =>
    rw [genLExprBase]
    refine le_trans ?_ (prob_frequency_ge _ _ 0 (by simp) _)
    simp only [List.getElem_cons_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      prob_genBoolConst]
    ennr

theorem bool_bvar_ge (n : Nat) (bctx : BVarCtx) (hb : (bvarsOfType bctx LMonoTy.bool).length > 0) :
    1 / 12 ≤ prob (Gb bctx n LMonoTy.bool) (IsForm .bvar) := by
  show _ ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n (.tcons "bool" [])) _
  cases n with
  | zero =>
    rw [genLExprBase]
    refine le_trans ?_ (prob_oneOf_ge _ _ 1 (by simp) _)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.length_cons, List.length_nil]
    rw [dif_pos hb, prob_pickBVar]
    ennr
  | succ n =>
    rw [genLExprBase]
    refine le_trans ?_ (prob_frequency_ge _ _ 6 (by simp) _)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    rw [dif_pos hb, prob_pickBVar]
    ennr

-- ── Size 0: leaves only ─────────────────────────────────────────────

def IsLeaf (e : LExpr') : Prop :=
  rootForm e = .const ∨ rootForm e = .bvar ∨ rootForm e = .fvar ∨ rootForm e = .op

theorem natArbitrary_true : IsSoundFor (ArbNat.Nat.arbitrary (G := SPMF)) (fun _ => True) :=
  fun _ _ => trivial
theorem genInterestingChar_true :
    IsSoundFor (StrataGenerators.PrimitiveGens.genInterestingChar (G := SPMF)) (fun _ => True) :=
  fun _ _ => trivial
theorem natArbGeom_true :
    IsSoundFor (StrataGenerators.PrimitiveGens.natArbGeom (G := SPMF)) (fun _ => True) :=
  fun _ _ => trivial

theorem pickBVar_leaf (bc : BVarCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickBVar (G := SPMF) bc σ h) IsLeaf := by
  intro e he
  unfold pickBVar at he
  rw [mem_support_elements_iff] at he
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
  exact Or.inr (Or.inl rfl)
theorem pickFVar_leaf (fc : FVarCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickFVar (G := SPMF) fc σ h) IsLeaf := by
  intro e he
  unfold pickFVar at he
  rw [mem_support_elements_iff] at he
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
  exact Or.inr (Or.inr (Or.inl rfl))
theorem pickOp_leaf (oc : OpCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickOp (G := SPMF) oc σ h) IsLeaf := by
  intro e he
  unfold pickOp at he
  rw [mem_support_elements_iff] at he
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
  exact Or.inr (Or.inr (Or.inr rfl))

theorem gen_true (bc : BVarCtx) (m : Nat) (σ : LMonoTy) :
    IsSoundFor (Gb bc m σ) (fun _ => True) := fun _ _ => trivial

theorem genAppArgTy_true (bc : BVarCtx) (m : Nat) (σ : LMonoTy) :
    IsSoundFor (genAppArgTy (G := SPMF) fctx octx tvars bc m σ) (fun _ => True) := fun _ _ => trivial
theorem genGenerableTy_true (bc : BVarCtx) (m : Nat) :
    IsSoundFor (genGenerableTy (G := SPMF) fctx octx tvars bc m) (fun _ => True) := fun _ _ => trivial
theorem genLMonoTy_true (m : Nat) :
    IsSoundFor (genLMonoTy (G := SPMF) tvars m) (fun _ => True) := fun _ _ => trivial
theorem genIndir_true (σ : LMonoTy) (g : LMonoTy → SPMF LExpr') (h) :
    IsSoundFor (genIndir (G := SPMF) octx σ g h) (fun _ => True) := fun _ _ => trivial
theorem genIndirPolyCore_true (bc : BVarCtx) (σ : LMonoTy) (g : LMonoTy → SPMF LExpr') (fb k) :
    IsSoundFor (genIndirPolyCore (G := SPMF) fctx octx pctx bc σ g fb k) (fun _ => True) :=
  fun _ _ => trivial

theorem zero_leaf (bctx : BVarCtx) (τ : LMonoTy) :
    IsSoundFor (Gb bctx 0 τ) IsLeaf := by
  rw [IsSoundFor.iff_obs, genLExprBase.eq_def]
  walk [(gen_true fctx octx pctx tvars _ _ _).obs, (genAppArgTy_true fctx octx tvars _ _ _).obs,
    (genGenerableTy_true fctx octx tvars _ _).obs, (genLMonoTy_true tvars _).obs,
    (genIndir_true octx _ _ _).obs, (genIndirPolyCore_true fctx octx pctx _ _ _ _ _).obs,
    natArbitrary_true.obs, genInterestingChar_true.obs, natArbGeom_true.obs,
    (pickBVar_leaf _ _ _).obs, (pickFVar_leaf _ _ _).obs, (pickOp_leaf _ _ _).obs]
  all_goals first | assumption | exact Or.inl rfl

-- ── Height ──────────────────────────────────────────────────────────

/-- The syntactic height of an expression: a leaf is `0`, each compound node adds `1`. Unlike the
package's `termDepth`, it charges nothing for type annotations, and an application spine costs one
level per `app` node. -/
def height : LExpr' → Nat
  | .abs _ _ _ b => height b + 1
  | .quant _ _ _ _ tr b => max (height tr) (height b) + 1
  | .app _ f a => max (height f) (height a) + 1
  | .ite _ c t e => max (height c) (max (height t) (height e)) + 1
  | .eq _ a b => max (height a) (height b) + 1
  | _ => 0

theorem height_of_isLeaf {e : LExpr'} (h : IsLeaf e) : height e = 0 := by
  cases e <;> simp_all [IsLeaf, rootForm, height]

theorem pickBVar_height (bc : BVarCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickBVar (G := SPMF) bc σ h) (fun e => height e = 0) :=
  fun e he => height_of_isLeaf (pickBVar_leaf bc σ h e he)
theorem pickFVar_height (fc : FVarCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickFVar (G := SPMF) fc σ h) (fun e => height e = 0) :=
  fun e he => height_of_isLeaf (pickFVar_leaf fc σ h e he)
theorem pickOp_height (oc : OpCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickOp (G := SPMF) oc σ h) (fun e => height e = 0) :=
  fun e he => height_of_isLeaf (pickOp_leaf oc σ h e he)

set_option linter.unusedSimpArgs false in
/-- **Without a factory of positive arity, the size bounds the height.** When no operator of
`octx` takes an argument and `pctx` is empty, the two `Indir` rules never fire (the monomorphic one
is guarded off, the polymorphic one falls back to the same type one level down), so every compound
node spends one unit of the size. -/
theorem height_le (hops : ∀ σ, findOpsInCtx octx σ = []) :
    ∀ n bctx τ, IsSoundFor (genLExprBase (G := SPMF) fctx octx [] tvars bctx n τ)
      (fun e => height e ≤ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ N ih =>
  cases N with
  | zero =>
    intro bctx τ e he
    exact (height_of_isLeaf (zero_leaf fctx octx [] tvars bctx τ e he)).le
  | succ n =>
    intro bctx τ
    have ihW : ∀ m bc σ, IsSoundFor (genLExprBase (G := SPMF) fctx octx [] tvars bc m σ)
        (fun e => m < n + 1 → height e ≤ m) := fun m bc σ e he hm => ih m hm bc σ e he
    have hIndir : ∀ σ (g : LMonoTy → SPMF LExpr') h,
        IsSoundFor (genIndir (G := SPMF) octx σ g h) (fun _ => False) := by
      intro σ g h; rw [hops σ] at h; simp at h
    have hPoly : ∀ m bc σ, IsSoundFor (genIndirPolyCore (G := SPMF) fctx octx [] bc σ
        (genLExprBase (G := SPMF) fctx octx [] tvars bc m)
        (genLExprBase (G := SPMF) fctx octx [] tvars bc m σ) 3)
        (fun e => m < n + 1 → height e ≤ m) := by
      intro m bc σ e he
      rcases StrataGenerators.IndirSupport.genIndirPolyCore_shape _ _ _ _ _ _ _ _ e he with
        ⟨_, _, _, _, hmem, _⟩ | hfb
      · simp [findPolymorphicOps] at hmem
      · exact ihW m bc σ e hfb
    rw [IsSoundFor.iff_obs, genLExprBase.eq_def]
    walk [(ihW _ _ _).obs, (genAppArgTy_true fctx octx tvars _ _ _).obs,
      (genGenerableTy_true fctx octx tvars _ _).obs, (genLMonoTy_true tvars _).obs,
      (hIndir _ _ _).obs, (hPoly _ _ _).obs,
      natArbitrary_true.obs, genInterestingChar_true.obs, natArbGeom_true.obs,
      (pickBVar_height _ _ _).obs, (pickFVar_height _ _ _).obs, (pickOp_height _ _ _).obs]
    all_goals (first | omega | (simp only [height] at *; omega) | (simp_all only [height]; try omega))

-- ── Forms occurring anywhere in a term ──────────────────────────────

/-- Every form that occurs in an expression, at any node. -/
def formsOf : LExpr' → Finset Form
  | .abs _ _ _ b => insert .abs (formsOf b)
  | .quant _ _ _ _ tr b => insert .quant (formsOf tr ∪ formsOf b)
  | .app _ f a => insert .app (formsOf f ∪ formsOf a)
  | .ite _ c t e => insert .ite (formsOf c ∪ (formsOf t ∪ formsOf e))
  | .eq _ a b => insert .eq (formsOf a ∪ formsOf b)
  | e => {rootForm e}

theorem rootForm_mem_formsOf (e : LExpr') : rootForm e ∈ formsOf e := by
  cases e <;> simp [formsOf, rootForm]

/-- The five compound forms. -/
def compoundForms : Finset Form := {.abs, .quant, .app, .ite, .eq}

/-- The seven forms of the simply-typed fragment that a closed `bool` term can exhibit: constants,
bound variables, and the five compound forms. -/
def stlcForms : Finset Form := {.const, .bvar, .abs, .quant, .app, .ite, .eq}

/-- A term **covers** the simply-typed fragment when every one of `stlcForms` occurs in it. -/
def Covers (e : LExpr') : Prop := stlcForms ⊆ formsOf e

def compoundOf (e : LExpr') : Finset Form := (formsOf e).filter (· ∈ compoundForms)

theorem compoundOf_of_height_zero {e : LExpr'} (h : height e = 0) : compoundOf e = ∅ := by
  cases e <;> simp_all [height, compoundOf, formsOf, rootForm, compoundForms]

theorem card_compoundOf_le_one {e : LExpr'} (h : height e ≤ 1) : (compoundOf e).card ≤ 1 := by
  cases e with
  | abs _ _ _ b =>
    have hb : height b = 0 := by simp [height] at h; omega
    have := compoundOf_of_height_zero hb
    simp only [compoundOf, formsOf, Finset.filter_insert] at this ⊢
    rw [this]; simp [compoundForms]
  | quant _ _ _ _ tr b =>
    have h1 : height tr = 0 := by simp [height] at h; omega
    have h2 : height b = 0 := by simp [height] at h; omega
    have e1 := compoundOf_of_height_zero h1; have e2 := compoundOf_of_height_zero h2
    simp only [compoundOf, formsOf, Finset.filter_insert, Finset.filter_union] at e1 e2 ⊢
    rw [e1, e2]; simp [compoundForms]
  | app _ f a =>
    have h1 : height f = 0 := by simp [height] at h; omega
    have h2 : height a = 0 := by simp [height] at h; omega
    have e1 := compoundOf_of_height_zero h1; have e2 := compoundOf_of_height_zero h2
    simp only [compoundOf, formsOf, Finset.filter_insert, Finset.filter_union] at e1 e2 ⊢
    rw [e1, e2]; simp [compoundForms]
  | ite _ c t e =>
    have h1 : height c = 0 := by simp [height] at h; omega
    have h2 : height t = 0 := by simp [height] at h; omega
    have h3 : height e = 0 := by simp [height] at h; omega
    have e1 := compoundOf_of_height_zero h1; have e2 := compoundOf_of_height_zero h2
    have e3 := compoundOf_of_height_zero h3
    simp only [compoundOf, formsOf, Finset.filter_insert, Finset.filter_union] at e1 e2 e3 ⊢
    rw [e1, e2, e3]; simp [compoundForms]
  | eq _ a b =>
    have h1 : height a = 0 := by simp [height] at h; omega
    have h2 : height b = 0 := by simp [height] at h; omega
    have e1 := compoundOf_of_height_zero h1; have e2 := compoundOf_of_height_zero h2
    simp only [compoundOf, formsOf, Finset.filter_insert, Finset.filter_union] at e1 e2 ⊢
    rw [e1, e2]; simp [compoundForms]
  | _ => exact le_trans (Finset.card_filter_le _ _) (by simp [formsOf])

theorem card_insert_union_le (F : Form) (s t : Finset Form) :
    (insert F (s ∪ t)).card ≤ 1 + s.card + t.card := by
  have := Finset.card_insert_le F (s ∪ t)
  have := Finset.card_union_le s t
  omega

/-- A term of height at most `2` has at most four compound nodes, so it shows at most four of the
five compound forms. -/
theorem card_compoundOf_le_four {e : LExpr'} (h : height e ≤ 2) : (compoundOf e).card ≤ 4 := by
  cases e with
  | abs _ _ _ b =>
    have := card_compoundOf_le_one (e := b) (by simp [height] at h; omega)
    simp only [compoundOf, formsOf, Finset.filter_insert] at this ⊢
    split <;> (try have := Finset.card_insert_le Form.abs ((formsOf b).filter (· ∈ compoundForms))) <;> omega
  | quant _ _ _ _ tr b =>
    have h1 := card_compoundOf_le_one (e := tr) (by simp [height] at h; omega)
    have h2 := card_compoundOf_le_one (e := b) (by simp [height] at h; omega)
    simp only [compoundOf, formsOf, Finset.filter_insert, Finset.filter_union] at h1 h2 ⊢
    split
    · have := card_insert_union_le .quant ((formsOf tr).filter (· ∈ compoundForms))
        ((formsOf b).filter (· ∈ compoundForms)); omega
    · have := Finset.card_union_le ((formsOf tr).filter (· ∈ compoundForms))
        ((formsOf b).filter (· ∈ compoundForms)); omega
  | app _ f a =>
    have h1 := card_compoundOf_le_one (e := f) (by simp [height] at h; omega)
    have h2 := card_compoundOf_le_one (e := a) (by simp [height] at h; omega)
    simp only [compoundOf, formsOf, Finset.filter_insert, Finset.filter_union] at h1 h2 ⊢
    split
    · have := card_insert_union_le .app ((formsOf f).filter (· ∈ compoundForms))
        ((formsOf a).filter (· ∈ compoundForms)); omega
    · have := Finset.card_union_le ((formsOf f).filter (· ∈ compoundForms))
        ((formsOf a).filter (· ∈ compoundForms)); omega
  | ite _ c t e =>
    have h1 := card_compoundOf_le_one (e := c) (by simp [height] at h; omega)
    have h2 := card_compoundOf_le_one (e := t) (by simp [height] at h; omega)
    have h3 := card_compoundOf_le_one (e := e) (by simp [height] at h; omega)
    simp only [compoundOf, formsOf, Finset.filter_insert, Finset.filter_union] at h1 h2 h3 ⊢
    have h4 := Finset.card_union_le ((formsOf t).filter (· ∈ compoundForms))
        ((formsOf e).filter (· ∈ compoundForms))
    split
    · have := card_insert_union_le .ite ((formsOf c).filter (· ∈ compoundForms))
        ((formsOf t).filter (· ∈ compoundForms) ∪ (formsOf e).filter (· ∈ compoundForms)); omega
    · have := Finset.card_union_le ((formsOf c).filter (· ∈ compoundForms))
        ((formsOf t).filter (· ∈ compoundForms) ∪ (formsOf e).filter (· ∈ compoundForms)); omega
  | eq _ a b =>
    have h1 := card_compoundOf_le_one (e := a) (by simp [height] at h; omega)
    have h2 := card_compoundOf_le_one (e := b) (by simp [height] at h; omega)
    simp only [compoundOf, formsOf, Finset.filter_insert, Finset.filter_union] at h1 h2 ⊢
    split
    · have := card_insert_union_le .eq ((formsOf a).filter (· ∈ compoundForms))
        ((formsOf b).filter (· ∈ compoundForms)); omega
    · have := Finset.card_union_le ((formsOf a).filter (· ∈ compoundForms))
        ((formsOf b).filter (· ∈ compoundForms)); omega
  | _ => exact le_trans (Finset.card_filter_le _ _) (by simp [formsOf])

/-- **No term of height `≤ 2` covers the fragment.** It would need all five compound forms. -/
theorem not_covers_of_height_le_two {e : LExpr'} (h : height e ≤ 2) : ¬ Covers e := by
  intro hc
  have hsub : compoundForms ⊆ compoundOf e := by
    intro F hF
    refine Finset.mem_filter.mpr ⟨hc ?_, hF⟩
    simp only [compoundForms, Finset.mem_insert, Finset.mem_singleton] at hF
    simp only [stlcForms, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have := Finset.card_le_card hsub
  have h5 : compoundForms.card = 5 := by decide
  have := card_compoundOf_le_four h
  omega

-- ── The coverage threshold ──────────────────────────────────────────

/-- **Below size 3, no draw covers the fragment** — at any target type, in any binder context, for
any free-variable context, provided the factory contributes no operator of positive arity. -/
theorem prob_covers_eq_zero (hops : ∀ σ, findOpsInCtx octx σ = []) (n : Nat) (hn : n ≤ 2)
    (bctx : BVarCtx) (τ : LMonoTy) :
    prob (genLExprBase (G := SPMF) fctx octx [] tvars bctx n τ) {e | Covers e} = 0 :=
  (prob_eq_zero_iff _ _).mpr fun e he hc =>
    not_covers_of_height_le_two (le_trans (height_le fctx octx tvars hops n bctx τ e he) hn) hc

theorem bvarsOfType_cons_self (τ : LMonoTy) (bctx : BVarCtx) :
    (bvarsOfType (τ :: bctx) τ).length > 0 := by
  simp [bvarsOfType, bvarsOfType.go]

/-- The lower bound on the coverage probability at every size `≥ 3`. It is the probability of one
witness shape, `ite (eq _ _) (app (λ:bool. #0) c) (∀:bool. _)`, which shows all seven forms. -/
noncomputable def coverBound : ℝ≥0∞ :=
  2 / 24 * ((2 / 24 * (1 / 120 * (7 / 24 * (7 / 24)))) *
    ((1 / 24 * (1 / 120 * (1 / 24 * (4 / 21 * (1 / 12))))) *
     (2 / 24 * (1 / 120 * (1 / 120 * (7 / 24 * (7 / 24)))))))

theorem coverBound_pos : 0 < coverBound := by
  unfold coverBound
  simp only [ENNReal.mul_pos_iff, ENNReal.div_pos_iff]
  norm_num

/-- **From size 3 on, a draw covers the fragment with probability at least `coverBound`**, at the
`bool` type, in every context: free variables, factory and binders are all arbitrary. -/
theorem prob_covers_ge (n : Nat) (bctx : BVarCtx) :
    coverBound ≤ prob (Gb bctx (n + 3) LMonoTy.bool) {e | Covers e} := by
  have hsub : IteOf (EqOf Set.univ Set.univ)
      (AppOf (AbsOf LMonoTy.bool (IsForm .bvar)) (IsForm .const))
      (QuantOf .all LMonoTy.bool Set.univ) ⊆ {e | Covers e} := by
    rintro x ⟨c, t, e, rfl, ⟨a, b, rfl, -, -⟩, ⟨f, a', rfl, ⟨body, rfl, hbody⟩, ha'⟩,
      ⟨tr, b', rfl, -⟩⟩
    have h1 := rootForm_mem_formsOf body
    have h2 := rootForm_mem_formsOf a'
    simp only [IsForm, Set.mem_setOf_eq] at hbody ha'
    rw [hbody] at h1; rw [ha'] at h2
    intro F hF
    simp only [stlcForms, Finset.mem_insert, Finset.mem_singleton] at hF
    simp only [formsOf, Finset.mem_insert, Finset.mem_union]
    rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  refine le_trans ?_ (prob_mono hsub)
  refine le_trans ?_ (bool_ite_ge fctx octx pctx tvars (n + 2) bctx _ _ _)
  have hc := bool_eq_ge fctx octx pctx tvars (n + 1) bctx Set.univ Set.univ
  have hm := mass_bool_ge fctx octx pctx tvars (n + 1) bctx
  have ht := bool_app_ge fctx octx pctx tvars (n + 1) bctx
    (AbsOf LMonoTy.bool (IsForm .bvar)) (IsForm .const)
  have hk := bool_const_ge fctx octx pctx tvars (n + 1) bctx
  have hf := arrow_abs_ge fctx octx pctx tvars n bctx LMonoTy.bool LMonoTy.bool (IsForm .bvar)
  have hv := bool_bvar_ge fctx octx pctx tvars n (LMonoTy.bool :: bctx)
    (bvarsOfType_cons_self _ _)
  have he := bool_forall_ge fctx octx pctx tvars (n + 1) bctx Set.univ
  have hm' := mass_bool_ge fctx octx pctx tvars (n + 1) (LMonoTy.bool :: bctx)
  unfold coverBound
  refine mul_le_mul' le_rfl (mul_le_mul' ?_ (mul_le_mul' ?_ ?_))
  · refine le_trans ?_ hc
    gcongr <;> exact hm
  · refine le_trans ?_ ht
    gcongr
    refine le_trans ?_ hf
    gcongr
  · refine le_trans ?_ he
    gcongr
    exact hm'

-- ── The application threshold ───────────────────────────────────────

theorem findOpsInCtx_empty (σ : LMonoTy) : findOpsInCtx ∅ σ = [] := by
  simp [findOpsInCtx]

/-- In the closed setting, a size-0 draw at an arrow type in the empty binder context is
impossible: there is no variable or operator to pick, and no constant of a function type. -/
theorem closed_zero_arrow_empty (tvars : List TyIdentifier) (a b : LMonoTy) (e : LExpr') :
    e ∉ SPMF.support (genLExprBase (G := SPMF) [] ∅ [] tvars [] 0 (.arrow a b)) := by
  intro he
  change e ∈ SPMF.support (genLExprBase (G := SPMF) [] ∅ [] tvars [] 0 (.tcons "arrow" [a, b])) at he
  rw [genLExprBase] at he
  simp [bvarsOfType, bvarsOfType.go, fvarsOfType, opsOfType_empty] at he

theorem leaf_ne_app {e : LExpr'} (h : IsLeaf e) : rootForm e ≠ .app := by
  rcases h with h | h | h | h <;> simp [h]

/-- **At size 1, a closed `bool` draw is never an application.** The function position would need a
size-0 term of an arrow type, and the closed setting has none. -/
theorem closed_one_not_app (tvars : List TyIdentifier) :
    IsSoundFor (genLExprBase (G := SPMF) [] ∅ [] tvars [] 1 LMonoTy.bool)
      (fun e => rootForm e ≠ .app) := by
  have hz : ∀ bc σ, IsSoundFor (genLExprBase (G := SPMF) [] ∅ [] tvars bc 0 σ)
      (fun e => IsLeaf e ∧ (bc = [] → ∀ a b, σ = .arrow a b → False)) := by
    intro bc σ e he
    refine ⟨zero_leaf [] ∅ [] tvars bc σ e he, ?_⟩
    rintro rfl a b rfl
    exact closed_zero_arrow_empty tvars a b e he
  have hIndir : ∀ σ (g : LMonoTy → SPMF LExpr') h,
      IsSoundFor (genIndir (G := SPMF) ∅ σ g h) (fun _ => False) := by
    intro σ g h; rw [findOpsInCtx_empty] at h; simp at h
  have hPoly : ∀ bc σ, IsSoundFor (genIndirPolyCore (G := SPMF) [] ∅ [] bc σ
      (genLExprBase (G := SPMF) [] ∅ [] tvars bc 0)
      (genLExprBase (G := SPMF) [] ∅ [] tvars bc 0 σ) 3) IsLeaf := by
    intro bc σ e he
    rcases StrataGenerators.IndirSupport.genIndirPolyCore_shape _ _ _ _ _ _ _ _ e he with
      ⟨_, _, _, _, hmem, _⟩ | hfb
    · simp [findPolymorphicOps] at hmem
    · exact (hz bc σ e hfb).1
  show IsSoundFor (genLExprBase (G := SPMF) [] ∅ [] tvars [] (0 + 1) (.tcons "bool" [])) _
  rw [IsSoundFor.iff_obs, genLExprBase]
  walk [(hz _ _).obs, (genAppArgTy_true [] ∅ tvars _ _ _).obs,
    (genGenerableTy_true [] ∅ tvars _ _).obs, (genLMonoTy_true tvars _).obs,
    (hIndir _ _ _).obs, (hPoly _ _).obs,
    (pickBVar_leaf _ _ _).obs, (pickFVar_leaf _ _ _).obs, (pickOp_leaf _ _ _).obs]
  all_goals first
    | (simp [rootForm]; done)
    | exact leaf_ne_app ‹_›
    | (rename_i hfn; exact (hfn.2 rfl _ _ rfl).elim)
    | (split
       all_goals first
        | (simp [rootForm]; done)
        | (intro _ h; exact leaf_ne_app h)
        | (intro _ h; exact leaf_ne_app h.1))

-- ── Headline results ────────────────────────────────────────────────

/-- **Size 0 gives leaves only**, at every type and in every context. -/
theorem prob_compound_size_zero (bctx : BVarCtx) (τ : LMonoTy) :
    prob (Gb bctx 0 τ) {e | ¬ IsLeaf e} = 0 :=
  (prob_eq_zero_iff _ _).mpr fun e he hn => hn (zero_leaf fctx octx pctx tvars bctx τ e he)

/-- **Size 1 gives no closed application.** -/
theorem prob_closed_app_size_one (tvars : List TyIdentifier) :
    prob (genLExprBase (G := SPMF) [] ∅ [] tvars [] 1 LMonoTy.bool) (IsForm .app) = 0 :=
  (prob_eq_zero_iff _ _).mpr fun e he hn => closed_one_not_app tvars e he hn

noncomputable def constBound : ℝ≥0∞ := 1 / 24
noncomputable def iteBound : ℝ≥0∞ := 2 / 24 * (7 / 24 * (7 / 24 * (7 / 24)))
noncomputable def eqBound : ℝ≥0∞ := 2 / 24 * (1 / 120 * (7 / 24 * (7 / 24)))
noncomputable def quantBound : ℝ≥0∞ := 2 / 24 * (1 / 120 * (1 / 120 * (7 / 24 * (7 / 24))))
noncomputable def appBound : ℝ≥0∞ := 1 / 24 * (1 / 120 * (7 / 24 * (4 / 21 * (7 / 24))))

theorem prob_const_ge (n : Nat) (bctx : BVarCtx) :
    constBound ≤ prob (Gb bctx n LMonoTy.bool) (IsForm .const) :=
  bool_const_ge fctx octx pctx tvars n bctx

theorem prob_ite_ge (n : Nat) (bctx : BVarCtx) :
    iteBound ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (IsForm .ite) := by
  have hm := mass_bool_ge fctx octx pctx tvars n bctx
  refine le_trans ?_ (le_trans (bool_ite_ge fctx octx pctx tvars n bctx Set.univ Set.univ Set.univ)
    (prob_mono ?_))
  · unfold iteBound; gcongr <;> exact hm
  · rintro _ ⟨_, _, _, rfl, -⟩; rfl

theorem prob_eq_ge (n : Nat) (bctx : BVarCtx) :
    eqBound ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (IsForm .eq) := by
  have hm := mass_bool_ge fctx octx pctx tvars n bctx
  refine le_trans ?_ (le_trans (bool_eq_ge fctx octx pctx tvars n bctx Set.univ Set.univ)
    (prob_mono ?_))
  · unfold eqBound; gcongr <;> exact hm
  · rintro _ ⟨_, _, rfl, -⟩; rfl

theorem prob_forall_ge (n : Nat) (bctx : BVarCtx) :
    quantBound ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (IsForm .quant) := by
  have hm := mass_bool_ge fctx octx pctx tvars n (LMonoTy.bool :: bctx)
  refine le_trans ?_ (le_trans (bool_forall_ge fctx octx pctx tvars n bctx Set.univ)
    (prob_mono ?_))
  · unfold quantBound; gcongr; exact hm
  · rintro _ ⟨_, _, rfl, -⟩; rfl

theorem prob_app_ge (n : Nat) (bctx : BVarCtx) :
    appBound ≤ prob (Gb bctx (n + 2) LMonoTy.bool) (IsForm .app) := by
  have hm := mass_bool_ge fctx octx pctx tvars (n + 1) bctx
  have hm' := mass_bool_ge fctx octx pctx tvars n (LMonoTy.bool :: bctx)
  have hf := arrow_abs_ge fctx octx pctx tvars n bctx LMonoTy.bool LMonoTy.bool Set.univ
  refine le_trans ?_ (le_trans (bool_app_ge fctx octx pctx tvars (n + 1) bctx
    (AbsOf LMonoTy.bool Set.univ) Set.univ) (prob_mono ?_))
  · unfold appBound
    gcongr
    · exact hm
    · refine le_trans ?_ hf; gcongr; exact hm'
  · rintro _ ⟨_, _, rfl, -⟩; rfl

theorem bounds_pos : 0 < constBound ∧ 0 < iteBound ∧ 0 < eqBound ∧ 0 < quantBound ∧ 0 < appBound := by
  unfold constBound iteBound eqBound quantBound appBound
  simp only [ENNReal.mul_pos_iff, ENNReal.div_pos_iff]
  norm_num

/-- **The root-form threshold, closed setting.** With no free variables, no factory and no
binders, size `0` gives only leaves, size `1` never an application, and every size `≥ 2` an
application with probability at least `appBound > 0` (and so every `bool` root form with a positive,
size-independent lower bound). -/
theorem closed_root_threshold (tvars : List TyIdentifier) :
    prob (genLExprBase (G := SPMF) [] ∅ [] tvars [] 0 LMonoTy.bool) {e | ¬ IsLeaf e} = 0 ∧
    prob (genLExprBase (G := SPMF) [] ∅ [] tvars [] 1 LMonoTy.bool) (IsForm .app) = 0 ∧
    (∀ n, appBound ≤ prob (genLExprBase (G := SPMF) [] ∅ [] tvars [] (n + 2) LMonoTy.bool)
      (IsForm .app)) ∧
    0 < appBound :=
  ⟨prob_compound_size_zero [] ∅ [] tvars [] _, prob_closed_app_size_one tvars,
   fun n => prob_app_ge [] ∅ [] tvars n [], bounds_pos.2.2.2.2⟩

/-- **The coverage threshold.** For a factory with no operator of positive arity and no
polymorphic operators, a draw at `bool` covers all seven forms with probability `0` below size `3`,
and with probability at least `coverBound > 0` at every size from `3` on. -/
theorem coverage_threshold (hops : ∀ σ, findOpsInCtx octx σ = []) (bctx : BVarCtx) :
    (∀ n ≤ 2, prob (genLExprBase (G := SPMF) fctx octx [] tvars bctx n LMonoTy.bool)
      {e | Covers e} = 0) ∧
    (∀ n ≥ 3, coverBound ≤ prob (genLExprBase (G := SPMF) fctx octx [] tvars bctx n LMonoTy.bool)
      {e | Covers e}) ∧
    0 < coverBound := by
  refine ⟨fun n hn => prob_covers_eq_zero fctx octx tvars hops n hn bctx _, fun n hn => ?_,
    coverBound_pos⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact prob_covers_ge fctx octx [] tvars m bctx

/-- The closed instance of `coverage_threshold`. -/
theorem closed_coverage_threshold (tvars : List TyIdentifier) :
    (∀ n ≤ 2, prob (genLExprBase (G := SPMF) [] ∅ [] tvars [] n LMonoTy.bool) {e | Covers e} = 0) ∧
    (∀ n ≥ 3, coverBound ≤ prob (genLExprBase (G := SPMF) [] ∅ [] tvars [] n LMonoTy.bool)
      {e | Covers e}) :=
  let h := coverage_threshold [] ∅ tvars findOpsInCtx_empty []
  ⟨h.1, h.2.1⟩

-- ── `genLExpr`: the root-weighted wrapper ───────────────────────────

/-- `genLExpr` keeps `genLExprBase` as a branch of weight at least `1/10` (the `1`-of-`10` base
branch when a monomorphic candidate exists, the `1`-of-`2` `pick` otherwise), so every lower bound on
`genLExprBase` transfers at a factor of `1/10`, in every context and for every `retryCont`. -/
theorem prob_genLExpr_ge (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) (k : Nat)
    (rc : (LMonoTy → SPMF LExpr') → (LMonoTy → SPMF LExpr')) (E : Set LExpr') :
    1 / 10 * prob (Gb bctx n τ) E ≤
      prob (genLExpr (G := SPMF) fctx octx pctx tvars bctx n τ k rc) E := by
  unfold genLExpr; dsimp only; split
  · refine le_trans ?_ (prob_frequency_ge _ _ 0 (by simp) _)
    simp only [List.getElem_cons_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    exact mul_le_mul' (le_of_eq (by norm_num)) le_rfl
  · refine le_trans ?_ (prob_oneOf_ge _ _ 0 (by simp) _)
    simp only [List.getElem_cons_zero, List.length_cons, List.length_nil]
    exact mul_le_mul' (by ennr) le_rfl

/-- Without a factory of positive arity and without polymorphic operators, `genLExpr`'s support is
inside `genLExprBase`'s: the `Indir` branch is guarded off and `IndirPoly` falls back to the base
generator at the same size and type. -/
theorem genLExpr_support_sub (hops : ∀ σ, findOpsInCtx octx σ = []) (bctx : BVarCtx) (n : Nat)
    (τ : LMonoTy) (k : Nat) (rc : (LMonoTy → SPMF LExpr') → (LMonoTy → SPMF LExpr'))
    (e : LExpr') (he : e ∈ SPMF.support (genLExpr (G := SPMF) fctx octx [] tvars bctx n τ k rc)) :
    e ∈ SPMF.support (genLExprBase (G := SPMF) fctx octx [] tvars bctx n τ) := by
  unfold genLExpr at he; dsimp only at he
  rw [dif_neg (by rw [hops τ]; simp)] at he
  simp only [mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
    or_false] at he
  obtain ⟨g, hg, he⟩ := he
  rcases hg with rfl | rfl
  · exact he
  · rcases StrataGenerators.IndirSupport.genIndirPolyCore_shape _ _ _ _ _ _ _ _ e he with
      ⟨_, _, _, _, hmem, _⟩ | hfb
    · simp [findPolymorphicOps] at hmem
    · exact hfb

theorem prob_genLExpr_covers_eq_zero (hops : ∀ σ, findOpsInCtx octx σ = []) (n : Nat) (hn : n ≤ 2)
    (bctx : BVarCtx) (τ : LMonoTy) (k : Nat)
    (rc : (LMonoTy → SPMF LExpr') → (LMonoTy → SPMF LExpr')) :
    prob (genLExpr (G := SPMF) fctx octx [] tvars bctx n τ k rc) {e | Covers e} = 0 :=
  (prob_eq_zero_iff _ _).mpr fun e he hc =>
    not_covers_of_height_le_two
      (le_trans (height_le fctx octx tvars hops n bctx τ e
        (genLExpr_support_sub fctx octx tvars hops bctx n τ k rc e he)) hn) hc

theorem prob_genLExpr_covers_ge (n : Nat) (bctx : BVarCtx) (k : Nat)
    (rc : (LMonoTy → SPMF LExpr') → (LMonoTy → SPMF LExpr')) :
    1 / 10 * coverBound ≤
      prob (genLExpr (G := SPMF) fctx octx pctx tvars bctx (n + 3) LMonoTy.bool k rc)
        {e | Covers e} :=
  le_trans (mul_le_mul' le_rfl (prob_covers_ge fctx octx pctx tvars n bctx))
    (prob_genLExpr_ge fctx octx pctx tvars bctx _ _ k rc _)

/-- **The coverage threshold for `genClosedLExpr`, with no hypotheses.** The closed top-level
generator draws its target type, then a closed term of it. Below size `3` no draw covers the seven
forms; from size `3` on, a draw covers them with probability at least `coverBound / 120`: the type
draw lands on `bool` with probability at least `1/12`, and `genLExpr` keeps the base generator at
weight at least `1/10`. -/
theorem genClosedLExpr_coverage_threshold (tvars : List TyIdentifier) (k : Nat) :
    (∀ n ≤ 2, prob (genClosedLExpr (G := SPMF) tvars n k) {e | Covers e} = 0) ∧
    (∀ n ≥ 3, 1 / 12 * (1 / 10 * coverBound) ≤
      prob (genClosedLExpr (G := SPMF) tvars n k) {e | Covers e}) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · unfold genClosedLExpr
    rw [prob_bind]
    refine le_antisymm (le_trans (expect_mono fun τ => le_of_eq
      (prob_genLExpr_covers_eq_zero [] ∅ tvars findOpsInCtx_empty n hn [] τ k id)) ?_) (zero_le _)
    simp [expect]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    unfold genClosedLExpr
    refine le_trans ?_ (prob_bind_ge {LMonoTy.bool} (d := 1 / 10 * coverBound) fun τ hτ => ?_)
    · gcongr; exact prob_genLMonoTy_bool tvars _
    · rw [Set.mem_singleton_iff.mp hτ]
      exact prob_genLExpr_covers_ge [] ∅ [] tvars m [] k id

end StrataGenerators.SizeDistribution
