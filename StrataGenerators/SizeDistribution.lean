import StrataGenerators.HasTypeAGen
import Basalt.Walk.Entry
import Basalt.Walk.Sound

/-!
# How the size parameter shapes the distribution of `genLExprBase`

The support proofs in this package say which expressions `genLExprBase … size τ` *can* produce. This
module reads the same generator as a measure (`SPMF.prob`) and answers: **for a given size, what
does the distribution look like?** Which root forms (constant, variable, `ite`, `eq`, quantifier,
application, …) have probability zero, and which have a guaranteed positive share? And how tall
are the terms?

## Results, for the `bool` target

| size | root form      | bound                                   | where |
|------|----------------|-----------------------------------------|-------|
| 0    | any compound   | probability `0` (any type, any context) | `prob_compound_size_zero` |
| 1    | application    | probability `0` (closed setting)        | `prob_closed_app_size_one` |
| `n + rootFormSize F` | `F` | `≥ rootFormBound F > 0`            | `prob_rootForm_ge` |

`rootForms` is the five forms covered: a constant (`rootFormSize = 0`), `ite`, `eq` and a
quantifier (`1`), and an application (`2`). `rootFormBound` ranges from `1/24` for a constant down
to `≈ 4.9e-7` for a quantifier. The bound does not depend on the size, so these say "from this size
on, at a rate that never decays"; below the offset some of the same probabilities are exactly `0`.

Every lower bound holds in **every** context — any free variables, any factory, any binders — which
is why the constants are small: they are what survives the worst case of each type draw
(`prob_genGenerableTy_bool`) and of each sub-draw's mass (`mass_bool_ge`).

So the application form is the one that needs the most size: `app` needs a function-typed subterm,
and at size 0 in the closed setting there is none (`closed_zero_arrow_empty`). For the root form
alone, **size 2 is the threshold**: below it some form has probability `0`, from it every form has a
positive, size-independent lower bound.

## Height as a function of `n`

`prob_height_ge`: at every size `n`, in every context, a `bool` draw has height at least `n` with
probability at least `(7/24) · (49/6912)ⁿ`. `prob_height_eq`: without a factory of positive arity,
where `height_le` makes `n` the largest possible height, a draw has height exactly `n` with at
least this probability, so maximal-depth terms are rare but always possible.

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

/-! ### The recurring structural shares

Four quantities appear in bound after bound. Naming them keeps the headline statements readable and
records what each factor pays for. -/


/-- A lower bound on the mass of one identifier draw (`genIdentName`, `genFreshName`,
`genFreshLabel`): its terminating branch. The generators are `partial_fixpoint`, so this is all the
mass that is proved. -/
noncomputable def nameMass : ℝ≥0∞ := 1 / 2

/-- One declaration kind's weight share in `genDeclStep`: weight `1` of the total `15`. -/
noncomputable def stepShare : ℝ≥0∞ := 1 / 15

/-- A lower bound on the mass of one declaration step, through the abstract-type kind. -/
noncomputable def stepMass : ℝ≥0∞ := 1 / 30

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

-- ── The arm bounds, in terms of the weights ─────────────────────────

/-! ### Bounds stated with the tuning weights

`genLExprBase` is `@[tunable (depth := n)]`, so `genLExprBase.tuned θ` reads each branch weight from
a `Tuning` value `θ` instead of a literal. The weight of branch `i` at a site whose schedules start
at flat index `off` is `θ.weight (off + i) d` at remaining depth `d`. Every lower bound below is a
statement about `genLExprBase.tuned θ` for an arbitrary `θ`, with the branch shares in place of the
literal fractions. The literal versions further down are corollaries at `θ = genLExprBase.defaults`,
through `genLExprBase.tuned_defaults`, which holds by `rfl`.

No hypothesis on `θ` is needed. `Tuning.weight` is `max a 1 + d · b`, so every weight is at least
`1` (`Tuning.weight_pos`), every site's total is positive, and every share is positive.

Two sites matter here: the `bool` arm at depth `n + 1` (flat offset `8`, `11` branches) and the
arrow arm at depth `n + 1` (offset `0`, `8` branches). The depth-`0` arms are uniform `oneOf`s with
no weights. -/

/-- The share of branch `i` at a `frequency` site with `k` branches whose schedules start at flat
index `off` of `θ`, at depth `d`: `w_{off+i}(d) / Σ_{j<k} w_{off+j}(d)`. -/
noncomputable def share (θ : Tuning) (off k i d : Nat) : ℝ≥0∞ :=
  (θ.weight (off + i) d : ℝ≥0∞) / (((List.range k).map (fun j => θ.weight (off + j) d)).sum : ℕ)

/-- The share of branch `i` of the `bool` arm at depth `d + 1`. Branches: `0` constant, `1`
application, `2` `ite`, `3` `eq`, `4` `∀`, `5` `∃`, `6` bound variable, `7` free variable, `8`
operator, `9` `Indir`, `10` `IndirPoly`. -/
noncomputable abbrev boolShare (θ : Tuning) (i d : Nat) : ℝ≥0∞ := share θ 8 11 i d

/-- The share of branch `i` of the arrow arm at depth `d + 1`. Branch `0` is the lambda. -/
noncomputable abbrev arrowShare (θ : Tuning) (i d : Nat) : ℝ≥0∞ := share θ 0 8 i d

/-- A lower bound on the mass of a `bool` draw at depth `n`: `1` at depth `0`, where every branch
is a leaf, and the four leaf shares (constant, bound variable, free variable, operator) above. -/
noncomputable def massT (θ : Tuning) : Nat → ℝ≥0∞
  | 0 => 1
  | n + 1 => boolShare θ 0 n + boolShare θ 6 n + boolShare θ 7 n + boolShare θ 8 n

/-- A lower bound on a root constant at depth `n`: one branch of four at depth `0`, the constant
share above. -/
noncomputable def constT (θ : Tuning) : Nat → ℝ≥0∞
  | 0 => 1 / 4
  | n + 1 => boolShare θ 0 n


theorem massT_bool_ge (θ : Tuning) (n : Nat) (bctx : BVarCtx) :
    massT θ n ≤ prob (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx n (.tcons "bool" []))
      Set.univ := by
  obtain ⟨h1, h2, h3⟩ := bool_leaf_univ fctx octx bctx
  cases n with
  | zero =>
    refine le_trans ?_ (prob_oneOf_ge_of_forall₂ _ (by simp) _ [1, 1, 1, 1] ?_)
    · simp only [massT, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]; ennr
    · simp only [List.forall₂_cons, List.Forall₂.nil, and_true]
      exact ⟨prob_genBoolConst_univ.ge, h1, h2, h3⟩
  | succ n =>
    refine le_trans (le_of_eq ?_) (prob_frequency_ge_of_forall₂ _ (Tuning.sum_map_fst_pos _ _ _ _ _)
      _ [1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0] ?_)
    · simp only [massT, boolShare, share, ← ENNReal.add_div, List.zipWith_cons_cons,
        List.zipWith_nil_right, List.sum_cons, List.sum_nil, List.map_cons, List.map_nil, mul_one,
        mul_zero, add_zero, zero_add]
      simp [List.range_succ, add_assoc]
    · simp only [List.forall₂_cons, List.Forall₂.nil, and_true, zero_le, true_and]
      exact ⟨prob_genBoolConst_univ.ge, h1, h2, h3⟩

/-- Peel branch `i` of a tuned `frequency` site and close with `t`, reading the branch's share. -/
macro "armT " i:num ", " t:term : tactic => `(tactic| (
  refine le_trans ?_ (prob_frequency_ge _ (Tuning.sum_map_fst_pos _ _ _ _ _) $i (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  refine mul_le_mul' (le_of_eq ?_) $t
  simp [share, List.range_succ]))

local notation "Gt" θ:max bctx:max n:max τ:max =>
  genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx n τ

theorem boolT_ite_ge (θ : Tuning) (n : Nat) (bctx : BVarCtx) (Ec Et Ee : Set LExpr') :
    boolShare θ 2 n * (prob (Gt θ bctx n LMonoTy.bool) Ec * (prob (Gt θ bctx n LMonoTy.bool) Et *
      prob (Gt θ bctx n LMonoTy.bool) Ee))
      ≤ prob (Gt θ bctx (n + 1) LMonoTy.bool) (IteOf Ec Et Ee) := by
  armT 2, prob_genIte _ _ _ _ _ _

theorem boolT_eq_ge (θ : Tuning) (n : Nat) (bctx : BVarCtx) (E₁ E₂ : Set LExpr') :
    boolShare θ 3 n * (1 / 120 * (prob (Gt θ bctx n LMonoTy.bool) E₁ *
      prob (Gt θ bctx n LMonoTy.bool) E₂))
      ≤ prob (Gt θ bctx (n + 1) LMonoTy.bool) (EqOf E₁ E₂) := by
  armT 3, le_trans (mul_le_mul' (prob_genGenerableTy_bool fctx octx tvars bctx n) le_rfl)
    (prob_genEq _ _ LMonoTy.bool _ _)

theorem boolT_forall_ge (θ : Tuning) (n : Nat) (bctx : BVarCtx) (Eb : Set LExpr') :
    boolShare θ 4 n * (1 / 120 * (1 / 120 * (massT θ n *
      prob (Gt θ (LMonoTy.bool :: bctx) n LMonoTy.bool) Eb)))
      ≤ prob (Gt θ bctx (n + 1) LMonoTy.bool) (QuantOf .all LMonoTy.bool Eb) := by
  have hT := prob_genGenerableTy_bool fctx octx tvars bctx n
  have hq := prob_genQuant .all (genGenerableTy (G := SPMF) fctx octx tvars bctx n)
    (fun τ' => genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars (τ' :: bctx) n)
    (fun τ' => genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars (τ' :: bctx) n LMonoTy.bool)
    LMonoTy.bool LMonoTy.bool Eb
  have hm : massT θ n ≤ prob (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars
      (LMonoTy.bool :: bctx) n LMonoTy.bool) Set.univ := massT_bool_ge fctx octx pctx tvars θ n _
  armT 4, le_trans (mul_le_mul' hT (mul_le_mul' hT (mul_le_mul' hm le_rfl))) hq

theorem boolT_app_ge (θ : Tuning) (n : Nat) (bctx : BVarCtx) (Ef Ea : Set LExpr') :
    boolShare θ 1 n * (1 / 120 * (prob (Gt θ bctx n LMonoTy.bool) Ea *
      prob (Gt θ bctx n (LMonoTy.arrow LMonoTy.bool LMonoTy.bool)) Ef))
      ≤ prob (Gt θ bctx (n + 1) LMonoTy.bool) (AppOf Ef Ea) := by
  armT 1, le_trans (mul_le_mul' (prob_genAppArgTy_bool fctx octx tvars bctx n _) le_rfl)
    (prob_genApp _ _ _ LMonoTy.bool _ _)

theorem arrowT_abs_ge (θ : Tuning) (n : Nat) (bctx : BVarCtx) (τ₁ τ₂ : LMonoTy) (Eb : Set LExpr') :
    arrowShare θ 0 n * prob (Gt θ (τ₁ :: bctx) n τ₂) Eb
      ≤ prob (Gt θ bctx (n + 1) (LMonoTy.arrow τ₁ τ₂)) (AbsOf τ₁ Eb) := by
  armT 0, prob_genAbs _ _ _

theorem boolT_const_ge (θ : Tuning) (n : Nat) (bctx : BVarCtx) :
    constT θ n ≤ prob (Gt θ bctx n LMonoTy.bool) (IsForm .const) := by
  cases n with
  | zero =>
    refine le_trans ?_ (prob_oneOf_ge _ (by simp) 0 (by simp) _)
    simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, prob_genBoolConst, constT]
    ennr
  | succ n =>
    refine le_trans ?_ (prob_frequency_ge _ (Tuning.sum_map_fst_pos _ _ _ _ _) 0 (by simp) _)
    simp only [List.getElem_cons_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      prob_genBoolConst, mul_one, constT]
    apply le_of_eq
    simp [share, List.range_succ]


-- ── The literal bounds, as corollaries at the default weights ───────

/-- Evaluate a share at the default weights of `genLExprBase`. -/
macro "share_defaults" : tactic => `(tactic|
  simp [share, List.range_succ, Tuning.weight, genLExprBase.defaults])

/-- The mass of the `bool` arm is at least `7/24` at every depth and in every context. -/
theorem mass_bool_ge (n : Nat) (bctx : BVarCtx) :
    7 / 24 ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n (.tcons "bool" [])) Set.univ := by
  rw [← genLExprBase.tuned_defaults]
  refine le_trans ?_ (massT_bool_ge fctx octx pctx tvars genLExprBase.defaults n bctx)
  cases n with
  | zero => simp only [massT]; ennr
  | succ n =>
    have : massT genLExprBase.defaults (n + 1) = 7 / 24 := by
      simp only [massT, boolShare]; share_defaults
      rw [inv_eq_one_div, ← ENNReal.add_div, ← ENNReal.add_div, ← ENNReal.add_div]; norm_num
    rw [this]

local notation "Gb" bctx:max n:max τ:max => genLExprBase (G := SPMF) fctx octx pctx tvars bctx n τ

theorem bool_ite_ge (n : Nat) (bctx : BVarCtx) (Ec Et Ee : Set LExpr') :
    2 / 24 * (prob (Gb bctx n LMonoTy.bool) Ec * (prob (Gb bctx n LMonoTy.bool) Et *
      prob (Gb bctx n LMonoTy.bool) Ee))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (IteOf Ec Et Ee) := by
  have h := boolT_ite_ge fctx octx pctx tvars genLExprBase.defaults n bctx Ec Et Ee
  rw [show boolShare genLExprBase.defaults 2 n = 2 / 24 by share_defaults] at h
  simpa only [genLExprBase.tuned_defaults] using h

theorem bool_eq_ge (n : Nat) (bctx : BVarCtx) (E₁ E₂ : Set LExpr') :
    2 / 24 * (1 / 120 * (prob (Gb bctx n LMonoTy.bool) E₁ * prob (Gb bctx n LMonoTy.bool) E₂))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (EqOf E₁ E₂) := by
  have h := boolT_eq_ge fctx octx pctx tvars genLExprBase.defaults n bctx E₁ E₂
  rw [show boolShare genLExprBase.defaults 3 n = 2 / 24 by share_defaults] at h
  simpa only [genLExprBase.tuned_defaults] using h

theorem bool_forall_ge (n : Nat) (bctx : BVarCtx) (Eb : Set LExpr') :
    2 / 24 * (1 / 120 * (1 / 120 * (7 / 24 * prob (Gb (LMonoTy.bool :: bctx) n LMonoTy.bool) Eb)))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (QuantOf .all LMonoTy.bool Eb) := by
  have h := boolT_forall_ge fctx octx pctx tvars genLExprBase.defaults n bctx Eb
  rw [show boolShare genLExprBase.defaults 4 n = 2 / 24 by share_defaults] at h
  simp only [genLExprBase.tuned_defaults] at h
  refine le_trans ?_ h
  gcongr
  cases n with
  | zero => simp only [massT]; ennr
  | succ n =>
    apply le_of_eq
    simp only [massT, boolShare]; share_defaults
    rw [inv_eq_one_div, ← ENNReal.add_div, ← ENNReal.add_div, ← ENNReal.add_div]; norm_num

theorem bool_app_ge (n : Nat) (bctx : BVarCtx) (Ef Ea : Set LExpr') :
    1 / 24 * (1 / 120 * (prob (Gb bctx n LMonoTy.bool) Ea *
      prob (Gb bctx n (LMonoTy.arrow LMonoTy.bool LMonoTy.bool)) Ef))
      ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (AppOf Ef Ea) := by
  have h := boolT_app_ge fctx octx pctx tvars genLExprBase.defaults n bctx Ef Ea
  rw [show boolShare genLExprBase.defaults 1 n = 1 / 24 by share_defaults] at h
  simpa only [genLExprBase.tuned_defaults] using h

theorem arrow_abs_ge (n : Nat) (bctx : BVarCtx) (τ₁ τ₂ : LMonoTy) (Eb : Set LExpr') :
    4 / 21 * prob (Gb (τ₁ :: bctx) n τ₂) Eb
      ≤ prob (Gb bctx (n + 1) (LMonoTy.arrow τ₁ τ₂)) (AbsOf τ₁ Eb) := by
  have h := arrowT_abs_ge fctx octx pctx tvars genLExprBase.defaults n bctx τ₁ τ₂ Eb
  rw [show arrowShare genLExprBase.defaults 0 n = 4 / 21 by share_defaults] at h
  simpa only [genLExprBase.tuned_defaults] using h

theorem bool_const_ge (n : Nat) (bctx : BVarCtx) :
    1 / 24 ≤ prob (Gb bctx n LMonoTy.bool) (IsForm .const) := by
  have h := boolT_const_ge fctx octx pctx tvars genLExprBase.defaults n bctx
  simp only [genLExprBase.tuned_defaults] at h
  refine le_trans ?_ h
  cases n with
  | zero => simp only [constT]; ennr
  | succ n => apply le_of_eq; simp only [constT, boolShare]; share_defaults


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

/-- The five root forms a `bool` draw is proved to reach, with, for each, the least size at which
it is reachable (`rootFormSize`) and a size-independent lower bound on its probability from that
size on (`rootFormBound`). A constant needs no size; `ite`, `eq` and a quantifier need one level;
an application needs two, because its function position needs a lambda, which needs a level of its
own. -/
def rootForms : Finset Form := {.const, .ite, .eq, .quant, .app}

def rootFormSize : Form → Nat
  | .app => 2
  | .ite | .eq | .quant => 1
  | _ => 0

noncomputable def rootFormBound : Form → ℝ≥0∞
  | .const => 1 / 24
  | .ite => 2 / 24 * (7 / 24 * (7 / 24 * (7 / 24)))
  | .eq => 2 / 24 * (1 / 120 * (7 / 24 * (7 / 24)))
  | .quant => 2 / 24 * (1 / 120 * (1 / 120 * (7 / 24 * (7 / 24))))
  | .app => 1 / 24 * (1 / 120 * (7 / 24 * (4 / 21 * (7 / 24))))
  | _ => 0

theorem prob_const_ge (n : Nat) (bctx : BVarCtx) :
    rootFormBound .const ≤ prob (Gb bctx n LMonoTy.bool) (IsForm .const) :=
  bool_const_ge fctx octx pctx tvars n bctx

theorem prob_ite_ge (n : Nat) (bctx : BVarCtx) :
    rootFormBound .ite ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (IsForm .ite) := by
  have hm := mass_bool_ge fctx octx pctx tvars n bctx
  refine le_trans ?_ (le_trans (bool_ite_ge fctx octx pctx tvars n bctx Set.univ Set.univ Set.univ)
    (prob_mono ?_))
  · simp only [rootFormBound]; gcongr <;> exact hm
  · rintro _ ⟨_, _, _, rfl, -⟩; rfl

theorem prob_eq_ge (n : Nat) (bctx : BVarCtx) :
    rootFormBound .eq ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (IsForm .eq) := by
  have hm := mass_bool_ge fctx octx pctx tvars n bctx
  refine le_trans ?_ (le_trans (bool_eq_ge fctx octx pctx tvars n bctx Set.univ Set.univ)
    (prob_mono ?_))
  · simp only [rootFormBound]; gcongr <;> exact hm
  · rintro _ ⟨_, _, rfl, -⟩; rfl

theorem prob_forall_ge (n : Nat) (bctx : BVarCtx) :
    rootFormBound .quant ≤ prob (Gb bctx (n + 1) LMonoTy.bool) (IsForm .quant) := by
  have hm := mass_bool_ge fctx octx pctx tvars n (LMonoTy.bool :: bctx)
  refine le_trans ?_ (le_trans (bool_forall_ge fctx octx pctx tvars n bctx Set.univ)
    (prob_mono ?_))
  · simp only [rootFormBound]; gcongr; exact hm
  · rintro _ ⟨_, _, rfl, -⟩; rfl

theorem prob_app_ge (n : Nat) (bctx : BVarCtx) :
    rootFormBound .app ≤ prob (Gb bctx (n + 2) LMonoTy.bool) (IsForm .app) := by
  have hm := mass_bool_ge fctx octx pctx tvars (n + 1) bctx
  have hm' := mass_bool_ge fctx octx pctx tvars n (LMonoTy.bool :: bctx)
  have hf := arrow_abs_ge fctx octx pctx tvars n bctx LMonoTy.bool LMonoTy.bool Set.univ
  refine le_trans ?_ (le_trans (bool_app_ge fctx octx pctx tvars (n + 1) bctx
    (AbsOf LMonoTy.bool Set.univ) Set.univ) (prob_mono ?_))
  · simp only [rootFormBound]
    gcongr
    · exact hm
    · refine le_trans ?_ hf; gcongr; exact hm'
  · rintro _ ⟨_, _, rfl, -⟩; rfl

theorem rootFormBound_pos (F : Form) (hF : F ∈ rootForms) : 0 < rootFormBound F := by
  fin_cases hF <;>
    (simp only [rootFormBound, ENNReal.mul_pos_iff, ENNReal.div_pos_iff]; norm_num)

/-- **Every root form, as a function of the size.** For each of the five forms `F`, at every size
`n`, in every context, a `bool` draw at size `n + rootFormSize F` has `F` at its root with
probability at least `rootFormBound F > 0` — a bound that does not shrink as the size grows. The
offset `rootFormSize F` is the threshold: below it some of these probabilities are `0`
(`prob_compound_size_zero`, `prob_closed_app_size_one`). -/
theorem prob_rootForm_ge (F : Form) (hF : F ∈ rootForms) (n : Nat) (bctx : BVarCtx) :
    rootFormBound F ≤ prob (Gb bctx (n + rootFormSize F) LMonoTy.bool) (IsForm F) := by
  fin_cases hF
  · exact prob_const_ge fctx octx pctx tvars n bctx
  · exact prob_ite_ge fctx octx pctx tvars n bctx
  · exact prob_eq_ge fctx octx pctx tvars n bctx
  · exact prob_forall_ge fctx octx pctx tvars n bctx
  · exact prob_app_ge fctx octx pctx tvars n bctx

/-- **The root-form threshold, closed setting.** A user-facing bundle; nothing in this package
builds on it. With no free variables, no factory and no
binders, size `0` gives only leaves, size `1` never an application, and every size `≥ 2` an
application with probability at least `appBound > 0` (and so every `bool` root form with a positive,
size-independent lower bound). -/
theorem closed_root_threshold (tvars : List TyIdentifier) :
    prob (genLExprBase (G := SPMF) [] ∅ [] tvars [] 0 LMonoTy.bool) {e | ¬ IsLeaf e} = 0 ∧
    prob (genLExprBase (G := SPMF) [] ∅ [] tvars [] 1 LMonoTy.bool) (IsForm .app) = 0 ∧
    (∀ F ∈ rootForms, ∀ n,
      rootFormBound F ≤ prob (genLExprBase (G := SPMF) [] ∅ [] tvars []
        (n + rootFormSize F) LMonoTy.bool) (IsForm F) ∧ 0 < rootFormBound F) :=
  ⟨prob_compound_size_zero [] ∅ [] tvars [] _, prob_closed_app_size_one tvars,
   fun F hF n => ⟨prob_rootForm_ge [] ∅ [] tvars F hF n [], rootFormBound_pos F hF⟩⟩


-- ── `genLExpr`: the root-weighted wrapper ───────────────────────────


-- ── Closed forms in `n`: deep terms are rare but possible ───────────────

theorem prob_mono_support {α} {p : SPMF α} {E F : Set α} (h : ∀ a ∈ p.support, a ∈ E → a ∈ F) :
    prob p E ≤ prob p F := by
  unfold prob
  refine expect_mono_support fun a ha => ?_
  by_cases hE : a ∈ E
  · simp [Set.indicator, hE, h a ha hE]
  · simp [Set.indicator, hE]

/-- The lower bound on reaching height `n` at size `n`: `(7/24) · (49/6912)ⁿ`. `7/24` is the mass
of the innermost draw; each of the `n` levels costs the `ite` weight `2/24` and the masses `7/24`
of the two branches it does not descend into, and `2/24 · (7/24)² = 49/6912`. -/
noncomputable def heightAtSize (n : Nat) : ℝ≥0∞ := 7 / 24 * (49 / 6912) ^ n

theorem heightAtSize_eq (n : Nat) :
    heightAtSize n = 7 / 24 * (2 / 24 * (7 / 24 * (7 / 24))) ^ n := by
  have hbase : (49 / 6912 : ℝ≥0∞) = 2 / 24 * (7 / 24 * (7 / 24)) := by
    rw [div_mul_div 7 7 24 (b := 24) (by norm_num) (by norm_num),
      div_mul_div 2 (7 * 7) ((24 : ℝ≥0∞) * 24) (b := 24) (by norm_num) (by norm_num)]
    frac_eq
  rw [heightAtSize, hbase]

theorem heightAtSize_pos (n : Nat) : 0 < heightAtSize n := by
  rw [heightAtSize]
  refine ENNReal.mul_pos (by norm_num) (pow_ne_zero n ?_)
  rw [← pos_iff_ne_zero, ENNReal.div_pos_iff]
  exact ⟨by norm_num, by norm_num⟩

/-- **A term of height `n` at size `n`, with probability at least `heightAtSize n`.** At every
size `n`, in every context, a `bool` draw has height at least `n` with at least this probability.
The witness is a chain of `ite`s through the condition. -/
theorem prob_height_ge (n : Nat) (bctx : BVarCtx) :
    heightAtSize n ≤ prob (Gb bctx n LMonoTy.bool) {e | n ≤ height e} := by
  rw [heightAtSize_eq]
  induction n with
  | zero =>
    have h := mass_bool_ge fctx octx pctx tvars 0 bctx
    simpa [Set.ofPred_true, LMonoTy.bool] using h
  | succ n ih =>
    have hm := mass_bool_ge fctx octx pctx tvars n bctx
    refine le_trans ?_ (le_trans (bool_ite_ge fctx octx pctx tvars n bctx
      {x | n ≤ height x} Set.univ Set.univ) (prob_mono ?_))
    · generalize hq : (2 / 24 * (7 / 24 * (7 / 24)) : ℝ≥0∞) = q
      have hre : 7 / 24 * q ^ (n + 1) = 2 / 24 * ((7 / 24 * q ^ n) * (7 / 24 * (7 / 24))) := by
        rw [← hq]; ring
      rw [hre]
      rw [hq] at ih
      gcongr <;> exact hm
    · rintro _ ⟨c, t, f, rfl, hc, -, -⟩
      simp only [Set.mem_ofPred_eq, height] at hc ⊢
      omega

/-- **The height distribution's top atom, closed form.** Without a factory of positive arity,
the height of a size-`n` draw is at most `n`, and it is exactly `n` with probability at least
`heightAtSize n = (7/24) · (49/6912)ⁿ`: maximal-depth terms are exponentially rare in `n` under
this bound, and never impossible. -/
theorem prob_height_eq (hops : ∀ σ, findOpsInCtx octx σ = []) (n : Nat) (bctx : BVarCtx) :
    heightAtSize n
        ≤ prob (genLExprBase (G := SPMF) fctx octx [] tvars bctx n LMonoTy.bool)
          {e | height e = n}
      ∧ 0 < heightAtSize n :=
  ⟨le_trans (prob_height_ge fctx octx [] tvars n bctx) (prob_mono_support fun e he h => by
    have := height_le fctx octx tvars hops n bctx _ e he
    simp only [Set.mem_ofPred_eq] at h ⊢; omega), heightAtSize_pos n⟩

-- ── Headline bounds in terms of the weights ─────────────────────────

/-! ### The headline bounds, for every tuning

The bounds below hold for `genLExprBase.tuned θ` at every `θ`. Each is a product of branch shares
of `θ` and of `massT θ`. At `θ = genLExprBase.defaults` they give back the literal bounds above, so
those are the special case at the shipping weights. -/

theorem share_pos (θ : Tuning) (off k i d : Nat) (_hik : i < k) : 0 < share θ off k i d := by
  rw [share, ENNReal.div_pos_iff]
  refine ⟨by exact_mod_cast (Tuning.weight_pos θ _ d).ne', by finiteness⟩

theorem massT_pos (θ : Tuning) (n : Nat) : 0 < massT θ n := by
  cases n with
  | zero => simp [massT]
  | succ n =>
    simp only [massT]
    exact lt_of_lt_of_le (share_pos θ 8 11 0 n (by omega)) (by
      refine le_trans ?_ le_self_add; refine le_trans ?_ le_self_add; exact le_self_add)

/-- The lower bound on root form `F` at depth `n + rootFormSize F`, for the weights `θ`. -/
noncomputable def rootFormBoundT (θ : Tuning) : Form → Nat → ℝ≥0∞
  | .const, n => constT θ n
  | .ite, n => boolShare θ 2 n * (massT θ n * (massT θ n * massT θ n))
  | .eq, n => boolShare θ 3 n * (1 / 120 * (massT θ n * massT θ n))
  | .quant, n => boolShare θ 4 n * (1 / 120 * (1 / 120 * (massT θ n * massT θ n)))
  | .app, n => boolShare θ 1 (n + 1) * (1 / 120 * (massT θ (n + 1) * (arrowShare θ 0 n * massT θ n)))
  | _, _ => 0

/-- **Every root form, for every tuning.** For each of the five forms `F`, at every size `n`, in
every context, and for every weights `θ`, a `bool` draw of `genLExprBase.tuned θ` at size
`n + rootFormSize F` has `F` at its root with probability at least `rootFormBoundT θ F n`. -/
theorem prob_rootForm_ge_tuned (θ : Tuning) (F : Form) (hF : F ∈ rootForms) (n : Nat)
    (bctx : BVarCtx) :
    rootFormBoundT θ F n ≤ prob (Gt θ bctx (n + rootFormSize F) LMonoTy.bool) (IsForm F) := by
  have hm := massT_bool_ge fctx octx pctx tvars θ n bctx
  fin_cases hF
  · exact boolT_const_ge fctx octx pctx tvars θ n bctx
  · refine le_trans ?_ (le_trans (boolT_ite_ge fctx octx pctx tvars θ n bctx Set.univ Set.univ
      Set.univ) (prob_mono ?_))
    · simp only [rootFormBoundT]; gcongr <;> exact hm
    · rintro _ ⟨_, _, _, rfl, -⟩; rfl
  · refine le_trans ?_ (le_trans (boolT_eq_ge fctx octx pctx tvars θ n bctx Set.univ Set.univ)
      (prob_mono ?_))
    · simp only [rootFormBoundT]; gcongr <;> exact hm
    · rintro _ ⟨_, _, rfl, -⟩; rfl
  · have hm' := massT_bool_ge fctx octx pctx tvars θ n (LMonoTy.bool :: bctx)
    refine le_trans ?_ (le_trans (boolT_forall_ge fctx octx pctx tvars θ n bctx Set.univ)
      (prob_mono ?_))
    · simp only [rootFormBoundT]; gcongr; exact hm'
    · rintro _ ⟨_, _, rfl, -⟩; rfl
  · have hm1 := massT_bool_ge fctx octx pctx tvars θ (n + 1) bctx
    have hm' := massT_bool_ge fctx octx pctx tvars θ n (LMonoTy.bool :: bctx)
    have hf := arrowT_abs_ge fctx octx pctx tvars θ n bctx LMonoTy.bool LMonoTy.bool Set.univ
    refine le_trans ?_ (le_trans (boolT_app_ge fctx octx pctx tvars θ (n + 1) bctx
      (AbsOf LMonoTy.bool Set.univ) Set.univ) (prob_mono ?_))
    · simp only [rootFormBoundT]
      gcongr
      · exact hm1
      · refine le_trans ?_ hf; gcongr; exact hm'
    · rintro _ ⟨_, _, rfl, -⟩; rfl

theorem mul_pos' {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  ENNReal.mul_pos ha.ne' hb.ne'

theorem rootFormBoundT_pos (θ : Tuning) (F : Form) (hF : F ∈ rootForms) (n : Nat) :
    0 < rootFormBoundT θ F n := by
  have hm := massT_pos θ
  have hb := fun i d (h : i < 11) => share_pos θ 8 11 i d h
  have ha := share_pos θ 0 8 0 n (by omega)
  have hc : (0 : ℝ≥0∞) < 1 / 120 := by rw [ENNReal.div_pos_iff]; exact ⟨by norm_num, by norm_num⟩
  fin_cases hF <;> simp only [rootFormBoundT]
  · cases n with
    | zero => simp [constT]
    | succ n => exact hb 0 n (by omega)
  · exact mul_pos' (hb 2 n (by omega)) (mul_pos' (hm n) (mul_pos' (hm n) (hm n)))
  · exact mul_pos' (hb 3 n (by omega)) (mul_pos' hc (mul_pos' (hm n) (hm n)))
  · exact mul_pos' (hb 4 n (by omega)) (mul_pos' hc (mul_pos' hc (mul_pos' (hm n) (hm n))))
  · exact mul_pos' (hb 1 (n + 1) (by omega)) (mul_pos' hc (mul_pos' (hm (n + 1)) (mul_pos' ha (hm n))))

/-- The lower bound on reaching height `n` at size `n`, for the weights `θ`: each level costs the
`ite` share at that depth and the masses of the two branches it does not descend into. -/
noncomputable def heightT (θ : Tuning) : Nat → ℝ≥0∞
  | 0 => 1
  | n + 1 => boolShare θ 2 n * (heightT θ n * (massT θ n * massT θ n))

/-- **Height, for every tuning.** -/
theorem prob_height_ge_tuned (θ : Tuning) (n : Nat) (bctx : BVarCtx) :
    heightT θ n ≤ prob (Gt θ bctx n LMonoTy.bool) {e | n ≤ height e} := by
  induction n with
  | zero =>
    have h := massT_bool_ge fctx octx pctx tvars θ 0 bctx
    simpa [Set.ofPred_true, LMonoTy.bool, heightT, massT] using h
  | succ n ih =>
    have hm := massT_bool_ge fctx octx pctx tvars θ n bctx
    refine le_trans ?_ (le_trans (boolT_ite_ge fctx octx pctx tvars θ n bctx
      {x | n ≤ height x} Set.univ Set.univ) (prob_mono ?_))
    · simp only [heightT]; gcongr <;> exact hm
    · rintro _ ⟨c, t, f, rfl, hc, -, -⟩
      simp only [Set.mem_ofPred_eq, height] at hc ⊢
      omega

theorem heightT_pos (θ : Tuning) : ∀ n, 0 < heightT θ n
  | 0 => by simp [heightT]
  | n + 1 => mul_pos' (share_pos θ 8 11 2 n (by omega))
      (mul_pos' (heightT_pos θ n) (mul_pos' (massT_pos θ n) (massT_pos θ n)))


theorem share_le_of_sibling (θ : Tuning) (off k i j d : Nat) (hj : j < k) :
    share θ off k i d ≤ (θ.weight (off + i) d : ℝ≥0∞) / (θ.weight (off + j) d : ℝ≥0∞) := by
  rw [share]
  refine ENNReal.div_le_div_left ?_ _
  have hmem : θ.weight (off + j) d ∈ (List.range k).map (fun j => θ.weight (off + j) d) :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  exact_mod_cast List.le_sum_of_mem hmem

/-- **The `1/d` decay.** If branch `i` has a schedule `(a, 0)` and a sibling `j` has a slope `b`,
the share of `i` at depth `d` is at most `max a 1 / (d · b)`. -/
theorem share_le_inv_depth (θ : Tuning) (off k i j d : Nat) (hj : j < k)
    (hi : (θ.schedules.getD (off + i) (1, 0)).2 = 0) :
    share θ off k i d ≤ ((max (θ.schedules.getD (off + i) (1, 0)).1 1 : ℕ) : ℝ≥0∞)
      / ((d * (θ.schedules.getD (off + j) (1, 0)).2 : ℕ) : ℝ≥0∞) := by
  refine le_trans (share_le_of_sibling θ off k i j d hj) ?_
  have hwi : θ.weight (off + i) d = max (θ.schedules.getD (off + i) (1, 0)).1 1 := by
    simp only [Tuning.weight]; rw [hi, mul_zero, add_zero]
  have hwj : d * (θ.schedules.getD (off + j) (1, 0)).2 ≤ θ.weight (off + j) d := by
    simp only [Tuning.weight]; omega
  rw [hwi]
  exact ENNReal.div_le_div_left (by exact_mod_cast hwj) _

end StrataGenerators.SizeDistribution
