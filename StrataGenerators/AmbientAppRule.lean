import Basalt.Combinators
import Basalt.SPMF.Expect.Obs
import Basalt.SPMF.Support

/-!
# Ambient function applications: the default STLC rule vs. Pałka et al.'s rule

A small STLC with `Int`/`String`/`Bool` base types and *ambient* functions (constants of a fixed
signature, e.g. `String.take : String → Int → String`). Two fuel-indexed generators for terms
of a target type:

* `genExpr` uses only the generation rules read off the typing rules; its application rule
  draws the argument type from `genTy` (Pałka et al.'s "default" rule, Fig. `genApp` of the paper).
* `genExprP` adds Pałka et al.'s alternative rule: pick an ambient function whose *result* type
  is the target, then generate its arguments at the argument types read off its signature.

`genExpr_prob_takeCall_le`: under the default rule, a call `take a b` is produced with probability
at most `Pr(genTy = String) * Pr(genTy = Int)`, for every fuel, context, and type generator.
`genExprP_prob_takeCall_ge`: with Pałka et al.'s rule it is produced with probability at least
`1 / (64 * |sig|)`, a constant independent of the fuel, the context and `genTy`.
-/

namespace StrataGenerators.AmbientApp

open scoped ENNReal

/-! ## Syntax -/

inductive Ty where
  | int | str | bool
  | arrow (a b : Ty)
  deriving DecidableEq, Repr

/-- Argument types of a curried function type. -/
def Ty.args : Ty → List Ty
  | .arrow a b => a :: b.args
  | _ => []

/-- Result type of a curried function type, after all arguments are supplied. -/
def Ty.res : Ty → Ty
  | .arrow _ b => b.res
  | t => t

/-- An ambient function: a name with its (fixed) type. -/
structure Fn where
  name : String
  ty : Ty
  deriving DecidableEq, Repr

inductive Expr where
  | intLit | strLit | boolLit
  | var (i : Nat)
  | const (f : Fn)
  | app (f x : Expr)
  | lam (a : Ty) (body : Expr)
  deriving DecidableEq, Repr

/-- `String.take : String → Int → String`. -/
def takeTy : Ty := .arrow .str (.arrow .int .str)

/-- The event "the root of the term is a full call `f a b` of the ambient function `f`". -/
def CallOf (f : Fn) : Set Expr := {e | ∃ a b, e = .app (.app (.const f) a) b}

/-! ## Generators -/

def lits : Ty → List Expr
  | .int => [.intLit]
  | .str => [.strLit]
  | .bool => [.boolLit]
  | .arrow _ _ => []

def vars (Γ : List Ty) (τ : Ty) : List Expr :=
  Γ.zipIdx.filterMap fun (τ', i) => if τ' = τ then some (.var i) else none

/-- Leaves of type `τ`: literals, local variables, and ambient functions of exactly type `τ`. -/
def leafCands (sig : List Fn) (Γ : List Ty) (τ : Ty) : List Expr :=
  lits τ ++ vars Γ τ ++ (sig.filter (·.ty = τ)).map .const

def genLeaf [Gen G] (sig : List Fn) (Γ : List Ty) (τ : Ty) : G Expr :=
  if h : leafCands sig Γ τ ≠ [] then elements (leafCands sig Γ τ) h else default

/-- Terms of type `τ`, built only from the generation rules read off the STLC typing rules. -/
def genExpr [Gen G] (genTy : G Ty) (sig : List Fn) : Nat → List Ty → Ty → G Expr
  | 0, Γ, τ => genLeaf sig Γ τ
  | n + 1, Γ, τ => frequency [
      (1, fun _ => genLeaf sig Γ τ),
      (1, fun _ => match τ with
        | .arrow a b => Expr.lam a <$> genExpr genTy sig n (a :: Γ) b
        | _ => genLeaf sig Γ τ),
      (1, fun _ => do
        let τ' ← genTy
        let f ← genExpr genTy sig n Γ (.arrow τ' τ)
        let x ← genExpr genTy sig n Γ τ'
        return .app f x)]

/-- Ambient functions whose result type is `τ`. -/
def candidates (sig : List Fn) (τ : Ty) : List Fn := sig.filter (·.ty.res = τ)

/-- `genExpr` plus Pałka et al.'s rule for applying an ambient function. -/
def genExprP [Gen G] (genTy : G Ty) (sig : List Fn) : Nat → List Ty → Ty → G Expr
  | 0, Γ, τ => genLeaf sig Γ τ
  | n + 1, Γ, τ => frequency [
      (1, fun _ => genLeaf sig Γ τ),
      (1, fun _ => match τ with
        | .arrow a b => Expr.lam a <$> genExprP genTy sig n (a :: Γ) b
        | _ => genLeaf sig Γ τ),
      (1, fun _ => do
        let τ' ← genTy
        let f ← genExprP genTy sig n Γ (.arrow τ' τ)
        let x ← genExprP genTy sig n Γ τ'
        return .app f x),
      (1, fun _ =>
        if h : candidates sig τ ≠ [] then do
          let c ← elements (candidates sig τ) h
          let args ← c.ty.args.mapM (genExprP genTy sig n Γ)
          return args.foldl .app (.const c)
        else genLeaf sig Γ τ)]

/-! ## Probability plumbing -/

section plumbing

variable {α β : Type}

theorem prob_eq_zero_of_support {p : SPMF α} {E : Set α} (h : ∀ a ∈ p.support, a ∉ E) :
    SPMF.prob p E = 0 :=
  (SPMF.prob_eq_zero_iff p E).2 h

/-- A bind lands in `E` only through first draws in `F`. -/
theorem prob_bind_le_prob {x : SPMF α} {g : α → SPMF β} {E : Set β} (F : Set α)
    (h : ∀ a, a ∉ F → SPMF.prob (g a) E = 0) :
    SPMF.prob (x >>= g) E ≤ SPMF.prob x F := by
  rw [SPMF.prob_bind]
  refine SPMF.expect_mono fun a => ?_
  by_cases ha : a ∈ F
  · simp only [Set.indicator_of_mem ha, Pi.one_apply]
    exact (SPMF.prob_le_mass _ _).trans (SPMF.mass_le_one _)
  · simp [h a ha]

theorem prob_genLeaf_eq_zero {sig : List Fn} {Γ : List Ty} {τ : Ty} {E : Set Expr}
    (h : ∀ e ∈ leafCands sig Γ τ, e ∉ E) : SPMF.prob (genLeaf sig Γ τ : SPMF Expr) E = 0 := by
  unfold genLeaf
  split
  · rename_i hne
    unfold SPMF.prob
    rw [SPMF.expect_elements hne]
    rw [List.sum_eq_zero, ENNReal.zero_div]
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    simp [Set.indicator_of_notMem (h e he)]
  · unfold SPMF.prob SPMF.expect
    simp [SPMF.default_apply]

theorem mass_genLeaf {sig : List Fn} {Γ : List Ty} {τ : Ty} (h : lits τ ≠ []) :
    (genLeaf sig Γ τ : SPMF Expr).mass = 1 := by
  have hne : leafCands sig Γ τ ≠ [] := by simp [leafCands, h]
  unfold genLeaf
  rw [dif_pos hne, ← SPMF.expect_one, SPMF.expect_elements hne]
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
  exact ENNReal.div_self (by simpa using hne) (by simp)

theorem div_natCast_le {X B : ℝ≥0∞} {k : ℕ} (hk : 1 ≤ k) (h : X ≤ B) : X / k ≤ B :=
  ENNReal.div_le_of_le_mul (h.trans (le_mul_of_one_le_right' (by exact_mod_cast hk)))

/-- The default application rule lands in `E` only through function terms in `F`. -/
theorem prob_appRule_le (genTy : SPMF Ty) (g h : Ty → SPMF Expr) {E : Set Expr} (F : Set Expr)
    (hF : ∀ f, f ∉ F → ∀ x, Expr.app f x ∉ E) (φ : Ty → ℝ≥0∞)
    (hφ : ∀ σ, SPMF.prob (g σ) F ≤ φ σ) :
    SPMF.prob (do
        let σ ← genTy
        let f ← g σ
        let x ← h σ
        return Expr.app f x) E ≤ SPMF.expect genTy φ := by
  rw [SPMF.prob_bind]
  refine SPMF.expect_mono fun σ => (prob_bind_le_prob F fun f hf => ?_).trans (hφ σ)
  refine prob_eq_zero_of_support ?_
  simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff]
  rintro _ ⟨x, -, rfl⟩
  exact hF f hf x

/-- Two draws followed by a `pure` that always lands in `E`: the probability is the product of
the two masses. -/
theorem prob_bind_bind_pure_of_mem {x y : SPMF α} {k : α → α → β} {E : Set β}
    (h : ∀ a b, k a b ∈ E) :
    SPMF.prob (x >>= fun a => y >>= fun b => pure (k a b)) E = x.mass * y.mass := by
  classical
  have hy : ∀ a, SPMF.prob (y >>= fun b => pure (k a b)) E = y.mass := by
    intro a
    rw [SPMF.prob_bind]
    simp only [SPMF.prob_pure, h, if_true]
    exact SPMF.expect_one y
  rw [SPMF.prob_bind]
  simp only [hy, SPMF.expect_const]

end plumbing

/-! ## The default rule: an upper bound -/

section default

variable (genTy : SPMF Ty) (sig : List Fn)

/-- An ambient constant is generated only at its own type. -/
theorem genExpr_prob_const (n : Nat) (Γ : List Ty) {τ : Ty} {c : Fn} (hc : c.ty ≠ τ) :
    SPMF.prob (genExpr genTy sig n Γ τ) {.const c} = 0 := by
  have hleaf : SPMF.prob (genLeaf sig Γ τ : SPMF Expr) {.const c} = 0 := by
    refine prob_genLeaf_eq_zero fun e he hE => hc ?_
    rw [Set.mem_singleton_iff.1 hE] at he
    simp [leafCands, lits, vars] at he
    cases τ <;> simp_all
  cases n with
  | zero => exact hleaf
  | succ n =>
    unfold genExpr
    rw [SPMF.prob_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hleaf, mul_zero,
      zero_add, add_zero, Nat.cast_one, one_mul]
    rw [ENNReal.div_eq_zero_iff, add_eq_zero]
    refine Or.inl ⟨?_, ?_⟩
    · cases τ <;> first
        | exact hleaf
        | exact prob_eq_zero_of_support (by simp; intros; subst_vars; simp)
    · exact prob_eq_zero_of_support (by simp; intros; subst_vars; simp)

/-- A partial call `take a` (at type `τ' → String`) needs `τ' = Int`, and then the inner
application rule must draw `String` as its argument type. -/
theorem genExpr_prob_partialCall (n : Nat) (Γ : List Ty) (τ' : Ty) {take : Fn}
    (ht : take.ty = takeTy) :
    SPMF.prob (genExpr genTy sig n Γ (.arrow τ' .str)) {e | ∃ a, e = .app (.const take) a}
      ≤ if τ' = .int then SPMF.prob genTy {.str} else 0 := by
  have hleaf : SPMF.prob (genLeaf sig Γ (.arrow τ' .str) : SPMF Expr)
      {e | ∃ a, e = .app (.const take) a} = 0 :=
    prob_genLeaf_eq_zero fun e he ⟨a, hE⟩ => by subst hE; simp [leafCands, lits, vars] at he
  cases n with
  | zero => unfold genExpr; rw [hleaf]; exact zero_le _
  | succ n =>
    unfold genExpr
    rw [SPMF.prob_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hleaf, mul_zero,
      zero_add, add_zero, Nat.cast_one, one_mul]
    rw [prob_eq_zero_of_support (by simp; intros; subst_vars; simp), zero_add]
    refine div_natCast_le (by omega) ?_
    refine (prob_appRule_le genTy _ _ {.const take}
      (by rintro f hf x ⟨a, h⟩; cases h; exact hf rfl)
      (fun σ => if σ = .str ∧ τ' = .int then 1 else 0) fun σ => ?_).trans ?_
    · exact if hσ : σ = .str ∧ τ' = .int then (by
          beta_reduce; rw [if_pos hσ]; exact (SPMF.prob_le_mass _ _).trans (SPMF.mass_le_one _))
        else (by
          beta_reduce; rw [if_neg hσ, genExpr_prob_const genTy sig n Γ (by
            rw [ht, takeTy]; intro h; cases h; exact hσ ⟨rfl, rfl⟩)])
    · by_cases hτ : τ' = .int
      · simp only [hτ, and_true, if_true]
        refine le_of_eq ?_
        unfold SPMF.prob; congr 1; funext σ; by_cases h : σ = .str <;> simp [h]
      · simp [hτ, SPMF.expect_const]

/-- **The default rule rarely calls `String.take`.** For every type generator, fuel, and context,
`genExpr` produces a full call `take a b` at type `String` with probability at most
`Pr(genTy = String) * Pr(genTy = Int)`: both application rules must guess an argument type. -/
theorem genExpr_prob_takeCall_le (n : Nat) (Γ : List Ty) {take : Fn} (ht : take.ty = takeTy) :
    SPMF.prob (genExpr genTy sig n Γ .str) (CallOf take)
      ≤ SPMF.prob genTy {.str} * SPMF.prob genTy {.int} := by
  have hleaf : SPMF.prob (genLeaf sig Γ .str : SPMF Expr) (CallOf take) = 0 :=
    prob_genLeaf_eq_zero fun e he ⟨a, b, hE⟩ => by subst hE; simp [leafCands, lits, vars] at he
  cases n with
  | zero => unfold genExpr; rw [hleaf]; exact zero_le _
  | succ n =>
    unfold genExpr
    rw [SPMF.prob_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hleaf, mul_zero,
      zero_add, add_zero, Nat.cast_one, one_mul]
    refine div_natCast_le (by omega) ?_
    refine (prob_appRule_le genTy _ _ {e | ∃ a, e = .app (.const take) a}
      (by rintro f hf x ⟨a, b, h⟩; cases h; exact hf ⟨a, rfl⟩) _ fun σ =>
        genExpr_prob_partialCall genTy sig n Γ σ ht).trans ?_
    have : (fun σ : Ty => if σ = .int then SPMF.prob genTy {.str} else 0)
        = fun σ => SPMF.prob genTy {.str} * ({Ty.int} : Set Ty).indicator 1 σ := by
      funext σ; by_cases h : σ = .int <;> simp [h]
    rw [this, SPMF.expect_mul_left]
    rfl

end default

/-! ## Pałka et al.'s rule: a constant lower bound -/

section palka

variable (genTy : SPMF Ty) (sig : List Fn)

/-- At a base type, `genExprP` succeeds with probability at least `1/4` at every fuel: its leaf
branch always has a literal to return. -/
theorem genExprP_mass_ge (n : Nat) (Γ : List Ty) {τ : Ty} (hτ : lits τ ≠ []) :
    1 / 4 ≤ (genExprP genTy sig n Γ τ).mass := by
  cases n with
  | zero => unfold genExprP; rw [mass_genLeaf hτ]; norm_num
  | succ n =>
    unfold genExprP
    rw [← SPMF.expect_one, SPMF.expect_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, SPMF.expect_one,
      mass_genLeaf hτ, Nat.cast_one, one_mul, add_zero]
    calc (1 : ℝ≥0∞) / 4 = 1 / ((1 + (1 + (1 + 1)) : ℕ) : ℝ≥0∞) := by norm_num
      _ ≤ _ := ENNReal.div_le_div_right le_self_add _

/-- Pałka et al.'s branch, having picked `take`, always produces a call to `take`, and does so
whenever both argument draws succeed. -/
theorem genExprP_prob_takeBranch_ge (n : Nat) (Γ : List Ty) {take : Fn} (ht : take.ty = takeTy) :
    1 / 16 ≤ SPMF.prob (do
        let args ← take.ty.args.mapM (genExprP genTy sig n Γ)
        return args.foldl .app (.const take)) (CallOf take) := by
  rw [ht]
  simp only [takeTy, Ty.args, List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind,
    List.foldl_cons, List.foldl_nil]
  rw [prob_bind_bind_pure_of_mem (k := fun a b => Expr.app (.app (.const take) a) b)
    (E := CallOf take) fun a b => ⟨a, b, rfl⟩]
  calc (1 : ℝ≥0∞) / 16 = 1 / 4 * (1 / 4) := by
        rw [← ENNReal.mul_div_mul_comm (by norm_num) (by norm_num)]; norm_num
    _ ≤ _ := mul_le_mul' (genExprP_mass_ge genTy sig n Γ (by simp [lits]))
        (genExprP_mass_ge genTy sig n Γ (by simp [lits]))

/-- **Pałka et al.'s rule calls `String.take` with constant probability.** For every type
generator, fuel `n + 1`, and context, if `take ∈ sig` then `genExprP` produces a full call
`take a b` at type `String` with probability at least `1 / (64 * |sig|)`. The bound does not
mention `genTy`: no argument type is guessed. -/
theorem genExprP_prob_takeCall_ge (n : Nat) (Γ : List Ty) {take : Fn} (hmem : take ∈ sig)
    (ht : take.ty = takeTy) :
    1 / (64 * sig.length) ≤ SPMF.prob (genExprP genTy sig (n + 1) Γ .str) (CallOf take) := by
  have hc : take ∈ candidates sig .str := by
    simp [candidates, hmem, ht, takeTy, Ty.res]
  have hne : candidates sig .str ≠ [] := List.ne_nil_of_mem hc
  have hlen : (candidates sig .str).length ≤ sig.length := List.length_filter_le _ _
  have hbranch : 1 / (16 * sig.length) ≤ SPMF.prob (do
      let c ← elements (candidates sig .str) hne
      let args ← c.ty.args.mapM (genExprP genTy sig n Γ)
      return args.foldl .app (.const c)) (CallOf take) := by
    rw [SPMF.prob_bind]
    unfold SPMF.prob
    rw [SPMF.expect_elements hne, one_div,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (by norm_num)), div_eq_mul_inv]
    refine mul_le_mul'
      ((le_of_eq (one_div _).symm).trans ((genExprP_prob_takeBranch_ge genTy sig n Γ ht).trans ?_))
      (ENNReal.inv_le_inv.2 (by exact_mod_cast hlen))
    exact List.le_sum_of_mem (List.mem_map_of_mem hc)
  unfold genExprP
  rw [SPMF.prob_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
    add_zero, dif_pos hne]
  have h64 : (1 : ℝ≥0∞) / (64 * sig.length) = 1 / (16 * sig.length) * 4⁻¹ := by
    simp only [one_div]
    rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (by norm_num)),
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (by norm_num)),
      show (64 : ℝ≥0∞) = 16 * 4 by norm_num,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    ring
  rw [h64, ← div_eq_mul_inv, show (((1 + (1 + (1 + 1)) : ℕ)) : ℝ≥0∞) = 4 by norm_num]
  exact ENNReal.div_le_div_right
    (hbranch.trans (le_add_left (le_add_left (le_add_left le_rfl)))) _

end palka

end StrataGenerators.AmbientApp
