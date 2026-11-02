import Basalt.Combinators
import Basalt.SPMF.Expect.Obs
import Basalt.SPMF.Support

/-!
# Ambient function applications: the default STLC rule vs. Pałka et al.'s rule

A small STLC with base types `Int`, `String`, `Bool`, `bv w` and *ambient* functions (constants
of a fixed signature `sig`, e.g. `String.take : String → Int → String`). Two fuel-indexed
generators for terms of a target type, each a uniform `frequency` over named rules:

* `genExpr`  = leaf | `lamRule` | `appRule`: the rules read off the STLC typing rules.
  `appRule` guesses the argument type with `genTy` (paper, Fig. `genApp`).
* `genExprP` = leaf | `lamRule` | `appRule` | `palkaRule`: adds Pałka et al.'s rule, which picks
  an ambient function returning the target type and reads the argument types off its signature.

Results, for every two-argument ambient function `f : a → b → r` in `sig`, type generator
`genTy`, fuel `n`, and context `Γ` (`String.take : String → Int → String` is the running
example, `take_separation`):

* `genExpr_prob_call_le`: Pr[`genExpr` makes a call `f x y`] ≤ `Pr(genTy = a) · Pr(genTy = b)`.
* `genExprP_prob_call_ge`: if `a`, `b`, `r` are base types, `palkaFloor sig` ≤
  Pr[`genExprP` makes a call `f x y`], where `palkaFloor sig` = Pr(pick `palkaRule`) ·
  Pr(pick `f`) · Pr(both arguments succeed), independent of `genTy` and `n`.
* `default_lt_palka`: so Pałka et al.'s rule is strictly more frequent whenever
  `Pr(genTy = a) · Pr(genTy = b) < palkaFloor sig`.
* With `genTy := genTyUniform k` (uniform over `k` base types):
  `genExpr_genTyUniform_prob_call_le` bounds the default rule by `1 / k²`;
  `palka_ratio_ge` shows Pałka et al.'s rule is at least `k² · palkaFloor sig` times as frequent;
  `default_vs_palka_separation` shows the default rule's probability tends to `0` while Pałka
  et al.'s stays `≥ palkaFloor sig`, so from some `N` on Pałka et al.'s is strictly more frequent.
-/

namespace StrataGenerators.AmbientApp

open scoped ENNReal
open SPMF (prob expect mass)

/-! ## Syntax -/

inductive Ty where
  | int | str | bool
  /-- A family of further base types, standing in for Strata's bitvector widths; they let the
  number of base types grow without bound. -/
  | bv (w : Nat)
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

/-- Base types: everything but arrows. -/
def Ty.IsBase : Ty → Prop
  | .arrow _ _ => False
  | _ => True

theorem Ty.IsBase.res {τ : Ty} (h : τ.IsBase) : τ.res = τ := by
  cases τ <;> simp_all [Ty.IsBase, Ty.res]

theorem Ty.IsBase.args {τ : Ty} (h : τ.IsBase) : τ.args = [] := by
  cases τ <;> simp_all [Ty.IsBase, Ty.args]

/-- An ambient function: a name with its (fixed) type. -/
structure Fn where
  name : String
  ty : Ty
  deriving DecidableEq, Repr

inductive Expr where
  | intLit | strLit | boolLit
  | bvLit (w : Nat)
  | var (i : Nat)
  | const (f : Fn)
  | app (f x : Expr)
  | lam (a : Ty) (body : Expr)
  deriving DecidableEq, Repr

/-- `String.take : String → Int → String`. -/
def takeTy : Ty := .arrow .str (.arrow .int .str)

/-- The event "the root of the term is a full call `f a b` of the ambient function `f`". -/
def CallOf (f : Fn) : Set Expr := {e | ∃ a b, e = .app (.app (.const f) a) b}

/-- The event "the root of the term is a partial call `f a`". -/
def PartialCallOf (f : Fn) : Set Expr := {e | ∃ a, e = .app (.const f) a}

/-! ## Generators -/

def lits : Ty → List Expr
  | .int => [.intLit]
  | .str => [.strLit]
  | .bool => [.boolLit]
  | .bv w => [.bvLit w]
  | .arrow _ _ => []

theorem Ty.IsBase.lits_ne_nil {τ : Ty} (h : τ.IsBase) : lits τ ≠ [] := by
  cases τ <;> simp_all [Ty.IsBase, lits]

def vars (Γ : List Ty) (τ : Ty) : List Expr :=
  Γ.zipIdx.filterMap fun (τ', i) => if τ' = τ then some (.var i) else none

/-- Leaves of type `τ`: literals, local variables, and ambient functions of exactly type `τ`. -/
def leafCands (sig : List Fn) (Γ : List Ty) (τ : Ty) : List Expr :=
  lits τ ++ vars Γ τ ++ (sig.filter (·.ty = τ)).map .const

def genLeaf [Gen G] (sig : List Fn) (Γ : List Ty) (τ : Ty) : G Expr :=
  if h : leafCands sig Γ τ ≠ [] then elements (leafCands sig Γ τ) h else default

/-- Ambient functions whose result type is `τ`. -/
def candidates (sig : List Fn) (τ : Ty) : List Fn := sig.filter (·.ty.res = τ)

/-! ## Generation rules -/

/-- The `λ` rule: at an arrow type `a → b`, generate a body of type `b` under `a :: Γ`. At any
other type there is no `λ`, so the rule falls back to a leaf. -/
def lamRule [Gen G] (sig : List Fn) (gen : List Ty → Ty → G Expr) (Γ : List Ty) : Ty → G Expr
  | .arrow a b => Expr.lam a <$> gen (a :: Γ) b
  | τ => genLeaf sig Γ τ

/-- The STLC application rule (paper, Fig. `genApp`): guess an argument type `τ'` with `genTy`,
then generate `f : τ' → τ` and `x : τ'`. -/
def appRule [Gen G] (genTy : G Ty) (gen : Ty → G Expr) (τ : Ty) : G Expr := do
  let τ' ← genTy
  let f ← gen (.arrow τ' τ)
  let x ← gen τ'
  return .app f x

/-- Pałka et al.'s rule: pick an ambient function `c` whose result type is `τ`, generate its
arguments at the types read off `c`'s signature, and apply `c` to them. Falls back to a leaf
when no ambient function returns `τ`. -/
def palkaRule [Gen G] (sig : List Fn) (gen : Ty → G Expr) (Γ : List Ty) (τ : Ty) : G Expr :=
  if h : candidates sig τ ≠ [] then do
    let c ← elements (candidates sig τ) h
    let args ← c.ty.args.mapM gen
    return args.foldl .app (.const c)
  else genLeaf sig Γ τ

/-! ## Generators -/

/-- Terms of type `τ`, built only from the rules read off the STLC typing rules. -/
def genExpr [Gen G] (genTy : G Ty) (sig : List Fn) : Nat → List Ty → Ty → G Expr
  | 0, Γ, τ => genLeaf sig Γ τ
  | n + 1, Γ, τ => frequency [
      (1, fun _ => genLeaf sig Γ τ),
      (1, fun _ => lamRule sig (genExpr genTy sig n) Γ τ),
      (1, fun _ => appRule genTy (genExpr genTy sig n Γ) τ)]

/-- `genExpr` plus Pałka et al.'s rule for applying an ambient function. -/
def genExprP [Gen G] (genTy : G Ty) (sig : List Fn) : Nat → List Ty → Ty → G Expr
  | 0, Γ, τ => genLeaf sig Γ τ
  | n + 1, Γ, τ => frequency [
      (1, fun _ => genLeaf sig Γ τ),
      (1, fun _ => lamRule sig (genExprP genTy sig n) Γ τ),
      (1, fun _ => appRule genTy (genExprP genTy sig n Γ) τ),
      (1, fun _ => palkaRule sig (genExprP genTy sig n Γ) Γ τ)]

/-! ## Probability plumbing

Generic facts about `prob`, `expect` and `mass`, independent of the generators. -/

section plumbing

variable {α β : Type}

theorem prob_eq_zero_of_support {p : SPMF α} {E : Set α} (h : ∀ a ∈ p.support, a ∉ E) :
    prob p E = 0 :=
  (SPMF.prob_eq_zero_iff p E).2 h

/-- If `g a` can only land in `E` when `a ∈ F`, then `x >>= g` lands in `E` at most as often as
`x` lands in `F`. -/
theorem prob_bind_le_prob {x : SPMF α} {g : α → SPMF β} {E : Set β} (F : Set α)
    (h : ∀ a, a ∉ F → prob (g a) E = 0) :
    prob (x >>= g) E ≤ prob x F := by
  rw [SPMF.prob_bind]
  refine SPMF.expect_mono fun a => ?_
  by_cases ha : a ∈ F
  · simp only [Set.indicator_of_mem ha, Pi.one_apply]
    exact (SPMF.prob_le_mass _ _).trans (SPMF.mass_le_one _)
  · simp [h a ha]

/-- Two draws, then a `pure` that always lands in `E`: the probability is the product of the
two masses (the chance that both draws succeed). -/
theorem prob_bind_bind_pure_of_mem {x : SPMF α} {y : SPMF α} {mk : α → α → β} {E : Set β}
    (h : ∀ a b, mk a b ∈ E) :
    prob (x >>= fun a => y >>= fun b => pure (mk a b)) E = mass x * mass y := by
  classical
  have hy : ∀ a, prob (y >>= fun b => pure (mk a b)) E = mass y := by
    intro a
    rw [SPMF.prob_bind]
    simp only [SPMF.prob_pure, h, if_true]
    exact SPMF.expect_one y
  rw [SPMF.prob_bind]
  simp only [hy, SPMF.expect_const]

/-- `E[if x = a then c else 0] = c · Pr(x = a)`. -/
theorem expect_ite_singleton [DecidableEq α] (p : SPMF α) (a : α) (c : ℝ≥0∞) :
    expect p (fun x => if x = a then c else 0) = c * prob p {a} := by
  have : (fun x => if x = a then c else 0) = fun x => c * (if x = a then 1 else 0) := by
    funext x; split <;> simp
  rw [this, SPMF.expect_mul_left, SPMF.expect_ite_eq, SPMF.prob_singleton]

/-- A uniform choice among three branches averages their probabilities. -/
theorem prob_frequency3 (a b c : Unit → SPMF α) (h) (E : Set α) :
    prob (frequency [(1, a), (1, b), (1, c)] h) E
      = (prob (a ()) E + prob (b ()) E + prob (c ()) E) / 3 := by
  rw [SPMF.prob_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
    add_zero, add_assoc]
  norm_num

/-- A uniform choice among four branches averages their probabilities. -/
theorem prob_frequency4 (a b c d : Unit → SPMF α) (h) (E : Set α) :
    prob (frequency [(1, a), (1, b), (1, c), (1, d)] h) E
      = (prob (a ()) E + prob (b ()) E + prob (c ()) E + prob (d ()) E) / 4 := by
  rw [SPMF.prob_frequency]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one, one_mul,
    add_zero, add_assoc]
  norm_num

theorem mass_eq_prob_univ (p : SPMF α) : mass p = prob p Set.univ := by
  unfold SPMF.prob
  rw [Set.indicator_univ]
  exact (SPMF.expect_one p).symm

theorem div_three_le (x : ℝ≥0∞) : x / 3 ≤ x :=
  ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' (by norm_num))

end plumbing

/-! ## Facts about each rule

Each lemma is stated for an arbitrary recursive generator `gen`, so it is about the rule alone. -/

section rules

variable {G : Type → Type} (sig : List Fn) (Γ : List Ty)

/-- A leaf lands in `E` only if one of the leaf candidates is in `E`. -/
theorem prob_genLeaf_eq_zero {τ : Ty} {E : Set Expr} (h : ∀ e ∈ leafCands sig Γ τ, e ∉ E) :
    prob (genLeaf sig Γ τ : SPMF Expr) E = 0 := by
  unfold genLeaf
  split
  · rename_i hne
    unfold SPMF.prob
    rw [SPMF.expect_elements hne, List.sum_eq_zero, ENNReal.zero_div]
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    simp [Set.indicator_of_notMem (h e he)]
  · unfold SPMF.prob SPMF.expect
    simp [SPMF.default_apply]

/-- No leaf is an application. -/
theorem prob_genLeaf_app_eq_zero {τ : Ty} {E : Set Expr} (hE : ∀ e ∈ E, ∃ f x, e = .app f x) :
    prob (genLeaf sig Γ τ : SPMF Expr) E = 0 :=
  prob_genLeaf_eq_zero sig Γ fun e he hmem => by
    obtain ⟨f, x, rfl⟩ := hE e hmem
    cases τ <;> simp [leafCands, lits, vars] at he

/-- At a base type (one with a literal), a leaf always succeeds. -/
theorem mass_genLeaf {τ : Ty} (h : lits τ ≠ []) : mass (genLeaf sig Γ τ : SPMF Expr) = 1 := by
  have hne : leafCands sig Γ τ ≠ [] := by simp [leafCands, h]
  unfold genLeaf
  rw [dif_pos hne, ← SPMF.expect_one, SPMF.expect_elements hne]
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
  exact ENNReal.div_self (by simpa using hne) (by simp)

/-- No `λ`-rule output is an application: at an arrow type it produces a `λ`, and at any other
type it falls back to a leaf. -/
theorem prob_lamRule_app_eq_zero (gen : List Ty → Ty → SPMF Expr) (τ : Ty)
    {E : Set Expr} (hE : ∀ e ∈ E, ∃ f x, e = .app f x) :
    prob (lamRule sig gen Γ τ) E = 0 := by
  cases τ with
  | arrow a b =>
    refine prob_eq_zero_of_support fun e he hmem => ?_
    simp only [lamRule, SPMF.mem_support_map_iff] at he
    obtain ⟨body, -, rfl⟩ := he
    obtain ⟨f, x, h⟩ := hE _ hmem
    cases h
  | _ => exact prob_genLeaf_app_eq_zero sig Γ hE

/-- The application rule produces only applications. -/
theorem prob_appRule_eq_zero (genTy : SPMF Ty) (gen : Ty → SPMF Expr) (τ : Ty) {E : Set Expr}
    (hE : ∀ f x, Expr.app f x ∉ E) : prob (appRule genTy gen τ) E = 0 :=
  prob_eq_zero_of_support fun e he hmem => by
    simp only [appRule, SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at he
    obtain ⟨_, -, f, -, x, -, rfl⟩ := he
    exact hE f x hmem

/-- **The application rule, bounded.** If `f x ∈ E` forces `f ∈ F`, then the rule lands in `E`
at most as often as the guessed function type `τ' → τ` lands in `F`, averaged over the guess
`τ' ∼ genTy`. -/
theorem prob_appRule_le (genTy : SPMF Ty) (gen : Ty → SPMF Expr) (τ : Ty) {E : Set Expr}
    (F : Set Expr) (hF : ∀ f x, Expr.app f x ∈ E → f ∈ F) (φ : Ty → ℝ≥0∞)
    (hφ : ∀ τ', prob (gen (.arrow τ' τ)) F ≤ φ τ') :
    prob (appRule genTy gen τ) E ≤ expect genTy φ := by
  unfold appRule
  rw [SPMF.prob_bind]
  refine SPMF.expect_mono fun τ' => (prob_bind_le_prob F fun f hf => ?_).trans (hφ τ')
  refine prob_eq_zero_of_support ?_
  simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff]
  rintro _ ⟨x, -, rfl⟩ hmem
  exact hf (hF f x hmem)

/-- **Pałka et al.'s rule, bounded below.** For an ambient function `f : a → b → r` in `sig`
with `r` a base type, the rule (at target `r`) calls `f` with probability at least
`Pr(pick f) · Pr(gen a succeeds) · Pr(gen b succeeds)`. -/
theorem prob_palkaRule_call_ge (gen : Ty → SPMF Expr) {f : Fn} {a b r : Ty} (hmem : f ∈ sig)
    (hf : f.ty = .arrow a (.arrow b r)) (hr : r.IsBase) :
    ((candidates sig r).length : ℝ≥0∞)⁻¹ * (mass (gen a) * mass (gen b))
      ≤ prob (palkaRule sig gen Γ r) (CallOf f) := by
  have hc : f ∈ candidates sig r := by simp [candidates, hmem, hf, Ty.res, hr.res]
  have hne : candidates sig r ≠ [] := List.ne_nil_of_mem hc
  -- Once `f` is picked, the call is made iff both argument draws succeed.
  have hcall : prob (do
      let args ← f.ty.args.mapM gen
      return args.foldl .app (.const f)) (CallOf f) = mass (gen a) * mass (gen b) := by
    rw [hf]
    simp only [Ty.args, hr.args, List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind,
      List.foldl_cons, List.foldl_nil]
    exact prob_bind_bind_pure_of_mem (mk := fun x y => Expr.app (.app (.const f) x) y)
      fun x y => ⟨x, y, rfl⟩
  -- `elements` averages over the candidates; keep only the `f` summand.
  unfold palkaRule
  rw [dif_pos hne, SPMF.prob_bind]
  unfold SPMF.prob
  rw [SPMF.expect_elements hne, div_eq_mul_inv, mul_comm]
  gcongr
  rw [← hcall]
  exact List.le_sum_of_mem (List.mem_map_of_mem hc)

end rules

/-! ## The default rule: an upper bound

Throughout, `f : a → b → r` is a two-argument ambient function. -/

section default

variable (genTy : SPMF Ty) (sig : List Fn)

/-- An ambient constant `c` is generated (as a leaf) only at its own type `c.ty`. -/
theorem genExpr_prob_const_le (n : Nat) (Γ : List Ty) (τ : Ty) (c : Fn) :
    prob (genExpr genTy sig n Γ τ) {.const c} ≤ if c.ty = τ then 1 else 0 := by
  split
  · exact (SPMF.prob_le_mass _ _).trans (SPMF.mass_le_one _)
  rename_i hc
  have hleaf : prob (genLeaf sig Γ τ : SPMF Expr) {.const c} = 0 := by
    refine prob_genLeaf_eq_zero sig Γ fun e he hE => hc ?_
    rw [Set.mem_singleton_iff.1 hE] at he
    simp [leafCands, lits, vars] at he
    cases τ <;> simp_all
  cases n with
  | zero => exact hleaf.le
  | succ n =>
    have hlam : prob (lamRule sig (genExpr genTy sig n) Γ τ) {.const c} = 0 := by
      cases τ <;> first
        | exact hleaf
        | exact prob_eq_zero_of_support (by simp [lamRule]; intros; subst_vars; simp)
    unfold genExpr
    rw [prob_frequency3, hleaf, hlam, prob_appRule_eq_zero genTy _ τ (by simp)]
    simp

/-- **The inner application.** A partial call `f x` at type `τ' → r` requires the inner
`appRule` to guess `a`, and is only well typed if `τ' = b`. -/
theorem genExpr_prob_partialCall_le (n : Nat) (Γ : List Ty) (τ' : Ty) {f : Fn} {a b r : Ty}
    (hf : f.ty = .arrow a (.arrow b r)) :
    prob (genExpr genTy sig n Γ (.arrow τ' r)) (PartialCallOf f)
      ≤ if τ' = b then prob genTy {a} else 0 := by
  have hApp : ∀ e ∈ PartialCallOf f, ∃ g x, e = .app g x := fun _ ⟨x, h⟩ => ⟨_, x, h⟩
  cases n with
  | zero =>
    unfold genExpr; rw [prob_genLeaf_app_eq_zero sig Γ hApp]; exact zero_le _
  | succ n =>
    calc prob (genExpr genTy sig (n + 1) Γ (.arrow τ' r)) (PartialCallOf f)
        -- The leaf and `λ` branches never produce an application.
        = prob (appRule genTy (genExpr genTy sig n Γ) (.arrow τ' r)) (PartialCallOf f) / 3 := by
          unfold genExpr
          rw [prob_frequency3, prob_genLeaf_app_eq_zero sig Γ hApp,
            prob_lamRule_app_eq_zero sig Γ _ _ hApp, zero_add, zero_add]
      _ ≤ prob (appRule genTy (genExpr genTy sig n Γ) (.arrow τ' r)) (PartialCallOf f) :=
          div_three_le _
      -- `f x` needs the function part to be the constant `f`, of type `σ → τ' → r` for the
      -- guessed argument type `σ`.
      _ ≤ expect genTy (fun σ => if f.ty = .arrow σ (.arrow τ' r) then 1 else 0) :=
          prob_appRule_le genTy _ _ {.const f} (by rintro g x ⟨y, h⟩; cases h; rfl) _
            fun σ => genExpr_prob_const_le genTy sig n Γ _ f
      -- That type is `f.ty = a → b → r` iff `σ = a` and `τ' = b`.
      _ = if τ' = b then prob genTy {a} else 0 := by
          by_cases hτ : τ' = b
          · subst hτ
            simp only [hf, Ty.arrow.injEq, and_true, if_true]
            simp_rw [eq_comm (a := a)]
            rw [expect_ite_singleton, one_mul]
          · simp [hf, hτ, Ne.symm hτ, SPMF.expect_const]

/-- **The default rule rarely calls a two-argument function.** For every type generator, fuel,
and context, `genExpr` produces a full call `f x y` of `f : a → b → r` (at type `r`) with
probability at most `Pr(genTy = a) · Pr(genTy = b)`: both application rules must guess an
argument type. -/
theorem genExpr_prob_call_le (n : Nat) (Γ : List Ty) {f : Fn} {a b r : Ty}
    (hf : f.ty = .arrow a (.arrow b r)) :
    prob (genExpr genTy sig n Γ r) (CallOf f) ≤ prob genTy {a} * prob genTy {b} := by
  have hApp : ∀ e ∈ CallOf f, ∃ g x, e = .app g x := fun _ ⟨x, y, h⟩ => ⟨_, y, h⟩
  cases n with
  | zero =>
    unfold genExpr; rw [prob_genLeaf_app_eq_zero sig Γ hApp]; exact zero_le _
  | succ n =>
    calc prob (genExpr genTy sig (n + 1) Γ r) (CallOf f)
        -- The leaf and `λ` branches never produce an application.
        = prob (appRule genTy (genExpr genTy sig n Γ) r) (CallOf f) / 3 := by
          unfold genExpr
          rw [prob_frequency3, prob_genLeaf_app_eq_zero sig Γ hApp,
            prob_lamRule_app_eq_zero sig Γ _ _ hApp, zero_add, zero_add]
      _ ≤ prob (appRule genTy (genExpr genTy sig n Γ) r) (CallOf f) := div_three_le _
      -- `f x y` needs the function part to be a partial call `f x`, at the guessed type
      -- `τ' → r` ...
      _ ≤ expect genTy (fun τ' => if τ' = b then prob genTy {a} else 0) :=
          prob_appRule_le genTy _ _ (PartialCallOf f)
            (by rintro g y ⟨x, z, h⟩; cases h; exact ⟨x, rfl⟩) _
            fun τ' => genExpr_prob_partialCall_le genTy sig n Γ τ' hf
      -- ... and the guess must be `b`.
      _ = prob genTy {a} * prob genTy {b} := expect_ite_singleton _ _ _

end default

/-! ## Pałka et al.'s rule: a constant lower bound -/

section palka

variable (genTy : SPMF Ty) (sig : List Fn)

/-- Each of `genExprP`'s four branches is taken with probability `1/4`. -/
noncomputable def branchShare : ℝ≥0∞ := 1 / 4

/-- The lower bound for Pałka et al.'s rule, as a product of the three things that must happen:
* `branchShare`: `genExprP` picks `palkaRule`;
* `|sig|⁻¹`: `palkaRule` picks the function (among at most `|sig|` candidates);
* `branchShare²`: both argument draws succeed (each does, at least through its leaf branch). -/
noncomputable def palkaFloor (sig : List Fn) : ℝ≥0∞ :=
  branchShare * (sig.length : ℝ≥0∞)⁻¹ * (branchShare * branchShare)

theorem palkaFloor_pos : 0 < palkaFloor sig := by
  simp [palkaFloor, branchShare, pos_iff_ne_zero]

/-- At a base type, `genExprP` succeeds with probability at least `branchShare` at every fuel:
its leaf branch alone always succeeds. -/
theorem genExprP_mass_ge (n : Nat) (Γ : List Ty) {τ : Ty} (hτ : τ.IsBase) :
    branchShare ≤ mass (genExprP genTy sig n Γ τ) := by
  cases n with
  | zero =>
    unfold genExprP; rw [mass_genLeaf sig Γ hτ.lits_ne_nil, branchShare]; norm_num
  | succ n =>
    rw [mass_eq_prob_univ]
    unfold genExprP
    rw [prob_frequency4, ← mass_eq_prob_univ, mass_genLeaf sig Γ hτ.lits_ne_nil, branchShare,
      add_assoc, add_assoc]
    -- Keep the leaf branch, drop the other three.
    exact ENNReal.div_le_div_right le_self_add _

/-- **Pałka et al.'s rule, exact shape of the bound.** At fuel `n + 1`, a call to
`f : a → b → r` is made with probability at least
`Pr(pick palkaRule) · Pr(pick f) · Pr(a argument succeeds) · Pr(b argument succeeds)`. -/
theorem genExprP_prob_call_ge_shape (n : Nat) (Γ : List Ty) {f : Fn} {a b r : Ty}
    (hmem : f ∈ sig) (hf : f.ty = .arrow a (.arrow b r)) (hr : r.IsBase) :
    branchShare * ((candidates sig r).length : ℝ≥0∞)⁻¹
        * (mass (genExprP genTy sig n Γ a) * mass (genExprP genTy sig n Γ b))
      ≤ prob (genExprP genTy sig (n + 1) Γ r) (CallOf f) := by
  calc branchShare * ((candidates sig r).length : ℝ≥0∞)⁻¹
          * (mass (genExprP genTy sig n Γ a) * mass (genExprP genTy sig n Γ b))
      ≤ branchShare * prob (palkaRule sig (genExprP genTy sig n Γ) Γ r) (CallOf f) := by
        rw [mul_assoc]
        gcongr
        exact prob_palkaRule_call_ge sig Γ _ hmem hf hr
    -- `branchShare * p = p / 4`, and `palkaRule` is one of the four averaged branches.
    _ ≤ prob (genExprP genTy sig (n + 1) Γ r) (CallOf f) := by
        unfold genExprP
        rw [prob_frequency4, branchShare, mul_comm, ← div_eq_mul_one_div]
        exact ENNReal.div_le_div_right le_add_self _

/-- **Pałka et al.'s rule calls a two-argument function with constant probability.** For every
type generator, fuel `n + 1`, and context, if `f : a → b → r` is in `sig` and `a`, `b`, `r` are
base types, then `genExprP` produces a full call `f x y` with probability at least
`palkaFloor sig`, which does not mention `genTy` or `n`. -/
theorem genExprP_prob_call_ge (n : Nat) (Γ : List Ty) {f : Fn} {a b r : Ty} (hmem : f ∈ sig)
    (hf : f.ty = .arrow a (.arrow b r)) (ha : a.IsBase) (hb : b.IsBase) (hr : r.IsBase) :
    palkaFloor sig ≤ prob (genExprP genTy sig (n + 1) Γ r) (CallOf f) := by
  refine le_trans ?_ (genExprP_prob_call_ge_shape genTy sig n Γ hmem hf hr)
  unfold palkaFloor
  gcongr
  · exact List.length_filter_le _ _
  · exact genExprP_mass_ge genTy sig n Γ ha
  · exact genExprP_mass_ge genTy sig n Γ hb

end palka

/-! ## Comparing the two rules -/

section compare

variable (sig : List Fn)

/-- **Conditional comparison.** Whenever `genTy` puts little enough mass on the argument types
`a` and `b`, Pałka et al.'s rule calls `f : a → b → r` strictly more often than the default
rule, at the same fuel. -/
theorem default_lt_palka (genTy : SPMF Ty) (n : Nat) (Γ : List Ty) {f : Fn} {a b r : Ty}
    (hmem : f ∈ sig) (hf : f.ty = .arrow a (.arrow b r))
    (ha : a.IsBase) (hb : b.IsBase) (hr : r.IsBase)
    (hsmall : prob genTy {a} * prob genTy {b} < palkaFloor sig) :
    prob (genExpr genTy sig (n + 1) Γ r) (CallOf f)
      < prob (genExprP genTy sig (n + 1) Γ r) (CallOf f) :=
  calc prob (genExpr genTy sig (n + 1) Γ r) (CallOf f)
      ≤ prob genTy {a} * prob genTy {b} := genExpr_prob_call_le genTy sig _ Γ hf
    _ < palkaFloor sig := hsmall
    _ ≤ prob (genExprP genTy sig (n + 1) Γ r) (CallOf f) :=
        genExprP_prob_call_ge genTy sig n Γ hmem hf ha hb hr

/-- `numBaseTypes` base types: `Int`, `String`, and the bitvector types
`bv 0, …, bv (numBaseTypes - 3)` (just `Int` and `String` when `numBaseTypes ≤ 2`). -/
def baseTys (numBaseTypes : Nat) : List Ty :=
  .int :: .str :: (List.range (numBaseTypes - 2)).map Ty.bv

theorem baseTys_nodup (numBaseTypes : Nat) : (baseTys numBaseTypes).Nodup := by
  simp only [baseTys, List.nodup_cons, List.mem_cons, List.mem_map, reduceCtorEq,
    and_false, exists_false, not_false_eq_true, true_and, or_self]
  exact List.Nodup.map (fun _ _ h => Ty.bv.inj h) List.nodup_range

/-- A type generator uniform over the base types of `baseTys numBaseTypes`. -/
def genTyUniform [Gen G] (numBaseTypes : Nat) : G Ty :=
  elements (baseTys numBaseTypes) (by simp [baseTys])

/-- In a list without duplicates, a type occurs at most once. -/
theorem sum_indicator_le_one {l : List Ty} (hl : l.Nodup) (τ : Ty) :
    (l.map (({τ} : Set Ty).indicator (1 : Ty → ℝ≥0∞))).sum ≤ 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons]
    by_cases hx : x = τ
    · subst hx
      rw [List.sum_eq_zero fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact Set.indicator_of_notMem (fun h => hl.1 (by
          rw [Set.mem_singleton_iff] at h; subst h; exact hz)) _]
      simp
    · simp only [Set.indicator_of_notMem (show x ∉ ({τ} : Set Ty) from hx), zero_add]
      exact ih hl.2

/-- With `numBaseTypes ≥ 2` base types, `genTyUniform` picks any given type with probability at
most `1 / numBaseTypes` (exactly that for a base type in the list, `0` otherwise). -/
theorem genTyUniform_prob_le {numBaseTypes : Nat} (h2 : 2 ≤ numBaseTypes) (τ : Ty) :
    prob (genTyUniform numBaseTypes : SPMF Ty) {τ} ≤ (numBaseTypes : ℝ≥0∞)⁻¹ := by
  unfold SPMF.prob genTyUniform
  rw [SPMF.expect_elements, div_eq_mul_inv]
  have hlen : (baseTys numBaseTypes).length = numBaseTypes := by simp [baseTys]; omega
  rw [hlen]
  calc _ ≤ 1 * (numBaseTypes : ℝ≥0∞)⁻¹ := by
          gcongr; exact sum_indicator_le_one (baseTys_nodup _) τ
    _ = _ := one_mul _

/-- **The default rule with `k` uniformly drawn base types.** With `k ≥ 2` base types, the
STLC application rule produces a call to `f : a → b → r` with probability at most `1 / k²`: it
must guess `a` (probability `≤ 1/k`) and then `b` (probability `≤ 1/k`). -/
theorem genExpr_genTyUniform_prob_call_le (n : Nat) (Γ : List Ty) {f : Fn} {a b r : Ty}
    (hf : f.ty = .arrow a (.arrow b r)) {k : Nat} (hk : 2 ≤ k) :
    prob (genExpr (genTyUniform k) sig n Γ r) (CallOf f) ≤ 1 / (k : ℝ≥0∞) ^ 2 :=
  calc prob (genExpr (genTyUniform k) sig n Γ r) (CallOf f)
      ≤ prob (genTyUniform k) {a} * prob (genTyUniform k) {b} :=
        genExpr_prob_call_le _ sig n Γ hf
    _ ≤ (k : ℝ≥0∞)⁻¹ * (k : ℝ≥0∞)⁻¹ := by
        gcongr <;> exact genTyUniform_prob_le hk _
    _ = 1 / (k : ℝ≥0∞) ^ 2 := by
        rw [one_div, sq, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
          (Or.inl (ENNReal.natCast_ne_top _))]

/-- **Ratio.** With `k ≥ 2` uniformly drawn base types, Pałka et al.'s rule calls
`f : a → b → r` at least `k² · palkaFloor sig` times as often as the STLC application rule
(stated multiplicatively, so that no probability is divided by). -/
theorem palka_ratio_ge (n : Nat) (Γ : List Ty) {f : Fn} {a b r : Ty} (hmem : f ∈ sig)
    (hf : f.ty = .arrow a (.arrow b r)) (ha : a.IsBase) (hb : b.IsBase) (hr : r.IsBase)
    {k : Nat} (hk : 2 ≤ k) :
    (k : ℝ≥0∞) ^ 2 * palkaFloor sig * prob (genExpr (genTyUniform k) sig (n + 1) Γ r) (CallOf f)
      ≤ prob (genExprP (genTyUniform k) sig (n + 1) Γ r) (CallOf f) := by
  have hk0 : ((k : ℝ≥0∞) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : k ≠ 0))
  have hkT : ((k : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  calc (k : ℝ≥0∞) ^ 2 * palkaFloor sig * prob (genExpr (genTyUniform k) sig (n + 1) Γ r) (CallOf f)
      = palkaFloor sig * ((k : ℝ≥0∞) ^ 2 * prob (genExpr (genTyUniform k) sig (n + 1) Γ r)
          (CallOf f)) := by ring
    -- `k² · Pr_STLC ≤ k² · (1/k²) = 1`.
    _ ≤ palkaFloor sig * ((k : ℝ≥0∞) ^ 2 * (1 / (k : ℝ≥0∞) ^ 2)) := by
        gcongr; exact genExpr_genTyUniform_prob_call_le sig _ Γ hf hk
    _ = palkaFloor sig := by rw [one_div, ENNReal.mul_inv_cancel hk0 hkT, mul_one]
    _ ≤ prob (genExprP (genTyUniform k) sig (n + 1) Γ r) (CallOf f) :=
        genExprP_prob_call_ge _ sig n Γ hmem hf ha hb hr

/-- **Separation.** As the number of base types grows (`numBaseTypes → ∞`), for a
two-argument ambient function `f : a → b → r` over base types:
1. the default rule's probability of calling `f` drops below any `ε > 0` for all large enough
   `numBaseTypes` (i.e. it tends to `0`);
2. Pałka et al.'s stays at least `palkaFloor sig` for every `numBaseTypes`;
3. hence, from some `N` on, Pałka et al.'s rule is strictly more frequent. -/
theorem default_vs_palka_separation (n : Nat) (Γ : List Ty) {f : Fn} {a b r : Ty}
    (hmem : f ∈ sig) (hf : f.ty = .arrow a (.arrow b r))
    (ha : a.IsBase) (hb : b.IsBase) (hr : r.IsBase) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ numBaseTypes ≥ N,
        prob (genExpr (genTyUniform numBaseTypes) sig n Γ r) (CallOf f) < ε)
      ∧ (∀ numBaseTypes, palkaFloor sig ≤
          prob (genExprP (genTyUniform numBaseTypes) sig (n + 1) Γ r) (CallOf f))
      ∧ ∃ N, ∀ numBaseTypes ≥ N,
          prob (genExpr (genTyUniform numBaseTypes) sig (n + 1) Γ r) (CallOf f)
            < prob (genExprP (genTyUniform numBaseTypes) sig (n + 1) Γ r) (CallOf f) := by
  -- With `k ≥ 2` base types, the default rule's probability is at most `1/k² ≤ 1/k`.
  have hbound : ∀ m k, 2 ≤ k →
      prob (genExpr (genTyUniform k) sig m Γ r) (CallOf f) ≤ (k : ℝ≥0∞)⁻¹ := by
    intro m k hk
    calc prob (genExpr (genTyUniform k) sig m Γ r) (CallOf f)
        ≤ 1 / (k : ℝ≥0∞) ^ 2 := genExpr_genTyUniform_prob_call_le sig m Γ hf hk
      _ ≤ 1 / (k : ℝ≥0∞) := by
          gcongr
          exact_mod_cast (Nat.le_self_pow (by norm_num) k)
      _ = (k : ℝ≥0∞)⁻¹ := one_div _
  -- (1): pick `N₀` with `N₀⁻¹ < ε`; for `k ≥ max N₀ 2`, `Pr ≤ k⁻¹ ≤ N₀⁻¹ < ε`.
  have hsmall : ∀ m (ε : ℝ≥0∞), 0 < ε → ∃ N, ∀ k ≥ N,
      prob (genExpr (genTyUniform k) sig m Γ r) (CallOf f) < ε := by
    intro m ε hε
    obtain ⟨N₀, hN₀⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine ⟨max N₀ 2, fun k hk => (hbound m k (by omega)).trans_lt ?_⟩
    exact (ENNReal.inv_le_inv.2 (by exact_mod_cast (by omega : N₀ ≤ k))).trans_lt hN₀
  -- (2) is the lower bound.
  have hfloor := fun k => genExprP_prob_call_ge (genTyUniform k) sig n Γ hmem hf ha hb hr
  -- (3): apply (1) at fuel `n + 1` with `ε := palkaFloor sig`, which is positive.
  obtain ⟨N, hN⟩ := hsmall (n + 1) _ (palkaFloor_pos sig)
  exact ⟨hsmall n, hfloor, N, fun k hk => (hN k hk).trans_le (hfloor k)⟩

/-- The running example: `String.take : String → Int → String`. -/
theorem take_separation (n : Nat) (Γ : List Ty) {take : Fn} (hmem : take ∈ sig)
    (ht : take.ty = takeTy) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ numBaseTypes ≥ N,
        prob (genExpr (genTyUniform numBaseTypes) sig n Γ .str) (CallOf take) < ε)
      ∧ (∀ numBaseTypes, palkaFloor sig ≤
          prob (genExprP (genTyUniform numBaseTypes) sig (n + 1) Γ .str) (CallOf take))
      ∧ ∃ N, ∀ numBaseTypes ≥ N,
          prob (genExpr (genTyUniform numBaseTypes) sig (n + 1) Γ .str) (CallOf take)
            < prob (genExprP (genTyUniform numBaseTypes) sig (n + 1) Γ .str) (CallOf take) :=
  default_vs_palka_separation sig n Γ hmem ht trivial trivial trivial

end compare

end StrataGenerators.AmbientApp
