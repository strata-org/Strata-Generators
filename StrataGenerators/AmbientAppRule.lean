import Basalt.Combinators
import Basalt.SPMF.Expect.Obs
import Basalt.SPMF.Support
import Basalt.Walk.Expect
import Basalt.Walk.Mass
import Strata.DL.Lambda.LTy

/-!
# Ambient function applications: the default STLC rule vs. Pałka et al.'s rule

A small STLC with base types `Int`, `String`, `Bool`, `bv w`, any further (opaque) Strata Core
type, and *ambient* functions (constants of a fixed signature `sig`, e.g.
`String.take : String → Int → String`). Two fuel-indexed generators for terms of a target type,
each a uniform `frequency` over named rules:

* `genExpr`  = leaf | `lamRule` | `appRule`: the rules read off the STLC typing rules.
  `appRule` guesses the argument type with `genTy` (paper, Fig. `genApp`).
* `genExprP` = leaf | `lamRule` | `appRule` | `palkaRule`: adds Pałka et al.'s rule, which picks
  an ambient function returning the target type and reads the argument types off its signature.

Results, for every ambient function `f : a₁ → ⋯ → aₘ → r` in `sig` (of *any* arity `m`; its
argument types are `f.ty.args = [a₁, …, aₘ]` and its result type `f.ty.res = r`), type
generator `genTy`, fuel `n`, and context `Γ`:

* `genExpr_prob_call_le`: Pr[`genExpr` makes a full call `f x₁ ⋯ xₘ`]
  ≤ `Pr(genTy = a₁) ⋯ Pr(genTy = aₘ)`: each of the `m` nested application rules must guess its
  argument type.
* `genExprP_prob_call_ge`: if every `aᵢ` is a base type, `palkaFloor sig m` ≤
  Pr[`genExprP` makes a full call `f x₁ ⋯ xₘ`], where `palkaFloor sig m` = Pr(pick
  `palkaRule`) · Pr(pick `f`) · Pr(all `m` arguments succeed), independent of `genTy` and `n`.
* `default_lt_palka`: so Pałka et al.'s rule is strictly more frequent whenever
  `Pr(genTy = a₁) ⋯ Pr(genTy = aₘ) < palkaFloor sig m`.
* With `genTy := genTyUniform k` (uniform over `k` base types):
  `genExpr_genTyUniform_prob_call_le` bounds the default rule by `1 / kᵐ`;
  `palka_ratio_ge` shows Pałka et al.'s rule is at least `kᵐ · palkaFloor sig m` times as
  frequent; for `m ≥ 1`, `default_vs_palka_separation` shows the default rule's probability tends
  to `0` while Pałka et al.'s stays `≥ palkaFloor sig m`, so from some `N` on Pałka et al.'s is
  strictly more frequent.

`String.take : String → Int → String` is the running example (`take_separation`);
`AmbientAppRuleCore.lean` instantiates `sig` with the monomorphic functions of `Core.Factory`.
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
  /-- Any other Strata Core type (`real`, `regex`, `Map int bool`, …), kept opaque: a base type
  with a literal. This is an idealization: Strata has no literals for `regex` or `Map` types. -/
  | other (t : Lambda.LMonoTy)
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
  | otherLit (t : Lambda.LMonoTy)
  | var (i : Nat)
  | const (f : Fn)
  | app (f x : Expr)
  | lam (a : Ty) (body : Expr)
  deriving DecidableEq, Repr

/-- `String.take : String → Int → String`. -/
def takeTy : Ty := .arrow .str (.arrow .int .str)

/-- The event "the root of the term is the ambient function `f` applied to exactly `k`
arguments": `f` itself for `k = 0`, and an application `g x` with `g` such a term for `k - 1`
otherwise. -/
def CallN (f : Fn) : Nat → Set Expr
  | 0 => {.const f}
  | k + 1 => {e | ∃ g x, e = .app g x ∧ g ∈ CallN f k}

/-- The event "the root of the term is a full call `f x₁ ⋯ xₘ`", `m = f.ty.args.length`. -/
def CallOf (f : Fn) : Set Expr := CallN f f.ty.args.length

/-! ## Generators -/

def lits : Ty → List Expr
  | .int => [.intLit]
  | .str => [.strLit]
  | .bool => [.boolLit]
  | .bv w => [.bvLit w]
  | .other t => [.otherLit t]
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

/-- `E[if x = a then c else 0] = c · Pr(x = a)`. -/
theorem expect_ite_singleton [DecidableEq α] (p : SPMF α) (a : α) (c : ℝ≥0∞) :
    expect p (fun x => if x = a then c else 0) = c * prob p {a} := by
  have : (fun x => if x = a then c else 0) = fun x => c * (if x = a then 1 else 0) := by
    funext x; split <;> simp
  rw [this, SPMF.expect_mul_left, SPMF.expect_ite_eq, SPMF.prob_singleton]

/-! `walk` works on statements about the expectation observation `SPMF.expectObs`. A
probability is the expectation of an indicator, so a bound on a `prob` is a bound on the
observation, and the facts that close the leaves of a walk are bounds on `prob` restated so. -/

theorem prob_eq_obs (p : SPMF α) (E : Set α) :
    prob p E = SPMF.expectObs.spec p (E.indicator 1) := rfl

theorem obs_le_of_prob_le {p : SPMF α} {E : Set α} {B : ℝ≥0∞} (h : prob p E ≤ B) :
    SPMF.expectObs.spec p (E.indicator 1) ≤ B := h

theorem le_obs_of_le_prob {p : SPMF α} {E : Set α} {B : ℝ≥0∞} (h : B ≤ prob p E) :
    B ≤ SPMF.expectObs.spec p (E.indicator 1) := h

/-- The trivial lower bound, for the branches a walk need not count. -/
theorem zero_le_obs (p : SPMF α) (φ : α → ℝ≥0∞) : 0 ≤ SPMF.expectObs.spec p φ := zero_le

theorem div_three_le (x : ℝ≥0∞) : x / 3 ≤ x :=
  ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' (by norm_num))

/-- A product of `|l|` factors, each at least `c`, is at least `c ^ |l|`. -/
theorem pow_le_prod_map {l : List β} {g : β → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a ∈ l, c ≤ g a) :
    c ^ l.length ≤ (l.map g).prod := by
  simpa using List.pow_card_le_prod (l.map g) c (by simpa using h)

/-- A product of `|l|` factors, each at most `c`, is at most `c ^ |l|`. -/
theorem prod_map_le_pow {l : List β} {g : β → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a ∈ l, g a ≤ c) :
    (l.map g).prod ≤ c ^ l.length := by
  simpa using List.prod_le_pow_card (l.map g) c (by simpa using h)

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

/-- **Drawing the arguments of a call.** Starting from a call `g` of `f` with `k` arguments,
drawing one argument per type in `l` and applying `g` to them all gives a call with `k + |l|`
arguments exactly when every draw succeeds: the probability is the product of the draws'
masses. -/
theorem prob_mapM_foldl_app (gen : Ty → SPMF Expr) (f : Fn) :
    ∀ (l : List Ty) (g : Expr) (k : Nat), g ∈ CallN f k →
      prob (do let xs ← l.mapM gen; return xs.foldl .app g) (CallN f (k + l.length))
        = (l.map fun a => mass (gen a)).prod
  | [], g, k, hg => by classical simp [SPMF.prob_pure, hg]
  | a :: l, g, k, hg => by
    have ih := fun x => prob_mapM_foldl_app gen f l (.app g x) (k + 1) ⟨g, x, rfl, hg⟩
    simp only [List.mapM_cons, bind_assoc, pure_bind, List.foldl_cons, List.length_cons,
      List.map_cons, List.prod_cons, show k + (l.length + 1) = k + 1 + l.length by omega]
    rw [SPMF.prob_bind]
    simp only [ih, SPMF.expect_const]

/-- **Pałka et al.'s rule, bounded below.** For an ambient function `f ∈ sig`, the rule (at
`f`'s result type) makes a full call of `f` with probability at least
`Pr(pick f) · Pr(gen a₁ succeeds) ⋯ Pr(gen aₘ succeeds)`. -/
theorem prob_palkaRule_call_ge (gen : Ty → SPMF Expr) {f : Fn} (hmem : f ∈ sig) :
    ((candidates sig f.ty.res).length : ℝ≥0∞)⁻¹ * (f.ty.args.map fun a => mass (gen a)).prod
      ≤ prob (palkaRule sig gen Γ f.ty.res) (CallOf f) := by
  have hc : f ∈ candidates sig f.ty.res := by simp [candidates, hmem]
  have hne : candidates sig f.ty.res ≠ [] := List.ne_nil_of_mem hc
  -- Once `f` is picked, the call is made iff every argument draw succeeds.
  have hcall := prob_mapM_foldl_app gen f f.ty.args (.const f) 0 rfl
  rw [Nat.zero_add] at hcall
  -- `elements` averages over the candidates; keep only the `f` summand.
  unfold palkaRule
  rw [dif_pos hne, SPMF.prob_bind]
  unfold SPMF.prob
  rw [SPMF.expect_elements hne, div_eq_mul_inv, mul_comm]
  gcongr
  rw [← hcall]
  exact List.le_sum_of_mem (List.mem_map_of_mem hc)

end rules

/-! ## The default rule: an upper bound -/

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
    -- No branch produces `c`: the walk averages three zeros.
    unfold genExpr
    rw [prob_eq_obs]
    walk [obs_le_of_prob_le hleaf.le, obs_le_of_prob_le hlam.le,
      obs_le_of_prob_le (prob_appRule_eq_zero genTy (genExpr genTy sig n Γ) τ
        (E := {.const c}) (by simp)).le]
    simp

/-- The bound on a call of a function of type `t` with `k` arguments, at target type `τ`.
With no argument, the constant must have type `τ` exactly. With `k + 1`, the outermost
application rule guesses the last argument's type `σ`, and the remaining call is one with `k`
arguments at type `σ → τ`. -/
noncomputable def callBound (t : Ty) : Nat → Ty → ℝ≥0∞
  | 0, τ => if t = τ then 1 else 0
  | k + 1, τ => expect genTy fun σ => callBound t k (.arrow σ τ)

/-- **Each application rule, bounded.** `genExpr` makes a call of `f` with `k` arguments at type
`τ` with probability at most `callBound genTy f.ty k τ`. The induction is on `k`: one
application rule per argument. -/
theorem genExpr_prob_callN_le (f : Fn) (k : Nat) :
    ∀ n Γ τ, prob (genExpr genTy sig n Γ τ) (CallN f k) ≤ callBound genTy f.ty k τ := by
  induction k with
  | zero => exact fun n Γ τ => genExpr_prob_const_le genTy sig n Γ τ f
  | succ k ih =>
    intro n Γ τ
    have hApp : ∀ e ∈ CallN f (k + 1), ∃ g x, e = .app g x :=
      fun _ ⟨g, x, h, _⟩ => ⟨g, x, h⟩
    cases n with
    | zero =>
      unfold genExpr; rw [prob_genLeaf_app_eq_zero sig Γ hApp]; exact zero_le
    | succ n =>
      -- The application rule: `g x` is a call with `k + 1` arguments iff `g` is one with `k`,
      -- which at the guessed type `σ → τ` is bounded by the induction hypothesis.
      have happ : prob (appRule genTy (genExpr genTy sig n Γ) τ) (CallN f (k + 1))
          ≤ callBound genTy f.ty (k + 1) τ :=
        prob_appRule_le genTy _ _ (CallN f k) (by rintro _ _ ⟨_, _, h, hg⟩; cases h; exact hg)
          _ fun σ => ih n Γ (.arrow σ τ)
      -- The leaf and `λ` branches never produce an application, so the walk leaves
      -- `(0 + 0 + B) / 3 ≤ B`.
      unfold genExpr
      rw [prob_eq_obs]
      walk [obs_le_of_prob_le (prob_genLeaf_app_eq_zero sig Γ hApp).le,
        obs_le_of_prob_le (prob_lamRule_app_eq_zero sig Γ (genExpr genTy sig n) τ hApp).le,
        obs_le_of_prob_le happ]
      simpa using div_three_le _

/-- Peeling the first argument type `a` off the function type costs a factor `Pr(genTy = a)`:
the innermost application rule must guess `a`. -/
theorem callBound_arrow (a t : Ty) (k : Nat) :
    ∀ τ, callBound genTy (.arrow a t) (k + 1) τ = prob genTy {a} * callBound genTy t k τ := by
  induction k with
  | zero =>
    intro τ
    simp only [callBound, Ty.arrow.injEq]
    by_cases hτ : t = τ
    · subst hτ
      simp only [and_true, if_true, mul_one]
      simp_rw [eq_comm (a := a)]
      rw [expect_ite_singleton, one_mul]
    · simp [hτ, SPMF.expect_const]
  | succ k ih =>
    intro τ
    rw [callBound, callBound]
    simp only [ih, SPMF.expect_mul_left]

/-- For a full call, `callBound` is the product of the argument types' probabilities. -/
theorem callBound_full : ∀ t : Ty,
    callBound genTy t t.args.length t.res = (t.args.map fun a => prob genTy {a}).prod
  | .arrow a b => by
    simp only [Ty.args, Ty.res, List.length_cons, callBound_arrow, callBound_full b,
      List.map_cons, List.prod_cons]
  | .int | .str | .bool | .bv _ | .other _ => by simp [Ty.args, Ty.res, callBound]

/-- **The default rule rarely calls an `m`-argument function.** For every type generator, fuel,
and context, `genExpr` produces a full call `f x₁ ⋯ xₘ` of `f : a₁ → ⋯ → aₘ → r` (at type `r`)
with probability at most `Pr(genTy = a₁) ⋯ Pr(genTy = aₘ)`: each of the `m` application rules
must guess an argument type. -/
theorem genExpr_prob_call_le (n : Nat) (Γ : List Ty) (f : Fn) :
    prob (genExpr genTy sig n Γ f.ty.res) (CallOf f)
      ≤ (f.ty.args.map fun a => prob genTy {a}).prod :=
  (genExpr_prob_callN_le genTy sig f _ n Γ _).trans_eq (callBound_full genTy f.ty)

end default

/-! ## Pałka et al.'s rule: a constant lower bound -/

section palka

variable (genTy : SPMF Ty) (sig : List Fn)

/-- Each of `genExprP`'s four branches is taken with probability `1/4`. -/
noncomputable def branchShare : ℝ≥0∞ := 1 / 4

/-- The lower bound for Pałka et al.'s rule on an `m`-argument function, as a product of the
three things that must happen:
* `branchShare`: `genExprP` picks `palkaRule`;
* `|sig|⁻¹`: `palkaRule` picks the function (among at most `|sig|` candidates);
* `branchShare ^ m`: all `m` argument draws succeed (each does, at least through its leaf
  branch). -/
noncomputable def palkaFloor (sig : List Fn) (m : Nat) : ℝ≥0∞ :=
  branchShare * (sig.length : ℝ≥0∞)⁻¹ * branchShare ^ m

theorem palkaFloor_pos (m : Nat) : 0 < palkaFloor sig m := by
  simp [palkaFloor, branchShare, pos_iff_ne_zero]

/-- At a base type, `genExprP` succeeds with probability at least `branchShare` at every fuel:
its leaf branch alone always succeeds. -/
theorem genExprP_mass_ge (n : Nat) (Γ : List Ty) {τ : Ty} (hτ : τ.IsBase) :
    branchShare ≤ mass (genExprP genTy sig n Γ τ) := by
  cases n with
  | zero =>
    unfold genExprP; rw [mass_genLeaf sig Γ hτ.lits_ne_nil, branchShare]; norm_num
  | succ n =>
    have hleaf : 1 ≤ SPMF.expectObs.spec (genLeaf sig Γ τ : SPMF Expr) fun _ => 1 := by
      rw [← SPMF.mass_eq_obs, mass_genLeaf sig Γ hτ.lits_ne_nil]
    -- Keep the leaf branch, drop the other three: the walk leaves `1/4 ≤ (1 + 0 + 0 + 0) / 4`.
    unfold genExprP
    rw [SPMF.mass_eq_obs]
    walk [hleaf, zero_le_obs (lamRule sig (genExprP genTy sig n) Γ τ) fun _ => 1,
      zero_le_obs (appRule genTy (genExprP genTy sig n Γ) τ) fun _ => 1,
      zero_le_obs (palkaRule sig (genExprP genTy sig n Γ) Γ τ) fun _ => 1]
    simp [branchShare]

/-- **Pałka et al.'s rule, exact shape of the bound.** At fuel `n + 1`, a full call of
`f : a₁ → ⋯ → aₘ → r` is made with probability at least
`Pr(pick palkaRule) · Pr(pick f) · Pr(a₁ argument succeeds) ⋯ Pr(aₘ argument succeeds)`. -/
theorem genExprP_prob_call_ge_shape (n : Nat) (Γ : List Ty) {f : Fn} (hmem : f ∈ sig) :
    branchShare * ((candidates sig f.ty.res).length : ℝ≥0∞)⁻¹
        * (f.ty.args.map fun a => mass (genExprP genTy sig n Γ a)).prod
      ≤ prob (genExprP genTy sig (n + 1) Γ f.ty.res) (CallOf f) := by
  -- Only the `palkaRule` branch is counted; the walk leaves
  -- `branchShare · P ≤ (0 + 0 + 0 + P) / 4` for `P` the bound of `prob_palkaRule_call_ge`.
  conv_rhs => unfold genExprP
  rw [prob_eq_obs]
  walk [zero_le_obs (genLeaf sig Γ f.ty.res) ((CallOf f).indicator 1),
    zero_le_obs (lamRule sig (genExprP genTy sig n) Γ f.ty.res) ((CallOf f).indicator 1),
    zero_le_obs (appRule genTy (genExprP genTy sig n Γ) f.ty.res) ((CallOf f).indicator 1),
    le_obs_of_le_prob (prob_palkaRule_call_ge sig Γ (genExprP genTy sig n Γ) hmem)]
  simp [branchShare, div_eq_mul_inv, mul_comm, mul_assoc]

/-- **Pałka et al.'s rule calls an `m`-argument function with constant probability.** For every
type generator, fuel `n + 1`, and context, if `f : a₁ → ⋯ → aₘ → r` is in `sig` and every `aᵢ`
is a base type, then `genExprP` produces a full call `f x₁ ⋯ xₘ` with probability at least
`palkaFloor sig m`, which does not mention `genTy` or `n`. -/
theorem genExprP_prob_call_ge (n : Nat) (Γ : List Ty) {f : Fn} (hmem : f ∈ sig)
    (hargs : ∀ a ∈ f.ty.args, a.IsBase) :
    palkaFloor sig f.ty.args.length ≤ prob (genExprP genTy sig (n + 1) Γ f.ty.res) (CallOf f) := by
  refine le_trans ?_ (genExprP_prob_call_ge_shape genTy sig n Γ hmem)
  unfold palkaFloor
  gcongr
  · exact List.length_filter_le _ _
  · exact pow_le_prod_map fun a ha => genExprP_mass_ge genTy sig n Γ (hargs a ha)

end palka

/-! ## Comparing the two rules -/

section compare

variable (sig : List Fn)

/-- **Conditional comparison.** Whenever `genTy` puts little enough mass on the argument types
`a₁, …, aₘ`, Pałka et al.'s rule calls `f : a₁ → ⋯ → aₘ → r` strictly more often than the
default rule, at the same fuel. -/
theorem default_lt_palka (genTy : SPMF Ty) (n : Nat) (Γ : List Ty) {f : Fn} (hmem : f ∈ sig)
    (hargs : ∀ a ∈ f.ty.args, a.IsBase)
    (hsmall : (f.ty.args.map fun a => prob genTy {a}).prod < palkaFloor sig f.ty.args.length) :
    prob (genExpr genTy sig (n + 1) Γ f.ty.res) (CallOf f)
      < prob (genExprP genTy sig (n + 1) Γ f.ty.res) (CallOf f) :=
  calc prob (genExpr genTy sig (n + 1) Γ f.ty.res) (CallOf f)
      ≤ (f.ty.args.map fun a => prob genTy {a}).prod := genExpr_prob_call_le genTy sig _ Γ f
    _ < palkaFloor sig f.ty.args.length := hsmall
    _ ≤ prob (genExprP genTy sig (n + 1) Γ f.ty.res) (CallOf f) :=
        genExprP_prob_call_ge genTy sig n Γ hmem hargs

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
  refine (SPMF.expect_elements (xs := baseTys numBaseTypes) _ _).trans_le ?_
  rw [div_eq_mul_inv]
  have hlen : (baseTys numBaseTypes).length = numBaseTypes := by simp [baseTys]; omega
  rw [hlen]
  calc _ ≤ 1 * (numBaseTypes : ℝ≥0∞)⁻¹ := by
          gcongr; exact sum_indicator_le_one (baseTys_nodup _) τ
    _ = _ := one_mul _

/-- **The default rule with `k` uniformly drawn base types.** With `k ≥ 2` base types, the
STLC application rule produces a full call of `f : a₁ → ⋯ → aₘ → r` with probability at most
`1 / kᵐ`: it must guess each of the `m` argument types (probability `≤ 1/k` each). -/
theorem genExpr_genTyUniform_prob_call_le (n : Nat) (Γ : List Ty) (f : Fn) {k : Nat}
    (hk : 2 ≤ k) :
    prob (genExpr (genTyUniform k) sig n Γ f.ty.res) (CallOf f)
      ≤ 1 / (k : ℝ≥0∞) ^ f.ty.args.length :=
  calc prob (genExpr (genTyUniform k) sig n Γ f.ty.res) (CallOf f)
      ≤ (f.ty.args.map fun a => prob (genTyUniform k) {a}).prod :=
        genExpr_prob_call_le _ sig n Γ f
    _ ≤ (k : ℝ≥0∞)⁻¹ ^ f.ty.args.length :=
        prod_map_le_pow fun a _ => genTyUniform_prob_le hk a
    _ = 1 / (k : ℝ≥0∞) ^ f.ty.args.length := by rw [one_div, ENNReal.inv_pow]

/-- **Ratio.** With `k ≥ 2` uniformly drawn base types, Pałka et al.'s rule calls
`f : a₁ → ⋯ → aₘ → r` at least `kᵐ · palkaFloor sig m` times as often as the STLC application
rule (stated multiplicatively, so that no probability is divided by). -/
theorem palka_ratio_ge (n : Nat) (Γ : List Ty) {f : Fn} (hmem : f ∈ sig)
    (hargs : ∀ a ∈ f.ty.args, a.IsBase) {k : Nat} (hk : 2 ≤ k) :
    (k : ℝ≥0∞) ^ f.ty.args.length * palkaFloor sig f.ty.args.length
        * prob (genExpr (genTyUniform k) sig (n + 1) Γ f.ty.res) (CallOf f)
      ≤ prob (genExprP (genTyUniform k) sig (n + 1) Γ f.ty.res) (CallOf f) := by
  set m := f.ty.args.length
  have hk0 : ((k : ℝ≥0∞) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : k ≠ 0))
  have hkT : ((k : ℝ≥0∞) ^ m) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  calc (k : ℝ≥0∞) ^ m * palkaFloor sig m
          * prob (genExpr (genTyUniform k) sig (n + 1) Γ f.ty.res) (CallOf f)
      = palkaFloor sig m * ((k : ℝ≥0∞) ^ m
          * prob (genExpr (genTyUniform k) sig (n + 1) Γ f.ty.res) (CallOf f)) := by ring
    -- `kᵐ · Pr_STLC ≤ kᵐ · (1/kᵐ) = 1`.
    _ ≤ palkaFloor sig m * ((k : ℝ≥0∞) ^ m * (1 / (k : ℝ≥0∞) ^ m)) := by
        gcongr; exact genExpr_genTyUniform_prob_call_le sig _ Γ f hk
    _ = palkaFloor sig m := by rw [one_div, ENNReal.mul_inv_cancel hk0 hkT, mul_one]
    _ ≤ prob (genExprP (genTyUniform k) sig (n + 1) Γ f.ty.res) (CallOf f) :=
        genExprP_prob_call_ge _ sig n Γ hmem hargs

/-- **Separation.** As the number of base types grows (`numBaseTypes → ∞`), for an ambient
function `f : a₁ → ⋯ → aₘ → r` with `m ≥ 1` base-typed arguments:
1. the default rule's probability of calling `f` drops below any `ε > 0` for all large enough
   `numBaseTypes` (i.e. it tends to `0`);
2. Pałka et al.'s stays at least `palkaFloor sig m` for every `numBaseTypes`;
3. hence, from some `N` on, Pałka et al.'s rule is strictly more frequent.

(For `m = 0` the "call" is the constant `f` itself, a leaf, and there is nothing to separate.) -/
theorem default_vs_palka_separation (n : Nat) (Γ : List Ty) {f : Fn} (hmem : f ∈ sig)
    (harity : f.ty.args ≠ []) (hargs : ∀ a ∈ f.ty.args, a.IsBase) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ numBaseTypes ≥ N,
        prob (genExpr (genTyUniform numBaseTypes) sig n Γ f.ty.res) (CallOf f) < ε)
      ∧ (∀ numBaseTypes, palkaFloor sig f.ty.args.length ≤
          prob (genExprP (genTyUniform numBaseTypes) sig (n + 1) Γ f.ty.res) (CallOf f))
      ∧ ∃ N, ∀ numBaseTypes ≥ N,
          prob (genExpr (genTyUniform numBaseTypes) sig (n + 1) Γ f.ty.res) (CallOf f)
            < prob (genExprP (genTyUniform numBaseTypes) sig (n + 1) Γ f.ty.res) (CallOf f) := by
  have hm : f.ty.args.length ≠ 0 := by simpa using harity
  -- With `k ≥ 2` base types, the default rule's probability is at most `1/kᵐ ≤ 1/k`.
  have hbound : ∀ j k, 2 ≤ k →
      prob (genExpr (genTyUniform k) sig j Γ f.ty.res) (CallOf f) ≤ (k : ℝ≥0∞)⁻¹ := by
    intro j k hk
    calc prob (genExpr (genTyUniform k) sig j Γ f.ty.res) (CallOf f)
        ≤ 1 / (k : ℝ≥0∞) ^ f.ty.args.length := genExpr_genTyUniform_prob_call_le sig j Γ f hk
      _ ≤ 1 / (k : ℝ≥0∞) := by
          gcongr
          exact_mod_cast Nat.le_self_pow hm k
      _ = (k : ℝ≥0∞)⁻¹ := one_div _
  -- (1): pick `N₀` with `N₀⁻¹ < ε`; for `k ≥ max N₀ 2`, `Pr ≤ k⁻¹ ≤ N₀⁻¹ < ε`.
  have hsmall : ∀ j (ε : ℝ≥0∞), 0 < ε → ∃ N, ∀ k ≥ N,
      prob (genExpr (genTyUniform k) sig j Γ f.ty.res) (CallOf f) < ε := by
    intro j ε hε
    obtain ⟨N₀, hN₀⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine ⟨max N₀ 2, fun k hk => (hbound j k (by omega)).trans_lt ?_⟩
    exact (ENNReal.inv_le_inv.2 (by exact_mod_cast (by omega : N₀ ≤ k))).trans_lt hN₀
  -- (2) is the lower bound.
  have hfloor := fun k => genExprP_prob_call_ge (genTyUniform k) sig n Γ hmem hargs
  -- (3): apply (1) at fuel `n + 1` with `ε := palkaFloor sig m`, which is positive.
  obtain ⟨N, hN⟩ := hsmall (n + 1) _ (palkaFloor_pos sig f.ty.args.length)
  exact ⟨hsmall n, hfloor, N, fun k hk => (hN k hk).trans_le (hfloor k)⟩

/-- The running example: `String.take : String → Int → String`. -/
theorem take_separation (n : Nat) (Γ : List Ty) {take : Fn} (hmem : take ∈ sig)
    (ht : take.ty = takeTy) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ numBaseTypes ≥ N,
        prob (genExpr (genTyUniform numBaseTypes) sig n Γ .str) (CallOf take) < ε)
      ∧ (∀ numBaseTypes, palkaFloor sig 2 ≤
          prob (genExprP (genTyUniform numBaseTypes) sig (n + 1) Γ .str) (CallOf take))
      ∧ ∃ N, ∀ numBaseTypes ≥ N,
          prob (genExpr (genTyUniform numBaseTypes) sig (n + 1) Γ .str) (CallOf take)
            < prob (genExprP (genTyUniform numBaseTypes) sig (n + 1) Γ .str) (CallOf take) := by
  have h := default_vs_palka_separation sig n Γ hmem (by simp [ht, takeTy, Ty.args])
    (by simp [ht, takeTy, Ty.args, Ty.IsBase])
  simpa only [ht, takeTy, Ty.args, Ty.res, List.length_cons, List.length_nil] using h

end compare

end StrataGenerators.AmbientApp
