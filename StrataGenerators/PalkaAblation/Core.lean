import StrataGenerators.PalkaAblation.Bounds
import Mathlib.Data.NNRat.Order
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.NNReal.Basic

/-!
# The ablation over Strata Core's factory

`Bounds.lean` bounds, for an arbitrary operator context, how often `genLExprBase` makes a full
call of an operator with and without its Indir and IndirPoly branches (Pałka et al.'s rules for
applying a factory operator; `genAppArgTy`'s context-directed type guess is kept). Here the context is `coreMonoOps`
(every function of `Core.Factory`), and the two bounds are compared, function by function, by
computation.

`coreCalls` lists the 356 operators of `coreMonoOps` with at least one argument (73 with one, 276
with two, 7 with three; 22 of them are polymorphic entries such as `select` or `Set.insert`). For
each, `check` computes in `ℚ≥0`
* `ablatedBoundQ`: the upper bound on the ablated generator `genLExprBaseW … 0 0`, and
* `palkaBoundQ`: the lower bound on `genLExprBase`,
and checks the side conditions: `name` is an Indir candidate at its result type, and an operator
at no other type.

* `core_ablation`: for every call that passes (`separatedCalls`), at every depth `n + 1` and in
  every context, **`genLExprBase` makes the call strictly more often than the same generator
  without its Indir and IndirPoly branches.**
* `separatedCalls_length`: 240 calls pass: all 4 monomorphic three-argument functions and 236 of
  the 259 monomorphic two-argument ones. The bounds cannot decide the rest, which does not show
  that Pałka et al.'s rule loses there:
  - one-argument functions: one application rule needs one argument-type guess, and the bound
    charges the guess nothing (`γ = 1`);
  - `bool`-returning comparisons (`Int.Lt`, `Bool.And`, `Str.Contains`, …): the Indir rule
    chooses among 123 candidates that return `bool`, which offsets its advantage under these
    bounds;
  - polymorphic entries: there is no proven mass floor for `Map`, `Sequence` or type-variable
    arguments.
* `core_genLExpr_below_arity` (262 calls, `belowArityCalls`): for every depth `d` below the arity,
  the ablated generator makes the call with probability `0` and `genLExpr` with positive
  probability.

**Axioms.** `core_ablation` and `core_genLExpr_below_arity` use no `native_decide`: membership in
`separatedCalls` / `belowArityCalls` is a hypothesis, discharged by the check's own definition. They
depend only on the standard axioms and on the `native_decide` axioms that `Core.Factory` already
carries (its `name_nodup` field). Only the three counting theorems (`coreCalls_length`,
`separatedCalls_length`, `belowArityCalls_length`) use `native_decide` themselves; each use adds its
own auxiliary axiom of the same kind (trust in the compiled evaluator).
-/

namespace StrataGenerators.PalkaAblation

open Lambda
open scoped ENNReal NNRat NNReal
open SPMF (prob)

/-! ## Rationals as extended reals -/

/-- A nonnegative rational, as an extended real. -/
noncomputable def qe (q : ℚ≥0) : ℝ≥0∞ := ((q : ℝ≥0) : ℝ≥0∞)

theorem qe_mul (p q : ℚ≥0) : qe (p * q) = qe p * qe q := by
  simp [qe, NNRat.cast_mul, ENNReal.coe_mul]

theorem qe_natDiv (a b : ℕ) (hb : b ≠ 0) : qe ((a : ℚ≥0) / b) = (a : ℝ≥0∞) / b := by
  have : ((b : ℝ≥0)) ≠ 0 := by exact_mod_cast hb
  simp [qe, NNRat.cast_div, ENNReal.coe_div this]

theorem qe_lt {p q : ℚ≥0} (h : p < q) : qe p < qe q :=
  ENNReal.coe_lt_coe.2 (NNRat.cast_lt.2 h)

theorem qe_prod {α : Type} (l : List α) (g : α → ℚ≥0) :
    (l.map fun a => qe (g a)).prod = qe (l.map g).prod := by
  induction l with
  | nil => simp [qe]
  | cons a l ih => simp [List.map_cons, List.prod_cons, ih, qe_mul]

/-! ## The factors, in `ℚ≥0` -/

/-- `appShare` in `ℚ≥0`. -/
def appShareQ (τ : LMonoTy) : ℚ≥0 := if isArrow τ then 1 / 13 else 1 / 9

theorem appShare_eq (τ : LMonoTy) : appShare τ = qe (appShareQ τ) := by
  unfold appShare appShareQ
  split
  · rw [show (1 : ℚ≥0) / 13 = ((1 : ℕ) : ℚ≥0) / ((13 : ℕ) : ℚ≥0) by norm_num,
      qe_natDiv _ _ (by norm_num)]; norm_num
  · rw [show (1 : ℚ≥0) / 9 = ((1 : ℕ) : ℚ≥0) / ((9 : ℕ) : ℚ≥0) by norm_num,
      qe_natDiv _ _ (by norm_num)]; norm_num

/-- `massFloor` in `ℚ≥0`. -/
def massFloorQ (octx : OpCtx) : LMonoTy → ℚ≥0
  | .tcons "bool" [] => 7 / 24
  | .tcons "int" [] => 7 / 18
  | .tcons "string" [] => 7 / 18
  | .tcons "real" [] => 7 / 18
  | .bitvec _ => 7 / 18
  | .tcons "regex" [] => if (opsOfType octx .regex).length > 0 then 4 / 17 else 0
  | _ => 0

-- `norm_num` is needed in some of the seven cases and not others; the linter reports it per case.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem massFloor_eq (octx : OpCtx) (τ : LMonoTy) : massFloor octx τ = qe (massFloorQ octx τ) := by
  unfold massFloor massFloorQ
  split
  all_goals first
    | (simp only [qe]; norm_num; done)
    | (split <;> simp [qe] <;> norm_num)

/-- The ablated generator's bound (`offChain` with `γ = 1`), in `ℚ≥0`. -/
def offChainQ (ps : ℚ≥0) (r : LMonoTy) (as : List LMonoTy) : Nat → ℚ≥0
  | 0 => 1 / 3 * ps
  | k + 1 => appShareQ (tyAfter r as (k + 1)) * 1 * offChainQ ps r as k

theorem offChain_eq (ps : ℚ≥0) (r : LMonoTy) (as : List LMonoTy) (k : Nat) :
    offChain (fun _ _ => 1) (qe ps) r as k = qe (offChainQ ps r as k) := by
  induction k with
  | zero =>
    simp only [offChain, offChainQ, qe_mul]
    congr 1
    rw [show (1 : ℚ≥0) / 3 = ((1 : ℕ) : ℚ≥0) / ((3 : ℕ) : ℚ≥0) by norm_num,
      qe_natDiv _ _ (by norm_num)]; norm_num
  | succ k ih =>
    simp only [offChain, offChainQ, qe_mul, ih, appShare_eq]
    simp [qe]

/-! ## The check -/

/-- An operator call: its name, argument types, and result type. -/
abbrev Call := String × List LMonoTy × LMonoTy

/-- Every operator of `coreMonoOps` with at least one argument. -/
def coreCalls : List Call :=
  coreMonoOps.ops.filterMap fun (name, ty) =>
    match decomposeArrow ty with
    | ([], _) => none
    | (as, r) => some (name, as, r)

/-- The share of `name` among the operators of its own type, in `ℚ≥0`. -/
def pickShareQ (octx : OpCtx) (name : String) (σ : LMonoTy) : ℚ≥0 :=
  ((opsOfTypeList octx.ops σ).count name : ℚ≥0) / (opsOfTypeList octx.ops σ).length

/-- The upper bound on the ablated generator. -/
def ablatedBoundQ (octx : OpCtx) (c : Call) : ℚ≥0 :=
  offChainQ (pickShareQ octx c.1 (LMonoTy.mkArrow' c.2.2 c.2.1)) c.2.2 c.2.1 c.2.1.length

/-- The lower bound on `genLExprBase`. -/
def palkaBoundQ (octx : OpCtx) (c : Call) : ℚ≥0 :=
  4 / 24 * (1 / ((findOpsInCtx octx c.2.2).length : ℚ≥0) * (c.2.1.map (massFloorQ octx)).prod)

/-- The side conditions, and the comparison. -/
def check (octx : OpCtx) (c : Call) : Bool :=
  (c.1, c.2.1) ∈ findOpsInCtx octx c.2.2
    && c.2.1 != []
    && octx.ops.all (fun p => p.1 != c.1 || p.2 == LMonoTy.mkArrow' c.2.2 c.2.1)
    && decide (ablatedBoundQ octx c < palkaBoundQ octx c)

/-- The calls the computation separates. -/
def separatedCalls : List Call := coreCalls.filter (check coreMonoOps)

theorem coreCalls_length : coreCalls.length = 356 := by native_decide

theorem separatedCalls_length : separatedCalls.length = 240 := by native_decide

/-! ## Soundness of the check -/

theorem pickShare_eq_zero (octx : OpCtx) (name : String) (fty σ : LMonoTy) (hne : σ ≠ fty)
    (hall : octx.ops.all (fun p => p.1 != name || p.2 == fty) = true) :
    pickShare octx name σ = 0 := by
  unfold pickShare
  rw [opsOfType_eq_scan]
  have : (opsOfTypeList octx.ops σ).count name = 0 := by
    rw [List.count_eq_zero]
    intro hmem
    simp only [opsOfTypeList, List.mem_filterMap] at hmem
    obtain ⟨⟨x, ty⟩, hx, h⟩ := hmem
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rename_i hty
      have := List.all_eq_true.1 hall _ hx
      simp_all
    · simp at h
  simp [this]

theorem pickShare_eq (octx : OpCtx) (name : String) (σ : LMonoTy)
    (hpos : 0 < (opsOfTypeList octx.ops σ).length) :
    pickShare octx name σ = qe (pickShareQ octx name σ) := by
  unfold pickShare pickShareQ
  rw [opsOfType_eq_scan, qe_natDiv _ _ (by omega)]

/-- **The ablation, over Core's factory.** For every call that `check` separates, at every depth
`n + 1` and in every context, `genLExprBase` makes it strictly more often than the same generator
without its Indir and IndirPoly branches (`genLExprBaseW … 0 0`, which `genLExprBaseW_eq` pins to
`genLExprBase` at weights `4 4`). -/
theorem core_ablation (fctx : FVarCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat) {c : Call} (hc : c ∈ separatedCalls) :
    prob (genLExprBaseW (G := SPMF) fctx coreMonoOps pctx tvars 0 0 bctx (n + 1) c.2.2)
        (OpCall c.1 c.2.1.length)
      < prob (genLExprBase (G := SPMF) fctx coreMonoOps pctx tvars bctx (n + 1) c.2.2)
          (OpCall c.1 c.2.1.length) := by
  obtain ⟨name, as, r⟩ := c
  have hchk := (List.mem_filter.1 hc).2
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hmem, hne⟩, hall⟩, hlt⟩ := hchk
  have hmem' : (name, as) ∈ findOpsInCtx coreMonoOps r := by simpa using hmem
  have hne' : as ≠ [] := by simpa using hne
  -- `name` is an operator of its own type, so the `pickOp` list at that type is nonempty.
  have hpos : 0 < (opsOfTypeList coreMonoOps.ops (LMonoTy.mkArrow' r as)).length := by
    simp only [findOpsInCtx, List.mem_filterMap] at hmem'
    obtain ⟨⟨x, ty⟩, hx, h⟩ := hmem'
    have hxname : x = name := by split at h <;> simp_all
    subst hxname
    have hty : ty = LMonoTy.mkArrow' r as := by
      have := List.all_eq_true.1 hall _ hx; simpa using this
    subst hty
    refine List.length_pos_iff.2 (List.ne_nil_of_mem (a := x) ?_)
    simp only [opsOfTypeList, List.mem_filterMap]
    exact ⟨_, hx, by simp⟩
  have hoff := (off_call_le fctx coreMonoOps pctx tvars bctx name r as hne'
    (fun σ h => pickShare_eq_zero _ _ _ _ h hall) (fun _ _ => 1)
    (fun _ _ _ => (SPMF.prob_le_mass _ _).trans (SPMF.mass_le_one _)) as.length le_rfl).2.2 (n + 1)
  simp only [tyAfter, List.drop_length, LMonoTy.mkArrow'_nil] at hoff
  rw [pickShare_eq _ _ _ hpos, offChain_eq] at hoff
  have hF : (findOpsInCtx coreMonoOps r).length ≠ 0 :=
    (List.length_pos_iff.2 (List.ne_nil_of_mem hmem')).ne'
  calc prob (genLExprBaseW (G := SPMF) fctx coreMonoOps pctx tvars 0 0 bctx (n + 1) r)
        (OpCall name as.length)
      ≤ qe (ablatedBoundQ coreMonoOps (name, as, r)) := hoff
    _ < qe (palkaBoundQ coreMonoOps (name, as, r)) := qe_lt hlt
    _ = ((4 : ℕ) : ℝ≥0∞) / 24 * (((findOpsInCtx coreMonoOps r).length : ℝ≥0∞)⁻¹
          * (as.map (massFloor coreMonoOps)).prod) := by
        simp only [palkaBoundQ, qe_mul]
        rw [show (4 : ℚ≥0) / 24 = ((4 : ℕ) : ℚ≥0) / ((24 : ℕ) : ℚ≥0) by norm_num,
          qe_natDiv _ _ (by norm_num), show (1 : ℚ≥0) = ((1 : ℕ) : ℚ≥0) by norm_num,
          qe_natDiv _ _ hF, ← qe_prod]
        simp only [Nat.cast_one, one_div, Nat.cast_ofNat]
        rw [show (fun a => qe (massFloorQ coreMonoOps a)) = massFloor coreMonoOps from
          funext fun a => (massFloor_eq _ a).symm]
    _ ≤ _ := on_call_ge fctx coreMonoOps pctx tvars bctx n hmem'

/-! ## `genLExpr`, below the arity -/

/-- The calls with at least two arguments, all of a type with a proven positive mass floor, that
are Indir candidates. -/
def checkBelowArity (octx : OpCtx) (c : Call) : Bool :=
  (c.1, c.2.1) ∈ findOpsInCtx octx c.2.2 && decide (2 ≤ c.2.1.length)
    && c.2.1.all (fun a => decide (0 < massFloorQ octx a))

def belowArityCalls : List Call := coreCalls.filter (checkBelowArity coreMonoOps)

theorem belowArityCalls_length : belowArityCalls.length = 262 := by native_decide

theorem massFloor_pos {octx : OpCtx} {a : LMonoTy} (h : 0 < massFloorQ octx a) :
    0 < massFloor octx a := by
  rw [massFloor_eq]
  exact ENNReal.coe_pos.2 (by exact_mod_cast h)

/-- **Below its arity, only the Indir rules make the call.** For a call with `m ≥ 2`
arguments and every depth `d < m`, the ablated generator never makes it, while `genLExpr` makes it with positive probability. -/
theorem core_genLExpr_below_arity (fctx : FVarCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) {c : Call} (hc : c ∈ belowArityCalls) {d : Nat} (hd : d < c.2.1.length) :
    prob (genLExprBaseW (G := SPMF) fctx coreMonoOps pctx tvars 0 0 bctx d c.2.2)
        (OpCall c.1 c.2.1.length) = 0
      ∧ 0 < prob (genLExpr (G := SPMF) fctx coreMonoOps pctx tvars bctx d c.2.2)
          (OpCall c.1 c.2.1.length) := by
  obtain ⟨name, as, r⟩ := c
  have hchk := (List.mem_filter.1 hc).2
  simp only [checkBelowArity, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨hmem, h2⟩, hpos⟩ := hchk
  have hmem' : (name, as) ∈ findOpsInCtx coreMonoOps r := by simpa using hmem
  refine ⟨off_eq_zero_of_lt fctx coreMonoOps pctx tvars bctx name _ _ _ hd (by omega), ?_⟩
  refine lt_of_lt_of_le ?_ (genLExpr_call_ge fctx coreMonoOps pctx tvars bctx d hmem')
  refine ENNReal.mul_pos (by norm_num) (ENNReal.mul_pos (ENNReal.inv_ne_zero.2
    (ENNReal.natCast_ne_top _)) ?_).ne'
  refine List.prod_ne_zero fun h0 => ?_
  obtain ⟨a, ha, h⟩ := List.mem_map.1 h0
  exact (ENNReal.mul_pos (by norm_num) (massFloor_pos (hpos a ha)).ne').ne' h

end StrataGenerators.PalkaAblation
