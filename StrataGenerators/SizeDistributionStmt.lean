import StrataGenerators.SizeDistribution
import StrataGenerators.StmtHasTypeAGen

/-!
# How the size parameter shapes commands and statements

Continues `StrataGenerators.SizeDistribution` (expressions) one level up.

**Statements** (`genStmt`). `genStmt_nesting_threshold`: at size `0` the top level never holds a
`block`, `ite` or `loop`, in every context; at size `n + 1` it holds each of them with positive
probability, each a closed form in the size `n` and the body-length cap `k = maxStmtSeqLen`:
`iteAtSize k = 1/(16 (k+1)²)`, `blockAtSize k = 1/(32 (k+1))`,
`loopAtSize k = 1/(320 (k+1)²)`. Each witness is the empty form of the statement (empty
branches, empty body, nondeterministic guard), so it needs no sub-draw to succeed. Each body length
is uniform on `[0, k]`, and the witness takes it to be `0`, which gives each `1/(k+1)`. A `loop`'s
invariant list has a length uniform on `[0, k]` as well, so none of the three bounds depends on the
size.

**Sequences.** `stmtMassBound` bounds the mass of one statement at each size, and
`prob_genStmtChain_top_ge` turns an event on the first statement of a chain into an event on the
chain, paying `stmtMassBound size ^ len` for the rest. This is what the procedure and program
results in `StrataGenerators.SizeDistributionProgram` build on.

**The primitive draws.** `genIdentName`, `genFreshName`, `genFreshLabel` and `listOf` are
`partial_fixpoint` definitions whose termination is not proved here. Each still has mass at least
`1/2`, through its terminating branch (`prob_listOf_univ`), and that is all the bounds use.
-/

open Lambda RandomChoice SPMF NNReal ENNReal Core Imperative
open StrataGenerators.SizeDistribution StrataGenerators.Stmt

namespace StrataGenerators.SizeDistributionStmt

-- ── Primitive draws: a guaranteed terminating branch ────────────────

theorem prob_listOf_univ {α} (g : SPMF α) : 1 / 2 ≤ prob (listOf g) Set.univ := by
  rw [listOf]
  simp only [oneOfWith_eq]
  refine le_trans ?_ (prob_oneOf_ge _ _ 0 (by simp) _)
  simp only [List.getElem_cons_zero, List.length_cons, List.length_nil,
    prob_pure_of_mem (Set.mem_univ _)]
  ennr

theorem prob_bind_univ_ge {α β} {x : SPMF α} {f : α → SPMF β} {c d : ℝ≥0∞}
    (hx : c ≤ prob x Set.univ) (hf : ∀ a, d ≤ prob (f a) Set.univ) :
    c * d ≤ prob (x >>= f) Set.univ :=
  le_trans (mul_le_mul' hx le_rfl) (prob_bind_ge Set.univ fun a _ => hf a)

theorem prob_genIdentName_univ : nameMass ≤ prob (genIdentName (G := SPMF)) Set.univ := by
  rw [nameMass]
  unfold genIdentName genStartChar
  refine le_trans (le_of_eq (one_mul _).symm) (prob_bind_univ_ge
    (prob_elements_of_forall _ fun _ _ => trivial).ge fun x => ?_)
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge (prob_listOf_univ _) fun _ => ?_)
  exact (prob_pure_of_mem (Set.mem_univ _)).ge

-- ── Commands ────────────────────────────────────────────────────────


variable (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx)


-- ── Statements: which root forms each size produces ─────────────────

/-- The three statement forms that nest a body. -/
def IsNesting : Statement → Prop
  | .block .. => True
  | .ite .. => True
  | .loop .. => True
  | _ => False

/-- A draw holds a nesting statement at its top level. -/
def HasNesting (r : GenStmtResult) : Prop := ∃ s ∈ r.stmts, IsNesting s

section leaves
variable (imm : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
  (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)

theorem genCmdStmt_flat :
    IsSoundFor (genCmdStmt (G := SPMF) octx tvars imm C ctx d pctx) (fun r => ¬ HasNesting r) := by
  intro r hr
  simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp [HasNesting, IsNesting]

theorem genExitStmt_flat :
    IsSoundFor (genExitStmt (G := SPMF) labels C ctx) (fun r => ¬ HasNesting r) := by
  intro r hr
  cases labels with
  | nil => simp only [genExitStmt, mem_support_bot_iff] at hr
  | cons l ls =>
    simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    simp [HasNesting, IsNesting]

theorem genTypeDeclStmt_flat :
    IsSoundFor (genTypeDeclStmt (G := SPMF) C ctx d) (fun r => ¬ HasNesting r) := by
  intro r hr
  simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
  obtain ⟨_, _, hr⟩ := hr
  split at hr
  · simp only [mem_support_pure_iff] at hr; subst hr; simp [HasNesting, IsNesting]
  · simp only [mem_support_bot_iff] at hr

theorem genCallStmt_flat :
    IsSoundFor (genCallStmt (G := SPMF) octx tvars imm procs C ctx d pctx)
      (fun r => ¬ HasNesting r) := by
  intro r hr
  cases procs with
  | nil => simp only [genCallStmt, mem_support_bot_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff] at hr
    obtain ⟨_, _, _, _, hr⟩ := hr
    split at hr
    · simp only [mem_support_bind_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      split at hr
      · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr
        simp only [HasNesting, List.mem_append, List.mem_singleton, not_exists, not_and]
        rintro s (hs | rfl)
        · simp only [StrataGenerators.Stmt.initChain, List.mem_map] at hs
          obtain ⟨_, _, rfl⟩ := hs
          simp [IsNesting]
        · simp [IsNesting]
      · simp only [mem_support_bot_iff] at hr
    · simp only [mem_support_bot_iff] at hr

end leaves

/-- **Size 0 gives no nesting statement**, in every context. -/
theorem genStmt_zero_flat (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (k : Nat) :
    IsSoundFor (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx 0 k)
      (fun r => ¬ HasNesting r) := by
  rw [IsSoundFor.iff_obs, genStmt]
  walk [(genCmdStmt_flat octx tvars pctx _ _ _ _).obs, (genExitStmt_flat _ _ _).obs,
    (genTypeDeclStmt_flat _ _ _).obs,
    (genCallStmt_flat octx tvars pctx _ _ _ _ _).obs]
  all_goals assumption

def IsIte : Statement → Prop
  | .ite .. => True
  | _ => False
def IsBlock : Statement → Prop
  | .block .. => True
  | _ => False
def IsLoop : Statement → Prop
  | .loop .. => True
  | _ => False

/-- The event that the top level of a draw holds a statement satisfying `P`. -/
def TopLevelEvent (P : Statement → Prop) : Set GenStmtResult := {r | ∃ s ∈ r.stmts, P s}

theorem prob_choose_zero (m : Nat) (h : 0 ≤ m) :
    1 / ((m : ℝ≥0∞) + 1) ≤
      prob (RandomChoice.choose 0 m h : SPMF (ULift {x : Nat // 0 ≤ x ∧ x ≤ m}))
        {x | x.down.val = 0} := by
  refine le_trans ?_ (prob_mono (E := {⟨⟨0, by omega, by omega⟩⟩}) ?_)
  · rw [prob_singleton, choose_apply]
    simp
  · rintro x rfl; rfl

theorem genStmtChain_zero (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (maxStmtSeqLen : Nat) :
    genStmtChain (G := SPMF) octx tvars imm procs labels C ctx pctx size 0 maxStmtSeqLen
      = Pure.pure ([], C, ctx) := by
  rw [genStmtChain]

/-- The lower bound on a top-level `ite` at every size `n + 1`, with body-length cap `k`:
`1 / (16 (k+1)²)`. The `16` is the total branch weight of `genStmt`; each `(k+1)` is the chance that
one of the two branch lengths, uniform on `[0, k]`, comes out `0`. -/
noncomputable def iteAtSize (k : Nat) : ℝ≥0∞ := 1 / (16 * ((k : ℝ≥0∞) + 1) ^ 2)

/-- The lower bound on a top-level `block` at every size `n + 1`, with body-length cap `k`:
`1 / (32 (k+1))`. One body length, and the `1`-of-`16` branch weight against the `1/2` mass of the
fresh label. -/
noncomputable def blockAtSize (k : Nat) : ℝ≥0∞ := 1 / (32 * ((k : ℝ≥0∞) + 1))

/-- The lower bound on a top-level `loop` at every size `n + 1`, with cap `k`:
`1 / (320 (k+1)²)`. The `20` is the guard (`1/5`) and the measure (`1/4`), next to the
`1`-of-`16` weight; one `(k+1)` is the empty invariant list, the other the empty body. -/
noncomputable def loopAtSize (k : Nat) : ℝ≥0∞ := 1 / (320 * ((k : ℝ≥0∞) + 1) ^ 2)

theorem cast_add_one_ne_zero (k : Nat) : ((k : ℝ≥0∞) + 1) ≠ 0 := by
  intro h; rw [add_eq_zero] at h; simp at h

theorem cast_add_one_ne_top (k : Nat) : ((k : ℝ≥0∞) + 1) ≠ ⊤ := by
  simp [ENNReal.add_eq_top]

theorem cast_add_two_ne_zero (n : Nat) : ((n : ℝ≥0∞) + 2) ≠ 0 := by
  intro h; rw [add_eq_zero] at h; simp at h

theorem cast_add_two_ne_top (n : Nat) : ((n : ℝ≥0∞) + 2) ≠ ⊤ := by
  simp [ENNReal.add_eq_top]

/-- Discharge `≠ 0` / `≠ ⊤` for a product of numerals and `(n : ℝ≥0∞) + 2`. -/
macro "fin_ne" : tactic => `(tactic| first | finiteness | positivity | norm_num)

/-- The closed form, unfolded into the nested-product shape the branch-by-branch proof builds. -/
theorem iteAtSize_eq (k : Nat) :
    iteAtSize k = 1 / 16 * (1 / ((k : ℝ≥0∞) + 1) * (1 / ((k : ℝ≥0∞) + 1))) := by
  rw [iteAtSize,
    div_mul_div 1 1 ((k : ℝ≥0∞) + 1) (cast_add_one_ne_zero k) (cast_add_one_ne_top k),
    div_mul_div 1 (1 * 1) (((k : ℝ≥0∞) + 1) * ((k : ℝ≥0∞) + 1)) (by fin_ne) (by fin_ne)]
  frac_eq

theorem blockAtSize_eq (k : Nat) :
    blockAtSize k = 1 / 16 * (1 / 2 * (1 / ((k : ℝ≥0∞) + 1))) := by
  rw [blockAtSize,
    div_mul_div 1 1 ((k : ℝ≥0∞) + 1) (b := 2) (by fin_ne) (by fin_ne),
    div_mul_div 1 (1 * 1) ((2 : ℝ≥0∞) * ((k : ℝ≥0∞) + 1)) (b := 16) (by fin_ne) (by fin_ne)]
  frac_eq

theorem loopAtSize_eq (k : Nat) :
    loopAtSize k = 1 / 16 * (1 / 5 * (1 / 4 * (1 / ((k : ℝ≥0∞) + 1) * (1 / ((k : ℝ≥0∞) + 1))))) := by
  rw [loopAtSize,
    div_mul_div 1 1 ((k : ℝ≥0∞) + 1) (cast_add_one_ne_zero k) (cast_add_one_ne_top k),
    div_mul_div 1 (1 * 1) (((k : ℝ≥0∞) + 1) * ((k : ℝ≥0∞) + 1)) (b := 4) (by fin_ne) (by fin_ne),
    div_mul_div 1 (1 * (1 * 1)) ((4 : ℝ≥0∞) * (((k : ℝ≥0∞) + 1) * ((k : ℝ≥0∞) + 1))) (b := 5)
      (by fin_ne) (by fin_ne),
    div_mul_div 1 (1 * (1 * (1 * 1)))
      ((5 : ℝ≥0∞) * ((4 : ℝ≥0∞) * (((k : ℝ≥0∞) + 1) * ((k : ℝ≥0∞) + 1)))) (b := 16)
      (by fin_ne) (by fin_ne)]
  frac_eq

theorem iteAtSize_pos (k : Nat) : 0 < iteAtSize k := by
  rw [iteAtSize, ENNReal.div_pos_iff]; exact ⟨by norm_num, by finiteness⟩

theorem blockAtSize_pos (k : Nat) : 0 < blockAtSize k := by
  rw [blockAtSize, ENNReal.div_pos_iff]; exact ⟨by norm_num, by finiteness⟩

theorem loopAtSize_pos (k : Nat) : 0 < loopAtSize k := by
  rw [loopAtSize, ENNReal.div_pos_iff]; exact ⟨by norm_num, by finiteness⟩

/-- **From size 1 on, the top level is an `ite` with probability at least `iteAtSize k`.** The
witness is the nondeterministic `ite` with two empty branches, which needs no sub-draw to succeed;
each branch length is uniform on `[0, k]`. The bound does not depend on the size. -/
theorem prob_genStmt_ite_ge (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (n k : Nat) :
    iteAtSize k
      ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k)
          (TopLevelEvent IsIte) := by
  rw [iteAtSize_eq, genStmt]
  refine le_trans ?_ (prob_frequency_ge _ _ 6 (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  refine mul_le_mul' (le_of_eq (by norm_num)) ?_
  have hc := prob_choose_zero k (Nat.zero_le _)
  refine le_trans (mul_le_mul' hc le_rfl) (prob_bind_ge _ fun x hx => ?_)
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Set.mem_ofPred_eq] at hx; subst hx
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' hc le_rfl)
    (prob_bind_ge _ fun y hy => ?_))
  obtain ⟨⟨w, hw⟩⟩ := y
  simp only [Set.mem_ofPred_eq] at hy; subst hy
  simp only [genStmtChain_zero, LawfulMonad.pure_bind]
  refine (prob_pure_of_mem ?_).ge
  exact ⟨_, List.mem_singleton_self _, trivial⟩

theorem prob_genFreshLabel_univ (labels : List String) :
    nameMass ≤ prob (genFreshLabel (G := SPMF) labels) Set.univ := by
  rw [nameMass]
  unfold genFreshLabel
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge prob_genIdentName_univ fun s => ?_)
  split <;> exact (prob_pure_of_mem (Set.mem_univ _)).ge

theorem prob_genCondOrNondet_univ (ctx : VarCtx) (d : Nat) :
    1 / 5 ≤ prob (genCondOrNondet (G := SPMF) octx tvars ctx d pctx) Set.univ := by
  unfold genCondOrNondet
  refine le_trans ?_ (prob_frequency_ge _ _ 0 (by simp) _)
  simp only [List.getElem_cons_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    prob_pure_of_mem (Set.mem_univ _)]
  ennr

theorem prob_genOptMeasure_univ (ctx : VarCtx) (d : Nat) :
    1 / 4 ≤ prob (genOptMeasure (G := SPMF) octx tvars ctx d pctx) Set.univ := by
  unfold genOptMeasure biasedOptionGen
  refine le_trans ?_ (prob_bind_ge {false} (d := 1) fun b hb => ?_)
  · rw [mul_one, prob_singleton, coin_apply_false (by norm_num) (by norm_num)]
    have h34 : (3 / 4 : ℚ) = (3 : ℤ) / (4 : ℤ) := by norm_num
    have hd : (3 / 4 : ℚ).den = 4 := by
      have := Rat.den_div_eq_of_coprime (a := 3) (b := 4) (by norm_num) (by decide)
      rw [h34]; exact_mod_cast this
    have hn : (3 / 4 : ℚ).num = 3 := by
      rw [h34, Rat.num_div_eq_of_coprime (by norm_num) (by decide)]
    rw [hd, hn, show Int.toNat 3 = 3 from rfl]
    norm_num
  · rw [Set.mem_singleton_iff.mp hb]
    exact (prob_pure_of_mem (Set.mem_univ _)).ge

theorem prob_listOfMaxLength_univ {α} (m : Nat) (g : SPMF α) :
    1 / ((m : ℝ≥0∞) + 1) ≤ prob (listOfMaxLength m g) Set.univ := by
  unfold listOfMaxLength
  rw [map_eq_pure_bind, LawfulMonad.bind_assoc]
  refine le_trans (le_of_eq (mul_one _).symm)
    (le_trans (mul_le_mul' (prob_choose_zero m (Nat.zero_le _)) le_rfl)
      (prob_bind_ge _ fun x hx => ?_))
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Set.mem_ofPred_eq] at hx; subst hx
  simp only [LawfulMonad.pure_bind, vectorOf, List.replicate, List.foldr]
  exact (prob_pure_of_mem (Set.mem_univ _)).ge

theorem prob_genInvariants_univ (ctx : VarCtx) (m d : Nat) :
    1 / ((m : ℝ≥0∞) + 1) ≤ prob (genInvariants (G := SPMF) octx tvars ctx m d pctx) Set.univ := by
  unfold genInvariants; exact prob_listOfMaxLength_univ _ _

/-- **From size 1 on, the top level is a `block` with probability at least `blockAtSize k`**:
an empty block, under a label from `genFreshLabel`. -/
theorem prob_genStmt_block_ge (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (n k : Nat) :
    blockAtSize k
      ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k)
          (TopLevelEvent IsBlock) := by
  rw [blockAtSize_eq, genStmt]
  refine le_trans ?_ (prob_frequency_ge _ _ 4 (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  refine mul_le_mul' (le_of_eq (by norm_num)) ?_
  have hc := prob_choose_zero k (Nat.zero_le _)
  refine le_trans (mul_le_mul' (prob_genFreshLabel_univ labels) le_rfl)
    (prob_bind_ge Set.univ fun l _ => ?_)
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' hc le_rfl)
    (prob_bind_ge _ fun x hx => ?_))
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Set.mem_ofPred_eq] at hx; subst hx
  simp only [genStmtChain_zero, LawfulMonad.pure_bind]
  refine (prob_pure_of_mem ?_).ge
  exact ⟨_, List.mem_singleton_self _, trivial⟩

/-- **From size 1 on, the top level is a `loop` with probability at least `loopAtSize k`**:
a nondeterministic guard, no measure, no invariant, an empty body. -/
theorem prob_genStmt_loop_ge (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (n k : Nat) :
    loopAtSize k
      ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k)
          (TopLevelEvent IsLoop) := by
  rw [loopAtSize_eq, genStmt]
  refine le_trans ?_ (prob_frequency_ge _ _ 7 (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  refine mul_le_mul' (le_of_eq (by norm_num)) ?_
  have hc := prob_choose_zero k (Nat.zero_le _)
  have hi := prob_genInvariants_univ octx tvars pctx ctx k (n + 1)
  refine le_trans (mul_le_mul' (prob_genCondOrNondet_univ octx tvars pctx ctx _) le_rfl)
    (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (mul_le_mul' (prob_genOptMeasure_univ octx tvars pctx ctx _) le_rfl)
    (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (mul_le_mul' hi le_rfl) (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' hc le_rfl)
    (prob_bind_ge _ fun x hx => ?_))
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Set.mem_ofPred_eq] at hx; subst hx
  simp only [genStmtChain_zero, LawfulMonad.pure_bind]
  refine (prob_pure_of_mem ?_).ge
  exact ⟨_, List.mem_singleton_self _, trivial⟩


-- ── Masses, for threading through sequences ─────────────────────────

theorem prob_genFreshName_univ (ctx : VarCtx) (avoid : List String := []) :
    nameMass ≤ prob (_root_.genFreshName (G := SPMF) ctx avoid) Set.univ := by
  rw [nameMass]
  unfold _root_.genFreshName
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge prob_genIdentName_univ fun s => ?_)
  split <;> exact (prob_pure_of_mem (Set.mem_univ _)).ge

theorem prob_genCmd_univ (imm : List (Identifier Unit)) (ctx : VarCtx) (d : Nat)
    (avoid : List String := []) (kt : Lambda.KnownTypes := Core.KnownTypes) :
    1 / 14 * (1 / 2 * (1 / 12)) ≤
      prob (genCmd (G := SPMF) octx tvars imm ctx d pctx avoid kt) Set.univ := by
  have hi : 1 / 2 * (1 / 12) ≤ prob (genInitNondet (G := SPMF) tvars ctx d avoid) Set.univ := by
    unfold genInitNondet
    refine prob_bind_univ_ge (prob_genFreshName_univ ctx avoid) fun _ => ?_
    refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul'
      (le_trans (prob_genLMonoTy_bool tvars d) (prob_mono (Set.subset_univ _))) le_rfl)
      (prob_bind_ge Set.univ fun _ _ => (prob_pure_of_mem (Set.mem_univ _)).ge))
  unfold genCmd; dsimp only; split
  · refine le_trans ?_ (prob_frequency_ge _ _ 1 (by simp) _)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    exact mul_le_mul' (by ennr) hi
  · refine le_trans ?_ (prob_frequency_ge _ _ 1 (by simp) _)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    exact mul_le_mul' (by ennr) hi

/-- A size-indexed lower bound on the mass of `genStmt` with body-length cap `k`. At size 0 it is
the command branch; above, the empty nondeterministic `ite`. -/
noncomputable def stmtMassBound (k : Nat) : Nat → ℝ≥0∞
  | 0 => 4 / 9 * (1 / 14 * (1 / 2 * (1 / 12)))
  | _ + 1 => iteAtSize k

theorem prob_genStmt_univ (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (n k : Nat) :
    stmtMassBound k n ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx n k)
      Set.univ := by
  cases n with
  | zero =>
    rw [genStmt]
    refine le_trans ?_ (prob_frequency_ge _ _ 0 (by simp) _)
    simp only [List.getElem_cons_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    refine mul_le_mul' (le_of_eq (by norm_num)) ?_
    unfold genCmdStmt
    exact le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge
      (prob_genCmd_univ octx tvars pctx imm ctx 0 _ _) fun _ => (prob_pure_of_mem (Set.mem_univ _)).ge)
  | succ n =>
    exact le_trans (prob_genStmt_ite_ge octx tvars pctx imm procs labels C ctx n k)
      (prob_mono (Set.subset_univ _))

theorem prob_genStmtChain_univ (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (size : Nat) :
    ∀ (len k : Nat) (C : LContext CoreLParams) (ctx : VarCtx),
      stmtMassBound k size ^ len ≤
        prob (genStmtChain (G := SPMF) octx tvars imm procs labels C ctx pctx size len k)
          Set.univ := by
  intro len
  induction len with
  | zero => intro k C ctx; rw [genStmtChain_zero, pow_zero]; exact (prob_pure_of_mem (Set.mem_univ _)).ge
  | succ len ih =>
    intro k C ctx
    rw [genStmtChain, pow_succ, mul_comm]
    refine prob_bind_univ_ge (prob_genStmt_univ octx tvars pctx imm procs labels C ctx size k)
      fun r => ?_
    refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge (ih _ _ _) fun _ => ?_)
    exact (prob_pure_of_mem (Set.mem_univ _)).ge

/-- The event that a statement chain holds, at its top level, a statement satisfying `P`. -/
def TopLevelEventChain (P : Statement → Prop) :
    Set (List Statement × LContext CoreLParams × VarCtx) :=
  {t | ∃ s ∈ t.1, P s}

/-- A chain of length `len + 1` inherits a top-level event from its first statement, at the cost
of the mass of the remaining `len` statements. -/
theorem prob_genStmtChain_top_ge (P : Statement → Prop) (imm : List (Identifier Unit))
    (procs : ProcSigCtx) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
    (size len k : Nat) :
    prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx size k) (TopLevelEvent P) *
        stmtMassBound k size ^ len ≤
      prob (genStmtChain (G := SPMF) octx tvars imm procs labels C ctx pctx size (len + 1) k)
        (TopLevelEventChain P) := by
  rw [genStmtChain]
  refine prob_bind_ge (TopLevelEvent P) fun r hr => ?_
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul'
    (prob_genStmtChain_univ octx tvars pctx imm procs labels size len k _ _) le_rfl)
    (prob_bind_ge Set.univ fun t _ => ?_))
  refine (prob_pure_of_mem ?_).ge
  obtain ⟨s, hs, hP⟩ := hr
  exact ⟨s, List.mem_append_left _ hs, hP⟩

/-- **A size-0 chain has no nesting statement at its top level.** -/
theorem genStmtChain_zero_flat (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) :
    ∀ (len k : Nat) (C : LContext CoreLParams) (ctx : VarCtx),
      IsSoundFor (genStmtChain (G := SPMF) octx tvars imm procs labels C ctx pctx 0 len k)
        (fun t => ∀ s ∈ t.1, ¬ IsNesting s) := by
  intro len
  induction len with
  | zero =>
    intro k C ctx t ht
    rw [genStmtChain_zero, mem_support_pure_iff] at ht
    subst ht; simp
  | succ len ih =>
    intro k C ctx t ht
    rw [genStmtChain] at ht
    simp only [mem_support_bind_iff, mem_support_pure_iff] at ht
    obtain ⟨r, hr, ⟨rest, C'', ctx''⟩, hrest, rfl⟩ := ht
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact fun hn => genStmt_zero_flat octx tvars pctx imm procs labels C ctx k r hr ⟨s, hs, hn⟩
    · exact ih _ _ _ _ hrest s hs

/-- **The statement threshold.** At size `0` a statement draw never has a `block`, `ite` or
`loop` at its top level; at every size `n + 1` it has each of them with positive probability, for
every body-length cap `k`. -/
theorem genStmt_nesting_threshold (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (k : Nat) :
    prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx 0 k)
        (TopLevelEvent IsNesting) = 0 ∧
    ∀ n : Nat,
      (iteAtSize k
          ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k)
              (TopLevelEvent IsIte) ∧
        blockAtSize k
          ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k)
              (TopLevelEvent IsBlock) ∧
        loopAtSize k
          ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k)
              (TopLevelEvent IsLoop))
      ∧ 0 < iteAtSize k ∧ 0 < blockAtSize k ∧ 0 < loopAtSize k :=
  ⟨(prob_eq_zero_iff _ _).mpr fun r hr hn =>
      genStmt_zero_flat octx tvars pctx imm procs labels C ctx k r hr hn,
   fun n => ⟨⟨prob_genStmt_ite_ge octx tvars pctx imm procs labels C ctx n k,
     prob_genStmt_block_ge octx tvars pctx imm procs labels C ctx n k,
     prob_genStmt_loop_ge octx tvars pctx imm procs labels C ctx n k⟩,
     iteAtSize_pos k, blockAtSize_pos k, loopAtSize_pos k⟩⟩


end StrataGenerators.SizeDistributionStmt
