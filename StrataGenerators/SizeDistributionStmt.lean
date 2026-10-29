import StrataGenerators.SizeDistribution
import StrataGenerators.StmtHasTypeAGen

/-!
# How the size parameter shapes commands and statements

Continues `StrataGenerators.SizeDistribution` (expressions) one level up.

**Commands** (`genCmd`). The size is the expression size of the command's expression.
`genCmd_coverage_threshold`: for a factory with no operator of positive arity, a command never
carries an expression covering all seven forms below size `3`; from size `3` on it does with
probability at least `cmdCoverBound` (`prob_genCmd_covers`, which holds for every factory).

**Statements** (`genStmt`). `genStmt_nesting_threshold`: at size `0` the top level never holds a
`block`, `ite` or `loop`, in every context; at size `n + 1` it holds each of them with positive
probability, each a closed form in the size `n` and the body-length cap `k = maxStmtSeqLen`:
`iteAtSize k = 1/(16 (k+1)²)`, `blockAtSize k = 1/(32 (k+1))`,
`loopAtSize k = 1/(320 (k+1)²)`. Each witness is the empty form of the statement (empty
branches, empty body, nondeterministic guard), so it needs no sub-draw to succeed. Each body length
is uniform on `[0, k]`, and the witness takes it to be `0`, which gives each `1/(k+1)`. A `loop`'s
invariant list has a length uniform on `[0, k]` as well, so none of the three bounds depends on the
size.
`prob_genStmt_covers` lifts the command coverage bound to statements from size `3` on.

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

/-- The expressions a command carries. -/
def cmdExprs : Cmd Expression → List LExpr'
  | .init _ _ (.det e) _ => [e]
  | .set _ (.det e) _ => [e]
  | .assert _ e _ => [e]
  | .assume _ e _ => [e]
  | .cover _ e _ => [e]
  | _ => []

/-- A command covers the fragment when one of its expressions does. -/
def CmdCovers (c : Cmd Expression) : Prop := ∃ e ∈ cmdExprs c, Covers e

variable (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx)

theorem prob_genAssertCmd_covers (ctx : VarCtx) (n : Nat) :
    nameMass * (baseShare * coverBound) ≤
      prob (genAssertCmd (G := SPMF) octx tvars ctx (n + 3) pctx) {r | CmdCovers r.cmd} := by
  rw [nameMass]
  unfold genAssertCmd
  refine le_trans (mul_le_mul' prob_genIdentName_univ le_rfl) (prob_bind_ge Set.univ fun l _ => ?_)
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul'
    (prob_genLExpr_covers_ge _ octx pctx tvars n [] 3 id) le_rfl)
    (prob_bind_ge {e | Covers e} fun e he => ?_))
  refine (prob_pure_of_mem ?_).ge
  exact ⟨e, List.mem_singleton_self _, he⟩

/-- The lower bound on a command carrying a covering expression: the `1`-of-`7` weight of the
`assert` kind, the mass of its label draw, and the covering-expression bound through `genLExpr`. -/
noncomputable def cmdCoverBound : ℝ≥0∞ := 1 / 7 * (nameMass * (baseShare * coverBound))

/-- The share of the `assert` kind in `genCmd.tuned θ` at depth `d`. `genCmd` has two `frequency`
sites: with a writable variable in scope it offers seven kinds (flat offset `0`, `assert` is
branch `4`); without one it offers five (offset `7`, `assert` is branch `2`). -/
noncomputable def assertShare (θ : Tuning) (imm : List (Identifier Unit)) (ctx : VarCtx)
    (d : Nat) : ℝ≥0∞ :=
  if (ctx.writable imm).length > 0 then share θ 0 7 4 d else share θ 7 5 2 d

theorem assertShare_pos (θ : Tuning) (imm : List (Identifier Unit)) (ctx : VarCtx) (d : Nat) :
    0 < assertShare θ imm ctx d := by
  unfold assertShare; split
  · exact share_pos θ 0 7 4 d (by omega)
  · exact share_pos θ 7 5 2 d (by omega)

/-- **A command carries a covering expression, for every tuning of `genCmd`.** From expression
size `3` on, with probability at least the `assert` share of `θ` times the covering-expression
bound. -/
theorem prob_genCmd_covers_tuned (θ : Tuning) (imm : List (Identifier Unit)) (ctx : VarCtx)
    (n : Nat) :
    assertShare θ imm ctx (n + 3) * (nameMass * (baseShare * coverBound)) ≤
      prob (genCmd.tuned (G := SPMF) θ octx tvars imm ctx (n + 3) pctx) {r | CmdCovers r.cmd} := by
  have ha := prob_genAssertCmd_covers octx tvars pctx ctx n
  unfold genCmd.tuned assertShare; dsimp only; split
  · refine le_trans ?_ (prob_frequency_ge _ (Tuning.sum_map_fst_pos _ _ _ _ _) 4 (by simp) _)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    refine mul_le_mul' (le_of_eq ?_) ha
    simp [share, List.range_succ]
  · refine le_trans ?_ (prob_frequency_ge _ (Tuning.sum_map_fst_pos _ _ _ _ _) 2 (by simp) _)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    refine mul_le_mul' (le_of_eq ?_) ha
    simp [share, List.range_succ]

/-- **From expression size `3` on, a command carries a covering expression** with probability at
least `cmdCoverBound`, in every variable context. The case `θ = genCmd.defaults` of
`prob_genCmd_covers_tuned`: the `assert` share is `2/14` or `2/10`, and both are at least `1/7`. -/
theorem prob_genCmd_covers (imm : List (Identifier Unit)) (ctx : VarCtx) (n : Nat) :
    cmdCoverBound ≤
      prob (genCmd (G := SPMF) octx tvars imm ctx (n + 3) pctx) {r | CmdCovers r.cmd} := by
  rw [← genCmd.tuned_defaults (G := SPMF) octx tvars imm ctx (n + 3) pctx, cmdCoverBound]
  refine le_trans ?_ (prob_genCmd_covers_tuned octx tvars pctx genCmd.defaults imm ctx n)
  refine mul_le_mul' ?_ le_rfl
  unfold assertShare; split
  · apply le_of_eq; simp [share, List.range_succ, Tuning.weight, genCmd.defaults]
    rw [inv_eq_one_div, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · simp [share, List.range_succ, Tuning.weight, genCmd.defaults]; ennr

theorem genLExpr_not_covers (hops : ∀ σ, findOpsInCtx octx σ = []) (n : Nat) (hn : n ≤ 2)
    (fc : FVarCtx) (bc : BVarCtx) (τ : LMonoTy) (k : Nat)
    (rc : (LMonoTy → SPMF LExpr') → (LMonoTy → SPMF LExpr')) :
    IsSoundFor (genLExpr (G := SPMF) fc octx [] tvars bc n τ k rc) (fun e => ¬ Covers e) :=
  fun e he => ((prob_eq_zero_iff _ _).mp
    (prob_genLExpr_covers_eq_zero fc octx tvars hops n hn bc τ k rc)) e he

theorem genFreshName_true (ctx : VarCtx) :
    IsSoundFor (_root_.genFreshName (G := SPMF) ctx) (fun _ => True) := fun _ _ => trivial
theorem genIdentName_true : IsSoundFor (genIdentName (G := SPMF)) (fun _ => True) :=
  fun _ _ => trivial

/-- **Below expression size `3`, no command carries a covering expression**, for a factory with no
operator of positive arity and no polymorphic operator. -/
theorem genCmd_not_covers (hops : ∀ σ, findOpsInCtx octx σ = []) (imm : List (Identifier Unit))
    (ctx : VarCtx) (n : Nat) (hn : n ≤ 2) :
    IsSoundFor (genCmd (G := SPMF) octx tvars imm ctx n []) (fun r => ¬ CmdCovers r.cmd) := by
  have hL := genLExpr_not_covers octx tvars hops n hn
  rw [IsSoundFor.iff_obs]
  unfold genCmd genInitDet genInitNondet genSetDet genSetNondet genAssertCmd genAssumeCmd genCoverCmd
  walk [(hL _ _ _ _ _).obs, (genFreshName_true _).obs, (genLMonoTy_true tvars _).obs,
    genIdentName_true.obs]
  all_goals simp_all [CmdCovers, cmdExprs]

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

theorem genFuncDeclStmt_flat :
    IsSoundFor (genFuncDeclStmt (G := SPMF) octx C ctx d pctx) (fun r => ¬ HasNesting r) := by
  intro r hr
  simp only [genFuncDeclStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
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
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr
      simp only [HasNesting, List.mem_append, List.mem_singleton, not_exists, not_and]
      rintro s (hs | rfl)
      · simp only [StrataGenerators.Stmt.initChain, List.mem_map] at hs
        obtain ⟨_, _, rfl⟩ := hs
        simp [IsNesting]
      · simp [IsNesting]
    · simp only [mem_support_bot_iff] at hr

end leaves

/-- **Size 0 gives no nesting statement**, in every context. -/
theorem genStmt_zero_flat (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (k : Nat) :
    IsSoundFor (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx 0 k)
      (fun r => ¬ HasNesting r) := by
  rw [IsSoundFor.iff_obs, genStmt]
  walk [(genCmdStmt_flat octx tvars pctx _ _ _ _).obs, (genExitStmt_flat _ _ _).obs,
    (genFuncDeclStmt_flat octx pctx _ _ _).obs, (genTypeDeclStmt_flat _ _ _).obs,
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
def Top (P : Statement → Prop) : Set GenStmtResult := {r | ∃ s ∈ r.stmts, P s}

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
      ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k) (Top IsIte) := by
  rw [iteAtSize_eq, genStmt]
  refine le_trans ?_ (prob_frequency_ge _ _ 7 (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  refine mul_le_mul' (le_of_eq (by norm_num)) ?_
  have hc := prob_choose_zero k (Nat.zero_le _)
  refine le_trans (mul_le_mul' hc le_rfl) (prob_bind_ge _ fun x hx => ?_)
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Set.mem_setOf_eq] at hx; subst hx
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' hc le_rfl)
    (prob_bind_ge _ fun y hy => ?_))
  obtain ⟨⟨w, hw⟩⟩ := y
  simp only [Set.mem_setOf_eq] at hy; subst hy
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
  simp only [Set.mem_setOf_eq] at hx; subst hx
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
      ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k) (Top IsBlock) := by
  rw [blockAtSize_eq, genStmt]
  refine le_trans ?_ (prob_frequency_ge _ _ 5 (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  refine mul_le_mul' (le_of_eq (by norm_num)) ?_
  have hc := prob_choose_zero k (Nat.zero_le _)
  refine le_trans (mul_le_mul' (prob_genFreshLabel_univ labels) le_rfl)
    (prob_bind_ge Set.univ fun l _ => ?_)
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' hc le_rfl)
    (prob_bind_ge _ fun x hx => ?_))
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Set.mem_setOf_eq] at hx; subst hx
  simp only [genStmtChain_zero, LawfulMonad.pure_bind]
  refine (prob_pure_of_mem ?_).ge
  exact ⟨_, List.mem_singleton_self _, trivial⟩

/-- **From size 1 on, the top level is a `loop` with probability at least `loopAtSize k`**:
a nondeterministic guard, no measure, no invariant, an empty body. -/
theorem prob_genStmt_loop_ge (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (n k : Nat) :
    loopAtSize k
      ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k) (Top IsLoop) := by
  rw [loopAtSize_eq, genStmt]
  refine le_trans ?_ (prob_frequency_ge _ _ 8 (by simp) _)
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
  simp only [Set.mem_setOf_eq] at hx; subst hx
  simp only [genStmtChain_zero, LawfulMonad.pure_bind]
  refine (prob_pure_of_mem ?_).ge
  exact ⟨_, List.mem_singleton_self _, trivial⟩

/-- A top-level statement is a command that carries a covering expression. -/
def IsCoveringCmd : Statement → Prop
  | .cmd (.cmd c) => CmdCovers c
  | _ => False

/-- The lower bound on a command that carries a covering expression: the `1`-of-`7` command kind
and the `6`-of-`16` statement branch, against the covering-expression bound. -/
noncomputable def cmdCoverAtStmt : ℝ≥0∞ := 6 / 16 * cmdCoverBound

/-- **From size 3 on, a statement draw carries a covering expression** with probability at least
`cmdCoverAtStmt`, in every context. -/
theorem prob_genStmt_covers (imm : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (n k : Nat) :
    cmdCoverAtStmt
      ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 3) k)
          (Top IsCoveringCmd) := by
  rw [cmdCoverAtStmt, cmdCoverBound, genStmt]
  refine le_trans ?_ (prob_frequency_ge _ _ 0 (by simp) _)
  simp only [List.getElem_cons_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  refine mul_le_mul' (le_of_eq (by norm_num)) ?_
  unfold genCmdStmt
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans
    (mul_le_mul' (prob_genCmd_covers octx tvars pctx imm ctx n) le_rfl)
    (prob_bind_ge _ fun r hr => ?_))
  refine (prob_pure_of_mem ?_).ge
  exact ⟨_, List.mem_singleton_self _, hr⟩

-- ── Masses, for threading through sequences ─────────────────────────

theorem prob_genFreshName_univ (ctx : VarCtx) :
    nameMass ≤ prob (_root_.genFreshName (G := SPMF) ctx) Set.univ := by
  rw [nameMass]
  unfold _root_.genFreshName
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge prob_genIdentName_univ fun s => ?_)
  split <;> exact (prob_pure_of_mem (Set.mem_univ _)).ge

theorem prob_genCmd_univ (imm : List (Identifier Unit)) (ctx : VarCtx) (d : Nat) :
    1 / 14 * (1 / 2 * (1 / 12)) ≤
      prob (genCmd (G := SPMF) octx tvars imm ctx d pctx) Set.univ := by
  have hi : 1 / 2 * (1 / 12) ≤ prob (genInitNondet (G := SPMF) tvars ctx d) Set.univ := by
    unfold genInitNondet
    refine prob_bind_univ_ge (prob_genFreshName_univ ctx) fun _ => ?_
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
  | 0 => 4 / 10 * (1 / 14 * (1 / 2 * (1 / 12)))
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
      (prob_genCmd_univ octx tvars pctx imm ctx 0) fun _ => (prob_pure_of_mem (Set.mem_univ _)).ge)
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
def TopChain (P : Statement → Prop) : Set (List Statement × LContext CoreLParams × VarCtx) :=
  {t | ∃ s ∈ t.1, P s}

/-- A chain of length `len + 1` inherits a top-level event from its first statement, at the cost
of the mass of the remaining `len` statements. -/
theorem prob_genStmtChain_top_ge (P : Statement → Prop) (imm : List (Identifier Unit))
    (procs : ProcSigCtx) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
    (size len k : Nat) :
    prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx size k) (Top P) *
        stmtMassBound k size ^ len ≤
      prob (genStmtChain (G := SPMF) octx tvars imm procs labels C ctx pctx size (len + 1) k)
        (TopChain P) := by
  rw [genStmtChain]
  refine prob_bind_ge (Top P) fun r hr => ?_
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
    prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx 0 k) (Top IsNesting) = 0 ∧
    ∀ n : Nat,
      (iteAtSize k
          ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k) (Top IsIte) ∧
        blockAtSize k
          ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k)
              (Top IsBlock) ∧
        loopAtSize k
          ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1) k)
              (Top IsLoop))
      ∧ 0 < iteAtSize k ∧ 0 < blockAtSize k ∧ 0 < loopAtSize k :=
  ⟨(prob_eq_zero_iff _ _).mpr fun r hr hn =>
      genStmt_zero_flat octx tvars pctx imm procs labels C ctx k r hr hn,
   fun n => ⟨⟨prob_genStmt_ite_ge octx tvars pctx imm procs labels C ctx n k,
     prob_genStmt_block_ge octx tvars pctx imm procs labels C ctx n k,
     prob_genStmt_loop_ge octx tvars pctx imm procs labels C ctx n k⟩,
     iteAtSize_pos k, blockAtSize_pos k, loopAtSize_pos k⟩⟩

/-- **The command threshold.** For a factory with no operator of positive arity, a command never
carries a covering expression below expression size `3`; from size `3` on it does with
probability at least `coverBound / 140`, and that lower bound holds for every factory. -/
theorem genCmd_coverage_threshold (hops : ∀ σ, findOpsInCtx octx σ = [])
    (imm : List (Identifier Unit)) (ctx : VarCtx) :
    (∀ n ≤ 2, prob (genCmd (G := SPMF) octx tvars imm ctx n []) {r | CmdCovers r.cmd} = 0) ∧
    (∀ n, cmdCoverBound ≤
      prob (genCmd (G := SPMF) octx tvars imm ctx (n + 3) []) {r | CmdCovers r.cmd}) :=
  ⟨fun n hn => (prob_eq_zero_iff _ _).mpr fun r hr hc =>
      genCmd_not_covers octx tvars hops imm ctx n hn r hr hc,
   fun n => prob_genCmd_covers octx tvars [] imm ctx n⟩

end StrataGenerators.SizeDistributionStmt
