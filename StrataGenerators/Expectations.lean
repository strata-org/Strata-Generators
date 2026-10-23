import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.HasTypeAGen.IndirSupport

/-!
# Expectations and coverage probabilities for the statement generator

The support proofs in this package read a generator as an `SPMF` and speak only about
`SPMF.support` — which draws are *possible*. This module reads the same generator as a measure and
speaks about `SPMF.expect` and `SPMF.prob` — how *often* a draw has a feature.

Three results.

**(1) The expected loop count.** `genStmt_expect_numLoops_le`: the expected number of `loop`
statements in a draw of `genStmt … size`, at every nesting depth, is at most `loopBound size`, where

```
loopBound 0       = 0
loopBound (n + 1) = 2/17 + (5 * (n+1) / 17) * loopBound n
```

Both constants come off `genStmt`'s `frequency` list: `2/17` is the `loop` branch's weight share,
and the four nesting branches feed `5 * (n+1)` mean bodies into the total weight of `17` — `5`
because `block` takes one body, each `ite` two, and `loop` one, and `(n+1)/2` because a body's
length is `choose 0 (size+1)`. The multiplier exceeds `1` from `n = 3`, so the bound grows faster
than any exponential in `size`.

**(2) Factory operators in an expression.** At a position whose type is headed by a declared type
constructor (`IsDeclaredTyShaped`), `genLExprBase_prob_rootFactoryOp_ge` gives `2/14` as a lower
bound on the probability that a draw is a factory operator at the root, and
`genLExprBase_prob_rootFactoryApp_ge` gives `4/14` times the `Indir` branch's mass as a lower bound
on the probability that it is a factory operator *applied* to arguments.

**(3) A loop-coverage lower bound.** `genStmt_prob_rootLoop_ge`: the probability that a draw at
`size + 1` is a single `loop` statement is at least `2/17` times the loop branch's own mass, and
`genStmt_prob_rootLoop_pos` says that this is positive whenever the branch can produce anything.

**Why bounds and not equalities.** A leaf generator can fail — `genCmd` draws an expression, and an
expression generator has branches with empty support — so a sub-draw carries mass `< 1`, and a claim
about the whole is a claim about the parts weighted by masses that nothing here bounds from below.
`mass_le_one` is what the upper bound in (1) uses in place of `IsPMF`, and the mass factors in (2b)
and (3) are what an acceptance-rate result would remove. The direction is also the one the fixpoint
theory admits: `SPMF.admissible_expect_le` holds for `expect … ≤ B`, not for `B ≤ expect …`.
-/

namespace StrataGenerators.Expectations

open Lambda Core Imperative RandomChoice SPMF NNReal ENNReal
open StrataGenerators StrataGenerators.Stmt StrataGenerators.IndirSupport

-- ── Counting loops ───────────────────────────────────────────────────────

mutual

/-- The number of `loop` statements in a statement, at every nesting depth. -/
def numLoops : Statement → Nat
  | .loop _ _ _ body _ => 1 + numLoopsL body
  | .block _ body _ => numLoopsL body
  | .ite _ thenb elseb _ => numLoopsL thenb + numLoopsL elseb
  | .cmd _ => 0
  | .exit _ _ => 0
  | .funcDecl _ _ => 0
  | .typeDecl _ _ => 0

/-- `numLoops` summed over a statement list. -/
def numLoopsL : List Statement → Nat
  | [] => 0
  | s :: ss => numLoops s + numLoopsL ss

end

@[simp]
theorem numLoopsL_nil : numLoopsL [] = 0 := rfl

@[simp]
theorem numLoopsL_cons (s : Statement) (ss : List Statement) :
    numLoopsL (s :: ss) = numLoops s + numLoopsL ss := rfl

@[simp]
theorem numLoopsL_append (ss ts : List Statement) :
    numLoopsL (ss ++ ts) = numLoopsL ss + numLoopsL ts := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp [ih, Nat.add_assoc]

/-- A statement list of commands only holds no loop. -/
theorem numLoopsL_eq_zero_of_all_cmd {ss : List Statement}
    (h : ∀ s ∈ ss, ∃ c, s = .cmd c) : numLoopsL ss = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    obtain ⟨c, rfl⟩ := h s (by simp)
    simp only [numLoopsL_cons, numLoops, Nat.zero_add]
    exact ih fun t ht => h t (by simp [ht])

/-- The `init` chain that a call group prefixes is all commands. -/
@[simp]
theorem numLoopsL_initChain (news : List (Identifier Unit × LMonoTy)) :
    numLoopsL (StrataGenerators.Stmt.initChain news) = 0 := by
  refine numLoopsL_eq_zero_of_all_cmd fun s hs => ?_
  simp only [StrataGenerators.Stmt.initChain, List.mem_map] at hs
  obtain ⟨p, _, rfl⟩ := hs
  exact ⟨_, rfl⟩

-- ── The leaf branches contribute no loop ─────────────────────────────────

theorem genCmdStmt_numLoops (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (C : LContext CoreLParams) (ctx : VarCtx)
    (depth : Nat) (pctx : PolyOpCtx) (r : GenStmtResult)
    (hr : r ∈ support (genCmdStmt (G := SPMF) octx tvars immutableVars C ctx depth pctx)) :
    numLoopsL r.stmts = 0 := by
  simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

theorem genExitStmt_numLoops (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
    (r : GenStmtResult) (hr : r ∈ support (genExitStmt (G := SPMF) labels C ctx)) :
    numLoopsL r.stmts = 0 := by
  cases labels with
  | nil => simp only [genExitStmt, mem_support_bot_iff] at hr
  | cons l ls =>
    simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    rfl

theorem genFuncDeclStmt_numLoops (octx : OpCtx) (C : LContext CoreLParams) (ctx : VarCtx)
    (depth : Nat) (pctx : PolyOpCtx) (r : GenStmtResult)
    (hr : r ∈ support (genFuncDeclStmt (G := SPMF) octx C ctx depth pctx)) :
    numLoopsL r.stmts = 0 := by
  simp only [genFuncDeclStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

theorem genTypeDeclStmt_numLoops (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat)
    (r : GenStmtResult) (hr : r ∈ support (genTypeDeclStmt (G := SPMF) C ctx depth)) :
    numLoopsL r.stmts = 0 := by
  simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
  obtain ⟨_, _, hr⟩ := hr
  split at hr
  · simp only [mem_support_pure_iff] at hr; subst hr; rfl
  · simp only [mem_support_bot_iff] at hr

theorem genCallStmt_numLoops (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx)
    (r : GenStmtResult)
    (hr : r ∈ support (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx depth pctx)) :
    numLoopsL r.stmts = 0 := by
  cases procs with
  | nil => simp only [genCallStmt, mem_support_bot_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff] at hr
    obtain ⟨_, _, _, _, hr⟩ := hr
    split at hr
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr
      simp only [numLoopsL_append, numLoopsL_initChain, numLoopsL_cons, numLoopsL_nil]
      rfl
    · simp only [mem_support_bot_iff] at hr

-- ── The bound ────────────────────────────────────────────────────────────

/-- The number of loops in a draw, as a feature of the result. -/
noncomputable def loops (r : GenStmtResult) : ℝ≥0∞ := (numLoopsL r.stmts : ℝ≥0∞)

/-- The number of loops in a chain's result. -/
noncomputable def loopsChain (t : List Statement × LContext CoreLParams × VarCtx) : ℝ≥0∞ :=
  (numLoopsL t.1 : ℝ≥0∞)

/-- The bound on the expected loop count of `genStmt … size`.

`loopBound 0 = 0`: at size `0` only leaf constructors are produced. The step reads the branch
weights of `genStmt` off the `frequency` list: the `loop` branch's share is `2/17`, and the four
nesting branches feed `5 * (size + 1)` copies of a body drawn at `size` into the total of `17`. -/
noncomputable def loopBound : Nat → ℝ≥0∞
  | 0 => 0
  | n + 1 => 2 / 17 + (5 * (n + 1) / 17) * loopBound n

/-- The recurrence, as an equation. The multiplier `5 * (n+1) / 17` exceeds `1` from `n = 3`, so the
bound grows faster than any exponential in `size` — the mean body length grows with `size` too, and
that is what makes the branching factor grow. -/
theorem loopBound_succ (n : Nat) :
    loopBound (n + 1) = 2 / 17 + (5 * ((n : ℝ≥0∞) + 1) / 17) * loopBound n := rfl

/-- At `size = 1` the bound is exactly the `loop` branch's weight share. -/
theorem loopBound_one : loopBound 1 = 2 / 17 := by simp [loopBound]

/-- And at `size = 2` it is `2/17 + (10/17) * (2/17) ≈ 0.187`. -/
theorem loopBound_two : loopBound 2 = 2 / 17 + 10 / 17 * (2 / 17) := by
  rw [loopBound, loopBound_one]
  norm_num

/-- The bound is finite at every size, so `genStmt_expect_numLoops_le` is not the vacuous
`expect … ≤ ⊤`. -/
theorem loopBound_ne_top (n : Nat) : loopBound n ≠ ⊤ := by
  induction n with
  | zero => simp [loopBound]
  | succ n ih =>
    rw [loopBound]
    refine ENNReal.add_ne_top.mpr
      ⟨ENNReal.div_ne_top (by norm_num) (by norm_num), ENNReal.mul_ne_top ?_ ih⟩
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp)) (by norm_num)

/-- **The chain bound.** A chain of `len` groups holds at most `len` times what one group holds.
Stated against a hypothesis on `genStmt` at the same `size`, so the mutual recursion is discharged
by nesting this induction inside the induction on `size`. -/
theorem genStmtChain_expect_le (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (pctx : PolyOpCtx) (size : Nat) (B : ℝ≥0∞)
    (ih : ∀ C ctx, expect (genStmt (G := SPMF) octx tvars immutableVars procs labels
      C ctx pctx size) loops ≤ B) :
    ∀ (len : Nat) (C : LContext CoreLParams) (ctx : VarCtx),
      expect (genStmtChain (G := SPMF) octx tvars immutableVars procs labels
        C ctx pctx size len) loopsChain ≤ (len : ℝ≥0∞) * B := by
  intro len
  induction len with
  | zero =>
    intro C ctx
    rw [genStmtChain]
    simp only [expect_pure, loopsChain, numLoopsL_nil, Nat.cast_zero, Nat.cast_zero, zero_mul,
      le_refl]
  | succ len ihlen =>
    intro C ctx
    rw [genStmtChain, expect_bind]
    -- One group, then the rest: the loop count of the concatenation splits, `expect` is additive,
    -- and the mass of the tail is at most `1`.
    refine le_trans (expect_mono (g := fun r => loops r + (len : ℝ≥0∞) * B) fun r => ?_) ?_
    · rw [expect_bind]
      refine le_trans (expect_mono (g := fun d => loops r + loopsChain d) fun d => ?_) ?_
      · obtain ⟨rest, C'', ctx''⟩ := d
        simp only [expect_pure, loopsChain, loops, numLoopsL_append, Nat.cast_add, le_refl]
      · rw [expect_add]
        show _ ≤ loops r + (len : ℝ≥0∞) * B
        gcongr
        · calc expect _ (fun _ => loops r) = _ * loops r := expect_const _ _
            _ ≤ 1 * loops r := by gcongr; exact mass_le_one _
            _ = loops r := one_mul _
        · exact ihlen _ _
    · rw [expect_add, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm ((len : ℝ≥0∞) * B) B]
      gcongr
      · exact ih C ctx
      · calc expect _ (fun _ => (len : ℝ≥0∞) * B) = _ * ((len : ℝ≥0∞) * B) := expect_const _ _
          _ ≤ 1 * ((len : ℝ≥0∞) * B) := by gcongr; exact mass_le_one _
          _ = (len : ℝ≥0∞) * B := one_mul _

/-- The average of `len * L` over a uniform `len ∈ [0, m]` is `(m/2) * L`. This is the lemma that
puts the *average* body length into the recurrence rather than the worst case. -/
theorem expect_choose_mul (m : Nat) (L : ℝ≥0∞) :
    expect (choose 0 m (Nat.zero_le m) : SPMF _) (fun p => (p.down.val : ℝ≥0∞) * L)
      = ((m : ℝ≥0∞) / 2) * L := by
  rw [expect_choose (Nat.zero_le m) _ (fun x => (x : ℝ≥0∞) * L) (fun _ => rfl)]
  rw [Nat.sub_zero, ← Finset.sum_mul, ← Nat.cast_sum]
  -- Gauss' formula, in the doubled form that avoids a `Nat` division.
  have hIcc : Finset.Icc 0 m = Finset.range (m + 1) := by
    ext x; simp
  have hgauss : (∑ x ∈ Finset.Icc 0 m, x) * 2 = (m + 1) * m := by
    rw [hIcc, Finset.sum_range_id_mul_two]
    simp
  rw [show ((m : ℝ≥0∞) / 2 * L) = ((m : ℝ≥0∞) * L) / 2 from by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring,
      ENNReal.div_eq_div_iff (by simp) (by simp) (by simp) (by simp)]
  calc 2 * ((∑ x ∈ Finset.Icc 0 m, x : ℕ) * L)
      = (((∑ x ∈ Finset.Icc 0 m, x) * 2 : ℕ) : ℝ≥0∞) * L := by
        push_cast; ring
    _ = (((m + 1) * m : ℕ) : ℝ≥0∞) * L := by rw [hgauss]
    _ = ((m + 1 : ℕ) : ℝ≥0∞) * ((m : ℝ≥0∞) * L) := by push_cast; ring

-- ── The leaf branches, as expectations ───────────────────────────────────

/-- A generator whose every draw is loop-free has expected loop count `0`. -/
theorem expect_loops_eq_zero {g : SPMF GenStmtResult}
    (h : ∀ r ∈ support g, numLoopsL r.stmts = 0) : expect g loops = 0 :=
  le_antisymm (expect_le_of_support fun r hr => by simp [loops, h r hr]) (zero_le _)

theorem genStmt_leaf_expect (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (depth : Nat) :
    expect (genCmdStmt (G := SPMF) octx tvars immutableVars C ctx depth pctx) loops = 0
    ∧ expect (if labels.isEmpty then genCmdStmt (G := SPMF) octx tvars immutableVars C ctx depth pctx
        else genExitStmt (G := SPMF) labels C ctx) loops = 0
    ∧ expect (genFuncDeclStmt (G := SPMF) octx C ctx depth pctx) loops = 0
    ∧ expect (genTypeDeclStmt (G := SPMF) C ctx depth) loops = 0
    ∧ expect (if procs.isEmpty then genCmdStmt (G := SPMF) octx tvars immutableVars C ctx depth pctx
        else genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx depth pctx) loops = 0 := by
  refine ⟨expect_loops_eq_zero (genCmdStmt_numLoops _ _ _ _ _ _ _), ?_,
    expect_loops_eq_zero (genFuncDeclStmt_numLoops _ _ _ _ _),
    expect_loops_eq_zero (genTypeDeclStmt_numLoops _ _ _), ?_⟩
  · split
    · exact expect_loops_eq_zero (genCmdStmt_numLoops _ _ _ _ _ _ _)
    · exact expect_loops_eq_zero (genExitStmt_numLoops _ _ _)
  · split
    · exact expect_loops_eq_zero (genCmdStmt_numLoops _ _ _ _ _ _ _)
    · exact expect_loops_eq_zero (genCallStmt_numLoops _ _ _ _ _ _ _ _)

-- ── Generic expectation plumbing ─────────────────────────────────────────

/-- A draw whose continuation is bounded by a constant, whatever it draws. `mass ≤ 1` is what
makes this an inequality and not an equality: a sub-draw that fails contributes nothing. -/
theorem expect_bind_const_le {α : Type} (g : SPMF α) (h : α → SPMF GenStmtResult) (c : ℝ≥0∞)
    (hc : ∀ a, expect (h a) loops ≤ c) : expect (g >>= h) loops ≤ c := by
  rw [expect_bind]
  calc expect g (fun a => expect (h a) loops) ≤ expect g (fun _ => c) := expect_mono hc
    _ = g.mass * c := expect_const _ _
    _ ≤ 1 * c := by gcongr; exact mass_le_one _
    _ = c := one_mul c

/-- Adding a constant feature costs at most that constant. -/
theorem expect_add_const_le {α : Type} {g : SPMF α} {u : α → ℝ≥0∞} {B c : ℝ≥0∞}
    (h : expect g u ≤ B) : expect g (fun a => u a + c) ≤ B + c := by
  rw [expect_add]
  gcongr
  calc expect g (fun _ => c) = g.mass * c := expect_const _ _
    _ ≤ 1 * c := by gcongr; exact mass_le_one _
    _ = c := one_mul c

/-- `expect_add_const_le` with the constant on the left. -/
theorem expect_const_add_le {α : Type} {g : SPMF α} {u : α → ℝ≥0∞} {B c : ℝ≥0∞}
    (h : expect g u ≤ B) : expect g (fun a => c + u a) ≤ c + B :=
  calc expect g (fun a => c + u a)
      = expect g (fun a => u a + c) := expect_congr_support fun a _ => add_comm c (u a)
    _ ≤ B + c := expect_add_const_le h
    _ = c + B := add_comm B c

/-- **Averaging a body-length-linear bound over the uniform body length.** A bound `a + len * L` on
each `len` averages to `a + (m/2) * L`, because `choose 0 m` has mean `m/2`. This is the step that
puts the *mean* body length into the recurrence. -/
theorem expect_choose_le (m : Nat) (f : ULift {x : Nat // 0 ≤ x ∧ x ≤ m} → ℝ≥0∞) (a L : ℝ≥0∞)
    (hf : ∀ p, f p ≤ a + (p.down.val : ℝ≥0∞) * L) :
    expect (choose 0 m (Nat.zero_le m) : SPMF _) f ≤ a + (m : ℝ≥0∞) / 2 * L := by
  refine le_trans (expect_mono hf) ?_
  rw [expect_add, expect_choose_mul]
  gcongr
  calc expect (choose 0 m (Nat.zero_le m) : SPMF _) (fun _ => a) = _ * a := expect_const _ _
    _ ≤ 1 * a := by gcongr; exact mass_le_one _
    _ = a := one_mul a

-- ── The four nesting branches ────────────────────────────────────────────

/-- The mean loop count of one body: the mean body length `(size+1)/2` times the bound on one
group. -/
noncomputable def halfLen (size : Nat) : ℝ≥0∞ :=
  ((size + 1 : ℕ) : ℝ≥0∞) / 2 * loopBound size

section Branches

variable (octx : OpCtx) (tvars : List TyIdentifier) (immutableVars : List (Identifier Unit))
  (procs : ProcSigCtx) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
  (pctx : PolyOpCtx) (size : Nat)

/-- The bound on one drawn body: a chain of a uniformly drawn length. -/
private theorem body_le (labels' : List String)
    (ihsize : ∀ labels C ctx,
      expect (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size) loops
        ≤ loopBound size)
    (len : Nat) :
    expect (genStmtChain (G := SPMF) octx tvars immutableVars procs labels' C ctx pctx size len)
      loopsChain ≤ (len : ℝ≥0∞) * loopBound size :=
  genStmtChain_expect_le octx tvars immutableVars procs labels' pctx size (loopBound size)
    (fun C ctx => ihsize labels' C ctx) len C ctx

theorem block_branch_le
    (ihsize : ∀ labels C ctx,
      expect (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size) loops
        ≤ loopBound size) :
    expect (do
      let label ← genFreshLabel (G := SPMF) labels
      let ⟨⟨len, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
      let (body, _, _) ← genStmtChain (G := SPMF) octx tvars immutableVars procs (label :: labels)
        C ctx pctx size len
      Pure.pure (⟨[Stmt.block label body default], C, ctx⟩ : GenStmtResult)) loops
      ≤ halfLen size := by
  refine expect_bind_const_le _ _ _ fun label => ?_
  rw [expect_bind, halfLen, ← zero_add (((size + 1 : ℕ) : ℝ≥0∞) / 2 * loopBound size)]
  refine expect_choose_le (size + 1) _ 0 (loopBound size) fun p => ?_
  obtain ⟨⟨len, hlen⟩⟩ := p
  rw [zero_add, expect_bind]
  refine le_trans (expect_mono (g := loopsChain) fun d => ?_)
    (body_le octx tvars immutableVars procs C ctx pctx size (label :: labels) ihsize len)
  simp only [expect_pure, loops, loopsChain, numLoopsL_cons, numLoopsL_nil, numLoops,
    Nat.add_zero, le_refl]

theorem iteDet_branch_le
    (ihsize : ∀ labels C ctx,
      expect (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size) loops
        ≤ loopBound size) :
    expect (do
      let cond ← genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] (size + 1) .bool
      let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
      let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
      let (thenb, _, _) ← genStmtChain (G := SPMF) octx tvars immutableVars procs labels
        C ctx pctx size tlen
      let (elseb, _, _) ← genStmtChain (G := SPMF) octx tvars immutableVars procs labels
        C ctx pctx size elen
      Pure.pure (⟨[Stmt.ite (.det cond) thenb elseb default], C, ctx⟩ : GenStmtResult)) loops
      ≤ halfLen size + halfLen size := by
  refine expect_bind_const_le _ _ _ fun cond => ?_
  rw [expect_bind]
  show _ ≤ halfLen size + ((size + 1 : ℕ) : ℝ≥0∞) / 2 * loopBound size
  refine expect_choose_le (size + 1) _ (halfLen size) (loopBound size) fun p => ?_
  obtain ⟨⟨tlen, htlen⟩⟩ := p
  rw [expect_bind, add_comm (halfLen size) ((tlen : ℝ≥0∞) * loopBound size)]
  show _ ≤ (tlen : ℝ≥0∞) * loopBound size + ((size + 1 : ℕ) : ℝ≥0∞) / 2 * loopBound size
  refine expect_choose_le (size + 1) _ ((tlen : ℝ≥0∞) * loopBound size) (loopBound size) fun q => ?_
  obtain ⟨⟨elen, helen⟩⟩ := q
  rw [expect_bind]
  refine le_trans (expect_mono (g := fun d => loopsChain d + (elen : ℝ≥0∞) * loopBound size)
    fun d => ?_) ?_
  · rw [expect_bind]
    refine le_trans (expect_mono (g := fun e => loopsChain d + loopsChain e) fun e => ?_) ?_
    · simp only [expect_pure, loops, loopsChain, numLoopsL_cons, numLoopsL_nil, numLoops,
        Nat.add_zero, Nat.cast_add, le_refl]
    · show _ ≤ loopsChain d + (elen : ℝ≥0∞) * loopBound size
      exact expect_const_add_le
        (body_le octx tvars immutableVars procs C ctx pctx size labels ihsize elen)
  · exact expect_add_const_le (body_le octx tvars immutableVars procs C ctx pctx size labels
      ihsize tlen)

theorem iteNondet_branch_le
    (ihsize : ∀ labels C ctx,
      expect (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size) loops
        ≤ loopBound size) :
    expect (do
      let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose (m := SPMF) 0 (size + 1) (Nat.zero_le _)
      let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
      let (thenb, _, _) ← genStmtChain (G := SPMF) octx tvars immutableVars procs labels
        C ctx pctx size tlen
      let (elseb, _, _) ← genStmtChain (G := SPMF) octx tvars immutableVars procs labels
        C ctx pctx size elen
      Pure.pure (⟨[Stmt.ite .nondet thenb elseb default], C, ctx⟩ : GenStmtResult)) loops
      ≤ halfLen size + halfLen size := by
  rw [expect_bind]
  show _ ≤ halfLen size + ((size + 1 : ℕ) : ℝ≥0∞) / 2 * loopBound size
  refine expect_choose_le (size + 1) _ (halfLen size) (loopBound size) fun p => ?_
  obtain ⟨⟨tlen, htlen⟩⟩ := p
  rw [expect_bind, add_comm (halfLen size) ((tlen : ℝ≥0∞) * loopBound size)]
  show _ ≤ (tlen : ℝ≥0∞) * loopBound size + ((size + 1 : ℕ) : ℝ≥0∞) / 2 * loopBound size
  refine expect_choose_le (size + 1) _ ((tlen : ℝ≥0∞) * loopBound size) (loopBound size) fun q => ?_
  obtain ⟨⟨elen, helen⟩⟩ := q
  rw [expect_bind]
  refine le_trans (expect_mono (g := fun d => loopsChain d + (elen : ℝ≥0∞) * loopBound size)
    fun d => ?_) ?_
  · rw [expect_bind]
    refine le_trans (expect_mono (g := fun e => loopsChain d + loopsChain e) fun e => ?_) ?_
    · simp only [expect_pure, loops, loopsChain, numLoopsL_cons, numLoopsL_nil, numLoops,
        Nat.add_zero, Nat.cast_add, le_refl]
    · show _ ≤ loopsChain d + (elen : ℝ≥0∞) * loopBound size
      exact expect_const_add_le
        (body_le octx tvars immutableVars procs C ctx pctx size labels ihsize elen)
  · exact expect_add_const_le (body_le octx tvars immutableVars procs C ctx pctx size labels
      ihsize tlen)

theorem loop_branch_le
    (ihsize : ∀ labels C ctx,
      expect (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size) loops
        ≤ loopBound size) :
    expect (do
      let guard ← genCondOrNondet (G := SPMF) octx tvars ctx (size + 1) pctx
      let measure ← genOptMeasure octx tvars ctx (size + 1) pctx
      let invariants ← genInvariants octx tvars ctx (size + 1) pctx
      let ⟨⟨blen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
      let (body, _, _) ← genStmtChain (G := SPMF) octx tvars immutableVars procs labels
        C ctx pctx size blen
      Pure.pure (⟨[Stmt.loop guard measure invariants body default], C, ctx⟩ : GenStmtResult)) loops
      ≤ 1 + halfLen size := by
  refine expect_bind_const_le _ _ _ fun guard => ?_
  refine expect_bind_const_le _ _ _ fun measure => ?_
  refine expect_bind_const_le _ _ _ fun invariants => ?_
  rw [expect_bind, halfLen]
  refine expect_choose_le (size + 1) _ 1 (loopBound size) fun p => ?_
  obtain ⟨⟨blen, hblen⟩⟩ := p
  rw [expect_bind, add_comm]
  refine le_trans (expect_mono (g := fun d => loopsChain d + 1) fun d => ?_) ?_
  · simp [loops, loopsChain, numLoops, add_comm]
  · exact expect_add_const_le
      (body_le octx tvars immutableVars procs C ctx pctx size labels ihsize blen)

end Branches

-- ── The expected loop count ──────────────────────────────────────────────

/-- **(1) The expected number of loops in a draw of `genStmt` is at most `loopBound size`.** -/
theorem genStmt_expect_numLoops_le (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx) :
    ∀ (size : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx),
      expect (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size) loops
        ≤ loopBound size := by
  intro size
  induction size with
  | zero =>
    intro labels C ctx
    obtain ⟨h0, h1, h2, h3, h4⟩ :=
      genStmt_leaf_expect octx tvars immutableVars procs labels C ctx pctx 0
    rw [genStmt, expect_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3, h4]
    simp [loopBound]
  | succ size ihsize =>
    intro labels C ctx
    obtain ⟨h0, h1, h2, h3, h4⟩ :=
      genStmt_leaf_expect octx tvars immutableVars procs labels C ctx pctx (size + 1)
    rw [genStmt, expect_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3, h4,
      mul_zero, zero_add, add_zero, Nat.cast_ofNat]
    have hb := block_branch_le octx tvars immutableVars procs labels C ctx pctx size ihsize
    have hd := iteDet_branch_le octx tvars immutableVars procs labels C ctx pctx size ihsize
    have hn := iteNondet_branch_le octx tvars immutableVars procs labels C ctx pctx size ihsize
    have hl := loop_branch_le octx tvars immutableVars procs labels C ctx pctx size ihsize
    calc _ ≤ (2 * halfLen size + (2 * (halfLen size + halfLen size)
                + (((1 : ℕ) : ℝ≥0∞) * (halfLen size + halfLen size)
                  + 2 * (1 + halfLen size))))
              / (((4 + (1 + (1 + (1 + (3 + (2 + (2 + (1 + 2))))))) : ℕ) : ℝ≥0∞)) := by
          gcongr
      _ = loopBound (size + 1) := by
          rw [loopBound, halfLen]
          have hcast : ((size + 1 : ℕ) : ℝ≥0∞) = (size : ℝ≥0∞) + 1 := by push_cast; ring
          have hden : ((4 + (1 + (1 + (1 + (3 + (2 + (2 + (1 + 2))))))) : ℕ) : ℝ≥0∞) = 17 := by
            norm_num
          rw [hcast, hden]
          -- Ten copies of a mean body, plus the loop itself, over the total weight.
          have hhalf : (2 : ℝ≥0∞) * (((size : ℝ≥0∞) + 1) / 2) = (size : ℝ≥0∞) + 1 :=
            ENNReal.mul_div_cancel (by norm_num) (by norm_num)
          have key : (10 : ℝ≥0∞) * (((size : ℝ≥0∞) + 1) / 2 * loopBound size)
              = 5 * (((size : ℝ≥0∞) + 1) * loopBound size) := by
            calc (10 : ℝ≥0∞) * (((size : ℝ≥0∞) + 1) / 2 * loopBound size)
                = 5 * (2 * (((size : ℝ≥0∞) + 1) / 2) * loopBound size) := by ring
              _ = 5 * (((size : ℝ≥0∞) + 1) * loopBound size) := by rw [hhalf]
          have hnum : 2 * (((size : ℝ≥0∞) + 1) / 2 * loopBound size)
                + (2 * (((size : ℝ≥0∞) + 1) / 2 * loopBound size
                      + ((size : ℝ≥0∞) + 1) / 2 * loopBound size)
                  + (((1 : ℕ) : ℝ≥0∞) * (((size : ℝ≥0∞) + 1) / 2 * loopBound size
                        + ((size : ℝ≥0∞) + 1) / 2 * loopBound size)
                    + 2 * (1 + ((size : ℝ≥0∞) + 1) / 2 * loopBound size)))
              = 5 * (((size : ℝ≥0∞) + 1) * loopBound size) + 2 := by
            rw [← key]; push_cast; ring
          rw [hnum, ENNReal.add_div]
          rw [add_comm]
          congr 1
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring


-- ── (3) Coverage: the probability that a draw is a loop ──────────────────

/-- The event: the draw is a single `loop` statement. This is the shape that the loop-transformation
properties of the suite need to see, and the shape `stmtLoopHeavy` raises the weight of. -/
def RootLoop : Set GenStmtResult :=
  {r | ∃ guard measure invs body md, r.stmts = [Stmt.loop guard measure invs body md]}

/-- A generator all of whose draws lie in `E` puts its whole mass on `E`. -/
theorem prob_eq_mass_of_subset {α : Type} {p : SPMF α} {E : Set α}
    (h : ∀ a ∈ support p, a ∈ E) : prob p E = p.mass := by
  unfold prob
  rw [← expect_one p]
  exact expect_congr_support fun a ha => by simp [Set.indicator, h a ha]

/-- A loop-free generator never draws a root loop. -/
theorem prob_rootLoop_eq_zero_of_numLoops {g : SPMF GenStmtResult}
    (h : ∀ r ∈ support g, numLoopsL r.stmts = 0) : prob g RootLoop = 0 := by
  rw [prob_eq_zero_iff]
  intro r hr hmem
  obtain ⟨guard, measure, invs, body, md, hrs⟩ := hmem
  have := h r hr
  rw [hrs] at this
  simp only [numLoopsL_cons, numLoopsL_nil, numLoops, Nat.add_zero] at this
  omega

section Coverage

variable (octx : OpCtx) (tvars : List TyIdentifier) (immutableVars : List (Identifier Unit))
  (procs : ProcSigCtx) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
  (pctx : PolyOpCtx) (size : Nat)

/-- The `loop` branch of `genStmt` at `size + 1`, as a generator in its own right. Definitionally
the branch body, so `genStmt`'s `frequency` list mentions exactly this. -/
noncomputable def loopBranch : SPMF GenStmtResult := do
  let guard ← genCondOrNondet (G := SPMF) octx tvars ctx (size + 1) pctx
  let measure ← genOptMeasure octx tvars ctx (size + 1) pctx
  let invariants ← genInvariants octx tvars ctx (size + 1) pctx
  let ⟨⟨blen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
  let (body, _, _) ← genStmtChain (G := SPMF) octx tvars immutableVars procs labels
    C ctx pctx size blen
  Pure.pure (⟨[Stmt.loop guard measure invariants body default], C, ctx⟩ : GenStmtResult)

/-- Every draw of the `loop` branch is a root loop, so the branch puts its whole mass on
`RootLoop`. -/
theorem loop_branch_prob_rootLoop :
    prob (loopBranch octx tvars immutableVars procs labels C ctx pctx size) RootLoop
      = (loopBranch octx tvars immutableVars procs labels C ctx pctx size).mass := by
  refine prob_eq_mass_of_subset fun r hr => ?_
  simp only [loopBranch, mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
  obtain ⟨guard, -, measure, -, invariants, -, p, -, d, -, rfl⟩ := hr
  exact ⟨guard, measure, invariants, d.1, default, rfl⟩

/-- **(3) A coverage lower bound.** The `loop` branch's weight share, `2/17`, times that branch's
own mass, is a lower bound on the probability that a draw of `genStmt` at `size + 1` is a single
`loop` statement. The mass factor is what an acceptance-rate result would remove; `2/17` is the
weight share, and it is what `stmtLoopHeavy` raises. -/
theorem genStmt_prob_rootLoop_ge :
    2 * (loopBranch octx tvars immutableVars procs labels C ctx pctx size).mass / 17
      ≤ prob (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx (size + 1))
          RootLoop := by
  rw [genStmt, prob_frequency]
  have hden : ((4 + (1 + (1 + (1 + (3 + (2 + (2 + (1 + 2))))))) : ℕ) : ℝ≥0∞) = 17 := by norm_num
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hden]
  rw [← loop_branch_prob_rootLoop]
  refine ENNReal.div_le_div_right ?_ _
  show 2 * prob (loopBranch octx tvars immutableVars procs labels C ctx pctx size) RootLoop ≤ _
  -- Drop the eight branches that are not the `loop` branch.
  iterate 8 refine le_trans ?_ le_add_self
  exact le_self_add

/-- The lower bound is not vacuous: a `loop` is drawn with positive probability whenever the loop
branch can produce one at all. `loop_mem` supplies the witness. -/
theorem genStmt_prob_rootLoop_pos (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr) (invs : List (String × Expression.Expr))
    (body : List Statement) (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (blen : Nat) (hblen : blen ≤ size + 1)
    (hguard : guard ∈ support (genCondOrNondet (G := SPMF) octx tvars ctx (size + 1)))
    (hmeasure : measure ∈ support (genOptMeasure (G := SPMF) octx tvars ctx (size + 1)))
    (hinvs : invs ∈ support (genInvariants (G := SPMF) octx tvars ctx (size + 1)))
    (hbody : (body, C_body, Γ_body) ∈
      support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx [] size blen)) :
    0 < prob (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx [] (size + 1))
      RootLoop := by
  rw [pos_iff_ne_zero]
  intro hzero
  rw [prob_eq_zero_iff] at hzero
  exact hzero _ (StrataGenerators.Stmt.loop_mem procs C ctx size guard measure invs body C_body
    Γ_body blen hblen hguard hmeasure hinvs hbody) ⟨guard, measure, invs, body, default, rfl⟩

end Coverage

-- ── (2) Coverage: factory operators in a generated expression ────────────

/-- The event: the root of the expression is a factory operator, applied to a (possibly empty)
list of arguments. `pickOp` draws the empty case, a bare operator reference. -/
def RootFactoryOp : Set LExpr' :=
  {e | ∃ nm mty args, e = mkApps (LExpr.op () nm mty) args}

/-- The event: the root is a factory operator applied to at least one argument. This is the shape
the `Indir` and `IndirPoly` rules produce, and the one the ADT-law properties read. -/
def RootFactoryApp : Set LExpr' :=
  {e | ∃ nm mty args, args ≠ [] ∧ e = mkApps (LExpr.op () nm mty) args}

/-- Every candidate of `findOpsInCtx` takes at least one argument: the `filterMap` keeps only a
`some (arg :: args)`. This is why an `Indir` draw is an application and not a bare reference. -/
theorem findOpsInCtx_argTys_ne_nil (octx : OpCtx) (τ : LMonoTy) {nm : String}
    {argTys : List LMonoTy} (h : (nm, argTys) ∈ findOpsInCtx octx τ) : argTys ≠ [] := by
  simp only [findOpsInCtx, List.mem_filterMap] at h
  obtain ⟨⟨name, ty⟩, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact List.cons_ne_nil _ _
  · simp at h

/-- `pickOp` draws a bare factory operator, always. -/
theorem pickOp_prob_rootFactoryOp (octx : OpCtx) (τ : LMonoTy)
    (ho : (opsOfType octx τ).length > 0) :
    prob (pickOp (G := SPMF) octx τ ho) RootFactoryOp = 1 := by
  have hsub : ∀ e ∈ support (pickOp (G := SPMF) octx τ ho), e ∈ RootFactoryOp := by
    intro e he
    rw [pickOp, mem_support_elements_iff] at he
    simp only [List.mem_map] at he
    obtain ⟨nm, -, rfl⟩ := he
    exact ⟨⟨nm, ()⟩, some τ, [], rfl⟩
  rw [prob_eq_mass_of_subset hsub]
  exact le_antisymm (mass_le_one _) (by rw [pickOp]; exact le_mass_elements)

/-- Every `Indir` draw is a factory application. -/
theorem genIndir_prob_rootFactoryApp (octx : OpCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SPMF LExpr') (h : (findOpsInCtx octx τ).length > 0) :
    prob (genIndir (G := SPMF) octx τ genArg h) RootFactoryApp
      = (genIndir (G := SPMF) octx τ genArg h).mass := by
  refine prob_eq_mass_of_subset fun e he => ?_
  obtain ⟨name, argTys, args, hmem, hrel, rfl⟩ := genIndir_shape octx τ genArg h e he
  refine ⟨_, _, args, ?_, rfl⟩
  intro hnil
  subst hnil
  cases hrel
  exact findOpsInCtx_argTys_ne_nil octx τ hmem rfl

/-- `τ` is none of the shapes `genLExprBase` handles specially — so it is headed by a declared type
constructor. This is the case the factory branches exist for: a datatype-typed position, where the
only ways to build a term are a variable in scope and a constructor of the datatype. The ten
conjuncts are exactly the side conditions of `genLExprBase`'s catch-all equation. -/
def IsDeclaredTyShaped (τ : LMonoTy) : Prop :=
  (∀ τ₁ τ₂, τ = .tcons "arrow" [τ₁, τ₂] → False) ∧ (τ = .tcons "bool" [] → False) ∧
  (τ = .tcons "int" [] → False) ∧ (∀ name, τ = .ftvar name → False) ∧
  (τ = .tcons "string" [] → False) ∧ (τ = .tcons "real" [] → False) ∧
  (∀ w, τ = .bitvec w → False) ∧ (τ = .tcons "regex" [] → False) ∧
  (∀ τ₁ τ₂, τ = .tcons "Map" [τ₁, τ₂] → False) ∧ (∀ τ', τ = .tcons "Sequence" [τ'] → False)

/-- A declared nullary type constructor is one of these. Instantiating the two bounds below, so they
are visibly not vacuous. -/
theorem isDeclaredTyShaped_tcons (nm : String) (args : List LMonoTy)
    (h : nm ∉ ["arrow", "bool", "int", "string", "real", "regex", "Map", "Sequence"]) :
    IsDeclaredTyShaped (.tcons nm args) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  refine ⟨fun _ _ hc => ?_, fun hc => ?_, fun hc => ?_, fun _ hc => ?_, fun hc => ?_, fun hc => ?_,
    fun _ hc => ?_, fun hc => ?_, fun _ _ hc => ?_, fun _ hc => ?_⟩
  · exact h.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact LMonoTy.noConfusion hc
  · exact h.2.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.2.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact LMonoTy.noConfusion hc
  · exact h.2.2.2.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.2.2.2.2.2.1 (LMonoTy.tcons.injEq .. ▸ hc).1
  · exact h.2.2.2.2.2.2.2 (LMonoTy.tcons.injEq .. ▸ hc).1

/-- **(2a) A factory-operator coverage bound.** At a declared-type-constructor position with a
factory operator of that type in scope, at least `2/14` of the draws are a factory operator at the
root. The `2` is the `pickOp` branch's weight and `14` the total. No mass hypothesis is needed:
`elements` over a non-empty list is a genuine distribution, so this bound is unconditional. -/
theorem genLExprBase_prob_rootFactoryOp_ge (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy)
    (hτ : IsDeclaredTyShaped τ)
    (hv : (bvarsOfType bctx τ).length = 0) (hf : (fvarsOfType fctx τ).length = 0)
    (ho : (opsOfType octx τ).length > 0) :
    2 / 14 ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) τ)
      RootFactoryOp := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hτ
  rw [genLExprBase, prob_frequency]
  · have hden : ((2 + (2 + (2 + (4 + 4))) : ℕ) : ℝ≥0∞) = 14 := by norm_num
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hden, add_zero,
      dif_neg (by omega : ¬ (bvarsOfType bctx τ).length > 0),
      dif_neg (by omega : ¬ (fvarsOfType fctx τ).length > 0), dif_pos ho,
      pickOp_prob_rootFactoryOp, Nat.cast_ofNat, mul_one]
    refine ENNReal.div_le_div_right ?_ _
    iterate 2 refine le_trans ?_ le_add_self
    exact le_self_add
  all_goals assumption

/-- **(2b) A factory-application coverage bound.** The `Indir` branch's weight share `4/14` times
that branch's own mass. The mass factor is irreducible here: the branch draws an argument for every
input of the chosen operator, and an argument draw can fail — that is the acceptance-rate question,
and it is separate from the weight. -/
theorem genLExprBase_prob_rootFactoryApp_ge (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy)
    (hτ : IsDeclaredTyShaped τ) (hi : (findOpsInCtx octx τ).length > 0) :
    4 * (genIndir (G := SPMF) octx τ
          (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n) hi).mass / 14
      ≤ prob (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (n + 1) τ) RootFactoryApp := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hτ
  rw [genLExprBase, prob_frequency]
  · have hden : ((2 + (2 + (2 + (4 + 4))) : ℕ) : ℝ≥0∞) = 14 := by norm_num
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hden, add_zero,
      dif_pos hi, genIndir_prob_rootFactoryApp, Nat.cast_ofNat]
    refine ENNReal.div_le_div_right ?_ _
    iterate 3 refine le_trans ?_ le_add_self
    exact le_self_add
  all_goals assumption

/-- The side condition is satisfiable: a declared type constructor satisfies it. -/
example : IsDeclaredTyShaped (.tcons "MyList" [.int]) :=
  isDeclaredTyShaped_tcons "MyList" [.int] (by decide)

end StrataGenerators.Expectations
