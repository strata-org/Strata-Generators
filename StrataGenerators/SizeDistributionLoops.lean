import StrataGenerators.SizeDistributionStmt
import StrataGenerators.HasTypeAGen.IndirSupport
import Mathlib.Analysis.Complex.Exponential

/-!
# Loops as a function of the size `n`: expectation, tails and rare events

Every statement here is about `genStmt … n` for **every** size `n`, in every context, and gives a
closed form in `n`.

**Expected number of loops.** `genStmt_expect_numLoops_le` bounds the expected number of `loop`
statements (at every nesting depth) by `loopBound n`, the solution of

```
loopBound 0       = 0
loopBound (n + 1) = 2/17 + (5 (n+1) / 17) · loopBound n
```

`2/17` is the `loop` branch's weight; the four nesting branches feed `5 (n+1)` mean bodies into the
total weight 17, because a body's length is uniform on `[0, n+1]`. The recurrence solves exactly
(`loopBound_eq`):

```
loopBound n = (2/17) · (5/17)ⁿ · n! · Σ_{k=1}^{n} (17/5)ᵏ / k!
```

and so (`genStmt_expect_numLoops_closed`)

```
E[#loops] ≤ (2/17) (e^{17/5} − 1) · (5/17)ⁿ · n!
```

The bound grows like `n! · (5/17)ⁿ`, faster than any exponential: body lengths grow with `n`, so
the branching factor does too. `genStmt_prob_numLoops_ge` turns this into a Markov tail bound:
`P(#loops ≥ t) ≤ E-bound / t`.

**Loop depth.** `genStmt_depth`: no draw of size `n` nests loops more than `n` deep. A nest of
exactly that depth is a rare event, bracketed on both sides (`genStmt_prob_loopDepth_ge`,
`genStmt_prob_loopDepth_le`):

```
1 / (170ᵐ · ((m+1)!)²)  ≤  P(loop depth ≥ m at size m)  ≤  2 · m! / 17ᵐ
```

The lower bound is the probability of one witness: a tower of `loop`s with nondeterministic guards,
no measure, no invariants and one-statement bodies. The upper bound is a union bound over each body,
using that only a `loop` adds depth and that the other branches stay at most `n − 1` deep.

**Why mostly upper bounds.** A leaf generator can fail, so sub-draws have mass `< 1` and nothing
here computes those masses exactly. Upper bounds need only `mass ≤ 1`. The lower bounds take
witnesses that need no failing sub-draw.
-/

namespace StrataGenerators.SizeDistributionLoops

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

/-- The expectation of a function of the drawn value over a uniform `choose 0 m`. -/
theorem expect_choose_eq (m : Nat) (g : Nat → ℝ≥0∞) :
    expect (choose 0 m (Nat.zero_le m) : SPMF _) (fun p => g p.down.val)
      = (∑ x ∈ Finset.Icc 0 m, g x) / ((m - 0 + 1 : ℕ) : ℝ≥0∞) := by
  unfold expect
  simp only [choose_apply]
  rw [ENNReal.tsum_mul_left, SPMF.tsum_subtype_Icc 0 m g, one_div, mul_comm, div_eq_mul_inv]

/-- The average of `len * L` over a uniform `len ∈ [0, m]` is `(m/2) * L`. This is the lemma that
puts the *average* body length into the recurrence rather than the worst case. -/
theorem expect_choose_mul (m : Nat) (L : ℝ≥0∞) :
    expect (choose 0 m (Nat.zero_le m) : SPMF _) (fun p => (p.down.val : ℝ≥0∞) * L)
      = ((m : ℝ≥0∞) / 2) * L := by
  rw [expect_choose_eq m (fun x => (x : ℝ≥0∞) * L)]
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



-- ── Closed forms in `n` ──────────────────────────────────────────────────

open Finset in
/-- The closed form of `loopBound`, as a real number:
`(2/17) · (5/17)ⁿ · n! · ∑_{k=1}^{n} (17/5)ᵏ / k!`. -/
noncomputable def loopClosed (n : Nat) : ℝ :=
  2 / 17 * (5 / 17) ^ n * n.factorial * ∑ k ∈ range n, (17 / 5 : ℝ) ^ (k + 1) / (k + 1).factorial

open Finset in
theorem loopClosed_succ (n : Nat) :
    loopClosed (n + 1) = 2 / 17 + 5 * ((n : ℝ) + 1) / 17 * loopClosed n := by
  unfold loopClosed
  rw [sum_range_succ, Nat.factorial_succ]
  have hf : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hf' : (((n + 1) * n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at hf' ⊢
  rw [mul_add]
  have : 2 / 17 * (5 / 17 : ℝ) ^ (n + 1) * (((n : ℝ) + 1) * n.factorial) *
      ((17 / 5) ^ (n + 1) / (((n : ℝ) + 1) * n.factorial)) = 2 / 17 := by
    field_simp
    rw [← mul_pow]; norm_num
  rw [this]
  ring

theorem loopClosed_nonneg (n : Nat) : 0 ≤ loopClosed n := by
  unfold loopClosed; positivity

/-- **The expected-loop bound in closed form.** -/
theorem loopBound_eq (n : Nat) : loopBound n = ENNReal.ofReal (loopClosed n) := by
  induction n with
  | zero => simp [loopBound, loopClosed]
  | succ n ih =>
    rw [loopBound_succ, ih, loopClosed_succ,
      ENNReal.ofReal_add (by norm_num) (by have := loopClosed_nonneg n; positivity),
      ENNReal.ofReal_mul (by positivity)]
    congr 1
    · rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    · congr 1
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      simp [ENNReal.ofReal_add, ENNReal.ofReal_natCast]

/-- **Growth of the expected loop count.** `∑_{k=1}^{n} xᵏ/k! ≤ eˣ - 1`, so the bound is at most
`(2/17)(e^{17/5} - 1) · (5/17)ⁿ · n!`: it grows like `n! · (5/17)ⁿ`, faster than any exponential. -/
theorem loopClosed_le_exp (n : Nat) :
    loopClosed n ≤ 2 / 17 * (Real.exp (17 / 5) - 1) * ((5 / 17) ^ n * n.factorial) := by
  unfold loopClosed
  have hsum : ∑ k ∈ Finset.range n, (17 / 5 : ℝ) ^ (k + 1) / (k + 1).factorial
      ≤ Real.exp (17 / 5) - 1 := by
    have h := Real.sum_le_exp_of_nonneg (x := 17 / 5) (by norm_num) (n + 1)
    rw [Finset.sum_range_succ'] at h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
    linarith
  have hpos : (0 : ℝ) ≤ 2 / 17 * (5 / 17) ^ n * n.factorial := by positivity
  calc 2 / 17 * (5 / 17 : ℝ) ^ n * n.factorial * _
      ≤ 2 / 17 * (5 / 17) ^ n * n.factorial * (Real.exp (17 / 5) - 1) :=
        mul_le_mul_of_nonneg_left hsum hpos
    _ = _ := by ring

/-- **The expected number of loops of `genStmt … n`, in closed form**, in every context. -/
theorem genStmt_expect_numLoops_closed (octx : OpCtx) (tvars : List TyIdentifier)
    (imm : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx) (n : Nat)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) :
    expect (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx n) loops
      ≤ ENNReal.ofReal (2 / 17 * (Real.exp (17 / 5) - 1) * ((5 / 17) ^ n * n.factorial)) :=
  le_trans (genStmt_expect_numLoops_le octx tvars imm procs pctx n labels C ctx)
    (by rw [loopBound_eq]; exact ENNReal.ofReal_le_ofReal (loopClosed_le_exp n))

/-- **A tail bound (Markov).** The probability of at least `t` loops is at most the closed-form
expectation divided by `t`. -/
theorem genStmt_prob_numLoops_ge (octx : OpCtx) (tvars : List TyIdentifier)
    (imm : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx) (n : Nat)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (t : ℝ≥0∞) (ht0 : t ≠ 0)
    (htt : t ≠ ⊤) :
    prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx n) {r | t ≤ loops r}
      ≤ ENNReal.ofReal (2 / 17 * (Real.exp (17 / 5) - 1) * ((5 / 17) ^ n * n.factorial)) / t :=
  le_trans (prob_le_expect_div _ _ ht0 htt)
    (ENNReal.div_le_div_right (genStmt_expect_numLoops_closed octx tvars imm procs pctx n labels C ctx) _)

-- ── A rare event: loops nested `n` deep ──────────────────────────────────

mutual

/-- The loop-nesting depth of a statement: the most `loop`s on one path from it to a leaf. -/
def loopDepth : Statement → Nat
  | .loop _ _ _ body _ => loopDepthL body + 1
  | .block _ body _ => loopDepthL body
  | .ite _ thenb elseb _ => max (loopDepthL thenb) (loopDepthL elseb)
  | _ => 0

/-- `loopDepth` maximised over a statement list. -/
def loopDepthL : List Statement → Nat
  | [] => 0
  | s :: ss => max (loopDepth s) (loopDepthL ss)

end

open StrataGenerators.SizeDistribution StrataGenerators.SizeDistributionStmt

theorem sound_true' {α} (g : SPMF α) : IsSoundFor g (fun _ => True) := fun _ _ => trivial

theorem prob_choose_val (m j : Nat) (hj : j ≤ m) (h : 0 ≤ m) :
    1 / ((m : ℝ≥0∞) + 1) ≤
      prob (RandomChoice.choose 0 m h : SPMF (ULift {x : Nat // 0 ≤ x ∧ x ≤ m}))
        {x | x.down.val = j} := by
  refine le_trans ?_ (prob_mono (E := {⟨⟨j, by omega, hj⟩⟩}) ?_)
  · rw [prob_singleton, choose_apply]; simp
  · rintro x rfl; rfl

/-- One `loop` level: a `loop` whose one-statement body is a draw of size `n` satisfying `P`.
The guard is nondeterministic, the measure absent and the invariant list empty, as in
`prob_genStmt_loop_ge`; the body length is `1`. -/
theorem prob_genStmt_loop_body_ge (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx)
    (imm : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (P : Statement → Prop) (B : ℝ≥0∞)
    (hB : B ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx n) (Top P)) :
    2 / 17 * (1 / 5 * (1 / 4 * (1 / ((n : ℝ≥0∞) + 2) * (1 / ((n : ℝ≥0∞) + 2) * B))))
      ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1))
          (Top fun s => ∃ g m i body md, s = .loop g m i body md ∧ ∃ st ∈ body, P st) := by
  rw [genStmt]
  refine le_trans ?_ (prob_frequency_ge _ _ 8 (by simp) _)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  refine mul_le_mul' (le_of_eq (by norm_num)) ?_
  have hc := prob_choose_val (n + 1) 1 (by omega) (Nat.zero_le _)
  push_cast at hc
  rw [show (n : ℝ≥0∞) + 1 + 1 = n + 2 by ring] at hc
  have hi := prob_genInvariants_univ octx tvars pctx ctx (n + 1)
  push_cast at hi
  rw [show (n : ℝ≥0∞) + 1 + 1 = n + 2 by ring] at hi
  refine le_trans (mul_le_mul' (prob_genCondOrNondet_univ octx tvars pctx ctx _) le_rfl)
    (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (mul_le_mul' (prob_genOptMeasure_univ octx tvars pctx ctx _) le_rfl)
    (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (mul_le_mul' hi le_rfl) (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (mul_le_mul' hc le_rfl) (prob_bind_ge _ fun x hx => ?_)
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Set.mem_setOf_eq] at hx; subst hx
  have hch := prob_genStmtChain_top_ge octx tvars pctx P imm procs labels C ctx n 0
  rw [pow_zero, mul_one] at hch
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' (le_trans hB hch) le_rfl)
    (prob_bind_ge (TopChain P) fun t ht => ?_))
  obtain ⟨body, _, _⟩ := t
  refine (prob_pure_of_mem ?_).ge
  exact ⟨_, List.mem_singleton_self _, _, _, _, _, _, rfl, ht⟩

theorem loopDepthL_ge_of_mem {s : Statement} {ss : List Statement} (h : s ∈ ss) :
    loopDepth s ≤ loopDepthL ss := by
  induction ss with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [loopDepthL]; omega
    · have := ih h; simp only [loopDepthL]; omega

/-- The rare-event bound: `1 / (170ᵐ · ((m+1)!)²)`. -/
noncomputable def deepBound (m : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (170 ^ m * ((m + 1).factorial : ℝ) ^ 2))

theorem deepBound_succ_le (n : Nat) :
    deepBound (n + 1) ≤ 2 / 17 * (1 / 5 * (1 / 4 * (1 / ((n : ℝ≥0∞) + 2) *
      (1 / ((n : ℝ≥0∞) + 2) * deepBound n)))) := by
  unfold deepBound
  have hreal : (1 : ℝ) / (170 ^ (n + 1) * ((n + 1 + 1).factorial : ℝ) ^ 2)
      = 2 / 17 * (1 / 5 * (1 / 4 * (1 / ((n : ℝ) + 2) * (1 / ((n : ℝ) + 2) *
          (1 / (170 ^ n * ((n + 1).factorial : ℝ) ^ 2)))))) := by
    rw [Nat.factorial_succ (n + 1)]
    have : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [hreal]
  repeat rw [ENNReal.ofReal_mul (by positivity)]
  gcongr <;> (apply le_of_eq; rw [ENNReal.ofReal_div_of_pos (by positivity)]; simp [ENNReal.ofReal_add])

/-- **Loops nested `m` deep are possible at size `m`, but rare.** For every `m ≥ 1`, in every
context, a draw of `genStmt … m` holds a statement of loop depth at least `m` with probability at
least `1 / (170ᵐ · ((m+1)!)²)`. -/
theorem genStmt_prob_loopDepth_ge (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx)
    (imm : List (Identifier Unit)) (procs : ProcSigCtx) :
    ∀ (n : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx),
      deepBound (n + 1) ≤ prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (n + 1))
        (Top fun s => n + 1 ≤ loopDepth s) := by
  intro n
  induction n with
  | zero =>
    intro labels C ctx
    refine le_trans ?_ (le_trans (prob_genStmt_loop_ge octx tvars pctx imm procs labels C ctx 0)
      (prob_mono ?_))
    · unfold deepBound
      have h680 : (1 : ℝ) / (170 ^ (0 + 1) * (((0 + 1 + 1).factorial : ℕ) : ℝ) ^ 2) = 1 / 680 := by
        norm_num [Nat.factorial]
      have hl0 : loopAtSize 0 = 1 / 680 := by
        rw [loopAtSize]; norm_num
      rw [h680, hl0, ENNReal.ofReal_div_of_pos (by norm_num)]
      simp only [ENNReal.ofReal_one]
      rw [show ENNReal.ofReal 680 = 680 by simp]
    · rintro r ⟨st, hst, hl⟩
      refine ⟨st, hst, ?_⟩
      cases st <;> simp_all [IsLoop, loopDepth]
  | succ n ih =>
    intro labels C ctx
    refine le_trans (deepBound_succ_le (n + 1)) ?_
    refine le_trans (prob_genStmt_loop_body_ge octx tvars pctx imm procs labels C ctx (n + 1)
      (fun s => n + 1 ≤ loopDepth s) _ (ih labels C ctx)) (prob_mono ?_)
    rintro r ⟨st, hst, g, m, i, body, md, rfl, b, hb, hlb⟩
    refine ⟨_, hst, ?_⟩
    have := loopDepthL_ge_of_mem hb
    simp only [loopDepth]
    push_cast at hlb ⊢
    omega

-- ── The loop depth is bounded by the size ────────────────────────────────

theorem loopDepth_of_not_nesting {s : Statement} (h : ¬ IsNesting s) : loopDepth s = 0 := by
  cases s <;> simp_all [IsNesting, loopDepth]

theorem loopDepthL_eq_zero {ss : List Statement} (h : ∀ s ∈ ss, ¬ IsNesting s) :
    loopDepthL ss = 0 := by
  induction ss with
  | nil => rfl
  | cons x xs ih =>
    simp only [loopDepthL, loopDepth_of_not_nesting (h x (by simp)),
      ih fun s hs => h s (by simp [hs])]
    rfl

theorem loopDepthL_append (ss ts : List Statement) :
    loopDepthL (ss ++ ts) = max (loopDepthL ss) (loopDepthL ts) := by
  induction ss with
  | nil => simp [loopDepthL]
  | cons x xs ih => simp only [List.cons_append, loopDepthL, ih]; omega

theorem flat_depth {g : SPMF GenStmtResult} (h : IsSoundFor g (fun r => ¬ HasNesting r)) :
    IsSoundFor g (fun r => loopDepthL r.stmts = 0) :=
  fun r hr => loopDepthL_eq_zero fun s hs hn => h r hr ⟨s, hs, hn⟩

theorem genStmtChain_depth (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx)
    (imm : List (Identifier Unit)) (procs : ProcSigCtx) (size : Nat)
    (ih : ∀ labels C ctx, IsSoundFor (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx size)
      (fun r => loopDepthL r.stmts ≤ size)) :
    ∀ (len : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx),
      IsSoundFor (genStmtChain (G := SPMF) octx tvars imm procs labels C ctx pctx size len)
        (fun t => loopDepthL t.1 ≤ size) := by
  intro len
  induction len with
  | zero =>
    intro labels C ctx t ht
    rw [genStmtChain_zero, mem_support_pure_iff] at ht
    subst ht; simp [loopDepthL]
  | succ len ihl =>
    intro labels C ctx t ht
    rw [genStmtChain] at ht
    simp only [mem_support_bind_iff, mem_support_pure_iff] at ht
    obtain ⟨r, hr, ⟨rest, C'', ctx''⟩, hrest, rfl⟩ := ht
    have h1 := ih labels C ctx r hr
    have h2 := ihl labels _ _ _ hrest
    dsimp only at h2 ⊢
    simp only [loopDepthL_append]; omega

/-- **The loop depth of a draw of `genStmt … size` is at most `size`**, in every context. -/
theorem genStmt_depth (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx)
    (imm : List (Identifier Unit)) (procs : ProcSigCtx) :
    ∀ (size : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx),
      IsSoundFor (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx size)
        (fun r => loopDepthL r.stmts ≤ size) := by
  intro size
  induction size with
  | zero =>
    intro labels C ctx r hr
    rw [flat_depth (genStmt_zero_flat octx tvars pctx imm procs labels C ctx) r hr]
  | succ size ih =>
    intro labels C ctx
    have hch := genStmtChain_depth octx tvars pctx imm procs size ih
    rw [IsSoundFor.iff_obs, genStmt]
    walk [(flat_depth (genCmdStmt_flat octx tvars pctx _ _ _ _)).obs,
      (flat_depth (genExitStmt_flat _ _ _)).obs,
      (flat_depth (genFuncDeclStmt_flat octx pctx _ _ _)).obs,
      (flat_depth (genTypeDeclStmt_flat _ _ _)).obs,
      (flat_depth (genCallStmt_flat octx tvars pctx _ _ _ _ _)).obs,
      (hch _ _ _ _).obs, (sound_true' (genFreshLabel _)).obs,
      (sound_true' (genLExpr _ _ _ _ _ _ _ _ _)).obs,
      (sound_true' (genCondOrNondet _ _ _ _ _)).obs, (sound_true' (genOptMeasure _ _ _ _ _)).obs,
      (sound_true' (genInvariants _ _ _ _ _)).obs]
    all_goals (first | omega | (simp only [loopDepthL, loopDepth] at *; omega))

-- ── Deep loops are rare: an upper bound ──────────────────────────────────

theorem prob_le_zero_of_sound {α} {g : SPMF α} {E : Set α} (h : IsSoundFor g (fun a => a ∉ E)) :
    prob g E ≤ 0 :=
  le_of_eq ((prob_eq_zero_iff _ _).mpr fun a ha => h a ha)

theorem prob_bind_le {α β} {x : SPMF α} {f : α → SPMF β} {E : Set β} {c : ℝ≥0∞}
    (h : ∀ a, prob (f a) E ≤ c) : prob (x >>= f) E ≤ c := by
  rw [prob_bind]
  calc expect x (fun a => prob (f a) E) ≤ expect x (fun _ => c) := expect_mono h
    _ = x.mass * c := expect_const _ _
    _ ≤ 1 * c := by gcongr; exact mass_le_one _
    _ = c := one_mul c

theorem prob_pure_le_indicator {α} (a : α) (E : Set α) :
    prob (Pure.pure a : SPMF α) E ≤ E.indicator 1 a := by
  classical
  rw [prob_pure]; by_cases h : a ∈ E <;> simp [h]

theorem exists_deep_of_loopDepthL {k : Nat} (hk : 1 ≤ k) :
    ∀ {ss : List Statement}, k ≤ loopDepthL ss → ∃ s ∈ ss, k ≤ loopDepth s
  | [], h => by simp [loopDepthL] at h; omega
  | s :: ss, h => by
    simp only [loopDepthL] at h
    by_cases hs : k ≤ loopDepth s
    · exact ⟨s, by simp, hs⟩
    · obtain ⟨t, ht, hkt⟩ := exists_deep_of_loopDepthL hk (ss := ss) (by omega)
      exact ⟨t, by simp [ht], hkt⟩

/-- **The union bound over a chain.** A chain of `len` groups has a top-level statement satisfying
`P` with probability at most `len` times the bound for one group. -/
theorem prob_genStmtChain_top_le (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx)
    (imm : List (Identifier Unit)) (procs : ProcSigCtx) (size : Nat) (P : Statement → Prop)
    (B : ℝ≥0∞)
    (hB : ∀ labels C ctx, prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx size)
      (Top P) ≤ B) :
    ∀ (len : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx),
      prob (genStmtChain (G := SPMF) octx tvars imm procs labels C ctx pctx size len) (TopChain P)
        ≤ len * B := by
  classical
  intro len
  induction len with
  | zero =>
    intro labels C ctx
    rw [genStmtChain_zero]
    refine le_trans (prob_pure_le_indicator _ _) ?_
    simp [TopChain]
  | succ len ih =>
    intro labels C ctx
    rw [genStmtChain, prob_bind]
    calc expect _ (fun r => prob (_ >>= _) (TopChain P))
        ≤ expect (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx size)
            (fun r => (Top P).indicator 1 r + len * B) := by
          refine expect_mono fun r => ?_
          by_cases hr : r ∈ Top P
          · simp only [Set.indicator_of_mem hr, Pi.one_apply]
            exact le_trans (prob_le_mass _ _) (le_trans (mass_le_one _) le_self_add)
          · simp only [Set.indicator_of_notMem hr, zero_add]
            rw [prob_bind]
            refine le_trans (expect_mono (g := (TopChain P).indicator 1) fun t => ?_) ?_
            · obtain ⟨rest, C'', ctx''⟩ := t
              refine le_trans (prob_pure_le_indicator _ _) ?_
              by_cases ht : (r.stmts ++ rest, C'', ctx'') ∈ TopChain P
              · obtain ⟨s, hs, hP⟩ := ht
                rcases List.mem_append.mp hs with hs | hs
                · exact absurd (show r ∈ Top P from ⟨s, hs, hP⟩) hr
                · rw [Set.indicator_of_mem (show (rest, C'', ctx'') ∈ TopChain P from ⟨s, hs, hP⟩)]
                  exact Set.indicator_le (fun _ _ => le_rfl) _
              · simp [Set.indicator_of_notMem ht]
            · exact ih _ _ _
      _ ≤ B + len * B := by
          rw [expect_add]
          gcongr
          · exact hB labels C ctx
          · calc expect _ (fun _ => (len : ℝ≥0∞) * B) = _ * _ := expect_const _ _
              _ ≤ 1 * ((len : ℝ≥0∞) * B) := by gcongr; exact mass_le_one _
              _ = _ := one_mul _
      _ = ((len + 1 : ℕ) : ℝ≥0∞) * B := by push_cast; ring

/-- The upper bound on a loop nest of depth `m` at size `m`: `2 · m! / 17ᵐ`. -/
noncomputable def deepUpper (m : Nat) : ℝ≥0∞ := ENNReal.ofReal (2 * m.factorial / 17 ^ m)

theorem deepUpper_succ (m : Nat) :
    deepUpper (m + 1) = ((m + 1 : ℕ) : ℝ≥0∞) * deepUpper m / 17 := by
  unfold deepUpper
  have hreal : (2 * ((m + 1).factorial : ℝ) / 17 ^ (m + 1))
      = ((m + 1 : ℕ) : ℝ) * (2 * (m.factorial : ℝ) / 17 ^ m) / 17 := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hreal, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_mul (by positivity)]
  simp [ENNReal.ofReal_add]

/-- Close a `walk` leaf: a result whose top statements all have loop depth below `k + 1`. -/
macro "shallow_close" : tactic => `(tactic| (
  first
    | (rintro ⟨s, hs, hsd⟩
       have := loopDepthL_ge_of_mem hs
       omega)
    | (rintro ⟨s, hs, hsd⟩
       simp only [List.mem_singleton] at hs
       subst hs
       simp only [loopDepth, le_max_iff] at hsd
       omega)))

/-- Split the `frequency` of `genStmt` at size `k + 1` for a deep-loop event: the eight branches
other than `loop` have probability `0` (their outputs are shallow), the `loop` branch is bounded by
`X`, and the remaining goal is the arithmetic over the weights. -/
macro "deep_branches " hch:term ", " X:term : tactic => `(tactic| (
  refine le_trans (ENNReal.div_le_div_right
    (add_le_add (mul_le_mul_right (?b0 : _ ≤ (0 : ℝ≥0∞)) _)
    (add_le_add (mul_le_mul_right (?b1 : _ ≤ (0 : ℝ≥0∞)) _)
    (add_le_add (mul_le_mul_right (?b2 : _ ≤ (0 : ℝ≥0∞)) _)
    (add_le_add (mul_le_mul_right (?b3 : _ ≤ (0 : ℝ≥0∞)) _)
    (add_le_add (mul_le_mul_right (?b4 : _ ≤ (0 : ℝ≥0∞)) _)
    (add_le_add (mul_le_mul_right (?b5 : _ ≤ (0 : ℝ≥0∞)) _)
    (add_le_add (mul_le_mul_right (?b6 : _ ≤ (0 : ℝ≥0∞)) _)
    (add_le_add (mul_le_mul_right (?b7 : _ ≤ (0 : ℝ≥0∞)) _)
    (add_le_add (mul_le_mul_right (?b8 : _ ≤ $X) _) le_rfl))))))))) _) ?fin
  case b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7 =>
    exact prob_le_zero_of_sound (by
      rw [IsSoundFor.iff_obs]
      walk [(flat_depth (genCmdStmt_flat _ _ _ _ _ _ _)).obs,
        (flat_depth (genExitStmt_flat _ _ _)).obs,
        (flat_depth (genFuncDeclStmt_flat _ _ _ _ _)).obs,
        (flat_depth (genTypeDeclStmt_flat _ _ _)).obs,
        (flat_depth (genCallStmt_flat _ _ _ _ _ _ _ _)).obs,
        ($hch _ _ _ _).obs, (sound_true' (genFreshLabel _)).obs,
        (sound_true' (genLExpr _ _ _ _ _ _ _ _ _)).obs]
      all_goals shallow_close)))

/-- **Loops nested `m` deep at size `m` are rare: probability at most `2 · m! / 17ᵐ`**, in every
context. With `genStmt_prob_loopDepth_ge` this brackets the probability between
`1 / (170ᵐ · ((m+1)!)²)` and `2 · m! / 17ᵐ`. -/
theorem genStmt_prob_loopDepth_le (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx)
    (imm : List (Identifier Unit)) (procs : ProcSigCtx) :
    ∀ (k : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx),
      prob (genStmt (G := SPMF) octx tvars imm procs labels C ctx pctx (k + 1))
        (Top fun s => k + 1 ≤ loopDepth s) ≤ deepUpper (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro labels C ctx
    rw [genStmt, prob_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    deep_branches (genStmtChain_depth octx tvars pctx imm procs 0
      (genStmt_depth octx tvars pctx imm procs 0)), (1 : ℝ≥0∞)
    · exact le_trans (prob_le_mass _ _) (mass_le_one _)
    · have h1 : deepUpper (0 + 1) = 2 / 17 := by
        unfold deepUpper
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp
      rw [h1]
      apply le_of_eq
      norm_num
  | succ k ih =>
    intro labels C ctx
    rw [genStmt, prob_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    deep_branches (genStmtChain_depth octx tvars pctx imm procs (k + 1)
      (genStmt_depth octx tvars pctx imm procs (k + 1))),
      ((((k + 1 + 1 : ℕ) : ℝ≥0∞) / 2) * deepUpper (k + 1))
    · refine prob_bind_le fun _ => ?_
      refine prob_bind_le fun _ => ?_
      refine prob_bind_le fun _ => ?_
      rw [prob_bind]
      refine le_trans (expect_mono (g := fun p => (p.down.val : ℝ≥0∞) * deepUpper (k + 1))
        fun p => ?_) (le_of_eq (expect_choose_mul _ _))
      rw [prob_bind]
      refine le_trans (expect_mono
        (g := (TopChain fun s => k + 1 ≤ loopDepth s).indicator 1) fun t => ?_) ?_
      · refine le_trans (prob_pure_le_indicator _ _) ?_
        by_cases ht : t ∈ TopChain fun s => k + 1 ≤ loopDepth s
        · rw [Set.indicator_of_mem ht]; exact Set.indicator_le (fun _ _ => le_rfl) _
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem]
          rintro ⟨s, hs, hsd⟩
          simp only [List.mem_singleton] at hs
          subst hs
          simp only [loopDepth] at hsd
          exact ht (exists_deep_of_loopDepthL (by omega) (by omega))
      · exact prob_genStmtChain_top_le octx tvars pctx imm procs (k + 1) _ _ ih _ labels C ctx
    · rw [deepUpper_succ (k + 1)]
      simp only [mul_zero, zero_add, add_zero]
      have h2 : (2 : ℝ≥0∞) * (((k + 1 + 1 : ℕ) : ℝ≥0∞) / 2 * deepUpper (k + 1))
          = ((k + 1 + 1 : ℕ) : ℝ≥0∞) * deepUpper (k + 1) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
      rw [show ((2 : ℕ) : ℝ≥0∞) = 2 from rfl, h2]
      apply le_of_eq
      norm_num

end StrataGenerators.SizeDistributionLoops
