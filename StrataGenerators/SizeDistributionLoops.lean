import StrataGenerators.SizeDistributionStmt
import StrataGenerators.TuningPrototypes
import StrataGenerators.HasTypeAGen.IndirSupport
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Nested statements and loops as a function of the size, the weights and the body-length cap

Every statement here is about `genStmtT θ … n maxStmtSeqLen`, the statement generator with its
branch weights read from `θ` through the whole mutual recursion, for **every** `θ`, every size `n`
and every body-length cap `maxStmtSeqLen`, in every context. The shipping generator is the case
`θ = stmtDefault` (`genStmtT_defaults`, by `rfl`), and the `_default` corollaries state it with
numerals.

## The two quantities

Write `w₀, …, w₇` for the weights of the `size + 1` site of `genStmt` (`cmd`, `exit`, `typeDecl`,
`call`, `block`, deterministic `ite`, nondeterministic `ite`, `loop`) and `W` for their sum. Two
quantities control every bound:

* `loopShare θ = w₇ / W`, the share of the weight that the `loop` branch holds at size `n + 1`.
  The probability of a `loop` is at most this, because a sub-draw of the branch can fail.
* `expectedChildStmts maxStmtSeqLen θ = (w₄ + 2 w₅ + 2 w₆ + w₇) / W · maxStmtSeqLen / 2`, the
  expected number of statement draws one level down that one statement draw makes. The numerator
  counts the bodies that each branch opens (an `ite` opens two), and `maxStmtSeqLen / 2` is the mean
  of a body length uniform on `[0, maxStmtSeqLen]`.

## Expected counts

`genStmtT_expect_count_le` bounds the expected number of nested statements (at every depth) by the
solution of `B 0 = 0`, `B (n + 1) = nestShare c θ + r · B n`, with `r = expectedChildStmts`. The closed form
(`countBound_eq`) is a geometric sum:

```
E[#loops] ≤ loopShare θ · (1 + r + r² + … + r^{n-1})
```

and so (`genStmtT_expect_numLoops_le_geom`)

```
E[#loops] ≤ loopShare θ / (1 − r)        (every n; finite exactly when r < 1)
```

The same holds for the number of `block`, `ite` and `loop` statements together, with the share
`nestingShare θ = (w₄ + w₅ + w₆ + w₇) / W` in place of `loopShare θ`.

At the shipping weights `loopShare = 1/16` and `r = 3 · maxStmtSeqLen / 16`. At the default cap
`maxStmtSeqLen = 5`, `r = 15/16`: `genStmt_expect_numLoops_le_one` says that the expected number of
loops is at most `1` at every size, and `genStmt_expect_numNesting_le` that the expected number of
nested statements is at most `4`. These two corollaries are about the shipping weights only. A
tuning profile `θ` has its own `r`, and the geometric bound is finite only if that `r` is less than
`1`. A cap of `6` or more at the shipping weights gives `r > 1`, and then the upper bound grows like
`rⁿ`. No theorem here shows that the expected count itself grows.

**Every profile, at its own cap.** The tuned entry points use the cap `maxStmtSeqLenFor θ` by
default: the largest cap, at most `5`, with `r < 1` (`expectedChildStmts_maxStmtSeqLenFor_lt_one`).
So `genStmtT_expect_numNesting_finite` gives a finite bound on the expected nesting of one
statement draw for every profile, at every size.

All the bounds are upper bounds on the count of `block`, `ite` and `loop` statements. They say
nothing about the size of the expressions, which still grows with `n`. The length of an invariant
list, like the length of a nested body, is at most `maxStmtSeqLen`.

**Why only upper bounds.** A leaf generator can fail, so sub-draws have mass `< 1` and nothing
here computes those masses exactly. Upper bounds need only `mass ≤ 1`.
-/

namespace StrataGenerators.SizeDistributionLoops

open Lambda Core Imperative RandomChoice SPMF NNReal ENNReal
open StrataGenerators StrataGenerators.Stmt StrataGenerators.IndirSupport
open StrataGenerators.TuningProfiles

-- ── Unfolding the tuned statement generator ──────────────────────────────

/-! `genStmtT θ` is a projection of `genStmt._mutual.tuned`, a `WellFounded.fix` with no equation
lemmas. `WellFounded.fix_eq` unfolds it one step; the result is `genStmt`'s body with each weight
read from `θ` at depth `0` and each recursive call tuned. -/

theorem genStmtT_zero [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (maxStmtSeqLen : Nat) :
    genStmtT (G := G) θ octx tvars immutableVars procs labels C ctx pctx 0 maxStmtSeqLen =
    frequency
      [ (θ.weight 0 0, fun () => genCmdStmt octx tvars immutableVars C ctx 0 pctx),
        (θ.weight 1 0, fun () =>
          if labels.isEmpty then genCmdStmt octx tvars immutableVars C ctx 0 pctx
          else genExitStmt labels C ctx),
        (θ.weight 2 0, fun () => genTypeDeclStmt C ctx 0),
        (θ.weight 3 0, fun () =>
          if procs.isEmpty then genCmdStmt octx tvars immutableVars C ctx 0 pctx
          else genCallStmt octx tvars immutableVars procs C ctx 0 pctx) ]
      (Tuning.sum_map_fst_pos θ 0 0 _ _) := by
  unfold genStmtT
  delta genStmt._mutual.tuned
  rw [WellFounded.fix_eq]
  try rfl

theorem genStmtT_succ [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size maxStmtSeqLen : Nat) :
    genStmtT (G := G) θ octx tvars immutableVars procs labels C ctx pctx (size + 1) maxStmtSeqLen =
    frequency
      [ (θ.weight 4 0, fun () => genCmdStmt octx tvars immutableVars C ctx (size + 1) pctx),
        (θ.weight 5 0, fun () =>
          if labels.isEmpty then genCmdStmt octx tvars immutableVars C ctx (size + 1) pctx
          else genExitStmt labels C ctx),
        (θ.weight 6 0, fun () => genTypeDeclStmt C ctx (size + 1)),
        (θ.weight 7 0, fun () =>
          if procs.isEmpty then genCmdStmt octx tvars immutableVars C ctx (size + 1) pctx
          else genCallStmt octx tvars immutableVars procs C ctx (size + 1) pctx),
        (θ.weight 8 0, fun () => do
          let label ← genFreshLabel labels
          let ⟨⟨len, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
          let (body, _, _) ← genStmtChainT θ octx tvars immutableVars procs (label :: labels) C ctx
            pctx size len maxStmtSeqLen
          pure ⟨[Stmt.block label body default], C, ctx⟩),
        (θ.weight 9 0, fun () => do
          let cond ← genLExpr ctx.toFVarCtx octx pctx tvars [] (size + 1) .bool
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
          let (thenb, _, _) ← genStmtChainT θ octx tvars immutableVars procs labels C ctx pctx size
            tlen maxStmtSeqLen
          let (elseb, _, _) ← genStmtChainT θ octx tvars immutableVars procs labels C ctx pctx size
            elen maxStmtSeqLen
          pure ⟨[Stmt.ite (.det cond) thenb elseb default], C, ctx⟩),
        (θ.weight 10 0, fun () => do
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
          let (thenb, _, _) ← genStmtChainT θ octx tvars immutableVars procs labels C ctx pctx size
            tlen maxStmtSeqLen
          let (elseb, _, _) ← genStmtChainT θ octx tvars immutableVars procs labels C ctx pctx size
            elen maxStmtSeqLen
          pure ⟨[Stmt.ite .nondet thenb elseb default], C, ctx⟩),
        (θ.weight 11 0, fun () => do
          let guard ← genCondOrNondet octx tvars ctx (size + 1) pctx
          let measure ← genOptMeasure octx tvars ctx (size + 1) pctx
          let invariants ← genInvariants octx tvars ctx maxStmtSeqLen (size + 1) pctx
          let ⟨⟨blen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
          let (body, _, _) ← genStmtChainT θ octx tvars immutableVars procs labels C ctx pctx size
            blen maxStmtSeqLen
          pure ⟨[Stmt.loop guard measure invariants body default], C, ctx⟩) ]
      (Tuning.sum_map_fst_pos θ 4 0 _ _) := by
  unfold genStmtT
  delta genStmt._mutual.tuned
  rw [WellFounded.fix_eq]
  try rfl

theorem genStmtChainT_zero [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size maxStmtSeqLen : Nat) :
    genStmtChainT (G := G) θ octx tvars immutableVars procs labels C ctx pctx size 0 maxStmtSeqLen
      = Pure.pure ([], C, ctx) := by
  unfold genStmtChainT
  delta genStmt._mutual.tuned
  rw [WellFounded.fix_eq]
  try rfl

theorem genStmtChainT_succ [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size len maxStmtSeqLen : Nat) :
    genStmtChainT (G := G) θ octx tvars immutableVars procs labels C ctx pctx size (len + 1)
        maxStmtSeqLen = (do
      let r ← genStmtT θ octx tvars immutableVars procs labels C ctx pctx size maxStmtSeqLen
      let (rest, C'', ctx'') ←
        genStmtChainT θ octx tvars immutableVars procs labels r.outC r.outCtx pctx size len
          maxStmtSeqLen
      Pure.pure (r.stmts ++ rest, C'', ctx'')) := by
  unfold genStmtChainT
  delta genStmt._mutual.tuned
  rw [WellFounded.fix_eq]
  try rfl

-- ── Counting nested statements ───────────────────────────────────────────

/-- What a nested statement adds to a count: `block` for a `block`, `ite` for each `ite` and `loop`
for a `loop`. A leaf statement adds nothing. -/
structure NestCost where
  block : Nat
  ite : Nat
  loop : Nat

/-- Count the `loop` statements only. -/
def loopCost : NestCost := ⟨0, 0, 1⟩

/-- Count every nested statement: each `block`, `ite` and `loop`. -/
def nestingCost : NestCost := ⟨1, 1, 1⟩

mutual

/-- The count of the nested statements in a statement, at every nesting depth, weighted by `c`. -/
def nestCount (c : NestCost) : Statement → Nat
  | .loop _ _ _ body _ => c.loop + nestCountL c body
  | .block _ body _ => c.block + nestCountL c body
  | .ite _ thenb elseb _ => c.ite + nestCountL c thenb + nestCountL c elseb
  | .cmd _ => 0
  | .exit _ _ => 0
  | .typeDecl _ _ => 0

/-- `nestCount` summed over a statement list. -/
def nestCountL (c : NestCost) : List Statement → Nat
  | [] => 0
  | s :: ss => nestCount c s + nestCountL c ss

end

@[simp]
theorem nestCountL_nil (c : NestCost) : nestCountL c [] = 0 := rfl

@[simp]
theorem nestCountL_cons (c : NestCost) (s : Statement) (ss : List Statement) :
    nestCountL c (s :: ss) = nestCount c s + nestCountL c ss := rfl

@[simp]
theorem nestCountL_append (c : NestCost) (ss ts : List Statement) :
    nestCountL c (ss ++ ts) = nestCountL c ss + nestCountL c ts := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp [ih, Nat.add_assoc]

/-- A statement list of commands only holds no nested statement. -/
theorem nestCountL_eq_zero_of_all_cmd (c : NestCost) {ss : List Statement}
    (h : ∀ s ∈ ss, ∃ c, s = .cmd c) : nestCountL c ss = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    obtain ⟨c', rfl⟩ := h s (by simp)
    simp only [nestCountL_cons, nestCount, Nat.zero_add]
    exact ih fun t ht => h t (by simp [ht])

/-- The `init` chain that a call group prefixes is all commands. -/
@[simp]
theorem nestCountL_initChain (c : NestCost) (news : List (Identifier Unit × LMonoTy)) :
    nestCountL c (StrataGenerators.Stmt.initChain news) = 0 := by
  refine nestCountL_eq_zero_of_all_cmd c fun s hs => ?_
  simp only [StrataGenerators.Stmt.initChain, List.mem_map] at hs
  obtain ⟨p, _, rfl⟩ := hs
  exact ⟨_, rfl⟩

-- ── The leaf branches contribute nothing ─────────────────────────────────

section Leaves

variable (c : NestCost)

theorem genCmdStmt_count (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (C : LContext CoreLParams) (ctx : VarCtx)
    (depth : Nat) (pctx : PolyOpCtx) (r : GenStmtResult)
    (hr : r ∈ support (genCmdStmt (G := SPMF) octx tvars immutableVars C ctx depth pctx)) :
    nestCountL c r.stmts = 0 := by
  simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

theorem genExitStmt_count (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
    (r : GenStmtResult) (hr : r ∈ support (genExitStmt (G := SPMF) labels C ctx)) :
    nestCountL c r.stmts = 0 := by
  cases labels with
  | nil => simp only [genExitStmt, mem_support_bot_iff] at hr
  | cons l ls =>
    simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    rfl

theorem genTypeDeclStmt_count (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat)
    (r : GenStmtResult) (hr : r ∈ support (genTypeDeclStmt (G := SPMF) C ctx depth)) :
    nestCountL c r.stmts = 0 := by
  simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
  obtain ⟨_, _, hr⟩ := hr
  split at hr
  · simp only [mem_support_pure_iff] at hr; subst hr; rfl
  · simp only [mem_support_bot_iff] at hr

theorem genCallStmt_count (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx)
    (r : GenStmtResult)
    (hr : r ∈ support (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx depth pctx)) :
    nestCountL c r.stmts = 0 := by
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
        simp only [nestCountL_append, nestCountL_initChain, nestCountL_cons, nestCountL_nil]
        rfl
      · simp only [mem_support_bot_iff] at hr
    · simp only [mem_support_bot_iff] at hr

end Leaves

-- ── The weights and the two quantities ───────────────────────────────────

/-- The weight of branch `j` of the `size + 1` site of `genStmt` under `θ`. The site starts at flat
index `4` and `genStmt` reads its weights at depth `0`. Branches: `0` `cmd`, `1` `exit`,
`2` `typeDecl`, `3` `call`, `4` `block`, `5` deterministic `ite`, `6` nondeterministic `ite`,
`7` `loop`. -/
noncomputable def stmtWeight (θ : Tuning) (j : Nat) : ℝ≥0∞ := (θ.weight (4 + j) 0 : ℝ≥0∞)

/-- The total weight `W` of the `size + 1` site. -/
noncomputable def stmtTotalWeight (θ : Tuning) : ℝ≥0∞ :=
  stmtWeight θ 0 + stmtWeight θ 1 + stmtWeight θ 2 + stmtWeight θ 3 +
    stmtWeight θ 4 + stmtWeight θ 5 + stmtWeight θ 6 + stmtWeight θ 7

/-- The share of a statement draw at size `n + 1` that a count with costs `c` charges at the top:
`(c.block · w₄ + c.ite · (w₅ + w₆) + c.loop · w₇) / W`. -/
noncomputable def nestShare (c : NestCost) (θ : Tuning) : ℝ≥0∞ :=
  ((c.block : ℝ≥0∞) * stmtWeight θ 4 + (c.ite : ℝ≥0∞) * stmtWeight θ 5 +
    (c.ite : ℝ≥0∞) * stmtWeight θ 6 + (c.loop : ℝ≥0∞) * stmtWeight θ 7) / stmtTotalWeight θ

/-- **The loop share.** The share of the weight that the `loop` branch holds at size `n + 1`:
`w₇ / W`. It is the probability that `frequency` selects the branch. The probability that the draw
is a `loop` is at most this, because a sub-draw of the branch can fail. -/
noncomputable def loopShare (θ : Tuning) : ℝ≥0∞ := stmtWeight θ 7 / stmtTotalWeight θ

/-- The share of the weight that the nested branches (`block`, `ite` and `loop`) hold at size
`n + 1`: `(w₄ + w₅ + w₆ + w₇) / W`. -/
noncomputable def nestingShare (θ : Tuning) : ℝ≥0∞ :=
  (stmtWeight θ 4 + stmtWeight θ 5 + stmtWeight θ 6 + stmtWeight θ 7) / stmtTotalWeight θ

/-- The expected number of bodies that one statement draw at size `n + 1` opens:
`(w₄ + 2 w₅ + 2 w₆ + w₇) / W`. A `block` and a `loop` open one body, and each `ite` opens two. -/
noncomputable def bodiesPerStmt (θ : Tuning) : ℝ≥0∞ :=
  (stmtWeight θ 4 + 2 * stmtWeight θ 5 + 2 * stmtWeight θ 6 + stmtWeight θ 7) / stmtTotalWeight θ

/-- **The expected number of child statements**, the branching factor `r` of the statement
recursion: the expected number of statement draws one level down that one statement draw at size
`n + 1` makes. It is `bodiesPerStmt θ` times the mean body length `maxStmtSeqLen / 2`, because each
body length is uniform on `[0, maxStmtSeqLen]`. The expected count of nested statements stays
bounded in the size exactly when this is less than `1`. -/
noncomputable def expectedChildStmts (maxStmtSeqLen : Nat) (θ : Tuning) : ℝ≥0∞ :=
  bodiesPerStmt θ * ((maxStmtSeqLen : ℝ≥0∞) / 2)

theorem nestShare_loopCost (θ : Tuning) : nestShare loopCost θ = loopShare θ := by
  simp [nestShare, loopShare, loopCost]

theorem nestShare_nestingCost (θ : Tuning) : nestShare nestingCost θ = nestingShare θ := by
  simp [nestShare, nestingShare, nestingCost]

/-- The bound on the expected count of `genStmtT θ … n maxStmtSeqLen`, as a recurrence in `n`: no
nested statement at size `0`, and at size `n + 1` the share charged at the top plus `r` copies of
the bound one level down. -/
noncomputable def countBound (c : NestCost) (maxStmtSeqLen : Nat) (θ : Tuning) : Nat → ℝ≥0∞
  | 0 => 0
  | n + 1 => nestShare c θ + expectedChildStmts maxStmtSeqLen θ * countBound c maxStmtSeqLen θ n

-- ── Expectation plumbing ─────────────────────────────────────────────────

/-- The count of a draw, as a feature of the result. -/
noncomputable def count (c : NestCost) (r : GenStmtResult) : ℝ≥0∞ := (nestCountL c r.stmts : ℝ≥0∞)

/-- The count of a chain's result. -/
noncomputable def countChain (c : NestCost) (t : List Statement × LContext CoreLParams × VarCtx) :
    ℝ≥0∞ :=
  (nestCountL c t.1 : ℝ≥0∞)

/-- A generator whose every draw has count `0` has expected count `0`. -/
theorem expect_count_eq_zero (c : NestCost) {g : SPMF GenStmtResult}
    (h : ∀ r ∈ support g, nestCountL c r.stmts = 0) : expect g (count c) = 0 :=
  le_antisymm (expect_le_of_support fun r hr => by simp [count, h r hr]) (zero_le)

theorem genStmt_leaf_expect (c : NestCost) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (depth : Nat) :
    expect (genCmdStmt (G := SPMF) octx tvars immutableVars C ctx depth pctx) (count c) = 0
    ∧ expect (if labels.isEmpty then genCmdStmt (G := SPMF) octx tvars immutableVars C ctx depth pctx
        else genExitStmt (G := SPMF) labels C ctx) (count c) = 0
    ∧ expect (genTypeDeclStmt (G := SPMF) C ctx depth) (count c) = 0
    ∧ expect (if procs.isEmpty then genCmdStmt (G := SPMF) octx tvars immutableVars C ctx depth pctx
        else genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx depth pctx)
          (count c) = 0 := by
  refine ⟨expect_count_eq_zero c (genCmdStmt_count c _ _ _ _ _ _ _), ?_,
    expect_count_eq_zero c (genTypeDeclStmt_count c _ _ _), ?_⟩
  · split
    · exact expect_count_eq_zero c (genCmdStmt_count c _ _ _ _ _ _ _)
    · exact expect_count_eq_zero c (genExitStmt_count c _ _ _)
  · split
    · exact expect_count_eq_zero c (genCmdStmt_count c _ _ _ _ _ _ _)
    · exact expect_count_eq_zero c (genCallStmt_count c _ _ _ _ _ _ _ _)

/-- A draw whose continuation is bounded by a constant, whatever it draws. `mass ≤ 1` is what
makes this an inequality and not an equality: a sub-draw that fails contributes nothing. -/
theorem expect_bind_const_le {α β : Type} (g : SPMF α) (h : α → SPMF β) (u : β → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : ∀ a, expect (h a) u ≤ c) : expect (g >>= h) u ≤ c := by
  rw [expect_bind]
  calc expect g (fun a => expect (h a) u) ≤ expect g (fun _ => c) := expect_mono hc
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

/-- **Averaging a body-length-linear bound over the uniform body length.** A bound `a + len * L` on
each `len` averages to `a + (m/2) * L`, because `choose 0 m` has mean `m/2`. -/
theorem expect_choose_le (m : Nat) (f : ULift {x : Nat // 0 ≤ x ∧ x ≤ m} → ℝ≥0∞) (a L : ℝ≥0∞)
    (hf : ∀ p, f p ≤ a + (p.down.val : ℝ≥0∞) * L) :
    expect (choose 0 m (Nat.zero_le m) : SPMF _) f ≤ a + (m : ℝ≥0∞) / 2 * L := by
  refine le_trans (expect_mono hf) ?_
  rw [expect_add, expect_choose_mul]
  gcongr
  calc expect (choose 0 m (Nat.zero_le m) : SPMF _) (fun _ => a) = _ * a := expect_const _ _
    _ ≤ 1 * a := by gcongr; exact mass_le_one _
    _ = a := one_mul a

-- ── The chain and the four nesting branches ──────────────────────────────

section Branches

variable (c : NestCost) (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
  (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx)
  (size maxStmtSeqLen : Nat) (B : ℝ≥0∞)

/-- **The chain bound.** A chain of `len` groups holds at most `len` times what one group holds.
Stated against a hypothesis on `genStmtT` at the same `size`, so the mutual recursion is discharged
by nesting this induction inside the induction on `size`. -/
theorem genStmtChainT_expect_le (labels : List String)
    (ih : ∀ C ctx, expect (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels
      C ctx pctx size maxStmtSeqLen) (count c) ≤ B) :
    ∀ (len : Nat) (C : LContext CoreLParams) (ctx : VarCtx),
      expect (genStmtChainT (G := SPMF) θ octx tvars immutableVars procs labels
        C ctx pctx size len maxStmtSeqLen) (countChain c) ≤ (len : ℝ≥0∞) * B := by
  intro len
  induction len with
  | zero =>
    intro C ctx
    rw [genStmtChainT_zero]
    simp only [expect_pure, countChain, nestCountL_nil, Nat.cast_zero, zero_mul, le_refl]
  | succ len ihlen =>
    intro C ctx
    rw [genStmtChainT_succ, expect_bind]
    -- One group, then the rest: the count of the concatenation splits, `expect` is additive, and
    -- the mass of the tail is at most `1`.
    refine le_trans (expect_mono (g := fun r => count c r + (len : ℝ≥0∞) * B) fun r => ?_) ?_
    · rw [expect_bind]
      refine le_trans (expect_mono (g := fun d => count c r + countChain c d) fun d => ?_) ?_
      · obtain ⟨rest, C'', ctx''⟩ := d
        simp only [expect_pure, countChain, count, nestCountL_append, Nat.cast_add, le_refl]
      · exact expect_const_add_le (ihlen _ _)
    · rw [expect_add, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm ((len : ℝ≥0∞) * B) B]
      gcongr
      · exact ih C ctx
      · calc expect _ (fun _ => (len : ℝ≥0∞) * B) = _ * ((len : ℝ≥0∞) * B) := expect_const _ _
          _ ≤ 1 * ((len : ℝ≥0∞) * B) := by gcongr; exact mass_le_one _
          _ = (len : ℝ≥0∞) * B := one_mul _

variable (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
  (ihsize : ∀ labels C ctx,
    expect (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size
      maxStmtSeqLen) (count c) ≤ B)
include ihsize

/-- The bound on one drawn body: a chain of length `len`. -/
private theorem body_le (labels' : List String) (len : Nat) :
    expect (genStmtChainT (G := SPMF) θ octx tvars immutableVars procs labels' C ctx pctx size len
      maxStmtSeqLen) (countChain c) ≤ (len : ℝ≥0∞) * B :=
  genStmtChainT_expect_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen B labels'
    (fun C ctx => ihsize labels' C ctx) len C ctx

theorem block_branch_le :
    expect (do
      let label ← genFreshLabel (G := SPMF) labels
      let ⟨⟨len, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
      let (body, _, _) ← genStmtChainT (G := SPMF) θ octx tvars immutableVars procs
        (label :: labels) C ctx pctx size len maxStmtSeqLen
      Pure.pure (⟨[Stmt.block label body default], C, ctx⟩ : GenStmtResult)) (count c)
      ≤ c.block + (maxStmtSeqLen : ℝ≥0∞) / 2 * B := by
  refine expect_bind_const_le _ _ _ _ fun label => ?_
  rw [expect_bind]
  refine expect_choose_le maxStmtSeqLen _ _ B fun p => ?_
  obtain ⟨⟨len, hlen⟩⟩ := p
  rw [expect_bind]
  refine le_trans (expect_mono (g := fun d => (c.block : ℝ≥0∞) + countChain c d) fun d => ?_)
    (expect_const_add_le (body_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen B C
      ctx ihsize (label :: labels) len))
  simp only [expect_pure, count, countChain, nestCountL_cons, nestCountL_nil, nestCount,
    Nat.add_zero, Nat.cast_add, le_refl]

theorem iteDet_branch_le :
    expect (do
      let cond ← genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] (size + 1) .bool
      let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
      let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
      let (thenb, _, _) ← genStmtChainT (G := SPMF) θ octx tvars immutableVars procs labels
        C ctx pctx size tlen maxStmtSeqLen
      let (elseb, _, _) ← genStmtChainT (G := SPMF) θ octx tvars immutableVars procs labels
        C ctx pctx size elen maxStmtSeqLen
      Pure.pure (⟨[Stmt.ite (.det cond) thenb elseb default], C, ctx⟩ : GenStmtResult)) (count c)
      ≤ ((c.ite : ℝ≥0∞) + (maxStmtSeqLen : ℝ≥0∞) / 2 * B) + (maxStmtSeqLen : ℝ≥0∞) / 2 * B := by
  refine expect_bind_const_le _ _ _ _ fun cond => ?_
  rw [expect_bind]
  refine expect_choose_le maxStmtSeqLen _ _ B fun p => ?_
  obtain ⟨⟨tlen, htlen⟩⟩ := p
  rw [expect_bind, add_right_comm]
  refine expect_choose_le maxStmtSeqLen _ _ B fun q => ?_
  obtain ⟨⟨elen, helen⟩⟩ := q
  rw [expect_bind]
  refine le_trans (expect_mono (g := fun d => (c.ite : ℝ≥0∞) + countChain c d + (elen : ℝ≥0∞) * B)
    fun d => ?_) ?_
  · rw [expect_bind]
    refine le_trans (expect_mono (g := fun e => (c.ite : ℝ≥0∞) + countChain c d + countChain c e)
      fun e => ?_) ?_
    · simp only [expect_pure, count, countChain, nestCountL_cons, nestCountL_nil, nestCount,
        Nat.add_zero, Nat.cast_add, le_refl]
    · exact expect_const_add_le
        (body_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen B C ctx ihsize labels
          elen)
  · refine expect_add_const_le (expect_const_add_le ?_)
    exact body_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen B C ctx ihsize labels
      tlen

theorem iteNondet_branch_le :
    expect (do
      let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose (m := SPMF) 0 maxStmtSeqLen (Nat.zero_le _)
      let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
      let (thenb, _, _) ← genStmtChainT (G := SPMF) θ octx tvars immutableVars procs labels
        C ctx pctx size tlen maxStmtSeqLen
      let (elseb, _, _) ← genStmtChainT (G := SPMF) θ octx tvars immutableVars procs labels
        C ctx pctx size elen maxStmtSeqLen
      Pure.pure (⟨[Stmt.ite .nondet thenb elseb default], C, ctx⟩ : GenStmtResult)) (count c)
      ≤ ((c.ite : ℝ≥0∞) + (maxStmtSeqLen : ℝ≥0∞) / 2 * B) + (maxStmtSeqLen : ℝ≥0∞) / 2 * B := by
  rw [expect_bind]
  refine expect_choose_le maxStmtSeqLen _ _ B fun p => ?_
  obtain ⟨⟨tlen, htlen⟩⟩ := p
  rw [expect_bind, add_right_comm]
  refine expect_choose_le maxStmtSeqLen _ _ B fun q => ?_
  obtain ⟨⟨elen, helen⟩⟩ := q
  rw [expect_bind]
  refine le_trans (expect_mono (g := fun d => (c.ite : ℝ≥0∞) + countChain c d + (elen : ℝ≥0∞) * B)
    fun d => ?_) ?_
  · rw [expect_bind]
    refine le_trans (expect_mono (g := fun e => (c.ite : ℝ≥0∞) + countChain c d + countChain c e)
      fun e => ?_) ?_
    · simp only [expect_pure, count, countChain, nestCountL_cons, nestCountL_nil, nestCount,
        Nat.add_zero, Nat.cast_add, le_refl]
    · exact expect_const_add_le
        (body_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen B C ctx ihsize labels
          elen)
  · refine expect_add_const_le (expect_const_add_le ?_)
    exact body_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen B C ctx ihsize labels
      tlen

theorem loop_branch_le :
    expect (do
      let guard ← genCondOrNondet (G := SPMF) octx tvars ctx (size + 1) pctx
      let measure ← genOptMeasure (G := SPMF) octx tvars ctx (size + 1) pctx
      let invariants ← genInvariants (G := SPMF) octx tvars ctx maxStmtSeqLen (size + 1) pctx
      let ⟨⟨blen, _⟩⟩ ← RandomChoice.choose 0 maxStmtSeqLen (Nat.zero_le _)
      let (body, _, _) ← genStmtChainT (G := SPMF) θ octx tvars immutableVars procs labels
        C ctx pctx size blen maxStmtSeqLen
      Pure.pure (⟨[Stmt.loop guard measure invariants body default], C, ctx⟩ : GenStmtResult))
      (count c) ≤ c.loop + (maxStmtSeqLen : ℝ≥0∞) / 2 * B := by
  refine expect_bind_const_le _ _ _ _ fun guard => ?_
  refine expect_bind_const_le _ _ _ _ fun measure => ?_
  refine expect_bind_const_le _ _ _ _ fun invariants => ?_
  rw [expect_bind]
  refine expect_choose_le maxStmtSeqLen _ _ B fun p => ?_
  obtain ⟨⟨blen, hblen⟩⟩ := p
  rw [expect_bind]
  refine le_trans (expect_mono (g := fun d => (c.loop : ℝ≥0∞) + countChain c d) fun d => ?_)
    (expect_const_add_le (body_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen B C
      ctx ihsize labels blen))
  simp only [expect_pure, count, countChain, nestCountL_cons, nestCountL_nil, nestCount,
    Nat.add_zero, Nat.cast_add, le_refl]

end Branches

-- ── The expected count ───────────────────────────────────────────────────

/-- **(1) The expected count of `genStmtT θ … n maxStmtSeqLen` is at most `countBound`**, for every
`θ`, every size, every cap and every context. -/
theorem genStmtT_expect_count_le (c : NestCost) (θ : Tuning) (octx : OpCtx)
    (tvars : List TyIdentifier) (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (pctx : PolyOpCtx) (maxStmtSeqLen : Nat) :
    ∀ (size : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx),
      expect (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size
        maxStmtSeqLen) (count c) ≤ countBound c maxStmtSeqLen θ size := by
  intro size
  induction size with
  | zero =>
    intro labels C ctx
    obtain ⟨h0, h1, h2, h3⟩ :=
      genStmt_leaf_expect c octx tvars immutableVars procs labels C ctx pctx 0
    rw [genStmtT_zero, expect_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3]
    simp [countBound]
  | succ size ihsize =>
    intro labels C ctx
    obtain ⟨h0, h1, h2, h3⟩ :=
      genStmt_leaf_expect c octx tvars immutableVars procs labels C ctx pctx (size + 1)
    rw [genStmtT_succ, expect_frequency]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3,
      mul_zero, zero_add, add_zero]
    have hb := block_branch_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen _ labels C
      ctx ihsize
    have hd := iteDet_branch_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen _ labels
      C ctx ihsize
    have hn := iteNondet_branch_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen _
      labels C ctx ihsize
    have hl := loop_branch_le c θ octx tvars immutableVars procs pctx size maxStmtSeqLen _ labels C
      ctx ihsize
    refine le_trans (ENNReal.div_le_div_right (add_le_add (mul_le_mul_right hb _)
      (add_le_add (mul_le_mul_right hd _) (add_le_add (mul_le_mul_right hn _)
        (mul_le_mul_right hl _)))) _) (le_of_eq ?_)
    have hW : (((θ.weight 4 0 + (θ.weight 5 0 + (θ.weight 6 0 + (θ.weight 7 0 +
        (θ.weight 8 0 + (θ.weight 9 0 + (θ.weight 10 0 + θ.weight 11 0))))))) : ℕ) : ℝ≥0∞)
        = stmtTotalWeight θ := by
      simp only [stmtTotalWeight, stmtWeight]; push_cast; ring
    rw [hW]
    simp only [countBound, nestShare, expectedChildStmts, bodiesPerStmt, stmtWeight]
    simp only [div_eq_mul_inv]
    ring

-- ── Closed forms ─────────────────────────────────────────────────────────

/-- **The closed form of the count bound**: a geometric sum in the expected number of child
statements, `nestShare c θ · (1 + r + … + r^{n-1})`. -/
theorem countBound_eq (c : NestCost) (maxStmtSeqLen : Nat) (θ : Tuning) (n : Nat) :
    countBound c maxStmtSeqLen θ n
      = nestShare c θ * ∑ i ∈ Finset.range n, expectedChildStmts maxStmtSeqLen θ ^ i := by
  induction n with
  | zero => simp [countBound]
  | succ n ih =>
    rw [countBound, ih, Finset.sum_range_succ', pow_zero, mul_add, mul_one, add_comm,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- The geometric sum is at most its infinite sum `1 / (1 − r)`, at every `n`. In `ℝ≥0∞` this
needs no hypothesis: if `r ≥ 1` the right side is `⊤`. -/
theorem geom_le_inv (r : ℝ≥0∞) (n : Nat) : ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  rw [← ENNReal.tsum_geometric]
  exact ENNReal.sum_le_tsum _

/-- **The expected count, uniformly in the size**: at most `nestShare c θ / (1 − r)`. This is finite exactly
when `r = expectedChildStmts maxStmtSeqLen θ < 1`. -/
theorem genStmtT_expect_count_le_geom (c : NestCost) (θ : Tuning) (octx : OpCtx)
    (tvars : List TyIdentifier) (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (pctx : PolyOpCtx) (maxStmtSeqLen size : Nat) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) :
    expect (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size
        maxStmtSeqLen) (count c)
      ≤ nestShare c θ * (1 - expectedChildStmts maxStmtSeqLen θ)⁻¹ :=
  le_trans (genStmtT_expect_count_le c θ octx tvars immutableVars procs pctx maxStmtSeqLen size
    labels C ctx) (by rw [countBound_eq]; gcongr; exact geom_le_inv _ _)

/-- **The expected number of loops**, in terms of `loopShare θ` and
`r = expectedChildStmts maxStmtSeqLen θ`: at most `loopShare θ · (1 + r + … + r^{n-1})`, and so at
most `loopShare θ / (1 − r)`. -/
theorem genStmtT_expect_numLoops_le_geom (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx)
    (maxStmtSeqLen size : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) :
    expect (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size
        maxStmtSeqLen) (count loopCost)
      ≤ loopShare θ * ∑ i ∈ Finset.range size, expectedChildStmts maxStmtSeqLen θ ^ i ∧
    expect (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size
        maxStmtSeqLen) (count loopCost)
      ≤ loopShare θ * (1 - expectedChildStmts maxStmtSeqLen θ)⁻¹ := by
  have h := genStmtT_expect_count_le loopCost θ octx tvars immutableVars procs pctx maxStmtSeqLen
    size labels C ctx
  rw [countBound_eq, nestShare_loopCost] at h
  exact ⟨h, le_trans h (by gcongr; exact geom_le_inv _ _)⟩

/-- **The expected number of nested statements** (`block`, `ite` and `loop` together), in terms of
`nestingShare θ` and `r = expectedChildStmts maxStmtSeqLen θ`. -/
theorem genStmtT_expect_numNesting_le_geom (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx)
    (maxStmtSeqLen size : Nat) (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) :
    expect (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size
        maxStmtSeqLen) (count nestingCost)
      ≤ nestingShare θ * (1 - expectedChildStmts maxStmtSeqLen θ)⁻¹ := by
  have h := genStmtT_expect_count_le_geom nestingCost θ octx tvars immutableVars procs pctx
    maxStmtSeqLen size labels C ctx
  rwa [nestShare_nestingCost] at h

-- ── The shipping weights ─────────────────────────────────────────────────

/-- The shipping weights of the `size + 1` site: `7, 1, 1, 3, 1, 1, 1, 1`. -/
theorem stmtWeight_default :
    stmtWeight stmtDefault 0 = 7 ∧ stmtWeight stmtDefault 1 = 1 ∧ stmtWeight stmtDefault 2 = 1 ∧
    stmtWeight stmtDefault 3 = 3 ∧ stmtWeight stmtDefault 4 = 1 ∧ stmtWeight stmtDefault 5 = 1 ∧
    stmtWeight stmtDefault 6 = 1 ∧ stmtWeight stmtDefault 7 = 1 := by
  simp only [stmtWeight]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact_mod_cast (by decide : _)

theorem stmtTotalWeight_default : stmtTotalWeight stmtDefault = 16 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := stmtWeight_default
  rw [stmtTotalWeight, h0, h1, h2, h3, h4, h5, h6, h7]; norm_num

/-- At the shipping weights, the `loop` branch holds `1/16` of the weight at size `n + 1`. -/
theorem loopShare_default : loopShare stmtDefault = 1 / 16 := by
  rw [loopShare, stmtTotalWeight_default, stmtWeight_default.2.2.2.2.2.2.2]

/-- At the shipping weights, the nested branches hold `1/4` of the weight at size `n + 1`. -/
theorem nestingShare_default : nestingShare stmtDefault = 1 / 4 := by
  obtain ⟨-, -, -, -, h4, h5, h6, h7⟩ := stmtWeight_default
  rw [nestingShare, stmtTotalWeight_default, h4, h5, h6, h7,
    ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- At the shipping weights, one statement draw at size `n + 1` makes `3 · maxStmtSeqLen / 16` child
statement draws, on average. -/
theorem expectedChildStmts_default (maxStmtSeqLen : Nat) :
    expectedChildStmts maxStmtSeqLen stmtDefault = 3 * maxStmtSeqLen / 16 := by
  obtain ⟨-, -, -, -, h4, h5, h6, h7⟩ := stmtWeight_default
  rw [expectedChildStmts, bodiesPerStmt, stmtTotalWeight_default, h4, h5, h6, h7]
  simp only [div_eq_mul_inv]
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc (1 + 2 * 1 + 2 * 1 + 1 : ℝ≥0∞) * 16⁻¹ * ((maxStmtSeqLen : ℝ≥0∞) * 2⁻¹)
      = 3 * maxStmtSeqLen * 16⁻¹ * (2 * 2⁻¹) := by ring
    _ = 3 * maxStmtSeqLen * 16⁻¹ := by rw [h2, mul_one]

/-- At the default cap `5`, `r = 15/16`, and `1 / (1 − r) = 16`. -/
theorem inv_one_sub_expectedChildStmts_default :
    (1 - expectedChildStmts defaultMaxStmtSeqLen stmtDefault)⁻¹ = 16 := by
  rw [expectedChildStmts_default, show ((defaultMaxStmtSeqLen : ℕ) : ℝ≥0∞) = 5 from rfl]
  have h : (1 : ℝ≥0∞) - 3 * 5 / 16 = 1 / 16 := by
    refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
    rw [ENNReal.div_add_div_same]
    norm_num
    exact (ENNReal.div_self (by norm_num) (by norm_num)).symm
  rw [h, one_div, inv_inv]

/-- **At the shipping weights and the default cap, the expected number of loops is at most `1`, at
every size**, in every context. -/
theorem genStmt_expect_numLoops_le_one (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx) (size : Nat)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) :
    expect (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size)
      (count loopCost) ≤ 1 := by
  have h := (genStmtT_expect_numLoops_le_geom stmtDefault octx tvars immutableVars procs pctx
    defaultMaxStmtSeqLen size labels C ctx).2
  rw [genStmtT_defaults, loopShare_default, inv_one_sub_expectedChildStmts_default] at h
  refine le_trans h ?_
  ennr

/-- **At the shipping weights and the default cap, the expected number of nested statements is at
most `4`, at every size**, in every context. -/
theorem genStmt_expect_numNesting_le (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx) (size : Nat)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) :
    expect (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size)
      (count nestingCost) ≤ 4 := by
  have h := genStmtT_expect_numNesting_le_geom stmtDefault octx tvars immutableVars procs pctx
    defaultMaxStmtSeqLen size labels C ctx
  rw [genStmtT_defaults, nestingShare_default, inv_one_sub_expectedChildStmts_default] at h
  refine le_trans h ?_
  ennr

-- ── Every profile, at its own cap ────────────────────────────────────────

/-- **The per-profile cap keeps `r` below `1` for every profile.** At `maxStmtSeqLenFor θ`, one statement
draw makes fewer than one statement draw one level down, on average, for every `θ`. -/
theorem expectedChildStmts_maxStmtSeqLenFor_lt_one (θ : Tuning) :
    expectedChildStmts (maxStmtSeqLenFor θ) θ < 1 := by
  set B : ℕ := θ.weight 8 0 + 2 * θ.weight 9 0 + 2 * θ.weight 10 0 + θ.weight 11 0 with hB
  set W : ℕ := θ.weight 4 0 + θ.weight 5 0 + θ.weight 6 0 + θ.weight 7 0 +
    θ.weight 8 0 + θ.weight 9 0 + θ.weight 10 0 + θ.weight 11 0 with hW
  have hW0 : 0 < W := by have := Tuning.weight_pos θ 4 0; omega
  have hk : B * maxStmtSeqLenFor θ < W * 2 := by
    have h1 : maxStmtSeqLenFor θ ≤ (2 * W - 1) / B := Nat.min_le_right _ _
    calc B * maxStmtSeqLenFor θ ≤ B * ((2 * W - 1) / B) := Nat.mul_le_mul_left _ h1
      _ ≤ 2 * W - 1 := Nat.mul_div_le _ _
      _ < W * 2 := by omega
  have hr : expectedChildStmts (maxStmtSeqLenFor θ) θ
      = ((B * maxStmtSeqLenFor θ : ℕ) : ℝ≥0∞) / ((W * 2 : ℕ) : ℝ≥0∞) := by
    simp only [expectedChildStmts, bodiesPerStmt, stmtTotalWeight, stmtWeight]
    rw [StrataGenerators.SizeDistribution.div_mul_div _ _ _ (by
      simp only [ne_eq, add_eq_zero, Nat.cast_eq_zero]
      exact fun h => absurd h.1.1.1.1.1.1.1 (Tuning.weight_pos θ 4 0).ne') (by finiteness), hB, hW]
    push_cast
    congr 1
  rw [hr, ENNReal.div_lt_iff (Or.inl (by exact_mod_cast (by omega : W * 2 ≠ 0)))
    (Or.inl (by finiteness)), one_mul]
  exact_mod_cast hk

/-- **Every tuning profile, at its own cap, has a bounded expected nesting**: the tuned statement
generator at `maxStmtSeqLenFor θ` has at most `nestingShare θ / (1 − r)` nested statements on
average, at every size, and this bound is finite. This is about one statement draw. -/
theorem genStmtT_expect_numNesting_finite (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx) (size : Nat)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) :
    expect (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size)
        (count nestingCost)
      ≤ nestingShare θ * (1 - expectedChildStmts (maxStmtSeqLenFor θ) θ)⁻¹ ∧
    nestingShare θ * (1 - expectedChildStmts (maxStmtSeqLenFor θ) θ)⁻¹ ≠ ⊤ := by
  refine ⟨genStmtT_expect_numNesting_le_geom θ octx tvars immutableVars procs pctx _ size labels C
    ctx, ENNReal.mul_ne_top ?_ ?_⟩
  · refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
    rw [nestingShare]
    refine ENNReal.div_le_of_le_mul ?_
    simp only [stmtTotalWeight, one_mul]
    calc stmtWeight θ 4 + stmtWeight θ 5 + stmtWeight θ 6 + stmtWeight θ 7
        ≤ stmtWeight θ 0 + stmtWeight θ 1 + stmtWeight θ 2 + stmtWeight θ 3 +
            (stmtWeight θ 4 + stmtWeight θ 5 + stmtWeight θ 6 + stmtWeight θ 7) := le_add_self
      _ = _ := by ring
  · exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt (expectedChildStmts_maxStmtSeqLenFor_lt_one θ)).ne'

end StrataGenerators.SizeDistributionLoops
