/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.FunctionHasTypeAGen
import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.ProcedureHasTypeAGen
import StrataGenerators.TuningProfiles
import StrataGenerators.SetGen
import Basalt.Tuning.Attr

open Lambda RandomChoice Core Imperative
open StrataGenerators.Stmt
open StrataGenerators.TuningProfiles
open scoped SetGen.Set

/-!
# The shipping generators, tuned

Every generator this repo's test suite draws from, made distribution-tunable, with a machine-checked
theorem per generator that the conversion is *behavior-preserving*: at `SetGen.Set` the tuned
generator is **equal** to the untuned one for every `θ`, so every soundness and completeness result
about the original applies to every tuning of it. The weights themselves — which `θ` to use for which
family of properties, and the measurements behind them — are in
`StrataGenerators.TuningProfiles`; this file is the guarantee that no choice made there can cost
coverage.

* **§1 `PrecondElim`, knob 1 — the shape of a precondition, with no source edit.**
  `genPrecondition` is tagged from another module (`StrataGenerators.TuningProfiles`), not at its
  definition site. That is what the `@[tunable]` attribute bought over the older `tunable def`
  macro: because it rewrites the elaborated body, it does not have to be written at the definition
  site. The site it finds is `genPrecondition`'s existing 3:1 split between an input-mentioning
  clause and a plain `.bool` draw, so `genPrecondition.tuned θ` moves that ratio at runtime.

* **§2 `PrecondElim`, knob 2 — whether a precondition is present at all.**
  That split is `optionGen`'s rational `coin`, which is not a `frequency` and so is invisible to
  `@[tunable]`. `genPreconditionW` reworks it into the two-branch `frequency` of
  `SetGen.weightedOptionGen` (written inline, so the attribute sees it) and proves the rework has the
  same support as the shipping `genPrecondition` — so the conversion changes only the distribution.
  The same rework would make `genFunction`'s body/measure coins tunable, which is what the
  `function:` family needs; it is not done here.

* **§3 `LoopElim` — the real statement generator.** `StrataGenerators.Stmt.genStmt` is now tagged at
  its definition site, and `genStmt_mutual_tuned_eq` proves θ-invariance for the *whole mutual
  block* — so `loop` is flat index 13 of a real knob rather than of a mirror. An earlier revision of
  this file argued the shipping generator could not be tagged, and recorded the attribute's error as
  a `#guard_msgs`. Two source changes removed the obstacle, both in
  `StmtHasTypeAGen/Core.lean`:

  1. the `frequency`'s branch list was a `let`-bound variable; it is now written inline, so the
     weights are visible to be collected (the same one-line change unblocked `genCmd` and
     `genLExprBase`);
  2. `exit` and `call` carried the weight `if labels.isEmpty then 0 else 1`, and `@[tunable]`
     rejects both a computed weight and a literal `0`. Instead of the weight, the *branch* now
     tests the condition and falls back to `genCmdStmt` — the generator branch 0 already offers —
     so the list has only positive literal weights and `genStmt`'s support is unchanged, because
     the fallback's support was already in the union. Both forms are throw-free (`frequency` skips
     a zero-weight branch); they differ only in that `cmd` now absorbs the pruned branches' share
     instead of the list being renormalised.

* **§4 The rest.** `genCmd`, `genLMonoTy` and `genLExprBase` (59 branch weights across ten
  per-type sites), each with the same θ-invariance guarantee, one recursion form each — no
  recursion, `Nat.brecOn`, and `Nat.brecOn` under a wide match.
-/

namespace TuningPrototypes

open Strata.DL.Util (FuncPrecondition)

-- ══════════════════════════════════════════════════════════════════════════
-- 1. PrecondElim, knob 1: tuning the shipping generator in place
-- ══════════════════════════════════════════════════════════════════════════

/-! `genPrecondition` (`StrataGenerators/FunctionHasTypeAGen/Core.lean`) already contains a
`frequency`: inside the `some` clause it prefers an input-mentioning precondition over a plain
`.bool` draw, 3:1. `StrataGenerators.TuningProfiles` tags it — from a different module, with no edit
to its source — which makes that ratio a runtime knob. -/

/-- One site, arity 2, no recursive calls: the input-mentioning branch and the `.bool` branch. -/
example : genPrecondition.sites = #[⟨`genPrecondition.site0, 0, 2, #[0, 0]⟩] := rfl

/-- The defaults are the 3:1 split as written in the source. -/
example : genPrecondition.defaults = ⟨#[(3, 0), (1, 0)]⟩ := rfl

/-- Two `Tuning`s for the clause-shape site: the source's 3:1, and one that all but forces every
    generated precondition to mention an input (10:1). Both are support-total. -/
def precondDefault : Tuning := genPrecondition.defaults
def precondInputHeavy : Tuning := ⟨#[(10, 0), (1, 0)]⟩

/-- **The conversion is behavior-preserving.** For every `θ`, the tuned generator is *the same*
    `Set`-valued generator as the shipping one.

    `genPrecondition`'s site sits inside a `do` block, under a `dite` that binds the
    `inputs.toList ≠ []` proof, so the site cannot be rewritten in place by `rw` — the branch mentions
    the bound proof. Splitting on the condition first exposes it, and then
    `SetGen.frequency_eq_oneOf` sends each side's `frequency` to the same weight-free `oneOf` normal
    form. The `inputs.toList = []` case has no site at all, so it closes by reflexivity. -/
theorem genPrecondition_tuned_eq (θ : Tuning) (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat)
    (pctx : PolyOpCtx) :
    genPrecondition.tuned (G := SetGen.Set) θ octx inputs tvars depth pctx
      = genPrecondition octx inputs tvars depth pctx := by
  unfold genPrecondition genPrecondition.tuned
  by_cases hne : inputs.toList ≠ []
  · simp only [dif_pos hne]
    rw [SetGen.frequency_eq_oneOf, SetGen.frequency_eq_oneOf]
    all_goals simp [Tuning.weight_pos]
  · simp only [dif_neg hne]

/-- So the *exact* support characterization proved for the shipping generator
    (`mem_support_genPrecondition_iff`) holds verbatim of every tuning of it — one `rw`, no reproof.
    In particular `genPreconditions_complete`, and thence `genFunction_complete`, carry over. -/
example (θ : Tuning) (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx) :
    SetGen.support (genPrecondition.tuned (G := SetGen.Set) θ octx inputs tvars depth pctx)
      = SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth pctx) := by
  rw [genPrecondition_tuned_eq]

/-- And any soundness-and-completeness fact transfers without knowing what the predicate is. -/
example (θ : Tuning) (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx)
    (P : Option (FuncPrecondition LExpr' Unit) → Prop)
    (h : SetGen.IsSoundAndComplete
      (genPrecondition (G := SetGen.Set) octx inputs tvars depth pctx) P) :
    SetGen.IsSoundAndComplete
      (genPrecondition.tuned (G := SetGen.Set) θ octx inputs tvars depth pctx) P :=
  SetGen.IsSoundAndComplete.of_support_eq (by rw [genPrecondition_tuned_eq]) h

-- ══════════════════════════════════════════════════════════════════════════
-- 2. PrecondElim, knob 2: tuning whether a precondition is present
-- ══════════════════════════════════════════════════════════════════════════

/-- The `some`-clause body of `genPrecondition`, verbatim (3:1 toward input-mentioning clauses over
    a plain `.bool` draw, in the `inputsAsFVarCtx inputs` free-variable context). Factored out so the
    tunable split below has exactly *one* site — the `some`/`none` choice — rather than also
    capturing this inner `frequency`, which is knob 1's concern.

    (`@[tunable]` inlines only the tagged declaration's own auxiliaries, so a `frequency` inside a
    separate definition like this one is not collected.) -/
def genPrecondClause [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    G (FuncPrecondition LExpr' Unit) := do
  let e ←
    if hne : inputs.toList ≠ [] then
      frequency
        [ (3, fun () => genInputMentioningPrecond octx inputs tvars depth hne),
          (1, fun () => genLExpr (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool) ]
        (by show 0 < 3 + 1; omega)
    else
      genLExpr (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool
  pure { expr := e, md := () }

/-- `genPrecondition` with the `some`/`none` split made tunable.

    Identical to `FunctionHasTypeAGen.Core.genPrecondition` except the outer `optionGen` (a fixed 1/2
    `coin`) is replaced by a two-branch `frequency` — the shape of `SetGen.weightedOptionGen` — whose
    split is a tunable site. So `genPreconditionW.tuned θ` biases how often a function carries a
    `requires` clause, which is exactly the knob `PrecondElim` needs turned up.

    The split is written out rather than delegated to `SetGen.weightedOptionGen` because
    `@[tunable]` collects `frequency` calls in the tagged definition's own body; the combinator's
    weights are variables, not literals, so it is not tunable itself. `genPreconditionW_eq_weighted`
    below records that the two are nonetheless the same term.

    Because the definition has a binder named `depth`, the site reads its weights at that depth
    (`Tuning.weight θ i depth`), so a schedule with a nonzero growth coefficient can make
    preconditions rarer in deeper expression budgets. At `SetGen.Set` this is invisible — which is
    the guarantee, not a limitation: no schedule can change what is reachable. -/
@[tunable]
def genPreconditionW [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    G (Option (FuncPrecondition LExpr' Unit)) :=
  frequency [
    (1, fun _ => do let p ← genPrecondClause octx inputs tvars depth; pure (some p)),
    (1, fun _ => pure none)
  ] (by simp)

/-- One tunable site (`site0`), arity 2, no recursive calls. -/
example : genPreconditionW.sites = #[⟨`TuningPrototypes.genPreconditionW.site0, 0, 2, #[0, 0]⟩] := rfl

example : genPreconditionW.defaults = ⟨#[(1, 0), (1, 0)]⟩ := rfl

/-- The inline split really is `SetGen.weightedOptionGen`'s, at weights `1 : 1` — the same term, so
    `mem_support_weightedOptionGen_iff` characterizes `genPreconditionW`'s support directly. -/
theorem genPreconditionW_eq_weighted [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    genPreconditionW (G := G) octx inputs tvars depth
      = SetGen.weightedOptionGen 1 1 (genPrecondClause octx inputs tvars depth) := rfl

/-- Two `Tuning`s for the presence site: the default `1:1`, and a `PrecondElim`-oriented one that
    makes preconditions present ~4× as often as absent. Both are support-total. -/
def presenceDefault : Tuning := genPreconditionW.defaults
def presenceHeavy : Tuning := ⟨#[(4, 0), (1, 0)]⟩

/-- The tunable rework has the **same support** as the shipping `genPrecondition`, so all of the
    latter's soundness/completeness results transfer to it (and, via `tuned_defaults`, to
    `genPreconditionW.tuned genPreconditionW.defaults`). This is the theorem that certifies the
    conversion is behavior-preserving: only the distribution changes.

    The proof reduces both sides to the same disjunction over `genPrecondClause` reachability — the
    shipping `genPrecondition` is *definitionally* `optionGen (genPrecondClause …)`, its `optionGen`
    payload being the very do-block factored out above. So the `frequency` split here and
    `optionGen`'s `coin` split there have the same support. -/
theorem genPreconditionW_support_eq (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    SetGen.support (genPreconditionW (G := SetGen.Set) octx inputs tvars depth) =
      SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth) := by
  have hrhs : genPrecondition (G := SetGen.Set) octx inputs tvars depth
      = optionGen (genPrecondClause octx inputs tvars depth) := rfl
  ext o
  rw [hrhs, SetGen.mem_support_optionGen_iff]
  simp only [genPreconditionW, SetGen.mem_support_frequency_iff]
  constructor
  · rintro ⟨w, g, hmem, _, hg⟩
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      simp only [SetGen.mem_support_bind_iff, SetGen.mem_support_pure_iff] at hg
      obtain ⟨p, hp, rfl⟩ := hg
      exact Or.inr ⟨p, hp, rfl⟩
    · rcases List.mem_cons.mp hmem' with heq | hnil
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        simp only [SetGen.mem_support_pure_iff] at hg
        exact Or.inl hg
      · simp at hnil
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · refine ⟨1, _, List.mem_cons_of_mem _ List.mem_cons_self, by omega, ?_⟩
      simp only [SetGen.mem_support_pure_iff]
    · refine ⟨1, _, List.mem_cons_self, by omega, ?_⟩
      simp only [SetGen.mem_support_bind_iff, SetGen.mem_support_pure_iff]
      exact ⟨p, hp, rfl⟩

/-- Boosting the precondition rate is behavior-preserving for *any* `θ`, so soundness/completeness of
    the function generator is unaffected: only the frequency of `requires` clauses changes. -/
theorem genPreconditionW_tuned_eq (θ : Tuning) (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    genPreconditionW.tuned (G := SetGen.Set) θ octx inputs tvars depth
      = genPreconditionW octx inputs tvars depth := by
  unfold genPreconditionW genPreconditionW.tuned
  apply SetGen.frequency_congr_weights
  · rfl
  all_goals simp [Tuning.weight_pos]

/-- Chaining the two: every tuning of the reworked generator has the shipping generator's support. -/
example (θ : Tuning) (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) :
    SetGen.support (genPreconditionW.tuned (G := SetGen.Set) θ octx inputs tvars depth) =
      SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth) := by
  rw [genPreconditionW_tuned_eq, genPreconditionW_support_eq]

-- ══════════════════════════════════════════════════════════════════════════
-- 3. LoopElim: the real statement generator
-- ══════════════════════════════════════════════════════════════════════════

/-! `StrataGenerators.Stmt.genStmt` is tagged at its definition site, and
`StrataGenerators.TuningProfiles` additionally tags the mutual block's shared auxiliary
`genStmt._mutual`. Both are needed, and the difference between them is the whole story of how tuning
composes:

* `genStmt.tuned θ` reads the weights of the statement it produces itself. Its recursion, though,
  runs through `genStmtChain` — the *other* member of the block, which `@[tunable]` does not rewrite
  — so the statements nested inside a `block`/`ite`/`loop` body are drawn from the untuned generator.
  Measured (`dist-report`), with the `loop` weight at 40: top-level loops 15% → 72%, but
  loop-inside-a-loop only 2% → 7.5%.
* `genStmt._mutual.tuned θ` is the whole block. Its recursion is internal — one `WellFounded.fix`
  over a `PSum` of the two members' argument tuples — so `θ` threads through all of it. Same
  weighting: loop-inside-a-loop 3.5% → 66%.

`TuningProfiles.genStmtT`/`genStmtChainT` are therefore built on the auxiliary, and are pinned to the
shipping generators at `θ = defaults` by `rfl` there. -/

/-- **The conversion is behavior-preserving, for the whole mutual block.** For every `θ`, the tuned
    statement generator is *the same* `Set`-valued generator as the shipping one — so
    `genStmt_sound`, `genStmtChain_sound` and the completeness results transfer to every tuning by
    one `rw`, and no profile in `StrataGenerators.TuningProfiles` can make a statement shape
    unreachable.

    The proof is the `WellFounded.fix` recipe from `SetGen.Tuning`: `delta` exposes both sides as
    `WellFounded.fix` applied to functionals that differ only in their `frequency` weights (the
    recursive-call bundle `ih` is literally the same bound variable in both), `SetGen`'s
    `wellFounded_fix_congr` reduces the goal to those functionals being equal, and then there is one
    `frequency_congr_weights` per site: the `size = 0` list, the `size + 1` list, and `rfl` for the
    `PSum.inr` case, which is `genStmtChain` and has no site of its own. -/
theorem genStmt_mutual_tuned_eq (θ : Tuning) :
    (genStmt._mutual.tuned (G := SetGen.Set) θ) = genStmt._mutual := by
  funext fctx octx tvars immutableVars procs
  delta StrataGenerators.Stmt.genStmt._mutual StrataGenerators.Stmt.genStmt._mutual.tuned
  apply SetGen.wellFounded_fix_congr
  funext x ih
  cases x with
  | inl a =>
    obtain ⟨labels, C, ctx, n⟩ := a
    cases n with
    | zero =>
      apply SetGen.frequency_congr_weights
      · rfl
      all_goals simp [Tuning.weight_pos]
    | succ size =>
      apply SetGen.frequency_congr_weights
      · rfl
      all_goals simp [Tuning.weight_pos]
  | inr a => rfl

/-! `genStmt` and `genStmtChain` are irreducible (well-founded recursion), so recognising each as a
projection of the shared auxiliary — which is what the two corollaries below need — takes an
`unseal`. -/
unseal StrataGenerators.Stmt.genStmt StrataGenerators.Stmt.genStmtChain

/-- The single-statement generator, as tagged at its definition site: the same fact, read off the
    block's. -/
theorem genStmt_tuned_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size : Nat) :
    genStmtT (G := SetGen.Set) θ octx tvars immutableVars procs labels C ctx pctx size
      = genStmt octx tvars immutableVars procs labels C ctx pctx size := by
  unfold genStmtT
  rw [genStmt_mutual_tuned_eq]
  rfl

/-- …and for the chain, which is what the statement family's harness draws from. -/
theorem genStmtChain_tuned_eq (θ : Tuning) (octx : OpCtx)
    (tvars : List TyIdentifier) (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx)
    (size len : Nat) :
    genStmtChainT (G := SetGen.Set) θ octx tvars immutableVars procs labels C ctx pctx size len
      = genStmtChain octx tvars immutableVars procs labels C ctx pctx size len := by
  unfold genStmtChainT
  rw [genStmt_mutual_tuned_eq]
  rfl

theorem genProgramStmtsT_tuned_eq (θ : Tuning) (octx : OpCtx)
    (tvars : List TyIdentifier) (size len : Nat) (pctx : PolyOpCtx) :
    genProgramStmtsT (G := SetGen.Set) θ octx tvars size len pctx
      = genProgramStmts octx tvars size len pctx :=
  genStmtChain_tuned_eq ..

/-- The procedure generator too: `genProcedureT` differs from the shipping `genProcedure` only in
    which statement-chain generator it calls, so the block's θ-invariance is the whole proof. This is
    what makes the `proc:` family's profiles — the ones aimed at the three transform passes — free of
    consequence for `genProcedure_sound` and `genProcedure_complete`. -/
theorem genProcedureT_tuned_eq (θ : Tuning) (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (size len : Nat) (pctx : PolyOpCtx) :
    genProcedureT (G := SetGen.Set) θ octx procs C Γ size len pctx
      = StrataGenerators.Procedure.genProcedure octx procs C Γ size len pctx := by
  unfold genProcedureT StrataGenerators.Procedure.genProcedure
  simp only [genStmtChain_tuned_eq]

-- ══════════════════════════════════════════════════════════════════════════
-- 4. The command, type and expression generators
-- ══════════════════════════════════════════════════════════════════════════

/-- `genCmd` is not recursive, so the recipe is the first one in `SetGen.Tuning`'s list — except that
    its two sites sit in the two branches of a `dite` whose proof `h` the `set` branches *use*, so
    the condition has to be split first (exactly as for `genPrecondition` in §1). -/
theorem genCmd_tuned_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx) :
    genCmd.tuned (G := SetGen.Set) θ octx tvars immutableVars ctx depth pctx
      = genCmd octx tvars immutableVars ctx depth pctx := by
  unfold genCmd genCmd.tuned
  by_cases h : (ctx.writable immutableVars).length > 0
  · simp only [dif_pos h]
    apply SetGen.frequency_congr_weights
    · rfl
    all_goals simp [Tuning.weight_pos]
  · simp only [dif_neg h]
    apply SetGen.frequency_congr_weights
    · rfl
    all_goals simp [Tuning.weight_pos]

/-- So the tuned command *chain* is the shipping one, by induction on its length. -/
theorem genCmdsT_tuned_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (depth : Nat) :
    ∀ (n : Nat) (ctx : VarCtx),
      genCmdsT (G := SetGen.Set) θ octx tvars immutableVars ctx depth n
        = genCmds octx tvars immutableVars ctx depth n := by
  intro n
  induction n with
  | zero => intro ctx; rfl
  | succ n ih => intro ctx; simp only [genCmdsT, genCmds, genCmd_tuned_eq, ih]

/-- `genLMonoTy` recurses structurally on its depth, so this is the `Nat.brecOn` recipe: `delta`,
    `SetGen.brecOn_congr`, then one `frequency_congr_weights` per branch of the `n + 1` arm (the
    `0` arm is a `pick`/`oneOf`, with no weights, so it closes by `rfl`). Both sites are the same
    9:1 base-versus-compound split, once with type variables in scope and once without. -/
theorem genLMonoTy_tuned_eq (θ : Tuning) (tvars : List TyIdentifier) (n : Nat) :
    genLMonoTy.tuned (G := SetGen.Set) θ tvars n = genLMonoTy tvars n := by
  delta genLMonoTy genLMonoTy.tuned
  apply SetGen.brecOn_congr
  funext m below
  cases m with
  | zero => rfl
  | succ k =>
    by_cases h : tvars.length > 0
    · simp only [dif_pos h]
      apply SetGen.frequency_congr_weights
      · rfl
      all_goals simp [Tuning.weight_pos]
    · simp only [dif_neg h]
      apply SetGen.frequency_congr_weights
      · rfl
      all_goals simp [Tuning.weight_pos]

set_option maxHeartbeats 1000000 in
/-- `genLExprBase` is the widest of them: ten sites, 59 branch weights, and a match on the target
    type as well as the depth. It needs no more work than the others, because none of the ten arms
    has to be *named*: `split` produces one goal per arm of the match — the same matcher constant
    appears on both sides, since `@[tunable]` reuses matchers rather than rebuilding them — and each
    goal is then either an `n = 0` arm (a `oneOf`, closed by `rfl`) or one `frequency` whose weights
    are the only thing that differs.

    The `refine congrFun (congrFun …)` rather than `apply` is because the equation compiler moved
    `bctx` and the target type into `Nat.brecOn`'s motive, so `delta` leaves them applied outside the
    `brecOn` (see `SetGen.brecOn_congr`). -/
theorem genLExprBase_tuned_eq (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) :
    genLExprBase.tuned (G := SetGen.Set) θ fctx octx pctx tvars bctx n τ
      = genLExprBase fctx octx pctx tvars bctx n τ := by
  delta genLExprBase genLExprBase.tuned
  refine congrFun (congrFun (SetGen.brecOn_congr ?heq n) bctx) τ
  case heq =>
    funext m below bctx' τ'
    dsimp only
    split
    all_goals first
      | rfl
      | (apply SetGen.frequency_congr_weights
         · rfl
         all_goals simp [Tuning.weight_pos])

/-- The payoff, spelled out once: an arbitrary soundness-and-completeness fact about the shipping
    expression generator holds of every tuning of it, with no reference to what the predicate is. -/
example (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) (P : LExpr' → Prop)
    (h : SetGen.IsSoundAndComplete
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx n τ) P) :
    SetGen.IsSoundAndComplete
      (genLExprBase.tuned (G := SetGen.Set) θ fctx octx pctx tvars bctx n τ) P :=
  SetGen.IsSoundAndComplete.of_support_eq (by rw [genLExprBase_tuned_eq]) h

end TuningPrototypes
