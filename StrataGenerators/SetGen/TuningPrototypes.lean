/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.FunctionHasTypeAGen
import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.SetGen.WeightedOptionGen
import StrataGenerators.SetGen.Tuning
import Basalt.Tuning.Macro

open Lambda RandomChoice Core Imperative
open StrataGenerators.Stmt (genCondOrNondet)
open scoped SetGen.Set

/-!
# Prototypes: transformation-targeted tunings

Two worked conversions showing how to make an existing generator's distribution tunable so a Strata
Core transformation gets non-vacuous input:

* **`PrecondElim` — tunable precondition rate.** `genPreconditionW` reworks
  `FunctionHasTypeAGen.Core.genPrecondition`'s `some`/`none` split from `optionGen` (a rational
  `coin`, invisible to `tunable def`) to `SetGen.weightedOptionGen` (a two-branch `frequency`), then
  wraps it in `tunable def` so the `some`-weight is a runtime knob. `genPreconditionW_support_eq`
  proves the reworked generator has *the same support* as the original `genPrecondition`, so every
  soundness/completeness fact about the original (`genPreconditions_complete`,
  `mem_support_genPrecondition_iff`, and thence `genFunction_complete`) transfers unchanged via
  `SetGen.IsSoundAndComplete.of_support_eq`. Only the distribution moves.

* **`LoopElim` — loop-prioritizing statement generator.** `genStmtLoopy` mirrors the `size+1` arm of
  `StmtHasTypeAGen.Core.genStmt` (same nine branches, same order) as a `tunable def`, so `loop`
  becomes flat index 8 of its single site. `loopHeavy` is the `Tuning` that boosts that branch. The
  support-preservation argument is `SetGen.support_frequency_congr_weights` exactly as for
  `genOptNat` in `TuningExamples`.

Both are standalone prototypes: the precondition one calls the *real* `genPrecondition` internals so
the support-equality is a real theorem about the shipping generator; the loop one is a faithful
standalone `tunable def` (reproducing `genStmt`'s full mutual recursion is out of scope for a
prototype). The intended production edit is to mark the real definitions `tunable` and swap the
support lemma each proof cites, as documented per-site below.
-/

namespace TuningPrototypes

-- ══════════════════════════════════════════════════════════════════════════
-- PrecondElim: a tunable precondition rate
-- ══════════════════════════════════════════════════════════════════════════

open Strata.DL.Util (FuncPrecondition)

/-- The `some`-clause body of `genPrecondition`, verbatim (3:1 toward input-mentioning clauses over
    a plain `.bool` draw, in the `inputsAsFVarCtx` free-variable context). Factored out so the
    tunable split below has exactly *one* site — the `some`/`none` choice — rather than also
    capturing this inner `frequency`, whose weights are a separate concern. -/
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

    Identical to `FunctionHasTypeAGen.Core.genPrecondition` except the outer `optionGen` (a fixed
    1/2 `coin`) is replaced by a two-branch `frequency` — the same shape as `SetGen.weightedOptionGen`
    — whose split is a tunable site. Marked `tunable`, so `genPreconditionW.tuned θ` biases the
    `some`-weight — i.e. how often a function carries a `requires` clause — at runtime, which is
    exactly the knob `PrecondElim` needs turned up. -/
tunable def genPreconditionW [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    G (Option (FuncPrecondition LExpr' Unit)) :=
  frequency (site := `genPreconditionW.present) [
    (1, fun _ => do let p ← genPrecondClause octx inputs tvars depth; pure (some p)),
    (1, fun _ => pure none)
  ] (by simp)

/-- The tunable rework has the **same support** as the shipping `genPrecondition`, so all of the
    latter's soundness/completeness results transfer to it (and, via `tuned_defaults`, to
    `genPreconditionW.tuned genPreconditionW.defaults`). This is the theorem that certifies the
    conversion is behavior-preserving: only the distribution changes.

    The proof reduces both sides to the same disjunction over `genLExpr` reachability — the RHS of
    `mem_support_genPrecondition_iff` — and closes by that iff. -/
theorem genPreconditionW_support_eq (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    SetGen.support (genPreconditionW (G := SetGen.Set) octx inputs tvars depth) =
      SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth) := by
  -- The shipping `genPrecondition` is *definitionally* `optionGen (genPrecondClause …)`: its
  -- `optionGen` payload is the very do-block we factored into `genPrecondClause`. So both sides
  -- reduce to "`none`, or `some p` for a `p` reachable by the shared clause body" — the tunable
  -- `frequency` split (here) and `optionGen`'s `coin` split (there) have the same *support*.
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

/-- Two `Tuning`s for the precondition site: the default `1:1`, and a `PrecondElim`-oriented one
    that makes preconditions present ~4× as often as absent. Both are support-total. -/
def precondDefault : Tuning := genPreconditionW.defaults
def precondHeavy   : Tuning := ⟨#[(4, 0), (1, 0)]⟩

/-- One tunable site (`present`), arity 2, no recursive calls. -/
example : genPreconditionW.sites = #[⟨`genPreconditionW.present, 0, 2, #[0, 0]⟩] := rfl

/-- Boosting the precondition rate is support-preserving for *any* `θ`: soundness/completeness of
    the function generator is unaffected: only the frequency of `requires` clauses changes. -/
example (θ : Tuning) (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    SetGen.support (genPreconditionW.tuned θ (G := SetGen.Set) octx inputs tvars depth) =
      SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth) := by
  rw [← genPreconditionW_support_eq octx inputs tvars depth,
      show (genPreconditionW (G := SetGen.Set) octx inputs tvars depth)
          = genPreconditionW.tuned genPreconditionW.defaults octx inputs tvars depth from
        (genPreconditionW.tuned_defaults octx inputs tvars depth).symm]
  apply SetGen.support_frequency_congr_weights
  · rfl
  all_goals
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · cases h; exact Tuning.weight_pos ..
    · rcases List.mem_cons.mp h with h | h
      · cases h; exact Tuning.weight_pos ..
      · simp at h

-- ══════════════════════════════════════════════════════════════════════════
-- LoopElim: a loop-prioritizing statement generator
-- ══════════════════════════════════════════════════════════════════════════

/-- A faithful standalone mirror of the `size + 1` arm of `StmtHasTypeAGen.Core.genStmt`: the same
    nine branches in the same order, so the flat-index layout matches. Marked `tunable`, so each
    branch weight is a runtime knob.

    Branch layout (`genStmtLoopy.sites[0]`, flat indices):
    `0` cmd  `1` exit  `2` funcDecl  `3` typeDecl  `4` call  `5` block  `6` ite-det  `7` ite-nondet
    `8` **loop**.

    Simplified vs the real `genStmt` only in the *leaves*: the recursive sub-statement calls are
    stubbed with `pure`/`genLExpr` so this compiles standalone. The `frequency` shape — which is all
    tuning addresses — is identical. In production this is the branch structure you would put under
    `tunable def` on the real `genStmt`; the soundness proofs there transfer because reweighting is
    support-preserving (`SetGen.support_frequency_congr_weights`), just as proved for `genOptNat`. -/
tunable def genStmtLoopy [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (labels : List String) : G (List Statement) :=
  frequency (site := `genStmtLoopy.stmt) [
    (4, fun _ => pure []),                                    -- cmd    (stub)
    (1, fun _ => pure []),                                    -- exit   (stub)
    (1, fun _ => pure []),                                    -- funcDecl(stub)
    (1, fun _ => pure []),                                    -- typeDecl(stub)
    (1, fun _ => pure []),                                    -- call   (stub)
    (2, fun _ => pure []),                                    -- block  (stub)
    (2, fun _ => do                                           -- ite-det
      let cond ← genLExpr fctx octx [] tvars [] 0 .bool
      pure [Stmt.ite (.det cond) [] [] default]),
    (1, fun _ => pure [Stmt.ite .nondet [] [] default]),      -- ite-nondet
    (2, fun _ => do                                           -- loop  ← index 8
      let guard ← genCondOrNondet fctx octx tvars 0
      pure [Stmt.loop guard none [] [] default])
  ] (by simp)

/-- One tunable site (`stmt`), arity 9. The `loop` branch is index 8. -/
example : genStmtLoopy.sites = #[⟨`genStmtLoopy.stmt, 0, 9, #[0, 0, 0, 0, 0, 0, 0, 0, 0]⟩] := rfl

/-- The default weights are the source weights (mirroring `genStmt`'s `size+1` arm). -/
example : genStmtLoopy.defaults = ⟨#[(4,0),(1,0),(1,0),(1,0),(1,0),(2,0),(2,0),(1,0),(2,0)]⟩ := rfl

/-- **`LoopElim` weighting.** Crank the `loop` branch (index 8) so loops dominate control flow,
    while every other branch keeps its default weight. A weight of 12 vs the summed rest makes a
    loop the modal statement — plenty to make `LoopElim`'s loop-elimination path non-vacuous. -/
def loopHeavy : Tuning :=
  { schedules := genStmtLoopy.defaults.schedules.set! 8 (12, 0) }

/-- Sanity: `loopHeavy` only touches the loop entry; the other eight are the defaults. -/
example : loopHeavy.schedules = #[(4,0),(1,0),(1,0),(1,0),(1,0),(2,0),(2,0),(1,0),(12,0)] := rfl

/-- Boosting loops is support-preserving for *any* `θ` (so in particular `loopHeavy`): every branch
    weight stays ≥ 1 under `Tuning.weight`, so no statement form is lost — the generator still emits
    every shape it did before, just with loops far more often. This is the fact that lets the real
    `genStmt`'s soundness/completeness proofs carry over unchanged. -/
example (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (labels : List String) :
    SetGen.support (genStmtLoopy.tuned θ (G := SetGen.Set) fctx octx tvars labels) =
      SetGen.support (genStmtLoopy (G := SetGen.Set) fctx octx tvars labels) := by
  rw [show (genStmtLoopy (G := SetGen.Set) fctx octx tvars labels)
        = genStmtLoopy.tuned genStmtLoopy.defaults fctx octx tvars labels from
      (genStmtLoopy.tuned_defaults fctx octx tvars labels).symm]
  apply SetGen.support_frequency_congr_weights
  · rfl
  all_goals
    intro p hp
    -- nine branches: peel the membership list, each weight positive by `weight_pos`.
    iterate 8
      rcases List.mem_cons.mp hp with h | hp
      · cases h; exact Tuning.weight_pos ..
    rcases List.mem_cons.mp hp with h | hp
    · cases h; exact Tuning.weight_pos ..
    · simp at hp

end TuningPrototypes
