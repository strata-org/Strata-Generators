/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.FunctionHasTypeAGen
import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.SetGen
import Basalt.Tuning.Attr

open Lambda RandomChoice Core Imperative
open StrataGenerators.Stmt (genCondOrNondet)
open scoped SetGen.Set

/-!
# Prototypes: transformation-targeted tunings

Three worked conversions showing how to make a generator's distribution tunable so a Strata Core
transformation gets non-vacuous input. Each one ends in a machine-checked theorem that the tuning is
*behavior-preserving*: at `SetGen.Set` the tuned generator is **equal** to the untuned one for every
`θ`, so every soundness/completeness result about the original applies to every tuning of it.

* **`PrecondElim`, knob 1 — the shape of a precondition, with no source edit.**
  `attribute [tunable] genPrecondition` tags the *shipping* generator from another module.  This is
  what the `@[tunable]` attribute bought over the older `tunable def` macro: because it rewrites the
  elaborated body, it does not have to be written at the definition site.  The site it finds is
  `genPrecondition`'s existing 3:1 split between an input-mentioning clause and a plain `.bool` draw,
  so `genPrecondition.tuned θ` moves that ratio at runtime.

* **`PrecondElim`, knob 2 — whether a precondition is present at all.**
  That split is `optionGen`'s rational `coin`, which is not a `frequency` and so is invisible to
  `@[tunable]`. `genPreconditionW` reworks it into the two-branch `frequency` of
  `SetGen.weightedOptionGen` (written inline, so the attribute sees it) and proves the rework has the
  same support as the shipping `genPrecondition` — so the conversion changes only the distribution.
  This is the knob `PrecondElim` needs turned up.

* **`LoopElim` — a loop-prioritizing statement generator.** `genStmtLoopy` mirrors
  `StmtHasTypeAGen.Core.genStmt`'s branch structure as a recursive `@[tunable]` generator, so `loop`
  is flat index 8 of its single site and `loopHeavy` boosts it. §3 also records, as a
  `#guard_msgs`-checked error, exactly why the *shipping* `genStmt` cannot be tagged as written.
-/

namespace TuningPrototypes

open Strata.DL.Util (FuncPrecondition)

-- ══════════════════════════════════════════════════════════════════════════
-- 1. PrecondElim, knob 1: tuning the shipping generator in place
-- ══════════════════════════════════════════════════════════════════════════

/-! `genPrecondition` (`StrataGenerators/FunctionHasTypeAGen/Core.lean`) already contains a
`frequency`: inside the `some` clause it prefers an input-mentioning precondition over a plain
`.bool` draw, 3:1. Tagging it here — from a different module, with no edit to its source — makes that
ratio a runtime knob. -/

attribute [tunable] genPrecondition

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
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    genPrecondition.tuned (G := SetGen.Set) θ octx inputs tvars depth
      = genPrecondition octx inputs tvars depth := by
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
    (tvars : List TyIdentifier) (depth : Nat) :
    SetGen.support (genPrecondition.tuned (G := SetGen.Set) θ octx inputs tvars depth)
      = SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth) := by
  rw [genPrecondition_tuned_eq]

/-- And any soundness-and-completeness fact transfers without knowing what the predicate is. -/
example (θ : Tuning) (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (P : Option (FuncPrecondition LExpr' Unit) → Prop)
    (h : SetGen.IsSoundAndComplete
      (genPrecondition (G := SetGen.Set) octx inputs tvars depth) P) :
    SetGen.IsSoundAndComplete
      (genPrecondition.tuned (G := SetGen.Set) θ octx inputs tvars depth) P :=
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
-- 3. LoopElim: a loop-prioritizing statement generator
-- ══════════════════════════════════════════════════════════════════════════

/-! ### Why the shipping `genStmt` cannot be tagged as written

`@[tunable]` no longer cares how a generator recurses, so `StmtHasTypeAGen.Core.genStmt`'s mutual
well-founded recursion is not the obstacle. Its `frequency` call is: the branch list is a `let`-bound
variable, not a literal, so the weights are not visible to be collected. -/

/--
error: tunable: `StrataGenerators.Stmt.genStmt` has a `frequency` whose branch list is not a literal list of `(weight, generator)` pairs — the weights have to be visible to be collected
-/
#guard_msgs in
attribute [tunable] StrataGenerators.Stmt.genStmt

/-! Two source changes would be needed to tune the real generator, and the second is a genuine design
question rather than a mechanical edit:

1. Inline `gs` into the `frequency` call, so the branch list is a literal.
2. Do something about `wExit`/`wCall`. They are `if labels.isEmpty then 0 else 1` — a deliberate
   weight of `0`, used to prune the `exit` and `call` branches when their support is provably empty.
   `@[tunable]` rejects a literal `0` (it would break support-completeness) and rejects a non-literal
   weight, so those two branches would have to move out of the weight and into the *list*: build one
   literal branch list per case of `labels.isEmpty`/`procs.isEmpty`. That gives up to four sites with
   different arities, and a `Tuning` would have to address each — which is why the mirror below is a
   standalone prototype rather than an edit to `genStmt`.

`genStmtLoopy` therefore reproduces `genStmt`'s branch structure — the part tuning addresses — in a
form the attribute accepts. -/

/-- A recursive mirror of `StmtHasTypeAGen.Core.genStmt`'s `size + 1` arm: the same nine branches in
    the same order, so the flat-index layout matches. Tagged `@[tunable]`, so each branch weight is a
    runtime knob.

    Branch layout (`genStmtLoopy.sites[0]`, flat indices):
    `0` cmd  `1` exit  `2` funcDecl  `3` typeDecl  `4` call  `5` block  `6` ite-det  `7` ite-nondet
    `8` **loop**.

    Simplified vs the real `genStmt` in the *leaves*: the five non-recursive branches are stubbed with
    `pure []`, the block label is fixed rather than drawn fresh, and loop measures/invariants are
    omitted. The four recursive branches do recurse, at `depth + 1`, via `partial_fixpoint` — which the
    older `tunable def` macro could not have accepted, and which is what makes the θ-invariance proof
    below a statement about the whole recursive generator rather than one site. -/
@[tunable]
def genStmtLoopy [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (labels : List String) (depth : Nat) : G (List Statement) :=
  frequency [
    (4, fun _ => pure []),                                    -- cmd      (stub)
    (1, fun _ => pure []),                                    -- exit     (stub)
    (1, fun _ => pure []),                                    -- funcDecl (stub)
    (1, fun _ => pure []),                                    -- typeDecl (stub)
    (1, fun _ => pure []),                                    -- call     (stub)
    (2, fun _ => do                                           -- block
      let body ← genStmtLoopy fctx octx tvars ("blk" :: labels) (depth + 1)
      pure [Stmt.block "blk" body default]),
    (2, fun _ => do                                           -- ite-det
      let cond ← genLExpr fctx octx [] tvars [] depth .bool
      let thenb ← genStmtLoopy fctx octx tvars labels (depth + 1)
      let elseb ← genStmtLoopy fctx octx tvars labels (depth + 1)
      pure [Stmt.ite (.det cond) thenb elseb default]),
    (1, fun _ => do                                           -- ite-nondet
      let thenb ← genStmtLoopy fctx octx tvars labels (depth + 1)
      let elseb ← genStmtLoopy fctx octx tvars labels (depth + 1)
      pure [Stmt.ite .nondet thenb elseb default]),
    (2, fun _ => do                                           -- loop  ← index 8
      let guard ← genCondOrNondet fctx octx tvars depth
      let body ← genStmtLoopy fctx octx tvars labels (depth + 1)
      pure [Stmt.loop guard none [] body default])
  ] (by simp)
partial_fixpoint

/-- One tunable site, arity 9. `holes` counts the recursive calls per branch: the five stubs make
    none, `block` and `loop` one each, and the two `ite`s two each. The `loop` branch is index 8. -/
example : genStmtLoopy.sites =
    #[⟨`TuningPrototypes.genStmtLoopy.site0, 0, 9, #[0, 0, 0, 0, 0, 1, 2, 2, 1]⟩] := rfl

/-- The default weights are the source weights (mirroring `genStmt`'s `size + 1` arm). -/
example : genStmtLoopy.defaults =
    ⟨#[(4,0),(1,0),(1,0),(1,0),(1,0),(2,0),(2,0),(1,0),(2,0)]⟩ := rfl

/-- **`LoopElim` weighting.** Crank the `loop` branch (index 8) so loops dominate control flow, while
    every other branch keeps its default weight. A weight of 12 against the summed rest makes a loop
    the modal statement — plenty to make `LoopElim`'s loop-elimination path non-vacuous. -/
def loopHeavy : Tuning :=
  { schedules := genStmtLoopy.defaults.schedules.set! 8 (12, 0) }

/-- Sanity: `loopHeavy` only touches the loop entry; the other eight are the defaults. -/
example : loopHeavy.schedules = #[(4,0),(1,0),(1,0),(1,0),(1,0),(2,0),(2,0),(1,0),(12,0)] := rfl

/-- The same weighting, made subcritical by depth: the `cmd` stub's weight grows as `4 + 8·d`, so
    loops dominate near the root and the recursion is forced closed a few levels down. This is the
    `Tuning` shape to reach for when a root-heavy weighting would otherwise exhaust the sampler's
    fuel budget. (At `SetGen.Set` the growth coefficient is invisible — see
    `genStmtLoopy_tuned_eq`: no schedule can change what is reachable.) -/
def loopHeavyDecaying : Tuning :=
  { schedules := loopHeavy.schedules.set! 0 (4, 8) }

/-! Boosting loops is behavior-preserving for *any* `θ` — so in particular for `loopHeavy` and
`loopHeavyDecaying`. Every branch weight stays ≥ 1 under `Tuning.weight`, so no statement form is
lost: the generator still reaches every shape it did before, just with loops far more often. This is
the fact that would let the real `genStmt`'s soundness/completeness proofs carry over unchanged.

The `unseal` is needed because `partial_fixpoint` definitions are irreducible and `@[tunable]` copies
that status onto `.tuned`. -/

unseal genStmtLoopy genStmtLoopy.tuned

theorem genStmtLoopy_tuned_eq (θ : Tuning) :
    (genStmtLoopy.tuned (G := SetGen.Set) θ) = genStmtLoopy := by
  -- `partial_fixpoint` hoists the arguments that never change in a recursive call out of the fix, so
  -- `fctx`, `octx` and `tvars` have to be introduced before `Lean.Order.fix` is exposed; `labels` and
  -- `depth`, which do change, are the fix's own binders.
  funext fctx octx tvars
  apply SetGen.fix_congr
  funext f labels depth
  apply SetGen.frequency_congr_weights
  · rfl
  all_goals simp [Tuning.weight_pos]

/-- The support consequence, spelled out at `loopHeavy`. -/
example (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (labels : List String)
    (depth : Nat) :
    SetGen.support (genStmtLoopy.tuned (G := SetGen.Set) loopHeavy fctx octx tvars labels depth) =
      SetGen.support (genStmtLoopy (G := SetGen.Set) fctx octx tvars labels depth) := by
  rw [genStmtLoopy_tuned_eq]

end TuningPrototypes
