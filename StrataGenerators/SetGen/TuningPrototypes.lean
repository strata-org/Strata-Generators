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

This file makes every generator that the test suite draws from tunable, and proves one theorem per
generator that the conversion preserves behaviour. At `SetGen.Set` the tuned generator is **equal** to
the untuned one for every `θ`, so every soundness and completeness result about the original applies to
every tuning of it. `StrataGenerators.TuningProfiles` holds the weights themselves, which `θ` to use for
which family of properties, and the measurements behind them. This file is the guarantee that no choice
made there can cost coverage.

* **§1 `PrecondElim`, knob 1: the shape of a precondition, with no edit to the source.**
  `StrataGenerators.TuningProfiles` tags `genPrecondition` rather than its definition site does. The
  attribute rewrites the elaborated body, so a tag need not sit at the definition site. The site it
  finds is `genPrecondition`'s existing 3 to 1 split between a clause that mentions an input and a
  plain `.bool` draw, and `genPrecondition.tuned θ` moves that ratio at run time.

* **§2 `PrecondElim`, knob 2: whether a precondition is present at all.**
  A rational `coin` in `optionGen` decides that split. A coin is not a `frequency`, so `@[tunable]`
  cannot see it. `genPreconditionW` reworks the split into the two-branch `frequency` of
  `SetGen.weightedOptionGen`, written inline so that the attribute sees it. A proof shows that the
  rework has the support the shipping `genPrecondition` has, so the conversion changes only the
  distribution. The same rework would expose the body and measure coins of `genFunction`, which is what
  the `function:` family needs. This file does not do it.

* **§3 `LoopElim`: the real statement generator.** `StrataGenerators.Stmt.genStmt` carries the tag at
  its definition site, and `genStmt_mutual_tuned_eq` proves θ-invariance for the *whole mutual block*.
  So `loop` is flat index 13 of a real knob rather than of a mirror. Two changes in
  `StmtHasTypeAGen/Core.lean` made the tag possible:

  1. The branch list of the `frequency` was a `let`-bound variable, and it is now written inline. The
     weights are therefore visible to be collected. The same one-line change unblocked `genCmd` and
     `genLExprBase`.
  2. `exit` and `call` carried the weight `if labels.isEmpty then 0 else 1`, and `@[tunable]` rejects a
     computed weight and a literal `0` alike. The *branch* now tests the condition instead of the
     weight, and falls back to `genCmdStmt`, which branch 0 already offers. Every weight in the list is
     then a positive literal, and `genStmt`'s support is unchanged because the fallback's support was
     already in the union. Both forms are throw-free, since `frequency` skips a zero-weight branch. They
     differ in one way: `cmd` now absorbs the share of a pruned branch, where the old list renormalised.

* **§4 The rest.** `genCmd`, `genLMonoTy` and `genLExprBase` carry the same θ-invariance guarantee.
  `genLExprBase` has 79 branch weights across ten per-type sites. The three cover one recursion form
  each: no recursion, `Nat.brecOn`, and `Nat.brecOn` under a wide match.
-/

namespace TuningPrototypes

open Strata.DL.Util (FuncPrecondition)

-- ══════════════════════════════════════════════════════════════════════════
-- 1. PrecondElim, knob 1: tuning the shipping generator in place
-- ══════════════════════════════════════════════════════════════════════════

/-! `genPrecondition` already contains a `frequency`. Inside the `some` clause it prefers a
precondition that mentions an input over a plain `.bool` draw, at 3 to 1.
`StrataGenerators.TuningProfiles` tags it from a different module, with no edit to its source, and that
makes the ratio a runtime knob. -/

/-- One site of arity 2, with no recursive call. The two branches are the one that mentions an input
    and the `.bool` one. -/
example : genPrecondition.sites = #[⟨`genPrecondition.site0, 0, 2, #[0, 0]⟩] := rfl

/-- The defaults are the 3 to 1 split as the source writes it. -/
example : genPrecondition.defaults = ⟨#[(3, 0), (1, 0)]⟩ := rfl

/-- Two `Tuning`s for the clause-shape site. The first is the source's 3 to 1. The second is 10 to 1,
    which all but forces every generated precondition to mention an input. Both keep the full
    support. -/
def precondDefault : Tuning := genPrecondition.defaults
def precondInputHeavy : Tuning := ⟨#[(10, 0), (1, 0)]⟩

/-- **The conversion preserves behaviour.** For every `θ`, the tuned precondition generator is *the
    same* `Set`-valued generator as the shipping one.

    `genPrecondition`'s site sits inside a `do` block, under a `dite` that binds the proof of
    `inputs.toList ≠ []`. The branch mentions that bound proof, so `rw` cannot rewrite the site in
    place. A split on the condition exposes it. Then `SetGen.frequency_eq_oneOf` sends the `frequency`
    on each side to the same weight-free `oneOf` form. The `inputs.toList = []` case has no site at
    all, so it closes by reflexivity. -/
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

/-- The support characterization proved for the shipping generator therefore holds of every tuning of
    it, after one `rw` and with no reproof. -/
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

/-- The body of `genPrecondition`'s `some` clause. It prefers a clause that mentions an input over a
    plain `.bool` draw, at 3 to 1, in the free-variable context `inputsAsFVarCtx inputs`.

    It sits in its own definition so that the tunable split below has exactly *one* site, the choice
    between `some` and `none`. Otherwise that split would also capture this inner `frequency`, which is
    knob 1's concern. `@[tunable]` inlines only the tagged declaration's own auxiliaries, so it does not
    collect a `frequency` from a separate definition like this one. -/
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

/-- `genPrecondition` with the `some` and `none` split made tunable.

    The body is `FunctionHasTypeAGen.Core.genPrecondition`'s body, with one change: a two-branch
    `frequency` replaces the outer `optionGen`, whose `coin` fixes the split at one half. That
    `frequency` is a tunable site, and it has the shape of `SetGen.weightedOptionGen`. So
    `genPreconditionW.tuned θ` biases how often a function carries a `requires` clause, and that is the
    knob `PrecondElim` needs turned up.

    The split is written out rather than delegated to `SetGen.weightedOptionGen`, because `@[tunable]`
    collects the `frequency` calls in the tagged definition's own body. The combinator takes its weights
    as variables rather than as literals, so it is not tunable itself. `genPreconditionW_eq_weighted`
    below records that the two are nonetheless the same term.

    The definition has a binder named `depth`, so the site reads its weights at that depth. A schedule
    with a nonzero growth coefficient can therefore make a precondition rarer in a deeper expression
    budget. `SetGen.Set` cannot see that, and that is the guarantee rather than a limitation: no
    schedule changes what is reachable. -/
@[tunable]
def genPreconditionW [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    G (Option (FuncPrecondition LExpr' Unit)) :=
  frequency [
    (1, fun _ => do let p ← genPrecondClause octx inputs tvars depth; pure (some p)),
    (1, fun _ => pure none)
  ] (by simp)

/-- One tunable site of arity 2, with no recursive call. -/
example : genPreconditionW.sites = #[⟨`TuningPrototypes.genPreconditionW.site0, 0, 2, #[0, 0]⟩] := rfl

example : genPreconditionW.defaults = ⟨#[(1, 0), (1, 0)]⟩ := rfl

/-- The inline split is `SetGen.weightedOptionGen`'s split at weights 1 to 1. They are the same term, so
    the support lemma for the combinator describes `genPreconditionW`'s support directly. -/
theorem genPreconditionW_eq_weighted [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    genPreconditionW (G := G) octx inputs tvars depth
      = SetGen.weightedOptionGen 1 1 (genPrecondClause octx inputs tvars depth) := rfl

/-- Two `Tuning`s for the presence site. The first is the default 1 to 1. The second aims at
    `PrecondElim` and makes a precondition present about four times as often as absent. Both keep the
    full support. -/
def presenceDefault : Tuning := genPreconditionW.defaults
def presenceHeavy : Tuning := ⟨#[(4, 0), (1, 0)]⟩

/-- The tunable rework reaches the same values as the shipping `genPrecondition`. Every soundness and
    completeness result about the shipping generator therefore transfers to the rework. This is the
    theorem that certifies the conversion: only the distribution changes.

    The proof reduces both sides to the same disjunction over what `genPrecondClause` reaches. The
    shipping `genPrecondition` is *definitionally* `optionGen (genPrecondClause …)`, because its
    `optionGen` payload is the `do` block above. So the `frequency` split here and the `coin` split
    there reach the same values. -/
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

/-! `StrataGenerators.Stmt.genStmt` carries the tag at its definition site, and
`StrataGenerators.TuningProfiles` also tags the block's shared auxiliary `genStmt._mutual`. Both are
needed, and the difference between them is the whole story of how tuning composes.

`genStmt.tuned θ` reads the weights of the statement it produces itself. Its recursion runs through
`genStmtChain`, which is the *other* member of the block, and `@[tunable]` does not rewrite that member.
So a statement nested inside a `block`, an `ite` or a `loop` body comes from the untuned generator.
Measured with `dist-report` at a `loop` weight of 40, a top-level loop went from 15% to 72%, and a loop
inside a loop went only from 2% to 7.5%.

`genStmt._mutual.tuned θ` is the whole block. Its recursion is internal, over one `WellFounded.fix` on
a `PSum` of the two members' argument tuples, so `θ` threads through all of it. Under the same
weighting, a loop inside a loop went from 3.5% to 66%.

`TuningProfiles.genStmtT` and `genStmtChainT` are therefore built on the auxiliary, and pinned to the
shipping generators at `θ = defaults`. -/

/-- **The conversion preserves behaviour, for the whole mutual block.** For every `θ`, the tuned
    statement generator is *the same* `Set`-valued generator as the shipping one. The soundness and
    completeness results for statements therefore transfer to every tuning by one `rw`, and no profile
    can make a statement shape unreachable.

    Proved by the `WellFounded.fix` recipe. `delta` exposes both sides as one fix over functionals that
    differ only in their `frequency` weights, and the recursive-call bundle `ih` is literally the same
    bound variable in both. `SetGen.wellFounded_fix_congr` then reduces the goal to equality of those
    functionals, and one `frequency_congr_weights` closes each site. The sites are the `size = 0` list
    and the `size + 1` list. The `PSum.inr` case is `genStmtChain`, which has no site of its own, so it
    closes by `rfl`. -/
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

/-! Well-founded recursion makes `genStmt` and `genStmtChain` irreducible. The two corollaries below
need to see each one as a projection of the shared auxiliary, so they need an `unseal`. -/
unseal StrataGenerators.Stmt.genStmt StrataGenerators.Stmt.genStmtChain

/-- At every `θ`, the tuned single-statement generator is `genStmt`. This reads the block's fact off
    one projection. -/
theorem genStmt_tuned_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size : Nat) :
    genStmtT (G := SetGen.Set) θ octx tvars immutableVars procs labels C ctx pctx size
      = genStmt octx tvars immutableVars procs labels C ctx pctx size := by
  unfold genStmtT
  rw [genStmt_mutual_tuned_eq]
  rfl

/-- At every `θ`, the tuned statement chain is `genStmtChain`. This is the generator the statement
    family's harness draws from. -/
theorem genStmtChain_tuned_eq (θ : Tuning) (octx : OpCtx)
    (tvars : List TyIdentifier) (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx)
    (size len : Nat) :
    genStmtChainT (G := SetGen.Set) θ octx tvars immutableVars procs labels C ctx pctx size len
      = genStmtChain octx tvars immutableVars procs labels C ctx pctx size len := by
  unfold genStmtChainT
  rw [genStmt_mutual_tuned_eq]
  rfl

/-- At every `θ`, the tuned statement-list generator is `genProgramStmts`. -/
theorem genProgramStmtsT_tuned_eq (θ : Tuning) (octx : OpCtx)
    (tvars : List TyIdentifier) (size len : Nat) (pctx : PolyOpCtx) :
    genProgramStmtsT (G := SetGen.Set) θ octx tvars size len pctx
      = genProgramStmts octx tvars size len pctx :=
  genStmtChain_tuned_eq ..

/-- At every `θ`, the tuned procedure generator is `genProcedure`. `genProcedureT` differs from the
    shipping generator only in which statement-chain generator it calls, so the block's θ-invariance is
    the whole proof. This is why the `proc:` profiles, which aim at the three transform passes, have no
    consequence for the soundness and completeness of `genProcedure`. -/
theorem genProcedureT_tuned_eq (θ : Tuning) (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (size len : Nat) (pctx : PolyOpCtx) :
    genProcedureT (G := SetGen.Set) θ octx procs C Γ size len pctx
      = StrataGenerators.Procedure.genProcedure octx procs C Γ size len pctx := by
  unfold genProcedureT StrataGenerators.Procedure.genProcedure
  simp only [genStmtChain_tuned_eq]

-- ══════════════════════════════════════════════════════════════════════════
-- 4. The command, type and expression generators
-- ══════════════════════════════════════════════════════════════════════════

/-- At every `θ`, the tuned command generator is `genCmd`. `genCmd` is not recursive, so this uses the
    first recipe in `SetGen.Tuning`'s list, with one addition. Its two sites sit in the two branches of a
    `dite`, and the `set` branches *use* that `dite`'s proof, so the proof splits on the condition first.
    §1 does the same for `genPrecondition`. -/
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

/-- At every `θ`, the tuned command *chain* is `genCmds`, for any chain length. Proved by induction on
    the length. -/
theorem genCmdsT_tuned_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (depth : Nat) :
    ∀ (n : Nat) (ctx : VarCtx),
      genCmdsT (G := SetGen.Set) θ octx tvars immutableVars ctx depth n
        = genCmds octx tvars immutableVars ctx depth n := by
  intro n
  induction n with
  | zero => intro ctx; rfl
  | succ n ih => intro ctx; simp only [genCmdsT, genCmds, genCmd_tuned_eq, ih]

/-- At every `θ`, the tuned type generator is `genLMonoTy`. Both of its sites are the same 9 to 1 split
    between a base type and a compound type, once with type variables in scope and once without.

    `genLMonoTy` recurses structurally on its depth, so this uses the `Nat.brecOn` recipe: `delta`, then
    `SetGen.brecOn_congr`, then one `frequency_congr_weights` per branch of the `n + 1` arm. The `0` arm
    is a `pick` and carries no weight, so it closes by `rfl`. -/
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
/-- At every `θ`, the tuned base expression generator is `genLExprBase`. This is the widest generator
    here: ten sites, 79 branch weights, and a match on the target type as well as on the depth.

    It needs no more work than the others, because no arm of the match has to be *named*. `split`
    produces one goal per arm, and the same matcher constant appears on both sides, because
    `@[tunable]` reuses a matcher rather than rebuilds it. Each goal is then an `n = 0` arm, which is a
    `oneOf` and closes by `rfl`, or one `frequency` whose weights are the only difference.

    The proof uses `refine congrFun (congrFun …)` rather than `apply`, because the equation compiler
    moved `bctx` and the target type into `Nat.brecOn`'s motive. `delta` therefore leaves them applied
    outside the `brecOn`. -/
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

/-- The payoff, stated once. Any soundness and completeness fact about the shipping expression
    generator holds of every tuning of it, and the proof never mentions the predicate. -/
example (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) (P : LExpr' → Prop)
    (h : SetGen.IsSoundAndComplete
      (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx n τ) P) :
    SetGen.IsSoundAndComplete
      (genLExprBase.tuned (G := SetGen.Set) θ fctx octx pctx tvars bctx n τ) P :=
  SetGen.IsSoundAndComplete.of_support_eq (by rw [genLExprBase_tuned_eq]) h

end TuningPrototypes
