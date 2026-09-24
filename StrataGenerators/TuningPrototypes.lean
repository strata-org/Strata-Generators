/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.FunctionHasTypeAGen
import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.ProcedureHasTypeAGen
import StrataGenerators.TuningProfiles
import StrataGenerators.GenSupport
import StrataGenerators.TuningSupport
import Basalt.Tuning.Attr

open Lambda RandomChoice Core Imperative
open StrataGenerators.Stmt
open StrataGenerators.TuningProfiles

/-!
# The shipping generators, tuned

This file makes every generator that the test suite draws from tunable, and proves one theorem per
generator that the conversion preserves behaviour. At `SPMF` the tuned generator is **equal** to
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
  `StrataGenerators.weightedOptionGen`, written inline so that the attribute sees it. A proof shows that the
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
  `genLExprBase` has 84 branch weights across eleven per-type sites. The three cover one recursion form
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
    place. The support congruences of `StrataGenerators.TuningSupport` walk out through the
    `optionGen`, the `bind` and the `dite` until the site is at the head, and
    `SPMF.support_frequency_congr_weights` closes it. The `inputs.toList = []` case has no site at all,
    so it closes by reflexivity. -/
theorem genPrecondition_tuned_support_eq (θ : Tuning) (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat)
    (pctx : PolyOpCtx) :
    SPMF.support (genPrecondition.tuned (G := SPMF) θ octx inputs tvars depth pctx)
      = SPMF.support (genPrecondition (G := SPMF) octx inputs tvars depth pctx) := by
  unfold genPrecondition genPrecondition.tuned
  refine SPMF.support_optionGen_congr ?_
  dsimp only
  refine SPMF.support_dite_congr (fun hne => ?_) (fun _ => rfl)
  refine SPMF.support_bind_congr ?_ (fun _ => rfl)
  apply SPMF.support_frequency_congr_weights
  · rfl
  all_goals simp [Tuning.weight_pos]

/-- Any soundness-and-completeness fact transfers without knowing what the predicate is. -/
example (θ : Tuning) (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx)
    (P : Option (FuncPrecondition LExpr' Unit) → Prop)
    (h : IsSoundAndComplete
      (genPrecondition (G := SPMF) octx inputs tvars depth pctx) P) :
    IsSoundAndComplete
      (genPrecondition.tuned (G := SPMF) θ octx inputs tvars depth pctx) P :=
  IsSoundAndComplete.of_support_eq (genPrecondition_tuned_support_eq ..) h

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
    `frequency` is a tunable site, and it has the shape of `StrataGenerators.weightedOptionGen`. So
    `genPreconditionW.tuned θ` biases how often a function carries a `requires` clause, and that is the
    knob `PrecondElim` needs turned up.

    The split is written out rather than delegated to `StrataGenerators.weightedOptionGen`, because `@[tunable]`
    collects the `frequency` calls in the tagged definition's own body. The combinator takes its weights
    as variables rather than as literals, so it is not tunable itself. `genPreconditionW_eq_weighted`
    below records that the two are nonetheless the same term.

    The definition has a binder named `depth`, so the site reads its weights at that depth. A schedule
    with a nonzero growth coefficient can therefore make a precondition rarer in a deeper expression
    budget. `SPMF` cannot see that, and that is the guarantee rather than a limitation: no
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

/-- The inline split is `StrataGenerators.weightedOptionGen`'s split at weights 1 to 1. They are the same term, so
    the support lemma for the combinator describes `genPreconditionW`'s support directly. -/
theorem genPreconditionW_eq_weighted [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    genPreconditionW (G := G) octx inputs tvars depth
      = StrataGenerators.weightedOptionGen 1 1 (genPrecondClause octx inputs tvars depth) := rfl

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
    SPMF.support (genPreconditionW (G := SPMF) octx inputs tvars depth) =
      SPMF.support (genPrecondition (G := SPMF) octx inputs tvars depth) := by
  have hrhs : genPrecondition (G := SPMF) octx inputs tvars depth
      = optionGen (genPrecondClause octx inputs tvars depth) := rfl
  ext o
  rw [hrhs, SPMF.mem_support_optionGen_iff]
  simp only [genPreconditionW, SPMF.mem_support_frequency_iff]
  constructor
  · rintro ⟨w, g, hmem, _, hg⟩
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff] at hg
      obtain ⟨p, hp, rfl⟩ := hg
      exact Or.inr ⟨p, hp, rfl⟩
    · rcases List.mem_cons.mp hmem' with heq | hnil
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        simp only [SPMF.mem_support_pure_iff] at hg
        exact Or.inl hg
      · simp at hnil
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · refine ⟨1, _, List.mem_cons_of_mem _ List.mem_cons_self, by omega, ?_⟩
      simp only [SPMF.mem_support_pure_iff]
    · refine ⟨1, _, List.mem_cons_self, by omega, ?_⟩
      simp only [SPMF.mem_support_bind_iff, SPMF.mem_support_pure_iff]
      exact ⟨p, hp, rfl⟩

/-- Boosting the precondition rate is behavior-preserving for *any* `θ`, so soundness/completeness of
    the function generator is unaffected: only the frequency of `requires` clauses changes. -/
theorem genPreconditionW_tuned_support_eq (θ : Tuning) (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier) (depth : Nat) :
    SPMF.support (genPreconditionW.tuned (G := SPMF) θ octx inputs tvars depth)
      = SPMF.support (genPreconditionW (G := SPMF) octx inputs tvars depth) := by
  unfold genPreconditionW genPreconditionW.tuned
  apply SPMF.support_frequency_congr_weights
  · rfl
  all_goals simp [Tuning.weight_pos]

/-- Chaining the two: every tuning of the reworked generator has the shipping generator's support. -/
example (θ : Tuning) (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) :
    SPMF.support (genPreconditionW.tuned (G := SPMF) θ octx inputs tvars depth) =
      SPMF.support (genPrecondition (G := SPMF) octx inputs tvars depth) := by
  rw [genPreconditionW_tuned_support_eq, genPreconditionW_support_eq]

-- ══════════════════════════════════════════════════════════════════════════
-- 3. LoopElim: the real statement generator
-- ══════════════════════════════════════════════════════════════════════════

/-! `StrataGenerators.Stmt.genStmt` carries the tag at its definition site, and
`StrataGenerators.TuningProfiles` also tags the block's shared auxiliary `genStmt._mutual`. Both are
needed, and the difference between them is the whole story of how tuning composes. -/

/-- The relation the block's two members share: equality of supports. It has to be stated by cases on
    the `PSum`, because the shared auxiliary's result type is a `PSum.casesOn` and the two members
    return different types. -/
@[reducible] private def SuppEq :
    ∀ x : (_ : List String) ×' (_ : LContext CoreLParams) ×' (_ : VarCtx) ×' Nat ⊕'
           (_ : List String) ×' (_ : LContext CoreLParams) ×' (_ : VarCtx) ×' (_ : Nat) ×' Nat,
      (PSum.casesOn x (fun _ => SPMF GenStmtResult)
        (fun _ => SPMF (List Statement × LContext CoreLParams × VarCtx))) →
      (PSum.casesOn x (fun _ => SPMF GenStmtResult)
        (fun _ => SPMF (List Statement × LContext CoreLParams × VarCtx))) → Prop
  | .inl _ => fun a b => SPMF.support a = SPMF.support b
  | .inr _ => fun a b => SPMF.support a = SPMF.support b

/-- **The conversion preserves behaviour, for the whole mutual block.** For every `θ`, the tuned
    statement generator reaches exactly the statements the shipping one reaches. The soundness and
    completeness results for statements therefore transfer to every tuning, and no profile can make a
    statement shape unreachable.

    `delta` exposes both sides as one `WellFounded.fix` — `@[tunable]` never re-runs the equation
    compiler, so the accessibility proof is shared — over step functions that differ only in their
    `frequency` weights. `StrataGenerators.wellFounded_fix_rel` then hands the recursive calls' support
    equation to the step, and `support_congr` walks each body down to its sites. The sites are the
    `size = 0` list and the `size + 1` list; the `PSum.inr` member, `genStmtChain`, has no site of its
    own. -/
theorem genStmt_mutual_tuned_support_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx) :
    ∀ x, SuppEq x
      (genStmt._mutual.tuned (G := SPMF) θ octx tvars immutableVars procs pctx x)
      (genStmt._mutual (G := SPMF) octx tvars immutableVars procs pctx x) := by
  delta StrataGenerators.Stmt.genStmt._mutual StrataGenerators.Stmt.genStmt._mutual.tuned
  apply StrataGenerators.wellFounded_fix_rel
  intro x g g' hgg'
  -- Specialise the bundle at each `PSum` constructor. `SuppEq` matches on that constructor, so a
  -- hypothesis stated at `.inl`/`.inr` reduces to a plain support equation and unifies against the
  -- recursive calls in the body; `hgg'` at an unknown index does not.
  have hInl : ∀ y hy, SPMF.support (g (.inl y) hy) = SPMF.support (g' (.inl y) hy) :=
    fun y hy => hgg' (.inl y) hy
  have hInr : ∀ y hy, SPMF.support (g (.inr y) hy) = SPMF.support (g' (.inr y) hy) :=
    fun y hy => hgg' (.inr y) hy
  cases x with
  | inl a =>
    obtain ⟨labels, C, ctx, n⟩ := a
    show SPMF.support _ = SPMF.support _
    dsimp only
    cases n with
    | zero => support_congr [hInl, hInr]
    | succ size => support_congr [hInl, hInr]
  | inr a =>
    obtain ⟨labels, C, ctx, size, len⟩ := a
    show SPMF.support _ = SPMF.support _
    dsimp only
    cases len with
    | zero => support_congr [hInl, hInr]
    | succ len => support_congr [hInl, hInr]

/-! Well-founded recursion makes `genStmt` and `genStmtChain` irreducible. The two corollaries below
need to see each one as a projection of the shared auxiliary, so they need an `unseal`. -/
unseal StrataGenerators.Stmt.genStmt StrataGenerators.Stmt.genStmtChain

/-- At every `θ`, the tuned single-statement generator reaches what `genStmt` reaches. This reads the
    block's fact off one projection. -/
theorem genStmt_tuned_support_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size : Nat) :
    SPMF.support (genStmtT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size)
      = SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size) :=
  genStmt_mutual_tuned_support_eq θ octx tvars immutableVars procs pctx
    (.inl ⟨labels, C, ctx, size⟩)

/-- At every `θ`, the tuned statement chain reaches what `genStmtChain` reaches. This is the generator
    the statement family's harness draws from. -/
theorem genStmtChain_tuned_support_eq (θ : Tuning) (octx : OpCtx)
    (tvars : List TyIdentifier) (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx)
    (size len : Nat) :
    SPMF.support
        (genStmtChainT (G := SPMF) θ octx tvars immutableVars procs labels C ctx pctx size len)
      = SPMF.support
        (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size len) :=
  genStmt_mutual_tuned_support_eq θ octx tvars immutableVars procs pctx
    (.inr ⟨labels, C, ctx, size, len⟩)

/-- At every `θ`, the tuned statement-list generator reaches what `genProgramStmts` reaches. -/
theorem genProgramStmtsT_tuned_support_eq (θ : Tuning) (octx : OpCtx)
    (tvars : List TyIdentifier) (size len : Nat) (pctx : PolyOpCtx) :
    SPMF.support (genProgramStmtsT (G := SPMF) θ octx tvars size len pctx)
      = SPMF.support (genProgramStmts (G := SPMF) octx tvars size len pctx) :=
  genStmtChain_tuned_support_eq ..

/-- At every `θ`, the tuned procedure generator is `genProcedure`. `genProcedureT` differs from the
    shipping generator only in which statement-chain generator it calls, so the block's θ-invariance is
    the whole proof. This is why the `proc:` profiles, which aim at the three transform passes, have no
    consequence for the soundness and completeness of `genProcedure`. -/
theorem genProcedureT_tuned_support_eq (θ : Tuning) (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (size len : Nat) (pctx : PolyOpCtx) :
    SPMF.support (genProcedureT (G := SPMF) θ octx procs C Γ size len pctx)
      = SPMF.support
        (StrataGenerators.Procedure.genProcedure (G := SPMF) octx procs C Γ size len pctx) := by
  unfold genProcedureT StrataGenerators.Procedure.genProcedure
  -- The two `do` blocks agree draw for draw except for the statement-chain call, so descend through
  -- the binds and use the block's fact at the one that differs.
  repeat' first
    | refine SPMF.support_bind_congr rfl (fun _ => ?_)
    | refine SPMF.support_bind_congr (genStmtChain_tuned_support_eq ..) (fun _ => ?_)
    | rfl

-- ══════════════════════════════════════════════════════════════════════════
-- 4. The command, type and expression generators
-- ══════════════════════════════════════════════════════════════════════════

/-- At every `θ`, the tuned command generator is `genCmd`. `genCmd` is not recursive, so this uses the
    site-under-`bind` shape of `StrataGenerators.TuningSupport`, with one addition. Its two sites sit in the two branches of a
    `dite`, and the `set` branches *use* that `dite`'s proof, so the proof splits on the condition first.
    §1 does the same for `genPrecondition`. -/
theorem genCmd_tuned_support_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx) :
    SPMF.support (genCmd.tuned (G := SPMF) θ octx tvars immutableVars ctx depth pctx)
      = SPMF.support (genCmd (G := SPMF) octx tvars immutableVars ctx depth pctx) := by
  unfold genCmd genCmd.tuned
  by_cases h : (ctx.writable immutableVars).length > 0
  · simp only [dif_pos h]
    apply SPMF.support_frequency_congr_weights
    · rfl
    all_goals simp [Tuning.weight_pos]
  · simp only [dif_neg h]
    apply SPMF.support_frequency_congr_weights
    · rfl
    all_goals simp [Tuning.weight_pos]

/-- At every `θ`, the tuned command *chain* is `genCmds`, for any chain length. Proved by induction on
    the length. -/
theorem genCmdsT_tuned_support_eq (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (depth : Nat) :
    ∀ (n : Nat) (ctx : VarCtx),
      SPMF.support (genCmdsT (G := SPMF) θ octx tvars immutableVars ctx depth n)
        = SPMF.support (genCmds (G := SPMF) octx tvars immutableVars ctx depth n) := by
  intro n
  induction n with
  | zero => intro ctx; rfl
  | succ n ih =>
    intro ctx
    simp only [genCmdsT, genCmds]
    exact SPMF.support_bind_congr (genCmd_tuned_support_eq ..)
      (fun _ => SPMF.support_bind_congr (ih _) (fun _ => rfl))

/-- At every `θ`, the tuned type generator is `genLMonoTy`. Both of its sites are the same 9 to 1 split
    between a base type and a compound type, once with type variables in scope and once without.

    `genLMonoTy` recurses structurally on its depth, so this uses the `Nat.brecOn` recipe: `delta`, then
    `StrataGenerators.brecOn_congr`, then one `frequency_congr_weights` per branch of the `n + 1` arm. The `0` arm
    is a `pick` and carries no weight, so it closes by `rfl`. -/
theorem genLMonoTy_tuned_support_eq (θ : Tuning) (tvars : List TyIdentifier) :
    ∀ n, SPMF.support (genLMonoTy.tuned (G := SPMF) θ tvars n)
      = SPMF.support (genLMonoTy (G := SPMF) tvars n) := by
  intro n
  induction n with
  | zero =>
    -- The depth-0 arm is a `pick` and carries no weight, so the two generators are equal there.
    rfl
  | succ k ih =>
    -- `eq_def` unfolds the shipping generator; the tuned copy has no equation lemmas, so `delta`
    -- plus `dsimp only` reduces its `Nat.brecOn` at the successor. The recursive occurrences come
    -- out as the raw `Nat.rec` term, which is *definitionally* `genLMonoTy.tuned θ tvars k`, so the
    -- induction hypothesis still applies through `exact`.
    rw [genLMonoTy.eq_def]
    delta genLMonoTy.tuned
    dsimp only
    have hcompound : ∀ (gs gs' : List (Unit → SPMF LMonoTy)) (hne : gs ≠ []) (hne' : gs' ≠ []),
        List.Forall₂ (fun g g' => SPMF.support (g ()) = SPMF.support (g' ())) gs gs' →
        SPMF.support (oneOf gs hne) = SPMF.support (oneOf gs' hne') :=
      fun _ _ _ _ hrel => SPMF.support_oneOf_congr _ _ hrel
    have harrow : ∀ f : LMonoTy → LMonoTy → LMonoTy,
        SPMF.support (do let τ₁ ← genLMonoTy.tuned (G := SPMF) θ tvars k
                         let τ₂ ← genLMonoTy.tuned (G := SPMF) θ tvars k
                         pure (f τ₁ τ₂))
          = SPMF.support (do let τ₁ ← genLMonoTy (G := SPMF) tvars k
                             let τ₂ ← genLMonoTy (G := SPMF) tvars k
                             pure (f τ₁ τ₂)) :=
      fun _ => SPMF.support_bind_congr ih (fun _ => SPMF.support_bind_congr ih (fun _ => rfl))
    have hseq : ∀ f : LMonoTy → LMonoTy,
        SPMF.support (do let τ ← genLMonoTy.tuned (G := SPMF) θ tvars k; pure (f τ))
          = SPMF.support (do let τ ← genLMonoTy (G := SPMF) tvars k; pure (f τ)) :=
      fun _ => SPMF.support_bind_congr ih (fun _ => rfl)
    -- Split the `dite` with a congruence rather than with `dif_pos`/`dif_neg`: rewriting the
    -- condition away would rewrite it inside the recursive occurrences too, and those have to stay
    -- definitionally `genLMonoTy.tuned θ tvars k` for `ih` to apply.
    refine SPMF.support_dite_congr (fun h => ?_) (fun h => ?_)
    · apply SPMF.support_frequency_congr_branches
      · simp [Tuning.weight_pos]
      · simp
      · refine List.Forall₂.cons rfl (List.Forall₂.cons ?_ List.Forall₂.nil)
        refine hcompound _ _ (by simp) (by simp) ?_
        exact List.Forall₂.cons (harrow LMonoTy.arrow)
          (List.Forall₂.cons (harrow LMonoTy.map)
            (List.Forall₂.cons (hseq LMonoTy.seq) (List.Forall₂.cons rfl .nil)))
    · apply SPMF.support_frequency_congr_branches
      · simp [Tuning.weight_pos]
      · simp
      · refine List.Forall₂.cons rfl (List.Forall₂.cons ?_ List.Forall₂.nil)
        refine hcompound _ _ (by simp) (by simp) ?_
        exact List.Forall₂.cons (harrow LMonoTy.arrow)
          (List.Forall₂.cons (harrow LMonoTy.map) (List.Forall₂.cons (hseq LMonoTy.seq) .nil))

/-! ### The two argument-generator wrappers that `support_congr` cannot walk into

`genAbs`, `genApp`, `genIte`, `genEq` and `genQuant` are `@[reducible]`, so the `support_congr` tactic
unfolds them and descends through their `bind`s on its own. `genIndir` and `genIndirPolyCore` are plain
`def`s, so it cannot, and a leaf that mentions one of them would fall through to the tactic's expensive
last resorts. These two lemmas are the leaves for those branches: each says that the generator's support
depends on its argument generator (and, for the polymorphic rule, its fallback) only through *their*
supports. -/

/-- The support of the monomorphic Indir rule depends on `genArg` only through its support: the rule
    draws one operator and then draws each argument with a `mapM` over `genArg`. -/
theorem support_genIndir_congr (octx : OpCtx) (τ : LMonoTy)
    {genArg genArg' : LMonoTy → SPMF LExpr'}
    (hArg : ∀ σ, (genArg σ).support = (genArg' σ).support)
    (h : (findOpsInCtx octx τ).length > 0) :
    (genIndir (G := SPMF) octx τ genArg h).support
      = (genIndir (G := SPMF) octx τ genArg' h).support := by
  unfold genIndir
  refine SPMF.support_bind_congr rfl (fun p => ?_)
  obtain ⟨name, argTys⟩ := p
  exact SPMF.support_bind_congr (SPMF.support_mapM_congr hArg argTys) (fun _ => rfl)

/-- The support of the polymorphic IndirPoly rule depends on `genArg` and on `fallback` only through
    their supports. The type-sampling prefix does not mention either, so it stays put. -/
theorem support_genIndirPolyCore_congr (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (bctx : BVarCtx) (τ : LMonoTy)
    {genArg genArg' : LMonoTy → SPMF LExpr'} {fallback fallback' : SPMF LExpr'}
    (hArg : ∀ σ, (genArg σ).support = (genArg' σ).support)
    (hfb : fallback.support = fallback'.support) (maxNumArgs : Nat) :
    (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ genArg fallback maxNumArgs).support
      = (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ genArg' fallback' maxNumArgs).support := by
  unfold genIndirPolyCore
  refine SPMF.support_bind_congr rfl (fun sampledTys => ?_)
  refine SPMF.support_dite_congr (fun hops => ?_) (fun _ => hfb)
  refine SPMF.support_bind_congr rfl (fun p => ?_)
  obtain ⟨functionName, argTys⟩ := p
  exact SPMF.support_bind_congr (SPMF.support_mapM_congr hArg argTys) (fun _ => rfl)

/-! ### θ-invariance of `genLExprBase`, arm by arm

`@[tunable]` emits `.tuned` with `addDecl`, and it derives `.tuned.eq_def` only for a
`partial_fixpoint` body. `genLExprBase` recurses structurally, so `genLExprBase.tuned` has no equation
lemmas at all: unfolded, it is `(genLExprBase.match_1 … n τ arms) bundle`, a 22-arm matcher
*over-applied* to the `Nat.below` bundle that carries the recursive call. `dsimp only` will not reduce
that, `split` picks a `dite` from inside an arm instead of the match, and `split at` fails outright with
`Failed to find match-expression discriminants`.

Three moves get around it.

1. **Keep the two sides in step.** Generalise the depth back to a variable before splitting — the
   `hgen` of each branch below — so `split` fires on the shipping side at a *variable* discriminant and
   substitutes the depth and `τ` into the tuned side as well. Both then reduce together.
2. **One lemma per arm.** At a constructor pattern the tuned side whnfs to its `frequency`, so
   `apply SPMF.support_frequency_congr_branches` unifies straight through the matcher. That whnf costs
   between 1M and 8M heartbeats *per arm*, so all 21 arms in one declaration overruns any budget; each
   arm is its own lemma with its own.
3. **The catch-alls by matcher equation.** `genLExprBase.match_1.eq_21` and `.eq_22` take exactly the
   ten negative facts about `τ` that `split` hands over, and rewrite the matcher — the over-applied one
   included — to the catch-all arm. They are generated on demand and resolve by name.

Nothing here needs a `θ` to be well-behaved. `Tuning.weight` is `max a 1 + d * b`, so
`Tuning.weight_pos` holds for every `θ`, index and depth, and a schedule entry of `(0, 0)` reads as
weight 1. A `θ` moves weights and never the branch list, so no `θ` can drop a branch out of the
support; pruning one takes an edit to the `frequency` itself. -/

/-- The induction hypothesis of `genLExprBase_tuned_support_eq`, named so that the per-arm lemmas can
    take it as a premise. -/
abbrev TunedIH (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (k : Nat) : Prop :=
  ∀ (b : BVarCtx) (σ : LMonoTy),
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars b k σ).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars b k σ).support

/-- Close one successor arm. Both sides are a `frequency` over the same branch list, so the three real
    obligations are: every tuned weight is positive (`Tuning.weight_pos`), every shipping weight is
    (they are literals), and the branches agree in support. The last one walks down through the
    `@[reducible]` wrappers — `genAbs`, `genApp`, `genIte`, `genEq`, `genQuant` — to leaves closed by the
    induction hypothesis, or by the two congruences above for the `Indir` and `IndirPoly` branches,
    whose generators are plain `def`s the walk cannot enter. -/
macro "arm_close " ih:ident : tactic =>
  `(tactic|
    (apply SPMF.support_frequency_congr_branches <;>
      first
        | (intro _ hmem; (fin_cases hmem <;> simp [Tuning.weight_pos]); done)
        | exact Tuning.sum_map_fst_pos _ _ _ _ _
        | ((repeat' first
              | exact $ih _ _
              | exact support_genIndir_congr _ _ (fun σ' => $ih _ σ') _
              | exact support_genIndirPolyCore_congr _ _ _ _ _ (fun σ' => $ih _ σ') ($ih _ _) 3
              | refine SPMF.support_bind_congr ?_ (fun _ => ?_)
              | refine SPMF.support_dite_congr (fun _ => ?_) (fun _ => ?_)
              | refine List.Forall₂.cons ?_ ?_
              | exact List.Forall₂.nil
              | rfl); done)
        | (simp; done)))

set_option maxHeartbeats 8000000 in
private theorem arm_arrow_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat) (τ₁ τ₂ : LMonoTy)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) (LMonoTy.arrow τ₁ τ₂)).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) (LMonoTy.arrow τ₁ τ₂)).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_bool_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) LMonoTy.bool).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) LMonoTy.bool).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_int_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) LMonoTy.int).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) LMonoTy.int).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_ftvar_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat) (name : TyIdentifier)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) (LMonoTy.ftvar name)).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) (LMonoTy.ftvar name)).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_string_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) LMonoTy.string).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) LMonoTy.string).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_real_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) LMonoTy.real).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) LMonoTy.real).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_bitvec_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat) (w : Nat)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) (LMonoTy.bitvec w)).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) (LMonoTy.bitvec w)).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_regex_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) LMonoTy.regex).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) LMonoTy.regex).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_map_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat) (τ₁ τ₂ : LMonoTy)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) (LMonoTy.map τ₁ τ₂)).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) (LMonoTy.map τ₁ τ₂)).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
private theorem arm_seq_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat) (σ : LMonoTy)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) (LMonoTy.seq σ)).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) (LMonoTy.seq σ)).support := by
  arm_close ih
set_option maxHeartbeats 8000000 in
/-- The successor catch-all: a target type the generator has no rule for. The matcher cannot reduce at
    an opaque `τ`, so `genLExprBase.match_1.eq_22` does it instead, consuming the ten negative facts
    that `split` provides. -/
private theorem arm_other_succ (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (k : Nat) (τ : LMonoTy)
    (hArrow : ∀ τ₁ τ₂, τ = LMonoTy.tcons "arrow" [τ₁, τ₂] → False)
    (hBool : τ = LMonoTy.tcons "bool" [] → False)
    (hInt : τ = LMonoTy.tcons "int" [] → False)
    (hFtvar : ∀ nm, τ = LMonoTy.ftvar nm → False)
    (hString : τ = LMonoTy.tcons "string" [] → False)
    (hReal : τ = LMonoTy.tcons "real" [] → False)
    (hBitvec : ∀ w, τ = LMonoTy.bitvec w → False)
    (hRegex : τ = LMonoTy.tcons "regex" [] → False)
    (hMap : ∀ τ₁ τ₂, τ = LMonoTy.tcons "Map" [τ₁, τ₂] → False)
    (hSeq : ∀ σ, τ = LMonoTy.tcons "Sequence" [σ] → False)
    (ih : TunedIH θ fctx octx pctx tvars k) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx (k + 1) τ).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx (k + 1) τ).support := by
  unfold genLExprBase.tuned
  dsimp only
  rw [genLExprBase.eq_def]
  simp only [genLExprBase.match_1.eq_22]
  arm_close ih

set_option maxHeartbeats 8000000 in
/-- The depth-0 catch-all. Same shape as `arm_other_succ`, with `eq_21`; at depth 0 the two `oneOf`s
    carry no weight, so the branches agree by reflexivity. -/
private theorem arm_other_zero (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (τ : LMonoTy)
    (hArrow : ∀ τ₁ τ₂, τ = LMonoTy.tcons "arrow" [τ₁, τ₂] → False)
    (hBool : τ = LMonoTy.tcons "bool" [] → False)
    (hInt : τ = LMonoTy.tcons "int" [] → False)
    (hFtvar : ∀ nm, τ = LMonoTy.ftvar nm → False)
    (hString : τ = LMonoTy.tcons "string" [] → False)
    (hReal : τ = LMonoTy.tcons "real" [] → False)
    (hBitvec : ∀ w, τ = LMonoTy.bitvec w → False)
    (hRegex : τ = LMonoTy.tcons "regex" [] → False)
    (hMap : ∀ τ₁ τ₂, τ = LMonoTy.tcons "Map" [τ₁, τ₂] → False)
    (hSeq : ∀ σ, τ = LMonoTy.tcons "Sequence" [σ] → False) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx 0 τ).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx 0 τ).support := by
  -- At the literal `0` the depth is an `OfNat` numeral, so `Nat.brecOn.go`'s `Nat.rec` does not
  -- iota-reduce the way it does at `k + 1`. Restating the depth as `Nat.zero` — the same term up to
  -- defeq — puts a constructor there and lets the reduction fire.
  show (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx Nat.zero τ).support
    = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx Nat.zero τ).support
  unfold genLExprBase.tuned
  try dsimp only [Nat.brecOn, Nat.brecOn.go]
  try dsimp only
  rw [genLExprBase.eq_def]
  simp only [genLExprBase.match_1.eq_21]
set_option maxHeartbeats 8000000 in
/-- Depth 0, every target type. No arm carries a weight at depth 0 — each is a uniform `oneOf` — so the
    tuned generator and the shipping one are the *same* generator there, and every arm closes by
    reflexivity. The case analysis goes through the matcher's own splitter rather than `split`, so the
    shipping side is never reduced and each arm's goal keeps the shape the lemmas are stated in. -/
private theorem arm_zero_all (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (τ : LMonoTy) :
    (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx 0 τ).support
      = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx 0 τ).support := by
  refine genLExprBase.match_1.splitter
    (motive := fun m t => m = 0 →
      (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx m t).support
        = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx m t).support)
    0 τ
      (fun τ₁ τ₂ _ => rfl)
      (fun _ _ _ h => absurd h (by omega))
      (fun _ _ => rfl)
      (fun _ h => absurd h (by omega))
      (fun _ _ => rfl)
      (fun _ h => absurd h (by omega))
      (fun nm _ => rfl)
      (fun _ _ h => absurd h (by omega))
      (fun _ _ => rfl)
      (fun _ h => absurd h (by omega))
      (fun _ _ => rfl)
      (fun _ h => absurd h (by omega))
      (fun w _ => rfl)
      (fun _ _ h => absurd h (by omega))
      (fun _ _ => rfl)
      (fun _ h => absurd h (by omega))
      (fun τ₁ τ₂ _ => rfl)
      (fun _ _ _ h => absurd h (by omega))
      (fun σ _ => rfl)
      (fun _ _ h => absurd h (by omega))
      (fun t hA hB hC hD hE hF hG hH hI hJ _ => arm_other_zero θ fctx octx pctx tvars bctx t hA hB hC hD hE hF hG hH hI hJ)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (by omega))
    rfl

set_option maxHeartbeats 4000000 in
/-- **At every `θ`, the tuned base expression generator has the support `genLExprBase` has.** Eleven
    sites, 84 branch weights, and a match on the target type as well as on the depth. The section note
    above explains the three moves; this theorem is only the dispatch, one line per arm.

    The motive carries `m = k + 1` so that the splitter's depth-0 arms are discharged by `omega` rather
    than proved twice; `arm_zero_all` handles depth 0 on its own. -/
theorem genLExprBase_tuned_support_eq (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) :
    ∀ (n : Nat) (bctx : BVarCtx) (τ : LMonoTy),
      SPMF.support (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx n τ)
        = SPMF.support (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n τ) := by
  intro n
  induction n with
  | zero => intro bctx τ; exact arm_zero_all θ fctx octx pctx tvars bctx τ
  | succ k ih =>
    intro bctx τ
    refine genLExprBase.match_1.splitter
      (motive := fun m t => m = k + 1 →
        (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx m t).support
          = (genLExprBase (G := SPMF) fctx octx pctx tvars bctx m t).support)
      (k + 1) τ
      (fun _ _ h => absurd h (by omega))
      (fun j τ₁ τ₂ h => by cases Nat.succ.inj h; exact arm_arrow_succ θ fctx octx pctx tvars bctx _ τ₁ τ₂ ih)
      (fun _ h => absurd h (by omega))
      (fun j h => by cases Nat.succ.inj h; exact arm_bool_succ θ fctx octx pctx tvars bctx _ ih)
      (fun _ h => absurd h (by omega))
      (fun j h => by cases Nat.succ.inj h; exact arm_int_succ θ fctx octx pctx tvars bctx _ ih)
      (fun _ h => absurd h (by omega))
      (fun j nm h => by cases Nat.succ.inj h; exact arm_ftvar_succ θ fctx octx pctx tvars bctx _ nm ih)
      (fun _ h => absurd h (by omega))
      (fun j h => by cases Nat.succ.inj h; exact arm_string_succ θ fctx octx pctx tvars bctx _ ih)
      (fun _ h => absurd h (by omega))
      (fun j h => by cases Nat.succ.inj h; exact arm_real_succ θ fctx octx pctx tvars bctx _ ih)
      (fun _ h => absurd h (by omega))
      (fun j w h => by cases Nat.succ.inj h; exact arm_bitvec_succ θ fctx octx pctx tvars bctx _ w ih)
      (fun _ h => absurd h (by omega))
      (fun j h => by cases Nat.succ.inj h; exact arm_regex_succ θ fctx octx pctx tvars bctx _ ih)
      (fun _ _ h => absurd h (by omega))
      (fun j τ₁ τ₂ h => by cases Nat.succ.inj h; exact arm_map_succ θ fctx octx pctx tvars bctx _ τ₁ τ₂ ih)
      (fun _ h => absurd h (by omega))
      (fun j σ h => by cases Nat.succ.inj h; exact arm_seq_succ θ fctx octx pctx tvars bctx _ σ ih)
      (fun _ _ _ _ _ _ _ _ _ _ _ h => absurd h (by omega))
      (fun _ t hA hB hC hD hE hF hG hH hI hJ h => by cases Nat.succ.inj h; exact arm_other_succ θ fctx octx pctx tvars bctx _ t hA hB hC hD hE hF hG hH hI hJ ih)
      rfl

/-- The payoff, stated once. Any soundness and completeness fact about the shipping expression
    generator holds of every tuning of it, and the proof never mentions the predicate. -/
example (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) (P : LExpr' → Prop)
    (h : IsSoundAndComplete
      (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n τ) P) :
    IsSoundAndComplete
      (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx n τ) P :=
  IsSoundAndComplete.of_support_eq (genLExprBase_tuned_support_eq θ fctx octx pctx tvars n bctx τ) h

end TuningPrototypes
