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
  simp only [mem_support_pure_iff, genPreconditionW, SPMF.mem_support_frequency_iff]
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
    first recipe in `SetGen.Tuning`'s list, with one addition. Its two sites sit in the two branches of a
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

set_option maxHeartbeats 1000000 in
/-- At every `θ`, the tuned base expression generator is `genLExprBase`. This is the widest generator
    here: eleven sites, 84 branch weights, and a match on the target type as well as on the depth.

    It needs no more work than the others, because no arm of the match has to be *named*. `split`
    produces one goal per arm, and the same matcher constant appears on both sides, because
    `@[tunable]` reuses a matcher rather than rebuilds it. Each goal is then an `n = 0` arm, which is a
    `oneOf` and closes by `rfl`, or one `frequency` whose weights are the only difference.

    The proof uses `refine congrFun (congrFun …)` rather than `apply`, because the equation compiler
    moved `bctx` and the target type into `Nat.brecOn`'s motive. `delta` therefore leaves them applied
    outside the `brecOn`. -/
theorem genLExprBase_tuned_support_eq (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) :
    ∀ (n : Nat) (bctx : BVarCtx) (τ : LMonoTy),
      SPMF.support (genLExprBase.tuned (G := SPMF) θ fctx octx pctx tvars bctx n τ)
        = SPMF.support (genLExprBase (G := SPMF) fctx octx pctx tvars bctx n τ) := by
  -- **Not proved.** The recipe that closes `genLMonoTy_tuned_support_eq` — induct on the depth,
  -- unfold the shipping generator with `eq_def`, `delta`-and-`dsimp` the tuned copy's `Nat.brecOn`,
  -- then `support_congr` — does not reach here, and the obstruction is specific to this generator.
  --
  -- `genLExprBase` recurses structurally on the depth but *matches on the depth and the target type
  -- together*, and the equation compiler moves `bctx` and `τ` into `Nat.brecOn`'s motive. So `delta`
  -- leaves the tuned side as `Nat.brecOn.go … 0 (fun x f bctx τ => match x, τ with …)`, with the
  -- matcher applied to an argument the tactic block cannot see through: `dsimp only` reduces neither
  -- the `brecOn.go` nor the matcher, and `split` therefore splits the shipping side alone and the two
  -- sides fall out of step. The old proof sidestepped all of this by working at the *functional*
  -- level (`brecOn_congr` reduced the goal to an equality of step functions, which `Set` made true);
  -- at `SPMF` the step functions are genuinely unequal, so that route is closed.
  --
  -- What it needs is a support-level congruence for `Nat.brecOn` — the analogue of
  -- `SPMF.support_wellFounded_fix_congr`, which is what made the `genStmt` block go through. That
  -- means relating two `Nat.below` bundles, and it is a piece of work rather than a missing line.
  sorry

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
