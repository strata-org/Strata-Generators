import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.CmdHasTypeAGen
import StrataGenerators.FunctionHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Stmt

/-!
# Soundness and completeness of `genStmt` / `genStmts`

`genStmt` / `genStmts` (in `StmtHasTypeAGen/Core.lean`) generate random Strata
Core statements. This file proves them **sound** and **complete** with respect to
the `StmtHasTypeA` / `StmtsHasTypeA` typing relations of
`Strata.Languages.Core.StatementTypeSpec`.

## Compositional structure

The proofs are *compositional*: they reuse the soundness/completeness of the
component generators rather than reproving anything about expressions, commands,
or functions.

- **Commands** (`cmd` constructor): reuse `genCmd_sound_env` / `genCmd_complete`
  (from `CmdHasTypeAGen.lean`). A generated imperative command wrapped as
  `CmdExt.cmd` is typed by `CmdExtHasType'.cmd`, which delegates to
  `CmdHasType'`.
- **Functions** (`funcDecl` constructor): reuse `genFunction_sound` /
  `genFunction_complete` (from `FunctionHasTypeAGen.lean`).
- **Expressions** (guards, measures, invariants): reuse the `GenLExprSound` /
  `GenLExprComplete` predicates (from `CmdHasTypeAGen.lean`), exactly as the
  command generator does.

## What the annotated spec buys us

`instHasTypeA` ignores the ambient `C` and scope `Γ` when typing *expressions*:
`S.exprTyped C Γ e (S.embed τ)` reduces definitionally to `HasTypeA [] e τ`. So
the only constructor whose well-typedness genuinely depends on `C` is `typeDecl`,
whose premise `C.addKnownTypeWithError … = .ok C'` is discharged by *matching* on
the same operation the generator performs — no reasoning about the underlying
`HashMap` is needed.

## Threading

Both proofs thread two contexts, mirroring the generator:
- `Γ` is threaded via a `VarCtx` and related to the semantic `TContext` through a
  `toTCtx`/`VarCtxCorresponds` bundle (`GenStmtSoundEnv`), just as `genCmds` does.
- `C` is threaded as an honest `LContext CoreLParams`; the generator's output
  `outC` field *is* the output ambient context of the typing relation.
-/

namespace StrataGenerators.Stmt

open StrataGenerators.Function

-- ── Soundness environment ────────────────────────────────────────────────

/-- A soundness environment for the statement generator, bundling the
    context-dependent obligations needed to type every constructor. It packages
    the `genCmd` soundness data (`toTCtx`, `corr`, `exprSound`, `freshDisjoint`,
    `toTCtx_insert`) plus the operator-context simplicity condition
    (`simpleOps`) required by `genFunction_sound`.

    None of the fields mention a specific `C`, so the same environment types
    statements at *every* ambient context reached while threading a sequence. -/
structure GenStmtSoundEnv (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) where
  /-- Produce the semantic `TContext` for any flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The `VarCtx ↔ TContext` correspondence holds for every context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- Expression-level soundness (independent of the variable context). -/
  exprSound : GenLExprSound fctx octx tvars depth
  /-- Fresh names never collide with the free variables of generated expressions. -/
  freshDisjoint : ∀ ctx, FreshNamesDisjointFromExprs fctx octx tvars ctx depth
  /-- `toTCtx` commutes with `VarCtx.insert` (needed for the `init` command case). -/
  toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
    toTCtx (ctx.insert x mty) =
      { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }
  /-- The operator context contains only simple types (needed by `genFunction_sound`). -/
  simpleOps : ∀ p ∈ octx, SimpleType p.2

/-- Reinterpret a `GenStmtSoundEnv` as a `GenCmdSoundEnv` at an arbitrary ambient
    context `C`. Legal because no `GenCmdSoundEnv` field references `C`. -/
def GenStmtSoundEnv.toCmdEnv {fctx octx tvars depth}
    (env : GenStmtSoundEnv fctx octx tvars depth) (C : LContext CoreLParams) :
    GenCmdSoundEnv fctx octx tvars depth C where
  toTCtx := env.toTCtx
  corr := env.corr
  exprSound := env.exprSound
  freshDisjoint := env.freshDisjoint
  toTCtx_insert := env.toTCtx_insert

-- ── Leaf-case soundness lemmas ───────────────────────────────────────────

variable {fctx : FVarCtx} {octx : OpCtx} {tvars : List TyIdentifier}
  {labels : List String} {depth : Nat}

/-- `toPureFuncDecl` always produces a non-recursive declaration. -/
@[simp] theorem toPureFuncDecl_not_isRecursive (f : Function) :
    (Function.toPureFuncDecl f).isRecursive = false := rfl

/-- Soundness of `genCmdStmt`. -/
theorem genCmdStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars depth)
    (C : LContext CoreLParams) (ctx : VarCtx) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCmdStmt (G := SetGen.Set) fctx octx tvars C ctx depth)) :
    StmtHasTypeA P C (env.toTCtx ctx) r.stmt r.outC (env.toTCtx r.outCtx) := by
  simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨rc, hrc, rfl⟩ := hr
  have hcmd := genCmd_sound_env fctx octx tvars ctx depth C (env.toCmdEnv C) rc hrc
  exact StmtHasType'.cmd C (env.toTCtx ctx) (env.toTCtx rc.outCtx) (.cmd rc.cmd)
    (CmdExtHasType'.cmd (env.toTCtx ctx) (env.toTCtx rc.outCtx) rc.cmd hcmd)

/-- Soundness of `genExitStmt`. -/
theorem genExitStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars depth)
    (C : LContext CoreLParams) (ctx : VarCtx) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx)) :
    StmtHasTypeA P C (env.toTCtx ctx) r.stmt r.outC (env.toTCtx r.outCtx) := by
  cases labels with
  | nil =>
    simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _, rfl⟩ := hr
    exact StmtHasType'.exit C (env.toTCtx ctx) l default
  | cons hd tl =>
    simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _, rfl⟩ := hr
    exact StmtHasType'.exit C (env.toTCtx ctx) l default

/-- Soundness of `genFuncDeclStmt`. -/
theorem genFuncDeclStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars depth)
    (C : LContext CoreLParams) (ctx : VarCtx) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genFuncDeclStmt (G := SetGen.Set) fctx octx C ctx depth)) :
    StmtHasTypeA P C (env.toTCtx ctx) r.stmt r.outC (env.toTCtx r.outCtx) := by
  simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff,
             mem_support_pure_iff] at hr
  obtain ⟨decl, ⟨f0, _hf0, rfl⟩, func, hfunc, rfl⟩ := hr
  have hwt : FuncHasTypeA C (env.toTCtx ctx) func :=
    genFunction_sound fctx octx depth env.simpleOps C (env.toTCtx ctx) func hfunc
  exact StmtHasType'.funcDecl C (env.toTCtx ctx) (Function.toPureFuncDecl f0) func default
    (by simp) hwt

/-- Soundness of `genTypeDeclStmt`. The `.ok` branch discharges `typeDecl`; the
    `.error` (name-clash) branch falls back to a well-typed `exit`. -/
theorem genTypeDeclStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars depth)
    (C : LContext CoreLParams) (ctx : VarCtx) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx depth)) :
    StmtHasTypeA P C (env.toTCtx ctx) r.stmt r.outC (env.toTCtx r.outCtx) := by
  simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
  obtain ⟨tc, _htc, hr⟩ := hr
  -- Branch on the same `addKnownTypeWithError` the generator computed.
  split at hr
  · -- `.ok C'`: the split hypothesis is exactly the `typeDecl` premise.
    rename_i C' heq
    simp only [mem_support_pure_iff] at hr
    subst hr
    exact StmtHasType'.typeDecl C C' (env.toTCtx ctx) tc default heq
  · -- `.error`: falls back to `exit`.
    rename_i heq
    simp only [mem_support_pure_iff] at hr
    subst hr
    exact StmtHasType'.exit C (env.toTCtx ctx) "" default

-- ── Guard / measure / invariant soundness helpers ────────────────────────

/-- Any `.det`-guard produced by `genCondOrNondet` carries a boolean expression. -/
theorem genCondOrNondet_det_sound (env : GenStmtSoundEnv fctx octx tvars depth)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (cond : ExprOrNondet Expression)
    (hc : cond ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) fctx octx tvars depth))
    (g : Expression.Expr) (hg : cond = .det g) :
    HasTypeA' [] g .bool := by
  simp only [genCondOrNondet, mem_support_pick_iff, mem_support_pure_iff,
             mem_support_map_iff] at hc
  rcases hc with hnondet | ⟨e, he, rfl⟩
  · exact absurd (hg ▸ hnondet) (by simp)
  · have : e = g := by simpa using hg
    subst this
    exact env.exprSound .bool e he

/-- Any `some`-measure produced by `genOptMeasure` carries an integer expression. -/
theorem genOptMeasure_some_sound (env : GenStmtSoundEnv fctx octx tvars depth)
    (m? : Option Expression.Expr)
    (hm : m? ∈ SetGen.support (genOptMeasure (G := SetGen.Set) fctx octx tvars depth))
    (m : Expression.Expr) (hmeq : m? = some m) :
    HasTypeA' [] m .int := by
  simp only [genOptMeasure, mem_support_pick_iff, mem_support_pure_iff,
             mem_support_map_iff] at hm
  rcases hm with hnone | ⟨e, he, rfl⟩
  · exact absurd (hmeq ▸ hnone) (by simp)
  · have : e = m := by simpa using hmeq
    subst this
    exact env.exprSound .int e he

/-- Every invariant produced by `genInvariants` carries a boolean expression. -/
theorem genInvariants_sound (env : GenStmtSoundEnv fctx octx tvars depth)
    (invs : List (String × Expression.Expr))
    (hinv : invs ∈ SetGen.support (genInvariants (G := SetGen.Set) fctx octx tvars depth))
    (p : String × Expression.Expr) (hp : p ∈ invs) :
    HasTypeA' [] p.2 .bool := by
  simp only [genInvariants, mem_support_listOfMaxLength_iff] at hinv
  have hp_supp := hinv.2 p hp
  simp only [genInvariant, mem_support_bind_iff, mem_support_pure_iff] at hp_supp
  obtain ⟨l, _hl, e, he, rfl⟩ := hp_supp
  exact env.exprSound .bool e he

-- ── Mutual soundness of genStmt / genStmts ───────────────────────────────

mutual

/-- **Soundness of `genStmt`.** Every statement in the generator's support is
    well-typed w.r.t. `StmtHasTypeA` (for any program `P`), with the generator's
    output ambient context `r.outC` and output scope `env.toTCtx r.outCtx` being
    exactly the output contexts of the typing relation.

    Proof by well-founded recursion on the nesting fuel `n`. Leaf constructors
    (`cmd`, `exit`, `funcDecl`, `typeDecl`) are discharged by the per-constructor
    lemmas above; nesting constructors (`block`, `ite`, `loop`) invert the
    corresponding `do`-block and appeal to `genStmts_sound` at the smaller fuel. -/
theorem genStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars depth)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n)) :
    StmtHasTypeA P C (env.toTCtx ctx) r.stmt r.outC (env.toTCtx r.outCtx) := by
  cases n with
  | zero =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact genCmdStmt_sound P env C ctx r hr
    · exact genExitStmt_sound P env C ctx r hr
    · exact genFuncDeclStmt_sound P env C ctx r hr
    · exact genTypeDeclStmt_sound P env C ctx r hr
  | succ fuel =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact genCmdStmt_sound P env C ctx r hr
    · exact genExitStmt_sound P env C ctx r hr
    · exact genFuncDeclStmt_sound P env C ctx r hr
    · exact genTypeDeclStmt_sound P env C ctx r hr
    · -- block
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨label, _hlabel, ⟨⟨len, _⟩⟩, _hlenbd, triple, htriple, rfl⟩ := hr
      have ih := genStmts_sound P env (label :: labels) C ctx fuel len triple htriple
      exact StmtHasType'.block C (env.toTCtx ctx) triple.2.1 (env.toTCtx triple.2.2)
        label triple.1 default ih
    · -- ite_det
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨cond, hcond, ⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmts_sound P env labels C ctx fuel tlen tt htt
      have ihe := genStmts_sound P env labels C ctx fuel elen et het
      exact StmtHasType'.ite_det C (env.toTCtx ctx) tt.2.1 (env.toTCtx tt.2.2)
        et.2.1 (env.toTCtx et.2.2) cond tt.1 et.1 default
        (env.exprSound .bool cond hcond) iht ihe
    · -- ite_nondet
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmts_sound P env labels C ctx fuel tlen tt htt
      have ihe := genStmts_sound P env labels C ctx fuel elen et het
      exact StmtHasType'.ite_nondet C (env.toTCtx ctx) tt.2.1 (env.toTCtx tt.2.2)
        et.2.1 (env.toTCtx et.2.2) tt.1 et.1 default iht ihe
    · -- loop
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨guard, hguard, measure, hmeasure, invs, hinvs, ⟨⟨blen, _⟩⟩, _, body, hbody, rfl⟩ := hr
      have ih := genStmts_sound P env labels C ctx fuel blen body hbody
      refine StmtHasType'.loop C (env.toTCtx ctx) body.2.1 (env.toTCtx body.2.2)
        guard measure invs body.1 default ?_ ?_ ?_ ih
      · intro g hg
        exact genCondOrNondet_det_sound env C (env.toTCtx ctx) guard hguard g hg
      · intro m hm
        exact genOptMeasure_some_sound env measure hmeasure m hm
      · intro p hp
        exact genInvariants_sound env invs hinvs p hp
termination_by (n, 0, 0)

/-- **Soundness of `genStmts`.** Every statement sequence in the generator's
    support satisfies the chained `StmtsHasTypeA` relation between the input
    contexts and the generator's threaded output contexts.

    Proof by well-founded recursion on the remaining length `len` (with the
    nesting fuel `fuel` fixed): the `nil` case is trivial, and the `cons` case
    types the head via `genStmt_sound` and the tail via the induction
    hypothesis. -/
theorem genStmts_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars depth)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (fuel len : Nat)
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel len)) :
    StmtsHasTypeA P C (env.toTCtx ctx) result.1 result.2.1 (env.toTCtx result.2.2) := by
  cases len with
  | zero =>
    simp only [genStmts, mem_support_pure_iff] at hr
    subst hr
    exact StmtsHasType'.nil C (env.toTCtx ctx)
  | succ len =>
    simp only [genStmts, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨rhead, hhead, rtail, htail, rfl⟩ := hr
    have hh := genStmt_sound P env labels C ctx fuel rhead hhead
    have ht := genStmts_sound P env labels rhead.outC rhead.outCtx fuel len rtail htail
    exact StmtsHasType'.cons C rhead.outC rtail.2.1 (env.toTCtx ctx) (env.toTCtx rhead.outCtx)
      (env.toTCtx rtail.2.2) rhead.stmt rtail.1 hh ht
termination_by (fuel, 1, len)

end

-- ── Membership-lifting lemmas (for completeness) ─────────────────────────
-- These lift a result from a sub-generator's support into `genStmt`'s support.
-- Every branch of the `frequency` list has positive weight, so its support is
-- contained in `genStmt`'s support; these lemmas package the reconstruction.

/-- A `genCmdStmt` result is reachable by `genStmt` at *every* fuel `n`. -/
theorem genCmdStmt_mem (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCmdStmt (G := SetGen.Set) fctx octx tvars C ctx depth)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1; omega)]
    exact ⟨4, _, .head _, by omega, hr⟩
  | succ fuel =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+2+2+1+2; omega)]
    exact ⟨4, _, .head _, by omega, hr⟩

/-- A `genExitStmt` result is reachable by `genStmt` at *every* fuel `n`. -/
theorem genExitStmt_mem (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1; omega)]
    exact ⟨1, _, .tail _ (.head _), by omega, hr⟩
  | succ fuel =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+2+2+1+2; omega)]
    exact ⟨1, _, .tail _ (.head _), by omega, hr⟩

/-- A `genFuncDeclStmt` result is reachable by `genStmt` at every fuel `n`. -/
theorem genFuncDeclStmt_mem (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genFuncDeclStmt (G := SetGen.Set) fctx octx C ctx depth)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.head _)), by omega, hr⟩
  | succ fuel =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+2+2+1+2; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.head _)), by omega, hr⟩

/-- A `genTypeDeclStmt` result is reachable by `genStmt` at every fuel `n`. -/
theorem genTypeDeclStmt_mem (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx depth)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩
  | succ fuel =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+2+2+1+2; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩

/-- A `block` statement is reachable by `genStmt` at fuel `fuel+1` when its body
    (of some length `len ≤ depth`) is reachable by `genStmts` at fuel `fuel`. -/
theorem block_mem (C : LContext CoreLParams) (ctx : VarCtx) (fuel : Nat)
    (label : String) (body : List Statement) (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (len : Nat) (hlen : len ≤ depth)
    (hbody : (body, C_body, Γ_body) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars (label :: labels) C ctx depth fuel len))
    (hlabel : label ∈ SetGen.support (String.arbitrary (G := SetGen.Set))) :
    (⟨Stmt.block label body default, C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth (fuel + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+2+2+1+2; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨label, hlabel, ⟨⟨len, Nat.zero_le _, hlen⟩⟩, ⟨Nat.zero_le _, hlen⟩,
    (body, C_body, Γ_body), hbody, rfl⟩

/-- An `ite (.det cond)` statement is reachable by `genStmt` at fuel `fuel+1` when
    the condition is a reachable boolean and both branches are reachable. -/
theorem ite_det_mem (C : LContext CoreLParams) (ctx : VarCtx) (fuel : Nat)
    (cond : Expression.Expr) (thenb elseb : List Statement)
    (Ct : LContext CoreLParams) (Γt : VarCtx) (Ce : LContext CoreLParams) (Γe : VarCtx)
    (tlen elen : Nat) (htlen : tlen ≤ depth) (helen : elen ≤ depth)
    (hcond : cond ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool))
    (hthen : (thenb, Ct, Γt) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel tlen))
    (helse : (elseb, Ce, Γe) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel elen)) :
    (⟨Stmt.ite (.det cond) thenb elseb default, C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth (fuel + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+2+2+1+2; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨cond, hcond, ⟨⟨tlen, Nat.zero_le _, htlen⟩⟩, ⟨Nat.zero_le _, htlen⟩,
    ⟨⟨elen, Nat.zero_le _, helen⟩⟩, ⟨Nat.zero_le _, helen⟩,
    (thenb, Ct, Γt), hthen, (elseb, Ce, Γe), helse, rfl⟩

/-- An `ite .nondet` statement is reachable by `genStmt` at fuel `fuel+1` when both
    branches are reachable. -/
theorem ite_nondet_mem (C : LContext CoreLParams) (ctx : VarCtx) (fuel : Nat)
    (thenb elseb : List Statement)
    (Ct : LContext CoreLParams) (Γt : VarCtx) (Ce : LContext CoreLParams) (Γe : VarCtx)
    (tlen elen : Nat) (htlen : tlen ≤ depth) (helen : elen ≤ depth)
    (hthen : (thenb, Ct, Γt) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel tlen))
    (helse : (elseb, Ce, Γe) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel elen)) :
    (⟨Stmt.ite .nondet thenb elseb default, C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth (fuel + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+2+2+1+2; omega)]
  refine ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨⟨⟨tlen, Nat.zero_le _, htlen⟩⟩, ⟨Nat.zero_le _, htlen⟩,
    ⟨⟨elen, Nat.zero_le _, helen⟩⟩, ⟨Nat.zero_le _, helen⟩,
    (thenb, Ct, Γt), hthen, (elseb, Ce, Γe), helse, rfl⟩

/-- A `loop` statement is reachable by `genStmt` at fuel `fuel+1` when its guard,
    measure, invariants, and body are all reachable. -/
theorem loop_mem (C : LContext CoreLParams) (ctx : VarCtx) (fuel : Nat)
    (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (body : List Statement)
    (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (blen : Nat) (hblen : blen ≤ depth)
    (hguard : guard ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) fctx octx tvars depth))
    (hmeasure : measure ∈ SetGen.support (genOptMeasure (G := SetGen.Set) fctx octx tvars depth))
    (hinvs : invs ∈ SetGen.support (genInvariants (G := SetGen.Set) fctx octx tvars depth))
    (hbody : (body, C_body, Γ_body) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel blen)) :
    (⟨Stmt.loop guard measure invs body default, C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth (fuel + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+2+2+1+2; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨guard, hguard, measure, hmeasure, invs, hinvs,
    ⟨⟨blen, Nat.zero_le _, hblen⟩⟩, ⟨Nat.zero_le _, hblen⟩,
    (body, C_body, Γ_body), hbody, rfl⟩

-- ── genStmts membership: cons / nil ──────────────────────────────────────

/-- The empty statement list is in `genStmts`'s support at length `0`. -/
theorem genStmts_nil_mem (C : LContext CoreLParams) (ctx : VarCtx) (fuel : Nat) :
    ((([] : List Statement)), C, ctx) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel 0) := by
  rw [genStmts]; exact mem_support_pure_iff.mpr rfl

/-- If the head statement `r` is reachable by `genStmt` (at fuel `fuel`) and the
    tail is reachable by `genStmts` from the head's output contexts (at the same
    fuel, length `len`), then the whole `cons` is reachable at length `len+1`. -/
theorem genStmts_cons_mem (C : LContext CoreLParams) (ctx : VarCtx) (fuel len : Nat)
    (r : GenStmtResult) (rest : List Statement) (C'' : LContext CoreLParams) (Γ'' : VarCtx)
    (hhead : r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel))
    (htail : (rest, C'', Γ'') ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels r.outC r.outCtx depth fuel len)) :
    (r.stmt :: rest, C'', Γ'') ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel (len + 1)) := by
  rw [genStmts]
  simp only [mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨r, hhead, (rest, C'', Γ''), htail, rfl⟩

-- ── Fuel monotonicity ────────────────────────────────────────────────────
-- A result reachable at some fuel is reachable at every larger fuel. Proved as a
-- mutual well-founded recursion mirroring the generators (same `(fuel, tag, len)`
-- measure). Leaf branches reuse the `_mem` lemmas above (they already hold at
-- every fuel); nesting branches invert the source membership, bump each body via
-- the `genStmts` IH, then re-package with the `_mem` lemmas.
--
-- NOTE: these are a standalone structural property of the generator. The final
-- completeness proof below threads a *single* fuel through `StmtReachable`
-- (exactly as `genStmts` does), so it does not actually consume monotonicity —
-- but the lemmas are kept as they characterize the generator's fuel behavior and
-- would be needed for any per-statement-fuel restatement of completeness.

mutual

/-- **Fuel monotonicity of `genStmt`.** If a result is reachable at fuel `n`, it
    is reachable at every fuel `n' ≥ n`. Leaf constructors hold at every fuel; the
    nesting constructors bump their bodies via `genStmts_mem_mono`. -/
theorem genStmt_mem_mono (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n n' : Nat)
    (hnn' : n ≤ n') (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n') := by
  cases n with
  | zero =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact genCmdStmt_mem C ctx n' r hr
    · exact genExitStmt_mem C ctx n' r hr
    · exact genFuncDeclStmt_mem C ctx n' r hr
    · exact genTypeDeclStmt_mem C ctx n' r hr
  | succ fuel =>
    -- `n' ≥ fuel + 1 ≥ 1`, so `n' = fuel' + 1` with `fuel ≤ fuel'`.
    obtain ⟨fuel', rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    have hff : fuel ≤ fuel' := by omega
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact genCmdStmt_mem C ctx (fuel' + 1) r hr
    · exact genExitStmt_mem C ctx (fuel' + 1) r hr
    · exact genFuncDeclStmt_mem C ctx (fuel' + 1) r hr
    · exact genTypeDeclStmt_mem C ctx (fuel' + 1) r hr
    · -- block
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨label, hlabel, ⟨⟨len, _⟩⟩, hlenbd, ⟨body, C_body, Γ_body⟩, hbody, rfl⟩ := hr
      exact block_mem C ctx fuel' label body C_body Γ_body len hlenbd.2
        (genStmts_mem_mono (label :: labels) C ctx fuel fuel' len hff (body, C_body, Γ_body) hbody) hlabel
    · -- ite_det
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨cond, hcond, ⟨⟨tlen, _⟩⟩, htlenbd, ⟨⟨elen, _⟩⟩, helenbd,
        ⟨thenb, Ct, Γt⟩, hthen, ⟨elseb, Ce, Γe⟩, helse, rfl⟩ := hr
      exact ite_det_mem C ctx fuel' cond thenb elseb Ct Γt Ce Γe tlen elen htlenbd.2 helenbd.2 hcond
        (genStmts_mem_mono labels C ctx fuel fuel' tlen hff (thenb, Ct, Γt) hthen)
        (genStmts_mem_mono labels C ctx fuel fuel' elen hff (elseb, Ce, Γe) helse)
    · -- ite_nondet
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨⟨⟨tlen, _⟩⟩, htlenbd, ⟨⟨elen, _⟩⟩, helenbd,
        ⟨thenb, Ct, Γt⟩, hthen, ⟨elseb, Ce, Γe⟩, helse, rfl⟩ := hr
      exact ite_nondet_mem C ctx fuel' thenb elseb Ct Γt Ce Γe tlen elen htlenbd.2 helenbd.2
        (genStmts_mem_mono labels C ctx fuel fuel' tlen hff (thenb, Ct, Γt) hthen)
        (genStmts_mem_mono labels C ctx fuel fuel' elen hff (elseb, Ce, Γe) helse)
    · -- loop
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨guard, hguard, measure, hmeasure, invs, hinvs, ⟨⟨blen, _⟩⟩, hblenbd,
        ⟨body, C_body, Γ_body⟩, hbody, rfl⟩ := hr
      exact loop_mem C ctx fuel' guard measure invs body C_body Γ_body blen hblenbd.2
        hguard hmeasure hinvs
        (genStmts_mem_mono labels C ctx fuel fuel' blen hff (body, C_body, Γ_body) hbody)
termination_by (n, 0, 0)

/-- **Fuel monotonicity of `genStmts`.** If a statement list is reachable at fuel
    `fuel`, it is reachable at every fuel `fuel' ≥ fuel` (at the same length). The
    `cons` case bumps the head via `genStmt_mem_mono` and the tail via the IH. -/
theorem genStmts_mem_mono (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (fuel fuel' len : Nat)
    (hff : fuel ≤ fuel')
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel len)) :
    result ∈ SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel' len) := by
  cases len with
  | zero =>
    simp only [genStmts, mem_support_pure_iff] at hr
    subst hr
    exact genStmts_nil_mem C ctx fuel'
  | succ len =>
    rw [genStmts] at hr
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨rhead, hhead, ⟨rest, C'', Γ''⟩, htail, rfl⟩ := hr
    have hhead' := genStmt_mem_mono labels C ctx fuel fuel' hff rhead hhead
    have htail' := genStmts_mem_mono labels rhead.outC rhead.outCtx fuel fuel' len hff
      (rest, C'', Γ'') htail
    exact genStmts_cons_mem C ctx fuel' len rhead rest C'' Γ'' hhead' htail'
termination_by (fuel, 1, len)

end

-- ── Completeness helper lemmas (Step B helpers) ──────────────────────────
-- Straightforward `pick`/`map`/`listOfMaxLength` support-inversion lemmas, one
-- per guard/measure/invariant/type-constructor sub-generator, mirroring
-- `genOptExpr_complete` in `FunctionHasTypeAGen.lean`.

/-- Completeness of `genCondOrNondet`. `.nondet` is always reachable; `.det g` is
    reachable when `g` is reachable by `genLExpr` at type `bool`. -/
theorem genCondOrNondet_complete (cond : ExprOrNondet Expression)
    (hcond : ∀ g, cond = .det g →
      g ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    cond ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genCondOrNondet, mem_support_pick_iff, mem_support_pure_iff, mem_support_map_iff]
  cases cond with
  | nondet => exact Or.inl rfl
  | det g => exact Or.inr ⟨g, hcond g rfl, rfl⟩

/-- Completeness of `genOptMeasure`. `none` is always reachable; `some m` is
    reachable when `m` is reachable by `genLExpr` at type `int`. -/
theorem genOptMeasure_complete (measure : Option Expression.Expr)
    (hmeasure : ∀ m, measure = some m →
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .int)) :
    measure ∈ SetGen.support (genOptMeasure (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genOptMeasure, mem_support_pick_iff, mem_support_pure_iff, mem_support_map_iff]
  cases measure with
  | none => exact Or.inl rfl
  | some m => exact Or.inr ⟨m, hmeasure m rfl, rfl⟩

/-- Completeness of `genInvariant`. A `(label, e)` pair is reachable when the
    label is a reachable alphanumeric string and `e` is a reachable boolean. -/
theorem genInvariant_complete (p : String × Expression.Expr)
    (hlabel : p.1 ∈ SetGen.support (String.arbitrary (G := SetGen.Set)))
    (hexpr : p.2 ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    p ∈ SetGen.support (genInvariant (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genInvariant, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨p.1, hlabel, p.2, hexpr, rfl⟩

/-- Completeness of `genInvariants`. A list of invariants is reachable when it is
    no longer than `depth` and each element is reachable by `genInvariant`. -/
theorem genInvariants_complete (invs : List (String × Expression.Expr))
    (hlen : invs.length ≤ depth)
    (hinvs : ∀ p ∈ invs, p.1 ∈ SetGen.support (String.arbitrary (G := SetGen.Set)) ∧
      p.2 ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    invs ∈ SetGen.support (genInvariants (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genInvariants, mem_support_listOfMaxLength_iff]
  refine ⟨hlen, fun p hp => ?_⟩
  exact genInvariant_complete p (hinvs p hp).1 (hinvs p hp).2

/-- Completeness of `genTypeConstructor`. A type constructor is reachable when its
    name and each parameter name are reachable alphanumeric strings, its parameter
    list is no longer than `depth`, and its `bound` is at the default `.Infinite`. -/
theorem genTypeConstructor_complete (tc : TypeConstructor)
    (hbound : tc.bound = .Infinite)
    (hname : tc.name ∈ SetGen.support (String.arbitrary (G := SetGen.Set)))
    (hlen : tc.params.length ≤ depth)
    (hparams : ∀ s ∈ tc.params, s ∈ SetGen.support (String.arbitrary (G := SetGen.Set))) :
    tc ∈ SetGen.support (genTypeConstructor (G := SetGen.Set) depth) := by
  simp only [genTypeConstructor, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_listOfMaxLength_iff]
  refine ⟨tc.name, hname, tc.params, ⟨hlen, hparams⟩, ?_⟩
  obtain ⟨bound, name, params⟩ := tc
  simp only at hbound
  subst hbound
  rfl

-- ── Reachability relation (Step B) ───────────────────────────────────────
-- `StmtReachable`/`StmtsReachable` are a fuel-indexed, `VarCtx`-threaded mutual
-- inductive mirroring `genStmt`/`genStmts` *exactly*. A statement is "reachable"
-- when it is in the generator's normal form (metadata `default`) and each of its
-- components is reachable by the corresponding sub-generator:
--
--   * leaf constructors carry the sub-result's membership in the leaf
--     sub-generator's support (`genCmdStmt`/`genExitStmt`/`genFuncDeclStmt`/
--     `genTypeDeclStmt`), which — via the component completeness lemmas
--     (`genCmd_complete`, `genFunction_complete`, …) and soundness — is exactly
--     "a well-typed command/function/type-constructor in normal form";
--   * nesting constructors (`block`/`ite`/`loop`) carry the reachability of their
--     guard/measure/invariants (via `genLExpr` support) and their bodies (via
--     `StmtsReachable` at the smaller fuel), plus the `len ≤ depth` length bounds.
--
-- The relation threads a *single* fuel through a whole list (as `genStmts` does),
-- so the sequence case needs no fuel-monotonicity or output-context-determinism
-- reasoning. `genStmt_complete`/`genStmts_complete` below show every reachable
-- statement is in the generator's support; combined with `genStmt_sound`
-- (support ⇒ `StmtHasTypeA`), this pins down the generator's support precisely.

mutual

/-- Fuel-indexed reachability for a single statement. `StmtReachable labels C ctx n s C' ctx'`
    means the result `⟨s, C', ctx'⟩` is produced by `genStmt … labels C ctx depth n`.
    `labels` (the enclosing block labels) is an *index* because a `block` extends it
    with its own label when descending into its body. -/
inductive StmtReachable (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) :
    List String → LContext CoreLParams → VarCtx → Nat → Statement →
    LContext CoreLParams → VarCtx → Prop where
  /-- A `cmd` statement: any result of the `genCmdStmt` sub-generator, at any fuel. -/
  | cmd : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genCmdStmt (G := SetGen.Set) fctx octx tvars C ctx depth) →
      StmtReachable fctx octx tvars depth labels C ctx n res.stmt res.outC res.outCtx
  /-- An `exit` statement: any result of `genExitStmt` at the enclosing `labels`. -/
  | exit : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx) →
      StmtReachable fctx octx tvars depth labels C ctx n res.stmt res.outC res.outCtx
  /-- A `funcDecl` statement: any result of `genFuncDeclStmt`, at any fuel. -/
  | funcDecl : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genFuncDeclStmt (G := SetGen.Set) fctx octx C ctx depth) →
      StmtReachable fctx octx tvars depth labels C ctx n res.stmt res.outC res.outCtx
  /-- A `typeDecl` statement (or its `exit` fallback): any result of `genTypeDeclStmt`. -/
  | typeDecl : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx depth) →
      StmtReachable fctx octx tvars depth labels C ctx n res.stmt res.outC res.outCtx
  /-- A `block`, at fuel `fuel+1`, whose body is reachable at fuel `fuel`. The body
      is generated under `label :: labels`, so a nested `exit` may target this block. -/
  | block : ∀ labels C ctx fuel label body C_body Γ_body len,
      len ≤ depth →
      label ∈ SetGen.support (String.arbitrary (G := SetGen.Set)) →
      StmtsReachable fctx octx tvars depth (label :: labels) C ctx fuel len body C_body Γ_body →
      StmtReachable fctx octx tvars depth labels C ctx (fuel + 1)
        (Stmt.block label body default) C ctx
  /-- A deterministic `ite`, at fuel `fuel+1`, with reachable condition and branches. -/
  | ite_det : ∀ labels C ctx fuel cond thenb elseb Ct Γt Ce Γe tlen elen,
      tlen ≤ depth → elen ≤ depth →
      cond ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool) →
      StmtsReachable fctx octx tvars depth labels C ctx fuel tlen thenb Ct Γt →
      StmtsReachable fctx octx tvars depth labels C ctx fuel elen elseb Ce Γe →
      StmtReachable fctx octx tvars depth labels C ctx (fuel + 1)
        (Stmt.ite (.det cond) thenb elseb default) C ctx
  /-- A non-deterministic `ite`, at fuel `fuel+1`, with reachable branches. -/
  | ite_nondet : ∀ labels C ctx fuel thenb elseb Ct Γt Ce Γe tlen elen,
      tlen ≤ depth → elen ≤ depth →
      StmtsReachable fctx octx tvars depth labels C ctx fuel tlen thenb Ct Γt →
      StmtsReachable fctx octx tvars depth labels C ctx fuel elen elseb Ce Γe →
      StmtReachable fctx octx tvars depth labels C ctx (fuel + 1)
        (Stmt.ite .nondet thenb elseb default) C ctx
  /-- A `loop`, at fuel `fuel+1`, with reachable guard/measure/invariants and body. -/
  | loop : ∀ labels C ctx fuel guard measure invs body C_body Γ_body blen,
      blen ≤ depth →
      guard ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) fctx octx tvars depth) →
      measure ∈ SetGen.support (genOptMeasure (G := SetGen.Set) fctx octx tvars depth) →
      invs ∈ SetGen.support (genInvariants (G := SetGen.Set) fctx octx tvars depth) →
      StmtsReachable fctx octx tvars depth labels C ctx fuel blen body C_body Γ_body →
      StmtReachable fctx octx tvars depth labels C ctx (fuel + 1)
        (Stmt.loop guard measure invs body default) C ctx

/-- Fuel-indexed reachability for a statement list. `StmtsReachable labels C ctx fuel len ss C' ctx'`
    means `(ss, C', ctx')` is produced by `genStmts … labels C ctx depth fuel len`. -/
inductive StmtsReachable (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) :
    List String → LContext CoreLParams → VarCtx → Nat → Nat → List Statement →
    LContext CoreLParams → VarCtx → Prop where
  /-- The empty list, at length `0`. -/
  | nil : ∀ labels C ctx fuel,
      StmtsReachable fctx octx tvars depth labels C ctx fuel 0 [] C ctx
  /-- A `cons`, at length `len+1`: reachable head threaded into a reachable tail. -/
  | cons : ∀ labels C ctx fuel len s C_h Γ_h rest C'' Γ'',
      StmtReachable fctx octx tvars depth labels C ctx fuel s C_h Γ_h →
      StmtsReachable fctx octx tvars depth labels C_h Γ_h fuel len rest C'' Γ'' →
      StmtsReachable fctx octx tvars depth labels C ctx fuel (len + 1) (s :: rest) C'' Γ''

end

-- ── Completeness: every reachable statement is in the generator's support ──

mutual

/-- **Completeness of `genStmt`.** Every statement reachable per `StmtReachable`
    (in generator normal form with reachable components) is in `genStmt`'s support,
    with the *exact* statement, output ambient context, and output scope. Proof by
    induction on the reachability derivation, dispatching each constructor to the
    membership-lifting lemma of the corresponding generator branch. -/
theorem genStmt_complete (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (s : Statement) (C' : LContext CoreLParams) (ctx' : VarCtx)
    (h : StmtReachable fctx octx tvars depth labels C ctx n s C' ctx') :
    (⟨s, C', ctx'⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n) := by
  cases h with
  | cmd labels C ctx n res hres => exact genCmdStmt_mem C ctx n res hres
  | exit labels C ctx n res hres => exact genExitStmt_mem C ctx n res hres
  | funcDecl labels C ctx n res hres => exact genFuncDeclStmt_mem C ctx n res hres
  | typeDecl labels C ctx n res hres => exact genTypeDeclStmt_mem C ctx n res hres
  | block labels C ctx fuel label body C_body Γ_body len hlen hlabel hbody =>
    exact block_mem C ctx fuel label body C_body Γ_body len hlen
      (genStmts_complete (label :: labels) C ctx fuel len body C_body Γ_body hbody) hlabel
  | ite_det labels C ctx fuel cond thenb elseb Ct Γt Ce Γe tlen elen htlen helen hcond hthen helse =>
    exact ite_det_mem C ctx fuel cond thenb elseb Ct Γt Ce Γe tlen elen htlen helen hcond
      (genStmts_complete labels C ctx fuel tlen thenb Ct Γt hthen)
      (genStmts_complete labels C ctx fuel elen elseb Ce Γe helse)
  | ite_nondet labels C ctx fuel thenb elseb Ct Γt Ce Γe tlen elen htlen helen hthen helse =>
    exact ite_nondet_mem C ctx fuel thenb elseb Ct Γt Ce Γe tlen elen htlen helen
      (genStmts_complete labels C ctx fuel tlen thenb Ct Γt hthen)
      (genStmts_complete labels C ctx fuel elen elseb Ce Γe helse)
  | loop labels C ctx fuel guard measure invs body C_body Γ_body blen hblen hguard hmeasure hinvs hbody =>
    exact loop_mem C ctx fuel guard measure invs body C_body Γ_body blen hblen
      hguard hmeasure hinvs
      (genStmts_complete labels C ctx fuel blen body C_body Γ_body hbody)

/-- **Completeness of `genStmts`.** Every statement list reachable per
    `StmtsReachable` is in `genStmts`'s support, with the exact list and output
    contexts. The `cons` case threads the head via `genStmt_complete` and the tail
    via the induction hypothesis, both at the same fuel — no monotonicity needed. -/
theorem genStmts_complete (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (fuel len : Nat)
    (ss : List Statement) (C' : LContext CoreLParams) (ctx' : VarCtx)
    (h : StmtsReachable fctx octx tvars depth labels C ctx fuel len ss C' ctx') :
    ((ss, C', ctx') : List Statement × LContext CoreLParams × VarCtx) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars labels C ctx depth fuel len) := by
  cases h with
  | nil => exact genStmts_nil_mem C ctx fuel
  | cons labels _ _ _ len s C_h Γ_h rest _ _ hhead htail =>
    have hh := genStmt_complete labels C ctx fuel s C_h Γ_h hhead
    have ht := genStmts_complete labels C_h Γ_h fuel len rest C' ctx' htail
    exact genStmts_cons_mem C ctx fuel len ⟨s, C_h, Γ_h⟩ rest C' ctx' hh ht

end

-- ── Capstone: reachable ⇒ in support ∧ well-typed ────────────────────────

/-- **Completeness–soundness capstone for `genStmt`.** Every statement reachable
    per `StmtReachable` is (a) in `genStmt`'s support at the exact statement/output
    contexts (completeness), and (b) well-typed w.r.t. `StmtHasTypeA` for any
    program `P` (soundness). Together these witness that `StmtReachable` characterizes
    exactly the generator's *well-typed* support, confirming the reachability
    relation is not vacuous. -/
theorem genStmt_complete_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars depth)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (s : Statement) (C' : LContext CoreLParams) (ctx' : VarCtx)
    (h : StmtReachable fctx octx tvars depth labels C ctx n s C' ctx') :
    (⟨s, C', ctx'⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars labels C ctx depth n) ∧
    StmtHasTypeA P C (env.toTCtx ctx) s C' (env.toTCtx ctx') := by
  have hmem := genStmt_complete labels C ctx n s C' ctx' h
  exact ⟨hmem, genStmt_sound P env labels C ctx n ⟨s, C', ctx'⟩ hmem⟩

end StrataGenerators.Stmt
