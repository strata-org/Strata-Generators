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

## The single `size` budget

`genStmt`/`genStmts` take a single `size` (the QuickCheck-style `sized` knob):
there is no separate nesting `fuel`. `size` bounds nesting depth *and* — being
passed on to the leaf/expression sub-generators — the size of expressions and the
length of generated statement sequences, exactly as the single `Nat` argument of
`genLExprBase` does for expressions. As a statement nests, `size` shrinks, so the
leaf/expression sub-generators are invoked at *varying* depths.

Consequently the soundness environment (`GenStmtSoundEnv`) is **depth-generic**:
its expression-level obligations are quantified over *all* depths `d`, since a
generated command/expression may sit at any depth reached while nesting.

## What the annotated spec buys us

`instHasTypeA` ignores the ambient `C` and scope `Γ` when typing *expressions*:
`S.exprTyped C Γ e (S.embed τ)` reduces definitionally to `HasTypeA [] e τ`. So
the only constructor whose well-typedness genuinely depends on `C` is `typeDecl`,
whose premise `C.addKnownTypeWithError … = .ok C'` is discharged by *matching* on
the same operation the generator performs — no reasoning about the underlying
`HashMap` is needed.

## Threading

Both proofs thread three contexts, mirroring the generator:
- `Γ` is threaded via a `VarCtx` and related to the semantic `TContext` through a
  `toTCtx`/`VarCtxCorresponds` bundle (`GenStmtSoundEnv`), just as `genCmds` does.
- `C` is threaded as an honest `LContext CoreLParams`; the generator's output
  `outC` field *is* the output ambient context of the typing relation.
- `L` (the enclosing-block labels, `labels`) is threaded as a `List String`. It is
  the fifth argument of the 6-place `StmtHasTypeA` relation. Its typing role is in
  two constructors: `exit label` requires `label ∈ L`, discharged by the
  `elements` support of `genExitStmt`; `block label` requires `label ∉ L`,
  discharged by the freshness of `genFreshLabel` (see `genFreshLabel_fresh`).
-/

namespace StrataGenerators.Stmt

open StrataGenerators.Function

-- ── Soundness environment ────────────────────────────────────────────────

/-- A soundness environment for the statement generator, bundling the
    context-dependent obligations needed to type every constructor. It packages
    the `genCmd` soundness data (`toTCtx`, `corr`, `exprSound`, `freshDisjoint`,
    `toTCtx_insert`).

    The expression-level obligations (`exprSound`, `freshDisjoint`) are quantified
    over **all** depths `d`: because the single `size` budget shrinks as statements
    nest, a generated command/expression may be produced at any depth, so the
    environment must justify soundness uniformly across depths.

    None of the fields mention a specific `C`, so the same environment types
    statements at *every* ambient context reached while threading a sequence. -/
structure GenStmtSoundEnv (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) where
  /-- Produce the semantic `TContext` for any flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The `VarCtx ↔ TContext` correspondence holds for every context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- Expression-level soundness at *every* depth (independent of the variable
      context). -/
  exprSound : ∀ d, GenLExprSound fctx octx tvars d
  /-- Fresh names never collide with the free variables of generated expressions,
      at every depth. -/
  freshDisjoint : ∀ d ctx, FreshNamesDisjointFromExprs fctx octx tvars ctx d
  /-- `toTCtx` commutes with `VarCtx.insert` (needed for the `init` command case). -/
  toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
    toTCtx (ctx.insert x mty) =
      { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }

/-- Reinterpret a `GenStmtSoundEnv` as a `GenCmdSoundEnv` at an arbitrary ambient
    context `C` and depth `d`. Legal because no `GenCmdSoundEnv` field references
    `C`, and the environment supplies its expression obligations at every depth. -/
def GenStmtSoundEnv.toCmdEnv {fctx octx tvars}
    (env : GenStmtSoundEnv fctx octx tvars) (C : LContext CoreLParams) (d : Nat) :
    GenCmdSoundEnv fctx octx tvars d C where
  toTCtx := env.toTCtx
  corr := env.corr
  exprSound := env.exprSound d
  freshDisjoint := env.freshDisjoint d
  toTCtx_insert := env.toTCtx_insert

-- ── Leaf-case soundness lemmas ───────────────────────────────────────────

variable {fctx : FVarCtx} {octx : OpCtx} {tvars : List TyIdentifier}
  {immutableVars : List (Identifier Unit)} {labels : List String}

/-- `toPureFuncDecl` always produces a non-recursive declaration. -/
@[simp] theorem toPureFuncDecl_not_isRecursive (f : Function) :
    (Function.toPureFuncDecl f).isRecursive = false := rfl

/-- Soundness of `genCmdStmt` (at any depth `d`). -/
theorem genCmdStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCmdStmt (G := SetGen.Set) fctx octx tvars immutableVars C ctx d)) :
    StmtHasTypeA P C (env.toTCtx ctx) labels r.stmt r.outC (env.toTCtx r.outCtx) := by
  simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨rc, hrc, rfl⟩ := hr
  have hcmd := genCmd_sound_env fctx octx tvars immutableVars ctx d C (env.toCmdEnv C d) hFun rc hrc
  exact StmtHasType'.cmd C (env.toTCtx ctx) (env.toTCtx rc.outCtx) labels (.cmd rc.cmd)
    (CmdExtHasType'.cmd (env.toTCtx ctx) (env.toTCtx rc.outCtx) rc.cmd hcmd)

/-- Soundness of `genExitStmt`. With enclosing labels the target is drawn from
    them (`label ∈ L`, discharging the `exit` premise); with no enclosing block
    (`labels = []`) the generator is empty (support `∅`), so there is nothing to
    prove. -/
theorem genExitStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars)
    (C : LContext CoreLParams) (ctx : VarCtx) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx)) :
    StmtHasTypeA P C (env.toTCtx ctx) labels r.stmt r.outC (env.toTCtx r.outCtx) := by
  cases labels with
  | nil =>
    -- `genExitStmt [] … = default`, whose support is `∅`.
    simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons hd tl =>
    simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨l, hl, rfl⟩ := hr
    exact StmtHasType'.exit C (env.toTCtx ctx) (hd :: tl) l default hl

/-- Soundness of `genFuncDeclStmt` (at any depth `d`). -/
theorem genFuncDeclStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genFuncDeclStmt (G := SetGen.Set) fctx octx C ctx d)) :
    StmtHasTypeA P C (env.toTCtx ctx) labels r.stmt r.outC (env.toTCtx r.outCtx) := by
  simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff,
             mem_support_pure_iff] at hr
  obtain ⟨decl, ⟨f0, _hf0, rfl⟩, func, hfunc, rfl⟩ := hr
  have hwt : FuncHasTypeA C (env.toTCtx ctx) func :=
    genFunction_sound fctx octx d C (env.toTCtx ctx) func hfunc
  exact StmtHasType'.funcDecl C (env.toTCtx ctx) labels (Function.toPureFuncDecl f0) func default
    (by simp) hwt

/-- Soundness of `genTypeDeclStmt` (at any depth `d`). The `.ok` branch discharges
    `typeDecl`; the `.error` (name-clash) branch is the empty generator (support
    `∅`), so there is nothing to prove. -/
theorem genTypeDeclStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx d)) :
    StmtHasTypeA P C (env.toTCtx ctx) labels r.stmt r.outC (env.toTCtx r.outCtx) := by
  simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
  obtain ⟨tc, _htc, hr⟩ := hr
  -- Branch on the same `addKnownTypeWithError` the generator computed.
  split at hr
  · -- `.ok C'`: the split hypothesis is exactly the `typeDecl` premise.
    rename_i C' heq
    simp only [mem_support_pure_iff] at hr
    subst hr
    exact StmtHasType'.typeDecl C C' (env.toTCtx ctx) labels tc default heq
  · -- `.error`: the empty generator `default`, whose support is `∅`.
    rename_i heq
    simp only [SetGen.support, SetGen.bot_mem_iff] at hr

-- ── Fresh-label freshness (for the `block` premise) ──────────────────────

/-- The foldl-max accumulator over label lengths is non-decreasing. -/
private theorem foldl_maxlen_ge_init (xs : List String) (init : Nat) :
    init ≤ xs.foldl (fun acc l => max acc l.length) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- The foldl-max result bounds the length of every member. -/
private theorem foldl_maxlen_ge_of_mem (xs : List String) (l : String)
    (h : l ∈ xs) (init : Nat) :
    l.length ≤ xs.foldl (fun acc l => max acc l.length) init := by
  induction xs generalizing init with
  | nil => exact absurd h (by exact List.not_mem_nil)
  | cons hd tl ih =>
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) (foldl_maxlen_ge_init tl _)
    | tail _ hmem => exact ih hmem _

/-- `fallbackFreshLabel labels` is absent from `labels`: it is strictly longer
    than every label in the list. -/
theorem fallbackFreshLabel_not_mem (labels : List String) :
    fallbackFreshLabel labels ∉ labels := by
  intro hmem
  have hlen : (fallbackFreshLabel labels).length =
      (labels.foldl (fun acc l => max acc l.length) 0) + 1 := by
    simp [fallbackFreshLabel, String.length_ofList, List.length_replicate]
  have hle := foldl_maxlen_ge_of_mem labels (fallbackFreshLabel labels) hmem 0
  omega

/-- Every label in the support of `genFreshLabel labels` is absent from `labels`,
    discharging the `label ∉ L` premise of the `block` typing rule. -/
theorem genFreshLabel_not_mem (labels : List String) :
    ∀ l, l ∈ SetGen.support (genFreshLabel (G := SetGen.Set) labels) → l ∉ labels := by
  intro l hmem
  simp only [genFreshLabel, mem_support_bind_iff] at hmem
  obtain ⟨s, _, hl⟩ := hmem
  simp only [mem_support_ite_iff, mem_support_pure_iff] at hl
  rcases hl with ⟨_, rfl⟩ | ⟨hns, rfl⟩
  · exact fallbackFreshLabel_not_mem labels
  · exact hns

-- ── Procedure-call soundness ──────────────────────────────────────────────

/-- Every `genCallStmt` result leaves the variable scope unchanged (`outCtx =
    ctx`): the emitted call is a lexically-scoped block, so functionality of the
    context is preserved. The empty-`procs`/guard-false branches are the empty
    generator, so there is nothing to prove. -/
theorem genCallStmt_outCtx {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCallStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx d)) :
    Map.Functional r.outCtx := by
  cases procs with
  | nil => simp only [genCallStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff, mem_support_elements_iff] at hr
    obtain ⟨s, hs, hr⟩ := hr
    split at hr
    · simp only [mem_support_bind_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      -- Both emitted shapes (inline call / init-chain block) leave `outCtx = ctx`.
      split at hr
      · simp only [mem_support_pure_iff] at hr
        obtain rfl := hr; exact hFun
      · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr; exact hFun
    · simp only [SetGen.support, SetGen.bot_mem_iff] at hr

/-! ### Reconciling the recipe with the call-soundness lemmas

`genCallStmt` inspects the in-out block `s.M` and the out-only block `s.O`
*separately* (that is the point of the recipe): it guards only on `s.M`, chooses
out-argument targets `T = outTargets … s.O` for itself, and concatenates two
`filter`s to get its init-list. The lemmas in `GenCallStmtSound.lean`, in
contrast, speak about the single
appended list `M ++ T` of variables the call writes to. The lemmas below are the
whole reconciliation: three facts about `outTargets` and two `append` fusions. -/

/-- `outTarget` never touches the *type* component: whichever variable it chooses,
    that variable carries the type the callee declares. -/
theorem outTarget_snd (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (base : Nat)
    (q : Identifier Unit × LMonoTy) (i : Nat) :
    (outTarget immutableVars ctx base q i).2 = q.2 := by
  simp only [outTarget]; split <;> rfl

/-- **The out targets are positionally type-aligned with the callee's out block.**
    This is the `hTVals` premise every call-soundness lemma takes, and the only
    relation
    between the chosen targets `T` and the callee's declared out block `O` that the
    Core spec requires (out-argument *names* are the caller's to pick). -/
theorem outTargets_values (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (O : @LMonoTySignature Unit) : (outTargets immutableVars ctx O).values = O.values := by
  simp only [outTargets, ListMap.values_eq_map_snd, List.map_map]
  rw [show (Prod.snd ∘ fun p : (Identifier Unit × LMonoTy) × Nat =>
        outTarget immutableVars ctx (maxNameLen ctx) p.1 p.2) = Prod.snd ∘ Prod.fst
      from by funext p; exact outTarget_snd ..,
    ← List.map_map, List.zipIdx_map_fst]
  rfl

/-- One receiving variable per out-only parameter. -/
theorem outTargets_length (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (O : @LMonoTySignature Unit) :
    (outTargets immutableVars ctx O).length = O.length := by
  simp only [outTargets, List.length_map, List.length_zipIdx]; rfl

/-- **Every chosen out target is usable, unconditionally.** A target is either a
    `reusable` ambient variable (first disjunct) or a brand-new
    `indexedFreshName (maxNameLen ctx) i`, which is fresh for `ctx` and hence
    `needsInit` (second disjunct). This is why the generator's guard need only
    mention the in-out block: an out-only parameter can never make a callee
    uncallable. -/
theorem outTargets_all_usableName (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (O : @LMonoTySignature Unit) :
    (outTargets immutableVars ctx O).all (usableName immutableVars ctx) = true := by
  rw [List.all_eq_true]
  intro p hp
  simp only [outTargets, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  simp only [outTarget]
  split
  · rename_i h; simp [usableName, h]
  · simp [usableName, needsInit, indexedFreshName_isFresh]

/-- The recipe's in-out usability check, extended over `M ++ T` — the out targets
    contribute nothing to prove (`outTargets_all_usableName`). -/
theorem all_usableName_append (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (M O : @LMonoTySignature Unit)
    (hM : M.all (usableName immutableVars ctx) = true) :
    (List.append M (outTargets immutableVars ctx O)).all (usableName immutableVars ctx) = true := by
  rw [List.all_eq_true]
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact List.all_eq_true.mp hM q h
  · exact List.all_eq_true.mp (outTargets_all_usableName immutableVars ctx O) q h

/-- The recipe's per-block init-lists (in-out args first, then out targets), fused
    into one filter over `M ++ T`. -/
theorem filter_needsInit_append (ctx : VarCtx) (M T : @LMonoTySignature Unit) :
    (M.filter (needsInit ctx) ++ T.filter (needsInit ctx))
      = (List.append M T).filter (needsInit ctx) :=
  (List.filter_append ..).symm

/-- The generator's syntactic freshness filter (over the flat `VarCtx`) agrees with
    the semantic `missingIn` filter (over the `TContext`). Both directions
    come from `VarCtxCorresponds`: fresh names are absent from `Γ`, and a bound
    `ctx` entry maps to a `some` in `Γ`. -/
theorem filter_needsInit_eq_missingIn (env : GenStmtSoundEnv fctx octx tvars)
    (ctx : VarCtx) (names : List (Identifier Unit × LMonoTy)) :
    names.filter (needsInit ctx)
      = StrataGenerators.Stmt.missingIn (env.toTCtx ctx) names := by
  simp only [StrataGenerators.Stmt.missingIn]
  apply List.filter_congr
  intro q _
  simp only [needsInit]
  by_cases hfr : VarCtx.isFresh ctx q.1 = true
  · rw [(env.corr ctx).2 q.1 hfr]; simp [hfr]
  · -- not fresh ⇒ `ctx.find? = some τ` ⇒ `Γ.types.find? = some (∀[].τ)` ⇒ not `isNone`
    have hne : ctx.find? q.1 ≠ none := by
      intro h; exact hfr (by simp [VarCtx.isFresh, h])
    obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.mp hne
    rw [(env.corr ctx).1 q.1 τ hτ]
    simp [hfr]

/-- Soundness of `genCallStmt` (at any depth `d`). Every emitted procedure call is
    well-typed: the callee's signature is read off `hProcs`, the drawn by-value
    inputs are typed via `env.exprSound`, and the statement is assembled by
    `call_inline_sound` (nothing missing — a bare inline call) or `call_mixed_sound`
    (something missing — an init-chain block). Either way the output scope is the
    input `ctx`. The empty-`procs` and guard-false branches are the empty generator,
    so there is nothing to prove there. -/
theorem genCallStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars)
    (procs : ProcSigCtx) (hProcs : ProcSigCorresponds procs P)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCallStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx d)) :
    StmtHasTypeA P C (env.toTCtx ctx) labels r.stmt r.outC (env.toTCtx r.outCtx) := by
  cases procs with
  | nil => simp only [genCallStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff] at hr
    obtain ⟨s, hs, hr⟩ := hr
    rw [mem_support_elements_iff] at hs
    -- Split on the usability/Nodup guard.
    split at hr
    · rename_i hcond
      obtain ⟨hMusable, hNodup⟩ := hcond
      -- Name the out targets the generator picked for itself, and record the two
      -- facts the call-soundness lemmas need: usability (free — a new name is
      -- always fresh) and positional type alignment with `s.O`.
      obtain ⟨T, hT⟩ : ∃ T, outTargets immutableVars ctx s.O = T := ⟨_, rfl⟩
      have hallusable : (List.append s.M T).all (usableName immutableVars ctx) = true := by
        rw [← hT]; exact all_usableName_append immutableVars ctx s.M s.O hMusable
      have hTVals : T.values = s.O.values := by
        rw [← hT]; exact outTargets_values immutableVars ctx s.O
      rw [hT] at hNodup hr
      simp only [mem_support_bind_iff] at hr
      obtain ⟨exprs, hexprs, hr⟩ := hr
      -- Callee signature facts from the correspondence.
      obtain ⟨proc, hfind, _htyargs, hInputs, hOutputs, hIdisjOut⟩ := hProcs s hs
      -- The drawn inputs are pointwise reachable.
      have hF₂ := (mem_support_mapM_iff
        (fun σ => genLExpr (G := SetGen.Set) fctx octx [] tvars [] d σ) s.I.values exprs).mp hexprs
      have hExLen : exprs.length = s.I.length := by
        rw [hF₂.length_eq, lm_values_length]
      have hExTy : ∀ i (hi : i < exprs.length) (hj : i < s.I.values.length),
          LExpr.HasTypeA [] (exprs[i]'hi) (s.I.values[i]'hj) := by
        intro i hi hj
        obtain ⟨σ, hσ, hmem⟩ := hF₂.getElem?_some (i := i) (List.getElem?_eq_getElem hi)
        rw [List.getElem?_eq_getElem hj] at hσ
        have hσeq : σ = s.I.values[i]'hj := (Option.some.inj hσ).symm
        subst hσeq
        exact env.exprSound d (s.I.values[i]'hj) (exprs[i]'hi) hmem
      -- Each required name is *either* already bound at its declared type (reuse)
      -- *or* absent (init) — this is exactly the generator's `usable` guard,
      -- transported across `VarCtxCorresponds`.
      have hReuse : ∀ p ∈ (s.M ++ T).toList,
          (env.toTCtx ctx).types.find? p.1 = some (.forAll [] p.2) ∨
          (env.toTCtx ctx).types.find? p.1 = none := by
        intro q hq
        have hq' := List.all_eq_true.mp hallusable q hq
        -- `usableName q = reusable q || needsInit q`; both disjuncts inspect `ctx.find? q.1`.
        rcases hfind_q : ctx.find? q.1 with _ | τ
        · -- absent ⇒ absent in Γ too
          exact Or.inr ((env.corr ctx).2 q.1 (by simp [VarCtx.isFresh, hfind_q]))
        · -- bound ⇒ `needsInit` is false, so `reusable` holds: bound at the declared type
          have hnotinit : needsInit ctx q = false := by
            simp [needsInit, VarCtx.isFresh, hfind_q]
          have hreuse : reusable immutableVars ctx q = true := by
            simp only [usableName, hnotinit, Bool.or_false] at hq'; exact hq'
          have hτ : τ = q.2 := by
            simp only [reusable, hfind_q, Bool.and_eq_true, beq_iff_eq, Option.some.injEq]
              at hreuse
            exact hreuse.1
          have hb := (env.corr ctx).1 q.1 τ hfind_q
          rw [hτ] at hb
          exact Or.inl hb
      -- Split on whether anything needed initializing.
      split at hr
      · -- Nothing missing: every required name is reused ⇒ bare inline call.
        rename_i hempty
        -- Fuse the recipe's in-out-then-out-target init lists into one filter.
        rw [filter_needsInit_append] at hempty
        simp only [mem_support_pure_iff] at hr
        obtain rfl := hr
        -- `missing = []` upgrades the reuse-or-absent fact to all-bound.
        have hAllBound : ∀ p ∈ (s.M ++ T).toList,
            (env.toTCtx ctx).types.find? p.1 = some (.forAll [] p.2) := by
          intro q hq
          rcases hReuse q hq with hb | habsent
          · exact hb
          · -- an absent name would appear in `missing`, contradicting `isEmpty`
            exfalso
            have hfr : VarCtx.isFresh ctx q.1 = true := by
              rcases hfind_q : ctx.find? q.1 with _ | τ
              · simp [VarCtx.isFresh, hfind_q]
              · rw [(env.corr ctx).1 q.1 τ hfind_q] at habsent; simp at habsent
            rw [List.isEmpty_iff, List.filter_eq_nil_iff] at hempty
            exact absurd hfr (by simpa [needsInit] using hempty q hq)
        exact call_inline_sound s.M s.I s.O T exprs hfind hInputs hOutputs
          hExLen hTVals hExTy hIdisjOut hAllBound
      · -- Something missing: init-chain block over just the missing names.
        simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
        obtain ⟨label, hlabel, rfl⟩ := hr
        have hfresh_label := genFreshLabel_not_mem labels label hlabel
        -- The generator inits the missing in-out args then the missing out targets
        -- and filters over `ctx`; `call_mixed_sound` takes one `missingIn` over
        -- `env.toTCtx ctx`.
        rw [filter_needsInit_append, filter_needsInit_eq_missingIn env ctx]
        exact call_mixed_sound label s.M s.I s.O T exprs hfresh_label hfind hInputs hOutputs
          hExLen hTVals hExTy hIdisjOut hNodup hReuse
    · simp only [SetGen.support, SetGen.bot_mem_iff] at hr

-- ── Guard / measure / invariant soundness helpers ────────────────────────

/-- Any `.det`-guard produced by `genCondOrNondet` (at depth `d`) carries a
    boolean expression. -/
theorem genCondOrNondet_det_sound (env : GenStmtSoundEnv fctx octx tvars) (d : Nat)
    (cond : ExprOrNondet Expression)
    (hc : cond ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) fctx octx tvars d))
    (g : Expression.Expr) (hg : cond = .det g) :
    HasTypeA' [] g .bool := by
  simp only [genCondOrNondet, mem_support_pick_iff, mem_support_pure_iff,
             mem_support_map_iff] at hc
  rcases hc with hnondet | ⟨e, he, rfl⟩
  · exact absurd (hg ▸ hnondet) (by simp)
  · have : e = g := by simpa using hg
    subst this
    exact env.exprSound d .bool e he

/-- Any `some`-measure produced by `genOptMeasure` (at depth `d`) carries an
    integer expression. -/
theorem genOptMeasure_some_sound (env : GenStmtSoundEnv fctx octx tvars) (d : Nat)
    (m? : Option Expression.Expr)
    (hm : m? ∈ SetGen.support (genOptMeasure (G := SetGen.Set) fctx octx tvars d))
    (m : Expression.Expr) (hmeq : m? = some m) :
    HasTypeA' [] m .int := by
  simp only [genOptMeasure,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)] at hm
  rcases hm with hnone | ⟨e, he, hm⟩
  · exact absurd (hmeq ▸ hnone) (by simp)
  · subst hmeq
    have : e = m := (Option.some.inj hm).symm
    subst this
    exact env.exprSound d .int e he

/-- Every invariant produced by `genInvariants` (at depth `d`) carries a boolean
    expression. -/
theorem genInvariants_sound (env : GenStmtSoundEnv fctx octx tvars) (d : Nat)
    (invs : List (String × Expression.Expr))
    (hinv : invs ∈ SetGen.support (genInvariants (G := SetGen.Set) fctx octx tvars d))
    (p : String × Expression.Expr) (hp : p ∈ invs) :
    HasTypeA' [] p.2 .bool := by
  simp only [genInvariants, mem_support_listOfMaxLength_iff] at hinv
  have hp_supp := hinv.2 p hp
  simp only [genInvariant, mem_support_bind_iff, mem_support_pure_iff] at hp_supp
  obtain ⟨l, _hl, e, he, rfl⟩ := hp_supp
  exact env.exprSound d .bool e he

-- ── Mutual soundness of genStmt / genStmts ───────────────────────────────

/-- `genStmt` preserves *functionality* of the context. The nesting
    constructors (`block`, `ite`, `loop`) are lexically scoped — their output
    scope is the *input* `ctx` (the body's threaded scope is discarded) — and the
    non-`cmd` leaves also leave `ctx` unchanged, so the only case that can grow
    the context is `cmd`, handled by `genCmd_outCtx_functional`. No recursion into
    the body is needed, so this stands outside the soundness `mutual` block. -/
theorem genStmt_outCtx_functional
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n)) :
    Map.Functional r.outCtx := by
  cases n with
  | zero =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · -- cmd
      simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨rc, hrc, rfl⟩ := hr
      exact genCmd_outCtx_functional fctx octx tvars immutableVars ctx 0 hFun rc hrc
    · -- exit
      cases labels with
      | nil => simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
      | cons hd tl =>
        simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_elements_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr; exact hFun
    · -- funcDecl
      simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff,
                 mem_support_pure_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr; exact hFun
    · -- typeDecl
      simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
      obtain ⟨tc, _, hr⟩ := hr
      split at hr
      · simp only [mem_support_pure_iff] at hr; subst hr; exact hFun
      · simp only [SetGen.support, SetGen.bot_mem_iff] at hr
    · -- call: outCtx = ctx (lexically scoped block)
      exact genCallStmt_outCtx hFun r hr
  | succ size =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · -- cmd
      simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨rc, hrc, rfl⟩ := hr
      exact genCmd_outCtx_functional fctx octx tvars immutableVars ctx (size + 1) hFun rc hrc
    · -- exit
      cases labels with
      | nil => simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
      | cons hd tl =>
        simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_elements_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr; exact hFun
    · -- funcDecl
      simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff,
                 mem_support_pure_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr; exact hFun
    · -- typeDecl
      simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
      obtain ⟨tc, _, hr⟩ := hr
      split at hr
      · simp only [mem_support_pure_iff] at hr; subst hr; exact hFun
      · simp only [SetGen.support, SetGen.bot_mem_iff] at hr
    · -- call: outCtx = ctx (lexically scoped block)
      exact genCallStmt_outCtx hFun r hr
    · -- block: outCtx = ctx
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨_, _, ⟨⟨_, _⟩⟩, _, _, _, rfl⟩ := hr; exact hFun
    · -- ite_det
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨_, _, ⟨⟨_, _⟩⟩, _, ⟨⟨_, _⟩⟩, _, _, _, _, _, rfl⟩ := hr; exact hFun
    · -- ite_nondet
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨⟨⟨_, _⟩⟩, _, ⟨⟨_, _⟩⟩, _, _, _, _, _, rfl⟩ := hr; exact hFun
    · -- loop
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨_, _, _, _, _, _, ⟨⟨_, _⟩⟩, _, _, _, rfl⟩ := hr; exact hFun

mutual

/-- **Soundness of `genStmt`.** Every statement in the generator's support is
    well-typed w.r.t. `StmtHasTypeA` (for any program `P`), with the generator's
    output ambient context `r.outC` and output scope `env.toTCtx r.outCtx` being
    exactly the output contexts of the typing relation.

    Proof by well-founded recursion on the `size` budget `n`. Leaf constructors
    (`cmd`, `exit`, `funcDecl`, `typeDecl`) are discharged by the per-constructor
    lemmas above (at the current depth); nesting constructors (`block`, `ite`,
    `loop`) invert the corresponding `do`-block and appeal to `genStmts_sound` at
    the smaller `size`. -/
theorem genStmt_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n)) :
    StmtHasTypeA P C (env.toTCtx ctx) labels r.stmt r.outC (env.toTCtx r.outCtx) := by
  cases n with
  | zero =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact genCmdStmt_sound P env C ctx 0 hFun r hr
    · exact genExitStmt_sound P env C ctx r hr
    · exact genFuncDeclStmt_sound P env C ctx 0 r hr
    · exact genTypeDeclStmt_sound P env C ctx 0 r hr
    · exact genCallStmt_sound P env procs hProcs C ctx 0 r hr
  | succ size =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact genCmdStmt_sound P env C ctx (size + 1) hFun r hr
    · exact genExitStmt_sound P env C ctx r hr
    · exact genFuncDeclStmt_sound P env C ctx (size + 1) r hr
    · exact genTypeDeclStmt_sound P env C ctx (size + 1) r hr
    · exact genCallStmt_sound P env procs hProcs C ctx (size + 1) r hr
    · -- block
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨label, hlabel, ⟨⟨len, _⟩⟩, _hlenbd, triple, htriple, rfl⟩ := hr
      have hfresh := genFreshLabel_not_mem labels label hlabel
      have ih := genStmts_sound P env immutableVars procs hProcs (label :: labels) C ctx size len hFun triple htriple
      exact StmtHasType'.block C (env.toTCtx ctx) triple.2.1 (env.toTCtx triple.2.2)
        labels label triple.1 default hfresh ih
    · -- ite_det
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨cond, hcond, ⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmts_sound P env immutableVars procs hProcs labels C ctx size tlen hFun tt htt
      have ihe := genStmts_sound P env immutableVars procs hProcs labels C ctx size elen hFun et het
      exact StmtHasType'.ite_det C (env.toTCtx ctx) tt.2.1 (env.toTCtx tt.2.2)
        et.2.1 (env.toTCtx et.2.2) labels cond tt.1 et.1 default
        (env.exprSound (size + 1) .bool cond hcond) iht ihe
    · -- ite_nondet
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmts_sound P env immutableVars procs hProcs labels C ctx size tlen hFun tt htt
      have ihe := genStmts_sound P env immutableVars procs hProcs labels C ctx size elen hFun et het
      exact StmtHasType'.ite_nondet C (env.toTCtx ctx) tt.2.1 (env.toTCtx tt.2.2)
        et.2.1 (env.toTCtx et.2.2) labels tt.1 et.1 default iht ihe
    · -- loop
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨guard, hguard, measure, hmeasure, invs, hinvs, ⟨⟨blen, _⟩⟩, _, body, hbody, rfl⟩ := hr
      have ih := genStmts_sound P env immutableVars procs hProcs labels C ctx size blen hFun body hbody
      refine StmtHasType'.loop C (env.toTCtx ctx) body.2.1 (env.toTCtx body.2.2)
        labels guard measure invs body.1 default ?_ ?_ ?_ ih
      · intro g hg
        exact genCondOrNondet_det_sound env (size + 1) guard hguard g hg
      · intro m hm
        exact genOptMeasure_some_sound env (size + 1) measure hmeasure m hm
      · intro p hp
        exact genInvariants_sound env (size + 1) invs hinvs p hp
termination_by (n, 0, 0)

/-- **Soundness of `genStmts`.** Every statement sequence in the generator's
    support satisfies the chained `StmtsHasTypeA` relation between the input
    contexts and the generator's threaded output contexts.

    Proof by well-founded recursion on the remaining length `len` (with the
    `size` fixed): the `nil` case is trivial, and the `cons` case types the head
    via `genStmt_sound` and the tail via the induction hypothesis. -/
theorem genStmts_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (size len : Nat) (hFun : Map.Functional ctx)
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size len)) :
    StmtsHasTypeA P C (env.toTCtx ctx) labels result.1 result.2.1 (env.toTCtx result.2.2) := by
  cases len with
  | zero =>
    simp only [genStmts, mem_support_pure_iff] at hr
    subst hr
    exact StmtsHasType'.nil C (env.toTCtx ctx) labels
  | succ len =>
    simp only [genStmts, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨rhead, hhead, rtail, htail, rfl⟩ := hr
    have hh := genStmt_sound P env immutableVars procs hProcs labels C ctx size hFun rhead hhead
    have hFun' : Map.Functional rhead.outCtx :=
      genStmt_outCtx_functional fctx octx tvars immutableVars procs labels C ctx size hFun rhead hhead
    have ht := genStmts_sound P env immutableVars procs hProcs labels rhead.outC rhead.outCtx size len hFun' rtail htail
    exact StmtsHasType'.cons C rhead.outC rtail.2.1 (env.toTCtx ctx) (env.toTCtx rhead.outCtx)
      (env.toTCtx rtail.2.2) labels rhead.stmt rtail.1 hh ht
termination_by (size, 1, len)

end

-- ── Membership-lifting lemmas (for completeness) ─────────────────────────
-- These lift a result from a sub-generator's support into `genStmt`'s support.
-- Every branch of the `frequency` list has positive weight, so its support is
-- contained in `genStmt`'s support; these lemmas package the reconstruction.
--
-- With the single `size` budget, the leaf sub-generators are invoked at *the same*
-- size `n` as `genStmt` itself (`genStmt … n` calls `genCmdStmt … n`), so the leaf
-- `_mem` lemmas take a result at depth `n` and land in `genStmt … n`.

/-- A `genCmdStmt` result (at depth `n`) is reachable by `genStmt … n`. -/
theorem genCmdStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCmdStmt (G := SetGen.Set) fctx octx tvars immutableVars C ctx n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1; omega)]
    exact ⟨4, _, .head _, by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
    exact ⟨4, _, .head _, by omega, hr⟩

/-- A `genExitStmt` result is reachable by `genStmt … n` at *every* size `n`. -/
theorem genExitStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1; omega)]
    exact ⟨1, _, .tail _ (.head _), by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
    exact ⟨1, _, .tail _ (.head _), by omega, hr⟩

/-- A `genFuncDeclStmt` result (at depth `n`) is reachable by `genStmt … n`. -/
theorem genFuncDeclStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genFuncDeclStmt (G := SetGen.Set) fctx octx C ctx n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.head _)), by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.head _)), by omega, hr⟩

/-- A `genTypeDeclStmt` result (at depth `n`) is reachable by `genStmt … n`. -/
theorem genTypeDeclStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩

/-- A `genCallStmt` result (at depth `n`) is reachable by `genStmt … n`. The call
    branch sits at frequency index 4 in both the size-0 and size+1 lists. -/
theorem genCallStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCallStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, hr⟩

/-- A `block` statement is reachable by `genStmt … (size+1)` when its body (of some
    length `len ≤ size+1`) is reachable by `genStmts … size` under the extended
    label scope `label :: labels`. -/
theorem block_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (label : String) (body : List Statement) (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (len : Nat) (hlen : len ≤ size + 1)
    (hbody : (body, C_body, Γ_body) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs (label :: labels) C ctx size len))
    (hlabel : label ∈ SetGen.support (genFreshLabel (G := SetGen.Set) labels)) :
    (⟨Stmt.block label body default, C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx (size + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨label, hlabel, ⟨⟨len, Nat.zero_le _, hlen⟩⟩, ⟨Nat.zero_le _, hlen⟩,
    (body, C_body, Γ_body), hbody, rfl⟩

/-- An `ite (.det cond)` statement is reachable by `genStmt … (size+1)` when the
    condition is a reachable boolean (at depth `size+1`) and both branches are
    reachable by `genStmts … size`. -/
theorem ite_det_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (cond : Expression.Expr) (thenb elseb : List Statement)
    (Ct : LContext CoreLParams) (Γt : VarCtx) (Ce : LContext CoreLParams) (Γe : VarCtx)
    (tlen elen : Nat) (htlen : tlen ≤ size + 1) (helen : elen ≤ size + 1)
    (hcond : cond ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] (size + 1) .bool))
    (hthen : (thenb, Ct, Γt) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size tlen))
    (helse : (elseb, Ce, Γe) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size elen)) :
    (⟨Stmt.ite (.det cond) thenb elseb default, C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx (size + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨cond, hcond, ⟨⟨tlen, Nat.zero_le _, htlen⟩⟩, ⟨Nat.zero_le _, htlen⟩,
    ⟨⟨elen, Nat.zero_le _, helen⟩⟩, ⟨Nat.zero_le _, helen⟩,
    (thenb, Ct, Γt), hthen, (elseb, Ce, Γe), helse, rfl⟩

/-- An `ite .nondet` statement is reachable by `genStmt … (size+1)` when both
    branches are reachable by `genStmts … size`. -/
theorem ite_nondet_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (thenb elseb : List Statement)
    (Ct : LContext CoreLParams) (Γt : VarCtx) (Ce : LContext CoreLParams) (Γe : VarCtx)
    (tlen elen : Nat) (htlen : tlen ≤ size + 1) (helen : elen ≤ size + 1)
    (hthen : (thenb, Ct, Γt) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size tlen))
    (helse : (elseb, Ce, Γe) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size elen)) :
    (⟨Stmt.ite .nondet thenb elseb default, C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx (size + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
  refine ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨⟨⟨tlen, Nat.zero_le _, htlen⟩⟩, ⟨Nat.zero_le _, htlen⟩,
    ⟨⟨elen, Nat.zero_le _, helen⟩⟩, ⟨Nat.zero_le _, helen⟩,
    (thenb, Ct, Γt), hthen, (elseb, Ce, Γe), helse, rfl⟩

/-- A `loop` statement is reachable by `genStmt … (size+1)` when its guard, measure,
    invariants (all at depth `size+1`), and body (by `genStmts … size`) are all
    reachable. -/
theorem loop_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (body : List Statement)
    (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (blen : Nat) (hblen : blen ≤ size + 1)
    (hguard : guard ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) fctx octx tvars (size + 1)))
    (hmeasure : measure ∈ SetGen.support (genOptMeasure (G := SetGen.Set) fctx octx tvars (size + 1)))
    (hinvs : invs ∈ SetGen.support (genInvariants (G := SetGen.Set) fctx octx tvars (size + 1)))
    (hbody : (body, C_body, Γ_body) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size blen)) :
    (⟨Stmt.loop guard measure invs body default, C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx (size + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by show 0 < 4+1+1+1+1+2+2+1+2; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨guard, hguard, measure, hmeasure, invs, hinvs,
    ⟨⟨blen, Nat.zero_le _, hblen⟩⟩, ⟨Nat.zero_le _, hblen⟩,
    (body, C_body, Γ_body), hbody, rfl⟩

-- ── genStmts membership: cons / nil ──────────────────────────────────────

/-- The empty statement list is in `genStmts`'s support at length `0`. -/
theorem genStmts_nil_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat) :
    ((([] : List Statement)), C, ctx) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size 0) := by
  rw [genStmts]; exact mem_support_pure_iff.mpr rfl

/-- If the head statement `r` is reachable by `genStmt` (at `size`) and the tail is
    reachable by `genStmts` from the head's output contexts (at the same `size`,
    length `len`), then the whole `cons` is reachable at length `len+1`. -/
theorem genStmts_cons_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size len : Nat)
    (r : GenStmtResult) (rest : List Statement) (C'' : LContext CoreLParams) (Γ'' : VarCtx)
    (hhead : r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size))
    (htail : (rest, C'', Γ'') ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels r.outC r.outCtx size len)) :
    (r.stmt :: rest, C'', Γ'') ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size (len + 1)) := by
  rw [genStmts]
  simp only [mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨r, hhead, (rest, C'', Γ''), htail, rfl⟩

-- ── Completeness helper lemmas ────────────────────────────────────────────
-- Straightforward `pick`/`map`/`listOfMaxLength` support-inversion lemmas, one
-- per guard/measure/invariant/type-constructor sub-generator, mirroring
-- `genOptExpr_complete` in `FunctionHasTypeAGen.lean`. These convert typed
-- side-conditions into the raw support-membership premises of `StmtReachable`, so
-- a caller can build a reachability witness. Each is stated at an arbitrary depth.

/-- Completeness of `genCondOrNondet`. `.nondet` is always reachable; `.det g` is
    reachable when `g` is reachable by `genLExpr` at type `bool`. -/
theorem genCondOrNondet_complete (depth : Nat) (cond : ExprOrNondet Expression)
    (hcond : ∀ g, cond = .det g →
      g ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    cond ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genCondOrNondet, mem_support_pick_iff, mem_support_pure_iff, mem_support_map_iff]
  cases cond with
  | nondet => exact Or.inl rfl
  | det g => exact Or.inr ⟨g, hcond g rfl, rfl⟩

/-- Completeness of `genOptMeasure`. `none` is always reachable; `some m` is
    reachable when `m` is reachable by `genLExpr` at type `int`. -/
theorem genOptMeasure_complete (depth : Nat) (measure : Option Expression.Expr)
    (hmeasure : ∀ m, measure = some m →
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .int)) :
    measure ∈ SetGen.support (genOptMeasure (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genOptMeasure,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)]
  cases measure with
  | none => exact Or.inl rfl
  | some m => exact Or.inr ⟨m, hmeasure m rfl, rfl⟩

/-- Completeness of `genInvariant`. A `(label, e)` pair is reachable when the
    label is a reachable identifier (via `genIdentName`, so non-empty and
    non-keyword) and `e` is a reachable boolean. -/
theorem genInvariant_complete (depth : Nat) (p : String × Expression.Expr)
    (hlabel : p.1 ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hexpr : p.2 ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    p ∈ SetGen.support (genInvariant (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genInvariant, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨p.1, hlabel, p.2, hexpr, rfl⟩

/-- Completeness of `genInvariants`. A list of invariants is reachable when it is
    no longer than `depth` and each element is reachable by `genInvariant`. -/
theorem genInvariants_complete (depth : Nat) (invs : List (String × Expression.Expr))
    (hlen : invs.length ≤ depth)
    (hinvs : ∀ p ∈ invs, p.1 ∈ SetGen.support (genIdentName (G := SetGen.Set)) ∧
      p.2 ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    invs ∈ SetGen.support (genInvariants (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genInvariants, mem_support_listOfMaxLength_iff]
  refine ⟨hlen, fun p hp => ?_⟩
  exact genInvariant_complete depth p (hinvs p hp).1 (hinvs p hp).2

/-- Completeness of `genTypeConstructor`. A type constructor is reachable when its
    name and each parameter name are reachable identifiers (via `genIdentName`, so
    non-empty and non-keyword), its parameter list is no longer than `depth`, and
    its `bound` is at the default `.Infinite`. -/
theorem genTypeConstructor_complete (depth : Nat) (tc : TypeConstructor)
    (hbound : tc.bound = .Infinite)
    (hname : tc.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hlen : tc.params.length ≤ depth)
    (hparams : ∀ s ∈ tc.params, s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    tc ∈ SetGen.support (genTypeConstructor (G := SetGen.Set) depth) := by
  simp only [genTypeConstructor, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_listOfMaxLength_iff]
  refine ⟨tc.name, hname, tc.params, ⟨hlen, hparams⟩, ?_⟩
  obtain ⟨bound, name, params⟩ := tc
  simp only at hbound
  subst hbound
  rfl

-- ── Reachability relation ──────────────────────────────────────────────────
-- `StmtReachable`/`StmtsReachable` are a size-indexed, `VarCtx`-threaded mutual
-- inductive mirroring `genStmt`/`genStmts` *exactly*. A statement is "reachable"
-- when it is in the generator's normal form (metadata `default`) and each of its
-- components is reachable by the corresponding sub-generator (at the appropriate
-- depth). The relation is the *specification* of completeness: `genStmt_complete`
-- below shows every reachable statement is in the generator's support, and
-- `genStmt_sound` shows the converse-flavored fact that support ⇒ `StmtHasTypeA`.
-- (Completeness cannot be stated directly over `StmtHasTypeA`: lexical scoping
-- makes the judgment of `block`/`ite`/`loop` `C Γ ⟶ C Γ`, so it would be vacuous
-- for the nesting constructors.)

mutual

/-- Size-indexed reachability for a single statement. `StmtReachable labels C ctx n s C' ctx'`
    means the result `⟨s, C', ctx'⟩` is produced by `genStmt … labels C ctx n`.
    `labels` (the enclosing block labels) is an *index* because a `block` extends it
    with its own label when descending into its body. -/
inductive StmtReachable (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) :
    List String → LContext CoreLParams → VarCtx → Nat → Statement →
    LContext CoreLParams → VarCtx → Prop where
  /-- A `cmd` statement (generated at depth = the size `n`). -/
  | cmd : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genCmdStmt (G := SetGen.Set) fctx octx tvars immutableVars C ctx n) →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx n res.stmt res.outC res.outCtx
  /-- An `exit` statement: any result of `genExitStmt` at the enclosing `labels`. -/
  | exit : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx) →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx n res.stmt res.outC res.outCtx
  /-- A `funcDecl` statement (generated at depth = the size `n`). -/
  | funcDecl : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genFuncDeclStmt (G := SetGen.Set) fctx octx C ctx n) →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx n res.stmt res.outC res.outCtx
  /-- A `typeDecl` statement (or its `exit` fallback), generated at depth `n`. -/
  | typeDecl : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx n) →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx n res.stmt res.outC res.outCtx
  /-- A procedure `call` statement (generated at depth = the size `n`). -/
  | call : ∀ labels C ctx n (res : GenStmtResult),
      res ∈ SetGen.support (genCallStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n) →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx n res.stmt res.outC res.outCtx
  /-- A `block`, at size `size+1`, whose body is reachable at size `size`. The body
      is generated under `label :: labels`, so a nested `exit` may target this block. -/
  | block : ∀ labels C ctx size label body C_body Γ_body len,
      len ≤ size + 1 →
      label ∈ SetGen.support (genFreshLabel (G := SetGen.Set) labels) →
      StmtsReachable fctx octx tvars immutableVars procs (label :: labels) C ctx size len body C_body Γ_body →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx (size + 1)
        (Stmt.block label body default) C ctx
  /-- A deterministic `ite`, at size `size+1`, with reachable condition (at depth
      `size+1`) and branches (at size `size`). -/
  | ite_det : ∀ labels C ctx size cond thenb elseb Ct Γt Ce Γe tlen elen,
      tlen ≤ size + 1 → elen ≤ size + 1 →
      cond ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] (size + 1) .bool) →
      StmtsReachable fctx octx tvars immutableVars procs labels C ctx size tlen thenb Ct Γt →
      StmtsReachable fctx octx tvars immutableVars procs labels C ctx size elen elseb Ce Γe →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx (size + 1)
        (Stmt.ite (.det cond) thenb elseb default) C ctx
  /-- A non-deterministic `ite`, at size `size+1`, with reachable branches. -/
  | ite_nondet : ∀ labels C ctx size thenb elseb Ct Γt Ce Γe tlen elen,
      tlen ≤ size + 1 → elen ≤ size + 1 →
      StmtsReachable fctx octx tvars immutableVars procs labels C ctx size tlen thenb Ct Γt →
      StmtsReachable fctx octx tvars immutableVars procs labels C ctx size elen elseb Ce Γe →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx (size + 1)
        (Stmt.ite .nondet thenb elseb default) C ctx
  /-- A `loop`, at size `size+1`, with reachable guard/measure/invariants (at depth
      `size+1`) and body (at size `size`). -/
  | loop : ∀ labels C ctx size guard measure invs body C_body Γ_body blen,
      blen ≤ size + 1 →
      guard ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) fctx octx tvars (size + 1)) →
      measure ∈ SetGen.support (genOptMeasure (G := SetGen.Set) fctx octx tvars (size + 1)) →
      invs ∈ SetGen.support (genInvariants (G := SetGen.Set) fctx octx tvars (size + 1)) →
      StmtsReachable fctx octx tvars immutableVars procs labels C ctx size blen body C_body Γ_body →
      StmtReachable fctx octx tvars immutableVars procs labels C ctx (size + 1)
        (Stmt.loop guard measure invs body default) C ctx

/-- Size-indexed reachability for a statement list. `StmtsReachable labels C ctx size len ss C' ctx'`
    means `(ss, C', ctx')` is produced by `genStmts … labels C ctx size len`. -/
inductive StmtsReachable (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) :
    List String → LContext CoreLParams → VarCtx → Nat → Nat → List Statement →
    LContext CoreLParams → VarCtx → Prop where
  /-- The empty list, at length `0`. -/
  | nil : ∀ labels C ctx size,
      StmtsReachable fctx octx tvars immutableVars procs labels C ctx size 0 [] C ctx
  /-- A `cons`, at length `len+1`: reachable head threaded into a reachable tail. -/
  | cons : ∀ labels C ctx size len s C_h Γ_h rest C'' Γ'',
      StmtReachable fctx octx tvars immutableVars procs labels C ctx size s C_h Γ_h →
      StmtsReachable fctx octx tvars immutableVars procs labels C_h Γ_h size len rest C'' Γ'' →
      StmtsReachable fctx octx tvars immutableVars procs labels C ctx size (len + 1) (s :: rest) C'' Γ''

end

-- ── Completeness: every reachable statement is in the generator's support ──

mutual

/-- **Completeness of `genStmt`.** Every statement reachable per `StmtReachable`
    (in generator normal form with reachable components) is in `genStmt`'s support,
    with the *exact* statement, output ambient context, and output scope. Proof by
    induction on the reachability derivation, dispatching each constructor to the
    membership-lifting lemma of the corresponding generator branch. -/
theorem genStmt_complete (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (s : Statement) (C' : LContext CoreLParams) (ctx' : VarCtx)
    (h : StmtReachable fctx octx tvars immutableVars procs labels C ctx n s C' ctx') :
    (⟨s, C', ctx'⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n) := by
  cases h with
  | cmd labels C ctx n res hres => exact genCmdStmt_mem procs C ctx n res hres
  | exit labels C ctx n res hres => exact genExitStmt_mem procs C ctx n res hres
  | funcDecl labels C ctx n res hres => exact genFuncDeclStmt_mem procs C ctx n res hres
  | typeDecl labels C ctx n res hres => exact genTypeDeclStmt_mem procs C ctx n res hres
  | call labels C ctx n res hres => exact genCallStmt_mem procs C ctx n res hres
  | block labels C ctx size label body C_body Γ_body len hlen hlabel hbody =>
    exact block_mem procs C ctx size label body C_body Γ_body len hlen
      (genStmts_complete procs (label :: labels) C ctx size len body C_body Γ_body hbody) hlabel
  | ite_det labels C ctx size cond thenb elseb Ct Γt Ce Γe tlen elen htlen helen hcond hthen helse =>
    exact ite_det_mem procs C ctx size cond thenb elseb Ct Γt Ce Γe tlen elen htlen helen hcond
      (genStmts_complete procs labels C ctx size tlen thenb Ct Γt hthen)
      (genStmts_complete procs labels C ctx size elen elseb Ce Γe helse)
  | ite_nondet labels C ctx size thenb elseb Ct Γt Ce Γe tlen elen htlen helen hthen helse =>
    exact ite_nondet_mem procs C ctx size thenb elseb Ct Γt Ce Γe tlen elen htlen helen
      (genStmts_complete procs labels C ctx size tlen thenb Ct Γt hthen)
      (genStmts_complete procs labels C ctx size elen elseb Ce Γe helse)
  | loop labels C ctx size guard measure invs body C_body Γ_body blen hblen hguard hmeasure hinvs hbody =>
    exact loop_mem procs C ctx size guard measure invs body C_body Γ_body blen hblen
      hguard hmeasure hinvs
      (genStmts_complete procs labels C ctx size blen body C_body Γ_body hbody)

/-- **Completeness of `genStmts`.** Every statement list reachable per
    `StmtsReachable` is in `genStmts`'s support, with the exact list and output
    contexts. The `cons` case threads the head via `genStmt_complete` and the tail
    via the induction hypothesis, both at the same `size`. -/
theorem genStmts_complete (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (size len : Nat)
    (ss : List Statement) (C' : LContext CoreLParams) (ctx' : VarCtx)
    (h : StmtsReachable fctx octx tvars immutableVars procs labels C ctx size len ss C' ctx') :
    ((ss, C', ctx') : List Statement × LContext CoreLParams × VarCtx) ∈
      SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx size len) := by
  cases h with
  | nil => exact genStmts_nil_mem procs C ctx size
  | cons labels _ _ _ len s C_h Γ_h rest _ _ hhead htail =>
    have hh := genStmt_complete procs labels C ctx size s C_h Γ_h hhead
    have ht := genStmts_complete procs labels C_h Γ_h size len rest C' ctx' htail
    exact genStmts_cons_mem procs C ctx size len ⟨s, C_h, Γ_h⟩ rest C' ctx' hh ht

end

-- ── Capstone: reachable ⇒ in support ∧ well-typed ────────────────────────

/-- **Completeness–soundness capstone for `genStmt`.** Every statement reachable
    per `StmtReachable` is (a) in `genStmt`'s support at the exact statement/output
    contexts (completeness), and (b) well-typed w.r.t. `StmtHasTypeA` for any
    program `P` (soundness). Together these witness that `StmtReachable` characterizes
    exactly the generator's *well-typed* support, confirming the reachability
    relation is not vacuous. -/
theorem genStmt_complete_sound (P : Program) (env : GenStmtSoundEnv fctx octx tvars)
    (procs : ProcSigCtx) (hProcs : ProcSigCorresponds procs P)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (hFun : Map.Functional ctx)
    (s : Statement) (C' : LContext CoreLParams) (ctx' : VarCtx)
    (h : StmtReachable fctx octx tvars immutableVars procs labels C ctx n s C' ctx') :
    (⟨s, C', ctx'⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars procs labels C ctx n) ∧
    StmtHasTypeA P C (env.toTCtx ctx) labels s C' (env.toTCtx ctx') := by
  have hmem := genStmt_complete procs labels C ctx n s C' ctx' h
  exact ⟨hmem, genStmt_sound P env immutableVars procs hProcs labels C ctx n hFun ⟨s, C', ctx'⟩ hmem⟩

end StrataGenerators.Stmt
