import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.CmdHasTypeAGen
import StrataGenerators.FunctionHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Stmt

/-!
# Soundness and completeness of `genStmt` / `genStmtChain`

`genStmt` / `genStmtChain` (in `StmtHasTypeAGen/Core.lean`) generate random Strata
Core statements. This file proves them **sound** and **complete** with respect to
the `StatementHasTypeA` / `StatementsHasTypeA` typing relations of
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

`genStmt`/`genStmtChain` take a single `size` (the QuickCheck-style `sized` knob):
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
  the fifth argument of the 6-place `StatementHasTypeA` relation. Its typing role is in
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
structure GenStmtSoundEnv (octx : OpCtx) (tvars : List TyIdentifier)
    (pctx : PolyOpCtx := []) where
  /-- Produce the semantic `TContext` for any flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The `VarCtx ↔ TContext` correspondence holds for every context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- Expression-level soundness at *every* depth, at each context's own derived
      free-variable projection `ctx.toFVarCtx` (the statement generators feed that
      into `genLExpr`). -/
  exprSound : ∀ d (ctx : VarCtx), GenLExprSound ctx.toFVarCtx octx tvars d pctx
  /-- Fresh names never collide with the free variables of generated expressions, at
      every depth — now unconditional at each `ctx`, since free variables are drawn
      from `ctx.toFVarCtx` (whose names are `ctx`'s) and a fresh name avoids `ctx`. -/
  freshDisjoint :
    ∀ d (ctx : VarCtx), FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx d pctx
  /-- `toTCtx` commutes with `VarCtx.insert` up to `TContext.Equiv` (needed for the `init`
      command case). Equality is unavailable now that a scope is an opaque hash map —
      see `GenCmdSoundEnv.toTCtx_insert`. -/
  toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
    TContext.Equiv (T := CoreLParams) (toTCtx (ctx.insert x mty))
      { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }

/-- Reinterpret a `GenStmtSoundEnv` as a `GenCmdSoundEnv` at an arbitrary ambient
    context `C` and depth `d`. Legal because no `GenCmdSoundEnv` field references
    `C`, and the environment supplies its expression obligations at every depth. -/
def GenStmtSoundEnv.toCmdEnv {octx tvars pctx}
    (env : GenStmtSoundEnv octx tvars pctx) (C : LContext CoreLParams) (d : Nat) :
    GenCmdSoundEnv octx tvars d C pctx where
  toTCtx := env.toTCtx
  corr := env.corr
  exprSound := fun ctx => env.exprSound d ctx
  freshDisjoint := fun ctx => env.freshDisjoint d ctx
  toTCtx_insert := env.toTCtx_insert

/-- `toTCtx` commutes with a *whole* `init` chain, not just one insertion: the
    generator-side `insertAllCtx` and the semantic `insertAll` are the same `foldl`,
    and `toTCtx_insert` matches them step by step. This is what lets the inline call
    chunk — whose output scope is `insertAllCtx ctx toInit` — be typed by the
    call-soundness lemmas, which speak about `insertAll Γ …`. -/
theorem GenStmtSoundEnv.toTCtx_insertAllCtx {octx tvars pctx}
    (env : GenStmtSoundEnv octx tvars pctx) (news : List (Identifier Unit × LMonoTy)) :
    ∀ ctx, TContext.Equiv (T := CoreLParams)
      (env.toTCtx (StrataGenerators.Stmt.insertAllCtx ctx news))
      (StrataGenerators.Stmt.insertAll (env.toTCtx ctx) news) := by
  induction news with
  | nil => intro ctx; exact TContext.Equiv.refl (T := CoreLParams) _
  | cons hd tl ih =>
    intro ctx
    rw [StrataGenerators.Stmt.insertAllCtx_cons]
    -- `insertAll (…insert…) tl` on the right; step past the head insertion with
    -- `toTCtx_insert`, then `insertAll` congruence for the tail.
    refine (ih _).trans ?_
    rw [show StrataGenerators.Stmt.insertAll (env.toTCtx ctx) (hd :: tl)
          = StrataGenerators.Stmt.insertAll
              { env.toTCtx ctx with
                types := (env.toTCtx ctx).types.insert hd.1 (.forAll [] hd.2) } tl from by
        simp [StrataGenerators.Stmt.insertAll]]
    exact StrataGenerators.Stmt.insertAll_equiv tl (env.toTCtx_insert ctx hd.1 hd.2)

-- ── Leaf-case soundness lemmas ───────────────────────────────────────────

variable {octx : OpCtx} {tvars : List TyIdentifier} {pctx : PolyOpCtx}
  {immutableVars : List (Identifier Unit)} {labels : List String}

-- ── The well-kindedness premises upstream's `init` rules impose ──────────
--
-- `CmdHasType'.init_det`/`init_nondet` now require the stored monotype to be well-kinded
-- in the ambient context (`C.WellKindedTy`), i.e. every type constructor applied at the
-- arity `C.knownTypes` records for it. Two of the statement generators store types:
--
-- * `genCmdStmt`, whose `init` types come from `genLMonoTy` — always `SimpleType`s, so
--   `SimpleTyArities C` suffices (`wellKindedTy_of_genLMonoTy`);
-- * `genCallStmt`, whose inline `init` chain stores the *callee's* signature types
--   instantiated by a sampled `σ`. Those are `SimpleType`s only if the callable
--   signatures and the sampled instantiation are, which depends on `procs`, `ctx` and
--   `octx` rather than on the generator alone.
--
-- `WellKindedOk` bundles exactly those facts, and `WellKindedPreserved` says a generated
-- statement carries them to its output context. Both are taken as **premises**: proving
-- the second needs `SimpleType`-closure results for `generableTypesFromCtx` and for the
-- contexts `typeDecl`/`funcDecl` produce, which is generator theory this port does not
-- add. Everything downstream threads them unchanged, so discharging them later is a
-- local change here and at the two `ProgramGen` call sites.

/-- The well-kindedness discipline the statement generators need at an ambient context `C`
    and variable scope `ctx`: `C` registers the `SimpleType` constructors at their own
    arities, every type reachable as a sampled instantiation is a `SimpleType`, and so is
    every type in a callable procedure's written-to blocks. -/
structure WellKindedOk (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) : Prop where
  /-- `C` registers `bool`/`int`/`string`/`real`/`regex` at 0, `arrow`/`Map` at 2 and
      `Sequence` at 1 — enough to make every `SimpleType` well-kinded in `C`. -/
  arities : SimpleTyArities C
  /-- Every type the call generator can sample for a callee's type parameter is a
      `SimpleType`. -/
  generable : ∀ ty ∈ generableTypesFromCtx ctx.values [] octx, SimpleType ty
  /-- Every type in a callable procedure's in-out and out-only blocks — the blocks the
      call generator writes back through, and therefore `init`s — is a `SimpleType`. -/
  sigs : ∀ s ∈ procs, ∀ ty ∈ (s.M ++ s.O).values, SimpleType ty

/-- `WellKindedOk` is carried from a statement's input context to its output context.
    Taken as a premise; see the note above. -/
def WellKindedPreserved (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (pctx : PolyOpCtx) : Prop :=
  ∀ (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult),
    r ∈ SetGen.support
      (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx pctx n) →
    WellKindedOk octx procs C ctx → WellKindedOk octx procs r.outC r.outCtx

/-- `toPureFuncDecl` always produces a non-recursive declaration. -/
@[simp] theorem toPureFuncDecl_not_isRecursive (f : Function) :
    (Function.toPureFuncDecl f).isRecursive = false := rfl

/-- Soundness of `genCmdStmt` (at any depth `d`). -/
theorem genCmdStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (C : LContext CoreLParams) (hC : SimpleTyArities C) (ctx : VarCtx) (d : Nat) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCmdStmt (G := SetGen.Set) octx tvars immutableVars C ctx d pctx)) :
    StatementsHasTypeA P C (env.toTCtx ctx) labels r.stmts r.outC (env.toTCtx r.outCtx) := by
  simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨rc, hrc, rfl⟩ := hr
  have hcmd :=
    genCmd_sound_env octx tvars immutableVars ctx d C pctx (env.toCmdEnv C d) hC hFun rc hrc
  exact StatementsHasTypeA_singleton
    (StatementHasType'.cmd C (env.toTCtx ctx) (env.toTCtx rc.outCtx) labels (.cmd rc.cmd) _
      (CmdExtHasType'.cmd (env.toTCtx ctx) (env.toTCtx rc.outCtx) rc.cmd hcmd)
      (tctxEquivRefl _))

/-- Soundness of `genExitStmt`. With enclosing labels the target is drawn from
    them (`label ∈ L`, discharging the `exit` premise); with no enclosing block
    (`labels = []`) the generator is empty (support `∅`), so there is nothing to
    prove. -/
theorem genExitStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (C : LContext CoreLParams) (ctx : VarCtx) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx)) :
    StatementsHasTypeA P C (env.toTCtx ctx) labels r.stmts r.outC (env.toTCtx r.outCtx) := by
  cases labels with
  | nil =>
    -- `genExitStmt [] … = default`, whose support is `∅`.
    simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons hd tl =>
    simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨l, hl, rfl⟩ := hr
    exact StatementsHasTypeA_singleton (StatementHasType'.exit C (env.toTCtx ctx) (hd :: tl) l default _ hl
      (tctxEquivRefl _))

/-- Soundness of `genFuncDeclStmt` (at any depth `d`). -/
theorem genFuncDeclStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (C : LContext CoreLParams) (hC : SimpleTyArities C) (ctx : VarCtx) (d : Nat) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genFuncDeclStmt (G := SetGen.Set) octx C ctx d pctx)) :
    StatementsHasTypeA P C (env.toTCtx ctx) labels r.stmts r.outC (env.toTCtx r.outCtx) := by
  simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff,
             mem_support_pure_iff] at hr
  obtain ⟨decl, ⟨f0, _hf0, rfl⟩, func, hfunc, rfl⟩ := hr
  have hwt : FuncHasTypeA C (env.toTCtx ctx) func :=
    genFunction_sound [] octx d C (env.toTCtx ctx) pctx hC func hfunc
  exact StatementsHasTypeA_singleton
    (StatementHasType'.funcDecl C (env.toTCtx ctx) labels (Function.toPureFuncDecl f0) func default _
      (by simp) hwt (tctxEquivRefl _))

/-- Soundness of `genTypeDeclStmt` (at any depth `d`). The `.ok` branch discharges
    `typeDecl`; the `.error` (name-clash) branch is the empty generator (support
    `∅`), so there is nothing to prove. -/
theorem genTypeDeclStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat) (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx d)) :
    StatementsHasTypeA P C (env.toTCtx ctx) labels r.stmts r.outC (env.toTCtx r.outCtx) := by
  simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
  obtain ⟨tc, _htc, hr⟩ := hr
  -- Branch on the same `addKnownTypeWithError` the generator computed.
  split at hr
  · -- `.ok C'`: the split hypothesis is exactly the `typeDecl` premise.
    rename_i C' heq
    simp only [mem_support_pure_iff] at hr
    subst hr
    exact StatementsHasTypeA_singleton (StatementHasType'.typeDecl C C' (env.toTCtx ctx) labels tc default _ heq
      (tctxEquivRefl _))
  · -- `.error`: the empty generator `default`, whose support is `∅`.
    rename_i heq
    simp only [SetGen.support, SetGen.bot_mem_iff] at hr

-- ── Fresh-label freshness (for the `block` premise) ──────────────────────

/-- `fallbackFreshLabel labels` is absent from `labels`: it is strictly longer
    than every label in the list. Reuses the shared foldl-max bound
    `foldl_max_ge_of_mem` from `CmdHasTypeAGen/Core.lean` at `f := String.length`. -/
theorem fallbackFreshLabel_not_mem (labels : List String) :
    fallbackFreshLabel labels ∉ labels := by
  intro hmem
  have hlen : (fallbackFreshLabel labels).length =
      (labels.foldl (fun acc l => max acc l.length) 0) + 1 := by
    simp [fallbackFreshLabel, String.length_ofList, List.length_replicate]
  have hle := foldl_max_ge_of_mem String.length labels (fallbackFreshLabel labels) hmem 0
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
theorem filter_needsInit_eq_missingIn (env : GenStmtSoundEnv octx tvars pctx)
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

/-- Every `genCallStmt` result extends the variable scope by its (inline) `init`
    chain, and that extension preserves functionality: the declared names are
    pairwise distinct (a sublist of the guard's `Nodup` key list) and each is fresh
    for `ctx` (that is what `needsInit` selected them for), so
    `insertAllCtx_functional` applies. The empty-`procs`/guard-false branches are
    the empty generator, so there is nothing to prove. -/
theorem genCallStmt_outCtx {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support
      (genCallStmt (G := SetGen.Set) octx tvars immutableVars procs C ctx d pctx)) :
    Map.Functional r.outCtx := by
  cases procs with
  | nil => simp only [genCallStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff, mem_support_elements_iff] at hr
    obtain ⟨s, hs, hr⟩ := hr
    -- Peel the type-instantiation (`σvals`) sampling `mapM`.
    obtain ⟨σvals, hσvals, hr⟩ := hr
    split at hr
    · rename_i hcond
      obtain ⟨_, hNodup⟩ := hcond
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, rfl⟩ := hr
      -- Fuse the recipe's two init-lists into one filter over `Mσ ++ T`.
      rw [filter_needsInit_append]
      refine insertAllCtx_functional _ ctx hFun ?_ ?_
      · -- keys of a `filter` of a `Nodup`-keyed list are `Nodup`
        refine List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) ?_
        rw [← ListMap.keys_eq_map_fst]; exact hNodup
      · -- every selected name passed `needsInit`, i.e. is absent from `ctx`
        intro p hp
        have := (List.mem_filter.mp hp).2
        simpa [needsInit, VarCtx.isFresh, VarCtx.find?, Option.isNone_iff_eq_none] using this
    · simp only [SetGen.support, SetGen.bot_mem_iff] at hr

/-- Soundness of `genCallStmt` (at any depth `d`). Every emitted call *group* — the
    missing-name `init`s followed by the call, spliced inline — is a well-typed
    statement **list**: the callee's signature is read off `hProcs`, the drawn
    by-value inputs are typed via `env.exprSound`, and the sequence is assembled by
    `call_mixed_body_sound`. Its output scope is the `insertAllCtx`-extended `ctx`,
    which `toTCtx_insertAllCtx` identifies with the `insertAll`-extended `Γ` the
    lemma produces; when nothing was missing the chain is empty and this degenerates
    to the bare call at the unchanged scope. Because no block is emitted, the
    judgment holds at *every* enclosing-label set `labels`. The empty-`procs` and
    guard-false branches are the empty generator, so there is nothing to prove
    there. -/
theorem genCallStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (procs : ProcSigCtx) (hProcs : ProcSigCorresponds procs P)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)
    -- The inline `init` chain a call emits stores the callee's σ-instantiated written-to
    -- types, and upstream's `init` rules require the stored monotype to be well-kinded
    -- in `C`. `WellKindedOk` is exactly what that needs.
    (hWK : WellKindedOk octx procs C ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCallStmt (G := SetGen.Set) octx tvars immutableVars procs C ctx d pctx)) :
    StatementsHasTypeA P C (env.toTCtx ctx) labels r.stmts r.outC (env.toTCtx r.outCtx) := by
  cases procs with
  | nil => simp only [genCallStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff] at hr
    obtain ⟨s, hs, hr⟩ := hr
    rw [mem_support_elements_iff] at hs
    -- Peel the type-instantiation sampling; name the chosen instantiation `σ`.
    obtain ⟨σvals, hσvals, hr⟩ := hr
    obtain ⟨σ, hσ⟩ : ∃ σ, s.typeArgs.zip σvals = σ := ⟨_, rfl⟩
    -- Name the instantiated signature blocks the generator uses.
    obtain ⟨Mσ, hMσ⟩ : ∃ Mσ, StrataGenerators.Stmt.substSig σ s.M = Mσ := ⟨_, rfl⟩
    obtain ⟨Iσ, hIσ⟩ : ∃ Iσ, StrataGenerators.Stmt.substSig σ s.I = Iσ := ⟨_, rfl⟩
    obtain ⟨Oσ, hOσ⟩ : ∃ Oσ, StrataGenerators.Stmt.substSig σ s.O = Oσ := ⟨_, rfl⟩
    simp only [hσ, hMσ, hIσ, hOσ] at hr
    -- Split on the usability/Nodup guard.
    split at hr
    · rename_i hcond
      obtain ⟨hMusable, hNodup⟩ := hcond
      -- Name the out targets the generator picked for itself, and record the two
      -- facts the call-soundness lemmas need: usability (free — a new name is
      -- always fresh) and positional type alignment with the *instantiated* `Oσ`.
      obtain ⟨T, hT⟩ : ∃ T, outTargets immutableVars ctx Oσ = T := ⟨_, rfl⟩
      have hallusable : (List.append Mσ T).all (usableName immutableVars ctx) = true := by
        rw [← hT]; exact all_usableName_append immutableVars ctx Mσ Oσ hMusable
      have hTVals : T.values = Oσ.values := by
        rw [← hT]; exact outTargets_values immutableVars ctx Oσ
      rw [hT] at hNodup hr
      simp only [mem_support_bind_iff] at hr
      obtain ⟨exprs, hexprs, hr⟩ := hr
      -- Callee signature facts from the correspondence.
      obtain ⟨proc, hfind, _htyargs, hInputs, hOutputs, hIdisjOut⟩ := hProcs s hs
      -- The drawn inputs are pointwise reachable, at the *instantiated* input types.
      have hF₂ := (mem_support_mapM_iff
        (fun τ => genLExpr (G := SetGen.Set) ctx.toFVarCtx octx pctx tvars [] d τ) Iσ.values exprs).mp hexprs
      have hExLen : exprs.length = s.I.length := by
        rw [hF₂.length_eq, ← hIσ, lm_values_length, StrataGenerators.Stmt.substSig_length]
      -- `hExTy` at the instantiated input types `subst [σ] (s.I.values[i])`.
      have hExTy : ∀ i (hi : i < exprs.length) (hj : i < s.I.values.length),
          LExpr.HasTypeA [] (exprs[i]'hi) (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (s.I.values[i]'hj)) := by
        intro i hi hj
        have hjσ : i < Iσ.values.length := by
          rw [← hIσ, lm_values_length, StrataGenerators.Stmt.substSig_length, ← lm_values_length]
          exact hj
        obtain ⟨τ, hτ, hmem⟩ := hF₂.getElem?_some (i := i) (List.getElem?_eq_getElem hi)
        rw [List.getElem?_eq_getElem hjσ] at hτ
        have hτeq : τ = Iσ.values[i]'hjσ := (Option.some.inj hτ).symm
        subst hτeq
        have hbind := env.exprSound d ctx (Iσ.values[i]'hjσ) (exprs[i]'hi) hmem
        -- `Iσ.values[i] = subst [σ] (s.I.values[i])` (as a value equation, so the
        -- index proof `hjσ` is untouched).
        have hval : Iσ.values[i]'hjσ = LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (s.I.values[i]'hj) := by
          have hjσ' : i < (StrataGenerators.Stmt.substSig σ s.I).values.length := by rw [hIσ]; exact hjσ
          rw [← StrataGenerators.Stmt.substSig_values_getElem σ s.I i hjσ' hj]
          congr 1 <;> rw [hIσ]
        rwa [hval] at hbind
      -- Each required name (in the instantiated write-list `Mσ ++ T`) is *either*
      -- already bound at its recorded type (reuse) *or* absent (init) — the
      -- generator's `usable` guard, transported across `VarCtxCorresponds`.
      have hReuse : ∀ p ∈ (Mσ ++ T).toList,
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
      -- Every type the init chain stores is well-kinded in `C`: the sampled `σ` values
      -- come from the generable set (or are `bool`), so they are `SimpleType`s, and
      -- `substSig` preserves that.
      have hσSimple : ∀ t ∈ σ.map Prod.snd, SimpleType t := by
        intro t ht
        -- A value of `σ = s.typeArgs.zip σvals` is one of the sampled `σvals` …
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hσ ▸ ht)
        have hqσ : q.2 ∈ σvals := (List.of_mem_zip hq).2
        -- … and each of those is drawn from `generableTys` or is the `bool` fallback.
        obtain ⟨τ0, _, hmem⟩ :=
          forall₂_mem_left ((mem_support_mapM_iff _ s.typeArgs σvals).mp hσvals) q.2 hqσ
        split at hmem
        · exact hWK.generable q.2 (by rwa [mem_support_elements_iff] at hmem)
        · rw [mem_support_pure_iff] at hmem; rw [hmem]; exact .bool
      have hwk : ∀ p ∈ (StrataGenerators.Stmt.substSig σ s.M ++ T).toList,
          C.WellKindedTy p.2 := by
        intro q hq
        refine simpleType_wellKindedTy hWK.arities ?_
        rcases List.mem_append.mp hq with hqM | hqT
        · exact substSig_values_simple σ s.M hσSimple
            (fun ty hty => hWK.sigs s hs ty (by
              rw [lm_values_append]; exact List.mem_append_left _ hty))
            q.2 (by rw [ListMap.values_eq_map_snd]; exact List.mem_map_of_mem hqM)
        · have : q.2 ∈ T.values := by
            rw [ListMap.values_eq_map_snd]; exact List.mem_map_of_mem hqT
          rw [hTVals, ← hOσ] at this
          exact substSig_values_simple σ s.O hσSimple
            (fun ty hty => hWK.sigs s hs ty (by
              rw [lm_values_append]; exact List.mem_append_right _ hty))
            q.2 this
      -- One uniform shape: the (possibly empty) init chain, then the call.
      simp only [mem_support_pure_iff] at hr
      obtain rfl := hr
      -- Move both the emitted chain and the output scope to the single `missingIn`
      -- filter over `env.toTCtx ctx` that `call_mixed_body_sound` speaks about:
      -- fuse the recipe's two per-block filters, then transport the syntactic
      -- freshness filter to the semantic one.
      show StatementsHasTypeA P C (env.toTCtx ctx) labels
        (initChain (Mσ.filter (needsInit ctx) ++ T.filter (needsInit ctx)) ++ _) C
        (env.toTCtx (insertAllCtx ctx (Mσ.filter (needsInit ctx) ++ T.filter (needsInit ctx))))
      -- The generator-side scope and the semantic one agree only up to `TContext.Equiv`
      -- (opaque hash-map scopes), so move the output along it.
      refine StatementsHasTypeA_out_equiv ?_
        (env.toTCtx_insertAllCtx (Mσ.filter (needsInit ctx) ++ T.filter (needsInit ctx)) ctx)
      rw [filter_needsInit_append, filter_needsInit_eq_missingIn env ctx]
      -- `call_mixed_body_sound` takes declared blocks + `σ`; `Mσ`/`Oσ` are the
      -- instantiated ones the generator used. Rewrite them back to `substSig σ …`.
      rw [← hMσ] at hNodup hReuse ⊢
      rw [← hOσ] at hTVals
      exact call_mixed_body_sound σ s.M s.I s.O T exprs hfind hInputs hOutputs
        hExLen hTVals hExTy hIdisjOut hNodup hReuse hwk
    · simp only [SetGen.support, SetGen.bot_mem_iff] at hr

-- ── Procedure-call completeness (forward membership) ──────────────────────

/-- **Forward membership for `genCallStmt` (Part 2 of call completeness).** Given a
    callee `s` in the procedure context, whose in-out block is usable and whose
    combined write-key list is `Nodup` (the generator's own guard), and by-value
    inputs `exprs` each reachable by `genLExpr` at the declared input type, the
    generator's own recipe output — the missing-name `init` chain followed by the
    assembled call — is in `genCallStmt`'s support.

    This is the completeness analogue of `genCallStmt_sound`: it runs the
    `genCallStmt` `do`-block *forward* (`elements` membership of `s`, the
    type-instantiation sampling, the guard branch, `mapM` membership of `exprs`,
    `pure`), rather than inverting it. The chosen instantiation is `σ := s.typeArgs.zip σvals`
    for a sampled `σvals` (`hσvals` places it in the sampling step's support), and
    the emitted group/output scope are stated over the instantiated blocks
    `substSig σ s.M` / `substSig σ s.O`, with `T := outTargets immutableVars ctx (substSig σ s.O)`.
    A monomorphic callee (`s.typeArgs = []`) forces `σvals = []`, `σ = []`, and
    `substSig [] = id`, recovering the previous statement. -/
theorem genCallStmt_mem_complete (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)
    (s : ProcSig) (hs : s ∈ procs)
    (σvals : List LMonoTy)
    (hσvals : σvals ∈ SetGen.support
      (s.typeArgs.mapM (fun _ =>
        if hg : (generableTypesFromCtx ctx.values [] octx).length > 0 then
          elements (generableTypesFromCtx ctx.values [] octx)
            (by apply List.ne_nil_of_length_pos; assumption)
        else pure (.bool : LMonoTy)) : SetGen.Set (List LMonoTy)))
    (exprs : List Expression.Expr)
    (hMusable : (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).all
      (usableName immutableVars ctx) = true)
    (hNodup : (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M
      ++ outTargets immutableVars ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)).keys.Nodup)
    (hexprs : List.Forall₂
      (fun e τ => e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] d τ))
      exprs (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.I).values) :
    (⟨StrataGenerators.Stmt.initChain
        ((StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).filter (needsInit ctx)
          ++ (outTargets immutableVars ctx
                (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)).filter (needsInit ctx))
        ++ [Statement.call s.pname
              (StrataGenerators.Stmt.mkArgs s.M
                (outTargets immutableVars ctx
                  (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)) exprs) default],
      C, StrataGenerators.Stmt.insertAllCtx ctx
        ((StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).filter (needsInit ctx)
          ++ (outTargets immutableVars ctx
                (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)).filter (needsInit ctx))⟩
      : GenStmtResult) ∈
      SetGen.support (genCallStmt (G := SetGen.Set) octx tvars immutableVars procs C ctx d) := by
  -- `procs` is non-empty (it contains `s`), so the `p₀ :: ps` branch fires.
  cases procs with
  | nil => exact absurd hs (by simp)
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff]
    refine ⟨s, (mem_support_elements_iff (by simp)).mpr hs, ?_⟩
    -- Exhibit the sampled `σvals` for the type-instantiation `mapM`.
    refine ⟨σvals, hσvals, ?_⟩
    -- Take the guard-true branch (`hMusable` and `hNodup` are exactly its condition).
    rw [if_pos ⟨hMusable, hNodup⟩]
    simp only [mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨exprs, (mem_support_mapM_iff _ _ exprs).mpr hexprs, rfl⟩

-- ── Guard / measure / invariant soundness helpers ────────────────────────

/-- Any `.det`-guard produced by `genCondOrNondet` (at depth `d`) carries a
    boolean expression. -/
theorem genCondOrNondet_det_sound (env : GenStmtSoundEnv octx tvars pctx) (d : Nat) (ctx : VarCtx)
    (cond : ExprOrNondet Expression)
    (hc : cond ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) octx tvars ctx d pctx))
    (g : Expression.Expr) (hg : cond = .det g) :
    HasTypeA' [] g .bool := by
  rw [genCondOrNondet, mem_support_frequency_iff] at hc
  obtain ⟨w, gen, hmem, _, hc⟩ := hc
  simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · -- nondet branch: `cond = .nondet`, contradicting `cond = .det g`
    rw [mem_support_pure_iff] at hc
    exact absurd (hg ▸ hc) (by simp)
  · -- det branch: `cond = .det e` for a generated boolean `e`
    rw [mem_support_map_iff] at hc
    obtain ⟨e, he, rfl⟩ := hc
    have : e = g := by simpa using hg
    subst this
    exact env.exprSound d ctx .bool e he

/-- Any `some`-measure produced by `genOptMeasure` (at depth `d`) carries an
    integer expression. -/
theorem genOptMeasure_some_sound (env : GenStmtSoundEnv octx tvars pctx) (d : Nat) (ctx : VarCtx)
    (m? : Option Expression.Expr)
    (hm : m? ∈ SetGen.support (genOptMeasure (G := SetGen.Set) octx tvars ctx d pctx))
    (m : Expression.Expr) (hmeq : m? = some m) :
    HasTypeA' [] m .int := by
  simp only [genOptMeasure,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)] at hm
  rcases hm with hnone | ⟨e, he, hm⟩
  · exact absurd (hmeq ▸ hnone) (by simp)
  · subst hmeq
    have : e = m := (Option.some.inj hm).symm
    subst this
    exact env.exprSound d ctx .int e he

/-- Every invariant produced by `genInvariants` (at depth `d`) carries a boolean
    expression. -/
theorem genInvariants_sound (env : GenStmtSoundEnv octx tvars pctx) (d : Nat) (ctx : VarCtx)
    (invs : List (String × Expression.Expr))
    (hinv : invs ∈ SetGen.support (genInvariants (G := SetGen.Set) octx tvars ctx d pctx))
    (p : String × Expression.Expr) (hp : p ∈ invs) :
    HasTypeA' [] p.2 .bool := by
  simp only [genInvariants, mem_support_listOfMaxLength_iff] at hinv
  have hp_supp := hinv.2 p hp
  simp only [genInvariant, mem_support_bind_iff, mem_support_pure_iff] at hp_supp
  obtain ⟨l, _hl, e, he, rfl⟩ := hp_supp
  exact env.exprSound d ctx .bool e he

-- ── Mutual soundness of genStmt / genStmtChain ───────────────────────────────

/-- `genStmt` preserves *functionality* of the context. The nesting
    constructors (`block`, `ite`, `loop`) are lexically scoped — their output
    scope is the *input* `ctx` (the body's threaded scope is discarded) — and the
    non-`cmd` leaves also leave `ctx` unchanged, so the only case that can grow
    the context is `cmd`, handled by `genCmd_outCtx_functional`. No recursion into
    the body is needed, so this stands outside the soundness `mutual` block. -/
theorem genStmt_outCtx_functional
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support
      (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx pctx n)) :
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
      exact genCmd_outCtx_functional octx pctx tvars immutableVars ctx 0 hFun rc hrc
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
    · -- call: the inline `init` chain genuinely extends the scope
      exact genCallStmt_outCtx hFun r hr
  | succ size =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · -- cmd
      simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨rc, hrc, rfl⟩ := hr
      exact genCmd_outCtx_functional octx pctx tvars immutableVars ctx (size + 1) hFun rc hrc
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
    · -- call: the inline `init` chain genuinely extends the scope
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
    well-typed w.r.t. `StatementHasTypeA` (for any program `P`), with the generator's
    output ambient context `r.outC` and output scope `env.toTCtx r.outCtx` being
    exactly the output contexts of the typing relation.

    Proof by well-founded recursion on the `size` budget `n`. Leaf constructors
    (`cmd`, `exit`, `funcDecl`, `typeDecl`) are discharged by the per-constructor
    lemmas above (at the current depth); nesting constructors (`block`, `ite`,
    `loop`) invert the corresponding `do`-block and appeal to `genStmtChain_sound` at
    the smaller `size`. -/
theorem genStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx)
    (hWK : WellKindedOk octx procs C ctx)
    (hWKpres : WellKindedPreserved octx tvars immutableVars procs pctx)
    (n : Nat) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx pctx n)) :
    StatementsHasTypeA P C (env.toTCtx ctx) labels r.stmts r.outC (env.toTCtx r.outCtx) := by
  cases n with
  | zero =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact genCmdStmt_sound P env C hWK.arities ctx 0 hFun r hr
    · exact genExitStmt_sound P env C ctx r hr
    · exact genFuncDeclStmt_sound P env C hWK.arities ctx 0 r hr
    · exact genTypeDeclStmt_sound P env C ctx 0 r hr
    · exact genCallStmt_sound P env procs hProcs C ctx 0 hWK r hr
  | succ size =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact genCmdStmt_sound P env C hWK.arities ctx (size + 1) hFun r hr
    · exact genExitStmt_sound P env C ctx r hr
    · exact genFuncDeclStmt_sound P env C hWK.arities ctx (size + 1) r hr
    · exact genTypeDeclStmt_sound P env C ctx (size + 1) r hr
    · exact genCallStmt_sound P env procs hProcs C ctx (size + 1) hWK r hr
    · -- block
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨label, hlabel, ⟨⟨len, _⟩⟩, _hlenbd, triple, htriple, rfl⟩ := hr
      have hfresh := genFreshLabel_not_mem labels label hlabel
      have ih := genStmtChain_sound P env immutableVars procs hProcs (label :: labels) C ctx hWK hWKpres size len hFun triple htriple
      exact StatementsHasTypeA_singleton
        (StatementHasType'.block C (env.toTCtx ctx) triple.2.1 (env.toTCtx triple.2.2)
          labels label triple.1 default _ hfresh ih
          (tctxEquivRefl _))
    · -- ite_det
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨cond, hcond, ⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmtChain_sound P env immutableVars procs hProcs labels C ctx hWK hWKpres size tlen hFun tt htt
      have ihe := genStmtChain_sound P env immutableVars procs hProcs labels C ctx hWK hWKpres size elen hFun et het
      exact StatementsHasTypeA_singleton
        (StatementHasType'.ite_det C (env.toTCtx ctx) tt.2.1 (env.toTCtx tt.2.2)
          et.2.1 (env.toTCtx et.2.2) labels cond tt.1 et.1 default _
          (env.exprSound (size + 1) ctx .bool cond hcond) iht ihe
          (tctxEquivRefl _))
    · -- ite_nondet
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmtChain_sound P env immutableVars procs hProcs labels C ctx hWK hWKpres size tlen hFun tt htt
      have ihe := genStmtChain_sound P env immutableVars procs hProcs labels C ctx hWK hWKpres size elen hFun et het
      exact StatementsHasTypeA_singleton
        (StatementHasType'.ite_nondet C (env.toTCtx ctx) tt.2.1 (env.toTCtx tt.2.2)
          et.2.1 (env.toTCtx et.2.2) labels tt.1 et.1 default _ iht ihe
          (tctxEquivRefl _))
    · -- loop
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨guard, hguard, measure, hmeasure, invs, hinvs, ⟨⟨blen, _⟩⟩, _, body, hbody, rfl⟩ := hr
      have ih := genStmtChain_sound P env immutableVars procs hProcs labels C ctx hWK hWKpres size blen hFun body hbody
      refine StatementsHasTypeA_singleton
        (StatementHasType'.loop C (env.toTCtx ctx) body.2.1 (env.toTCtx body.2.2)
          labels guard measure invs body.1 default _ ?_ ?_ ?_ ih
          (tctxEquivRefl _))
      · intro g hg
        exact genCondOrNondet_det_sound env (size + 1) ctx guard hguard g hg
      · intro m hm
        exact genOptMeasure_some_sound env (size + 1) ctx measure hmeasure m hm
      · intro p hp
        exact genInvariants_sound env (size + 1) ctx invs hinvs p hp
termination_by (n, 0, 0)

/-- **Soundness of `genStmtChain`.** Every statement sequence in the generator's
    support satisfies the chained `StatementsHasTypeA` relation between the input
    contexts and the generator's threaded output contexts.

    Proof by well-founded recursion on the remaining length `len` (with the
    `size` fixed): the `nil` case is trivial, and the `cons` case types the head
    via `genStmt_sound` and the tail via the induction hypothesis. -/
theorem genStmtChain_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx)
    (hWK : WellKindedOk octx procs C ctx)
    (hWKpres : WellKindedPreserved octx tvars immutableVars procs pctx)
    (size len : Nat) (hFun : Map.Functional ctx)
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx pctx size len)) :
    StatementsHasTypeA P C (env.toTCtx ctx) labels result.1 result.2.1 (env.toTCtx result.2.2) := by
  cases len with
  | zero =>
    simp only [genStmtChain, mem_support_pure_iff] at hr
    subst hr
    exact StatementsHasType'.nil C (env.toTCtx ctx) labels _ (tctxEquivRefl _)
  | succ len =>
    simp only [genStmtChain, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨rhead, hhead, rtail, htail, rfl⟩ := hr
    have hh := genStmt_sound P env immutableVars procs hProcs labels C ctx hWK hWKpres size hFun rhead hhead
    have hFun' : Map.Functional rhead.outCtx :=
      genStmt_outCtx_functional octx pctx tvars immutableVars procs labels C ctx size hFun
        rhead hhead
    have ht := genStmtChain_sound P env immutableVars procs hProcs labels rhead.outC rhead.outCtx
      (hWKpres labels C ctx size rhead hhead hWK) hWKpres size len hFun' rtail htail
    exact StatementsHasTypeA_append hh ht
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
    (hr : r ∈ SetGen.support (genCmdStmt (G := SetGen.Set) octx tvars immutableVars C ctx n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨4, _, .head _, by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨4, _, .head _, by omega, hr⟩

/-- A `genExitStmt` result is reachable by `genStmt … n` at *every* size `n`. -/
theorem genExitStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
  -- With `labels = []` the `exit` branch is weighted 0, but there `genExitStmt`
  -- is `default` (support `∅`), so `hr` is impossible; with `labels ≠ []` the
  -- branch weight reduces to `1`.
  cases labels with
  | nil => simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons hd tl =>
    cases n with
    | zero =>
      rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
      exact ⟨_, _, .tail _ (.head _), by simp, hr⟩
    | succ size =>
      rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
      exact ⟨_, _, .tail _ (.head _), by simp, hr⟩

/-- A `genFuncDeclStmt` result (at depth `n`) is reachable by `genStmt … n`. -/
theorem genFuncDeclStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genFuncDeclStmt (G := SetGen.Set) octx C ctx n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.head _)), by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.head _)), by omega, hr⟩

/-- A `genTypeDeclStmt` result (at depth `n`) is reachable by `genStmt … n`. -/
theorem genTypeDeclStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩

/-- A `genCallStmt` result (at depth `n`) is reachable by `genStmt … n`. The call
    branch sits at frequency index 4 in both the size-0 and size+1 lists. -/
theorem genCallStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCallStmt (G := SetGen.Set) octx tvars immutableVars procs C ctx n)) :
    r ∈ SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
  -- With `procs = []` the `call` branch is weighted 0, but there `genCallStmt`
  -- is `default` (support `∅`), so `hr` is impossible; with `procs ≠ []` the
  -- branch weight reduces to `1`.
  cases procs with
  | nil => simp only [genCallStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons hd tl =>
    cases n with
    | zero =>
      rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
      exact ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by simp, hr⟩
    | succ size =>
      rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
      exact ⟨_, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by simp, hr⟩

/-- A `block` statement is reachable by `genStmt … (size+1)` when its body (of some
    length `len ≤ size+1`) is reachable by `genStmtChain … size` under the extended
    label scope `label :: labels`. -/
theorem block_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (label : String) (body : List Statement) (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (len : Nat) (hlen : len ≤ size + 1)
    (hbody : (body, C_body, Γ_body) ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs (label :: labels) C ctx [] size len))
    (hlabel : label ∈ SetGen.support (genFreshLabel (G := SetGen.Set) labels)) :
    (⟨[Stmt.block label body default], C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] (size + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨label, hlabel, ⟨⟨len, Nat.zero_le _, hlen⟩⟩, ⟨Nat.zero_le _, hlen⟩,
    (body, C_body, Γ_body), hbody, rfl⟩

/-- An `ite (.det cond)` statement is reachable by `genStmt … (size+1)` when the
    condition is a reachable boolean (at depth `size+1`) and both branches are
    reachable by `genStmtChain … size`. -/
theorem ite_det_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (cond : Expression.Expr) (thenb elseb : List Statement)
    (Ct : LContext CoreLParams) (Γt : VarCtx) (Ce : LContext CoreLParams) (Γe : VarCtx)
    (tlen elen : Nat) (htlen : tlen ≤ size + 1) (helen : elen ≤ size + 1)
    (hcond : cond ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] (size + 1) .bool))
    (hthen : (thenb, Ct, Γt) ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] size tlen))
    (helse : (elseb, Ce, Γe) ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] size elen)) :
    (⟨[Stmt.ite (.det cond) thenb elseb default], C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] (size + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨cond, hcond, ⟨⟨tlen, Nat.zero_le _, htlen⟩⟩, ⟨Nat.zero_le _, htlen⟩,
    ⟨⟨elen, Nat.zero_le _, helen⟩⟩, ⟨Nat.zero_le _, helen⟩,
    (thenb, Ct, Γt), hthen, (elseb, Ce, Γe), helse, rfl⟩

/-- An `ite .nondet` statement is reachable by `genStmt … (size+1)` when both
    branches are reachable by `genStmtChain … size`. -/
theorem ite_nondet_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (thenb elseb : List Statement)
    (Ct : LContext CoreLParams) (Γt : VarCtx) (Ce : LContext CoreLParams) (Γe : VarCtx)
    (tlen elen : Nat) (htlen : tlen ≤ size + 1) (helen : elen ≤ size + 1)
    (hthen : (thenb, Ct, Γt) ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] size tlen))
    (helse : (elseb, Ce, Γe) ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] size elen)) :
    (⟨[Stmt.ite .nondet thenb elseb default], C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] (size + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
  refine ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨⟨⟨tlen, Nat.zero_le _, htlen⟩⟩, ⟨Nat.zero_le _, htlen⟩,
    ⟨⟨elen, Nat.zero_le _, helen⟩⟩, ⟨Nat.zero_le _, helen⟩,
    (thenb, Ct, Γt), hthen, (elseb, Ce, Γe), helse, rfl⟩

/-- A `loop` statement is reachable by `genStmt … (size+1)` when its guard, measure,
    invariants (all at depth `size+1`), and body (by `genStmtChain … size`) are all
    reachable. -/
theorem loop_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (body : List Statement)
    (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (blen : Nat) (hblen : blen ≤ size + 1)
    (hguard : guard ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) octx tvars ctx (size + 1)))
    (hmeasure : measure ∈ SetGen.support (genOptMeasure (G := SetGen.Set) octx tvars ctx (size + 1)))
    (hinvs : invs ∈ SetGen.support (genInvariants (G := SetGen.Set) octx tvars ctx (size + 1)))
    (hbody : (body, C_body, Γ_body) ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] size blen)) :
    (⟨[Stmt.loop guard measure invs body default], C, ctx⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] (size + 1)) := by
  rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
  refine ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨guard, hguard, measure, hmeasure, invs, hinvs,
    ⟨⟨blen, Nat.zero_le _, hblen⟩⟩, ⟨Nat.zero_le _, hblen⟩,
    (body, C_body, Γ_body), hbody, rfl⟩

-- ── genStmtChain membership: cons / nil ──────────────────────────────────────

/-- The empty statement list is in `genStmtChain`'s support at length `0`. -/
theorem genStmtChain_nil_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat) :
    ((([] : List Statement)), C, ctx) ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] size 0) := by
  rw [genStmtChain]; exact mem_support_pure_iff.mpr rfl

/-- If the head statement `r` is reachable by `genStmt` (at `size`) and the tail is
    reachable by `genStmtChain` from the head's output contexts (at the same `size`,
    length `len`), then the whole `cons` is reachable at length `len+1`. -/
theorem genStmtChain_cons_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size len : Nat)
    (r : GenStmtResult) (rest : List Statement) (C'' : LContext CoreLParams) (Γ'' : VarCtx)
    (hhead : r ∈ SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] size))
    (htail : (rest, C'', Γ'') ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels r.outC r.outCtx [] size len)) :
    (r.stmts ++ rest, C'', Γ'') ∈
      SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] size (len + 1)) := by
  rw [genStmtChain]
  simp only [mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨r, hhead, (rest, C'', Γ''), htail, rfl⟩

-- ── Completeness helper lemmas ────────────────────────────────────────────
-- Straightforward `pick`/`map`/`listOfMaxLength` support-inversion lemmas, one
-- per guard/measure/invariant/type-constructor sub-generator, mirroring
-- `genOptExpr_complete` in `FunctionHasTypeAGen.lean`. These convert typed
-- side-conditions into raw support-membership facts consumed by the spec-indexed
-- completeness proof (`StmtHasTypeAGenComplete.lean`). Each is stated at an arbitrary depth.

/-- Completeness of `genCondOrNondet`. `.nondet` is always reachable; `.det g` is
    reachable when `g` is reachable by `genLExpr` at type `bool`. -/
theorem genCondOrNondet_complete (depth : Nat) (ctx : VarCtx) (cond : ExprOrNondet Expression)
    (hcond : ∀ g, cond = .det g →
      g ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] depth .bool)) :
    cond ∈ SetGen.support (genCondOrNondet (G := SetGen.Set) octx tvars ctx depth) := by
  rw [genCondOrNondet, mem_support_frequency_iff]
  cases cond with
  | nondet =>
    -- weight-1 `.nondet` branch
    exact ⟨1, _, List.mem_cons_self, by omega, mem_support_pure_iff.mpr rfl⟩
  | det g =>
    -- weight-4 `.det` branch
    exact ⟨4, _, List.mem_cons_of_mem _ List.mem_cons_self, by omega,
      mem_support_map_iff.mpr ⟨g, hcond g rfl, rfl⟩⟩

/-- Completeness of `genOptMeasure`. `none` is always reachable; `some m` is
    reachable when `m` is reachable by `genLExpr` at type `int`. -/
theorem genOptMeasure_complete (depth : Nat) (ctx : VarCtx) (measure : Option Expression.Expr)
    (hmeasure : ∀ m, measure = some m →
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] depth .int)) :
    measure ∈ SetGen.support (genOptMeasure (G := SetGen.Set) octx tvars ctx depth) := by
  simp only [genOptMeasure,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)]
  cases measure with
  | none => exact Or.inl rfl
  | some m => exact Or.inr ⟨m, hmeasure m rfl, rfl⟩

/-- Completeness of `genInvariant`. A `(label, e)` pair is reachable when the
    label is a reachable identifier (via `genIdentName`, so non-empty and
    non-keyword) and `e` is a reachable boolean. -/
theorem genInvariant_complete (depth : Nat) (ctx : VarCtx) (p : String × Expression.Expr)
    (hlabel : p.1 ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hexpr : p.2 ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] depth .bool)) :
    p ∈ SetGen.support (genInvariant (G := SetGen.Set) octx tvars ctx depth) := by
  simp only [genInvariant, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨p.1, hlabel, p.2, hexpr, rfl⟩

/-- Completeness of `genInvariants`. A list of invariants is reachable when it is
    no longer than `depth` and each element is reachable by `genInvariant`. -/
theorem genInvariants_complete (depth : Nat) (ctx : VarCtx) (invs : List (String × Expression.Expr))
    (hlen : invs.length ≤ depth)
    (hinvs : ∀ p ∈ invs, p.1 ∈ SetGen.support (genIdentName (G := SetGen.Set)) ∧
      p.2 ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] depth .bool)) :
    invs ∈ SetGen.support (genInvariants (G := SetGen.Set) octx tvars ctx depth) := by
  simp only [genInvariants, mem_support_listOfMaxLength_iff]
  refine ⟨hlen, fun p hp => ?_⟩
  exact genInvariant_complete depth ctx p (hinvs p hp).1 (hinvs p hp).2

/-- Completeness of `genTypeConstructor`. A type constructor is reachable when its
    name and each parameter name are reachable identifiers (via `genIdentName`, so
    non-empty and non-keyword) and its parameter list is no longer than `depth`.
    The `bound` field carries no side-condition: the generator samples over both
    `Boundedness` values, so either is reachable. -/
theorem genTypeConstructor_complete (depth : Nat) (tc : TypeConstructor)
    (hname : tc.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hlen : tc.params.length ≤ depth)
    (hparams : ∀ s ∈ tc.params, s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    tc ∈ SetGen.support (genTypeConstructor (G := SetGen.Set) depth) := by
  simp only [genTypeConstructor, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_listOfMaxLength_iff]
  refine ⟨tc.name, hname, tc.params, ⟨hlen, hparams⟩, tc.bound, ?_, ?_⟩
  · -- both `Boundedness` values are in the sampled list
    rw [mem_support_elements_iff]; cases tc.bound <;> simp
  · obtain ⟨bound, name, params⟩ := tc; rfl

/-- `genTypeConstructor_complete`, and `mem_support_genIdentName_iff` discharges both of its
    hypotheses on name reachability from syntax. Only decidable conditions remain: the name of the
    constructor and each parameter name is a bare Core identifier and is not a reserved
    keyword. -/
theorem genTypeConstructor_complete_of_syntactic (depth : Nat) (tc : TypeConstructor)
    (hnameSyn : StrataGenerators.Function.IsGenIdentName tc.name)
    (hnameKw : isReservedKeyword tc.name = false)
    (hlen : tc.params.length ≤ depth)
    (hparams : ∀ s ∈ tc.params,
      StrataGenerators.Function.IsGenIdentName s ∧ isReservedKeyword s = false) :
    tc ∈ SetGen.support (genTypeConstructor (G := SetGen.Set) depth) :=
  genTypeConstructor_complete depth tc
    (StrataGenerators.Function.mem_support_genIdentName_of_syntactic hnameSyn hnameKw) hlen
    (fun s hs => StrataGenerators.Function.mem_support_genIdentName_of_syntactic
      (hparams s hs).1 (hparams s hs).2)

end StrataGenerators.Stmt
