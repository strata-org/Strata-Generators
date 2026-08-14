import StrataGenerators.HasTypeAGen
import StrataGenerators.CmdHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen

/-!
# Discharging the freshness hypothesis of `genCmd_sound`

`genCmd_sound` (in `CmdHasTypeAGen.lean`) takes `FreshNamesDisjointFromExprs` as a
hypothesis. The command generators now derive their free-variable context from the
*current* scope `ctx` (via `VarCtx.toFVarCtx`), so this predicate holds *for every*
`ctx`: `genLExpr ctx.toFVarCtx` draws free variables only from `ctx.toFVarCtx`,
whose names are exactly `ctx`'s (`VarCtx.toFVarCtx_names`), while a fresh `init`
name — produced by `genFreshName ctx` — is by construction absent from `ctx`. So a
fresh name can never occur in a generated expression.

This file discharges that hypothesis (`freshNamesDisjointFromExprs_toFVarCtx`) and
packages the hypothesis-free entry points `genCmd_sound_nil` / `genCmds_sound_nil`
(the `_nil` suffix is retained for continuity; it now refers to the *empty starting
scope*, not an empty fvar context).

The old `fctx = []` special case (`freshNamesDisjointFromExprs_nil`) is retained as
a corollary: `[].toFVarCtx = []` and its names are empty, so a fresh name trivially
avoids the (empty) free variables.
-/

/-- Fresh names never collide with the free variables of expressions generated at
    `ctx.toFVarCtx` — the free-variable context the command generators derive from
    the current scope. Every generated free variable is a name of `ctx.toFVarCtx`,
    i.e. a name of `ctx` (`VarCtx.toFVarCtx_names`); a fresh `init` name is absent
    from `ctx` (`genFreshName_produces_fresh`); hence disjoint. This discharges the
    `FreshNamesDisjointFromExprs` hypothesis of `genCmd_sound` for *every* `ctx`. -/
theorem freshNamesDisjointFromExprs_toFVarCtx (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) :
    FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx depth pctx := by
  intro name hname τ e he hmem
  -- The generated expression's free vars are ⊆ the (identifier) keys of `ctx.toFVarCtx`.
  have hsub := Lambda.LExpr.genLExpr_fvars_subset ctx.toFVarCtx octx pctx tvars [] depth τ e he
  have hmem' : (⟨name, ()⟩ : Identifier Unit)
      ∈ ctx.toFVarCtx.map (fun p => (⟨p.1, ()⟩ : Identifier Unit)) := by
    have : (⟨name, ()⟩ : Identifier Unit) ∈ LExpr.getVars e := by
      simpa only [HasVarsPure.getVars] using hmem
    exact hsub this
  -- Unfold `ctx.toFVarCtx = ctx.map (fun q => (q.1.name, q.2))` and extract the
  -- originating scope entry `q ∈ ctx`, whose key is exactly `⟨name, ()⟩`.
  simp only [VarCtx.toFVarCtx, List.map_map, List.mem_map, Function.comp_def] at hmem'
  obtain ⟨q, hq, hqeq⟩ := hmem'
  -- `⟨q.1.name, ()⟩ = ⟨name, ()⟩` and metadata is `Unit`, so `q.1 = ⟨name, ()⟩`, i.e.
  -- `(⟨name, ()⟩, q.2) = q` is a member of `ctx`.
  have hqfst : q.1 = (⟨name, ()⟩ : Identifier Unit) := by
    have hn : q.1.name = name := by injection hqeq
    -- metadata is `Unit`, so an `Identifier Unit` is determined by its name.
    have : q.1 = ⟨q.1.name, ()⟩ := by cases q.1 with | mk n m => cases m; rfl
    rw [this, hn]
  have hmemCtx : List.Mem ((⟨name, ()⟩ : Identifier Unit), q.2) ctx := by
    have : q = ((⟨name, ()⟩ : Identifier Unit), q.2) := by rw [← hqfst]
    rwa [← this]
  -- But a fresh name is absent from `ctx`, contradiction.
  have hfresh := genFreshName_produces_fresh ctx name hname
  simp only [VarCtx.isFresh, VarCtx.find?, Option.isNone_iff_eq_none] at hfresh
  exact Map.not_mem_of_find?_none ctx ⟨name, ()⟩ hfresh q.2 hmemCtx

/-- Corollary at the empty fvar context (`[].toFVarCtx = []`): retained for callers
    that still speak of `fctx = []`. -/
theorem freshNamesDisjointFromExprs_nil (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) :
    FreshNamesDisjointFromExprs [] octx tvars ctx depth := by
  intro name _ τ e he
  have hnil : LExpr.getVars e = [] :=
    Lambda.LExpr.genLExpr_no_fvars octx [] tvars [] depth τ e he
  simp only [HasVarsPure.getVars, hnil, List.not_mem_nil, not_false_eq_true]

/-- Hypothesis-free soundness of `genCmd`: every result in the generator's support
    produces a well-typed command. The only remaining obligations are the genuine
    context-dependent ones — `hCorr` (the `VarCtx ↔ TContext` correspondence) and
    `hExprSound` (expression-level soundness, at the scope-derived free-var context).
    The freshness/disjointness hypothesis is discharged internally via
    `freshNamesDisjointFromExprs_toFVarCtx`. -/
theorem genCmd_sound_nil
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (hC : SimpleTyArities C)
    (hCorr : VarCtxCorresponds ctx Γ)
    (hFun : Map.Functional ctx)
    (hExprSound : GenLExprSound ctx.toFVarCtx octx tvars depth)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth)) :
    ∃ Γ', CmdHasTypeA C Γ r.cmd Γ' :=
  genCmd_sound octx tvars immutableVars ctx depth C Γ hC hCorr hFun hExprSound
    (freshNamesDisjointFromExprs_toFVarCtx octx tvars ctx depth) r hr

/-- A `GenCmdSoundEnv` built from the proven disjointness fact. The remaining
    fields — `toTCtx`, `corr`, `exprSound`, `toTCtx_insert` — are the genuine
    context-dependent obligations the caller supplies (`exprSound` at each scope's
    derived free-var context). -/
def genCmdSoundEnv_nil
    (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (C : LContext CoreLParams)
    (toTCtx : VarCtx → TContext Unit)
    (corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx))
    (exprSound : ∀ (ctx : VarCtx), GenLExprSound ctx.toFVarCtx octx tvars depth)
    (toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
      TContext.Equiv (T := CoreLParams) (toTCtx (ctx.insert x mty))
        { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }) :
    GenCmdSoundEnv octx tvars depth C where
  toTCtx := toTCtx
  corr := corr
  exprSound := exprSound
  freshDisjoint := fun ctx => freshNamesDisjointFromExprs_toFVarCtx octx tvars ctx depth
  toTCtx_insert := toTCtx_insert

/-- Hypothesis-free soundness of `genCmds` (command sequences): every generated
    sequence satisfies the chained `CmdsHasTypeA` relation. -/
theorem genCmds_sound_nil
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) (n : Nat)
    (C : LContext CoreLParams)
    (env : GenCmdSoundEnv octx tvars depth C)
    (hC : SimpleTyArities C)
    (hFun : Map.Functional ctx)
    (result : List (Cmd Expression) × VarCtx)
    (hr : result ∈ SetGen.support (genCmds (G := SetGen.Set) octx tvars immutableVars ctx depth n)) :
    CmdsHasTypeA C (env.toTCtx ctx) result.1 (env.toTCtx result.2) :=
  genCmds_sound octx tvars immutableVars ctx depth n C env hC hFun result hr
