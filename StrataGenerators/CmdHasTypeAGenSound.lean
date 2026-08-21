import StrataGenerators.HasTypeAGen
import StrataGenerators.CmdHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen

/-!
# The proof of the freshness hypothesis of `genCmd_sound`

`genCmd_sound` takes `FreshNamesDisjointFromExprs` as a hypothesis. The command generators
build their free-variable context from the *current* scope `ctx`, through
`VarCtx.toFVarCtx`. That predicate therefore holds for *each* `ctx`.
`genLExpr ctx.toFVarCtx` draws a free variable only from `ctx.toFVarCtx`, whose names are
the names of `ctx`, as `VarCtx.toFVarCtx_names` states. A fresh name for an `init` comes
from `genFreshName ctx`, and it is by construction absent from `ctx`. A fresh name can
therefore never occur in a generated expression.

This file proves that hypothesis in `freshNamesDisjointFromExprs_toFVarCtx`. It also gives
the entry points `genCmd_sound_nil` and `genCmds_sound_nil`, which need no such hypothesis.
The `_nil` in each name refers to the *empty scope at the start*, and not to an empty
free-variable context.

`freshNamesDisjointFromExprs_nil` is a corollary for the case `fctx = []`. There
`[].toFVarCtx` is `[]`, whose names are empty, so a fresh name avoids the free variables.
-/

/-- A fresh name never equals a free variable of an expression that the generator makes at
    `ctx.toFVarCtx`. That context is the free-variable context that the command generators build
    from the current scope. Each generated free variable is a name of `ctx.toFVarCtx`, and
    therefore a name of `ctx`, as `VarCtx.toFVarCtx_names` states. A fresh name for an `init` is
    absent from `ctx`, as `genFreshName_produces_fresh` states. The two sets are therefore
    disjoint. This theorem proves the `FreshNamesDisjointFromExprs` hypothesis of `genCmd_sound`
    for *each* `ctx`. -/
theorem freshNamesDisjointFromExprs_toFVarCtx (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) :
    FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx depth pctx := by
  intro name hname τ e he hmem
  -- The free variables of the generated expression are a subset of the identifier keys of
  -- `ctx.toFVarCtx`.
  have hsub := Lambda.LExpr.genLExpr_fvars_subset ctx.toFVarCtx octx pctx tvars [] depth τ e he
  have hmem' : (⟨name, ()⟩ : Identifier Unit)
      ∈ ctx.toFVarCtx.map (fun p => (⟨p.1, ()⟩ : Identifier Unit)) := by
    have : (⟨name, ()⟩ : Identifier Unit) ∈ LExpr.getVars e := by
      simpa only [HasFvars.getFvars] using hmem
    exact hsub this
  -- Unfold `ctx.toFVarCtx` to `ctx.map (fun q => (q.1.name, q.2))`, and take the scope entry `q`
  -- of `ctx` that gave the variable. The key of that entry is `⟨name, ()⟩`.
  simp only [VarCtx.toFVarCtx, List.map_map, List.mem_map, Function.comp_def] at hmem'
  obtain ⟨q, hq, hqeq⟩ := hmem'
  -- `⟨q.1.name, ()⟩` equals `⟨name, ()⟩`, and the metadata is `Unit`. Therefore
  -- `q.1 = ⟨name, ()⟩`, and `ctx` holds `(⟨name, ()⟩, q.2)`, which is `q`.
  have hqfst : q.1 = (⟨name, ()⟩ : Identifier Unit) := by
    have hn : q.1.name = name := by injection hqeq
    -- The metadata is `Unit`, so the name determines an `Identifier Unit`.
    have : q.1 = ⟨q.1.name, ()⟩ := by cases q.1 with | mk n m => cases m; rfl
    rw [this, hn]
  have hmemCtx : List.Mem ((⟨name, ()⟩ : Identifier Unit), q.2) ctx := by
    have : q = ((⟨name, ()⟩ : Identifier Unit), q.2) := by rw [← hqfst]
    rwa [← this]
  -- However, a fresh name is absent from `ctx`, and this is a contradiction.
  have hfresh := genFreshName_produces_fresh ctx name hname
  simp only [VarCtx.isFresh, VarCtx.find?, Option.isNone_iff_eq_none] at hfresh
  exact Map.not_mem_of_find?_none ctx ⟨name, ()⟩ hfresh q.2 hmemCtx

/-- The same claim at the empty free-variable context, where `[].toFVarCtx` is `[]`. This corollary
    serves a caller that speaks of `fctx = []`. -/
theorem freshNamesDisjointFromExprs_nil (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) :
    FreshNamesDisjointFromExprs [] octx tvars ctx depth := by
  intro name _ τ e he
  have hnil : LExpr.getVars e = [] :=
    Lambda.LExpr.genLExpr_no_fvars octx [] tvars [] depth τ e he
  simp only [HasFvars.getFvars, hnil, List.not_mem_nil, not_false_eq_true]

/-- Soundness of `genCmd` with no hypothesis about freshness: each result in the support of the
    generator gives a well-typed command. Two obligations remain, and both depend on the context.
    `hCorr` is the correspondence between a `VarCtx` and a `TContext`. `hExprSound` is the
    soundness of the generator for an expression, at the free-variable context of the scope. This
    theorem discharges the hypothesis about a fresh name with
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

/-- A `GenCmdSoundEnv` that uses the proved fact about a fresh name. The caller gives the four
    other fields, `toTCtx`, `corr`, `exprSound` and `toTCtx_insert`, and each one depends on the
    context. The caller gives `exprSound` at the free-variable context of each scope. -/
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

/-- Soundness of `genCmds` with no hypothesis about freshness. Each generated sequence of commands
    satisfies the chain relation `CmdsHasTypeA`. -/
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
