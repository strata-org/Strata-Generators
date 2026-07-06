import StrataGenerators.HasTypeAGen
import StrataGenerators.CmdHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen

/-!
# Hypothesis-free soundness of `genCmd` at an empty fvar context

`genCmd_sound` (in `CmdHasTypeAGen.lean`) takes `FreshNamesDisjointFromExprs` as a
hypothesis, noting it was not yet proven. That predicate is in fact *false* for a
nonempty `fctx`: `genLExpr` draws free variables from `fctx` via `pickFVar`, and a
name fresh with respect to the command context `ctx` can still collide with an
`fctx` entry. It is, however, true (and provable) for `fctx = []` — exactly the
instantiation both test harnesses use — because then `pickFVar` is unreachable and
generated expressions contain no free variables at all (`genLExpr_no_fvars`).

This file discharges that hypothesis for `fctx = []` and packages the result as
hypothesis-free entry points `genCmd_sound_nil` / `genCmds_sound_nil`.
-/

/-- With an empty fvar context, fresh names never collide with the free variables
    of generated expressions — because generated expressions have no free
    variables at all (`Lambda.LExpr.genLExpr_no_fvars`). This discharges the
    `FreshNamesDisjointFromExprs` hypothesis of `genCmd_sound` for `fctx = []`. -/
theorem freshNamesDisjointFromExprs_nil (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) :
    FreshNamesDisjointFromExprs [] octx tvars ctx depth := by
  intro name _ τ e he
  -- `getVars` for `Expression` is `LExpr.getVars`, which is `[]` here.
  have hnil : LExpr.getVars e = [] :=
    Lambda.LExpr.genLExpr_no_fvars octx [] tvars [] depth τ e he
  simp only [HasVarsPure.getVars, hnil, List.not_mem_nil, not_false_eq_true]

/-- Hypothesis-free soundness of `genCmd` at an empty fvar context: every result
    in the generator's support produces a well-typed command. The only remaining
    obligations are the genuine context-dependent ones — `hCorr` (the
    `VarCtx ↔ TContext` correspondence) and `hExprSound` (expression-level
    soundness). The freshness/disjointness hypothesis is discharged internally via
    `freshNamesDisjointFromExprs_nil`. -/
theorem genCmd_sound_nil
    (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (hCorr : VarCtxCorresponds ctx Γ)
    (hExprSound : GenLExprSound [] octx tvars depth)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) [] octx tvars ctx depth)) :
    ∃ Γ', CmdHasTypeA C Γ r.cmd Γ' :=
  genCmd_sound [] octx tvars ctx depth C Γ hCorr hExprSound
    (freshNamesDisjointFromExprs_nil octx tvars ctx depth) r hr

/-- A `GenCmdSoundEnv` at an empty fvar context, built from the proven
    disjointness fact. The remaining fields — `toTCtx`, `corr`, `exprSound`,
    `toTCtx_insert` — are the genuine context-dependent obligations the caller
    supplies. -/
def genCmdSoundEnv_nil
    (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (C : LContext CoreLParams)
    (toTCtx : VarCtx → TContext Unit)
    (corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx))
    (exprSound : GenLExprSound [] octx tvars depth)
    (toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
      toTCtx (ctx.insert x mty) =
        { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }) :
    GenCmdSoundEnv [] octx tvars depth C where
  toTCtx := toTCtx
  corr := corr
  exprSound := exprSound
  freshDisjoint := fun ctx => freshNamesDisjointFromExprs_nil octx tvars ctx depth
  toTCtx_insert := toTCtx_insert

/-- Hypothesis-free soundness of `genCmds` (command sequences) at an empty fvar
    context: every generated sequence satisfies the chained `CmdsHasTypeA`
    relation. -/
theorem genCmds_sound_nil
    (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (n : Nat)
    (C : LContext CoreLParams)
    (env : GenCmdSoundEnv [] octx tvars depth C)
    (result : List (Cmd Expression) × VarCtx)
    (hr : result ∈ SetGen.support (genCmds (G := SetGen.Set) [] octx tvars ctx depth n)) :
    CmdsHasTypeA C (env.toTCtx ctx) result.1 (env.toTCtx result.2) :=
  genCmds_sound [] octx tvars ctx depth n C env result hr
