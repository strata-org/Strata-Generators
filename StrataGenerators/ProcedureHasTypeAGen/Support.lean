import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.CmdHasTypeAGenSound

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen
open StrataGenerators.Stmt

/-!
# A concrete `GenStmtSoundEnv` for the procedure generator

`genProcedure` generates a structured body via `genStmtChain` seeded from the
procedure's *output* parameters. To reuse the statement-generator soundness proof
(`genStmt_sound` / `genStmtChain_sound`), we need an actual `GenStmtSoundEnv`
instance — a bundle exhibiting a semantic `TContext` for each flat `VarCtx`,
together with the `VarCtxCorresponds` correspondence and the expression-level
obligations.

This file constructs the *first concrete* such environment, `procStmtEnv`, at an
empty fvar context (`fctx = []`). The construction is possible precisely because
`VarCtxCorresponds` is now stated in terms of `Map.find?` (rather than raw
`List.Mem`): with the find?-based statement, the natural single-scope reading

    toTCtx ctx := { types := [ctx.fmap (LTy.forAll [])] }

satisfies the correspondence *unconditionally*, via `Map.find?_fmap`.

The single scope is exactly the shape `procBodyContext` produces for a procedure
with empty `typeArgs` / `inputs` / in-out params (its body scope is then just the
output parameters pushed as one new scope onto the empty ambient `Γ`), which is
what lets `genProcedure_sound` line up the body's `StmtsHasTypeA` with the
declarative `ProcBodyHasType'.structured` obligation.
-/

namespace StrataGenerators.Procedure

/-- `Map.fmap` commutes with `Map.insert`: inserting then mapping the values is
    the same as mapping then inserting the mapped value. -/
theorem Map.fmap_insert [DecidableEq α] (m : Map α β) (x : α) (v : β) (f : β → γ) :
    (m.insert x v).fmap f = (m.fmap f).insert x (f v) := by
  induction m with
  | nil => rfl
  | cons p m ih =>
    obtain ⟨a, b⟩ := p
    simp only [Map.insert, Map.fmap, List.map]
    split <;> simp_all [Map.fmap]

/-- Inserting into a single-scope stack `[m]` updates that one scope. -/
theorem Maps.insert_singleton [DecidableEq α] (m : Map α β) (x : α) (v : β) :
    Maps.insert [m] x v = [m.insert x v] := by
  simp only [Maps.insert, Maps.find?]
  cases h : Map.find? m x <;>
    simp [Maps.pop, Maps.push, Maps.newest, Maps.update, h]

/-- The concrete single-scope `TContext` for a flat `VarCtx`: one new scope in
    which every variable is bound to its declared monotype as a trivial polytype
    (`LTy.forAll []`). -/
def procToTCtx (ctx : VarCtx) : TContext Unit :=
  { types := [ctx.fmap (fun mty => (LTy.forAll [] mty))] }

/-- Looking up `x` in `procToTCtx ctx` is exactly the flat-context lookup with its
    monotype wrapped as a trivial polytype. Follows from `Map.find?_fmap`. -/
theorem procToTCtx_find (ctx : VarCtx) (x : Identifier Unit) :
    (procToTCtx ctx).types.find? x = (Map.find? ctx x).map (fun mty => (LTy.forAll [] mty)) := by
  show Maps.find? [ctx.fmap _] x = _
  cases h : Map.find? ctx x <;>
    simp [Maps.find?, Map.find?_fmap, h]

/-- The `VarCtx ↔ TContext` correspondence holds for `procToTCtx` at *every* flat
    context — unconditionally, thanks to the find?-based `VarCtxCorresponds`. -/
theorem procToTCtx_corr (ctx : VarCtx) : VarCtxCorresponds ctx (procToTCtx ctx) := by
  constructor
  · intro x mty hfind
    rw [procToTCtx_find]
    unfold VarCtx.find? at hfind
    rw [hfind]; rfl
  · intro x hfresh
    rw [procToTCtx_find]
    unfold VarCtx.isFresh VarCtx.find? at hfresh
    rw [Option.isNone_iff_eq_none] at hfresh
    rw [hfresh]; rfl

/-- `procToTCtx` commutes with `VarCtx.insert`: this is the `init`-command
    obligation of `GenCmdSoundEnv`/`GenStmtSoundEnv`. -/
theorem procToTCtx_insert (ctx : VarCtx) (x : Identifier Unit) (mty : LMonoTy) :
    procToTCtx (ctx.insert x mty) =
      { procToTCtx ctx with types := (procToTCtx ctx).types.insert x (LTy.forAll [] mty) } := by
  unfold procToTCtx
  simp only [TContext.mk.injEq]
  show [(ctx.insert x mty).fmap _] = Maps.insert [ctx.fmap _] x (LTy.forAll [] mty) ∧ _
  rw [Maps.insert_singleton, Map.fmap_insert]
  exact ⟨rfl, trivial⟩

/-- **The concrete statement-generator soundness environment**, for any operator
    context `octx` and type-variable list `tvars`.

    - `toTCtx` / `corr` / `toTCtx_insert`: the single-scope construction above.
    - `exprSound`: discharged by the unconditional `genLExpr_sound` (at each scope's
      derived free-variable context `ctx.toFVarCtx`).
    - `freshDisjoint`: discharged by `freshNamesDisjointFromExprs_toFVarCtx` — valid
      at *every* `ctx`, since generated free variables come from `ctx.toFVarCtx`
      (whose names are `ctx`'s) and a fresh `init` name avoids `ctx`. This is what
      lets a generated procedure body genuinely *read* its parameters. -/
def procStmtEnv (octx : OpCtx) (tvars : List TyIdentifier) :
    GenStmtSoundEnv octx tvars where
  toTCtx := procToTCtx
  corr := procToTCtx_corr
  exprSound := fun d ctx τ e he => genLExpr_sound ctx.toFVarCtx octx [] tvars [] d τ e he
  freshDisjoint := fun d ctx => freshNamesDisjointFromExprs_toFVarCtx octx tvars ctx d
  toTCtx_insert := procToTCtx_insert

@[simp] theorem procStmtEnv_toTCtx (octx : OpCtx) (tvars : List TyIdentifier) :
    (procStmtEnv octx tvars).toTCtx = procToTCtx := rfl

end StrataGenerators.Procedure
