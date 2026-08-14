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
what lets `genProcedure_sound` line up the body's `StatementsHasTypeA` with the
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

/-- Strata's first-match `Map.find?` is `List.lookup`. Bridges the flat `VarCtx` lookup to
    `Freshening.find?_ofList_reverse`, which speaks about `List.lookup`. -/
theorem Map.find?_eq_lookup {β} (m : Map (Identifier Unit) β) (x : Identifier Unit) :
    Map.find? m x = m.lookup x := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [Map.find?, List.lookup_cons]
    by_cases hk : k = x
    · subst hk; simp
    · rw [if_neg hk, show (x == k) = false from by simp [Ne.symm hk], ih]

/-- The concrete single-scope `TContext` for a flat `VarCtx`: one new scope in
    which every variable is bound to its declared monotype as a trivial polytype
    (`LTy.forAll []`).

    A `TContext` scope is an opaque `Strata.Util.HMap` upstream, so the flat context is
    reversed before `HMap.ofList`: `ofList` keeps the *last* binding for a key, while
    `Map.find?` returns the *first*, and reversing makes the two agree
    (`Freshening.find?_ofList_reverse`). -/
def procToTCtx (ctx : VarCtx) : TContext Unit :=
  { types := [Strata.Util.HMap.ofList (ctx.fmap (fun mty => (LTy.forAll [] mty))).reverse] }

/-- Looking up `x` in `procToTCtx ctx` is exactly the flat-context lookup with its
    monotype wrapped as a trivial polytype. Follows from `Map.find?_fmap`. -/
theorem procToTCtx_find (ctx : VarCtx) (x : Identifier Unit) :
    (procToTCtx ctx).types.find? x = (Map.find? ctx x).map (fun mty => (LTy.forAll [] mty)) := by
  show Strata.Util.HMaps.find? [_] x = _
  rw [Strata.Util.HMaps.find?_single_scope, Freshening.find?_ofList_reverse,
    ← Map.find?_eq_lookup, Map.find?_fmap]

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

/-- Inserting into a single-scope stack updates that one scope (an equality, since both
    branches of `HMaps.insert` collapse to the same list on a singleton). -/
theorem HMaps.insert_singleton {α β} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (m : Strata.Util.HMap α β) (x : α) (v : β) :
    Strata.Util.HMaps.insert [m] x v = [m.insert x v] := by
  simp only [Strata.Util.HMaps.insert, Strata.Util.HMaps.find?]
  cases hm : Strata.Util.HMap.find? m x with
  | none =>
    simp only [Strata.Util.HMaps.pop, Strata.Util.HMaps.push, Strata.Util.HMaps.newest]
  | some w =>
    simp only [hm, Strata.Util.HMaps.update]

/-- The single scope `procToTCtx ctx` is built from. -/
private theorem procToTCtx_types (ctx : VarCtx) :
    (procToTCtx ctx).types
      = [Strata.Util.HMap.ofList (ctx.fmap (fun mty => (LTy.forAll [] mty))).reverse] := rfl

/-- `procToTCtx`'s single scope looks up exactly like the flat context. -/
private theorem procToTCtx_scope_find (ctx : VarCtx) (k : Identifier Unit) :
    Strata.Util.HMap.find?
        (Strata.Util.HMap.ofList (ctx.fmap (fun mty => (LTy.forAll [] mty))).reverse) k
      = (Map.find? ctx k).map (fun mty => (LTy.forAll [] mty)) := by
  rw [Freshening.find?_ofList_reverse, ← Map.find?_eq_lookup, Map.find?_fmap]

/-- `procToTCtx` commutes with `VarCtx.insert` up to `TContext.Equiv`: this is the
    `init`-command obligation of `GenCmdSoundEnv`/`GenStmtSoundEnv`. Only `Equiv` is
    available — and only `Equiv` is needed — because a scope is an opaque hash map, so
    `ofList` of an extended list is not the same *map value* as an insertion. -/
theorem procToTCtx_insert (ctx : VarCtx) (x : Identifier Unit) (mty : LMonoTy) :
    TContext.Equiv (T := CoreLParams) (procToTCtx (ctx.insert x mty))
      { procToTCtx ctx with types := (procToTCtx ctx).types.insert x (LTy.forAll [] mty) } := by
  -- One scope on each side, so scope-stack equivalence is pointwise `find?` agreement.
  have hpt : Strata.Util.HMap.Equiv
      (Strata.Util.HMap.ofList
        ((ctx.insert x mty).fmap (fun t => (LTy.forAll [] t))).reverse)
      ((Strata.Util.HMap.ofList
        (ctx.fmap (fun t => (LTy.forAll [] t))).reverse).insert x (LTy.forAll [] mty)) := by
    intro k
    rw [procToTCtx_scope_find (ctx.insert x mty) k]
    by_cases hk : k = x
    · subst hk
      rw [Strata.Util.HMap.find?_insert_self, Map.find?_insert_self]; rfl
    · rw [Strata.Util.HMap.find?_insert_ne _ x k _ (by simp [bne]; exact hk),
        Map.find?_insert_ne ctx k x mty hk, procToTCtx_scope_find ctx k]
  refine ⟨?_, rfl⟩
  rw [procToTCtx_types ctx, procToTCtx_types (ctx.insert x mty), HMaps.insert_singleton]
  exact ⟨hpt, True.intro⟩

/-- **The concrete statement-generator soundness environment**, for any operator
    context `octx` and type-variable list `tvars`.

    - `toTCtx` / `corr` / `toTCtx_insert`: the single-scope construction above.
    - `exprSound`: discharged by the unconditional `genLExpr_sound` (at each scope's
      derived free-variable context `ctx.toFVarCtx`).
    - `freshDisjoint`: discharged by `freshNamesDisjointFromExprs_toFVarCtx` — valid
      at *every* `ctx`, since generated free variables come from `ctx.toFVarCtx`
      (whose names are `ctx`'s) and a fresh `init` name avoids `ctx`. This is what
      lets a generated procedure body genuinely *read* its parameters. -/
def procStmtEnv (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx := []) :
    GenStmtSoundEnv octx tvars pctx where
  toTCtx := procToTCtx
  corr := procToTCtx_corr
  exprSound := fun d ctx τ e he => genLExpr_sound ctx.toFVarCtx octx pctx tvars [] d τ _ e he
  freshDisjoint := fun d ctx => freshNamesDisjointFromExprs_toFVarCtx octx tvars ctx d pctx
  toTCtx_insert := procToTCtx_insert

@[simp] theorem procStmtEnv_toTCtx (octx : OpCtx) (tvars : List TyIdentifier)
    (pctx : PolyOpCtx) :
    (procStmtEnv octx tvars pctx).toTCtx = procToTCtx := rfl

-- ── Γ-parameterized environment (ambient-context threading) ────────────────

/-- The `Γ`-parameterized single-scope `TContext` for a flat `VarCtx`: one new
    scope in which every variable is bound to its declared monotype as a trivial
    polytype, *carrying the ambient `Γ`'s alias list*. This aligns with the
    declarative `procBodyContext Γ proc`, which pushes the body scope onto
    `Γ.types` and preserves `Γ.aliases`; when `Γ.types = []` the two agree. -/
def procToTCtxΓ (Γ : TContext Unit) (ctx : VarCtx) : TContext Unit :=
  { types := (procToTCtx ctx).types, aliases := Γ.aliases }

/-- Looking up `x` in `procToTCtxΓ Γ ctx` is the flat-context lookup with its
    monotype wrapped as a trivial polytype (the `types` field is independent of
    `Γ`, so this is `procToTCtx_find` verbatim). -/
theorem procToTCtxΓ_find (Γ : TContext Unit) (ctx : VarCtx) (x : Identifier Unit) :
    (procToTCtxΓ Γ ctx).types.find? x = (Map.find? ctx x).map (fun mty => (LTy.forAll [] mty)) :=
  procToTCtx_find ctx x

/-- The `VarCtx ↔ TContext` correspondence holds for `procToTCtxΓ Γ` at *every*
    flat context, for *any* `Γ` — the correspondence only inspects the `.types`
    field, which is independent of `Γ.aliases`. -/
theorem procToTCtxΓ_corr (Γ : TContext Unit) (ctx : VarCtx) :
    VarCtxCorresponds ctx (procToTCtxΓ Γ ctx) := by
  constructor
  · intro x mty hfind
    rw [procToTCtxΓ_find]
    unfold VarCtx.find? at hfind
    rw [hfind]; rfl
  · intro x hfresh
    rw [procToTCtxΓ_find]
    unfold VarCtx.isFresh VarCtx.find? at hfresh
    rw [Option.isNone_iff_eq_none] at hfresh
    rw [hfresh]; rfl

/-- `procToTCtxΓ Γ` commutes with `VarCtx.insert`: the `init`-command obligation
    (aliases carry through unchanged, and the `types` update mirrors
    `procToTCtx_insert`). -/
theorem procToTCtxΓ_insert (Γ : TContext Unit) (ctx : VarCtx) (x : Identifier Unit) (mty : LMonoTy) :
    TContext.Equiv (T := CoreLParams) (procToTCtxΓ Γ (ctx.insert x mty))
      { procToTCtxΓ Γ ctx with
        types := (procToTCtxΓ Γ ctx).types.insert x (LTy.forAll [] mty) } :=
  -- Only `types` is at stake, and it is `procToTCtx`'s verbatim.
  ⟨(procToTCtx_insert ctx x mty).1, rfl⟩

/-- **The Γ-parameterized statement-generator soundness environment**: identical
    to `procStmtEnv` except its `toTCtx` carries the ambient `Γ`'s alias list. All
    non-`toTCtx` obligations (`corr`/`toTCtx_insert`) are unaffected by aliases,
    and `exprSound`/`freshDisjoint` hold at every `ctx`'s own derived
    free-variable projection `ctx.toFVarCtx` (exactly as in `procStmtEnv`). -/
def procStmtEnvΓ (Γ : TContext Unit) (octx : OpCtx) (tvars : List TyIdentifier)
    (pctx : PolyOpCtx := []) : GenStmtSoundEnv octx tvars pctx where
  toTCtx := procToTCtxΓ Γ
  corr := procToTCtxΓ_corr Γ
  exprSound := fun d ctx τ e he => genLExpr_sound ctx.toFVarCtx octx pctx tvars [] d τ _ e he
  freshDisjoint := fun d ctx => freshNamesDisjointFromExprs_toFVarCtx octx tvars ctx d pctx
  toTCtx_insert := procToTCtxΓ_insert Γ

@[simp] theorem procStmtEnvΓ_toTCtx (Γ : TContext Unit) (octx : OpCtx)
    (tvars : List TyIdentifier) (pctx : PolyOpCtx) :
    (procStmtEnvΓ Γ octx tvars pctx).toTCtx = procToTCtxΓ Γ := rfl

end StrataGenerators.Procedure
