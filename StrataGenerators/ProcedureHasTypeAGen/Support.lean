import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.CmdHasTypeAGenSound

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen
open StrataGenerators.Stmt

/-!
# A concrete `GenStmtSoundEnv` for the procedure generator

`genProcedure` gives a structured body through `genStmtChain`, from a scope that holds the inputs, the
outputs and the `old` bindings of the procedure. The soundness proofs of the statement generator need a
`GenStmtSoundEnv` instance, which is a bundle that gives a semantic `TContext` for each flat `VarCtx`,
together with the correspondence `VarCtxCorresponds` and the obligations at the level of an expression.

This file builds one concrete such environment, `procStmtEnv`, at an empty context of the free variables. The
construction is possible because `VarCtxCorresponds` is stated in terms of `Map.find?`, and not in terms of a
raw membership in a list. With the form over `find?`, the natural reading of one scope

    toTCtx ctx := { types := [ctx.fmap (LTy.forAll [])] }

satisfies the correspondence *unconditionally*, via `Map.find?_fmap`.

The single scope has the shape of `procBodyScopes []`: one new scope over an empty stack.
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
    by_cases hax : a = x
    · rw [Map.insert_cons_of_eq hax]
      exact (Map.insert_cons_of_eq (b := f b) (m := Map.fmap f m) hax).symm
    · rw [Map.insert_cons_of_ne hax]
      refine Eq.trans ?_ (Map.insert_cons_of_ne (b := f b) (m := Map.fmap f m) hax).symm
      exact congrArg ((a, f b) :: ·) ih

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
  rw [Strata.Util.HMaps.find?_single_scope,
    Freshening.find?_ofList_reverse (ctx.fmap (fun mty => (LTy.forAll [] mty))) x,
    ← Map.find?_eq_lookup (ctx.fmap (fun mty => (LTy.forAll [] mty))) x, Map.find?_fmap]

/-- The correspondence between a flat context and a `TContext` holds for `procToTCtx` at *each* flat context, and
    it needs no hypothesis, because `VarCtxCorresponds` is stated over `find?`. -/
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
  rw [Freshening.find?_ofList_reverse (ctx.fmap (fun mty => (LTy.forAll [] mty))) k,
    ← Map.find?_eq_lookup (ctx.fmap (fun mty => (LTy.forAll [] mty))) k, Map.find?_fmap]

/-- `procToTCtx` commutes with `VarCtx.insert`, up to `TContext.Equiv`. That is the obligation about an `init`
    command in each environment for the soundness proofs. Only that equivalence is available, and only it is
    necessary, because a scope is a hash map. Therefore `ofList` over an extended list gives a different *map
    value* than an insertion gives. -/
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
    - `freshNamesDisjointFromExprs_toFVarCtx` discharges the field `freshDisjoint`. That lemma holds at *each*
      scope, because each generated free variable comes from `ctx.toFVarCtx`, whose names are the names of the
      scope, and a fresh name of an `init` differs from each name of the scope. That fact is what
      lets a generated procedure body genuinely *read* its parameters. -/
def procStmtEnv (octx : OpCtx) (tvars : List TyIdentifier) (pctx : PolyOpCtx := []) :
    GenStmtSoundEnv octx tvars pctx where
  toTCtx := procToTCtx
  corr := procToTCtx_corr
  freshDisjoint := fun d ctx => freshNamesDisjointFromExprs_toFVarCtx octx tvars ctx d pctx
  toTCtx_insert := procToTCtx_insert

@[simp] theorem procStmtEnv_toTCtx (octx : OpCtx) (tvars : List TyIdentifier)
    (pctx : PolyOpCtx) :
    (procStmtEnv octx tvars pctx).toTCtx = procToTCtx := rfl

end StrataGenerators.Procedure
