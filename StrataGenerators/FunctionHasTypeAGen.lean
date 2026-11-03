import StrataGenerators.HasTypeAGen
import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Dedup
import StrataGenerators.FunctionHasTypeAGen.IdentName
import Basalt.Walk.Complete
import Strata.Languages.Core.FunctionTypeSpec

open Lambda LExpr RandomChoice Core Imperative TypeSpec ArbString
open StrataGenerators.Dedup

/-!
# The soundness and the completeness of `genFunction`

`genFunction` makes a random Strata Core function, which is a `Function` and therefore an
`LFunc CoreLParams`. This file proves that the generator is sound and complete against the
typing relation `FuncHasTypeA`.

## Why this file is simpler than the file for a command

The annotated typing specification `instHasTypeA` that `FuncHasTypeA` uses *ignores* the
ambient typing context:

```
instance instHasTypeA : ExprTypingSpec LMonoTy where
  embed := id
  exprTyped := fun _C _Γ e mty => LExpr.HasTypeA [] e mty
```

The two obligations `bodyTyped` and `measureTyped` therefore reduce *by definition* to
`LExpr.HasTypeA [] body output` and to `LExpr.HasTypeA [] m .int`. Those are exactly the
claims that `genLExpr … [] tvars [] depth τ` gives. No correspondence between a `VarCtx`
and a `TContext` is necessary.

## Contents

- The lemmas about a free variable, which relate `allFtvarsIn` and `mkArrow'` to
  `LMonoTy.freeVars`.
- `genFunction_sound`: each generated function satisfies `FuncHasTypeA`.
- `genFunction_complete`: the support of `genFunction` holds each well-typed function that
  satisfies the side conditions about the reachability of its expressions.
-/

namespace StrataGenerators.Function

-- ── The lemmas about a free variable ─────────────────────────────────

/-- If `v` is a free variable of the list of types `tys`, then some element of `tys` holds `v`.

    Strata proves this claim as `Lambda.LMonoTys.freeVars_exists`. That theorem is in a module with
    no `public section`, so only an `import all` reaches it, and this file is not a `module` and
    cannot use such an import. The proof here is three lines from the public
    `LMonoTys.freeVars_of_cons`, so this file has its own copy and Strata keeps its visibility. -/
theorem freeVars_exists' {v : TyIdentifier} {tys : List LMonoTy}
    (hv : v ∈ LMonoTys.freeVars tys)
    : ∃ ty, ty ∈ tys ∧ v ∈ LMonoTy.freeVars ty := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons ty rest ih =>
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    cases hv with
    | inl h => exact ⟨ty, .head _, h⟩
    | inr h => obtain ⟨t, ht, hvt⟩ := ih h; exact ⟨t, .tail _ ht, hvt⟩

/-- `allFtvarsIn tvars τ` says that each free type variable of `τ` comes from `tvars`. This theorem
    states the same claim through `LMonoTy.freeVars`, which is the form that `noUndeclaredVars`
    uses. -/
theorem allFtvarsIn_freeVars {tvars : List TyIdentifier} {τ : LMonoTy}
    (h : allFtvarsIn tvars τ) : ∀ v ∈ LMonoTy.freeVars τ, v ∈ tvars := by
  induction τ with
  | ftvar f =>
    intro v hv
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv
    unfold allFtvarsIn at h
    exact h
  | bitvec n =>
    intro v hv
    simp [LMonoTy.freeVars] at hv
  | tcons name args ih =>
    intro v hv
    simp only [LMonoTy.freeVars] at hv
    -- `allFtvarsIn tvars (.tcons name args)` unfolds to one claim for each argument.
    have hargs : ∀ a ∈ args, allFtvarsIn tvars a := by unfold allFtvarsIn at h; exact h
    -- Reduce membership in `LMonoTys.freeVars` to an element that holds `v`.
    obtain ⟨ty, hty_mem, hv_ty⟩ := freeVars_exists' hv
    exact ih ty hty_mem (hargs ty hty_mem) v hv_ty

set_option linter.unusedSimpArgs false in
/-- A free variable of `mkArrow' out vals` is a free variable of `out`, or it is a free variable of
    an element of `vals`. -/
theorem freeVars_mkArrow' (out : LMonoTy) (vals : List LMonoTy) (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' out vals)) :
    v ∈ LMonoTy.freeVars out ∨ ∃ t ∈ vals, v ∈ LMonoTy.freeVars t := by
  induction vals with
  | nil =>
    left
    rwa [LMonoTy.mkArrow'_nil] at hv
  | cons t rest ih =>
    rw [LMonoTy.mkArrow'_cons] at hv
    -- `.arrow t (mkArrow' out rest)` is `.tcons "arrow" [t, mkArrow' out rest]`.
    simp only [LMonoTy.arrow, LMonoTy.freeVars, LMonoTys.freeVars_of_cons,
               LMonoTys.freeVars, List.append_nil, List.mem_append] at hv
    rcases hv with hvt | hvrest
    · exact Or.inr ⟨t, List.mem_cons_self, hvt⟩
    · rcases ih hvrest with hout | ⟨t', ht'_mem, hv'⟩
      · exact Or.inl hout
      · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht'_mem, hv'⟩

-- ── The support of the generators for a name, a type argument and an input ──

/-- Each list in the support of `genTypeArgs` holds no duplicate, because `List.uniq` builds
    it. -/
theorem genTypeArgs_nodup (depth : Nat) (l : List TyIdentifier)
    (hl : l ∈ SPMF.support (genTypeArgs (G := SPMF) depth)) : l.Nodup := by
  simp only [genTypeArgs, mem_support_map_iff] at hl
  obtain ⟨names, _, rfl⟩ := hl
  exact List.nodup_uniq names

/-- Each list in the support of `genIdents` holds no duplicate, because `List.uniq` builds it. -/
theorem genIdents_nodup (depth : Nat) (l : List (Identifier Unit))
    (hl : l ∈ SPMF.support (genIdents (G := SPMF) depth)) : l.Nodup := by
  simp only [genIdents, mem_support_map_iff] at hl
  obtain ⟨names, _, rfl⟩ := hl
  exact List.nodup_uniq _

-- ── A generated name is not a keyword and it holds no space ──────────
-- The `IdentName` module holds these results. Each one follows from
-- `mem_support_genIdentName_iff`, which gives the support in both directions. That module also uses
-- the same lemma to discharge the side conditions about the reachability of a name in the proofs of
-- completeness in this package. The results are `genIdentName_not_keyword`,
-- `genIdentName_no_space`, the `dodgeKeyword` lemmas, `append_underscore_not_keyword` and
-- `no_keyword_ends_underscore`. Each one is in the namespace `StrataGenerators.Function`.

/-- The `mapM` inside `genInputs` gives a `ListMap` whose keys are the list of input identifiers and
    each of whose values is in the support of `genLMonoTy tvars depth`. -/
theorem mapM_genInputs_keys_values (tvars : List TyIdentifier) (depth : Nat)
    (idents : List (Identifier Unit)) (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SPMF.support
      (idents.mapM (m := SPMF) (fun x => do
        let ty ← genLMonoTy (G := SPMF) tvars depth
        pure (x, ty)))) :
    m.keys = idents ∧
    ∀ ty ∈ m.values, ty ∈ SPMF.support (genLMonoTy (G := SPMF) tvars depth) := by
  induction idents generalizing m with
  | nil =>
    obtain rfl := SPMF.mem_support_pure_iff.mp hm
    exact ⟨rfl, nofun⟩
  | cons x xs ih =>
    revert m; show IsSoundFor _ _
    rw [IsSoundFor.iff_obs, List.mapM_cons]
    walk [IsSoundFor.obs ih, IsSoundFor.obs (g := genLMonoTy (G := SPMF) tvars depth) fun _ h => h]
    all_goals aesop (add norm simp [ListMap.keys, ListMap.values])

/-- What membership in the support of `genInputs tvars depth` gives. The keys of the `ListMap` are a
    list of identifiers with no duplicate, and each value is in the support of
    `genLMonoTy tvars depth`. -/
theorem genInputs_support (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SPMF.support (genInputs (G := SPMF) tvars depth)) :
    m.keys.Nodup ∧ ∀ ty ∈ m.values, ty ∈ SPMF.support (genLMonoTy (G := SPMF) tvars depth) := by
  simp only [genInputs, mem_support_bind_iff] at hm
  obtain ⟨idents, hidents, hm⟩ := hm
  have hnd := genIdents_nodup depth idents hidents
  obtain ⟨hkeys, hvals⟩ := mapM_genInputs_keys_values tvars depth idents m hm
  exact ⟨hkeys ▸ hnd, hvals⟩

/-- `genIdentName` can reach the `name` of each key of a signature that `genInputs` gives. The keys
    are the list of identifiers after `List.uniq`, their names come from `genNameList`, and
    `genNameList` takes each name from `genIdentName`. -/
theorem genInputs_key_name_reachable (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SPMF.support (genInputs (G := SPMF) tvars depth))
    (k : Identifier Unit) (hk : k ∈ m.keys) :
    k.name ∈ SPMF.support (genIdentName (G := SPMF)) := by
  simp only [genInputs, mem_support_bind_iff] at hm
  obtain ⟨idents, hidents, hmapM⟩ := hm
  obtain ⟨hkeys, _⟩ := mapM_genInputs_keys_values tvars depth idents m hmapM
  rw [hkeys] at hk
  simp only [genIdents, mem_support_map_iff] at hidents
  obtain ⟨names, hnames, rfl⟩ := hidents
  rw [← List.mem_of_dedup] at hk
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hk
  rw [genNameList, mem_support_listOfMaxLength_iff] at hnames
  exact hnames.2 s hs

/-- Each key of a signature that `genInputs` gives holds no space, so the characters of its `name`
    hold no `' '`. The proof joins `genInputs_key_name_reachable` and `genIdentName_no_space`. This
    fact separates a generated parameter name from a key that `CoreIdent.mkOld` makes, because such a
    key starts with `"old "`. It therefore keeps the first context of a procedure body
    `Functional`. -/
theorem genInputs_key_no_space (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SPMF.support (genInputs (G := SPMF) tvars depth))
    (k : Identifier Unit) (hk : k ∈ m.keys) :
    ' ' ∉ k.name.toList :=
  genIdentName_no_space k.name (genInputs_key_name_reachable tvars depth m hm k hk)

-- ── The soundness of the generator for an optional expression ────────

/-- With an empty context of polymorphic operators, `polyOpsForResult` is always empty. The side
    condition `hSimplePolyOps` of `genLExpr_sound` is therefore vacuous. -/
theorem polyOpsForResult_nil (τ : LMonoTy) (generableTys sampledTys : List LMonoTy) :
    findPolymorphicOps [] τ generableTys sampledTys = [] := by
  simp [findPolymorphicOps]

/-- Soundness of `genOptExpr`: each `some e` that it gives is well-typed at `τ`, in the empty context
    of bound variables. The case of a `none` is vacuous. -/
theorem genOptExpr_sound (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy) (pctx : PolyOpCtx)
    (o : Option LExpr')
    (ho : o ∈ SPMF.support (genOptExpr (G := SPMF) fctx octx tvars depth τ pctx))
    (e : LExpr') (heq : o = some e) :
    HasTypeA' [] e τ := by
  refine (show IsSoundFor _ (fun o => ∀ e, o = some e → HasTypeA' [] e τ) by
    rw [IsSoundFor.iff_obs, genOptExpr]
    walk [IsSoundFor.obs (genLExpr_sound fctx octx pctx tvars [] depth τ _)]
    all_goals simp_all) o ho e heq

-- ── The soundness of `genFunction` ───────────────────────────────────

/-- **Soundness of `genFunction`.** Each function in the support of the generator is well-typed
    against `FuncHasTypeA`, for *each* ambient context `Γ` and for *each* operator context. The
    annotated specification ignores the ambient context, and `genLExpr_sound` needs no condition on
    the operator context.

    The one condition on `C` is `SimpleTyArities`, and the field `signatureWellKinded` needs it. That
    field asks that each type in the signature be well-kinded in `C`. The generator builds only a
    type that it can make, so it is enough that `C` registers the eight type constructors at their own
    arities. The Core context of Strata does this, as `coreContextSimpleTyArities` states. -/
theorem genFunction_sound (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit) (pctx : PolyOpCtx)
    (hC : SimpleTyArities C)
    (func : Function)
    (hfunc : func ∈ SPMF.support (genFunction (G := SPMF) fctx octx depth pctx)) :
    FuncHasTypeA C Γ func := by
  -- Show the parts that the generator made for each field.
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff] at hfunc
  -- The generator also makes the preconditions, but `FuncHasType'` has no field for them. The proof
  -- therefore does not use the witness `_hpre` for their reachability.
  obtain ⟨name, _hname, typeArgs, htypeArgs, inputs, hinputs,
          output, houtput, body, hbody, measure, hmeasure,
          preconditions, _hpre, rfl⟩ := hfunc
  -- The facts about the generated type arguments and the generated inputs.
  have htyNodup : typeArgs.Nodup := genTypeArgs_nodup depth typeArgs htypeArgs
  obtain ⟨hkeysNodup, hvals⟩ := genInputs_support typeArgs depth inputs hinputs
  have houtputFtv : allFtvarsIn typeArgs output :=
    genLMonoTy_mem_ftvars houtput
  -- Build the `FuncHasType'` structure.
  refine ⟨hkeysNodup, htyNodup, ?_, ?_, ?_, ?_⟩
  · -- noUndeclaredVars
    intro v hv
    rcases freeVars_mkArrow' output inputs.values v hv with hout | ⟨t, ht_mem, hvt⟩
    · exact allFtvarsIn_freeVars houtputFtv v hout
    · -- `t` is an input value, so the support of `genLMonoTy` holds it and `allFtvarsIn` follows.
      have ht_supp := hvals t ht_mem
      have ht_ftv : allFtvarsIn typeArgs t :=
        genLMonoTy_mem_ftvars ht_supp
      exact allFtvarsIn_freeVars ht_ftv v hvt
  · -- signatureWellKinded. The generator can make each type of the signature, and the `tyCompat` of
    -- `HasTypeA` is plain equality, so `ty' := ty` works.
    intro ty hty
    refine ⟨ty, rfl, genLMonoTy_mem_wellKindedTy (tvars := typeArgs) hC ?_⟩
    rcases List.mem_cons.mp hty with rfl | hty
    · exact ⟨_, houtput⟩
    · exact ⟨_, hvals ty hty⟩
  · -- bodyTyped
    intro b hb
    exact genOptExpr_sound fctx octx typeArgs depth output pctx body hbody b hb
  · -- measureTyped
    intro m hm _
    exact genOptExpr_sound fctx octx typeArgs depth .int pctx measure hmeasure m hm

/-- **A generated function is never recursive.** `genFunction` writes no `isRecursive` field, so each
    function in its support carries the `false` default. `genFunction_complete` asks for the same fact
    in the other direction (`hRec`).

    Two places need it. `Function.toPureFuncDecl` writes `isRecursive := false` into the declaration it
    builds, so `ofPureFunc_toPureFuncDecl` recovers the function it started from only for a
    non-recursive one; and the `funcDecl` typing rule asks the declaration to be non-recursive. -/
theorem genFunction_not_isRecursive (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (pctx : PolyOpCtx) (func : Function)
    (hfunc : func ∈ SPMF.support (genFunction (G := SPMF) fctx octx depth pctx)) :
    func.isRecursive = false := by
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff] at hfunc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := hfunc
  rfl

/-- Soundness of `genFunction` at an empty operator context. This is a special case of
    `genFunction_sound`, which needs no condition on `octx`. -/
theorem genFunction_sound_nil (fctx : FVarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit) (hC : SimpleTyArities C)
    (func : Function)
    (hfunc : func ∈ SPMF.support (genFunction (G := SPMF) fctx ∅ depth)) :
    FuncHasTypeA C Γ func :=
  genFunction_sound fctx ∅ depth C Γ [] hC func hfunc

-- ── The lemmas for the completeness proof ────────────────────────────

/-- The support of `genNameList`, which comes from the support of `listOfMaxLength`. The generator can
    reach a list exactly when the length of the list is not more than `depth` and `genIdentName` can
    reach each name in it. This lemma turns the side conditions of `genFunction_complete` about the
    support of `genNameList` into concrete conditions.

    `mem_support_genIdentName_iff` gives the support of `genIdentName` in both directions, so the
    condition for one name is also concrete. -/
theorem mem_support_genNameList_iff (depth : Nat) (l : List String) :
    l ∈ SPMF.support (genNameList (G := SPMF) depth) ↔
      l.length ≤ depth ∧ ∀ s ∈ l, s ∈ SPMF.support (genIdentName (G := SPMF)) := by
  simp only [genNameList, mem_support_listOfMaxLength_iff]

/-- No name in a list that `genNameList` gives is a keyword. The proof carries
    `genIdentName_not_keyword` through the support of `genNameList`, which holds for each element. -/
theorem genNameList_not_keyword (depth : Nat) (l : List String)
    (hl : l ∈ SPMF.support (genNameList (G := SPMF) depth)) :
    ∀ s ∈ l, isReservedKeyword s = false := fun s hs =>
  genIdentName_not_keyword s ((mem_support_genNameList_iff depth l |>.mp hl).2 s hs)

/-- The converse of `mapM_genInputs_keys_values`. Take a `ListMap` such that
    `genLMonoTy tvars depth` can reach each of its values. The support of the `mapM` inside
    `genInputs`, over the keys of that map, then holds the map. -/
theorem mapM_genInputs_complete (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hvals : ∀ ty ∈ m.values, ty ∈ SPMF.support (genLMonoTy (G := SPMF) tvars depth)) :
    m ∈ SPMF.support
      (m.keys.mapM (m := SPMF) (fun x => do
        let ty ← genLMonoTy (G := SPMF) tvars depth
        pure (x, ty))) := by
  induction m with
  | nil => exact SPMF.mem_support_pure_iff.mpr rfl
  | cons p rest ih =>
    simp only [ListMap.values, List.mem_cons, forall_eq_or_imp] at hvals
    rw [ListMap.keys, List.mapM_cons]; refine SPMF.mem_support_iff_may.mpr ?_; walk
    exact ⟨_, hvals.1, _, ih hvals.2, rfl⟩

/-- `genIdents depth` can reach a list of identifiers `ids` that holds no duplicate, if
    `genNameList depth` can reach the list of names `ids.map (·.name)`. -/
theorem genIdents_complete (depth : Nat) (ids : List (Identifier Unit))
    (hnd : ids.Nodup)
    (hnames : ids.map (·.name) ∈ SPMF.support (genNameList (G := SPMF) depth)) :
    ids ∈ SPMF.support (genIdents (G := SPMF) depth) := by
  simp only [genIdents, mem_support_map_iff]
  refine ⟨ids.map (·.name), hnames, ?_⟩
  -- The map back over the names gives `ids` again, because the metadata of an `Identifier Unit` is
  -- `()`. `List.uniq` then leaves the list unchanged.
  have hmapeq : (ids.map (·.name)).map (fun s => (⟨s, ()⟩ : Identifier Unit)) = ids := by
    clear hnames hnd
    induction ids with
    | nil => rfl
    | cons a as ih =>
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih⟩; obtain ⟨n, u⟩ := a; trivial
  rw [hmapeq, uniq_eq_self ids hnd]

/-- `genTypeArgs depth` can reach a list of type arguments `l` that holds no duplicate, if
    `genNameList depth` can reach `l`. -/
theorem genTypeArgs_complete (depth : Nat) (l : List TyIdentifier)
    (hnd : l.Nodup)
    (hnames : l ∈ SPMF.support (genNameList (G := SPMF) depth)) :
    l ∈ SPMF.support (genTypeArgs (G := SPMF) depth) := by
  simp only [genTypeArgs, mem_support_map_iff]
  exact ⟨l, hnames, (uniq_eq_self l hnd).symm⟩

/-- Completeness of `genInputs`. The support of `genInputs tvars depth` holds a `ListMap` when three
    conditions hold: the keys of the map hold no duplicate; `genLMonoTy tvars depth` can reach each
    value; and `genNameList depth` can reach the names of the keys. -/
theorem genInputs_complete (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hnd : m.keys.Nodup)
    (hnames : m.keys.map (·.name) ∈ SPMF.support (genNameList (G := SPMF) depth))
    (hvals : ∀ ty ∈ m.values, ty ∈ SPMF.support (genLMonoTy (G := SPMF) tvars depth)) :
    m ∈ SPMF.support (genInputs (G := SPMF) tvars depth) := by
  simp only [genInputs, mem_support_bind_iff]
  exact ⟨m.keys, genIdents_complete depth m.keys hnd hnames, mapM_genInputs_complete tvars depth m hvals⟩

/-- Completeness of `genOptExpr`. The generator can always reach `none`. It can reach `some e` when
    `genLExpr` can reach `e`. -/
theorem genOptExpr_complete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy) (o : Option LExpr')
    (ho : ∀ e, o = some e → e ∈ SPMF.support (genLExpr (G := SPMF) fctx octx [] tvars [] depth τ)) :
    o ∈ SPMF.support (genOptExpr (G := SPMF) fctx octx tvars depth τ) := by
  rw [SPMF.mem_support_iff_may, genOptExpr]; walk
  cases o <;> simp_all

/-- Completeness of `genPreconditions`. The generator can always reach the empty list, through the
    `none` branch of `optionGen`. It can reach a list `[p]` of one element when `genLExpr` can reach
    `p.expr` at `.bool` over the formal parameters. The field `p.md` must be `()`, and the metadata
    type `Unit` forces that value.

    The generator can reach **no** list of two or more elements, because `genPreconditions` emits at
    most one clause. This is the reason why `genFunction_complete` takes the hypothesis
    `func.preconditions.length ≤ 1`, and does not drop the side condition about a precondition.

    The `.bool` draw in `hreach` is the branch of the `frequency` in `genPrecondition` that has no
    bias. Its weight is 1 and not 0, so the generator can really reach it, and this hypothesis is
    therefore enough. The branch that mentions an input only *adds* reachable expressions, and it
    removes none.

    This lemma is one-directional, and it names only the `.bool` branch, because that is all that
    `genFunction_complete` needs. `mem_support_genPrecondition_iff` gives the *exact* support, and it
    also covers the clauses from `genInputMentioningPrecond`. -/
theorem genPreconditions_complete (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier)
    (depth : Nat) (ps : List (Strata.DL.Util.FuncPrecondition LExpr' Unit))
    (hlen : ps.length ≤ 1)
    (hreach : ∀ p ∈ ps, p.expr ∈ SPMF.support
      (genLExpr (G := SPMF) (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool)) :
    ps ∈ SPMF.support (genPreconditions (G := SPMF) octx inputs tvars depth) := by
  rw [SPMF.mem_support_iff_may, genPreconditions, genPrecondition]; walk
  rcases ps with _ | ⟨p, _ | ⟨_, _⟩⟩
  · exact .inr rfl
  · -- Reach `p.expr` through the `.bool` draw, in both cases of the test whether `inputs.toList` is
    -- empty: the only generator with no formal parameter, the branch of weight 1 with one.
    have h := hreach p (by simp)
    refine .inl ?_; split
    · exact .inr ⟨_, h, rfl⟩
    · exact ⟨_, h, rfl⟩
  · simp at hlen

/-- The **exact** support of `genPrecondition`, as an equivalence. `genPreconditions_complete` gives
    only one direction.

    This theorem answers a natural question: does a *full* theorem of completeness need to quantify
    over the preconditions that are provable or valid, and therefore bring in undecidability? It does
    not. The support of a generator is a set of `LExpr'` *syntax trees*, and
    `FuncWF.precond_freevars` constrains a precondition only syntactically, because it asks that the
    free variables be among the names of the inputs. Nothing here mentions satisfiability, validity
    or provability, so there is no semantic quantifier that can be undecidable.

    The right side of the equivalence is a finite disjunction over the two branches of the
    `frequency`, and each part reduces to the reach of `genLExpr`. Whether *that* reach is decidable
    is a separate question about `genLExpr`, and `genLExprBase_complete` answers it. The hypotheses of
    that theorem are `HasTypeA'`, `emptyNames`, `allVarsInCtx`, `AllTypesSimple` and a bound on
    `termDepth`, and each one is syntactic. -/
theorem mem_support_genPrecondition_iff (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier)
    (depth : Nat) (o : Option (Strata.DL.Util.FuncPrecondition LExpr' Unit)) :
    o ∈ SPMF.support (genPrecondition (G := SPMF) octx inputs tvars depth)
      ↔ o = none ∨ ∃ e,
          (-- The `.bool` draw with no bias. It is available with and without a formal parameter.
           e ∈ SPMF.support (genLExpr (G := SPMF)
             (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool)
           ∨ -- The branch that mentions an input: `x == e'` for a formal parameter `(x, τ)`.
           (∃ (x : Identifier Unit) (τ : LMonoTy) (e' : LExpr'),
             (x, τ) ∈ inputs.toList ∧
             e' ∈ SPMF.support (genLExpr (G := SPMF)
               (inputsAsFVarCtx inputs) octx [] tvars [] depth τ) ∧
             e = .eq () (.fvar () x (some τ)) e'))
          ∧ o = some { expr := e, md := () } := by
  constructor
  · revert o; show IsSoundFor _ _
    rw [IsSoundFor.iff_obs, genPrecondition]
    walk [fun τ => IsSoundFor.obs (g := genLExpr (G := SPMF) (inputsAsFVarCtx inputs) octx [] tvars [] depth τ)
      fun _ h => h]
    all_goals first
      | exact .inl rfl
      | exact .inr ⟨_, .inl ‹_›, rfl⟩
      | exact .inr ⟨_, .inr ⟨_, _, _, ‹_›, ‹_›, rfl⟩, rfl⟩
  · rintro (rfl | ⟨e, hb | ⟨x, τ, e', hx, he', rfl⟩, rfl⟩)
    all_goals rw [SPMF.mem_support_iff_may, genPrecondition]; walk
    · split
      · exact .inr ⟨_, hb, rfl⟩
      · exact ⟨_, hb, rfl⟩
    · -- A clause that mentions an input forces `inputs.toList` to be not empty, because it holds `x`.
      rw [dif_pos (List.ne_nil_of_mem hx)]
      exact .inl ⟨_, hx, _, he', rfl⟩

-- ── The completeness of `genFunction` ────────────────────────────────

/-- **Completeness of `genFunction`.** The support of `genFunction` holds each well-typed function
    that meets two conditions. First, the fields that the generator does not vary hold their default
    values. Second, the smaller generators can reach its name, its types, its body and its measure,
    one part at a time.

    The hypotheses about reachability follow `hExprComplete`, `hNameReach` and `hTyReach` of
    `genCmd_complete`. They give exactly what the generator must be able to make, beyond good typing:
    - `hNameReach`: `genIdentName` can reach the name of the function and each parameter name.
    - `hTyArgsLen` and `hTyArgsReach`: the `typeArgs` list, which already holds no duplicate, is not
      longer than `depth`, and `genIdentName` can reach each of its names.
    - `hInputNamesLen` and `hInputNamesReach`: the same two conditions for the parameter names.
    - `hInputTyReach` and `hOutputReach`: `genLMonoTy` can reach the output type and each input type.
    - `hBodyReach` and `hMeasureReach`: `genLExpr` can reach the body and the measure, when the
      function has them.
    - `hPreLen` and `hPreReach`: the function has at most one `requires` clause, and `genLExpr` can
      reach its expression at `.bool` **in the context of the formal parameters**, which is
      `inputsAsFVarCtx func.inputs` and not `fctx`. A function whose precondition mentions an ambient
      variable is therefore out of reach by design, and such a function also breaks
      `FuncWF.precond_freevars`.

    `mem_support_genNameList_iff` turns the conditions about `typeArgs` and about the input names into
    concrete conditions: a bound on the length, and the reach of `genIdentName` for each name.

    The annotated specification ignores the ambient context, so `bodyTyped` gives exactly
    `HasTypeA [] body output`, and that is what the completeness of `genLExpr` needs. -/
theorem genFunction_complete (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (func : Function)
    (hwt : FuncHasTypeA C Γ func)
    -- The generator does not vary these fields, so each one must hold its default value.
    (hConstr : func.isConstr = false)
    (hRec : func.isRecursive = false)
    (hAttr : func.attr = #[])
    (hAxioms : func.axioms = [])
    -- The generator does make the preconditions, but it makes at most one clause, because
    -- `genPreconditions` emits an `Option.toList`. A longer list is therefore out of reach.
    (hPreLen : func.preconditions.length ≤ 1)
    -- The parts that the generator makes must be reachable.
    (hNameReach : func.name.name ∈ SPMF.support (genIdentName (G := SPMF)))
    (hTyArgsLen : func.typeArgs.length ≤ depth)
    (hTyArgsReach : ∀ s ∈ func.typeArgs, s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hInputNamesLen : (func.inputs.keys.map (·.name)).length ≤ depth)
    (hInputNamesReach : ∀ s ∈ func.inputs.keys.map (·.name),
      s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hInputTyReach : ∀ ty ∈ func.inputs.values,
      ty ∈ SPMF.support (genLMonoTy (G := SPMF) func.typeArgs depth))
    (hOutputReach : func.output ∈ SPMF.support (genLMonoTy (G := SPMF) func.typeArgs depth))
    (hBodyReach : ∀ b, func.body = some b →
      b ∈ SPMF.support (genLExpr (G := SPMF) fctx octx [] func.typeArgs [] depth func.output))
    (hMeasureReach : ∀ m, func.measure = some m →
      m ∈ SPMF.support (genLExpr (G := SPMF) fctx octx [] func.typeArgs [] depth .int))
    -- The generator makes a precondition over the *formal parameters*, which is
    -- `inputsAsFVarCtx`, and not over `fctx`. See `genPrecondition` and
    -- `FuncWF.precond_freevars`.
    (hPreReach : ∀ p ∈ func.preconditions, p.expr ∈ SPMF.support
      (genLExpr (G := SPMF) (inputsAsFVarCtx func.inputs) octx []
        func.typeArgs [] depth .bool)) :
    func ∈ SPMF.support (genFunction (G := SPMF) fctx octx depth) := by
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff]
  -- The witnesses are the parts of the function itself.
  refine ⟨func.name.name, hNameReach,
          func.typeArgs, ?_,
          func.inputs, ?_,
          func.output, hOutputReach,
          func.body, ?_,
          func.measure, ?_,
          func.preconditions, ?_, ?_⟩
  · -- `genTypeArgs` reaches the type arguments. They hold no duplicate, so `List.uniq` leaves
    -- them unchanged.
    exact genTypeArgs_complete depth func.typeArgs hwt.typeArgsNodup
      (mem_support_genNameList_iff depth func.typeArgs |>.mpr ⟨hTyArgsLen, hTyArgsReach⟩)
  · -- `genInputs` reaches the inputs.
    exact genInputs_complete func.typeArgs depth func.inputs
      hwt.inputsNodup
      (mem_support_genNameList_iff depth _ |>.mpr ⟨hInputNamesLen, hInputNamesReach⟩)
      hInputTyReach
  · -- `genOptExpr` reaches the body.
    exact genOptExpr_complete fctx octx func.typeArgs depth func.output func.body hBodyReach
  · -- `genOptExpr` reaches the measure.
    exact genOptExpr_complete fctx octx func.typeArgs depth .int func.measure hMeasureReach
  · -- `genPreconditions` reaches the preconditions.
    exact genPreconditions_complete octx func.inputs func.typeArgs depth
      func.preconditions hPreLen hPreReach
  · -- The record that the proof builds again equals `func`.
    obtain ⟨fname, ftyArgs, fconstr, frec, finputs, foutput, fbody, fattr,
            faxioms, fpre, fmeasure⟩ := func
    obtain ⟨nm, nmeta⟩ := fname
    simp only at hConstr hRec hAttr hAxioms ⊢
    subst hConstr hRec hAttr hAxioms
    rfl

-- ── Function-level keyword-freedom ───────────────────────────────────

/-- Every type-argument name produced by `genTypeArgs` is a non-keyword: the
    names come from `genNameList` (all non-keyword by `genNameList_not_keyword`),
    and `List.uniq` only removes elements. -/
theorem genTypeArgs_not_keyword (depth : Nat) (l : List TyIdentifier)
    (hl : l ∈ SPMF.support (genTypeArgs (G := SPMF) depth)) :
    ∀ s ∈ l, isReservedKeyword s = false := by
  simp only [genTypeArgs, mem_support_map_iff] at hl
  obtain ⟨names, hnames, rfl⟩ := hl
  intro s hs
  exact genNameList_not_keyword depth names hnames s ((List.mem_of_dedup names s).mpr hs)

/-- Every input-identifier name produced by `genIdents` is a non-keyword: each
    identifier `⟨s, ()⟩` comes from mapping over the `genNameList` names, and
    `List.uniq` only removes elements. -/
theorem genIdents_not_keyword (depth : Nat) (l : List (Identifier Unit))
    (hl : l ∈ SPMF.support (genIdents (G := SPMF) depth)) :
    ∀ x ∈ l, isReservedKeyword x.name = false := by
  simp only [genIdents, mem_support_map_iff] at hl
  obtain ⟨names, hnames, rfl⟩ := hl
  intro x hx
  -- `x ∈ (names.map ⟨·,()⟩).uniq` ⇒ `x ∈ names.map ⟨·,()⟩` ⇒ `x.name ∈ names`.
  have hx' : x ∈ names.map (fun s => (⟨s, ()⟩ : Identifier Unit)) :=
    (List.mem_of_dedup _ x).mpr hx
  obtain ⟨s, hs_mem, rfl⟩ := List.mem_map.mp hx'
  exact genNameList_not_keyword depth names hnames s hs_mem

/-- **No name of `genFunction` is a keyword.** Each name that a generated function puts at the position of an
    identifier is not a keyword, so no such name is a reserved word that the parser of Core would reject there.
    Those names are the name of the function, its type arguments and its parameter names. This lemma puts no
    condition on the body, on the measure or on a type of the function, and it is about the names at the position
    of an identifier only. -/
theorem genFunction_names_not_keyword (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (func : Function)
    (hfunc : func ∈ SPMF.support (genFunction (G := SPMF) fctx octx depth)) :
    isReservedKeyword func.name.name = false ∧
    (∀ s ∈ func.typeArgs, isReservedKeyword s = false) ∧
    (∀ x ∈ func.inputs.keys, isReservedKeyword x.name = false) := by
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff] at hfunc
  obtain ⟨name, hname, typeArgs, htypeArgs, inputs, hinputs,
          output, _houtput, body, _hbody, measure, _hmeasure,
          preconditions, _hpre, rfl⟩ := hfunc
  refine ⟨genIdentName_not_keyword name hname, genTypeArgs_not_keyword depth typeArgs htypeArgs, ?_⟩
  -- `inputs.keys = idents`, and each ident's name is non-keyword by `genIdents_not_keyword`.
  simp only [genInputs, mem_support_bind_iff] at hinputs
  obtain ⟨idents, hidents, hmap⟩ := hinputs
  obtain ⟨hkeys, _⟩ := mapM_genInputs_keys_values typeArgs depth idents inputs hmap
  rw [hkeys]
  exact genIdents_not_keyword depth idents hidents

end StrataGenerators.Function
