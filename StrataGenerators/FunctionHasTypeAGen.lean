import StrataGenerators.HasTypeAGen
import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Dedup
import StrataGenerators.FunctionHasTypeAGen.IdentName
import Strata.Languages.Core.FunctionTypeSpec

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
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

/-- Each list in the support of `genTypeArgs` holds no duplicate, because `List.dedup` builds
    it. -/
theorem genTypeArgs_nodup (depth : Nat) (l : List TyIdentifier)
    (hl : l ∈ SetGen.support (genTypeArgs (G := SetGen.Set) depth)) : l.Nodup := by
  simp only [genTypeArgs, mem_support_map_iff] at hl
  obtain ⟨names, _, rfl⟩ := hl
  exact List.nodup_dedup names

/-- Each list in the support of `genIdents` holds no duplicate, because `List.dedup` builds it. -/
theorem genIdents_nodup (depth : Nat) (l : List (Identifier Unit))
    (hl : l ∈ SetGen.support (genIdents (G := SetGen.Set) depth)) : l.Nodup := by
  simp only [genIdents, mem_support_map_iff] at hl
  obtain ⟨names, _, rfl⟩ := hl
  exact List.nodup_dedup _

-- ── A generated name is not a keyword and it holds no space ──────────
-- The `IdentName` module holds these results. Each one follows from
-- `mem_support_genIdentName_iff`, which gives the support in both directions. That module also uses
-- the same lemma to discharge the side conditions about the reachability of a name in the proofs of
-- completeness in this package. The results are `genIdentName_not_keyword`,
-- `genIdentName_no_space`, the `dodgeKeyword` lemmas, `append_underscore_not_keyword` and
-- `no_keyword_ends_underscore`. Each one is in the namespace `StrataGenerators.Function`.

set_option linter.unusedSimpArgs false in
/-- The `mapM` inside `genInputs` gives a `ListMap` whose keys are the list of input identifiers and
    each of whose values is in the support of `genLMonoTy tvars depth`. -/
theorem mapM_genInputs_keys_values (tvars : List TyIdentifier) (depth : Nat)
    (idents : List (Identifier Unit)) (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support
      (idents.mapM (m := SetGen.Set) (fun x => do
        let ty ← genLMonoTy (G := SetGen.Set) tvars depth
        pure (x, ty)))) :
    m.keys = idents ∧
    ∀ ty ∈ m.values, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth) := by
  induction idents generalizing m with
  | nil =>
    simp only [List.mapM_nil] at hm
    subst hm
    exact ⟨rfl, by intro ty hty; simp [ListMap.values] at hty⟩
  | cons x xs ih =>
    simp only [List.mapM_cons, mem_support_bind_iff, mem_support_pure_iff] at hm
    obtain ⟨pair, hpair, rest, hrest, rfl⟩ := hm
    -- The support of `genLMonoTy >>= fun ty => pure (x, ty)` holds `pair`. The `bind` and the
    -- `pure` of `Set` unfold by definition, so the proof takes `pair` apart at once.
    obtain ⟨ty, hty, rfl⟩ := hpair
    obtain ⟨hkeys_rest, hvals_rest⟩ := ih rest hrest
    refine ⟨?_, ?_⟩
    · simp only [ListMap.keys, hkeys_rest]
    · intro v hv
      simp only [ListMap.values, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hty
      · exact hvals_rest v hv

/-- What membership in the support of `genInputs tvars depth` gives. The keys of the `ListMap` are a
    list of identifiers with no duplicate, and each value is in the support of
    `genLMonoTy tvars depth`. -/
theorem genInputs_support (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support (genInputs (G := SetGen.Set) tvars depth)) :
    m.keys.Nodup ∧ ∀ ty ∈ m.values, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth) := by
  simp only [genInputs, mem_support_bind_iff] at hm
  obtain ⟨idents, hidents, hm⟩ := hm
  have hnd := genIdents_nodup depth idents hidents
  obtain ⟨hkeys, hvals⟩ := mapM_genInputs_keys_values tvars depth idents m hm
  exact ⟨hkeys ▸ hnd, hvals⟩

/-- `genIdentName` can reach the `name` of each key of a signature that `genInputs` gives. The keys
    are the list of identifiers after `List.dedup`, their names come from `genNameList`, and
    `genNameList` takes each name from `genIdentName`. -/
theorem genInputs_key_name_reachable (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support (genInputs (G := SetGen.Set) tvars depth))
    (k : Identifier Unit) (hk : k ∈ m.keys) :
    k.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
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
    (hm : m ∈ SetGen.support (genInputs (G := SetGen.Set) tvars depth))
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
    (ho : o ∈ SetGen.support (genOptExpr (G := SetGen.Set) fctx octx tvars depth τ pctx))
    (e : LExpr') (heq : o = some e) :
    HasTypeA' [] e τ := by
  simp only [genOptExpr,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)] at ho
  rcases ho with hnone | ⟨e', he', ho⟩
  · -- The `none` branch contradicts `o = some e`.
    exact absurd (heq ▸ hnone) (by simp)
  · -- In the `some e'` branch, `e'` is well-typed and `e'` equals `e`.
    subst heq
    have hee : e' = e := (Option.some.inj ho).symm
    subst hee
    exact genLExpr_sound fctx octx pctx tvars [] depth τ _ e' he'

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
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth pctx)) :
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

/-- Soundness of `genFunction` at an empty operator context. This is a special case of
    `genFunction_sound`, which needs no condition on `octx`. -/
theorem genFunction_sound_nil (fctx : FVarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit) (hC : SimpleTyArities C)
    (func : Function)
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx ∅ depth)) :
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
    l ∈ SetGen.support (genNameList (G := SetGen.Set) depth) ↔
      l.length ≤ depth ∧ ∀ s ∈ l, s ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  simp only [genNameList, mem_support_listOfMaxLength_iff]

/-- No name in a list that `genNameList` gives is a keyword. The proof carries
    `genIdentName_not_keyword` through the support of `genNameList`, which holds for each element. -/
theorem genNameList_not_keyword (depth : Nat) (l : List String)
    (hl : l ∈ SetGen.support (genNameList (G := SetGen.Set) depth)) :
    ∀ s ∈ l, isReservedKeyword s = false := fun s hs =>
  genIdentName_not_keyword s ((mem_support_genNameList_iff depth l |>.mp hl).2 s hs)

set_option linter.unusedSimpArgs false in
/-- The converse of `mapM_genInputs_keys_values`. Take a `ListMap` such that
    `genLMonoTy tvars depth` can reach each of its values. The support of the `mapM` inside
    `genInputs`, over the keys of that map, then holds the map. -/
theorem mapM_genInputs_complete (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hvals : ∀ ty ∈ m.values, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth)) :
    m ∈ SetGen.support
      (m.keys.mapM (m := SetGen.Set) (fun x => do
        let ty ← genLMonoTy (G := SetGen.Set) tvars depth
        pure (x, ty))) := by
  induction m with
  | nil =>
    show [] ∈ SetGen.support (pure [] : SetGen.Set _)
    rw [mem_support_pure_iff]
  | cons p rest ih =>
    obtain ⟨x, ty⟩ := p
    simp only [ListMap.keys, List.mapM_cons, mem_support_bind_iff]
    have hty : ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth) :=
      hvals ty (by simp [ListMap.values])
    have hrest : ∀ ty' ∈ ListMap.values rest,
        ty' ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth) := by
      intro ty' hty'; exact hvals ty' (by simp only [ListMap.values, List.mem_cons]; exact Or.inr hty')
    refine ⟨(x, ty), ⟨ty, hty, rfl⟩, rest, ih hrest, rfl⟩

/-- `genIdents depth` can reach a list of identifiers `ids` that holds no duplicate, if
    `genNameList depth` can reach the list of names `ids.map (·.name)`. -/
theorem genIdents_complete (depth : Nat) (ids : List (Identifier Unit))
    (hnd : ids.Nodup)
    (hnames : ids.map (·.name) ∈ SetGen.support (genNameList (G := SetGen.Set) depth)) :
    ids ∈ SetGen.support (genIdents (G := SetGen.Set) depth) := by
  simp only [genIdents, mem_support_map_iff]
  refine ⟨ids.map (·.name), hnames, ?_⟩
  -- The map back over the names gives `ids` again, because the metadata of an `Identifier Unit` is
  -- `()`. `List.dedup` then leaves the list unchanged.
  have hmapeq : (ids.map (·.name)).map (fun s => (⟨s, ()⟩ : Identifier Unit)) = ids := by
    clear hnames hnd
    induction ids with
    | nil => rfl
    | cons a as ih =>
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih⟩; obtain ⟨n, u⟩ := a; trivial
  rw [hmapeq, dedup_eq_self ids hnd]

/-- `genTypeArgs depth` can reach a list of type arguments `l` that holds no duplicate, if
    `genNameList depth` can reach `l`. -/
theorem genTypeArgs_complete (depth : Nat) (l : List TyIdentifier)
    (hnd : l.Nodup)
    (hnames : l ∈ SetGen.support (genNameList (G := SetGen.Set) depth)) :
    l ∈ SetGen.support (genTypeArgs (G := SetGen.Set) depth) := by
  simp only [genTypeArgs, mem_support_map_iff]
  exact ⟨l, hnames, (dedup_eq_self l hnd).symm⟩

/-- Completeness of `genInputs`. The support of `genInputs tvars depth` holds a `ListMap` when three
    conditions hold: the keys of the map hold no duplicate; `genLMonoTy tvars depth` can reach each
    value; and `genNameList depth` can reach the names of the keys. -/
theorem genInputs_complete (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hnd : m.keys.Nodup)
    (hnames : m.keys.map (·.name) ∈ SetGen.support (genNameList (G := SetGen.Set) depth))
    (hvals : ∀ ty ∈ m.values, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth)) :
    m ∈ SetGen.support (genInputs (G := SetGen.Set) tvars depth) := by
  simp only [genInputs, mem_support_bind_iff]
  exact ⟨m.keys, genIdents_complete depth m.keys hnd hnames, mapM_genInputs_complete tvars depth m hvals⟩

/-- Completeness of `genOptExpr`. The generator can always reach `none`. It can reach `some e` when
    `genLExpr` can reach `e`. -/
theorem genOptExpr_complete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy) (o : Option LExpr')
    (ho : ∀ e, o = some e → e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ)) :
    o ∈ SetGen.support (genOptExpr (G := SetGen.Set) fctx octx tvars depth τ) := by
  simp only [genOptExpr,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)]
  cases o with
  | none =>
    -- The generator can always reach `none`.
    exact Or.inl rfl
  | some e =>
    -- The generator can reach `some e`, because `genLExpr` can reach `e`.
    exact Or.inr ⟨e, ho e rfl, rfl⟩

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
    (hreach : ∀ p ∈ ps, p.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool)) :
    ps ∈ SetGen.support (genPreconditions (G := SetGen.Set) octx inputs tvars depth) := by
  simp only [genPreconditions, genPrecondition, mem_support_map_iff,
    mem_support_optionGen_iff]
  match ps with
  | [] =>
    -- `[]` is `Option.toList none`, and the support of `optionGen` always holds `none`.
    exact ⟨none, Or.inl rfl, rfl⟩
  | [p] =>
    -- `[p]` is `Option.toList (some p)`, and `p.expr` gives the reach of `some p`.
    refine ⟨some p, Or.inr ⟨p, ?_, rfl⟩, rfl⟩
    -- Reach `p.expr` through the `.bool` draw, in both cases of the test whether `inputs.toList` is
    -- empty. That draw is the only generator when there is no formal parameter, and it is the branch
    -- of weight 1 in the `frequency` when there is one.
    have hbody : ∀ g : SetGen.Set LExpr',
        p.expr ∈ SetGen.support g →
        p ∈ SetGen.support (do let y ← g; pure ({ expr := y, md := () } :
          Strata.DL.Util.FuncPrecondition LExpr' Unit)) := by
      intro g hg
      simp only [mem_support_bind_iff, mem_support_pure_iff]
      refine ⟨p.expr, hg, ?_⟩
      -- The proof builds the record again from `p.expr` and the one value of `Unit`.
      obtain ⟨e, md⟩ := p
      rfl
    by_cases hne : inputs.toList ≠ []
    · rw [dif_pos hne]
      refine hbody _ ?_
      rw [mem_support_frequency_iff]
      refine ⟨1, fun _ => genLExpr (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool,
        by simp, by omega, hreach p (by simp)⟩
    · rw [dif_neg hne]
      exact hbody _ (hreach p (by simp))
  | _ :: _ :: _ =>
    -- `hlen` excludes this case.
    simp at hlen

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
    o ∈ SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth)
      ↔ o = none ∨ ∃ e,
          (-- The `.bool` draw with no bias. It is available with and without a formal parameter.
           e ∈ SetGen.support (genLExpr (G := SetGen.Set)
             (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool)
           ∨ -- The branch that mentions an input: `x == e'` for a formal parameter `(x, τ)`.
           (∃ (x : Identifier Unit) (τ : LMonoTy) (e' : LExpr'),
             (x, τ) ∈ inputs.toList ∧
             e' ∈ SetGen.support (genLExpr (G := SetGen.Set)
               (inputsAsFVarCtx inputs) octx [] tvars [] depth τ) ∧
             e = .eq () (.fvar () x (some τ)) e'))
          ∧ o = some { expr := e, md := () } := by
  simp only [genPrecondition, mem_support_optionGen_iff]
  constructor
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · exact Or.inl rfl
    refine Or.inr ⟨p.expr, ?_, ?_⟩
    · by_cases hne : inputs.toList ≠ []
      · rw [dif_pos hne, mem_support_bind_iff] at hp
        obtain ⟨e, he, hpe⟩ := hp
        rw [mem_support_pure_iff] at hpe
        have hexpr : p.expr = e := by subst hpe; rfl
        rw [mem_support_frequency_iff] at he
        obtain ⟨w, g, hmem, _, hg⟩ := he
        -- The `frequency` list holds two branches, and `simp` splits the membership.
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · -- The branch that mentions an input.
          rw [genInputMentioningPrecond, mem_support_bind_iff] at hg
          obtain ⟨⟨x, τ⟩, hxmem, hrest⟩ := hg
          rw [mem_support_bind_iff] at hrest
          obtain ⟨e', he', heq⟩ := hrest
          rw [mem_support_pure_iff] at heq
          rw [mem_support_elements_iff] at hxmem
          exact Or.inr ⟨x, τ, e', hxmem, he', by rw [hexpr, ← heq]⟩
        · -- The `.bool` branch with no bias.
          exact Or.inl (hexpr ▸ hg)
      · rw [dif_neg hne, mem_support_bind_iff] at hp
        obtain ⟨e, he, hpe⟩ := hp
        rw [mem_support_pure_iff] at hpe
        exact Or.inl (by rw [show p.expr = e by subst hpe; rfl]; exact he)
    · obtain ⟨e, md⟩ := p; rfl
  · rintro (rfl | ⟨e, hbranch, rfl⟩)
    · exact Or.inl rfl
    refine Or.inr ⟨{ expr := e, md := () }, ?_, rfl⟩
    have hpure : ∀ g : SetGen.Set LExpr', e ∈ SetGen.support g →
        ({ expr := e, md := () } : Strata.DL.Util.FuncPrecondition LExpr' Unit) ∈
          SetGen.support (do let y ← g; pure ({ expr := y, md := () } :
            Strata.DL.Util.FuncPrecondition LExpr' Unit)) := by
      intro g hg
      rw [mem_support_bind_iff]
      exact ⟨e, hg, by rw [mem_support_pure_iff]⟩
    rcases hbranch with hbool | ⟨x, τ, e', hxmem, he', rfl⟩
    · by_cases hne : inputs.toList ≠ []
      · rw [dif_pos hne]
        refine hpure _ ?_
        rw [mem_support_frequency_iff]
        exact ⟨1, fun _ => genLExpr (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool,
          by simp, by omega, hbool⟩
      · rw [dif_neg hne]; exact hpure _ hbool
    · -- A clause that mentions an input forces `inputs.toList` to be not empty, because it holds `x`.
      have hne : inputs.toList ≠ [] := by
        intro h; rw [h] at hxmem; simp at hxmem
      rw [dif_pos hne]
      refine hpure _ ?_
      rw [mem_support_frequency_iff]
      refine ⟨3, fun _ => genInputMentioningPrecond octx inputs tvars depth hne,
        by simp, by omega, ?_⟩
      rw [genInputMentioningPrecond, mem_support_bind_iff]
      refine ⟨(x, τ), by rw [mem_support_elements_iff]; exact hxmem, ?_⟩
      rw [mem_support_bind_iff]
      exact ⟨e', he', by rw [mem_support_pure_iff]⟩

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
    (hNameReach : func.name.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hTyArgsLen : func.typeArgs.length ≤ depth)
    (hTyArgsReach : ∀ s ∈ func.typeArgs, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hInputNamesLen : (func.inputs.keys.map (·.name)).length ≤ depth)
    (hInputNamesReach : ∀ s ∈ func.inputs.keys.map (·.name),
      s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hInputTyReach : ∀ ty ∈ func.inputs.values,
      ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) func.typeArgs depth))
    (hOutputReach : func.output ∈ SetGen.support (genLMonoTy (G := SetGen.Set) func.typeArgs depth))
    (hBodyReach : ∀ b, func.body = some b →
      b ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] func.typeArgs [] depth func.output))
    (hMeasureReach : ∀ m, func.measure = some m →
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] func.typeArgs [] depth .int))
    -- The generator makes a precondition over the *formal parameters*, which is
    -- `inputsAsFVarCtx`, and not over `fctx`. See `genPrecondition` and
    -- `FuncWF.precond_freevars`.
    (hPreReach : ∀ p ∈ func.preconditions, p.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (inputsAsFVarCtx func.inputs) octx []
        func.typeArgs [] depth .bool)) :
    func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth) := by
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff]
  -- The witnesses are the parts of the function itself.
  refine ⟨func.name.name, hNameReach,
          func.typeArgs, ?_,
          func.inputs, ?_,
          func.output, hOutputReach,
          func.body, ?_,
          func.measure, ?_,
          func.preconditions, ?_, ?_⟩
  · -- `genTypeArgs` reaches the type arguments. They hold no duplicate, so `List.dedup` leaves
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
    and `List.dedup` only removes elements. -/
theorem genTypeArgs_not_keyword (depth : Nat) (l : List TyIdentifier)
    (hl : l ∈ SetGen.support (genTypeArgs (G := SetGen.Set) depth)) :
    ∀ s ∈ l, isReservedKeyword s = false := by
  simp only [genTypeArgs, mem_support_map_iff] at hl
  obtain ⟨names, hnames, rfl⟩ := hl
  intro s hs
  exact genNameList_not_keyword depth names hnames s ((List.mem_of_dedup names s).mpr hs)

/-- Every input-identifier name produced by `genIdents` is a non-keyword: each
    identifier `⟨s, ()⟩` comes from mapping over the `genNameList` names, and
    `List.dedup` only removes elements. -/
theorem genIdents_not_keyword (depth : Nat) (l : List (Identifier Unit))
    (hl : l ∈ SetGen.support (genIdents (G := SetGen.Set) depth)) :
    ∀ x ∈ l, isReservedKeyword x.name = false := by
  simp only [genIdents, mem_support_map_iff] at hl
  obtain ⟨names, hnames, rfl⟩ := hl
  intro x hx
  -- `x ∈ (names.map ⟨·,()⟩).dedup` ⇒ `x ∈ names.map ⟨·,()⟩` ⇒ `x.name ∈ names`.
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
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth)) :
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
