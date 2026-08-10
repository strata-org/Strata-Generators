import StrataGenerators.HasTypeAGen
import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Dedup
import StrataGenerators.FunctionHasTypeAGen.IdentName
import Strata.Languages.Core.FunctionTypeSpec

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Dedup

/-!
# Soundness and completeness of `genFunction`

`genFunction` (in `FunctionHasTypeAGen/Core.lean`) generates random Strata Core
functions (`Function = LFunc CoreLParams`). This file proves it sound and
complete with respect to the `FuncHasTypeA` typing relation of
`Strata.Languages.Core.FunctionTypeSpec`.

## Key simplification (vs. commands)

The annotated typing spec `instHasTypeA` used by `FuncHasTypeA` *ignores* the
ambient typing context:

```
instance instHasTypeA : ExprTypingSpec LMonoTy where
  embed := id
  exprTyped := fun _C _Γ e mty => LExpr.HasTypeA [] e mty
```

So the two obligations `bodyTyped`/`measureTyped` reduce *definitionally* to
`LExpr.HasTypeA [] body output` and `LExpr.HasTypeA [] m .int`, which is exactly
what `genLExpr … [] tvars [] depth τ` produces. No `VarCtx ↔ TContext`
correspondence is needed.

## Contents

- Free-variable helpers relating `allFtvarsIn` / `mkArrow'` to `LMonoTy.freeVars`.
- `genFunction_sound` — every generated function satisfies `FuncHasTypeA`.
- `genFunction_complete` — every well-typed function (satisfying the expression
  reachability side conditions) is in `genFunction`'s support.
-/

namespace StrataGenerators.Function

-- ── Free-variable helpers ────────────────────────────────────────────

/-- If `v ∈ LMonoTys.freeVars tys`, then some element of `tys` contains `v`.

    Strata proves this as `Lambda.LMonoTys.freeVars_exists`, but it lives in
    `Strata.DL.Lambda.LTyProps`, which has no `public section`, so it is only
    reachable via `import all` — illegal from this non-`module` file. The proof
    is three lines from the public `LMonoTys.freeVars_of_cons`, so we reprove it
    locally rather than widen Strata's visibility. -/
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

/-- `allFtvarsIn tvars τ` says every ftvar in `τ` is drawn from `tvars`; this is
    exactly the `noUndeclaredVars`-style statement phrased via `LMonoTy.freeVars`. -/
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
    -- `allFtvarsIn tvars (.tcons name args)` unfolds to a per-argument statement
    have hargs : ∀ a ∈ args, allFtvarsIn tvars a := by unfold allFtvarsIn at h; exact h
    -- reduce membership in `LMonoTys.freeVars` to some element containing `v`
    obtain ⟨ty, hty_mem, hv_ty⟩ := freeVars_exists' hv
    exact ih ty hty_mem (hargs ty hty_mem) v hv_ty

set_option linter.unusedSimpArgs false in
/-- Free variables of `mkArrow' out vals` split into those of `out` and those of
    some element of `vals`. -/
theorem freeVars_mkArrow' (out : LMonoTy) (vals : List LMonoTy) (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' out vals)) :
    v ∈ LMonoTy.freeVars out ∨ ∃ t ∈ vals, v ∈ LMonoTy.freeVars t := by
  induction vals with
  | nil =>
    left
    rwa [LMonoTy.mkArrow'_nil] at hv
  | cons t rest ih =>
    rw [LMonoTy.mkArrow'_cons] at hv
    -- `.arrow t (mkArrow' out rest)` is `.tcons "arrow" [t, mkArrow' out rest]`
    simp only [LMonoTy.arrow, LMonoTy.freeVars, LMonoTys.freeVars_of_cons,
               LMonoTys.freeVars, List.append_nil, List.mem_append] at hv
    rcases hv with hvt | hvrest
    · exact Or.inr ⟨t, List.mem_cons_self, hvt⟩
    · rcases ih hvrest with hout | ⟨t', ht'_mem, hv'⟩
      · exact Or.inl hout
      · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht'_mem, hv'⟩

-- ── Support of the name/typeArg/input sub-generators ─────────────────

/-- Any list in the support of `genTypeArgs` is `Nodup` (it is `List.dedup`ped). -/
theorem genTypeArgs_nodup (depth : Nat) (l : List TyIdentifier)
    (hl : l ∈ SetGen.support (genTypeArgs (G := SetGen.Set) depth)) : l.Nodup := by
  simp only [genTypeArgs, mem_support_map_iff] at hl
  obtain ⟨names, _, rfl⟩ := hl
  exact nodup_dedup names

/-- Any list in the support of `genIdents` is `Nodup` (it is `List.dedup`ped). -/
theorem genIdents_nodup (depth : Nat) (l : List (Identifier Unit))
    (hl : l ∈ SetGen.support (genIdents (G := SetGen.Set) depth)) : l.Nodup := by
  simp only [genIdents, mem_support_map_iff] at hl
  obtain ⟨names, _, rfl⟩ := hl
  exact nodup_dedup _

-- ── Keyword-freedom and space-freedom of generated names ─────────────
-- `FunctionHasTypeAGen/IdentName.lean` holds these results. They are corollaries
-- of `mem_support_genIdentName_iff`, the support lemma in both directions. That
-- file also uses the lemma to discharge the side conditions on name reachability
-- in the completeness proofs of this package. The results are
-- `genIdentName_not_keyword`, `genIdentName_no_space`, `dodgeKeyword_*`,
-- `append_underscore_not_keyword` and `no_keyword_ends_underscore`, all in the
-- namespace `StrataGenerators.Function`.

set_option linter.unusedSimpArgs false in
/-- The `mapM` inside `genInputs` produces a `ListMap` whose keys are exactly the
    input ident list and whose values are each in `genLMonoTy tvars depth`. -/
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
    -- `pair ∈ support (genLMonoTy >>= fun ty => pure (x, ty))`; `Set.bind`/`pure`
    -- unfold definitionally, so we can destructure directly.
    obtain ⟨ty, hty, rfl⟩ := hpair
    obtain ⟨hkeys_rest, hvals_rest⟩ := ih rest hrest
    refine ⟨?_, ?_⟩
    · simp only [ListMap.keys, hkeys_rest]
    · intro v hv
      simp only [ListMap.values, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hty
      · exact hvals_rest v hv

/-- Membership in `genInputs tvars depth`: the resulting `ListMap`'s keys are a
    `Nodup` ident list and every value is in the support of `genLMonoTy tvars depth`. -/
theorem genInputs_support (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support (genInputs (G := SetGen.Set) tvars depth)) :
    m.keys.Nodup ∧ ∀ ty ∈ m.values, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth) := by
  simp only [genInputs, mem_support_bind_iff] at hm
  obtain ⟨idents, hidents, hm⟩ := hm
  have hnd := genIdents_nodup depth idents hidents
  obtain ⟨hkeys, hvals⟩ := mapM_genInputs_keys_values tvars depth idents m hm
  exact ⟨hkeys ▸ hnd, hvals⟩

/-- Every key of a `genInputs`-generated signature has its underlying `name`
    reachable by `genIdentName`: the keys are the (deduped) identifier list, whose
    names come from `genNameList`, i.e. each from `genIdentName`. -/
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
  rw [StrataGenerators.Dedup.mem_dedup] at hk
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hk
  rw [genNameList, mem_support_listOfMaxLength_iff] at hnames
  exact hnames.2 s hs

/-- Every key of a `genInputs`-generated signature is space-free (its `name`'s
    character list contains no `' '`). Combines `genInputs_key_name_reachable` with
    `genIdentName_no_space`. This is the fact that separates generated parameter
    names from `CoreIdent.mkOld` keys (`"old " ++ …`), keeping the in-out body
    seed `Functional`. -/
theorem genInputs_key_no_space (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support (genInputs (G := SetGen.Set) tvars depth))
    (k : Identifier Unit) (hk : k ∈ m.keys) :
    ' ' ∉ k.name.toList :=
  genIdentName_no_space k.name (genInputs_key_name_reachable tvars depth m hm k hk)

-- ── Optional-expression soundness ───────────────────────────────────

/-- With an empty polymorphic-op context, `polyOpsForResult` is always empty, so
    the `hSimplePolyOps` side-condition of `genLExpr_sound` is vacuous. -/
theorem polyOpsForResult_nil (τ : LMonoTy) (generableTys sampledTys : List LMonoTy) :
    findPolymorphicOps [] τ generableTys sampledTys = [] := by
  simp [findPolymorphicOps]

/-- Soundness of `genOptExpr`: any `some e` it produces is well-typed at `τ`
    (empty bvar context). The `none` case is vacuous. -/
theorem genOptExpr_sound (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy)
    (o : Option LExpr')
    (ho : o ∈ SetGen.support (genOptExpr (G := SetGen.Set) fctx octx tvars depth τ))
    (e : LExpr') (heq : o = some e) :
    HasTypeA' [] e τ := by
  simp only [genOptExpr,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)] at ho
  rcases ho with hnone | ⟨e', he', ho⟩
  · -- `none` branch: contradicts `o = some e`
    exact absurd (heq ▸ hnone) (by simp)
  · -- `some e'` branch: `e'` is well-typed and `e' = e`
    subst heq
    have hee : e' = e := (Option.some.inj ho).symm
    subst hee
    exact genLExpr_sound fctx octx [] tvars [] depth τ _ e' he'

-- ── Soundness of genFunction ─────────────────────────────────────────

/-- **Soundness of `genFunction`.** Every function in the generator's support is
    well-typed w.r.t. `FuncHasTypeA` for *any* ambient context `Γ` (the annotated
    spec ignores it) and *any* operator context — `genLExpr_sound` is now
    unconditional. -/
theorem genFunction_sound (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (func : Function)
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth)) :
    FuncHasTypeA C Γ func := by
  -- Expose the components generated for each field.
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff] at hfunc
  -- (`preconditions` is generated too, but `FuncHasType'` has no precondition
  -- field, so its reachability witness `_hpre` is simply unused here.)
  obtain ⟨name, _hname, typeArgs, htypeArgs, inputs, hinputs,
          output, houtput, body, hbody, measure, hmeasure,
          preconditions, _hpre, rfl⟩ := hfunc
  -- Facts about the generated typeArgs / inputs.
  have htyNodup : typeArgs.Nodup := genTypeArgs_nodup depth typeArgs htypeArgs
  obtain ⟨hkeysNodup, hvals⟩ := genInputs_support typeArgs depth inputs hinputs
  have houtputFtv : allFtvarsIn typeArgs output :=
    (genLMonoTy_support typeArgs depth output |>.mp houtput).2.2
  -- Build the `FuncHasType'` structure.
  refine ⟨hkeysNodup, htyNodup, ?_, ?_, ?_⟩
  · -- noUndeclaredVars
    intro v hv
    rcases freeVars_mkArrow' output inputs.values v hv with hout | ⟨t, ht_mem, hvt⟩
    · exact allFtvarsIn_freeVars houtputFtv v hout
    · -- t is one of the input values, hence in genLMonoTy's support ⇒ allFtvarsIn
      have ht_supp := hvals t ht_mem
      have ht_ftv : allFtvarsIn typeArgs t :=
        (genLMonoTy_support typeArgs depth t |>.mp ht_supp).2.2
      exact allFtvarsIn_freeVars ht_ftv v hvt
  · -- bodyTyped
    intro b hb
    exact genOptExpr_sound fctx octx typeArgs depth output body hbody b hb
  · -- measureTyped
    intro m hm _
    exact genOptExpr_sound fctx octx typeArgs depth .int measure hmeasure m hm

/-- Hypothesis-free soundness of `genFunction` at an empty operator context.
    (Now a special case of `genFunction_sound`, which is unconditional in `octx`.) -/
theorem genFunction_sound_nil (fctx : FVarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (func : Function)
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx [] depth)) :
    FuncHasTypeA C Γ func :=
  genFunction_sound fctx [] depth C Γ func hfunc

-- ── Completeness helpers ─────────────────────────────────────────────

/-- Support of `genNameList`, inherited from `listOfMaxLength`: a list is
    reachable iff it has length ≤ `depth` and every name is reachable by
    `genIdentName`. This concretizes the opaque `∈ support (genNameList …)`
    reachability side-conditions of `genFunction_complete`.

    (The remaining `∈ support genIdentName` per-name obligation is the
    residual bottleneck noted in `docs/vectorof-listofmaxlength-integration.md`
    §4/§5 — it awaits a public two-directional `genIdentName` support lemma.) -/
theorem mem_support_genNameList_iff (depth : Nat) (l : List String) :
    l ∈ SetGen.support (genNameList (G := SetGen.Set) depth) ↔
      l.length ≤ depth ∧ ∀ s ∈ l, s ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  simp only [genNameList, mem_support_listOfMaxLength_iff]

/-- Every name in a list produced by `genNameList` is a non-keyword (lifts
    `genIdentName_not_keyword` through the element-wise `genNameList` support). -/
theorem genNameList_not_keyword (depth : Nat) (l : List String)
    (hl : l ∈ SetGen.support (genNameList (G := SetGen.Set) depth)) :
    ∀ s ∈ l, isReservedKeyword s = false := fun s hs =>
  genIdentName_not_keyword s ((mem_support_genNameList_iff depth l |>.mp hl).2 s hs)

set_option linter.unusedSimpArgs false in
/-- Reverse of `mapM_genInputs_keys_values`: a `ListMap` whose every value is
    reachable by `genLMonoTy tvars depth` is itself in the support of the `mapM`
    inside `genInputs`, run over its own keys. -/
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

/-- A `Nodup` list of identifiers `ids` is reachable by `genIdents depth` provided
    the underlying name list `ids.map (·.name)` is reachable by `genNameList depth`. -/
theorem genIdents_complete (depth : Nat) (ids : List (Identifier Unit))
    (hnd : ids.Nodup)
    (hnames : ids.map (·.name) ∈ SetGen.support (genNameList (G := SetGen.Set) depth)) :
    ids ∈ SetGen.support (genIdents (G := SetGen.Set) depth) := by
  simp only [genIdents, mem_support_map_iff]
  refine ⟨ids.map (·.name), hnames, ?_⟩
  -- (ids.map (·.name)).map ⟨·, ()⟩ = ids  (by eta on Identifier Unit), then dedup fixed point.
  have hmapeq : (ids.map (·.name)).map (fun s => (⟨s, ()⟩ : Identifier Unit)) = ids := by
    clear hnames hnd
    induction ids with
    | nil => rfl
    | cons a as ih =>
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih⟩; obtain ⟨n, u⟩ := a; trivial
  rw [hmapeq, dedup_eq_self ids hnd]

/-- A `Nodup` list of type args `l` is reachable by `genTypeArgs depth` provided
    `l` is reachable by `genNameList depth`. -/
theorem genTypeArgs_complete (depth : Nat) (l : List TyIdentifier)
    (hnd : l.Nodup)
    (hnames : l ∈ SetGen.support (genNameList (G := SetGen.Set) depth)) :
    l ∈ SetGen.support (genTypeArgs (G := SetGen.Set) depth) := by
  simp only [genTypeArgs, mem_support_map_iff]
  exact ⟨l, hnames, (dedup_eq_self l hnd).symm⟩

/-- Completeness of `genInputs`: a `ListMap` with `Nodup` keys, values reachable
    by `genLMonoTy tvars depth`, and underlying key-names reachable by
    `genNameList depth`, is in the support of `genInputs tvars depth`. -/
theorem genInputs_complete (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hnd : m.keys.Nodup)
    (hnames : m.keys.map (·.name) ∈ SetGen.support (genNameList (G := SetGen.Set) depth))
    (hvals : ∀ ty ∈ m.values, ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth)) :
    m ∈ SetGen.support (genInputs (G := SetGen.Set) tvars depth) := by
  simp only [genInputs, mem_support_bind_iff]
  exact ⟨m.keys, genIdents_complete depth m.keys hnd hnames, mapM_genInputs_complete tvars depth m hvals⟩

/-- Completeness of `genOptExpr`. `none` is always reachable; `some e` is
    reachable when `e` is reachable by `genLExpr`. -/
theorem genOptExpr_complete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy) (o : Option LExpr')
    (ho : ∀ e, o = some e → e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ)) :
    o ∈ SetGen.support (genOptExpr (G := SetGen.Set) fctx octx tvars depth τ) := by
  simp only [genOptExpr,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)]
  cases o with
  | none =>
    -- `none` is always reachable
    exact Or.inl rfl
  | some e =>
    -- `some e` is reachable because `e` is reachable by `genLExpr`
    exact Or.inr ⟨e, ho e rfl, rfl⟩

/-- Completeness of `genPreconditions`. The empty list is always reachable (the
    `none` branch of `optionGen`); a *singleton* `[p]` is reachable when `p.expr`
    is reachable by `genLExpr` at `.bool` over the formals, and `p.md = ()`
    (forced, since the metadata type is `Unit`).

    Lists of length ≥ 2 are **not** reachable — `genPreconditions` emits at most
    one clause — which is why `genFunction_complete` carries a
    `func.preconditions.length ≤ 1` hypothesis rather than dropping the
    precondition side condition entirely.

    The `.bool` draw named in `hreach` is the *unbiased* branch of
    `genPrecondition`'s `frequency`. It carries weight 1 (not 0), so it is genuinely
    reachable and this hypothesis remains sufficient: the input-mentioning branch
    added for the "prefer inputs" bias only *adds* reachable expressions, it removes
    none.

    This lemma is deliberately one-directional and mentions only the `.bool` branch,
    because that is all `genFunction_complete` needs. For the *exact* support —
    including the `genInputMentioningPrecond` clauses — see
    `mem_support_genPrecondition_iff`, which is a genuine iff. -/
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
    -- `[] = Option.toList none`, and `none` is always in `optionGen`'s support.
    exact ⟨none, Or.inl rfl, rfl⟩
  | [p] =>
    -- `[p] = Option.toList (some p)`; `some p` is reachable via `p.expr`.
    refine ⟨some p, Or.inr ⟨p, ?_, rfl⟩, rfl⟩
    -- Reach `p.expr` through the `.bool` draw, on both sides of the
    -- `inputs.toList ≠ []` split: it is the sole generator when there are no
    -- formals, and the weight-1 branch of the `frequency` when there are.
    have hbody : ∀ g : SetGen.Set LExpr',
        p.expr ∈ SetGen.support g →
        p ∈ SetGen.support (do let y ← g; pure ({ expr := y, md := () } :
          Strata.DL.Util.FuncPrecondition LExpr' Unit)) := by
      intro g hg
      simp only [mem_support_bind_iff, mem_support_pure_iff]
      refine ⟨p.expr, hg, ?_⟩
      -- The record is rebuilt from `p.expr` and the unique `Unit` metadata.
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
    -- Excluded by `hlen`.
    simp at hlen

/-- **Exact** characterization of `genPrecondition`'s support: an iff, not just the
    one-directional `genPreconditions_complete`.

    Worth stating explicitly because it settles a natural worry — that a *full*
    completeness theorem would have to quantify over the "provable" or "valid"
    preconditions and so drag in undecidability. It does not. The support of a
    generator is a set of `LExpr'` *syntax trees*, and `FuncWF.precond_freevars`
    (`Func.lean:120`) constrains preconditions only syntactically (free variables ⊆
    input names). Nothing here mentions satisfiability, validity, or provability, so
    there is no semantic quantifier to be undecidable about.

    The right-hand side is a finite disjunction over the two `frequency` branches,
    each reduced to `genLExpr` reachability. Whether *that* is decidable is a
    separate question about `genLExpr`, already answered by `genLExprBase_complete`
    (whose hypotheses — `HasTypeA'`, `emptyNames`, `allVarsInCtx`, `AllTypesSimple`,
    `termDepth ≤ depth` — are all syntactic). -/
theorem mem_support_genPrecondition_iff (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier)
    (depth : Nat) (o : Option (Strata.DL.Util.FuncPrecondition LExpr' Unit)) :
    o ∈ SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth)
      ↔ o = none ∨ ∃ e,
          (-- the unbiased `.bool` draw, available whether or not there are formals
           e ∈ SetGen.support (genLExpr (G := SetGen.Set)
             (inputsAsFVarCtx inputs) octx [] tvars [] depth .bool)
           ∨ -- the input-mentioning branch: `x == e'` for a formal `(x, τ)`
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
        -- Two branches in the `frequency` list; `simp` splits the membership.
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · -- input-mentioning branch
          rw [genInputMentioningPrecond, mem_support_bind_iff] at hg
          obtain ⟨⟨x, τ⟩, hxmem, hrest⟩ := hg
          rw [mem_support_bind_iff] at hrest
          obtain ⟨e', he', heq⟩ := hrest
          rw [mem_support_pure_iff] at heq
          rw [mem_support_elements_iff] at hxmem
          exact Or.inr ⟨x, τ, e', hxmem, he', by rw [hexpr, ← heq]⟩
        · -- unbiased `.bool` branch
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
    · -- an input-mentioning clause forces `inputs.toList ≠ []` (it contains `x`)
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

-- ── Completeness of genFunction ──────────────────────────────────────

/-- **Completeness of `genFunction`.** Every well-typed function that (a) has the
    default values for the fields the generator does not vary and (b) whose
    name/types/body/measure are individually reachable by the corresponding
    sub-generators, is in `genFunction`'s support.

    The reachability hypotheses mirror `genCmd_complete`'s `hExprComplete` /
    `hNameReach` / `hTyReach`: they capture exactly what the generator must be
    able to produce beyond well-typedness. Concretely:
    - `hNameReach` — the function name and the parameter names are reachable
      identifier strings (needed by `genIdentName`);
    - `hTyArgsLen` / `hTyArgsReach` — the (already `Nodup`) `typeArgs` list is no
      longer than `depth` and each name is reachable by `genIdentName`;
    - `hInputNamesLen` / `hInputNamesReach` — likewise for the parameter names;
    - `hTyReach` — the output and each input type are reachable by `genLMonoTy`;
    - `hBodyReach` / `hMeasureReach` — the body/measure (when present) are
      reachable by `genLExpr`;
    - `hPreLen` / `hPreReach` — there is at most one `requires` clause and its
      expression is reachable by `genLExpr` at `.bool` **in the formals context**
      `inputsAsFVarCtx func.inputs` (not `fctx`). A function whose precondition
      mentions an ambient variable is therefore out of reach by design — such a
      function violates `FuncWF.precond_freevars` anyway.

    The `typeArgs` / input-name conditions are stated concretely (a length bound
    plus per-name `genIdentName` reachability) via
    `mem_support_genNameList_iff`, rather than as opaque `∈ support (genNameList …)`
    facts.

    Because the annotated spec ignores the ambient context, `bodyTyped` gives us
    exactly `HasTypeA [] body output`, which is what `genLExpr` completeness needs. -/
theorem genFunction_complete (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (func : Function)
    (hwt : FuncHasTypeA C Γ func)
    -- the generator does not vary these fields, so they must be at defaults:
    (hConstr : func.isConstr = false)
    (hRec : func.isRecursive = false)
    (hAttr : func.attr = #[])
    -- (Strata's `76933e8b` split moved the function-typed `concreteEval` off the
    -- base `Func`, so `Function` no longer has that field and the former
    -- `func.concreteEval = none` hypothesis is gone.)
    (hAxioms : func.axioms = [])
    -- `preconditions` IS generated, but at most one clause (`genPreconditions`
    -- emits `Option.toList`), so a longer list is out of reach:
    (hPreLen : func.preconditions.length ≤ 1)
    -- reachability of the generated components:
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
    -- A precondition is generated over the *formals* (`inputsAsFVarCtx`), not
    -- `fctx` — see `genPrecondition` and `FuncWF.precond_freevars`.
    (hPreReach : ∀ p ∈ func.preconditions, p.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (inputsAsFVarCtx func.inputs) octx []
        func.typeArgs [] depth .bool)) :
    func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth) := by
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff]
  -- Witnesses: the function's own components.
  refine ⟨func.name.name, hNameReach,
          func.typeArgs, ?_,
          func.inputs, ?_,
          func.output, hOutputReach,
          func.body, ?_,
          func.measure, ?_,
          func.preconditions, ?_, ?_⟩
  · -- typeArgs reachable via genTypeArgs (Nodup ⇒ dedup fixed point)
    exact genTypeArgs_complete depth func.typeArgs hwt.typeArgsNodup
      (mem_support_genNameList_iff depth func.typeArgs |>.mpr ⟨hTyArgsLen, hTyArgsReach⟩)
  · -- inputs reachable via genInputs
    exact genInputs_complete func.typeArgs depth func.inputs
      hwt.inputsNodup
      (mem_support_genNameList_iff depth _ |>.mpr ⟨hInputNamesLen, hInputNamesReach⟩)
      hInputTyReach
  · -- body reachable via genOptExpr
    exact genOptExpr_complete fctx octx func.typeArgs depth func.output func.body hBodyReach
  · -- measure reachable via genOptExpr
    exact genOptExpr_complete fctx octx func.typeArgs depth .int func.measure hMeasureReach
  · -- preconditions reachable via genPreconditions
    exact genPreconditions_complete octx func.inputs func.typeArgs depth
      func.preconditions hPreLen hPreReach
  · -- the reassembled record equals `func`
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
  exact genNameList_not_keyword depth names hnames s ((mem_dedup names s).mp hs)

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
    (mem_dedup _ x).mp hx
  obtain ⟨s, hs_mem, rfl⟩ := List.mem_map.mp hx'
  exact genNameList_not_keyword depth names hnames s hs_mem

/-- **Keyword-freedom of `genFunction`.** Every name a generated function exposes
    in identifier position — its own name, its type arguments, and its parameter
    names — is a non-keyword, so none is a reserved word the Core parser would
    reject in identifier position. (The function's body/measure and its types are
    unconstrained by this lemma; it is about the identifier-position names only.) -/
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
