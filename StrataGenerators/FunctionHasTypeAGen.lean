import StrataGenerators.HasTypeAGen
import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Dedup
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
    obtain ⟨ty, hty_mem, hv_ty⟩ := LMonoTys.freeVars_exists hv
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

-- ── Keyword-freedom of generated names ───────────────────────────────
-- `genIdentName` post-processes each candidate with `dodgeKeyword`, so it never
-- produces a reserved Strata Core keyword. These lemmas make that guarantee
-- explicit and provable (a soundness-style property of the name generator): no
-- generated function name, type argument, or parameter name is a reserved word
-- the parser would reject in identifier position.

/-- No reserved keyword's character list ends in `_` (checked over the concrete
    source list `reservedKeywordsList`). -/
theorem no_keyword_ends_underscore :
    ∀ k ∈ reservedKeywordsList, k.toList.getLast? ≠ some '_' := by decide +kernel

/-- `s ++ "_"` is never a reserved keyword: it ends in `_`, and no keyword does.
    Stated via `isReservedKeyword` (the `HashSet` lookup) and discharged through
    the `isReservedKeyword_eq_list_contains` bridge to `reservedKeywordsList`. -/
theorem append_underscore_not_keyword (s : String) :
    isReservedKeyword (s ++ "_") = false := by
  rw [isReservedKeyword_eq_list_contains, Bool.eq_false_iff]
  intro hc
  rw [List.contains_iff_mem] at hc
  have hlast : (s ++ "_").toList.getLast? = some '_' := by
    rw [String.toList_append]; exact List.getLast?_concat
  exact no_keyword_ends_underscore _ hc hlast

/-- `dodgeKeyword` never returns a reserved keyword: keywords are mapped to
    `k ++ "_"` (not a keyword), non-keywords are returned unchanged. -/
theorem dodgeKeyword_not_keyword (s : String) :
    isReservedKeyword (dodgeKeyword s) = false := by
  unfold dodgeKeyword
  split
  · rename_i h
    exact append_underscore_not_keyword s
  · rename_i h
    simpa using h

/-- **Keyword-freedom of `genIdentName`.** Every name in the support of
    `genIdentName` is a non-keyword identifier. -/
theorem genIdentName_not_keyword (s : String)
    (hs : s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    isReservedKeyword s = false := by
  simp only [genIdentName, mem_support_bind_iff, mem_support_pure_iff] at hs
  obtain ⟨x, _, xs, _, rfl⟩ := hs
  exact dodgeKeyword_not_keyword _

/-- `dodgeKeyword` never introduces a space: the keyword branch appends `"_"`
    (no space), the fallthrough returns the string unchanged. -/
theorem dodgeKeyword_no_space (s : String) (h : ' ' ∉ s.toList) :
    ' ' ∉ (dodgeKeyword s).toList := by
  unfold dodgeKeyword
  split
  · rw [String.toList_append]
    intro hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · exact h h1
    · simp at h2
  · exact h

/-- **Space-freedom of `genIdentName`.** Every generated identifier's character
    list contains no space: the leading char is drawn from `startChars` and the
    rest from `remainingChars` — neither list contains `' '` — and `dodgeKeyword`
    only ever appends `"_"`. This is the enabling fact for the in-out procedure
    body seed: `CoreIdent.mkOld` prefixes `"old "` (which *does* contain a space),
    so no generated parameter name can equal an `old`-binding key. -/
theorem genIdentName_no_space (s : String)
    (hs : s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    ' ' ∉ s.toList := by
  simp only [genIdentName, mem_support_bind_iff, mem_support_pure_iff] at hs
  obtain ⟨x, hx, xs, hxs, rfl⟩ := hs
  have hstart : x ∈ startChars := by
    simpa only [genStartChar,
      mem_support_elements_iff (show startChars ≠ [] from by decide +kernel)] using hx
  have hxs' : ∀ c ∈ xs, c ∈ remainingChars := by
    intro c hc
    have := SetGen.mem_support_listOf hxs c hc
    simpa only [genRemainingChar,
      mem_support_elements_iff (show remainingChars ≠ [] from by decide +kernel)] using this
  apply dodgeKeyword_no_space
  rw [String.toList_ofList]
  intro hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact (by decide +kernel : ' ' ∉ startChars) hstart
  · exact (by decide +kernel : ' ' ∉ remainingChars) (hxs' _ hmem)

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
    exact genLExpr_sound fctx octx [] tvars [] depth τ e' he'

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
  obtain ⟨name, _hname, typeArgs, htypeArgs, inputs, hinputs,
          output, houtput, body, hbody, measure, hmeasure, rfl⟩ := hfunc
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
      reachable by `genLExpr`.

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
    (hPre : func.preconditions = [])
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
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] func.typeArgs [] depth .int)) :
    func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth) := by
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff]
  -- Witnesses: the function's own components.
  refine ⟨func.name.name, hNameReach,
          func.typeArgs, ?_,
          func.inputs, ?_,
          func.output, hOutputReach,
          func.body, ?_,
          func.measure, ?_, ?_⟩
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
  · -- the reassembled record equals `func`
    obtain ⟨fname, ftyArgs, fconstr, frec, finputs, foutput, fbody, fattr,
            faxioms, fpre, fmeasure⟩ := func
    obtain ⟨nm, nmeta⟩ := fname
    simp only at hConstr hRec hAttr hAxioms hPre ⊢
    subst hConstr hRec hAttr hAxioms hPre
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
          output, _houtput, body, _hbody, measure, _hmeasure, rfl⟩ := hfunc
  refine ⟨genIdentName_not_keyword name hname, genTypeArgs_not_keyword depth typeArgs htypeArgs, ?_⟩
  -- `inputs.keys = idents`, and each ident's name is non-keyword by `genIdents_not_keyword`.
  simp only [genInputs, mem_support_bind_iff] at hinputs
  obtain ⟨idents, hidents, hmap⟩ := hinputs
  obtain ⟨hkeys, _⟩ := mapM_genInputs_keys_values typeArgs depth idents inputs hmap
  rw [hkeys]
  exact genIdents_not_keyword depth idents hidents

end StrataGenerators.Function
