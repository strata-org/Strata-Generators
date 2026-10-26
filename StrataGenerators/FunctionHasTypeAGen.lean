import StrataGenerators.HasTypeAGen
import StrataGenerators.HasTypeAGen.AnnotFacts
import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Dedup
import StrataGenerators.FunctionHasTypeAGen.IdentName
import Strata.Languages.Core.FunctionTypeSpec
import Strata.Util.ListMapProps

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Dedup StrataGenerators.AnnotFacts

/-!
# The soundness and the completeness of `genFunction`

`genFunction` makes a random Strata Core function, which is a `Function` and therefore an
`LFunc CoreLParams`. This file proves that every function it makes satisfies the typing spec
`FuncWellTyped` (`genFunction_sound`), and that its support holds every function of the shape it
draws (`genFunction_complete`).

The expressions are typed over `funcScopes ts func`, the ambient variable scopes with the formals
pushed on top. They draw their free variables from the formals and from the ambient variables that
no formal shadows, so each keeps its declared type. `genLExpr_exprWellTyped` and
`genLExpr_annotTyVars` give their typing and scoping.
-/

namespace StrataGenerators.Function

-- ── The lemmas about a free variable ─────────────────────────────────

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
    (hl : l ∈ SetGen.support (genTypeArgs (G := SetGen.Set) depth)) : l.Nodup := by
  simp only [genTypeArgs, mem_support_map_iff] at hl
  obtain ⟨names, _, rfl⟩ := hl
  exact List.nodup_uniq names

/-- Each list in the support of `genIdents` holds no duplicate, because `List.uniq` builds it. -/
theorem genIdents_nodup (depth : Nat) (l : List (Identifier Unit))
    (hl : l ∈ SetGen.support (genIdents (G := SetGen.Set) depth)) : l.Nodup := by
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

set_option linter.unusedSimpArgs false in
/-- The `mapM` inside `genInputs` gives a `ListMap` whose keys are the list of input identifiers and
    each of whose values is in the support of `genTy`. -/
theorem mapM_genInputs_keys_values (genTy : SetGen.Set LMonoTy)
    (idents : List (Identifier Unit)) (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support
      (idents.mapM (m := SetGen.Set) (fun x => do
        let ty ← genTy
        pure (x, ty)))) :
    m.keys = idents ∧ ∀ ty ∈ m.values, ty ∈ SetGen.support genTy := by
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

/-- What membership in the support of `genInputs genTy depth` gives. The keys of the `ListMap` are
    a list of identifiers with no duplicate, and each value is in the support of `genTy`. -/
theorem genInputs_support (genTy : SetGen.Set LMonoTy) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support (genInputs (G := SetGen.Set) genTy depth)) :
    m.keys.Nodup ∧ ∀ ty ∈ m.values, ty ∈ SetGen.support genTy := by
  simp only [genInputs, mem_support_bind_iff] at hm
  obtain ⟨idents, hidents, hm⟩ := hm
  have hnd := genIdents_nodup depth idents hidents
  obtain ⟨hkeys, hvals⟩ := mapM_genInputs_keys_values genTy idents m hm
  exact ⟨hkeys ▸ hnd, hvals⟩

/-- `genIdentName` can reach the `name` of each key of a signature that `genInputs` gives. The keys
    are the list of identifiers after `List.uniq`, their names come from `genNameList`, and
    `genNameList` takes each name from `genIdentName`. -/
theorem genInputs_key_name_reachable (genTy : SetGen.Set LMonoTy) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support (genInputs (G := SetGen.Set) genTy depth))
    (k : Identifier Unit) (hk : k ∈ m.keys) :
    k.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  simp only [genInputs, mem_support_bind_iff] at hm
  obtain ⟨idents, hidents, hmapM⟩ := hm
  obtain ⟨hkeys, _⟩ := mapM_genInputs_keys_values genTy idents m hmapM
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
theorem genInputs_key_no_space (genTy : SetGen.Set LMonoTy) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hm : m ∈ SetGen.support (genInputs (G := SetGen.Set) genTy depth))
    (k : Identifier Unit) (hk : k ∈ m.keys) :
    ' ' ∉ k.name.toList :=
  genIdentName_no_space k.name (genInputs_key_name_reachable genTy depth m hm k hk)

-- ── The variable scopes of a function ─────────────────────────────────

/-- `HMap.ofList` finds the first binding of a key in the reversed list. -/
theorem find?_ofList_eq_lookup_reverse {α β : Type} [BEq α] [LawfulBEq α] [Hashable α]
    [LawfulHashable α] (l : List (α × β)) (x : α) :
    Strata.Util.HMap.find? (Strata.Util.HMap.ofList l) x = l.reverse.lookup x := by
  have h := Freshening.find?_ofList_reverse l.reverse x
  rwa [List.reverse_reverse] at h

/-- The keys of the formals scope of `funcScopes` are the formals. -/
theorem funcScopes_scope_keys (func : Function) :
    ((func.inputs.map (fun (id, mty) => (id, LTy.forAll [] mty))).reverse.map Prod.fst) =
      func.inputs.keys.reverse := by
  rw [List.map_reverse, List.map_map, ListMap.keys_eq_map_fst]
  rfl

/-- `funcScopes` declares every formal at its type. -/
theorem funcScopes_find?_formal (ts : TypeScopes) (func : Function)
    (hnd : func.inputs.keys.Nodup) {x : Identifier Unit} {τ : LMonoTy}
    (hx : (x, τ) ∈ func.inputs.toList) :
    (funcScopes ts func).find? x = some (.forAll [] τ) := by
  unfold funcScopes
  refine Strata.Util.HMaps.find?_push_of_some _ _ _ _ ?_
  rw [find?_ofList_eq_lookup_reverse]
  refine List.lookup_of_mem_nodup _ ?_ _ _ ?_
  · rw [funcScopes_scope_keys]
    exact List.pairwise_reverse.mpr (List.Pairwise.imp Ne.symm hnd)
  · exact List.mem_reverse.mpr
      (List.mem_map_of_mem (f := fun (id, mty) => (id, LTy.forAll [] mty)) hx)

/-- `funcScopes` keeps the ambient declaration of a name that is not a formal. -/
theorem funcScopes_find?_ambient (ts : TypeScopes) (func : Function) {x : Identifier Unit}
    (hx : x ∉ func.inputs.keys) : (funcScopes ts func).find? x = ts.find? x := by
  unfold funcScopes
  refine Strata.Util.HMaps.find?_push_of_none _ _ _ ?_
  rw [find?_ofList_eq_lookup_reverse]
  cases hl : List.lookup x (func.inputs.map (fun (id, mty) => (id, LTy.forAll [] mty))).reverse with
  | none => rfl
  | some w =>
    have hmem := List.mem_map_of_mem (f := Prod.fst) (Freshening.lookup_mem _ _ _ hl)
    rw [funcScopes_scope_keys] at hmem
    exact absurd (List.mem_reverse.mp hmem) hx

-- ── The facts behind the fields of `FuncWellTyped` ─────────────────────

/-- The value of an entry of a signature is one of its values. -/
theorem mem_values_of_mem_toList {α β : Type} {m : ListMap α β} {x : α} {τ : β}
    (h : (x, τ) ∈ m.toList) : τ ∈ m.values := by
  rw [ListMap.values_eq_map_snd]
  exact List.mem_map_of_mem (f := Prod.snd) h

/-- A drawn optional expression is drawn by `genLExpr`. -/
theorem genOptExpr_mem {fctx : FVarCtx} {octx : OpCtx} {tvars : List TyIdentifier} {depth : Nat}
    {τ : LMonoTy} {pctx : PolyOpCtx} {e : LExpr'}
    (ho : some e ∈ SetGen.support (genOptExpr (G := SetGen.Set) fctx octx tvars depth τ pctx)) :
    e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ) := by
  simp only [genOptExpr,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)] at ho
  rcases ho with hnone | ⟨e', he', ho⟩
  · exact absurd hnone (by simp)
  · rw [Option.some.inj ho]
    exact he'

/-- Filtering a signature keeps its keys distinct when they were distinct. -/
theorem keys_filter_nodup {α β : Type} (q : α × β → Bool) (m : List (α × β))
    (h : (ListMap.keys m).Nodup) : (ListMap.keys (m.filter q)).Nodup := by
  rw [ListMap.keys_eq_map_fst] at h ⊢
  exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) h

/-- Each key of a filtered signature is the key of an entry that passes the filter. -/
theorem mem_keys_filter {α β : Type} (q : α × β → Bool) (m : List (α × β)) (x : α)
    (hx : x ∈ ListMap.keys (m.filter q)) : ∃ y, (x, y) ∈ m ∧ q (x, y) = true := by
  rw [ListMap.keys_eq_map_fst] at hx
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hmem, hq⟩ := List.mem_filter.mp hab
  exact ⟨b, hmem, hq⟩

/-- A free variable of the output or of an input type is a free variable of the signature. -/
theorem mem_freeVars_mkArrow' (out : LMonoTy) (vals : List LMonoTy) (v : TyIdentifier)
    (h : v ∈ LMonoTy.freeVars out ∨ ∃ t ∈ vals, v ∈ LMonoTy.freeVars t) :
    v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' out vals) := by
  induction vals with
  | nil =>
    rw [LMonoTy.mkArrow'_nil]
    rcases h with h | ⟨t, ht, _⟩
    · exact h
    · exact absurd ht List.not_mem_nil
  | cons t rest ih =>
    rw [LMonoTy.mkArrow'_cons]
    simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil, List.mem_append]
    rcases h with h | ⟨t', ht', hvt'⟩
    · exact Or.inr (ih (Or.inl h))
    · rcases List.mem_cons.mp ht' with rfl | ht'
      · exact Or.inl hvt'
      · exact Or.inr (ih (Or.inr ⟨t', ht', hvt'⟩))

/-- A free variable of a type of `out :: vals` is a free variable of `mkArrow' out vals`. -/
theorem mem_freeVars_mkArrow'_of_mem_sig {out ty : LMonoTy} {vals : List LMonoTy}
    {v : TyIdentifier} (hty : ty ∈ out :: vals) (hv : v ∈ LMonoTy.freeVars ty) :
    v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' out vals) := by
  refine mem_freeVars_mkArrow' _ _ v ?_
  rcases List.mem_cons.mp hty with rfl | hty
  · exact Or.inl hv
  · exact Or.inr ⟨ty, hty, hv⟩

/-- Every clause `genPreconditions` makes is a well-typed `bool` expression whose annotation
    type variables are in `tvars`, when the formals, the variables of `ambient` and the operators
    the clauses draw on agree with `C` and `ts` (`ExprCtxOk`) and their types, and every scheme,
    range over `tvars` (`ExprScopedCtx`). -/
theorem genPreconditions_sound {C : LContext CoreLParams} {ts : TypeScopes} {octx : OpCtx}
    {inputs : ListMap (Identifier Unit) LMonoTy} {tvars : List TyIdentifier} {depth : Nat}
    {pctx : PolyOpCtx} {ambient : FVarCtx}
    (hctx : ExprCtxOk C ts (inputsAsFVarCtx inputs ++ ambient) octx pctx)
    (hsc : ExprScopedCtx tvars (inputsAsFVarCtx inputs ++ ambient) octx pctx)
    {ps : List (Strata.DL.Util.FuncPrecondition LExpr' Unit)}
    (hps : ps ∈ SetGen.support
      (genPreconditions (G := SetGen.Set) octx inputs tvars depth pctx ambient)) :
    ∀ p ∈ ps, ExprWellTyped C ts p.expr .bool ∧ ∀ v ∈ annotTyVars p.expr, v ∈ tvars := by
  have hA := closureHyps_annotsOk tvars hctx
  have hB := closureHyps_annotTyVars hsc
  have hdraw : ∀ τ e, LMonoTy.knownInstance τ C.knownTypes = true →
      (∀ v ∈ LMonoTy.freeVars τ, v ∈ tvars) →
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) (inputsAsFVarCtx inputs ++ ambient) octx pctx
        tvars [] depth τ) →
      ExprWellTyped C ts e τ ∧ ∀ v ∈ annotTyVars e, v ∈ tvars :=
    fun τ e hk hv he => ⟨genLExpr_exprWellTyped hctx hk he, genLExpr_annotTyVars hsc hv he⟩
  intro p hp
  rw [genPreconditions, mem_support_listOfMaxLength_iff] at hps
  have hq := hps.2 p hp
  simp only [genPrecondition, mem_support_bind_iff, mem_support_pure_iff] at hq
  obtain ⟨e, he, rfl⟩ := hq
  by_cases hne : inputs.toList ≠ []
  · rw [dif_pos hne, mem_support_frequency_iff] at he
    obtain ⟨w, g, hmem, _, hg⟩ := he
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · -- The clause `x == e'` that mentions the formal parameter `x : τ`.
      rw [genInputMentioningPrecond, mem_support_bind_iff] at hg
      obtain ⟨⟨x, τ⟩, hxτ, hrest⟩ := hg
      rw [mem_support_bind_iff] at hrest
      obtain ⟨e', he', heq⟩ := hrest
      rw [mem_support_pure_iff] at heq
      subst heq
      rw [mem_support_elements_iff] at hxτ
      have hfx : (x.name, τ) ∈ inputsAsFVarCtx inputs ++ ambient :=
        List.mem_append_left _ (List.mem_map_of_mem (f := fun (id, mty) => (id.name, mty)) hxτ)
      obtain ⟨htyped, hscoped⟩ := hdraw τ e' (hctx.fvars _ hfx).1 (hsc.fvars _ hfx) he'
      exact ⟨⟨LExpr.HasTypeA.eq LExpr.HasTypeA.fvar htyped.1,
          hA.eq _ _ (hA.fvar _ hfx) htyped.2⟩,
        hB.eq _ _ (hB.fvar _ hfx) hscoped⟩
    · exact hdraw .bool _ hA.bool hB.bool hg
  · rw [dif_neg hne] at he
    exact hdraw .bool _ hA.bool hB.bool he

/-- A name is a key of a signature exactly when the signature gives it a type. -/
theorem keys_contains_iff_find? {m : ListMap (Identifier Unit) LMonoTy} {x : Identifier Unit} :
    m.keys.contains x = true ↔ ∃ ty, m.find? x = some ty := by
  induction m with
  | nil => simp [ListMap.keys, ListMap.find?]
  | cons p rest ih =>
    obtain ⟨y, τ⟩ := p
    by_cases hxy : x = y
    · subst hxy
      simp [ListMap.keys, ListMap.find?]
    · have hyx : y ≠ x := Ne.symm hxy
      simp only [ListMap.keys, List.contains_cons, Bool.or_eq_true, beq_iff_eq, ListMap.find?,
        hyx, if_false]
      rw [← ih]
      constructor
      · rintro (h | h)
        · exact absurd h hxy
        · exact h
      · exact Or.inr

/-- A signature with distinct keys gives each key the type of its entry. -/
theorem find?_of_mem_nodup {m : ListMap (Identifier Unit) LMonoTy} {x : Identifier Unit}
    {ty : LMonoTy} (hnd : m.keys.Nodup) (hmem : (x, ty) ∈ m.toList) : m.find? x = some ty := by
  induction m with
  | nil => exact absurd hmem List.not_mem_nil
  | cons p rest ih =>
    obtain ⟨y, τ⟩ := p
    simp only [ListMap.keys, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with heq | hrest
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp [ListMap.find?]
    · have hyx : y ≠ x := by
        rintro rfl
        refine hnd.1 ?_
        rw [ListMap.keys_eq_map_fst]
        exact List.mem_map_of_mem (f := Prod.fst) hrest
      simp only [ListMap.find?, hyx, if_false]
      exact ih hnd.2 hrest

/-- A formal of `datatypeFormals dts inputs` is an entry of `inputs` whose type is a datatype
    named in `dts`. -/
theorem mem_datatypeFormals {dts : List (String × Nat)} {inputs : ListMap (Identifier Unit) LMonoTy}
    {p : Identifier Unit × LMonoTy} (hp : p ∈ datatypeFormals dts inputs) :
    p ∈ inputs.toList ∧ ∃ n args, p.2 = .tcons n args ∧ ∃ kc ∈ dts, kc.1 = n := by
  obtain ⟨hmem, hdt⟩ := List.mem_filter.mp hp
  refine ⟨hmem, ?_⟩
  obtain ⟨x, ty⟩ := p
  match ty, hdt with
  | .tcons n args, hdt =>
    simp only [isDatatypeIn, List.any_eq_true, beq_iff_eq] at hdt
    exact ⟨n, args, rfl, hdt⟩
  | .ftvar _, hdt => simp [isDatatypeIn] at hdt
  | .bitvec _, hdt => simp [isDatatypeIn] at hdt

/-- A measure that `genIntMeasure` draws is a formal or not a bare variable, and `genLExpr` draws
    it at `int`. -/
theorem genIntMeasure_mem {fctx : FVarCtx} {octx : OpCtx} {tvars : List TyIdentifier}
    {depth : Nat} {pctx : PolyOpCtx} {inputs : ListMap (Identifier Unit) LMonoTy} {m : LExpr'}
    (h : some m ∈ SetGen.support
      (genIntMeasure (G := SetGen.Set) fctx octx tvars depth pctx inputs)) :
    measureOnFormal inputs m = true ∧
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .int) := by
  rw [genIntMeasure, mem_support_map_iff] at h
  obtain ⟨o, ho, hfo⟩ := h
  cases o with
  | none => exact absurd hfo (by simp)
  | some m₀ =>
    rw [eq_comm, Option.filter_eq_some_iff] at hfo
    obtain ⟨hm₀, hon⟩ := hfo
    cases hm₀
    exact ⟨hon, genOptExpr_mem ho⟩

/-- A measure that `genMeasure` draws is one that `genIntMeasure` draws, or a formal whose type is
    a datatype of `dts`, annotated with that type. -/
theorem genMeasure_mem {dts : List (String × Nat)} {fctx : FVarCtx} {octx : OpCtx}
    {tvars : List TyIdentifier} {depth : Nat} {pctx : PolyOpCtx}
    {inputs : ListMap (Identifier Unit) LMonoTy} {m : LExpr'}
    (h : some m ∈ SetGen.support
      (genMeasure (G := SetGen.Set) dts fctx octx tvars depth pctx inputs)) :
    (measureOnFormal inputs m = true ∧
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .int)) ∨
      ∃ p ∈ datatypeFormals dts inputs, m = .fvar () p.1 (some p.2) := by
  unfold genMeasure at h
  split at h
  · rw [mem_support_frequency_iff] at h
    obtain ⟨w, g, hmem, _, hg⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl (genIntMeasure_mem hg)
    · rw [mem_support_map_iff] at hg
      obtain ⟨p, hp, heq⟩ := hg
      rw [mem_support_elements_iff] at hp
      exact Or.inr ⟨p, hp, Option.some.inj heq⟩
  · exact Or.inl (genIntMeasure_mem h)

-- ── The soundness of `genFunction` ───────────────────────────────────

/-- The signature conditions of `FuncWellTyped` in context `C`: distinct formals and type
    arguments, type arguments that are exactly the type variables of the signature, and a
    well-kinded signature. -/
structure FuncSigOk (C : LContext CoreLParams) (func : Function) : Prop where
  inputsNodup : func.inputs.keys.Nodup
  typeArgsNodup : func.typeArgs.Nodup
  sigVars : ∀ ty ∈ func.output :: func.inputs.values, ∀ v ∈ LMonoTy.freeVars ty,
    v ∈ func.typeArgs
  typeArgsInSignature : ∀ ta ∈ func.typeArgs,
    ta ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values)
  signatureWellKinded : ∀ ty ∈ func.output :: func.inputs.values, C.WellKindedTy ty

/-- The signature conditions hold of a function with the same signature, in a context with the
    same known types. -/
theorem FuncSigOk.congr {C C' : LContext CoreLParams} {f g : Function} (h : FuncSigOk C g)
    (hkt : C'.knownTypes = C.knownTypes) (hta : f.typeArgs = g.typeArgs)
    (hin : f.inputs = g.inputs) (hout : f.output = g.output) : FuncSigOk C' f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hin]; exact h.inputsNodup
  · rw [hta]; exact h.typeArgsNodup
  · rw [hta, hin, hout]; exact h.sigVars
  · rw [hta, hin, hout]; exact h.typeArgsInSignature
  · intro ty hty
    rw [hin, hout] at hty
    unfold LContext.WellKindedTy
    rw [hkt]
    exact h.signatureWellKinded ty hty

/-- A well-typed function meets the signature conditions. -/
theorem FuncSigOk.of_funcWellTyped {C : LContext CoreLParams} {ts : TypeScopes} {f : Function}
    (h : FuncWellTyped C ts f) : FuncSigOk C f := by
  refine ⟨h.inputsNodup, h.typeArgsNodup, ?_, h.typeArgsInSignature, h.signatureWellKinded⟩
  exact fun ty hty v hv => h.noUndeclaredVars v (mem_freeVars_mkArrow'_of_mem_sig hty hv)

/-- A function that `genFuncSig` draws is named `name` and has only a signature. -/
theorem genFuncSig_stub {name : String} {depth : Nat} {avoid : String → Bool}
    {dts : List (String × Nat)} {sig : Function}
    (hsig : sig ∈ SetGen.support (genFuncSig (G := SetGen.Set) name depth avoid dts)) :
    sig.name = ⟨name, ()⟩ ∧ sig = funcStub sig := by
  simp only [genFuncSig, mem_support_bind_iff, mem_support_pure_iff] at hsig
  obtain ⟨_, _, _, _, _, _, rfl⟩ := hsig
  exact ⟨rfl, rfl⟩

/-- A function that `genFuncParts` draws keeps the name and signature of `sig`, and its recursion
    flag is one that `genRecursive` draws. -/
theorem genFuncParts_shape {genRecursive : SetGen.Set Bool} {fctx : FVarCtx} {octx : OpCtx}
    {depth : Nat} {pctx : PolyOpCtx} {dts : List (String × Nat)} {sig func : Function}
    (hfunc : func ∈ SetGen.support
      (genFuncParts (G := SetGen.Set) genRecursive fctx octx depth pctx dts sig)) :
    func.name = sig.name ∧ func.typeArgs = sig.typeArgs ∧ func.inputs = sig.inputs ∧
      func.output = sig.output ∧ func.isRecursive ∈ SetGen.support genRecursive := by
  simp only [genFuncParts, mem_support_bind_iff, mem_support_pure_iff] at hfunc
  obtain ⟨_, _, _, _, _, _, _, _, isRecursive, hrec, _, _, _, _, _, _, rfl⟩ := hfunc
  exact ⟨rfl, rfl, rfl, rfl, hrec⟩

/-- Every type `genInputTy` draws mentions only type variables of `tvars`, and it is well kinded in
    a context that registers the built-in types and each datatype of `dts` at its arity. -/
theorem genInputTy_sound {C : LContext CoreLParams} (harities : SimpleTyArities C)
    {dts : List (String × Nat)} (hdts : ∀ kc ∈ dts, C.knownTypes[kc.1]? = some kc.2)
    {tvars : List TyIdentifier} {depth : Nat} {ty : LMonoTy}
    (hty : ty ∈ SetGen.support (genInputTy (G := SetGen.Set) dts tvars depth)) :
    allFtvarsIn tvars ty ∧ C.WellKindedTy ty := by
  unfold genInputTy at hty
  split at hty
  · rw [mem_support_frequency_iff] at hty
    obtain ⟨w, g, hmem, _, hg⟩ := hty
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨genLMonoTy_mem_ftvars hg, genLMonoTy_mem_wellKindedTy harities ⟨_, hg⟩⟩
    · simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_vectorOf_iff] at hg
      obtain ⟨kc, hkc, args, ⟨hlen, hargs⟩, rfl⟩ := hg
      rw [mem_support_elements_iff] at hkc
      have hft : allFtvarsIn tvars (.tcons kc.1 args) := by
        simp only [allFtvarsIn]
        exact fun a ha => genLMonoTy_mem_ftvars (hargs a ha)
      refine ⟨hft, ?_⟩
      intro ref k hmem
      simp only [getTypeConsArities, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨a, ha, hmem⟩
      · rw [hlen]
        exact hdts kc hkc
      · exact genLMonoTy_mem_wellKindedTy harities ⟨_, hargs a ha⟩ ref k hmem
  · exact ⟨genLMonoTy_mem_ftvars hty, genLMonoTy_mem_wellKindedTy harities ⟨_, hty⟩⟩

/-- `genInputTy dts tvars depth` reaches every type that `genLMonoTy tvars depth` reaches, and
    every datatype of `dts` applied to as many such types as its arity. -/
theorem genInputTy_complete {dts : List (String × Nat)} {tvars : List TyIdentifier} {depth : Nat}
    {ty : LMonoTy}
    (h : ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth) ∨
      ∃ kc ∈ dts, ∃ args : List LMonoTy, ty = .tcons kc.1 args ∧ args.length = kc.2 ∧
        ∀ a ∈ args, a ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth)) :
    ty ∈ SetGen.support (genInputTy (G := SetGen.Set) dts tvars depth) := by
  unfold genInputTy
  split
  · rename_i hne
    rw [mem_support_frequency_iff]
    rcases h with hmono | ⟨kc, hkc, args, rfl, hlen, hargs⟩
    · exact ⟨3, _, List.mem_cons_self, by omega, hmono⟩
    · refine ⟨1, _, List.mem_cons_of_mem _ List.mem_cons_self, by omega, ?_⟩
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_vectorOf_iff]
      exact ⟨kc, (mem_support_elements_iff hne).mpr hkc, args, ⟨hlen, hargs⟩, rfl⟩
  · rename_i hempty
    rcases h with hmono | ⟨kc, hkc, _⟩
    · exact hmono
    · exact absurd (List.ne_nil_of_mem hkc) hempty

/-- Every signature that `genFuncSig` draws meets the signature conditions of `FuncWellTyped` in a
    context that registers the built-in types and each datatype of `dts` at its arity. -/
theorem genFuncSig_sound {C : LContext CoreLParams} (harities : SimpleTyArities C)
    (name : String) (depth : Nat) (avoid : String → Bool) {dts : List (String × Nat)}
    (hdts : ∀ kc ∈ dts, C.knownTypes[kc.1]? = some kc.2) {sig : Function}
    (hsig : sig ∈ SetGen.support (genFuncSig (G := SetGen.Set) name depth avoid dts)) :
    FuncSigOk C sig := by
  simp only [genFuncSig, mem_support_bind_iff, mem_support_pure_iff] at hsig
  obtain ⟨rawTypeArgs, hrawTypeArgs, rawInputs, hrawInputs, output, houtput, rfl⟩ := hsig
  have hrawNodup : rawTypeArgs.Nodup := genTypeArgs_nodup depth rawTypeArgs hrawTypeArgs
  obtain ⟨hrawKeysNodup, hrawVals⟩ := genInputs_support _ depth rawInputs hrawInputs
  have hdrawn : ∀ ty ∈ output :: ListMap.values (rawInputs.filter (fun p => !avoid p.1.name)),
      allFtvarsIn rawTypeArgs ty ∧ C.WellKindedTy ty := by
    intro ty hty
    rcases List.mem_cons.mp hty with rfl | hty
    · exact ⟨genLMonoTy_mem_ftvars houtput, genLMonoTy_mem_wellKindedTy harities ⟨_, houtput⟩⟩
    · exact genInputTy_sound harities hdts
        (hrawVals ty (ListMap.mem_values_filter _ rawInputs ty hty))
  refine ⟨keys_filter_nodup _ rawInputs hrawKeysNodup,
    List.Nodup.sublist List.filter_sublist hrawNodup, ?_, ?_, ?_⟩
  · intro ty hty v hv
    refine List.mem_filter.mpr ⟨allFtvarsIn_freeVars (hdrawn ty hty).1 v hv, ?_⟩
    exact List.contains_iff_mem.mpr (mem_freeVars_mkArrow'_of_mem_sig hty hv)
  · intro ta hta
    exact List.contains_iff_mem.mp (List.mem_filter.mp hta).2
  · intro ty hty
    exact (hdrawn ty hty).2

/-- **Soundness of `genFuncParts`.** Given a signature that meets the signature conditions, every
    function the generator makes is well-typed in context `C` and variable scopes `ts` when its
    contexts agree with them (`ExprCtxOk`, closed schemes) and `C` declares each datatype of
    `dts`. -/
theorem genFuncParts_sound (genRecursive : SetGen.Set Bool) (fctx : FVarCtx) (octx : OpCtx)
    (depth : Nat) (C : LContext CoreLParams) (ts : TypeScopes) (pctx : PolyOpCtx)
    (dts : List (String × Nat))
    (hctx : ExprCtxOk C ts fctx octx pctx)
    (hclosed : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx →
      ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs)
    (hdts : ∀ kc ∈ dts, (C.datatypes.getType kc.1).isSome)
    (sig : Function) (hsig : FuncSigOk C sig) (func : Function)
    (hfunc : func ∈ SetGen.support
      (genFuncParts (G := SetGen.Set) genRecursive fctx octx depth pctx dts sig)) :
    FuncWellTyped C ts func := by
  simp only [genFuncParts, mem_support_bind_iff, mem_support_pure_iff] at hfunc
  obtain ⟨isConstr, _, body, hbody, preconditions, hpre, axioms, haxioms, isRecursive, _,
          measure, hmeasure, attr, _, lemmas, _, hfeq⟩ := hfunc
  have hIn : func.inputs = sig.inputs := by rw [hfeq]
  have hOut : func.output = sig.output := by rw [hfeq]
  have hTA : func.typeArgs = sig.typeArgs := by rw [hfeq]
  have hBody : func.body = body := by rw [hfeq]
  have hPre : func.preconditions = preconditions := by rw [hfeq]
  have hAx : func.axioms = axioms := by rw [hfeq]
  have hRec : func.isRecursive = isRecursive := by rw [hfeq]
  have hMeas : func.measure = measure := by rw [hfeq]
  have hConstr : func.isConstr = isConstr := by rw [hfeq]
  have hsigF : FuncSigOk C func := by
    rw [hfeq]
    exact ⟨hsig.1, hsig.2, hsig.3, hsig.4, hsig.5⟩
  rw [← hIn, ← hOut, ← hTA] at hbody
  rw [← hIn, ← hTA] at hpre haxioms hmeasure
  have hkeysNodup : func.inputs.keys.Nodup := hsigF.inputsNodup
  have hknown : ∀ ty ∈ func.output :: func.inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true :=
    fun ty hty => Lambda.knownInstance_of_wellKinded _ _ (hsigF.signatureWellKinded ty hty)
  have hsigVars : ∀ ty ∈ func.output :: func.inputs.values, ∀ v ∈ LMonoTy.freeVars ty,
      v ∈ func.typeArgs := hsigF.sigVars
  have hsubOps : ∀ p ∈ (opsOver func.typeArgs octx).ops, p ∈ octx.ops ∧
      ∀ v ∈ LMonoTy.freeVars p.2, v ∈ func.typeArgs :=
    fun _ hp => mem_opsOver_iff.mp hp
  have hformal : ∀ q ∈ inputsAsFVarCtx func.inputs,
      ∃ x : Identifier Unit, (x, q.2) ∈ func.inputs.toList ∧ q.1 = x.name := by
    intro q hq
    obtain ⟨⟨x, τ⟩, hxτ, rfl⟩ := List.mem_map.mp hq
    exact ⟨x, hxτ, rfl⟩
  have hfx : ∀ p ∈ func.inputs.toList,
      (p.1.name, p.2) ∈ funcFctx fctx func.inputs func.typeArgs :=
    fun p hp => List.mem_append_left _
      (List.mem_map_of_mem (f := fun (id, mty) => (id.name, mty)) hp)
  have hctxE : ExprCtxOk C (funcScopes ts func) (funcFctx fctx func.inputs func.typeArgs)
      (opsOver func.typeArgs octx) pctx := by
    refine hctx.restrict ?_ (fun p hp => (hsubOps p hp).1) (fun _ hp => hp)
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨x, hx, hname⟩ := hformal q hq
      refine ⟨hknown q.2 (List.mem_cons_of_mem _ (mem_values_of_mem_toList hx)), ?_⟩
      rw [hname]
      exact funcScopes_find?_formal ts func hkeysNodup hx
    · obtain ⟨hq, hkeep⟩ := List.mem_filter.mp hq
      rw [Bool.and_eq_true] at hkeep
      have hnot : (⟨q.1, ()⟩ : Identifier Unit) ∉ func.inputs.keys := by
        intro hm
        rw [List.contains_iff_mem.mpr hm] at hkeep
        exact absurd hkeep.1 (by simp)
      obtain ⟨hk, hfind⟩ := hctx.fvars q hq
      exact ⟨hk, (funcScopes_find?_ambient ts func hnot).trans hfind⟩
  have hscE : ExprScopedCtx func.typeArgs (funcFctx fctx func.inputs func.typeArgs)
      (opsOver func.typeArgs octx) pctx := by
    refine ⟨?_, fun p hp => (hsubOps p hp).2, hclosed⟩
    intro q hq v hv
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨x, hx, _⟩ := hformal q hq
      exact hsigVars q.2 (List.mem_cons_of_mem _ (mem_values_of_mem_toList hx)) v hv
    · obtain ⟨_, hkeep⟩ := List.mem_filter.mp hq
      rw [Bool.and_eq_true] at hkeep
      exact List.contains_iff_mem.mp (List.all_eq_true.mp hkeep.2 v hv)
  have hdraw : ∀ τ e, LMonoTy.knownInstance τ C.knownTypes = true →
      (∀ v ∈ LMonoTy.freeVars τ, v ∈ func.typeArgs) →
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) pctx func.typeArgs [] depth τ) →
      ExprWellTyped C (funcScopes ts func) e τ ∧ ∀ v ∈ annotTyVars e, v ∈ func.typeArgs :=
    fun τ e hk hv he => ⟨genLExpr_exprWellTyped hctxE hk he, genLExpr_annotTyVars hscE hv he⟩
  have hboolVars : ∀ v ∈ LMonoTy.freeVars .bool, v ∈ func.typeArgs :=
    fun v hv => by simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv
  have hintVars : ∀ v ∈ LMonoTy.freeVars .int, v ∈ func.typeArgs :=
    fun v hv => by simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv
  have hpreOk := genPreconditions_sound (ambient := ambientFctx fctx func.inputs func.typeArgs)
    hctxE hscE hpre
  have hbodyMem : ∀ b, func.body = some b → b ∈ SetGen.support (genLExpr (G := SetGen.Set)
      (funcFctx fctx func.inputs func.typeArgs) (opsOver func.typeArgs octx) pctx func.typeArgs []
      depth func.output) := by
    intro b hb
    rw [hBody] at hb
    rw [hb] at hbody
    split at hbody
    · rw [mem_support_pure_iff] at hbody
      exact absurd hbody (by simp)
    · exact genOptExpr_mem hbody
  have haxMem : ∀ ax ∈ func.axioms, ax ∈ SetGen.support (genLExpr (G := SetGen.Set)
      (funcFctx fctx func.inputs func.typeArgs) (opsOver func.typeArgs octx) pctx func.typeArgs []
      depth .bool) := by
    intro ax hax
    rw [hAx] at hax
    exact (mem_support_listOfMaxLength_iff.mp haxioms).2 ax hax
  have hmeasMem : ∀ m, func.measure = some m →
      (measureOnFormal func.inputs m = true ∧ m ∈ SetGen.support (genLExpr (G := SetGen.Set)
        (funcFctx fctx func.inputs func.typeArgs) (opsOver func.typeArgs octx) pctx func.typeArgs []
        depth .int)) ∨ ∃ p ∈ datatypeFormals dts func.inputs, m = .fvar () p.1 (some p.2) := by
    intro m hm
    rw [hMeas] at hm
    rw [hm] at hmeasure
    split at hmeasure
    · exact genMeasure_mem hmeasure
    · rw [mem_support_pure_iff] at hmeasure
      exact absurd hmeasure (by simp)
  refine ⟨?inputsNodup, ?typeArgsNodup, ?noUndeclaredVars, ?typeArgsInSignature,
    ?signatureWellKinded, ?bodyTyped, ?measureOnlyRecursive, ?measureTyped, ?preconditionsTyped,
    ?axiomsTyped, ?annotsScoped, ?constrNoBody⟩
  case inputsNodup => exact hkeysNodup
  case typeArgsNodup => exact hsigF.typeArgsNodup
  case noUndeclaredVars =>
    intro v hv
    rcases freeVars_mkArrow' _ _ v hv with hout | ⟨t, ht_mem, hvt⟩
    · exact hsigVars _ List.mem_cons_self v hout
    · exact hsigVars t (List.mem_cons_of_mem _ ht_mem) v hvt
  case typeArgsInSignature => exact hsigF.typeArgsInSignature
  case signatureWellKinded => exact hsigF.signatureWellKinded
  case bodyTyped =>
    intro b hb
    exact (hdraw _ b (hknown _ List.mem_cons_self) (hsigVars _ List.mem_cons_self)
      (hbodyMem b hb)).1
  case measureOnlyRecursive =>
    intro hnr
    rw [hRec] at hnr
    rw [hMeas]
    rw [if_neg (by simp [hnr]), mem_support_pure_iff] at hmeasure
    exact hmeasure
  case measureTyped =>
    intro m hm
    rcases hmeasMem m hm with ⟨hon, hmem⟩ | ⟨p, hp, rfl⟩
    · have htyped := (hdraw .int m (knownInstance_int hctx.arities) hintVars hmem).1
      split
      · simp only [measureOnFormal] at hon
        obtain ⟨ty, hty⟩ := keys_contains_iff_find?.mp hon
        exact ⟨ty, hty, Or.inl htyped⟩
      · exact htyped
    · obtain ⟨hpIn, n, args, hty, kc, hkc, hkcn⟩ := mem_datatypeFormals hp
      have hget : (C.datatypes.getType n).isSome := hkcn ▸ hdts kc hkc
      have htyped :
          ExprWellTyped C (funcScopes ts func) (.fvar () p.1 (some p.2)) (.tcons n args) := by
        rw [← hty]
        exact ⟨LExpr.HasTypeA.fvar, (closureHyps_annotsOk func.typeArgs hctxE).fvar _ (hfx p hpIn)⟩
      dsimp only
      exact ⟨p.2, find?_of_mem_nodup hkeysNodup hpIn, Or.inr ⟨n, args, hty, hget, htyped⟩⟩
  case preconditionsTyped =>
    intro p hp
    rw [hPre] at hp
    exact (hpreOk p hp).1
  case axiomsTyped =>
    intro ax hax
    exact (hdraw .bool ax (knownInstance_bool hctx.arities) hboolVars (haxMem ax hax)).1
  case annotsScoped =>
    intro e he v hv
    simp only [Strata.DL.Util.Func.exprs, List.mem_append, List.mem_map, Option.mem_toList] at he
    rcases he with ((hb | hax) | ⟨p, hp, rfl⟩) | hm
    · exact (hdraw _ e (hknown _ List.mem_cons_self) (hsigVars _ List.mem_cons_self)
        (hbodyMem e hb)).2 v hv
    · exact (hdraw .bool e (knownInstance_bool hctx.arities) hboolVars (haxMem e hax)).2 v hv
    · rw [hPre] at hp
      exact (hpreOk p hp).2 v hv
    · rcases hmeasMem e hm with ⟨_, hmem⟩ | ⟨p, hp, rfl⟩
      · exact (hdraw .int e (knownInstance_int hctx.arities) hintVars hmem).2 v hv
      · exact (closureHyps_annotTyVars hscE).fvar _ (hfx p (mem_datatypeFormals hp).1) v hv
  case constrNoBody =>
    intro hc
    rw [hConstr] at hc
    rw [hBody]
    rw [if_pos hc, mem_support_pure_iff] at hbody
    exact hbody

/-- **Soundness of `genFunction`.** Every function the generator makes is well-typed in
    context `C` and variable scopes `ts`, when its contexts agree with them: the ambient variables,
    operators and polymorphic schemes meet `ExprCtxOk`, every scheme is closed, and every
    datatype of `dts` is registered in `C` with its arity. -/
theorem genFunction_sound (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (C : LContext CoreLParams) (ts : TypeScopes) (pctx : PolyOpCtx) (avoid : String → Bool)
    (dts : List (String × Nat))
    (hctx : ExprCtxOk C ts fctx octx pctx)
    (hclosed : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx →
      ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs)
    (hdts : ∀ kc ∈ dts, (C.datatypes.getType kc.1).isSome ∧ C.knownTypes[kc.1]? = some kc.2)
    (func : Function)
    (hfunc : func ∈ SetGen.support
      (genFunction (G := SetGen.Set) fctx octx depth pctx avoid dts)) :
    FuncWellTyped C ts func := by
  simp only [genFunction, mem_support_bind_iff] at hfunc
  obtain ⟨name, _, sig, hsig, hparts⟩ := hfunc
  exact genFuncParts_sound genRareFlag fctx octx depth C ts pctx dts hctx hclosed
    (fun kc hkc => (hdts kc hkc).1) sig
    (genFuncSig_sound hctx.arities name depth avoid (fun kc hkc => (hdts kc hkc).2) hsig) func
    hparts

/-- Soundness of `genFunction` at an empty operator context and an empty polymorphic context. -/
theorem genFunction_sound_nil (fctx : FVarCtx) (depth : Nat)
    (C : LContext CoreLParams) (ts : TypeScopes) (avoid : String → Bool)
    (hctx : ExprCtxOk C ts fctx ∅ []) (func : Function)
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx ∅ depth [] avoid)) :
    FuncWellTyped C ts func :=
  genFunction_sound fctx ∅ depth C ts [] avoid [] hctx (fun _ _ _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) func hfunc

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
/-- The converse of `mapM_genInputs_keys_values`. Take a `ListMap` such that `genTy` can reach
    each of its values. The support of the `mapM` inside `genInputs`, over the keys of that map,
    then holds the map. -/
theorem mapM_genInputs_complete (genTy : SetGen.Set LMonoTy)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hvals : ∀ ty ∈ m.values, ty ∈ SetGen.support genTy) :
    m ∈ SetGen.support
      (m.keys.mapM (m := SetGen.Set) (fun x => do
        let ty ← genTy
        pure (x, ty))) := by
  induction m with
  | nil =>
    show [] ∈ SetGen.support (pure [] : SetGen.Set _)
    rw [mem_support_pure_iff]
  | cons p rest ih =>
    obtain ⟨x, ty⟩ := p
    simp only [ListMap.keys, List.mapM_cons, mem_support_bind_iff]
    have hty : ty ∈ SetGen.support genTy := hvals ty (by simp [ListMap.values])
    have hrest : ∀ ty' ∈ ListMap.values rest, ty' ∈ SetGen.support genTy := by
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
  -- `()`. `List.uniq` then leaves the list unchanged.
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

/-- Completeness of `genInputs`. The support of `genInputs genTy depth` holds a `ListMap` when
    three conditions hold: the keys of the map hold no duplicate; `genTy` can reach each value; and
    `genNameList depth` can reach the names of the keys. -/
theorem genInputs_complete (genTy : SetGen.Set LMonoTy) (depth : Nat)
    (m : ListMap (Identifier Unit) LMonoTy)
    (hnd : m.keys.Nodup)
    (hnames : m.keys.map (·.name) ∈ SetGen.support (genNameList (G := SetGen.Set) depth))
    (hvals : ∀ ty ∈ m.values, ty ∈ SetGen.support genTy) :
    m ∈ SetGen.support (genInputs (G := SetGen.Set) genTy depth) := by
  simp only [genInputs, mem_support_bind_iff]
  exact ⟨m.keys, genIdents_complete depth m.keys hnd hnames, mapM_genInputs_complete genTy m hvals⟩

/-- Completeness of `genOptExpr`. The generator can always reach `none`. It can reach `some e` when
    `genLExpr` can reach `e`. -/
theorem genOptExpr_complete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy) (o : Option LExpr') {pctx : PolyOpCtx}
    (ho : ∀ e, o = some e →
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ)) :
    o ∈ SetGen.support (genOptExpr (G := SetGen.Set) fctx octx tvars depth τ pctx) := by
  simp only [genOptExpr,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)]
  cases o with
  | none =>
    -- The generator can always reach `none`.
    exact Or.inl rfl
  | some e =>
    -- The generator can reach `some e`, because `genLExpr` can reach `e`.
    exact Or.inr ⟨e, ho e rfl, rfl⟩

/-- A clause whose expression a generator reaches is in the support of the clause builder over
    that generator. -/
theorem mem_support_precondClause {p : Strata.DL.Util.FuncPrecondition LExpr' Unit}
    {g : SetGen.Set LExpr'} (hg : p.expr ∈ SetGen.support g) :
    p ∈ SetGen.support (do let y ← g; pure ({ expr := y, md := () } :
      Strata.DL.Util.FuncPrecondition LExpr' Unit)) := by
  simp only [mem_support_bind_iff, mem_support_pure_iff]
  refine ⟨p.expr, hg, ?_⟩
  obtain ⟨e, md⟩ := p
  rfl

/-- Completeness of `genPreconditions`: the generator reaches every list of at most
    `maxFuncClauses` clauses whose expressions `genLExpr` reaches at `.bool` over the formals and
    `ambient`. -/
theorem genPreconditions_complete (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier)
    (depth : Nat) (ambient : FVarCtx) (ps : List (Strata.DL.Util.FuncPrecondition LExpr' Unit))
    {pctx : PolyOpCtx} (hlen : ps.length ≤ maxFuncClauses)
    (hreach : ∀ p ∈ ps, p.expr ∈ SetGen.support (genLExpr (G := SetGen.Set)
      (inputsAsFVarCtx inputs ++ ambient) octx pctx tvars [] depth .bool)) :
    ps ∈ SetGen.support
      (genPreconditions (G := SetGen.Set) octx inputs tvars depth pctx ambient) := by
  rw [genPreconditions, mem_support_listOfMaxLength_iff]
  refine ⟨hlen, fun p hp => ?_⟩
  rw [genPrecondition]
  by_cases hne : inputs.toList ≠ []
  · rw [dif_pos hne]
    refine mem_support_precondClause ?_
    rw [mem_support_frequency_iff]
    exact ⟨1, fun _ => genLExpr (inputsAsFVarCtx inputs ++ ambient) octx pctx tvars [] depth .bool,
      by simp, by omega, hreach p hp⟩
  · rw [dif_neg hne]
    exact mem_support_precondClause (hreach p hp)

/-- The **exact** support of `genPrecondition`: a clause whose expression is a plain `.bool` draw
    over the formals and `ambient`, or `x == e'` for a formal `x : τ` and a draw `e'` at `τ`. -/
theorem mem_support_genPrecondition_iff (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier)
    (depth : Nat) (ambient : FVarCtx) (p : Strata.DL.Util.FuncPrecondition LExpr' Unit) :
    p ∈ SetGen.support (genPrecondition (G := SetGen.Set) octx inputs tvars depth [] ambient)
      ↔ ∃ e,
          (e ∈ SetGen.support (genLExpr (G := SetGen.Set)
             (inputsAsFVarCtx inputs ++ ambient) octx [] tvars [] depth .bool)
           ∨ (∃ (x : Identifier Unit) (τ : LMonoTy) (e' : LExpr'),
             (x, τ) ∈ inputs.toList ∧
             e' ∈ SetGen.support (genLExpr (G := SetGen.Set)
               (inputsAsFVarCtx inputs ++ ambient) octx [] tvars [] depth τ) ∧
             e = .eq () (.fvar () x (some τ)) e'))
          ∧ p = { expr := e, md := () } := by
  constructor
  · intro hp
    simp only [genPrecondition, mem_support_bind_iff, mem_support_pure_iff] at hp
    obtain ⟨e, he, rfl⟩ := hp
    refine ⟨e, ?_, rfl⟩
    by_cases hne : inputs.toList ≠ []
    · rw [dif_pos hne, mem_support_frequency_iff] at he
      obtain ⟨w, g, hmem, _, hg⟩ := he
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rw [genInputMentioningPrecond, mem_support_bind_iff] at hg
        obtain ⟨⟨x, τ⟩, hxmem, hrest⟩ := hg
        rw [mem_support_bind_iff] at hrest
        obtain ⟨e', he', heq⟩ := hrest
        rw [mem_support_pure_iff] at heq
        rw [mem_support_elements_iff] at hxmem
        exact Or.inr ⟨x, τ, e', hxmem, he', heq⟩
      · exact Or.inl hg
    · rw [dif_neg hne] at he
      exact Or.inl he
  · rintro ⟨e, hbranch, rfl⟩
    rw [genPrecondition]
    rcases hbranch with hbool | ⟨x, τ, e', hxmem, he', rfl⟩
    · by_cases hne : inputs.toList ≠ []
      · rw [dif_pos hne]
        refine mem_support_precondClause ?_
        rw [mem_support_frequency_iff]
        exact ⟨1,
          fun _ => genLExpr (inputsAsFVarCtx inputs ++ ambient) octx [] tvars [] depth .bool,
          by simp, by omega, hbool⟩
      · rw [dif_neg hne]
        exact mem_support_precondClause hbool
    · -- A clause that mentions an input forces `inputs.toList` to be not empty, because it holds `x`.
      have hne : inputs.toList ≠ [] := by
        intro h; rw [h] at hxmem; simp at hxmem
      rw [dif_pos hne]
      refine mem_support_precondClause ?_
      rw [mem_support_frequency_iff]
      refine ⟨3, fun _ => genInputMentioningPrecond octx inputs tvars depth hne [] ambient,
        by simp, by omega, ?_⟩
      rw [genInputMentioningPrecond, mem_support_bind_iff]
      refine ⟨(x, τ), by rw [mem_support_elements_iff]; exact hxmem, ?_⟩
      rw [mem_support_bind_iff]
      exact ⟨e', he', by rw [mem_support_pure_iff]⟩

-- ── Function-level keyword-freedom ───────────────────────────────────

/-- Every type-argument name produced by `genTypeArgs` is a non-keyword: the
    names come from `genNameList` (all non-keyword by `genNameList_not_keyword`),
    and `List.uniq` only removes elements. -/
theorem genTypeArgs_not_keyword (depth : Nat) (l : List TyIdentifier)
    (hl : l ∈ SetGen.support (genTypeArgs (G := SetGen.Set) depth)) :
    ∀ s ∈ l, isReservedKeyword s = false := by
  simp only [genTypeArgs, mem_support_map_iff] at hl
  obtain ⟨names, hnames, rfl⟩ := hl
  intro s hs
  exact genNameList_not_keyword depth names hnames s ((List.mem_of_dedup names s).mpr hs)

/-- Every input-identifier name produced by `genIdents` is a non-keyword: each
    identifier `⟨s, ()⟩` comes from mapping over the `genNameList` names, and
    `List.uniq` only removes elements. -/
theorem genIdents_not_keyword (depth : Nat) (l : List (Identifier Unit))
    (hl : l ∈ SetGen.support (genIdents (G := SetGen.Set) depth)) :
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
    (pctx : PolyOpCtx) (avoid : String → Bool) (dts : List (String × Nat))
    (func : Function)
    (hfunc : func ∈ SetGen.support
      (genFunction (G := SetGen.Set) fctx octx depth pctx avoid dts)) :
    isReservedKeyword func.name.name = false ∧
    (∀ s ∈ func.typeArgs, isReservedKeyword s = false) ∧
    (∀ x ∈ func.inputs.keys, isReservedKeyword x.name = false) := by
  simp only [genFunction, genFuncSig, genFuncParts, mem_support_bind_iff,
    mem_support_pure_iff] at hfunc
  obtain ⟨name, hname, _, ⟨typeArgs, htypeArgs, inputs, hinputs, output, _, rfl⟩, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := hfunc
  refine ⟨genIdentName_not_keyword name hname, ?_, ?_⟩
  · -- The type arguments are a filter of the drawn names.
    intro s hs
    have hsRaw : s ∈ typeArgs := (List.mem_filter.mp hs).1
    exact genTypeArgs_not_keyword depth typeArgs htypeArgs s hsRaw
  · -- The inputs are a filter of the drawn signature, whose keys are the drawn identifiers.
    intro x hx
    obtain ⟨y, hxy, _⟩ := mem_keys_filter _ inputs x hx
    simp only [genInputs, mem_support_bind_iff] at hinputs
    obtain ⟨idents, hidents, hmap⟩ := hinputs
    obtain ⟨hkeys, _⟩ := mapM_genInputs_keys_values _ idents inputs hmap
    have hxKey : x ∈ ListMap.keys inputs := by
      rw [ListMap.keys_eq_map_fst]
      exact List.mem_map_of_mem hxy
    rw [hkeys] at hxKey
    exact genIdents_not_keyword depth idents hidents x hxKey

end StrataGenerators.Function
