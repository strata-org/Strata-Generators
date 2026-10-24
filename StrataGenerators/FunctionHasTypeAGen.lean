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
`LFunc CoreLParams`. This file proves that every function it makes satisfies the weak typing
`FuncHasTypeW` (`genFunction_sound`), and that its support holds every function of the shape it
draws (`genFunction_complete`).

The body and the precondition are typed over `funcScopes ts func`, the ambient variable scopes
with the formals pushed on top. The body draws its free variables from the ambient variables that
no formal shadows, so they keep their ambient types; the precondition draws them from the formals.
`genLExpr_exprHasTypeW` and `genLExpr_annotTyVars` give the typing and the scoping of both.
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
    are the list of identifiers after `List.uniq`, their names come from `genNameList`, and
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

-- ── The facts behind the fields of `FuncHasTypeW` ─────────────────────

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

/-- An expression whose binder annotations are all generable types has only known binder
    annotations in each context that registers the built-in type constructors. -/
theorem binderAnnotsKnown_of_generable {C : LContext CoreLParams} (hC : SimpleTyArities C)
    (e : LExpr') (h : binderAnnotsGenerable e = true) : BinderAnnotsKnown C e := by
  intro t ht
  have hgen := List.all_eq_true.mp h t ht
  exact genLMonoTy_mem_knownInstance hC ⟨_, inGenLMonoTySupport_sound _ _ t hgen⟩

/-- Every clause `genPreconditions` makes is a weakly typed `bool` expression whose annotation
    type variables are in `tvars`, when the formals and operators the clauses draw on agree with
    `C` and `ts` (`ExprCtxOk`) and their types, and every scheme, range over `tvars`
    (`ExprScopedCtx`). -/
theorem genPreconditions_sound {C : LContext CoreLParams} {ts : TypeScopes} {octx : OpCtx}
    {inputs : ListMap (Identifier Unit) LMonoTy} {tvars : List TyIdentifier} {depth : Nat}
    {pctx : PolyOpCtx}
    (hctx : ExprCtxOk C ts (inputsAsFVarCtx inputs) octx pctx)
    (hsc : ExprScopedCtx tvars (inputsAsFVarCtx inputs) octx pctx)
    {ps : List (Strata.DL.Util.FuncPrecondition LExpr' Unit)}
    (hps : ps ∈ SetGen.support (genPreconditions (G := SetGen.Set) octx inputs tvars depth pctx)) :
    ∀ p ∈ ps, ExprHasTypeW C ts p.expr .bool ∧ ∀ v ∈ annotTyVars p.expr, v ∈ tvars := by
  have hA := closureHyps_annotsOk tvars hctx
  have hB := closureHyps_annotTyVars hsc
  have hdraw : ∀ τ e, LMonoTy.knownInstance τ C.knownTypes = true →
      (∀ v ∈ LMonoTy.freeVars τ, v ∈ tvars) →
      e ∈ SetGen.support
        (genLExpr (G := SetGen.Set) (inputsAsFVarCtx inputs) octx pctx tvars [] depth τ) →
      ExprHasTypeW C ts e τ ∧ ∀ v ∈ annotTyVars e, v ∈ tvars :=
    fun τ e hk hv he => ⟨genLExpr_exprHasTypeW hctx hk he, genLExpr_annotTyVars hsc hv he⟩
  intro p hp
  simp only [genPreconditions, mem_support_map_iff] at hps
  obtain ⟨o, ho, rfl⟩ := hps
  simp only [genPrecondition, mem_support_optionGen_iff] at ho
  rcases ho with rfl | ⟨q, hq, rfl⟩
  · exact absurd hp List.not_mem_nil
  have hpq : p = q := by
    simp only [Option.toList_some, List.mem_singleton] at hp
    exact hp
  subst hpq
  by_cases hne : inputs.toList ≠ []
  · rw [dif_pos hne, mem_support_bind_iff] at hq
    obtain ⟨e, he, hpe⟩ := hq
    rw [mem_support_pure_iff] at hpe
    subst hpe
    rw [mem_support_frequency_iff] at he
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
      have hfx : (x.name, τ) ∈ inputsAsFVarCtx inputs :=
        List.mem_map_of_mem (f := fun (id, mty) => (id.name, mty)) hxτ
      obtain ⟨htyped, hscoped⟩ := hdraw τ e' (hctx.fvars _ hfx).1 (hsc.fvars _ hfx) he'
      exact ⟨⟨LExpr.HasTypeA.eq LExpr.HasTypeA.fvar htyped.1,
          hA.eq _ _ (hA.fvar _ hfx) htyped.2⟩,
        hB.eq _ _ (hB.fvar _ hfx) hscoped⟩
    · exact hdraw .bool e hA.bool hB.bool hg
  · rw [dif_neg hne, mem_support_bind_iff] at hq
    obtain ⟨e, he, hpe⟩ := hq
    rw [mem_support_pure_iff] at hpe
    subst hpe
    exact hdraw .bool e hA.bool hB.bool he

-- ── The soundness of `genFunction` ───────────────────────────────────

/-- **Soundness of `genFunction`.** Every function the generator makes is weakly typed in
    context `C` and variable scopes `ts`, when its contexts agree with them: the ambient variables,
    operators and polymorphic schemes meet `ExprCtxOk`, and every scheme is closed, so that the
    polymorphic rule writes only annotations over the type arguments. -/
theorem genFunction_sound (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (C : LContext CoreLParams) (ts : TypeScopes) (pctx : PolyOpCtx) (avoid : String → Bool)
    (hctx : ExprCtxOk C ts fctx octx pctx)
    (hclosed : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx →
      ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs)
    (func : Function)
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth pctx avoid)) :
    FuncHasTypeW C ts func := by
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff] at hfunc
  obtain ⟨name, _, rawTypeArgs, hrawTypeArgs, rawInputs, hrawInputs,
          output, houtput, body, hbody, preconditions, hpre, hfeq⟩ := hfunc
  have hIn : func.inputs = rawInputs.filter (fun p => !avoid p.1.name) := by rw [hfeq]
  have hOut : func.output = output := by rw [hfeq]
  have hTA : func.typeArgs = (rawTypeArgs.filter isAllowedName).filter
      (fun a =>
        (LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values)).contains a) := by
    rw [hfeq]
  have hBody : func.body = body := by rw [hfeq]
  have hPre : func.preconditions = preconditions := by rw [hfeq]
  have hMeasure : func.measure = none := by rw [hfeq]
  have hAxioms : func.axioms = [] := by rw [hfeq]
  have hConstr : func.isConstr = false := by rw [hfeq]
  rw [← hIn, ← hOut, ← hTA] at hbody hpre
  -- The facts about the drawn type arguments and the drawn inputs.
  have hrawNodup : rawTypeArgs.Nodup := genTypeArgs_nodup depth rawTypeArgs hrawTypeArgs
  obtain ⟨hrawKeysNodup, hrawVals⟩ :=
    genInputs_support (rawTypeArgs.filter isAllowedName) depth rawInputs hrawInputs
  have hkeysNodup : func.inputs.keys.Nodup := by
    rw [hIn]
    exact keys_filter_nodup _ rawInputs hrawKeysNodup
  have hsig : ∀ ty ∈ func.output :: func.inputs.values,
      ∃ m, ty ∈ SetGen.support
        (genLMonoTy (G := SetGen.Set) (rawTypeArgs.filter isAllowedName) m) := by
    intro ty hty
    rcases List.mem_cons.mp hty with rfl | hty
    · rw [hOut]
      exact ⟨_, houtput⟩
    · rw [hIn] at hty
      exact ⟨_, hrawVals ty (ListMap.mem_values_filter _ rawInputs ty hty)⟩
  have hknown : ∀ ty ∈ func.output :: func.inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true :=
    fun ty hty => genLMonoTy_mem_knownInstance hctx.arities (hsig ty hty)
  -- Every type variable of the signature is a type argument.
  have hsigVars : ∀ ty ∈ func.output :: func.inputs.values, ∀ v ∈ LMonoTy.freeVars ty,
      v ∈ func.typeArgs := by
    intro ty hty v hv
    obtain ⟨m, hm⟩ := hsig ty hty
    rw [hTA]
    refine List.mem_filter.mpr ⟨allFtvarsIn_freeVars (genLMonoTy_mem_ftvars hm) v hv, ?_⟩
    refine List.contains_iff_mem.mpr (mem_freeVars_mkArrow' _ _ v ?_)
    rcases List.mem_cons.mp hty with rfl | hty
    · exact Or.inl hv
    · exact Or.inr ⟨ty, hty, hv⟩
  -- The contexts the body and the precondition are drawn from.
  have hsubOps : ∀ p ∈ (opsOver func.typeArgs octx).ops, p ∈ octx.ops ∧
      ∀ v ∈ LMonoTy.freeVars p.2, v ∈ func.typeArgs :=
    fun _ hp => mem_opsOver_iff.mp hp
  have hctxBody : ExprCtxOk C (funcScopes ts func)
      (fctx.filter (fun p => !func.inputs.keys.contains ⟨p.1, ()⟩ &&
        (LMonoTy.freeVars p.2).all func.typeArgs.contains))
      (opsOver func.typeArgs octx) pctx := by
    refine hctx.restrict ?_ (fun p hp => (hsubOps p hp).1) (fun _ hp => hp)
    intro p hp
    obtain ⟨hp, hkeep⟩ := List.mem_filter.mp hp
    rw [Bool.and_eq_true] at hkeep
    have hnot : (⟨p.1, ()⟩ : Identifier Unit) ∉ func.inputs.keys := by
      intro hm
      rw [List.contains_iff_mem.mpr hm] at hkeep
      exact absurd hkeep.1 (by simp)
    obtain ⟨hk, hfind⟩ := hctx.fvars p hp
    exact ⟨hk, (funcScopes_find?_ambient ts func hnot).trans hfind⟩
  have hscBody : ExprScopedCtx func.typeArgs
      (fctx.filter (fun p => !func.inputs.keys.contains ⟨p.1, ()⟩ &&
        (LMonoTy.freeVars p.2).all func.typeArgs.contains))
      (opsOver func.typeArgs octx) pctx := by
    refine ⟨?_, fun p hp => (hsubOps p hp).2, hclosed⟩
    intro p hp v hv
    obtain ⟨_, hkeep⟩ := List.mem_filter.mp hp
    rw [Bool.and_eq_true] at hkeep
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hkeep.2 v hv)
  have hformal : ∀ q ∈ inputsAsFVarCtx func.inputs,
      ∃ x : Identifier Unit, (x, q.2) ∈ func.inputs.toList ∧ q.1 = x.name := by
    intro q hq
    obtain ⟨⟨x, τ⟩, hxτ, rfl⟩ := List.mem_map.mp hq
    exact ⟨x, hxτ, rfl⟩
  have hctxPre : ExprCtxOk C (funcScopes ts func) (inputsAsFVarCtx func.inputs)
      (opsOver func.typeArgs octx) pctx := by
    refine hctx.restrict ?_ (fun p hp => (hsubOps p hp).1) (fun _ hp => hp)
    intro q hq
    obtain ⟨x, hx, hname⟩ := hformal q hq
    refine ⟨hknown q.2 (List.mem_cons_of_mem _ (mem_values_of_mem_toList hx)), ?_⟩
    rw [hname]
    exact funcScopes_find?_formal ts func hkeysNodup hx
  have hscPre : ExprScopedCtx func.typeArgs (inputsAsFVarCtx func.inputs)
      (opsOver func.typeArgs octx) pctx := by
    refine ⟨?_, fun p hp => (hsubOps p hp).2, hclosed⟩
    intro q hq
    obtain ⟨x, hx, _⟩ := hformal q hq
    exact hsigVars q.2 (List.mem_cons_of_mem _ (mem_values_of_mem_toList hx))
  have hpreOk := genPreconditions_sound hctxPre hscPre hpre
  have hbodyMem : ∀ b, func.body = some b → b ∈ SetGen.support (genLExpr (G := SetGen.Set)
      (fctx.filter (fun p => !func.inputs.keys.contains ⟨p.1, ()⟩ &&
        (LMonoTy.freeVars p.2).all func.typeArgs.contains))
      (opsOver func.typeArgs octx) pctx func.typeArgs [] depth func.output) := by
    intro b hb
    rw [hBody] at hb
    rw [hb] at hbody
    exact genOptExpr_mem hbody
  refine ⟨?inputsNodup, ?typeArgsNodup, ?noUndeclaredVars, ?typeArgsInSignature,
    ?signatureWellKinded, ?bodyTyped, ?measureOnlyRecursive, ?measureTyped, ?preconditionsTyped,
    ?axiomsTyped, ?annotsScoped, ?constrNoBody⟩
  case inputsNodup => exact hkeysNodup
  case typeArgsNodup =>
    rw [hTA]
    exact List.Nodup.sublist List.filter_sublist (List.Nodup.sublist List.filter_sublist hrawNodup)
  case noUndeclaredVars =>
    intro v hv
    rcases freeVars_mkArrow' _ _ v hv with hout | ⟨t, ht_mem, hvt⟩
    · exact hsigVars _ List.mem_cons_self v hout
    · exact hsigVars t (List.mem_cons_of_mem _ ht_mem) v hvt
  case typeArgsInSignature =>
    intro ta hta
    rw [hTA] at hta
    exact List.contains_iff_mem.mp (List.mem_filter.mp hta).2
  case signatureWellKinded =>
    intro ty hty
    exact genLMonoTy_mem_wellKindedTy hctx.arities (hsig ty hty)
  case bodyTyped =>
    intro b hb
    exact genLExpr_exprHasTypeW hctxBody (hknown _ List.mem_cons_self) (hbodyMem b hb)
  case measureOnlyRecursive => exact fun _ => hMeasure
  case measureTyped =>
    intro m hm
    rw [hMeasure] at hm
    exact absurd hm (by simp)
  case preconditionsTyped =>
    intro p hp
    rw [hPre] at hp
    exact (hpreOk p hp).1
  case axiomsTyped =>
    intro ax hax
    rw [hAxioms] at hax
    exact absurd hax List.not_mem_nil
  case annotsScoped =>
    intro e he v hv
    simp only [Strata.DL.Util.Func.exprs, hBody, hAxioms, hPre, hMeasure, List.append_nil,
      Option.toList_none, List.mem_append, List.mem_map] at he
    rcases he with ⟨he⟩ | ⟨p, hp, rfl⟩
    · cases hb : body with
      | none => rw [hb] at he; exact absurd he (by simp)
      | some b =>
        rw [hb, Option.toList_some, List.mem_singleton] at he
        subst he
        exact genLExpr_annotTyVars hscBody (hsigVars _ List.mem_cons_self)
          (hbodyMem e (hBody.trans hb)) v hv
    · exact (hpreOk p hp).2 v hv
  case constrNoBody =>
    intro h
    rw [hConstr] at h
    exact absurd h (by simp)

/-- Soundness of `genFunction` at an empty operator context and an empty polymorphic context. -/
theorem genFunction_sound_nil (fctx : FVarCtx) (depth : Nat)
    (C : LContext CoreLParams) (ts : TypeScopes) (avoid : String → Bool)
    (hctx : ExprCtxOk C ts fctx ∅ []) (func : Function)
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx ∅ depth [] avoid)) :
    FuncHasTypeW C ts func :=
  genFunction_sound fctx ∅ depth C ts [] avoid hctx (fun _ _ _ h => absurd h List.not_mem_nil)
    func hfunc

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
    (pctx : PolyOpCtx) (avoid : String → Bool)
    (func : Function)
    (hfunc : func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth pctx avoid)) :
    isReservedKeyword func.name.name = false ∧
    (∀ s ∈ func.typeArgs, isReservedKeyword s = false) ∧
    (∀ x ∈ func.inputs.keys, isReservedKeyword x.name = false) := by
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff] at hfunc
  obtain ⟨name, hname, typeArgs, htypeArgs, inputs, hinputs,
          output, _, body, _, measure, _,
          preconditions, _, rfl⟩ := hfunc
  refine ⟨genIdentName_not_keyword name hname, ?_, ?_⟩
  · -- The type arguments are a filter of a filter of the drawn names.
    intro s hs
    have hsRaw : s ∈ typeArgs := (List.mem_filter.mp (List.mem_filter.mp hs).1).1
    exact genTypeArgs_not_keyword depth typeArgs htypeArgs s hsRaw
  · -- The inputs are a filter of the drawn signature, whose keys are the drawn identifiers.
    intro x hx
    obtain ⟨y, hxy, _⟩ := mem_keys_filter _ inputs x hx
    simp only [genInputs, mem_support_bind_iff] at hinputs
    obtain ⟨idents, hidents, hmap⟩ := hinputs
    obtain ⟨hkeys, _⟩ := mapM_genInputs_keys_values _ depth idents inputs hmap
    have hxKey : x ∈ ListMap.keys inputs := by
      rw [ListMap.keys_eq_map_fst]
      exact List.mem_map_of_mem hxy
    rw [hkeys] at hxKey
    exact genIdents_not_keyword depth idents hidents x hxKey

end StrataGenerators.Function
