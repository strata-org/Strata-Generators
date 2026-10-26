import StrataGenerators.HasTypeAGenOpsConsistent
import Strata.Languages.Core.TypingSpec
import Strata.DL.Lambda.LExprTypeSpecProps

/-!
# The annotations of a generated expression

`genLExpr` writes three kinds of annotation into a term: the binder annotation of an abstraction
or a quantifier, the annotation of a free variable, and the annotation of an operator. The typing
specification asks that every binder annotation be a registered type, that every free
variable and operator annotation agree with the variable scopes and the function table, and, for
the expressions of a function, an axiom or a lemma, that every annotation type variable be a type
parameter. This file proves these facts of every generated expression from conditions on the
contexts that the generator reads.

The proof has two parts. `genLExpr_closed` shows that every generated term satisfies a property
`P` that holds of every leaf the generator can emit and is preserved by the term formers it uses,
provided a type invariant `T` holds of every type at which the generator is asked for a term. The
second part uses it twice: with `T` the registered types, for registered binder annotations and for
`ScopesAnnotAgree` (free-variable and operator annotations agree with the scopes and the function
table), and with `T` the types over `tvars`, for the scoping fact.
-/

open Lambda RandomChoice SetGen StrataGenerators.IndirSupport

namespace StrataGenerators.AnnotFacts

/-! ## Closure of a generator under a property -/

/-- Every element of the support of `s` satisfies `P`. -/
def Closed {α : Type} (P : α → Prop) (s : SetGen.Set α) : Prop :=
  ∀ a ∈ SetGen.support s, P a

section Combinators

variable {α β : Type} {P : α → Prop}

/-- A generator that returns `a` draws only terms satisfying `P` when `a` does. -/
theorem closed_pure {a : α} (h : P a) : Closed P (pure a) := by
  intro x hx
  rw [mem_support_pure_iff] at hx
  rw [hx]
  exact h

/-- A bind draws only terms satisfying `P` when every continuation it can reach does. -/
theorem closed_bind {x : SetGen.Set β} {f : β → SetGen.Set α}
    (h : ∀ b ∈ SetGen.support x, Closed P (f b)) : Closed P (x >>= f) := by
  intro a ha
  rw [mem_support_bind_iff] at ha
  obtain ⟨b, hb, hab⟩ := ha
  exact h b hb a hab

/-- The empty generator draws nothing. -/
theorem closed_default : Closed P (default : SetGen.Set α) := by
  intro a ha
  exact ((bot_mem_iff a).mp ha).elim

/-- A dependent conditional draws only terms satisfying `P` when both branches do. -/
theorem closed_dite {c : Prop} [Decidable c] {t : c → SetGen.Set α} {e : ¬c → SetGen.Set α}
    (ht : ∀ h, Closed P (t h)) (he : ∀ h, Closed P (e h)) : Closed P (dite c t e) := by
  intro a ha
  rw [mem_support_dite_iff] at ha
  rcases ha with ⟨h, hmem⟩ | ⟨h, hmem⟩
  · exact ht h a hmem
  · exact he h a hmem

/-- A choice between two generators draws only terms satisfying `P` when both do. -/
theorem closed_pick {x y : SetGen.Set α} (hx : Closed P x) (hy : Closed P y) :
    Closed P (pick (fun () => x) (fun () => y)) := by
  intro a ha
  rw [mem_support_pick_iff] at ha
  rcases ha with hmem | hmem
  · exact hx a hmem
  · exact hy a hmem

/-- Every generator of a list satisfies `P`. -/
def AllClosed (P : α → Prop) (gs : List (Unit → SetGen.Set α)) : Prop :=
  ∀ g ∈ gs, Closed P (g ())

/-- No generator of the empty list draws a term. -/
theorem allClosed_nil : AllClosed P [] := by
  intro g hg
  exact absurd hg List.not_mem_nil

/-- A list of generators is closed under `P` when its head and its tail are. -/
theorem allClosed_cons {g : Unit → SetGen.Set α} {gs : List (Unit → SetGen.Set α)}
    (hg : Closed P (g ())) (hgs : AllClosed P gs) : AllClosed P (g :: gs) := by
  intro g' hg'
  rcases List.mem_cons.mp hg' with rfl | hmem
  · exact hg
  · exact hgs g' hmem

/-- A uniform choice among generators draws only terms satisfying `P` when each of them does. -/
theorem closed_oneOf {gs : List (Unit → SetGen.Set α)} (hne : gs ≠ [])
    (h : AllClosed P gs) : Closed P (oneOf gs hne) := by
  intro a ha
  rw [mem_support_oneOf_iff] at ha
  obtain ⟨g, hg, hmem⟩ := ha
  exact h g hg a hmem

/-- Every generator of a weighted list satisfies `P`. -/
def AllClosedW (P : α → Prop) (gs : List (Nat × (Unit → SetGen.Set α))) : Prop :=
  ∀ p ∈ gs, Closed P (p.2 ())

/-- No generator of the empty weighted list draws a term. -/
theorem allClosedW_nil : AllClosedW P [] := by
  intro p hp
  exact absurd hp List.not_mem_nil

/-- A weighted list of generators is closed under `P` when its head and its tail are. -/
theorem allClosedW_cons {w : Nat} {g : Unit → SetGen.Set α}
    {gs : List (Nat × (Unit → SetGen.Set α))}
    (hg : Closed P (g ())) (hgs : AllClosedW P gs) : AllClosedW P ((w, g) :: gs) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hmem
  · exact hg
  · exact hgs p hmem

/-- A weighted choice among generators draws only terms satisfying `P` when each of them does. -/
theorem closed_frequency {gs : List (Nat × (Unit → SetGen.Set α))}
    (hpos : 0 < List.sum (List.map Prod.fst gs)) (h : AllClosedW P gs) :
    Closed P (frequency gs hpos) := by
  intro a ha
  rw [mem_support_frequency_iff] at ha
  obtain ⟨w, g, hmem, _, hga⟩ := ha
  exact h (w, g) hmem a hga

/-- A uniform choice from a list draws only terms satisfying `P` when every element does. -/
theorem closed_elements [Inhabited α] {xs : List α} (hne : xs ≠ [])
    (h : ∀ a ∈ xs, P a) : Closed P (elements xs hne) := by
  intro a ha
  rw [mem_support_elements_iff] at ha
  exact h a ha

end Combinators

/-! ## The generic closure argument -/

/-- The conditions under which every term `genLExpr` draws satisfies `P`. The type invariant `T`
    holds of the types that the generator reads from its contexts and of every type that it draws,
    every leaf satisfies `P`, and every term former that the generator uses preserves `P`. The
    polymorphic rule instantiates a scheme of `pctx`; the two conditions on it are stated over the
    types that rule samples from. -/
structure ClosureHyps (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (T : LMonoTy → Prop) (P : LExpr' → Prop) : Prop where
  arrow : ∀ a b, T (.arrow a b) ↔ T a ∧ T b
  bool : T .bool
  genTy : ∀ n t, t ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n) → T t
  fctxTy : ∀ p ∈ fctx, T p.2
  octxTy : ∀ p ∈ octx.ops, T p.2
  polyArgs : ∀ τ gen sampled name cats, T τ → (∀ t ∈ gen, T t) → (∀ t ∈ sampled, T t) →
    sampled.length = max 3 (maxBinders pctx) →
    (name, cats) ∈ findPolymorphicOps pctx τ gen sampled 3 → ∀ a ∈ cats, T a
  const : ∀ c, P (.const () c)
  bvar : ∀ i, P (.bvar () i)
  fvar : ∀ p ∈ fctx, P (.fvar () ⟨p.1, ()⟩ (some p.2))
  op : ∀ p ∈ octx.ops, P (.op () ⟨p.1, ()⟩ (some p.2))
  polyOp : ∀ τ gen sampled name cats, T τ → (∀ t ∈ gen, T t) → (∀ t ∈ sampled, T t) →
    sampled.length = max 3 (maxBinders pctx) →
    (name, cats) ∈ findPolymorphicOps pctx τ gen sampled 3 →
    P (.op () ⟨name, ()⟩ (some (cats.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)))
  abs : ∀ τ body, T τ → P body → P (.abs () "" (some τ) body)
  app : ∀ f a, P f → P a → P (.app () f a)
  ite : ∀ c t f, P c → P t → P f → P (.ite () c t f)
  eq : ∀ a b, P a → P b → P (.eq () a b)
  quant : ∀ k τ tr body, T τ → P tr → P body → P (.quant () k "" (some τ) tr body)

/-- `g` draws only terms satisfying `P`, at every type satisfying `T` and in every binder context
    whose types satisfy `T`. -/
def GenClosed (T : LMonoTy → Prop) (P : LExpr' → Prop)
    (g : BVarCtx → LMonoTy → SetGen.Set LExpr') : Prop :=
  ∀ bctx τ, (∀ t ∈ bctx, T t) → T τ → Closed P (g bctx τ)

section Closure

variable {fctx : FVarCtx} {octx : OpCtx} {pctx : PolyOpCtx} {tvars : List TyIdentifier}
  {T : LMonoTy → Prop} {P : LExpr' → Prop}

/-- A curried arrow type satisfies `T` exactly when its argument types and its result type do. -/
theorem ClosureHyps.foldr_arrow (H : ClosureHyps fctx octx pctx tvars T P) :
    ∀ (l : List LMonoTy) (τ : LMonoTy),
      T (l.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) ↔ (∀ a ∈ l, T a) ∧ T τ := by
  intro l τ
  induction l with
  | nil => simp only [List.foldr_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      true_and]
  | cons a rest ih =>
    rw [List.foldr_cons, H.arrow, ih, List.forall_mem_cons]
    exact ⟨fun ⟨ha, hr, hτ⟩ => ⟨⟨ha, hr⟩, hτ⟩, fun ⟨⟨ha, hr⟩, hτ⟩ => ⟨ha, hr, hτ⟩⟩

/-- Every base type `pickBaseType` draws is a type `genLMonoTy` draws at depth 0. -/
theorem pickBaseType_mem_genLMonoTy (tvars : List TyIdentifier) {t : LMonoTy}
    (ht : t ∈ SetGen.support (pickBaseType (G := SetGen.Set))) :
    t ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars 0) := by
  rw [genLMonoTy]
  split
  · rw [mem_support_pick_iff]
    exact Or.inl ht
  · exact ht

/-- Every syntactic subtype of a type satisfying `T` satisfies `T`. -/
theorem ClosureHyps.subtypes (H : ClosureHyps fctx octx pctx tvars T P) :
    ∀ t, T t → ∀ s ∈ syntacticSubtypes t, T s := by
  intro t
  induction t using syntacticSubtypes.induct with
  | case1 a b iha ihb =>
    intro ht s hs
    rw [syntacticSubtypes] at hs
    have hab : T a ∧ T b := (H.arrow a b).mp ht
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ht
    · rcases List.mem_append.mp hs with hs | hs
      · exact iha hab.1 s hs
      · exact ihb hab.2 s hs
  | case2 ty hne =>
    intro ht s hs
    rw [syntacticSubtypes] at hs
    · rw [List.mem_singleton.mp hs]
      exact ht
    · exact hne

/-- `addNewTypes` adds only result types of arrows already present, so it keeps `T`. -/
theorem ClosureHyps.newTypes (H : ClosureHyps fctx octx pctx tvars T P) :
    ∀ (fuel : Nat) (tys : List LMonoTy), (∀ t ∈ tys, T t) → ∀ t ∈ addNewTypes fuel tys, T t := by
  intro fuel
  induction fuel with
  | zero =>
    intro tys h t ht
    rw [addNewTypes] at ht
    exact h t ht
  | succ n ih =>
    intro tys h t ht
    rw [addNewTypes] at ht
    split at ht
    · exact h t ht
    · refine ih _ ?_ t ht
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact h u hu
      · rw [List.mem_filterMap] at hu
        obtain ⟨ty, hty, hsome⟩ := hu
        split at hsome
        · rename_i argTy retTy
          split at hsome
          · rw [Option.some.injEq] at hsome
            rw [← hsome]
            exact ((H.arrow argTy retTy).mp (h _ hty)).2
          · exact absurd hsome (by simp)
        · exact absurd hsome (by simp)

/-- Every type the context can generate satisfies `T`. -/
theorem ClosureHyps.generable (H : ClosureHyps fctx octx pctx tvars T P) {bctx : BVarCtx}
    (hb : ∀ t ∈ bctx, T t) : ∀ t ∈ generableTypesFromCtx bctx fctx octx, T t := by
  unfold generableTypesFromCtx
  refine H.newTypes _ _ ?_
  intro t ht
  rw [dedupTys_eq, List.mem_eraseDups, List.mem_flatMap] at ht
  obtain ⟨u, hu, hts⟩ := ht
  refine H.subtypes u ?_ t hts
  rcases List.mem_append.mp hu with hu | hu
  · rcases List.mem_append.mp hu with hu | hu
    · exact hb u hu
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      exact H.fctxTy p hp
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    exact H.octxTy p hp

/-! ### Leaves -/

/-- A boolean constant is a leaf satisfying `P`. -/
theorem closed_genBoolConst (H : ClosureHyps fctx octx pctx tvars T P) :
    Closed P (genBoolConst (G := SetGen.Set)) :=
  closed_pick (closed_pure (H.const _)) (closed_pure (H.const _))

/-- An integer constant is a leaf satisfying `P`. -/
theorem closed_genIntConst (H : ClosureHyps fctx octx pctx tvars T P) :
    Closed P (genIntConst (G := SetGen.Set)) :=
  closed_pick (closed_bind fun _ _ => closed_pure (H.const _))
    (closed_bind fun _ _ => closed_pure (H.const _))

/-- A string constant is a leaf satisfying `P`. -/
theorem closed_genStrConst (H : ClosureHyps fctx octx pctx tvars T P) :
    Closed P (genStrConst (G := SetGen.Set)) :=
  closed_bind fun _ _ => closed_pure (H.const _)

/-- A rational constant is a leaf satisfying `P`. -/
theorem closed_genRealConst (H : ClosureHyps fctx octx pctx tvars T P) :
    Closed P (genRealConst (G := SetGen.Set)) :=
  closed_bind fun _ _ => closed_pure (H.const _)

/-- A bitvector constant is a leaf satisfying `P`. -/
theorem closed_genBitvecConst (H : ClosureHyps fctx octx pctx tvars T P) (w : Nat) :
    Closed P (genBitvecConst (G := SetGen.Set) w) :=
  closed_bind fun _ _ => closed_pure (H.const _)

/-- A bound variable drawn from the binder context satisfies `P`. -/
theorem closed_pickBVar (H : ClosureHyps fctx octx pctx tvars T P) (bctx : BVarCtx)
    (τ : LMonoTy) : ∀ hv, Closed P (pickBVar (G := SetGen.Set) bctx τ hv) := by
  intro hv
  unfold pickBVar
  refine closed_elements _ ?_
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact H.bvar i

/-- A free variable drawn from `fctx` satisfies `P`. -/
theorem closed_pickFVar (H : ClosureHyps fctx octx pctx tvars T P) (τ : LMonoTy) :
    ∀ hf, Closed P (pickFVar (G := SetGen.Set) fctx τ hf) := by
  intro hf
  unfold pickFVar
  refine closed_elements _ ?_
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  exact H.fvar (x, τ) ((fvarsOfType_mem_iff fctx τ x).mp hx)

/-- An operator drawn from `octx` at its type satisfies `P`. -/
theorem closed_pickOp (H : ClosureHyps fctx octx pctx tvars T P) (τ : LMonoTy) :
    ∀ ho, Closed P (pickOp (G := SetGen.Set) octx τ ho) := by
  intro ho
  unfold pickOp
  refine closed_elements _ ?_
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  exact H.op (x, τ) (mem_opsOfType octx τ x hx)

/-- A bound variable of type `τ` if there is one, and a draw from `k` otherwise. -/
theorem closed_leafB (H : ClosureHyps fctx octx pctx tvars T P) (bctx : BVarCtx) (τ : LMonoTy)
    {k : SetGen.Set LExpr'} (hk : Closed P k) :
    Closed P (if hv : (bvarsOfType bctx τ).length > 0 then pickBVar bctx τ hv else k) :=
  closed_dite (closed_pickBVar H bctx τ) (fun _ => hk)

/-- A free variable of type `τ` if there is one, and a draw from `k` otherwise. -/
theorem closed_leafF (H : ClosureHyps fctx octx pctx tvars T P) (τ : LMonoTy)
    {k : SetGen.Set LExpr'} (hk : Closed P k) :
    Closed P (if hf : (fvarsOfType fctx τ).length > 0 then pickFVar fctx τ hf else k) :=
  closed_dite (closed_pickFVar H τ) (fun _ => hk)

/-- An operator of type `τ` if there is one, and a draw from `k` otherwise. -/
theorem closed_leafO (H : ClosureHyps fctx octx pctx tvars T P) (τ : LMonoTy)
    {k : SetGen.Set LExpr'} (hk : Closed P k) :
    Closed P (if ho : (opsOfType octx τ).length > 0 then pickOp octx τ ho else k) :=
  closed_dite (closed_pickOp H τ) (fun _ => hk)

/-! ### Term formers -/

/-- An application spine satisfies `P` when its head and its arguments do. -/
theorem ClosureHyps.mkApps (H : ClosureHyps fctx octx pctx tvars T P) :
    ∀ (args : List LExpr') (base : LExpr'), P base → (∀ a ∈ args, P a) → P (mkApps base args) := by
  intro args
  induction args with
  | nil =>
    intro base hbase _
    exact hbase
  | cons a rest ih =>
    intro base hbase hargs
    exact ih (.app () base a) (H.app base a hbase (hargs a List.mem_cons_self))
      (fun x hx => hargs x (List.mem_cons_of_mem a hx))

variable {g : BVarCtx → LMonoTy → SetGen.Set LExpr'}

/-- An application at a type satisfying `T` draws its argument type from `genLMonoTy`, so both
    sides are drawn at types satisfying `T`. -/
theorem closed_genApp (H : ClosureHyps fctx octx pctx tvars T P) (ih : GenClosed T P g)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) (n : Nat) {τ : LMonoTy} (hτ : T τ) :
    Closed P (genApp (genAppArgTy (G := SetGen.Set) fctx octx tvars bctx n τ) (g bctx) τ) := by
  refine closed_bind fun τ' hτ' => ?_
  have hT' : T τ' := H.genTy n τ' ((genAppArgTy_support fctx octx tvars bctx n τ τ').mp hτ')
  refine closed_bind fun arg harg => closed_bind fun fn hfn => closed_pure ?_
  exact H.app fn arg (ih bctx _ hb ((H.arrow τ' τ).mpr ⟨hT', hτ⟩) fn hfn)
    (ih bctx τ' hb hT' arg harg)

/-- A conditional at a type satisfying `T` draws its condition at `bool` and its branches at that
    type. -/
theorem closed_genIte (H : ClosureHyps fctx octx pctx tvars T P) (ih : GenClosed T P g)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) {τ : LMonoTy} (hτ : T τ) :
    Closed P (genIte (g bctx .bool) (g bctx τ) (g bctx τ)) :=
  closed_bind fun c hc => closed_bind fun t ht => closed_bind fun f hf =>
    closed_pure
      (H.ite c t f (ih bctx _ hb H.bool c hc) (ih bctx τ hb hτ t ht) (ih bctx τ hb hτ f hf))

/-- An equality draws both sides at a type from `genLMonoTy`. -/
theorem closed_genEq (H : ClosureHyps fctx octx pctx tvars T P) (ih : GenClosed T P g)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) (n : Nat) :
    Closed P (genEq (genGenerableTy (G := SetGen.Set) fctx octx tvars bctx n) (g bctx)) := by
  refine closed_bind fun τ' hτ' => ?_
  have hT' : T τ' := H.genTy n τ' ((genGenerableTy_support fctx octx tvars bctx n τ').mp hτ')
  exact closed_bind fun a ha => closed_bind fun b hb' =>
    closed_pure (H.eq a b (ih bctx τ' hb hT' a ha) (ih bctx τ' hb hT' b hb'))

/-- A quantifier draws its binder and trigger types from `genLMonoTy` and its body at `bool`, under
    the extended binder context. -/
theorem closed_genQuant (H : ClosureHyps fctx octx pctx tvars T P) (ih : GenClosed T P g)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) (n : Nat) (k : QuantifierKind) :
    Closed P (genQuant k (genGenerableTy (G := SetGen.Set) fctx octx tvars bctx n)
      (fun τ' => g (τ' :: bctx)) (fun τ' => g (τ' :: bctx) .bool)) := by
  refine closed_bind fun τ' hτ' => closed_bind fun τtr hτtr => ?_
  have hT' : T τ' := H.genTy n τ' ((genGenerableTy_support fctx octx tvars bctx n τ').mp hτ')
  have hTtr : T τtr :=
    H.genTy n τtr ((genGenerableTy_support fctx octx tvars bctx n τtr).mp hτtr)
  have hb' : ∀ t ∈ τ' :: bctx, T t := List.forall_mem_cons.mpr ⟨hT', hb⟩
  exact closed_bind fun tr htr => closed_bind fun body hbody =>
    closed_pure (H.quant k τ' tr body hT' (ih _ τtr hb' hTtr tr htr) (ih _ _ hb' H.bool body hbody))

/-- An abstraction at an arrow type satisfying `T` binds the domain and draws its body at the
    codomain. -/
theorem closed_genAbs (H : ClosureHyps fctx octx pctx tvars T P) (ih : GenClosed T P g)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) {τ₁ τ₂ : LMonoTy} (h₁ : T τ₁) (h₂ : T τ₂) :
    Closed P (genAbs (g (τ₁ :: bctx) τ₂) τ₁) :=
  closed_bind fun body hbody => closed_pure
    (H.abs τ₁ body h₁ (ih _ τ₂ (List.forall_mem_cons.mpr ⟨h₁, hb⟩) h₂ body hbody))

/-- Every term the monomorphic Indir rule draws satisfies `P` when the argument generator `g`
    draws only terms satisfying `P`: the rule applies an operator of `octx`, whose type
    satisfies `T`, to arguments that `g` draws at the argument types. -/
theorem closed_genIndir (H : ClosureHyps fctx octx pctx tvars T P) (ih : GenClosed T P g)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) {τ : LMonoTy}
    (hi : (findOpsInCtx octx τ).length > 0) :
    Closed P (genIndir octx τ (g bctx) hi) := by
  intro e he
  obtain ⟨name, argTys, args, hmem, hargs, rfl⟩ := genIndir_shape octx τ (g bctx) hi e he
  have hentry := (findOpsInCtx_mem' hmem).1
  have hargTys : ∀ a ∈ argTys, T a := ((H.foldr_arrow argTys τ).mp (H.octxTy _ hentry)).1
  exact H.mkApps args _ (H.op _ hentry)
    (forall₂_forall_of_cond (fun σ hσ => ih bctx σ hb hσ) hargTys hargs)

/-- Every term the monomorphic Indir rule draws, or `g` when no operator returns `τ`, satisfies
    `P` when `g` draws only terms satisfying `P`. -/
theorem closed_indirOrRec (H : ClosureHyps fctx octx pctx tvars T P) (ih : GenClosed T P g)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) {τ : LMonoTy} (hτ : T τ) :
    Closed P (if hi : (findOpsInCtx octx τ).length > 0
      then genIndir octx τ (g bctx) hi else g bctx τ) :=
  closed_dite (closed_genIndir H ih hb) (fun _ => ih bctx τ hb hτ)

/-- A list drawn by `mapM` over `List.replicate m ()` has length `m`, and each element is drawn
    by the mapped generator. -/
theorem mem_mapM_replicate {γ : Type} {f : Unit → SetGen.Set γ} :
    ∀ (m : Nat) (l : List γ),
      l ∈ SetGen.support (List.mapM (m := SetGen.Set) f (List.replicate m ())) →
        l.length = m ∧ ∀ x ∈ l, x ∈ SetGen.support (f ()) := by
  intro m
  induction m with
  | zero =>
    intro l hl
    simp only [List.replicate_zero, List.mapM_nil, mem_support_pure_iff] at hl
    rw [hl]
    exact ⟨rfl, fun x hx => absurd hx List.not_mem_nil⟩
  | succ m ih =>
    intro l hl
    simp only [List.replicate_succ, List.mapM_cons, mem_support_bind_iff,
      mem_support_pure_iff] at hl
    obtain ⟨y, hy, ys, hys, rfl⟩ := hl
    obtain ⟨hlen, hmem⟩ := ih ys hys
    refine ⟨by rw [List.length_cons, hlen], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hy
    · exact hmem x hx

/-- The shape of a term of the polymorphic rule, with the facts about the sampled types: there are
    `max maxNumArgs (maxBinders pctx)` of them, each a generable type of the context or a base
    type. -/
theorem genIndirPolyCore_cases {fctx : FVarCtx} {octx : OpCtx} {pctx : PolyOpCtx}
    {bctx : BVarCtx} {τ : LMonoTy} {genArg : LMonoTy → SetGen.Set LExpr'}
    {fallback : SetGen.Set LExpr'} {maxNumArgs : Nat} {e : LExpr'}
    (he : e ∈ SetGen.support
      (genIndirPolyCore (G := SetGen.Set) fctx octx pctx bctx τ genArg fallback maxNumArgs)) :
    (∃ (sampled : List LMonoTy) (name : String) (cats : List LMonoTy) (args : List LExpr'),
       sampled.length = max maxNumArgs (maxBinders pctx) ∧
       (∀ t ∈ sampled, t ∈ generableTypesFromCtx bctx fctx octx ∨
          t ∈ SetGen.support (pickBaseType (G := SetGen.Set))) ∧
       (name, cats) ∈ findPolymorphicOps pctx τ
         (generableTypesFromCtx bctx fctx octx) sampled maxNumArgs ∧
       List.Forall₂ (fun arg σ => arg ∈ SetGen.support (genArg σ)) args cats ∧
       e = mkApps (.op () ⟨name, ()⟩
         (some (cats.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) args)
    ∨ e ∈ SetGen.support fallback := by
  unfold genIndirPolyCore at he
  rw [mem_support_bind_iff] at he
  obtain ⟨sampled, hsampled, he⟩ := he
  obtain ⟨hlen, hmem⟩ := mem_mapM_replicate (max maxNumArgs (maxBinders pctx)) sampled hsampled
  have hsam : ∀ t ∈ sampled, t ∈ generableTypesFromCtx bctx fctx octx ∨
      t ∈ SetGen.support (pickBaseType (G := SetGen.Set)) := by
    intro t ht
    have htm := hmem t ht
    rw [mem_support_dite_iff] at htm
    rcases htm with ⟨_, htm⟩ | ⟨_, htm⟩
    · exact Or.inl ((mem_support_elements_iff _).mp htm)
    · exact Or.inr htm
  rw [mem_support_dite_iff] at he
  rcases he with ⟨_, he⟩ | ⟨_, he⟩
  · rw [mem_support_bind_iff] at he
    obtain ⟨entry, hentry, he⟩ := he
    rw [mem_support_bind_iff] at he
    obtain ⟨args, hargs, he⟩ := he
    rw [mem_support_pure_iff] at he
    rw [mem_support_elements_iff] at hentry
    exact Or.inl ⟨sampled, entry.1, entry.2, args, hlen, hsam, hentry,
      (mem_support_mapM_iff genArg entry.2 args).mp hargs, he⟩
  · exact Or.inr he

/-- Every term the polymorphic rule draws satisfies `P` when the argument generator `g` and the
    fallback draw only terms satisfying `P`: the rule applies an instance of a scheme of `pctx`
    to arguments that `g` draws at the instantiated argument types. -/
theorem closed_poly (H : ClosureHyps fctx octx pctx tvars T P) (ih : GenClosed T P g)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) {τ : LMonoTy} (hτ : T τ)
    {fallback : SetGen.Set LExpr'} (hfb : Closed P fallback) :
    Closed P (genIndirPolyCore fctx octx pctx bctx τ (g bctx) fallback) := by
  intro e he
  rcases genIndirPolyCore_cases he with
    ⟨sampled, name, cats, args, hlen, hsam, hmem, hargs, rfl⟩ | hfall
  · have hgen := H.generable hb
    have hTsam : ∀ t ∈ sampled, T t := by
      intro t ht
      rcases hsam t ht with ht | ht
      · exact hgen t ht
      · exact H.genTy 0 t (pickBaseType_mem_genLMonoTy tvars ht)
    exact H.mkApps args _ (H.polyOp τ _ sampled name cats hτ hgen hTsam hlen hmem)
      (forall₂_forall_of_cond (fun σ hσ => ih bctx σ hb hσ)
        (H.polyArgs τ _ sampled name cats hτ hgen hTsam hlen hmem) hargs)
  · exact hfb e hfall

/-! ### The generators -/

/-- One level of `genLExprBase`: at depth 0 it draws only leaves, and at depth `n + 1` it draws
    only terms satisfying `P` if it does so at depth `n`. -/
theorem closed_genLExprBase_level (H : ClosureHyps fctx octx pctx tvars T P) (depth : Nat)
    {bctx : BVarCtx} (hb : ∀ t ∈ bctx, T t) (τ : LMonoTy) :
    (∀ n, depth = n + 1 →
      GenClosed T P (fun b t => genLExprBase (G := SetGen.Set) fctx octx pctx tvars b n t)) →
    T τ → Closed P (genLExprBase (G := SetGen.Set) fctx octx pctx tvars bctx depth τ) := by
  rw [genLExprBase.eq_def]
  split
  case h_1 τ₁ τ₂ =>
    intro _ _
    exact closed_oneOf _ (allClosed_cons (closed_leafB H bctx _ closed_default) <|
      allClosed_cons (closed_leafF H _ closed_default) <|
      allClosed_cons (closed_leafO H _ closed_default) allClosed_nil)
  case h_2 n τ₁ τ₂ =>
    intro ih hτ
    have ihn := ih n rfl
    obtain ⟨h₁, h₂⟩ := (H.arrow τ₁ τ₂).mp hτ
    have habs := closed_genAbs H ihn hb h₁ h₂
    exact closed_frequency _ (allClosedW_cons habs <|
      allClosedW_cons (closed_genApp H ihn hb n hτ) <|
      allClosedW_cons (closed_genIte H ihn hb hτ) <|
      allClosedW_cons (closed_leafB H bctx _ habs) <|
      allClosedW_cons (closed_leafF H _ habs) <|
      allClosedW_cons (closed_leafO H _ habs) <|
      allClosedW_cons (closed_indirOrRec H ihn hb hτ) <|
      allClosedW_cons (closed_poly H ihn hb hτ (ihn bctx _ hb hτ)) allClosedW_nil)
  case h_3 =>
    intro _ _
    have hc := closed_genBoolConst H
    exact closed_oneOf _ (allClosed_cons hc <| allClosed_cons (closed_leafB H bctx _ hc) <|
      allClosed_cons (closed_leafF H _ hc) <| allClosed_cons (closed_leafO H _ hc) allClosed_nil)
  case h_4 n =>
    intro ih hτ
    have ihn := ih n rfl
    have hc := closed_genBoolConst H
    exact closed_frequency _ (allClosedW_cons hc <|
      allClosedW_cons (closed_genApp H ihn hb n hτ) <|
      allClosedW_cons (closed_genIte H ihn hb hτ) <|
      allClosedW_cons (closed_genEq H ihn hb n) <|
      allClosedW_cons (closed_genQuant H ihn hb n .all) <|
      allClosedW_cons (closed_genQuant H ihn hb n .exist) <|
      allClosedW_cons (closed_leafB H bctx _ hc) <|
      allClosedW_cons (closed_leafF H _ hc) <|
      allClosedW_cons (closed_leafO H _ hc) <|
      allClosedW_cons (closed_indirOrRec H ihn hb hτ) <|
      allClosedW_cons (closed_poly H ihn hb hτ (ihn bctx _ hb hτ)) allClosedW_nil)
  case h_5 =>
    intro _ _
    have hc := closed_genIntConst H
    exact closed_oneOf _ (allClosed_cons hc <| allClosed_cons (closed_leafB H bctx _ hc) <|
      allClosed_cons (closed_leafF H _ hc) <| allClosed_cons (closed_leafO H _ hc) allClosed_nil)
  case h_6 n =>
    intro ih hτ
    have ihn := ih n rfl
    have hc := closed_genIntConst H
    exact closed_frequency _ (allClosedW_cons hc <|
      allClosedW_cons (closed_genApp H ihn hb n hτ) <|
      allClosedW_cons (closed_genIte H ihn hb hτ) <|
      allClosedW_cons (closed_leafB H bctx _ hc) <|
      allClosedW_cons (closed_leafF H _ hc) <|
      allClosedW_cons (closed_leafO H _ hc) <|
      allClosedW_cons (closed_indirOrRec H ihn hb hτ) <|
      allClosedW_cons (closed_poly H ihn hb hτ (ihn bctx _ hb hτ)) allClosedW_nil)
  case h_7 _ | h_15 | h_17 _ _ | h_19 _ | h_21 =>
    intro _ _
    exact closed_oneOf _
      (allClosed_cons
        (closed_leafB H bctx _ (closed_leafF H _ (closed_leafO H _ closed_default))) <|
      allClosed_cons (closed_leafF H _ (closed_leafB H bctx _ (closed_leafO H _ closed_default))) <|
      allClosed_cons (closed_leafO H _ (closed_leafB H bctx _ (closed_leafF H _ closed_default)))
        allClosed_nil)
  case h_8 n _ | h_16 n | h_18 n _ _ | h_20 n _ =>
    intro ih hτ
    have ihn := ih n rfl
    exact closed_frequency _ (allClosedW_cons (closed_genApp H ihn hb n hτ) <|
      allClosedW_cons (closed_genIte H ihn hb hτ) <|
      allClosedW_cons
        (closed_leafB H bctx _ (closed_leafF H _ (closed_leafO H _ closed_default))) <|
      allClosedW_cons (closed_leafF H _ (closed_leafB H bctx _ closed_default)) <|
      allClosedW_cons (closed_leafO H _ (closed_leafB H bctx _ closed_default)) <|
      allClosedW_cons (closed_indirOrRec H ihn hb hτ) <|
      allClosedW_cons (closed_poly H ihn hb hτ (ihn bctx _ hb hτ)) allClosedW_nil)
  case h_9 =>
    intro _ _
    have hc := closed_genStrConst H
    exact closed_oneOf _ (allClosed_cons hc <| allClosed_cons (closed_leafB H bctx _ hc) <|
      allClosed_cons (closed_leafF H _ hc) <| allClosed_cons (closed_leafO H _ hc) allClosed_nil)
  case h_10 n =>
    intro ih hτ
    have ihn := ih n rfl
    have hc := closed_genStrConst H
    exact closed_frequency _ (allClosedW_cons hc <|
      allClosedW_cons (closed_genApp H ihn hb n hτ) <|
      allClosedW_cons (closed_genIte H ihn hb hτ) <|
      allClosedW_cons (closed_leafB H bctx _ hc) <|
      allClosedW_cons (closed_leafF H _ hc) <|
      allClosedW_cons (closed_leafO H _ hc) <|
      allClosedW_cons (closed_indirOrRec H ihn hb hτ) <|
      allClosedW_cons (closed_poly H ihn hb hτ (ihn bctx _ hb hτ)) allClosedW_nil)
  case h_11 =>
    intro _ _
    have hc := closed_genRealConst H
    exact closed_oneOf _ (allClosed_cons hc <| allClosed_cons (closed_leafB H bctx _ hc) <|
      allClosed_cons (closed_leafF H _ hc) <| allClosed_cons (closed_leafO H _ hc) allClosed_nil)
  case h_12 n =>
    intro ih hτ
    have ihn := ih n rfl
    have hc := closed_genRealConst H
    exact closed_frequency _ (allClosedW_cons hc <|
      allClosedW_cons (closed_genApp H ihn hb n hτ) <|
      allClosedW_cons (closed_genIte H ihn hb hτ) <|
      allClosedW_cons (closed_leafB H bctx _ hc) <|
      allClosedW_cons (closed_leafF H _ hc) <|
      allClosedW_cons (closed_leafO H _ hc) <|
      allClosedW_cons (closed_indirOrRec H ihn hb hτ) <|
      allClosedW_cons (closed_poly H ihn hb hτ (ihn bctx _ hb hτ)) allClosedW_nil)
  case h_13 w =>
    intro _ _
    have hc := closed_genBitvecConst H w
    exact closed_oneOf _ (allClosed_cons hc <| allClosed_cons (closed_leafB H bctx _ hc) <|
      allClosed_cons (closed_leafF H _ hc) <| allClosed_cons (closed_leafO H _ hc) allClosed_nil)
  case h_14 n w =>
    intro ih hτ
    have ihn := ih n rfl
    have hc := closed_genBitvecConst H w
    exact closed_frequency _ (allClosedW_cons hc <|
      allClosedW_cons (closed_genApp H ihn hb n hτ) <|
      allClosedW_cons (closed_genIte H ihn hb hτ) <|
      allClosedW_cons (closed_leafB H bctx _ hc) <|
      allClosedW_cons (closed_leafF H _ hc) <|
      allClosedW_cons (closed_leafO H _ hc) <|
      allClosedW_cons (closed_indirOrRec H ihn hb hτ) <|
      allClosedW_cons (closed_poly H ihn hb hτ (ihn bctx _ hb hτ)) allClosedW_nil)
  case h_22 _ _ n _ _ _ _ _ _ _ _ _ _ =>
    intro ih hτ
    have ihn := ih n rfl
    exact closed_frequency _
      (allClosedW_cons
        (closed_leafB H bctx _ (closed_leafF H _ (closed_leafO H _ closed_default))) <|
      allClosedW_cons
        (closed_leafF H _ (closed_leafB H bctx _ (closed_leafO H _ closed_default))) <|
      allClosedW_cons
        (closed_leafO H _ (closed_leafB H bctx _ (closed_leafF H _ closed_default))) <|
      allClosedW_cons (closed_indirOrRec H ihn hb hτ) <|
      allClosedW_cons (closed_poly H ihn hb hτ (ihn bctx _ hb hτ)) allClosedW_nil)

/-- Every term `genLExprBase` draws satisfies `P`, at every depth. -/
theorem genLExprBase_closed (H : ClosureHyps fctx octx pctx tvars T P) :
    ∀ depth, GenClosed T P
      (fun b t => genLExprBase (G := SetGen.Set) fctx octx pctx tvars b depth t) := by
  intro depth
  induction depth with
  | zero =>
    intro bctx τ hb hτ
    exact closed_genLExprBase_level H 0 hb τ (fun n hn => absurd hn (Nat.zero_ne_add_one n)) hτ
  | succ n ih =>
    intro bctx τ hb hτ
    refine closed_genLExprBase_level H (n + 1) hb τ ?_ hτ
    intro m hm
    rw [Nat.add_right_cancel hm] at ih
    exact ih

/-- **Every term `genLExpr` draws satisfies `P`**, at every depth, when the conditions of
    `ClosureHyps` hold. -/
theorem genLExpr_closed (H : ClosureHyps fctx octx pctx tvars T P) :
    ∀ depth, GenClosed T P
      (fun b t => genLExpr (G := SetGen.Set) fctx octx pctx tvars b depth t) := by
  intro depth
  induction depth with
  | zero =>
    intro bctx τ hb hτ
    have hbase := genLExprBase_closed H 0
    unfold genLExpr
    exact closed_dite
      (fun hi => closed_frequency _ (allClosedW_cons (hbase bctx τ hb hτ) <|
        allClosedW_cons (closed_pick (closed_genIndir H hbase hb hi)
          (closed_poly H hbase hb hτ (hbase bctx τ hb hτ))) allClosedW_nil))
      (fun _ => closed_pick (hbase bctx τ hb hτ) (closed_poly H hbase hb hτ (hbase bctx τ hb hτ)))
  | succ n ih =>
    intro bctx τ hb hτ
    have hbase := genLExprBase_closed H (n + 1)
    unfold genLExpr
    exact closed_dite
      (fun hi => closed_frequency _ (allClosedW_cons (hbase bctx τ hb hτ) <|
        allClosedW_cons (closed_pick (closed_genIndir H ih hb hi)
          (closed_poly H ih hb hτ (hbase bctx τ hb hτ))) allClosedW_nil))
      (fun _ => closed_pick (hbase bctx τ hb hτ) (closed_poly H ih hb hτ (hbase bctx τ hb hτ)))

end Closure

end StrataGenerators.AnnotFacts

namespace StrataGenerators.AnnotFacts

open Core Core.TypeSpec

/-! ## Types -/

/-- With `arrow` registered at arity 2, an arrow type is registered exactly when both sides are. -/
theorem knownInstance_arrow_iff {ks : KnownTypes} (harrow : ks["arrow"]? = some 2)
    (a b : LMonoTy) :
    LMonoTy.knownInstance (.arrow a b) ks = true ↔
      LMonoTy.knownInstance a ks = true ∧ LMonoTy.knownInstance b ks = true := by
  simp [LMonoTy.knownInstance, LMonoTys.knownInstances, KnownTypes.contains,
    Identifiers.contains, KnownType.arity, harrow]

/-- The type variables of an arrow are those of its two sides. -/
theorem freeVars_arrow_iff (tvars : List TyIdentifier) (a b : LMonoTy) :
    (∀ v ∈ LMonoTy.freeVars (.arrow a b), v ∈ tvars) ↔
      (∀ v ∈ LMonoTy.freeVars a, v ∈ tvars) ∧ (∀ v ∈ LMonoTy.freeVars b, v ∈ tvars) := by
  simp only [LMonoTy.freeVars, LMonoTys.freeVars,
    List.append_nil, List.mem_append]
  exact ⟨fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩,
    fun h v hv => hv.elim (h.1 v) (h.2 v)⟩

/-- The components `decomposeArrow` returns are registered when the type is. -/
theorem decomposeArrow_known {ks : KnownTypes} (harrow : ks["arrow"]? = some 2) :
    ∀ t, LMonoTy.knownInstance t ks = true →
      (∀ a ∈ (decomposeArrow t).1, LMonoTy.knownInstance a ks = true) ∧
        LMonoTy.knownInstance (decomposeArrow t).2 ks = true := by
  intro t
  fun_induction decomposeArrow t with
  | case1 σ rest args ret hrec ih =>
    intro ht
    obtain ⟨hσ, hrest⟩ := (knownInstance_arrow_iff harrow σ rest).mp ht
    rw [hrec] at ih
    obtain ⟨hargs, hret⟩ := ih hrest
    exact ⟨List.forall_mem_cons.mpr ⟨hσ, hargs⟩, hret⟩
  | case2 ty _ =>
    intro ht
    exact ⟨fun a ha => absurd ha List.not_mem_nil, ht⟩

/-- The type variables of the components `decomposeArrow` returns are those of the type. -/
theorem decomposeArrow_freeVars :
    ∀ t, (∀ a ∈ (decomposeArrow t).1, ∀ v ∈ LMonoTy.freeVars a, v ∈ LMonoTy.freeVars t) ∧
      ∀ v ∈ LMonoTy.freeVars (decomposeArrow t).2, v ∈ LMonoTy.freeVars t := by
  intro t
  fun_induction decomposeArrow t with
  | case1 σ rest args ret hrec ih =>
    rw [hrec] at ih
    have hsub : ∀ v, v ∈ LMonoTy.freeVars σ ∨ v ∈ LMonoTy.freeVars rest →
        v ∈ LMonoTy.freeVars (LMonoTy.tcons "arrow" [σ, rest]) := by
      intro v hv
      simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil,
        List.mem_append]
      exact hv
    refine ⟨?_, fun v hv => hsub v (Or.inr (ih.2 v hv))⟩
    intro a ha v hv
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hsub v (Or.inl hv)
    · exact hsub v (Or.inr (ih.1 a ha v hv))
  | case2 ty _ =>
    exact ⟨fun a ha => absurd ha List.not_mem_nil, fun v hv => hv⟩

/-- A one-scope substitution whose values are registered has a registered range. -/
theorem rangeKnown_substScope {ks : KnownTypes} (l : List (TyIdentifier × LMonoTy))
    (h : ∀ p ∈ l, LMonoTy.knownInstance p.2 ks = true) : Subst.RangeKnown (substScope l) ks := by
  intro mty hmty
  simp only [substScope, Strata.Util.HMaps.values, List.append_nil] at hmty
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (Strata.Util.HMap.mem_values_ofList _ _ hmty)
  exact h p (List.mem_reverse.mp hp)

/-! ## The polymorphic rule -/

/-- What a candidate of `findPolymorphicOps` is made of: a scheme of `pctx`, its renaming away from
    the variables in use and its arrow decomposition, a split point `k`, a unifier of the remaining
    result type with `τ`, and the substitution `ext` that also instantiates the open binders with
    the sampled types. `ext` sends the remaining result type to `τ`, and the candidate's argument
    types are `ext` applied to the first `k` argument types. -/
theorem findPolymorphicOps_mem_cases {pctx : PolyOpCtx} {τ : LMonoTy}
    {gen sampled : List LMonoTy} {m : Nat} {name : String} {cats : List LMonoTy}
    (h : (name, cats) ∈ findPolymorphicOps pctx τ gen sampled m) :
    ∃ (bvs : List TyIdentifier) (body : LMonoTy) (fbvs : List TyIdentifier) (fbody : LMonoTy)
      (argTys : List LMonoTy) (retTy : LMonoTy) (k : Nat) (si : SubstInfo),
      (name, .forAll bvs body) ∈ pctx ∧
      freshenBoundVars bvs body (τ.freeVars ++ gen.flatMap LMonoTy.freeVars).eraseDups =
        (fbvs, fbody) ∧
      decomposeArrow fbody = (argTys, retTy) ∧
      Constraints.unify [((argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy, τ)]
        SubstInfo.empty = .ok si ∧
      LMonoTy.subst (substScope ((findFreeTyVars fbvs si.subst).zip sampled) ++ si.subst)
        ((argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ ∧
      cats = (argTys.take k).map
        (LMonoTy.subst (substScope ((findFreeTyVars fbvs si.subst).zip sampled) ++ si.subst)) := by
  unfold findPolymorphicOps at h
  simp only [List.mem_flatMap] at h
  obtain ⟨⟨nm, bvs, body⟩, hmem, hfilt⟩ := h
  obtain ⟨fbvs, fbody, hfreshEq⟩ :
      ∃ a b, freshenBoundVars bvs body
        (τ.freeVars ++ List.flatMap LMonoTy.freeVars gen).eraseDups = (a, b) :=
    ⟨_, _, rfl⟩
  obtain ⟨argTys, retTy, hdecEq⟩ : ∃ a b, decomposeArrow fbody = (a, b) := ⟨_, _, rfl⟩
  simp only [hfreshEq, hdecEq] at hfilt
  split at hfilt
  · exact absurd hfilt List.not_mem_nil
  rw [List.mem_filterMap] at hfilt
  obtain ⟨k, _, hopt⟩ := hfilt
  simp only [guard, bind, failure, pure, Option.bind_eq_some_iff,
    Option.ite_some_none_eq_some, Option.some.injEq, Prod.mk.injEq] at hopt
  obtain ⟨subst, hunif, _, ⟨_, _⟩, _, ⟨hguard, _⟩, hname, hcat⟩ := hopt
  unfold unifyTypes at hunif
  split at hunif
  · rename_i si hsi
    rw [Option.some.injEq] at hunif
    subst hunif hname
    exact ⟨bvs, body, fbvs, fbody, argTys, retTy, k, si, hmem, hfreshEq, hdecEq, hsi,
      beq_iff_eq.mp hguard, hcat.symm⟩
  · exact absurd hunif (by simp)

/-- **The argument types of a polymorphic candidate are registered** when the scheme bodies of
    `pctx`, the target type and the sampled types are: renaming and unification only combine
    registered types. -/
theorem findPolymorphicOps_args_known {ks : KnownTypes} (harrow : ks["arrow"]? = some 2)
    {pctx : PolyOpCtx} {τ : LMonoTy} {gen sampled : List LMonoTy} {m : Nat} {name : String}
    {cats : List LMonoTy}
    (hpctx : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx →
      LMonoTy.knownInstance body ks = true)
    (hτ : LMonoTy.knownInstance τ ks = true)
    (hsam : ∀ t ∈ sampled, LMonoTy.knownInstance t ks = true)
    (h : (name, cats) ∈ findPolymorphicOps pctx τ gen sampled m) :
    ∀ a ∈ cats, LMonoTy.knownInstance a ks = true := by
  obtain ⟨bvs, body, fbvs, fbody, argTys, retTy, k, si, hmem, hfresh, hdec, hunify, _, rfl⟩ :=
    findPolymorphicOps_mem_cases h
  have hrename : Subst.RangeKnown
      (freshenRenaming bvs (τ.freeVars ++ gen.flatMap LMonoTy.freeVars).eraseDups) ks := by
    refine rangeKnown_substScope _ ?_
    intro p hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    simp only [LMonoTy.knownInstance]
  have hfbody : LMonoTy.knownInstance fbody ks = true := by
    have hsnd := freshenBoundVars_snd_eq bvs body
      (τ.freeVars ++ gen.flatMap LMonoTy.freeVars).eraseDups
    rw [hfresh] at hsnd
    rw [show fbody = _ from hsnd]
    exact knownInstance_subst ks _ body hrename (hpctx name bvs body hmem)
  obtain ⟨hargs, hret⟩ := decomposeArrow_known harrow fbody hfbody
  rw [hdec] at hargs hret
  have hfold : ∀ (l : List LMonoTy), (∀ a ∈ l, LMonoTy.knownInstance a ks = true) →
      LMonoTy.knownInstance (l.foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) ks = true := by
    intro l
    induction l with
    | nil => intro _; exact hret
    | cons a rest ih =>
      intro hl
      exact (knownInstance_arrow_iff harrow _ _).mpr
        ⟨hl a List.mem_cons_self, ih (fun x hx => hl x (List.mem_cons_of_mem a hx))⟩
  have hupd := hfold (argTys.drop k) (fun a ha => hargs a (List.mem_of_mem_drop ha))
  have hempty : Subst.RangeKnown SubstInfo.empty.subst ks := by
    intro mty hmty
    simp only [SubstInfo.empty, Subst.empty, Strata.Util.HMaps.values] at hmty
    exact absurd hmty List.not_mem_nil
  have hcs : Constraints.Known
      [((argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy, τ)] ks := by
    intro c hc
    rw [List.mem_singleton.mp hc]
    exact ⟨hupd, hτ⟩
  have hsi := Constraints.unify_RangeKnown ks _ _ si hunify hempty hcs
  have hext : Subst.RangeKnown
      (substScope ((findFreeTyVars fbvs si.subst).zip sampled) ++ si.subst) ks := by
    intro mty hmty
    rw [Strata.Util.HMaps.values_append, List.mem_append] at hmty
    rcases hmty with hmty | hmty
    · refine rangeKnown_substScope _ ?_ mty hmty
      intro p hp
      exact hsam p.2 (List.of_mem_zip hp).2
    · exact hsi mty hmty
  intro a ha
  obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
  exact knownInstance_subst ks _ a₀ hext (hargs a₀ (List.mem_of_mem_take ha₀))

/-- A scheme of `pctx` has at most `maxBinders pctx` binders. -/
theorem le_maxBinders {pctx : PolyOpCtx} {nm : String} {bvs : List TyIdentifier} {body : LMonoTy}
    (h : (nm, LTy.forAll bvs body) ∈ pctx) : bvs.length ≤ maxBinders pctx := by
  induction pctx with
  | nil => exact absurd h List.not_mem_nil
  | cons q rest ih =>
    obtain ⟨qn, ⟨qbvs, qbody⟩⟩ := q
    show bvs.length ≤ max qbvs.length (maxBinders rest)
    rcases List.mem_cons.mp h with heq | hmem
    · cases heq
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-- **The argument types of a polymorphic candidate range over `tvars`** when the target type and
    the sampled types do, every scheme of `pctx` is closed, and there are at least as many sampled
    types as the largest number of binders of a scheme. Every binder that unification leaves open
    then receives a sampled type; every other binder is sent to a subterm of the target, because
    the renamed binders avoid the target's variables. -/
theorem findPolymorphicOps_args_vars {tvars : List TyIdentifier} {pctx : PolyOpCtx}
    {τ : LMonoTy} {gen sampled : List LMonoTy} {m : Nat} {name : String} {cats : List LMonoTy}
    (hpctx : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx → ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs)
    (hτ : ∀ v ∈ LMonoTy.freeVars τ, v ∈ tvars)
    (hsam : ∀ t ∈ sampled, ∀ v ∈ LMonoTy.freeVars t, v ∈ tvars)
    (hlen : maxBinders pctx ≤ sampled.length)
    (h : (name, cats) ∈ findPolymorphicOps pctx τ gen sampled m) :
    ∀ a ∈ cats, ∀ v ∈ LMonoTy.freeVars a, v ∈ tvars := by
  obtain ⟨bvs, body, fbvs, fbody, argTys, retTy, k, si, hmem, hfresh, hdec, hunify, hguard, rfl⟩ :=
    findPolymorphicOps_mem_cases h
  have hclosed := hpctx name bvs body hmem
  have hbound := le_maxBinders hmem
  let inUse := (τ.freeVars ++ gen.flatMap LMonoTy.freeVars).eraseDups
  let upd := (argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy
  let uninst := findFreeTyVars fbvs si.subst
  let ext := substScope (uninst.zip sampled) ++ si.subst
  -- The renamed binders avoid the variables in use, and the renamed body is over them.
  obtain ⟨hfbvsFresh, _⟩ := freshenBoundVars_disjoint bvs body inUse hclosed fbvs fbody hfresh
  have hfbvs : fbvs = bvs.map (renameTyVar bvs inUse) := by
    have hfst := freshenBoundVars_fst_eq bvs body inUse
    rw [hfresh] at hfst
    exact hfst
  have hfbodyVars : ∀ v ∈ LMonoTy.freeVars fbody, v ∈ fbvs := by
    have hsnd := freshenBoundVars_snd_eq bvs body inUse
    rw [hfresh] at hsnd
    intro v hv
    rw [show fbody = _ from hsnd] at hv
    obtain ⟨u, hu, hvu⟩ := freeVars_subst_exists _ body v hv
    rw [subst_freshenRenaming_ftvar] at hvu
    simp only [LMonoTy.freeVars, List.mem_singleton] at hvu
    rw [hfbvs, hvu]
    exact List.mem_map_of_mem (hclosed u hu)
  have hdecVars := decomposeArrow_freeVars fbody
  rw [hdec] at hdecVars
  -- The open binders are no more than the sampled types.
  have huninstLen : uninst.length ≤ sampled.length := by
    have hle : uninst.length ≤ fbvs.length := List.length_filter_le _ _
    rw [hfbvs, List.length_map] at hle
    omega
  have hτInUse : ∀ v ∈ LMonoTy.freeVars τ, v ∈ inUse := by
    intro v hv
    exact List.mem_eraseDups.mpr (List.mem_append_left _ hv)
  -- The image under `ext` of every renamed binder ranges over `tvars`.
  have himage : ∀ v ∈ fbvs, ∀ w ∈ LMonoTy.freeVars (LMonoTy.subst ext (.ftvar v)), w ∈ tvars := by
    intro v hv w hw
    cases hS : Strata.Util.HMaps.find? si.subst v with
    | none =>
      have hvu : v ∈ uninst := by
        refine List.mem_filter.mpr ⟨hv, ?_⟩
        rw [hS]
        rfl
      obtain ⟨t, ht, hlk⟩ := Freshening.lookup_zip_of_length_le uninst sampled huninstLen v hvu
      have hfind : Strata.Util.HMaps.find? ext v = some t := by
        refine Strata.Util.HMaps.find?_append_of_some ?_ si.subst
        rw [Freshening.find?_substScope_eq_lookup, hlk]
      rw [LMonoTy.subst_ftvar_of_some hfind] at hw
      exact hsam t ht w hw
    | some t =>
      have hvu : v ∉ uninst := by
        intro hvu
        have hnone := (List.mem_filter.mp hvu).2
        rw [hS] at hnone
        exact absurd hnone (by simp)
      have hlk : (uninst.zip sampled).lookup v = none := by
        cases hl : (uninst.zip sampled).lookup v with
        | none => rfl
        | some t' =>
          exact absurd (List.of_mem_zip (Freshening.lookup_mem _ _ _ hl)).1 hvu
      have hfind : Strata.Util.HMaps.find? ext v = some t := by
        rw [Strata.Util.HMaps.find?_append_of_none ?_ si.subst]
        · exact hS
        · rw [Freshening.find?_substScope_eq_lookup, hlk]
      by_cases hvupd : v ∈ LMonoTy.freeVars upd
      · have hwτ := freeVars_subst_mono ext upd v hvupd w hw
        rw [hguard] at hwτ
        exact hτ w hwτ
      · exfalso
        have hkey := Strata.Util.HMaps.find?_mem_keys si.subst hS
        rcases LExpr.Constraints.unify_keys_incl hunify v hkey with hk | hk | hk
        · simp only [SubstInfo.empty, Subst.empty, Strata.Util.HMaps.keys] at hk
          exact absurd hk List.not_mem_nil
        · simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
            List.mem_append] at hk
          rcases hk with hk | hk
          · exact hvupd hk
          · exact hfbvsFresh v hv (hτInUse v hk)
        · simp only [SubstInfo.empty, Subst.empty, Subst.freeVars, Strata.Util.HMaps.values,
            List.flatMap_nil] at hk
          exact absurd hk List.not_mem_nil
  intro a ha w hw
  obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
  obtain ⟨v, hv, hwv⟩ := freeVars_subst_exists _ a₀ w hw
  have hva₀ := hdecVars.1 a₀ (List.mem_of_mem_take ha₀) v hv
  exact himage v (hfbodyVars v hva₀) w hwv

/-! ## Binder and agreement conditions -/

/-- The binder and agreement conditions of expression well-typedness: the binder annotations of
    `e` are registered in `C`, and its free-variable and operator annotations agree with the
    variable scopes `ts` and the function table of `C`. -/
def AnnotsOk (C : LContext CoreLParams) (ts : TypeScopes) (e : LExpr') : Prop :=
  BinderAnnotsKnown C e ∧ ScopesAnnotAgree C ts e

/-- A term none of whose four annotation lists has an element meets the conditions. -/
theorem annotsOk_of_empty {C : LContext CoreLParams} {ts : TypeScopes} {e : LExpr'}
    (hb : LExpr.binderAnnotations e = []) (hf : LExpr.freeVars e = [])
    (ho : LExpr.opAnnots e = []) (hg : LExpr.getOps e = []) : AnnotsOk C ts e := by
  refine ⟨fun t ht => ?_, ⟨fun x ann hx => ?_, fun o ty hx => ?_, fun o hx => ?_⟩⟩
  · rw [hb] at ht
    exact absurd ht List.not_mem_nil
  · rw [hf] at hx
    exact absurd hx List.not_mem_nil
  · rw [ho] at hx
    exact absurd hx List.not_mem_nil
  · rw [hg] at hx
    exact absurd hx List.not_mem_nil

/-- A term satisfies `ScopesAnnotAgree` (its annotated free variables are declared in the scopes at
    their annotations, and its operator annotations instantiate the schemes of their functions)
    when the terms covering it do and it has no free variable, operator annotation or operator
    outside them. -/
theorem scopesAgree_of_subterms {C : LContext CoreLParams} {ts : TypeScopes} {e : LExpr'}
    (es : List LExpr') (hes : ∀ e' ∈ es, ScopesAnnotAgree C ts e')
    (hf : LExpr.freeVars e = es.flatMap LExpr.freeVars)
    (ho : LExpr.opAnnots e = es.flatMap LExpr.opAnnots)
    (hg : LExpr.getOps e = es.flatMap LExpr.getOps) : ScopesAnnotAgree C ts e := by
  refine ⟨fun x ann hx => ?_, fun o ty hx => ?_, fun o hx => ?_⟩
  · rw [hf] at hx
    obtain ⟨e', he', hx⟩ := List.mem_flatMap.mp hx
    exact (hes e' he').fvarsDeclared x ann hx
  · rw [ho] at hx
    obtain ⟨e', he', hx⟩ := List.mem_flatMap.mp hx
    exact (hes e' he').opsInstantiate o ty hx
  · rw [hg] at hx
    obtain ⟨e', he', hx⟩ := List.mem_flatMap.mp hx
    exact (hes e' he').opsKnown o hx

/-- The conditions hold of a term whose annotation lists are covered by those of terms that meet
    them, together with one registered binder annotation if `binder` is `some`. -/
theorem annotsOk_of_subterms {C : LContext CoreLParams} {ts : TypeScopes} {e : LExpr'}
    (es : List LExpr') (binder : Option LMonoTy) (hes : ∀ e' ∈ es, AnnotsOk C ts e')
    (hbinder : ∀ t ∈ binder, LMonoTy.knownInstance t C.knownTypes = true)
    (hb : LExpr.binderAnnotations e = binder.toList ++ es.flatMap LExpr.binderAnnotations)
    (hf : LExpr.freeVars e = es.flatMap LExpr.freeVars)
    (ho : LExpr.opAnnots e = es.flatMap LExpr.opAnnots)
    (hg : LExpr.getOps e = es.flatMap LExpr.getOps) : AnnotsOk C ts e := by
  refine ⟨fun t ht => ?_, scopesAgree_of_subterms es (fun e' he' => (hes e' he').2) hf ho hg⟩
  rw [hb, List.mem_append] at ht
  rcases ht with ht | ht
  · exact hbinder t (Option.mem_toList.mp ht)
  · obtain ⟨e', he', ht⟩ := List.mem_flatMap.mp ht
    exact (hes e' he').1 t ht

/-- The context conditions under which every expression `genLExpr` draws meets the binder and
    agreement conditions in context `C` and variable scopes `ts`.

    `C` registers the built-in types and gives every function the type scheme of its signature.
    Every free variable of `fctx` is declared in `ts` at its registered type. Every operator of
    `octx` has a registered type that instantiates the signature of the function of `C` of its
    name, and every scheme of `pctx` is the registered scheme of a function of `C`. -/
structure ExprCtxOk (C : LContext CoreLParams) (ts : TypeScopes) (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) : Prop where
  arities : SimpleTyArities C
  sigs : ∀ (name : String) f, C.functions[name]? = some f →
    f.type = .ok (.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))
  fvars : ∀ p ∈ fctx, LMonoTy.knownInstance p.2 C.knownTypes = true ∧
    ts.find? ⟨p.1, ()⟩ = some (.forAll [] p.2)
  ops : ∀ p ∈ octx.ops, LMonoTy.knownInstance p.2 C.knownTypes = true ∧
    ∃ f, C.functions[p.1]? = some f ∧
      ∃ σ, p.2 = LMonoTy.subst σ (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))
  polys : PCtxWF C.functions pctx
  polysKnown : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx →
    LMonoTy.knownInstance body C.knownTypes = true

/-- The context conditions survive moving to fewer operators and schemes, and to free variables
    declared, at registered types, in other variable scopes. -/
theorem ExprCtxOk.restrict {C : LContext CoreLParams} {ts ts' : TypeScopes}
    {fctx fctx' : FVarCtx} {octx octx' : OpCtx} {pctx pctx' : PolyOpCtx}
    (h : ExprCtxOk C ts fctx octx pctx)
    (hf : ∀ p ∈ fctx', LMonoTy.knownInstance p.2 C.knownTypes = true ∧
      ts'.find? ⟨p.1, ()⟩ = some (.forAll [] p.2))
    (ho : ∀ p ∈ octx'.ops, p ∈ octx.ops) (hp : ∀ p ∈ pctx', p ∈ pctx) :
    ExprCtxOk C ts' fctx' octx' pctx' where
  arities := h.arities
  sigs := h.sigs
  fvars := hf
  ops := fun p hmem => h.ops p (ho p hmem)
  polys := fun name lty hmem => h.polys name lty (hp _ hmem)
  polysKnown := fun nm bvs body hmem => h.polysKnown nm bvs body (hp _ hmem)

/-- A function whose formals and type parameters are distinct and whose output is registered,
    with `arrow` registered at arity 2, has the type scheme of its signature. -/
theorem type_eq_of_sigWF {f : LFunc CoreLParams} {ks : KnownTypes}
    (harrow : ks["arrow"]? = some 2) (hin : f.inputs.keys.Nodup) (hta : f.typeArgs.Nodup)
    (hout : LMonoTy.knownInstance f.output ks = true) :
    f.type = .ok (.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))) := by
  have hok : ∃ ty, f.type = .ok ty := by
    unfold LFunc.type LFuncDefined.type
    simp only [hin, hta, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨ty, hty⟩ := hok
  rw [hty, LFunc.type_eq_mkArrow' harrow hty hout]

/-- The built-in arities survive growing the registered types. -/
theorem simpleTyArities_mono {C C' : LContext CoreLParams} (h : SimpleTyArities C)
    (hk : KnownTypesExtends C.knownTypes C'.knownTypes) : SimpleTyArities C' :=
  ⟨hk _ _ h.bool, hk _ _ h.int, hk _ _ h.string, hk _ _ h.real, hk _ _ h.regex, hk _ _ h.arrow,
    hk _ _ h.map, hk _ _ h.seq⟩

/-- The context conditions survive growing the registered types of `C` with its functions
    unchanged. -/
theorem ExprCtxOk.mono {C C' : LContext CoreLParams} {ts : TypeScopes} {fctx : FVarCtx}
    {octx : OpCtx} {pctx : PolyOpCtx} (h : ExprCtxOk C ts fctx octx pctx)
    (hfun : C'.functions = C.functions) (hk : KnownTypesExtends C.knownTypes C'.knownTypes) :
    ExprCtxOk C' ts fctx octx pctx where
  arities := simpleTyArities_mono h.arities hk
  sigs := by
    rw [hfun]
    exact h.sigs
  fvars := fun p hp =>
    ⟨knownInstance_mono _ _ _ hk (h.fvars p hp).1, (h.fvars p hp).2⟩
  ops := by
    rw [hfun]
    exact fun p hp => ⟨knownInstance_mono _ _ _ hk (h.ops p hp).1, (h.ops p hp).2⟩
  polys := by
    rw [hfun]
    exact h.polys
  polysKnown := fun nm bvs body hmem => knownInstance_mono _ _ _ hk (h.polysKnown nm bvs body hmem)

/-- The context conditions survive extending the function table of `C` with functions that have
    the type schemes of their signatures. -/
theorem ExprCtxOk.extend {C C' : LContext CoreLParams} {ts : TypeScopes} {fctx : FVarCtx}
    {octx : OpCtx} {pctx : PolyOpCtx} {newFuncs : List (LFunc CoreLParams)}
    (h : ExprCtxOk C ts fctx octx pctx)
    (hext : FactoryExtendedBy (fun f g => g = f) C C' newFuncs)
    (hnew : ∀ f ∈ newFuncs,
      f.type = .ok (.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))) :
    ExprCtxOk C' ts fctx octx pctx where
  arities := simpleTyArities_mono h.arities (fun _ _ hv => by rw [hext.knownTypes_eq]; exact hv)
  sigs := by
    intro name f hf
    cases hold : C.functions[name]? with
    | some g =>
      rw [hext.preserves_old name g hold, Option.some.injEq] at hf
      rw [← hf]
      exact h.sigs name g hold
    | none =>
      rcases hext.no_other name (Factory.memOfGetElem? hf) with hmem | hmem
      · rw [mem_get?_eq hmem rfl] at hold
        exact absurd hold (by simp)
      · obtain ⟨f', hf', hname⟩ := List.mem_map.mp hmem
        obtain ⟨g, hg, hgf⟩ := hext.contains_new f' hf'
        rw [hname, hf, Option.some.injEq] at hg
        rw [hg, hgf]
        exact hnew f' hf'
  fvars := by
    rw [hext.knownTypes_eq]
    exact h.fvars
  ops := by
    intro p hp
    obtain ⟨hk, f, hf, hσ⟩ := h.ops p hp
    rw [hext.knownTypes_eq]
    exact ⟨hk, f, hext.preserves_old _ f hf, hσ⟩
  polys := by
    intro name lty hmem
    obtain ⟨fn, hfn, hlty⟩ := h.polys name lty hmem
    exact ⟨fn, hext.preserves_old name fn hfn, hlty⟩
  polysKnown := by
    rw [hext.knownTypes_eq]
    exact h.polysKnown

/-- An operator annotated with an instance of the signature of the function of `C` of its name,
    when every function of `C` has the type scheme of its signature, satisfies `ScopesAnnotAgree`
    (in any variable scopes) and has no binder annotation. -/
theorem annotsOk_op {C : LContext CoreLParams} {ts : TypeScopes}
    (hsigs : ∀ (name : String) f, C.functions[name]? = some f →
      f.type = .ok (.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))))
    {name : String} {ty : LMonoTy} {f : LFunc CoreLParams} (hf : C.functions[name]? = some f)
    {σ : Subst} (hty : ty = LMonoTy.subst σ (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))) :
    AnnotsOk C ts (.op () ⟨name, ()⟩ (some ty)) := by
  refine ⟨fun t ht => ?_, ⟨fun x ann hx => ?_, fun o ty' hx => ?_, fun o hx => ?_⟩⟩
  · simp [LExpr.binderAnnotations] at ht
  · simp [LExpr.freeVars] at hx
  · simp only [LExpr.opAnnots, Option.toList_some, List.map_cons, List.map_nil,
      List.mem_singleton, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨f, f.typeArgs, _, hf, hsigs name f hf, σ, hty⟩
  · simp only [LExpr.getOps, List.mem_singleton] at hx
    rw [hx, hf]
    rfl

/-- **The closure conditions for registered binder annotations and for `ScopesAnnotAgree`**, with
    registered types as the type invariant. `ScopesAnnotAgree` asks that every annotated free
    variable be declared in the scopes at its annotation and that every operator annotation
    instantiate the scheme of its function in `C`. -/
theorem closureHyps_annotsOk {C : LContext CoreLParams} {ts : TypeScopes} {fctx : FVarCtx}
    {octx : OpCtx} {pctx : PolyOpCtx} (tvars : List TyIdentifier)
    (hctx : ExprCtxOk C ts fctx octx pctx) :
    ClosureHyps fctx octx pctx tvars (fun t => LMonoTy.knownInstance t C.knownTypes = true)
      (AnnotsOk C ts) where
  arrow := knownInstance_arrow_iff hctx.arities.arrow
  bool := by
    simp [LMonoTy.knownInstance, LMonoTys.knownInstances, KnownTypes.contains,
      Identifiers.contains, KnownType.arity, hctx.arities.bool]
  genTy := fun n _ ht => StrataGenerators.Function.genLMonoTy_mem_knownInstance hctx.arities ⟨n, ht⟩
  fctxTy := fun p hp => (hctx.fvars p hp).1
  octxTy := fun p hp => (hctx.ops p hp).1
  polyArgs := fun _ _ _ _ _ hτ _ hsam _ hmem =>
    findPolymorphicOps_args_known hctx.arities.arrow hctx.polysKnown hτ hsam hmem
  const := fun _ => annotsOk_of_empty rfl rfl rfl rfl
  bvar := fun _ => annotsOk_of_empty rfl rfl rfl rfl
  fvar := by
    intro p hp
    refine ⟨fun t ht => ?_, ⟨fun x ann hx => ?_, fun o ty hx => ?_, fun o hx => ?_⟩⟩
    · simp [LExpr.binderAnnotations] at ht
    · simp only [LExpr.freeVars, List.mem_singleton, Prod.mk.injEq, Option.some.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact (hctx.fvars p hp).2
    · simp [LExpr.opAnnots] at hx
    · simp [LExpr.getOps] at hx
  op := by
    intro p hp
    obtain ⟨_, f, hf, σ, hty⟩ := hctx.ops p hp
    exact annotsOk_op hctx.sigs hf hty
  polyOp := by
    intro τ gen sampled name cats _ _ _ _ hmem
    obtain ⟨fn, S, hget, hinst⟩ :=
      findPolymorphicOps_instanceR C.functions pctx τ gen sampled 3 hctx.polys name cats hmem
    exact annotsOk_op hctx.sigs hget hinst
  abs := fun τ body hτ hbody =>
    annotsOk_of_subterms [body] (some τ) (List.forall_mem_singleton.mpr hbody)
      (fun t ht => (Option.mem_some_iff.mp ht) ▸ hτ)
      (by simp [LExpr.binderAnnotations]) (by simp [LExpr.freeVars])
      (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])
  app := fun f a hf ha =>
    annotsOk_of_subterms [f, a] none (by simp [hf, ha]) (fun t ht => absurd ht (by simp))
      (by simp [LExpr.binderAnnotations]) (by simp [LExpr.freeVars])
      (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])
  ite := fun c t f hc ht hf =>
    annotsOk_of_subterms [c, t, f] none (by simp [hc, ht, hf]) (fun t ht => absurd ht (by simp))
      (by simp [LExpr.binderAnnotations]) (by simp [LExpr.freeVars])
      (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])
  eq := fun a b ha hb =>
    annotsOk_of_subterms [a, b] none (by simp [ha, hb]) (fun t ht => absurd ht (by simp))
      (by simp [LExpr.binderAnnotations]) (by simp [LExpr.freeVars])
      (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])
  quant := fun k τ tr body hτ htr hbody =>
    annotsOk_of_subterms [tr, body] (some τ) (by simp [htr, hbody])
      (fun t ht => (Option.mem_some_iff.mp ht) ▸ hτ)
      (by simp [LExpr.binderAnnotations]) (by simp [LExpr.freeVars])
      (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])

/-- **Every expression `genLExpr` draws at a registered type is well-typed** in context `C` and
    variable scopes `ts`, when the contexts it reads agree with `C` and `ts` (`ExprCtxOk`). -/
theorem genLExpr_exprWellTyped {C : LContext CoreLParams} {ts : TypeScopes} {fctx : FVarCtx}
    {octx : OpCtx} {pctx : PolyOpCtx} {tvars : List TyIdentifier}
    (hctx : ExprCtxOk C ts fctx octx pctx) {depth : Nat} {τ : LMonoTy}
    (hτ : LMonoTy.knownInstance τ C.knownTypes = true) {e : LExpr'}
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ)) :
    ExprWellTyped C ts e τ := by
  have hok := genLExpr_closed (closureHyps_annotsOk tvars hctx) depth []
    τ (fun _ ht => absurd ht List.not_mem_nil) hτ e he
  exact ⟨genLExpr_sound fctx octx pctx tvars [] depth τ _ e he, hok.1, hok.2⟩

/-- The context conditions under which every expression `genLExpr` draws meets the agreement
    condition with the variable scopes `ts` and the function table of `C`: every function of `C`
    has the type scheme of its signature, every free variable of `fctx` is declared in `ts` at its
    type, every operator of `octx` has a type that instantiates the signature of the function of
    `C` of its name, and every scheme of `pctx` is the registered scheme of a function of `C`. -/
structure ScopesCtxOk (C : LContext CoreLParams) (ts : TypeScopes) (fctx : FVarCtx)
    (octx : OpCtx) (pctx : PolyOpCtx) : Prop where
  sigs : ∀ (name : String) f, C.functions[name]? = some f →
    f.type = .ok (.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))
  fvars : ∀ p ∈ fctx, ts.find? ⟨p.1, ()⟩ = some (.forAll [] p.2)
  ops : ∀ p ∈ octx.ops, ∃ f, C.functions[p.1]? = some f ∧
    ∃ σ, p.2 = LMonoTy.subst σ (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))
  polys : PCtxWF C.functions pctx

/-- **The closure conditions for `ScopesAnnotAgree` alone**, with no condition on types:
    annotated free variables are declared in the scopes at their annotations, and operator
    annotations instantiate the schemes of their functions in `C`. -/
theorem closureHyps_scopes {C : LContext CoreLParams} {ts : TypeScopes} {fctx : FVarCtx}
    {octx : OpCtx} {pctx : PolyOpCtx} (tvars : List TyIdentifier)
    (hctx : ScopesCtxOk C ts fctx octx pctx) :
    ClosureHyps fctx octx pctx tvars (fun _ => True) (ScopesAnnotAgree C ts) where
  arrow := fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  bool := trivial
  genTy := fun _ _ _ => trivial
  fctxTy := fun _ _ => trivial
  octxTy := fun _ _ => trivial
  polyArgs := by intros; trivial
  const := fun _ => (annotsOk_of_empty rfl rfl rfl rfl).2
  bvar := fun _ => (annotsOk_of_empty rfl rfl rfl rfl).2
  fvar := by
    intro p hp
    refine ⟨fun x ann hx => ?_, fun o ty hx => ?_, fun o hx => ?_⟩
    · simp only [LExpr.freeVars, List.mem_singleton, Prod.mk.injEq, Option.some.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hctx.fvars p hp
    · simp [LExpr.opAnnots] at hx
    · simp [LExpr.getOps] at hx
  op := by
    intro p hp
    obtain ⟨f, hf, σ, hty⟩ := hctx.ops p hp
    exact (annotsOk_op hctx.sigs hf hty).2
  polyOp := by
    intro τ gen sampled name cats _ _ _ _ hmem
    obtain ⟨fn, S, hget, hinst⟩ :=
      findPolymorphicOps_instanceR C.functions pctx τ gen sampled 3 hctx.polys name cats hmem
    exact (annotsOk_op hctx.sigs hget hinst).2
  abs := fun _ body _ hbody =>
    scopesAgree_of_subterms [body] (List.forall_mem_singleton.mpr hbody)
      (by simp [LExpr.freeVars]) (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])
  app := fun f a hf ha =>
    scopesAgree_of_subterms [f, a] (by simp [hf, ha])
      (by simp [LExpr.freeVars]) (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])
  ite := fun c t f hc ht hf =>
    scopesAgree_of_subterms [c, t, f] (by simp [hc, ht, hf])
      (by simp [LExpr.freeVars]) (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])
  eq := fun a b ha hb =>
    scopesAgree_of_subterms [a, b] (by simp [ha, hb])
      (by simp [LExpr.freeVars]) (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])
  quant := fun _ _ tr body _ htr hbody =>
    scopesAgree_of_subterms [tr, body] (by simp [htr, hbody])
      (by simp [LExpr.freeVars]) (by simp [LExpr.opAnnots]) (by simp [LExpr.getOps])

/-- **Every expression `genLExpr` draws satisfies `ScopesAnnotAgree`**: its annotated free
    variables are declared in the variable scopes `ts` at their annotations, and its operator
    annotations instantiate the schemes of their functions in `C`. This holds at every type when
    the contexts the generator reads agree with `C` and `ts` (`ScopesCtxOk`). -/
theorem genLExpr_scopesAnnotAgree {C : LContext CoreLParams} {ts : TypeScopes} {fctx : FVarCtx}
    {octx : OpCtx} {pctx : PolyOpCtx} {tvars : List TyIdentifier}
    (hctx : ScopesCtxOk C ts fctx octx pctx) {depth : Nat} {τ : LMonoTy} {e : LExpr'}
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ)) :
    ScopesAnnotAgree C ts e :=
  genLExpr_closed (closureHyps_scopes tvars hctx) depth [] τ (fun _ _ => trivial) trivial e he

/-! ## Annotation type variables -/

/-- The context conditions under which every annotation type variable of an expression `genLExpr`
    draws is in `tvars`: the types of `fctx` and `octx` range over `tvars`, and every scheme of
    `pctx` is closed. -/
structure ExprScopedCtx (tvars : List TyIdentifier) (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) : Prop where
  fvars : ∀ p ∈ fctx, ∀ v ∈ LMonoTy.freeVars p.2, v ∈ tvars
  ops : ∀ p ∈ octx.ops, ∀ v ∈ LMonoTy.freeVars p.2, v ∈ tvars
  polys : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx → ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs

/-- The annotation type variables of a term are in `tvars` when those of the terms covering it
    are and those of its own annotation, if any, are. -/
theorem annotTyVars_of_subterms {tvars : List TyIdentifier} {e : LExpr'} (es : List LExpr')
    (ann : Option LMonoTy) (hes : ∀ e' ∈ es, ∀ v ∈ annotTyVars e', v ∈ tvars)
    (hann : ∀ t ∈ ann, ∀ v ∈ LMonoTy.freeVars t, v ∈ tvars)
    (he : annotTyVars e = ann.elim [] LMonoTy.freeVars ++ es.flatMap annotTyVars) :
    ∀ v ∈ annotTyVars e, v ∈ tvars := by
  intro v hv
  rw [he, List.mem_append] at hv
  rcases hv with hv | hv
  · cases ann with
    | none => exact absurd hv List.not_mem_nil
    | some t => exact hann t rfl v hv
  · obtain ⟨e', he', hv⟩ := List.mem_flatMap.mp hv
    exact hes e' he' v hv

/-- **The closure conditions for the scoping fact**, with the types over `tvars` as the type
    invariant. -/
theorem closureHyps_annotTyVars {tvars : List TyIdentifier} {fctx : FVarCtx} {octx : OpCtx}
    {pctx : PolyOpCtx} (hsc : ExprScopedCtx tvars fctx octx pctx) :
    ClosureHyps fctx octx pctx tvars (fun t => ∀ v ∈ LMonoTy.freeVars t, v ∈ tvars)
      (fun e => ∀ v ∈ annotTyVars e, v ∈ tvars) where
  arrow := freeVars_arrow_iff tvars
  bool := fun v hv => by simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv
  genTy := fun _ _ ht => StrataGenerators.Function.allFtvarsIn_freeVars (genLMonoTy_mem_ftvars ht)
  fctxTy := hsc.fvars
  octxTy := hsc.ops
  polyArgs := by
    intro _ _ sampled _ _ hτ _ hsam hlen hmem
    have hle : maxBinders pctx ≤ sampled.length := by
      rw [hlen]
      exact Nat.le_max_right _ _
    exact findPolymorphicOps_args_vars hsc.polys hτ hsam hle hmem
  const := fun _ v hv => by simp [annotTyVars, exprAnnotTys] at hv
  bvar := fun _ v hv => by simp [annotTyVars, exprAnnotTys] at hv
  fvar := fun p hp => annotTyVars_of_subterms [] (some p.2) (fun _ h => absurd h List.not_mem_nil)
    (fun t ht => (Option.mem_some_iff.mp ht) ▸ hsc.fvars p hp) (by simp [annotTyVars, exprAnnotTys])
  op := fun p hp => annotTyVars_of_subterms [] (some p.2) (fun _ h => absurd h List.not_mem_nil)
    (fun t ht => (Option.mem_some_iff.mp ht) ▸ hsc.ops p hp) (by simp [annotTyVars, exprAnnotTys])
  polyOp := by
    intro τ gen sampled name cats hτ _ hsam hlen hmem
    have hle : maxBinders pctx ≤ sampled.length := by
      rw [hlen]
      exact Nat.le_max_right _ _
    have hcats := findPolymorphicOps_args_vars hsc.polys hτ hsam hle hmem
    have hann : ∀ v ∈ LMonoTy.freeVars (cats.foldr (fun σ acc => LMonoTy.arrow σ acc) τ),
        v ∈ tvars := by
      clear hmem
      induction cats with
      | nil => exact hτ
      | cons a rest ih =>
        exact (freeVars_arrow_iff tvars a _).mpr
          ⟨hcats a List.mem_cons_self, ih (fun x hx => hcats x (List.mem_cons_of_mem a hx))⟩
    exact annotTyVars_of_subterms [] (some _) (fun _ h => absurd h List.not_mem_nil)
      (fun t ht => (Option.mem_some_iff.mp ht) ▸ hann) (by simp [annotTyVars, exprAnnotTys])
  abs := fun τ body hτ hbody =>
    annotTyVars_of_subterms [body] (some τ) (List.forall_mem_singleton.mpr hbody)
      (fun t ht => (Option.mem_some_iff.mp ht) ▸ hτ) (by simp [annotTyVars, exprAnnotTys])
  app := fun f a hf ha =>
    annotTyVars_of_subterms [f, a] none
      (List.forall_mem_cons.mpr ⟨hf, List.forall_mem_singleton.mpr ha⟩)
      (fun t ht => absurd ht (by simp))
      (by simp [annotTyVars, exprAnnotTys])
  ite := fun c t f hc ht hf =>
    annotTyVars_of_subterms [c, t, f] none
      (List.forall_mem_cons.mpr
        ⟨hc, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_singleton.mpr hf⟩⟩)
      (fun t ht => absurd ht (by simp))
      (by simp [annotTyVars, exprAnnotTys])
  eq := fun a b ha hb =>
    annotTyVars_of_subterms [a, b] none
      (List.forall_mem_cons.mpr ⟨ha, List.forall_mem_singleton.mpr hb⟩)
      (fun t ht => absurd ht (by simp))
      (by simp [annotTyVars, exprAnnotTys])
  quant := fun k τ tr body hτ htr hbody =>
    annotTyVars_of_subterms [tr, body] (some τ)
      (List.forall_mem_cons.mpr ⟨htr, List.forall_mem_singleton.mpr hbody⟩)
      (fun t ht => (Option.mem_some_iff.mp ht) ▸ hτ) (by simp [annotTyVars, exprAnnotTys])

/-- **Every annotation type variable of an expression `genLExpr` draws at a type over `tvars` is in
    `tvars`**, when the contexts it reads range over `tvars` (`ExprScopedCtx`). -/
theorem genLExpr_annotTyVars {tvars : List TyIdentifier} {fctx : FVarCtx} {octx : OpCtx}
    {pctx : PolyOpCtx} (hsc : ExprScopedCtx tvars fctx octx pctx) {depth : Nat} {τ : LMonoTy}
    (hτ : ∀ v ∈ LMonoTy.freeVars τ, v ∈ tvars) {e : LExpr'}
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ)) :
    ∀ v ∈ annotTyVars e, v ∈ tvars :=
  genLExpr_closed (closureHyps_annotTyVars hsc) depth [] τ
    (fun _ ht => absurd ht List.not_mem_nil) hτ e he

end StrataGenerators.AnnotFacts
