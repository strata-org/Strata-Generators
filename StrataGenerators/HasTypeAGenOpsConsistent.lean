import StrataGenerators.HasTypeAGen
import StrataGenerators.HasTypeAGen.Defs
import StrataGenerators.HasTypeAGen.IndirSupport
import StrataGenerators.HasTypeAGen.OpsConsistentBridge
import Strata.DL.Lambda.Denote.Assumptions
import Basalt.Walk.Entry
import Basalt.Walk.Sound

open Lambda RandomChoice ArbNat ArbChar ArbString

set_option linter.unusedSimpArgs false

/-!
# `OpsConsistentR` for a generated `LExpr`

This module proves that the generator gives a term that satisfies the *declarative*
`OpsConsistentR` predicate of Strata. That predicate is the inductive specification which says that each
type annotation on an `.op` node is *some* instance of the generic type of the factory function. The
soundness proof and the completeness proof for `HasTypeA` are in `HasTypeAGen.lean`. Together with them,
this module makes the generator sound and complete against *both* `HasTypeA` and `OpsConsistentR`.

Each proof here names `OpsConsistentR` directly, and this module holds no copy of it. Each proof is
stated against `OpsConsistentR` and closed by its constructors, so no proof unfolds the operational
`OpsConsistent`, and none uses the bridge between the two. The proofs need one helper that only a
`module` file can give, which is `mem_get?_eq`, a lookup in the `nameMap` of a `Factory`, in
`HasTypeAGen/OpsConsistentBridge.lean`.

Work against the declarative `OpsConsistentR` keeps these proofs simple. The `.op` check of the
operational `OpsConsistent` runs `opTypeSubst`, and it asks that unification can *rebuild* the
annotation. The `.op_in` constructor of `OpsConsistentR` asks only that an instantiating substitution
*exists*, and the generator builds each polymorphic annotation as exactly such an instance. Therefore no
proof here needs a result about the completeness of unification over a ground type.

## Why the generator satisfies `OpsConsistentR`

Each `.op` node that a generated term can hold comes from one of two places:

* **`pickOp`**, inside `genLExprBase`. The annotation is exactly the *generic* factory type of the
  operator, which `factoryOps` computes. It is therefore the instance under the identity substitution,
  which `OpsConsistentR.op_in` accepts directly. The same holds for the `.op` node of the monomorphic
  Indir rule.
* **`genIndirPoly`**. The annotation is `concreteArgTys.foldr arrow τ`, and the generator builds it as a
  substitution instance of the generic type of the operator. That instance is the renaming of the bound
  variables, together with the substitution of the generator. The guard in `findPolymorphicOps` asks
  that the substitution sends the result type to `τ`, so the instance targets `τ`.
  `findPolymorphicOps_instanceR` recovers one witnessing substitution, from the hypothesis `PCtxWF`
  about the factory, through `PolyOpsConsistentR_of_PCtxWF`. That step gives
  `genLExpr_opsConsistentR_of_PCtxWF`, which needs no hypothesis. This route also permits an annotation
  that names a free type variable, which no binder of the scheme quantifies.

Each compound case, which is `.app`, `.ite`, `.abs`, `.eq` or `.quant`, is structural.

## `OpsConsistentR` on the side of *completeness*

The last section of this file uses the same judgment in the other direction. It discharges the
`SchemeInstAt` predicate of `HasTypeAGen.lean`, which is the witness at the level of the specification
that the completeness of the polymorphic case needs, from an `OpsConsistentR F e` of the caller. That
step is `schemeInstAt_of_opsConsistentR`, and `genLExpr_complete_poly_opsConsistentR` packages the
result. That theorem gives reachability from the two judgments alone, with no generator internal in its
hypotheses.

`OpsConsistentR` must be a *premise* there. The `.op` rule of `HasTypeA'` accepts each annotation that a
node carries, so a well-typed term can carry an annotation that is not an instance of the scheme of the
operator. The generator would never emit such a term, and `OpsConsistentR.op_in` is the judgment that
excludes it, and it gives the instantiating substitution. The two directions therefore stay symmetric:
on the side of soundness, both judgments are theorems about a generated term, and on the side of
completeness, both are assumptions about the target term.

### A defect in `freshenBoundVars` that this section exposes

The construction of the matcher needs the renaming of `freshenBoundVars` to be injective on the binders
of the scheme, which the hypothesis `hfreshNodup` gives. That condition does *not* always hold:

```lean
#eval freshenBoundVars ["a", "b"] (LMonoTy.arrow (.ftvar "a") (.ftvar "b")) ["a"]
-- (["b", "b"], b → b)
```

`freshenBoundVars` renames the binders that clash with the set of the names in use, and it draws each
replacement name outside that set. It does not draw a name outside **the other binders of the scheme**.
Therefore a renamed binder can take the name of another binder, and two different type variables become
one. The scheme `∀ a b. a → b` then instantiates at `b → b` only, and no matcher exists for a true
instance such as `int → bool`. That is a real hole in completeness, and it is narrow. A filter of the
supply of the fresh names against the set of the names in use *and* the binders of the scheme would
close it. Such a change changes the output of `freshenBoundVars`, so it belongs to a change of that
function. A scheme with one binder cannot suffer this collapse, and most entries of `corePolyOps` have
one binder.
-/

-- ── The description of `factoryOps` ──────────────────────────────────

/-- Each operator entry that `factoryOps F` gives resolves to a factory function whose generic type is
    exactly the type of that entry. `factoryOps` builds the type as `mkArrow' fn.output fn.inputs.values`
    directly, so the equality of the two types is immediate. -/
theorem factoryOps_mem_char (F : @Factory LExprParams') (nm : String) (τ : LMonoTy)
    (h : (nm, τ) ∈ (factoryOps F).ops) :
    ∃ fn, F[nm]? = some fn ∧ τ = LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd) := by
  unfold factoryOps at h
  simp only [OpCtx.ops_ofList, List.mem_filterMap] at h
  obtain ⟨fn, hfn_mem, hfn_eq⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at hfn_eq
  obtain ⟨hnm, hτ⟩ := hfn_eq
  subst hnm
  have hfn_mem' : fn ∈ F.toArray := Array.mem_def.mpr hfn_mem
  obtain ⟨hs, hget⟩ := Factory.memNameGetElem hfn_mem' rfl
  exact ⟨fn, Lambda.mem_get?_eq hs hget, hτ.symm⟩

-- ── Well-formedness of `pctx` and the factory ────────────────────────

/-- The well-formedness condition that ties a polymorphic operator context `pctx` to the factory `F`. Each
    entry of `pctx` is the polymorphic type scheme of a factory function `fn`, and `F` holds `fn` under the
    name of that entry.

    The *declarative* `OpsConsistentR` relation needs this condition only, and it needs no invariant that
    the free variables of a scheme are among its binders. The `.op_in` constructor of `OpsConsistentR` asks
    only that a substitution *exists* which sends the generic type to the annotation, and the generator
    builds its annotation as exactly such an instance. Read `findPolymorphicOps_instanceR`. No proof here
    runs `opTypeSubst`, so the case for a monomorphic operator, which forces the extra invariant in a proof
    against the operational predicate, does not occur. -/
def PCtxWF (F : @Factory LExprParams') (pctx : PolyOpCtx) : Prop :=
  ∀ (name : String) (lty : Lambda.LTy),
    (name, lty) ∈ pctx →
    ∃ (fn : LFunc LExprParams'), F[name]? = some fn ∧
      lty = .forAll fn.typeArgs (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))

/-- A polymorphic operator context that comes directly from a factory is always well formed against that
    factory. `factoryPolyOps` builds each entry as exactly the scheme that `PCtxWF` asks for, so the proof
    only follows the `filterMap`, and it needs no assumption. That fact is what makes a generator over a
    factory op-consistent with no hypothesis, and also with a polymorphic operator. Read
    `genLExpr_opsConsistentR_factory`. -/
theorem PCtxWF_factoryPolyOps (F : @Factory LExprParams') :
    PCtxWF F (factoryPolyOps F) := by
  intro name lty h
  unfold factoryPolyOps at h
  simp only [List.mem_filterMap] at h
  obtain ⟨fn, hfn_mem, hfn_eq⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at hfn_eq
  obtain ⟨hnm, hlty⟩ := hfn_eq
  subst hnm
  have hfn_mem' : fn ∈ F.toArray := Array.mem_def.mpr hfn_mem
  obtain ⟨hs, hget⟩ := Factory.memNameGetElem hfn_mem' rfl
  exact ⟨fn, Lambda.mem_get?_eq hs hget, hlty.symm⟩

-- ── The consistency of an `.op` leaf from `pickOp` ───────────────────

/-- Membership in `opsOfType octx τ` implies `(name, τ) ∈ octx.ops`. -/
theorem mem_opsOfType (octx : OpCtx) (τ : LMonoTy) (name : String)
    (h : name ∈ opsOfType octx τ) : (name, τ) ∈ octx.ops := by
  rw [opsOfType_eq_scan] at h
  simp only [opsOfTypeList, List.mem_filterMap] at h
  obtain ⟨⟨x, ty⟩, hmem, heq⟩ := h
  split at heq
  · rename_i hty; simp only [Option.some.injEq] at heq
    have : ty = τ := beq_iff_eq.mp hty
    subst this; subst heq; exact hmem
  · simp at heq

/-- An `.op` node that `pickOp` emits over `factoryOps F` satisfies `Lambda.OpsConsistentR`. The annotation
    `τ` equals the generic factory type of the operator, which is exactly the instance that
    `OpsConsistentR.op_in` needs, under the identity substitution. -/
theorem pickOp_opsConsistentR (F : @Factory LExprParams') (τ : LMonoTy) (name : String)
    (hmem : name ∈ opsOfType (factoryOps F) τ) :
    Lambda.OpsConsistentR F (.op () ⟨name, ()⟩ (some τ)) := by
  have hoctx : (name, τ) ∈ (factoryOps F).ops := mem_opsOfType _ _ _ hmem
  obtain ⟨fn, hget, hτ⟩ := factoryOps_mem_char F name τ hoctx
  -- The equation `τ = genericTy` gives the instance under the identity substitution.
  exact .op_in (tySubst := []) hget (by rw [hτ]; exact (LMonoTy.subst_of_hasEmptyScopes (by simp) _).symm)

-- ── The public support lemmas for each `pick*` generator ─────────────

private theorem list_map_ne_nil_of_length_pos' {α β : Type} {xs : List α} {f : α → β}
    (h : xs.length > 0) : xs.map f ≠ [] := by
  intro heq
  apply List.ne_nil_of_length_pos h
  apply List.map_eq_nil_iff.mp heq

theorem mem_support_pickOp_iff' {octx : OpCtx} {τ : LMonoTy}
    {hv : (opsOfType octx τ).length > 0} {e : LExpr'} :
    e ∈ SPMF.support (pickOp (G := SPMF) octx τ hv) ↔
      ∃ name ∈ opsOfType octx τ, e = .op () ⟨name, ()⟩ (some τ) := by
  simp only [mem_support_pure_iff, pickOp, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv), List.mem_map]
  constructor
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩

/-- Any op node produced by `pickOp` on `factoryOps F` is `Lambda.OpsConsistentR`. -/
theorem pickOp_mem_opsConsistentR (F : @Factory LExprParams') (τ : LMonoTy)
    {hv : (opsOfType (factoryOps F) τ).length > 0} {e : LExpr'}
    (he : e ∈ SPMF.support (pickOp (G := SPMF) (factoryOps F) τ hv)) :
    Lambda.OpsConsistentR F e := by
  rw [mem_support_pickOp_iff'] at he
  obtain ⟨name, hmem, rfl⟩ := he
  exact pickOp_opsConsistentR F τ name hmem


/-- Any node produced by `pickBVar` is a `.bvar`, hence `Lambda.OpsConsistentR`. -/
theorem pickBVar_mem_opsConsistentR (F : @Factory LExprParams') (bctx : BVarCtx) (τ : LMonoTy)
    {hv : (bvarsOfType bctx τ).length > 0} {e : LExpr'}
    (he : e ∈ SPMF.support (pickBVar (G := SPMF) bctx τ hv)) :
    Lambda.OpsConsistentR F e := by
  change e ∈ SPMF.support (pickBVar (G := SPMF) bctx τ hv) at he
  simp only [mem_support_pure_iff, pickBVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv),
    List.mem_map] at he
  obtain ⟨i, _, rfl⟩ := he
  exact .bvar

/-- Any node produced by `pickFVar` is a `.fvar`, hence `Lambda.OpsConsistentR`. -/
theorem pickFVar_mem_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (τ : LMonoTy)
    {hv : (fvarsOfType fctx τ).length > 0} {e : LExpr'}
    (he : e ∈ SPMF.support (pickFVar (G := SPMF) fctx τ hv)) :
    Lambda.OpsConsistentR F e := by
  change e ∈ SPMF.support (pickFVar (G := SPMF) fctx τ hv) at he
  simp only [mem_support_pure_iff, pickFVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv),
    List.mem_map] at he
  obtain ⟨name, _, rfl⟩ := he
  exact .fvar

private theorem norm_bool' : LMonoTy.bool = LMonoTy.tcons "bool" [] := rfl
private theorem norm_int' : LMonoTy.int = LMonoTy.tcons "int" [] := rfl
private theorem norm_string' : LMonoTy.string = LMonoTy.tcons "string" [] := rfl
private theorem norm_real' : LMonoTy.real = LMonoTy.tcons "real" [] := rfl
private theorem norm_arrow' (τ₁ τ₂ : LMonoTy) :
    LMonoTy.arrow τ₁ τ₂ = LMonoTy.tcons "arrow" [τ₁, τ₂] := rfl

-- ── The support for the two Indir rules ──────────────────────────────
--
-- The two Indir rules are inside `genLExprBase`, so `genLExprBase_opsConsistentR` uses each definition
-- below, and each of them must therefore come before that theorem.

-- ── mkApps and mapM-argument consistency ─────────────────────────────

/-- `mkApps` of a base and of arguments that each satisfy `OpsConsistentR` also satisfies
    `OpsConsistentR`. The proof uses the `.app` constructor. -/
theorem mkApps_opsConsistentR (F : @Factory LExprParams') (base : LExpr') (args : List LExpr')
    (hbase : Lambda.OpsConsistentR F base)
    (hargs : ∀ a ∈ args, Lambda.OpsConsistentR F a) :
    Lambda.OpsConsistentR F (mkApps base args) := by
  induction args generalizing base with
  | nil => simpa [mkApps] using hbase
  | cons a rest ih =>
    simp only [mkApps, List.foldl_cons]
    apply ih
    · exact Lambda.OpsConsistentR.app hbase (hargs a (by simp))
    · intro x hx; exact hargs x (by simp [hx])

/-- Op-consistency through a `mapM`, for an arbitrary argument generator. If each term that `genArg σ` can
    give satisfies `OpsConsistentR`, then each element of a list that the `mapM` gives also satisfies it. The
    statement holds for an arbitrary generator, because `genLExpr` uses `genLExprBase` in the argument
    position at the depth floor, and it uses *itself* above the floor. -/
theorem mapM_genArg_opsConsistentR (F : @Factory LExprParams')
    (genArg : LMonoTy → SPMF LExpr')
    (hArg : ∀ σ a, a ∈ SPMF.support (genArg σ) → Lambda.OpsConsistentR F a)
    (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ SPMF.support (List.mapM (m := SPMF) genArg argTys)) :
    ∀ a ∈ args, Lambda.OpsConsistentR F a :=
  StrataGenerators.IndirSupport.mapM_forall genArg hArg argTys args hargs


-- ── Monomorphic Indir op-node consistency ────────────────────────────

/-- The public form of membership in `findOpsInCtx`. An entry of that list corresponds to an entry of the
    operator context, at the curried type that the argument types and the target type build. -/
theorem findOpsInCtx_mem' {octx : OpCtx} {τ : LMonoTy}
    {name : String} {argTys : List LMonoTy}
    (h : (name, argTys) ∈ findOpsInCtx octx τ) :
    (name, argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) ∈ octx.ops ∧ argTys ≠ [] := by
  simp only [findOpsInCtx, List.mem_filterMap] at h
  obtain ⟨⟨n, ty⟩, hmem, hfilt⟩ := h
  simp only at hfilt
  split at hfilt
  · rename_i arg args hargs
    simp only [Option.some.injEq, Prod.mk.injEq] at hfilt
    obtain ⟨rfl, rfl⟩ := hfilt
    refine ⟨?_, List.cons_ne_nil _ _⟩
    have heq := argsForResult_eq ty τ (arg :: args) hargs
    rw [heq] at hmem
    exact hmem
  · simp at hfilt

/-- The `.op` node of the monomorphic Indir rule satisfies `Lambda.OpsConsistentR`. Its annotation is the
    curried type that `findOpsInCtx (factoryOps F) τ` gives, which equals the generic type of the operator.
    Therefore it is the instance under the identity substitution that `OpsConsistentR.op_in` needs. -/
theorem indir_op_opsConsistentR (F : @Factory LExprParams') (τ : LMonoTy)
    (name : String) (argTys : List LMonoTy)    (hmem : (name, argTys) ∈ findOpsInCtx (factoryOps F) τ) :
    Lambda.OpsConsistentR F
      (.op () ⟨name, ()⟩ (some (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) := by
  obtain ⟨hoctx, _⟩ := findOpsInCtx_mem' hmem
  obtain ⟨fn, hget, hty⟩ := factoryOps_mem_char F name _ hoctx
  exact .op_in (tySubst := []) hget (by rw [hty]; exact (LMonoTy.subst_of_hasEmptyScopes (by simp) _).symm)

-- ── Polymorphic IndirPoly op-node consistency ────────────────────────

/-- The condition that each annotation of a polymorphic operator which `genIndirPoly` can emit at the target
    type `τ` satisfies `OpsConsistentR`. For each candidate of
    `findPolymorphicOps pctx τ generableTys sampledTys`, the `.op` node with the annotation
    `concreteArgTys.foldr arrow τ` is consistent.

    **This predicate has a proof.** `PolyOpsConsistentR_of_PCtxWF` derives it from `PCtxWF F pctx`, which is a
    condition about the well-formedness of a factory and which holds for each real factory. The general
    theorems below take it as an explicit hypothesis, so that they stay as general as possible. The top-level
    result that needs no hypothesis is `genLExpr_opsConsistentR_of_PCtxWF`.

    Against the *declarative* `OpsConsistentR`, the proof is direct, and it needs no machinery for a match
    over a ground type. The generator builds its annotation as `subst fullSubst (subst renameSubst genericTy)`,
    which is a true substitution *instance* of the generic type of the operator, and that is exactly the
    witness that `OpsConsistentR.op_in` asks for. Read `findPolymorphicOps_instanceR`. The guard in
    `findPolymorphicOps` asks that the substitution sends the result type to `τ`, so the instance targets `τ`.
    That guard also permits an annotation that names a free type variable, which no binder quantifies.

    The predicate holds with no content when `pctx` is empty. Read the results whose name ends in `_nil`,
    which need no such hypothesis. -/
def PolyOpsConsistentR (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (bctx : BVarCtx) (fctx : FVarCtx) (τ : LMonoTy) (maxNumArgs : Nat := 3) : Prop :=
  ∀ (sampledTys : List LMonoTy) (name : String) (concreteArgTys : List LMonoTy),
    (name, concreteArgTys) ∈
      findPolymorphicOps pctx τ (generableTypesFromCtx bctx fctx (factoryOps F))
        sampledTys maxNumArgs →
    Lambda.OpsConsistentR F
      (.op () ⟨name, ()⟩ (some (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)))

/-- `decomposeArrow` inverts the fold that builds an arrow type that nests to the right. -/
theorem decomposeArrow_foldr (t : LMonoTy) :
    t = (decomposeArrow t).1.foldr (fun σ acc => LMonoTy.arrow σ acc) (decomposeArrow t).2 := by
  fun_induction decomposeArrow t with
  | case1 σ rest args ret hrec ih =>
    simp only [hrec, List.foldr_cons]
    show LMonoTy.arrow σ rest = LMonoTy.arrow σ _
    congr 1
    rw [hrec] at ih; simpa using ih
  | case2 ty hne => rfl

/-- `LMonoTys.subst` is the `map` of `LMonoTy.subst` over the list. This is a public form of a lemma of
    Strata, whose own version is in a `module` file. -/
theorem LMonoTys_subst_map (S : Lambda.Subst) (args : List LMonoTy) :
    LMonoTys.subst S args = args.map (LMonoTy.subst S) := by
  have h := LMonoTy.subst_unfold S (LMonoTy.tcons "x" args)
  rw [LMonoTy.subst_tcons] at h
  simp only at h
  injection h with _ hh

/-- A substitution distributes over the fold that builds an arrow type that nests to the right.
    `LMonoTys_subst_map` handles the case of a substitution with empty scopes, so this proof needs no split on
    that case. -/
theorem subst_foldr_arrow (S : Lambda.Subst) (l : List LMonoTy) (t : LMonoTy) :
    LMonoTy.subst S (l.foldr (fun σ acc => LMonoTy.arrow σ acc) t)
      = (l.map (LMonoTy.subst S)).foldr (fun σ acc => LMonoTy.arrow σ acc)
          (LMonoTy.subst S t) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [LMonoTy.arrow, LMonoTy.subst_tcons, LMonoTys_subst_map]
    simp only [List.map_cons, List.map_nil]
    rw [ih]
    rfl

/-- The association list sending each free variable `v` of `P` to its image under the
    composite `subst T2 ∘ subst T1`. -/
def composeWitnessBindings (P : LMonoTy) (T1 T2 : Lambda.Subst) :
    List (TyIdentifier × LMonoTy) :=
  (LMonoTy.freeVars P).map (fun v => (v, LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))))

/-- The substitution of one scope that sends each free variable of `P` to its image under the composition of
    the two substitutions. Applied to `P`, or to any type each of whose free variables is free in `P`, it
    gives the same result as that composition. The existence witness of `OpsConsistentR` needs only that
    much, and it needs no ground type and no well-formedness condition.

    A scope of a `Subst` is a hash map, so `substScope` builds the scope from `composeWitnessBindings`, and no
    code writes it as a list. -/
def composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst) : Lambda.Subst :=
  substScope (composeWitnessBindings P T1 T2)

/-- Looking up a free variable `v` of `P` in `composeWitnessScope P T1 T2` returns
    its composite image. -/
theorem find?_composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst)
    (v : TyIdentifier) (hv : v ∈ LMonoTy.freeVars P) :
    Strata.Util.HMaps.find? (composeWitnessScope P T1 T2) v
      = some (LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))) := by
  rw [composeWitnessScope, Freshening.find?_substScope_eq_lookup, composeWitnessBindings]
  -- A `List.lookup` over the list `l.map (fun v => (v, g v))`, at a key of `l`, gives the image of that key
  -- under `g`.
  have key : ∀ (l : List TyIdentifier), v ∈ l →
      (l.map (fun v => (v, LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))))).lookup v
        = some (LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))) := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons w ws ih =>
      simp only [List.map_cons, List.lookup_cons]
      by_cases hvw : v = w
      · subst hvw; simp
      · simp only [show (v == w) = false from by simp [hvw]]
        rw [List.mem_cons] at hl
        rcases hl with h | h
        · exact absurd h hvw
        · exact ih h
  exact key (LMonoTy.freeVars P) hv

/-- **One scope in place of a composition.** When each free variable of `mty` is a free variable of `P`, the
    single scope `composeWitnessScope P T1 T2` applied to `mty` gives the same result as the composition of
    the two substitutions.

    `LMonoTy.subst_unfold` handles the case of a substitution with empty scopes, so the proof is a plain
    structural induction, with no split on whether the scope of the witness is empty. -/
theorem subst_composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst) :
    ∀ (mty : LMonoTy), (∀ v, v ∈ LMonoTy.freeVars mty → v ∈ LMonoTy.freeVars P) →
      LMonoTy.subst (composeWitnessScope P T1 T2) mty
        = LMonoTy.subst T2 (LMonoTy.subst T1 mty) := by
  intro mty
  induction mty with
  | ftvar v =>
    intro hsub
    have hv := hsub v (by simp [LMonoTy.freeVars])
    rw [LMonoTy.subst_unfold]
    simp only [find?_composeWitnessScope P T1 T2 v hv]
  | bitvec n => intro _; simp [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    intro hsub
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    congr 1
    rw [LMonoTys_subst_map, LMonoTys_subst_map, LMonoTys_subst_map, List.map_map]
    apply List.map_congr_left
    intro a ha
    exact ih a ha (fun v hv => hsub v (by
      simp only [LMonoTy.freeVars]; exact Freshening.freeVars_mem_of_mem ha hv))

/-- **One substitution in place of a composition.** When `A` equals `subst T2 (subst T1 P)`, there is a
    substitution `S` with `A = subst S P`. The witness is the single scope `composeWitnessScope P T1 T2`. This
    lemma needs no well-formedness condition on a substitution and no ground type, because
    `OpsConsistentR.op_in` accepts each `Subst`. -/
theorem composite_instance_subst (A P : LMonoTy) (T1 T2 : Lambda.Subst)
    (hA : A = LMonoTy.subst T2 (LMonoTy.subst T1 P)) :
    ∃ S : Lambda.Subst, A = LMonoTy.subst S P := by
  refine ⟨composeWitnessScope P T1 T2, ?_⟩
  rw [hA]
  exact (subst_composeWitnessScope P T1 T2 P (fun v hv => hv)).symm

/-- The body after the rename is a substitution applied to the original body. -/
theorem freshenBoundVars_snd_eq_subst (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (contextVars : List TyIdentifier) :
    ∃ R : Lambda.Subst, (freshenBoundVars boundVars monoTy contextVars).2
      = LMonoTy.subst R monoTy := by
  unfold freshenBoundVars
  exact ⟨_, rfl⟩

/-- **The witness that an annotation is an instance of a scheme.** Take a candidate of
    `findPolymorphicOps`, and the factory function `fn` of that name. Its annotation
    `A = concreteArgTys.foldr arrow τ` is a substitution *instance* of the generic type of `fn`, so there is a
    substitution `S` with `A = subst S genericTy`. That is exactly the witness that `OpsConsistentR.op_in`
    needs.

    This lemma needs **no** ground type and no result about the completeness of unification. The guard of
    `findPolymorphicOps` gives the equation about the orientation directly, so no argument about the soundness
    of unification is necessary. `composite_instance_subst` builds the witness from the renaming and the
    substitution of the generator, and it needs no well-formedness condition on a substitution. An annotation
    that names a free type variable needs no separate case. -/
theorem findPolymorphicOps_instanceR (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (τ : LMonoTy) (generableTys sampledTys : List LMonoTy) (maxNumArgs : Nat)
    (hPctx : PCtxWF F pctx)
    (name : String) (concreteArgTys : List LMonoTy)
    (hEntry : (name, concreteArgTys) ∈
      findPolymorphicOps pctx τ generableTys sampledTys maxNumArgs) :
    ∃ (fn : LFunc LExprParams') (S : Lambda.Subst),
      F[name]? = some fn ∧
      concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
        = LMonoTy.subst S (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)) := by
  -- Step 1. Unfold the membership in `findPolymorphicOps` down to the branch that succeeds.
  -- `findPolymorphicOps` is a `flatMap` over `pctx`, because one scheme can give a candidate at several split
  -- points. Its body for one scheme gives the empty list when the arity is too large, and otherwise a
  -- `filterMap` over each split point. Therefore the membership gives a scheme of `pctx`, the fact that the
  -- guard on the arity held, and a split point whose `do` block over `Option` gave the candidate.
  unfold findPolymorphicOps at hEntry
  simp only [List.mem_flatMap] at hEntry
  obtain ⟨⟨nm, boundVars, monoTy⟩, hmem, hfilt⟩ := hEntry
  -- Name the result of the rename and its arrow decomposition, so that each `let` reduces.
  obtain ⟨freshBoundVars, freshMonoTy, hfreshEq⟩ :
      ∃ a b, freshenBoundVars boundVars monoTy
        (τ.freeVars ++ List.flatMap LMonoTy.freeVars generableTys).eraseDups = (a, b) :=
    ⟨_, _, rfl⟩
  obtain ⟨argTys, retTy, hdecEq⟩ :
      ∃ a b, decomposeArrow freshMonoTy = (a, b) := ⟨_, _, rfl⟩
  simp only [hfreshEq, hdecEq] at hfilt
  -- The `if` on the arity took the `else` branch, because membership in the empty list is false.
  split at hfilt
  · exact absurd hfilt (List.not_mem_nil)
  -- The hypothesis `hfilt` is at this point the membership in the `filterMap` over the split points. Extract the split
  -- point and the equation of its `do` block over `Option`. That block holds two guards: one for a type
  -- variable that stays open, and then the guard about the instance.
  rw [List.mem_filterMap] at hfilt
  obtain ⟨k, _, hopt⟩ := hfilt
  simp only [guard, bind, failure, pure, Option.pure_def, Option.bind_eq_some_iff,
    Option.ite_some_none_eq_some, Option.some.injEq, Prod.mk.injEq] at hopt
  obtain ⟨subst, hunif, _, ⟨hguard1, _⟩, _, ⟨hguard2, _⟩, hname, hcat⟩ := hopt
  subst hname
  -- Step 2. `PCtxWF` gives the factory function and the shape of its type.
  obtain ⟨fn, hget, hlty⟩ := hPctx nm (.forAll boundVars monoTy) hmem
  -- The injectivity of `.forAll` gives the binders and the body of the scheme.
  rw [LTy.forAll.injEq] at hlty
  obtain ⟨hba, hmono⟩ := hlty
  have hgenericEq : monoTy = LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd) := hmono
  -- Step 3. The guard about the instance *is* the equation `subst fullSubst leftoverSuffix = τ`. Here
  -- `leftoverSuffix` is the part of the arrow type of the scheme that the term does not apply.
  have hunifEqFull : LMonoTy.subst
      (substScope ((findFreeTyVars freshBoundVars subst).zip sampledTys) ++ subst)
      ((argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ :=
    beq_iff_eq.mp hguard2
  -- Step 4. Build the witness for the substitution.
  -- First, the body after the rename is the renaming applied to the original body.
  obtain ⟨renameSubst, hfmt⟩ : ∃ R, freshMonoTy = LMonoTy.subst R monoTy := by
    obtain ⟨R, hR⟩ := freshenBoundVars_snd_eq_subst boundVars monoTy
      (τ.freeVars ++ List.flatMap LMonoTy.freeVars generableTys).eraseDups
    rw [hfreshEq] at hR; exact ⟨R, hR⟩
  -- Second, `A` equals `subst fullSubst (subst renameSubst genericTy)`. The one difference from the case of a
  -- full application is a split of the arrow type of the scheme at the split point, into the applied prefix
  -- and the remaining suffix.
  have hAeq : concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
      = LMonoTy.subst (substScope ((findFreeTyVars freshBoundVars subst).zip sampledTys) ++ subst)
          (LMonoTy.subst renameSubst
            (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))) := by
    rw [← hgenericEq, ← hfmt]
    -- freshMonoTy = argTys.foldr arrow retTy
    have hfreshFold : freshMonoTy
        = argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) retTy := by
      have := decomposeArrow_foldr freshMonoTy
      rw [hdecEq] at this; simpa using this
    -- Split the scheme's arrow type at `k`: the applied prefix, then the suffix.
    have hsplit : argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) retTy
        = (argTys.take k).foldr (fun σ acc => LMonoTy.arrow σ acc)
            ((argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) := by
      rw [← List.foldr_append, List.take_append_drop]
    rw [hfreshFold, hsplit, subst_foldr_arrow, hunifEqFull, ← hcat]
  -- Build one substitution as the witness. This step needs no ground type and no well-formedness condition.
  obtain ⟨S, hS⟩ := composite_instance_subst
    (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
    (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))
    renameSubst (substScope ((findFreeTyVars freshBoundVars subst).zip sampledTys) ++ subst)
    hAeq
  exact ⟨fn, S, hget, hS⟩

/-- `PCtxWF` gives the condition `PolyOpsConsistentR`, because each emitted annotation is a substitution
    instance of the generic type of the operator, which `findPolymorphicOps_instanceR` proves. That instance
    is exactly the witness that `OpsConsistentR.op_in` needs. The proof splits on no type argument, and it
    needs no ground type. -/
theorem PolyOpsConsistentR_of_PCtxWF (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (bctx : BVarCtx) (fctx : FVarCtx) (τ : LMonoTy) (maxNumArgs : Nat)
    (hPctx : PCtxWF F pctx) :
    PolyOpsConsistentR F pctx bctx fctx τ maxNumArgs := by
  intro sampledTys name concreteArgTys hEntry
  obtain ⟨fn, S, hget, hinst⟩ :=
    findPolymorphicOps_instanceR F pctx τ _ sampledTys maxNumArgs hPctx name concreteArgTys hEntry
  exact Lambda.OpsConsistentR.op_in hget hinst

-- ── Indir/IndirPoly op-consistency, parametric in the argument generator ──

open StrataGenerators.IndirSupport in
/-- Each term of the monomorphic Indir rule satisfies `OpsConsistentR`. The annotation of the `.op` node is
    the generic type of the operator, and each argument comes from `genArg`.

    The statement holds for an arbitrary `genArg`, for the same reason as each other result in
    `IndirSupport`: `genLExprBase` gives its own recursive call at the smaller depth index. -/
theorem genIndir_opsConsistentR (F : @Factory LExprParams') (τ : LMonoTy)
    (genArg : LMonoTy → SPMF LExpr')
    (hArg : ∀ σ a, a ∈ SPMF.support (genArg σ) → Lambda.OpsConsistentR F a)
    (h : (findOpsInCtx (factoryOps F) τ).length > 0) (e : LExpr')
    (he : e ∈ SPMF.support (genIndir (G := SPMF) (factoryOps F) τ genArg h)) :
    Lambda.OpsConsistentR F e := by
  obtain ⟨nm, argTys, args, hmem, hargs, rfl⟩ :=
    genIndir_shape (factoryOps F) τ genArg h e he
  exact mkApps_opsConsistentR F _ args (indir_op_opsConsistentR F τ nm argTys hmem)
    (mapM_forall genArg hArg argTys args ((mem_support_mapM_iff genArg argTys args).mpr hargs))

open StrataGenerators.IndirSupport in
/-- Each term of the polymorphic IndirPoly rule satisfies `OpsConsistentR`, under the condition
    `PolyOpsConsistentR`, which `PolyOpsConsistentR_of_PCtxWF` proves from `PCtxWF`, and under the condition
    that each term of the fallback satisfies `OpsConsistentR`. -/
theorem genIndirPolyCore_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (bctx : BVarCtx) (τ : LMonoTy) (maxNumArgs : Nat)
    (hPoly : PolyOpsConsistentR F pctx bctx fctx τ maxNumArgs)
    (genArg : LMonoTy → SPMF LExpr') (fallback : SPMF LExpr')
    (hArg : ∀ σ a, a ∈ SPMF.support (genArg σ) → Lambda.OpsConsistentR F a)
    (hFallback : ∀ a, a ∈ SPMF.support fallback → Lambda.OpsConsistentR F a)
    (e : LExpr')
    (he : e ∈ SPMF.support (genIndirPolyCore (G := SPMF) fctx (factoryOps F) pctx
      bctx τ genArg fallback maxNumArgs)) :
    Lambda.OpsConsistentR F e := by
  rcases genIndirPolyCore_shape fctx (factoryOps F) pctx bctx τ genArg fallback maxNumArgs e he with
    ⟨sampled, nm, concreteArgTys, args, hmem, hargs, rfl⟩ | hfb
  · exact mkApps_opsConsistentR F _ args (hPoly sampled nm concreteArgTys hmem)
      (mapM_forall genArg hArg concreteArgTys args
        ((mem_support_mapM_iff genArg concreteArgTys args).mpr hargs))
  · exact hFallback e hfb

/-- `genLExprBase_opsConsistentR` as a law, by induction on the depth. `split` exposes one arm of
    `genLExprBase` per goal, and `omega` refutes the arms of the other depth. `walk` then leaves one goal
    per path: a leaf closes by its constructor of `OpsConsistentR`, and a compound node by its constructor
    over the facts for its children. The leaves come from `pick*_mem_opsConsistentR`, the two Indir rules
    from `genIndir_opsConsistentR` and `genIndirPolyCore_opsConsistentR` over the induction hypothesis. -/
private theorem genLExprBase_opsConsistentR_aux (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m) :
    ∀ depth bctx τ, IsSoundFor (genLExprBase (G := SPMF) fctx (factoryOps F) pctx tvars bctx depth τ)
      (Lambda.OpsConsistentR F) := by
  have hB : ∀ bctx τ hv, IsSoundFor (pickBVar (G := SPMF) bctx τ hv) (Lambda.OpsConsistentR F) :=
    fun bctx τ _ _ he => pickBVar_mem_opsConsistentR F bctx τ he
  have hF : ∀ τ hv, IsSoundFor (pickFVar (G := SPMF) fctx τ hv) (Lambda.OpsConsistentR F) :=
    fun τ _ _ he => pickFVar_mem_opsConsistentR F fctx τ he
  have hO : ∀ τ hv, IsSoundFor (pickOp (G := SPMF) (factoryOps F) τ hv) (Lambda.OpsConsistentR F) :=
    fun τ _ _ he => pickOp_mem_opsConsistentR F τ he
  intro depth
  induction depth with
  | zero =>
    intro bctx τ
    rw [IsSoundFor.iff_obs, genLExprBase.eq_def]
    split
    all_goals first
      | (exfalso; omega)
      | (dsimp only
         walk_prims [(hB bctx _ _).obs, (hF _ _).obs, (hO _ _).obs])
    all_goals first
      | assumption
      | (simp only [LExpr.boolConst, LExpr.intConst, LExpr.strConst, LExpr.rationalConst,
          LExpr.bitvecConst]; exact .const)
  | succ n ih =>
    intro bctx τ
    have hI : ∀ σ h, IsSoundFor (genIndir (G := SPMF) (factoryOps F) σ
        (genLExprBase (G := SPMF) fctx (factoryOps F) pctx tvars bctx n) h) (Lambda.OpsConsistentR F) :=
      fun σ h e he => genIndir_opsConsistentR F σ _ (fun σ a ha => ih bctx σ a ha) h e he
    have hP : ∀ σ, IsSoundFor (genIndirPolyCore (G := SPMF) fctx (factoryOps F) pctx bctx σ
        (genLExprBase (G := SPMF) fctx (factoryOps F) pctx tvars bctx n)
        (genLExprBase (G := SPMF) fctx (factoryOps F) pctx tvars bctx n σ) 3)
        (Lambda.OpsConsistentR F) :=
      fun σ e he => genIndirPolyCore_opsConsistentR F fctx pctx bctx σ 3 (hPoly bctx σ 3) _ _
        (fun σ a ha => ih bctx σ a ha) (fun a ha => ih bctx σ a ha) e he
    rw [IsSoundFor.iff_obs, genLExprBase.eq_def]
    split
    all_goals first
      | (exfalso; omega)
      | (obtain rfl := Nat.succ.inj ‹_ = Nat.succ _›
         dsimp only
         walk_prims [(hB bctx _ _).obs, (hF _ _).obs, (hO _ _).obs,
          (ih _ _).obs, (hI _ _).obs, (hP _).obs,
          fun τ => (true_law (genAppArgTy (G := SPMF) fctx (factoryOps F) tvars bctx n τ)).obs,
          (true_law (genGenerableTy (G := SPMF) fctx (factoryOps F) tvars bctx n)).obs])
    all_goals first
      | assumption
      | (simp only [LExpr.boolConst, LExpr.intConst, LExpr.strConst, LExpr.rationalConst,
          LExpr.bitvecConst]; exact .const)
      | (constructor <;> assumption)

theorem genLExprBase_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    -- The IndirPoly rule is inside `genLExprBase`, so this theorem needs the same condition about a
    -- polymorphic annotation as `genLExpr_opsConsistentR`. The condition quantifies over each binder context
    -- and each target type, because the rule acts at each position of a subterm and not at the root only.
    -- `PolyOpsConsistentR_of_PCtxWF` gives it at each type from one `PCtxWF`, so each corollary below needs no
    -- change.
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SPMF.support (genLExprBase (G := SPMF) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e :=
  genLExprBase_opsConsistentR_aux F fctx pctx tvars hPoly depth bctx τ e he

/-- Each argument that `mapM (genLExprBase fctx (factoryOps F) …)` gives satisfies
    `Lambda.OpsConsistentR`. This is a special case of `mapM_genArg_opsConsistentR`. -/
theorem mapM_genLExprBase_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m)
    (bctx : BVarCtx) (depth : Nat) (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ SPMF.support (List.mapM (m := SPMF)
      (genLExprBase fctx (factoryOps F) pctx tvars bctx depth) argTys)) :
    ∀ a ∈ args, Lambda.OpsConsistentR F a :=
  mapM_genArg_opsConsistentR F _
    (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx depth σ a ha) argTys args hargs


-- ── genIndirPoly consistency ─────────────────────────────────────────

set_option maxHeartbeats 800000 in
/-- Each expression in the support of `genIndirPoly` satisfies `OpsConsistentR`, under the condition
    `PolyOpsConsistentR`, which `PolyOpsConsistentR_of_PCtxWF` proves from `PCtxWF`. Either the generator
    applied a polymorphic operator, and the condition gives the `.op` node while
    `mapM_genLExprBase_opsConsistentR` gives each argument, or the generator used the fallback
    `genLExprBase`. -/
theorem genIndirPoly_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat)
    -- The condition quantifies over each context and each type. `genLExprBase` acts with the IndirPoly rule
    -- at each position of a subterm, so the fallback needs the condition at those types too, and not at `τ`
    -- only. `PolyOpsConsistentR_of_PCtxWF` gives each of them from one `PCtxWF`.
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m)
    (genArg : LMonoTy → SPMF LExpr')
    (hArg : ∀ σ a, a ∈ SPMF.support (genArg σ) → Lambda.OpsConsistentR F a)
    (e : LExpr')
    (he : e ∈ SPMF.support
      (genIndirPoly (G := SPMF) fctx (factoryOps F) pctx tvars bctx depth τ
        maxNumArgs genArg)) :
    Lambda.OpsConsistentR F e := by
  -- `genIndirPoly` is a wrapper around `genIndirPolyCore`, so the result for an arbitrary argument generator
  -- applies. The hypothesis `hArg` gives the consistency of `genArg`, and the fallback is `genLExprBase` at
  -- the same depth.
  exact genIndirPolyCore_opsConsistentR F fctx pctx bctx τ maxNumArgs (hPoly bctx τ maxNumArgs)
    genArg _ hArg
    (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx depth τ a ha) e he

-- ── Top-level: genLExpr consistency ──────────────────────────────────

set_option maxHeartbeats 800000 in
/-- **The main result, at a general polymorphic context.** Each expression in the support of `genLExpr`, over
    the operator context `factoryOps F` of a factory, satisfies the declarative `OpsConsistentR F` of Strata.
    Together with the soundness of `genLExpr`, this theorem gives soundness against `HasTypeA` and against
    `OpsConsistentR`.

    The statement takes the condition `PolyOpsConsistentR` as a hypothesis, for generality.
    `PolyOpsConsistentR_of_PCtxWF` discharges it from `PCtxWF`, which gives
    `genLExpr_opsConsistentR_of_PCtxWF`, and that theorem needs no hypothesis. For an empty polymorphic
    context, use `genLExpr_opsConsistentR_nil`. -/
theorem genLExpr_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    -- The condition quantifies over *each* target type, and not over `τ` only. A factory application nests,
    -- so the generator makes each argument of an application at `τ` at another type, and each of those types
    -- needs its own condition. `PolyOpsConsistentR_of_PCtxWF` gives each of them from one `PCtxWF`, so each
    -- corollary below needs no change.
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m) (e : LExpr')
    (he : e ∈ SPMF.support
      (genLExpr (G := SPMF) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e := by
  -- The induction is on the depth index, as in the soundness proof. Each argument of an Indir rule comes from
  -- `genLExpr` at the smaller index, so the op-consistency of the argument generator at that index is the
  -- inductive hypothesis. The condition about a polymorphic annotation does not depend on the depth, so it
  -- survives the generalization unchanged.
  revert e; show IsSoundFor _ _
  have hB : ∀ d σ, IsSoundFor (genLExprBase (G := SPMF) fctx (factoryOps F) pctx tvars bctx d σ)
      (Lambda.OpsConsistentR F) := genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx
  induction depth generalizing τ with
  | zero =>
    have hI : ∀ σ h, IsSoundFor (genIndir (G := SPMF) (factoryOps F) σ
        (genLExprBase (G := SPMF) fctx (factoryOps F) pctx tvars bctx 0) h) (Lambda.OpsConsistentR F) :=
      fun σ h => genIndir_opsConsistentR F σ _ (hB 0) h
    have hP : ∀ σ, IsSoundFor (genIndirPoly (G := SPMF) fctx (factoryOps F) pctx tvars bctx 0 σ 3
        (genLExprBase (G := SPMF) fctx (factoryOps F) pctx tvars bctx 0)) (Lambda.OpsConsistentR F) :=
      fun σ => genIndirPoly_opsConsistentR F fctx pctx tvars bctx 0 σ 3 hPoly _ (hB 0)
    rw [IsSoundFor.iff_obs, genLExpr]; dsimp only [id]
    walk [(hB _ _).obs, (hI _ _).obs, (hP _).obs] <;> assumption
  | succ n ih =>
    have hI : ∀ σ h, IsSoundFor (genIndir (G := SPMF) (factoryOps F) σ
        (fun σ => genLExpr (G := SPMF) fctx (factoryOps F) pctx tvars bctx n σ) h)
        (Lambda.OpsConsistentR F) :=
      fun σ h => genIndir_opsConsistentR F σ _ ih h
    have hP : ∀ σ, IsSoundFor (genIndirPoly (G := SPMF) fctx (factoryOps F) pctx tvars bctx (n + 1) σ 3
        (fun σ => genLExpr (G := SPMF) fctx (factoryOps F) pctx tvars bctx n σ))
        (Lambda.OpsConsistentR F) :=
      fun σ => genIndirPoly_opsConsistentR F fctx pctx tvars bctx (n + 1) σ 3 hPoly _ ih
    rw [IsSoundFor.iff_obs, genLExpr]; dsimp only [id]
    walk [(hB _ _).obs, (hI _ _).obs, (hP _).obs] <;> assumption

-- `genLExpr_opsConsistentR` above proves `Lambda.OpsConsistentR F e` directly, which is the declarative
-- predicate of Strata. The proof is stated against that predicate throughout, and its constructors close it.
-- No step goes through the operational `OpsConsistent`, and no step uses a bridge between the two.

/-- The wrapper `genLExprWithFactory` over a `Factory` gives a term that satisfies `OpsConsistentR`, under the
    condition `PolyOpsConsistentR`. -/
theorem genLExprWithFactory_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (pctx : PolyOpCtx)
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m) (e : LExpr')
    (he : e ∈ SPMF.support
      (genLExprWithFactory (G := SPMF) fctx F tvars bctx depth τ pctx)) :
    Lambda.OpsConsistentR F e :=
  genLExpr_opsConsistentR F fctx pctx tvars bctx depth τ hPoly e he

/-- **The main result from `PCtxWF`, with no condition about a polymorphic annotation.** A well-formed
    polymorphic context is enough. `PCtxWF F pctx` says that each entry of `pctx` is the generic scheme of a
    factory function, and `PolyOpsConsistentR_of_PCtxWF` *derives* the other condition from it. Therefore
    `genLExpr` over a factory gives a term that satisfies `OpsConsistentR`, at *each* polymorphic context that
    matches the factory. -/
theorem genLExpr_opsConsistentR_of_PCtxWF (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hPctx : PCtxWF F pctx) (e : LExpr')
    (he : e ∈ SPMF.support
      (genLExpr (G := SPMF) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e :=
  genLExpr_opsConsistentR F fctx pctx tvars bctx depth τ
    (fun bc σ m => PolyOpsConsistentR_of_PCtxWF F pctx bc fctx σ m hPctx) e he

/-- **The main result at a polymorphic context from the factory, with no hypothesis.** When the polymorphic
    operator context comes directly from the factory, through `factoryPolyOps F`, then `PCtxWF` holds by
    construction, which `PCtxWF_factoryPolyOps` proves. Therefore `genLExpr` gives a term that satisfies
    `OpsConsistentR`, with no hypothesis, and also with a polymorphic operator. This theorem is the polymorphic
    form of `genLExpr_opsConsistentR_nil`: it puts no limit on the polymorphic context, and a caller
    discharges no side condition. -/
theorem genLExpr_opsConsistentR_factory (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SPMF.support
      (genLExpr (G := SPMF) fctx (factoryOps F) (factoryPolyOps F) tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e :=
  genLExpr_opsConsistentR_of_PCtxWF F fctx (factoryPolyOps F) tvars bctx depth τ
    (PCtxWF_factoryPolyOps F) e he

/-- The wrapper `genLExprWithFactory` over a `Factory`, at the polymorphic context `factoryPolyOps F` of that
    factory, gives a term that satisfies `OpsConsistentR`, with no hypothesis. -/
theorem genLExprWithFactory_opsConsistentR_factory (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SPMF.support
      (genLExprWithFactory (G := SPMF) fctx F tvars bctx depth τ (factoryPolyOps F))) :
    Lambda.OpsConsistentR F e :=
  genLExpr_opsConsistentR_factory F fctx tvars bctx depth τ e he

-- ── The corollary for an empty polymorphic context ───────────────────
--
-- The default value of the polymorphic context in each wrapper over a factory is `factoryPolyOps F`, and
-- `genLExpr_opsConsistentR_factory` covers that case with no hypothesis. The results below apply to a caller
-- that gives an empty polymorphic context. `findPolymorphicOps` gives the empty list for such a context, so
-- `genIndirPoly` emits no polymorphic operator, and the obligation about a polymorphic annotation has no
-- content. Therefore each result below needs no `PCtxWF`.

@[simp] theorem findPolymorphicOps_nil (τ : LMonoTy) (g s : List LMonoTy) (m : Nat) :
    findPolymorphicOps [] τ g s m = [] := by unfold findPolymorphicOps; rfl

/-- At an empty polymorphic context, `genIndirPoly` always uses the fallback `genLExprBase`. Therefore each of
    its terms satisfies `OpsConsistentR`. -/
theorem genIndirPoly_opsConsistentR_nil (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat) (genArg : LMonoTy → SPMF LExpr')
    -- This hypothesis is necessary, because each *argument* of `genIndirPolyCore` also comes from `genArg`. At
    -- an empty polymorphic context only the fallback acts, and the lemma states one claim over both branches.
    (hArg : ∀ σ a, a ∈ SPMF.support (genArg σ) → Lambda.OpsConsistentR F a)
    (e : LExpr')
    (he : e ∈ SPMF.support
      (genIndirPoly (G := SPMF) fctx (factoryOps F) [] tvars bctx depth τ
        maxNumArgs genArg)) :
    Lambda.OpsConsistentR F e := by
  -- At an empty polymorphic context, the condition about a polymorphic annotation has no content, because
  -- `findPolymorphicOps` gives the empty list. Therefore no proof can give a membership in the candidates, and
  -- only the fallback branch of `genIndirPolyCore` is reachable.
  exact genIndirPolyCore_opsConsistentR F fctx [] bctx τ maxNumArgs
    (fun _ _ _ hmem => by rw [findPolymorphicOps_nil] at hmem; simp at hmem)
    genArg _ hArg
    (fun a ha => genLExprBase_opsConsistentR F fctx [] tvars
      (fun _ _ _ _ _ _ hmem => by
        rw [findPolymorphicOps_nil] at hmem; simp at hmem)
      bctx depth τ a ha) e he

set_option maxHeartbeats 800000 in
/-- **The main result at an empty polymorphic context.** Each expression that `genLExpr` gives at an empty
    polymorphic context, over the operator context of a factory, satisfies `OpsConsistentR F`. This result
    covers each generator of a closed term. -/
theorem genLExpr_opsConsistentR_nil (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (e : LExpr')
    (he : e ∈ SPMF.support
      (genLExpr (G := SPMF) fctx (factoryOps F) [] tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e :=
  -- At an empty polymorphic context, the condition about a polymorphic annotation has no content. The context
  -- holds no entry, so `findPolymorphicOps` gives the empty list, and no proof can give a membership in the
  -- candidates. This proof therefore applies the general theorem, and it repeats no induction on the depth.
  genLExpr_opsConsistentR F fctx [] tvars bctx depth τ
    (fun _ _ _ _ _ _ hmem => by
      rw [findPolymorphicOps_nil] at hmem; simp at hmem)
    e he

-- ── `SchemeInstAt` from `OpsConsistentR` ─────────────────────────────
--
-- `SchemeInstAt`, in `HasTypeAGen.lean`, is the witness at the level of the specification that
-- `genLExpr_complete_poly_fullySpecShaped` needs. This section gives it from a `Lambda.OpsConsistentR F e` of
-- the caller. The `.op_in` constructor of that judgment holds exactly the missing part: the substitution
-- that sends the generic type of the operator to the annotation of the node.
--
-- `HasTypeA'` alone cannot give that witness. Its `.op` rule types an `.op` node at *each* annotation that
-- the node carries. Therefore a well-typed term can carry an annotation that is not an instance of the
-- scheme of the operator, and the generator would never emit such an annotation. `OpsConsistentR` is the
-- judgment that excludes it, so the side of completeness takes it as a premise. That is symmetric to
-- `HasTypeA'`, and on the side of soundness it is a *theorem*, which is
-- `genLExpr_opsConsistentR_factory`.
--
-- The work is a change of the variables. `OpsConsistentR` gives an instance of the *original* body of the
-- scheme. `SchemeInstAt` needs a matcher for the body *after* `freshenBoundVars` renames its binders.
-- Therefore the matcher is that substitution together with the *inverse* of the renaming. That inverse
-- exists exactly when the renaming sends no two different binders to one name, which the hypothesis
-- `hfreshNodup` gives.

/-- The renaming of the type variables that `freshenBoundVars` performs, as an association list.

    This definition copies the local `subst` binding of `freshenBoundVars`. It is separate, so that a proof can
    *name* the renaming. The two equations below hold by `rfl`, and that fact is the check that this definition
    still agrees with the generator. -/
def renamingPairs (boundVars varsAlreadyInUse : List TyIdentifier) :
    List (TyIdentifier × TyIdentifier) :=
  let conflictingTyVars := boundVars.filter (· ∈ varsAlreadyInUse)
  let allTypeVarsInUse := varsAlreadyInUse ++ conflictingTyVars
  let numFreshNames := allTypeVarsInUse.length + conflictingTyVars.length + 1
  let freshNames := (freshNameSupply numFreshNames).filter (· ∉ allTypeVarsInUse)
  conflictingTyVars.zip freshNames

/-- The renaming as a function on a type variable. It leaves each binder that does not collide with the
    context unchanged. -/
def renameTyVar (boundVars varsAlreadyInUse : List TyIdentifier) (v : TyIdentifier) :
    TyIdentifier :=
  ((renamingPairs boundVars varsAlreadyInUse).lookup v).getD v

/-- The renaming as a `Lambda.Subst`. -/
def freshenRenaming (boundVars varsAlreadyInUse : List TyIdentifier) : Lambda.Subst :=
  substScope ((renamingPairs boundVars varsAlreadyInUse).map
    (fun p => (p.1, LMonoTy.ftvar p.2)))

/-- The first component of `freshenBoundVars` is the renaming applied to each binder. -/
theorem freshenBoundVars_fst_eq (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (varsAlreadyInUse : List TyIdentifier) :
    (freshenBoundVars boundVars monoTy varsAlreadyInUse).1
      = boundVars.map (renameTyVar boundVars varsAlreadyInUse) := rfl

/-- The second component of `freshenBoundVars` is the renaming applied to the body. -/
theorem freshenBoundVars_snd_eq (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (varsAlreadyInUse : List TyIdentifier) :
    (freshenBoundVars boundVars monoTy varsAlreadyInUse).2
      = LMonoTy.subst (freshenRenaming boundVars varsAlreadyInUse) monoTy := rfl

/-- The renaming sends a variable to a variable, and never to a compound type. That fact is what makes it
    commute with `decomposeArrow`. -/
theorem subst_freshenRenaming_ftvar (boundVars varsAlreadyInUse : List TyIdentifier)
    (v : TyIdentifier) :
    LMonoTy.subst (freshenRenaming boundVars varsAlreadyInUse) (.ftvar v)
      = .ftvar (renameTyVar boundVars varsAlreadyInUse v) := by
  rw [LMonoTy.subst_unfold, freshenRenaming]
  simp only [Freshening.find?_substScope_eq_lookup, Freshening.lookup_map_snd, renameTyVar]
  rcases h : (renamingPairs boundVars varsAlreadyInUse).lookup v with _ | w <;> simp

-- ── The general lemmas about a substitution and `decomposeArrow` ─────

/-- A substitution of two steps gives the same result as one step, as soon as the two agree at each free
    variable. This lemma is the form of `agree_on_freeVars_implies_subst_eq` for a composition. -/
theorem subst_subst_of_pointwise (S₁ S₂ T : Lambda.Subst) (t : LMonoTy)
    (h : ∀ v ∈ t.freeVars,
      LMonoTy.subst S₂ (LMonoTy.subst S₁ (.ftvar v)) = LMonoTy.subst T (.ftvar v)) :
    LMonoTy.subst S₂ (LMonoTy.subst S₁ t) = LMonoTy.subst T t := by
  induction t with
  | ftvar v => exact h v (by simp [LMonoTy.freeVars])
  | bitvec n => simp [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_unfold, LMonoTy.subst_unfold, LMonoTy.subst_unfold]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact ih a ha (fun v hv => h v (by
      show v ∈ LMonoTys.freeVars args
      exact Freshening.freeVars_mem_of_mem ha hv))

/-- A substitution into a larger type keeps each variable that one of its own free variables gives. -/
theorem freeVars_subst_mono (S : Lambda.Subst) (t : LMonoTy) (v : TyIdentifier)
    (hv : v ∈ t.freeVars) :
    ∀ w ∈ (LMonoTy.subst S (.ftvar v)).freeVars, w ∈ (LMonoTy.subst S t).freeVars := by
  induction t with
  | ftvar u =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv; exact fun w hw => hw
  | bitvec n => simp only [LMonoTy.freeVars, List.not_mem_nil] at hv
  | tcons name args ih =>
    intro w hw
    obtain ⟨a, ha, hva⟩ :=
      Freshening.exists_of_freeVars_mem (show v ∈ LMonoTys.freeVars args from hv)
    rw [LMonoTy.subst_unfold]
    show w ∈ LMonoTys.freeVars (args.map (LMonoTy.subst S))
    exact Freshening.freeVars_mem_of_mem (List.mem_map_of_mem ha) (ih a ha hva w hw)

/-- Conversely, every free variable of `subst S t` is contributed by some free
    variable of `t`. -/
theorem freeVars_subst_exists (S : Lambda.Subst) (t : LMonoTy) (w : TyIdentifier)
    (hw : w ∈ (LMonoTy.subst S t).freeVars) :
    ∃ v ∈ t.freeVars, w ∈ (LMonoTy.subst S (.ftvar v)).freeVars := by
  induction t with
  | ftvar u => exact ⟨u, by simp [LMonoTy.freeVars], hw⟩
  | bitvec n => rw [LMonoTy.subst_bitvec] at hw; simp [LMonoTy.freeVars] at hw
  | tcons name args ih =>
    rw [LMonoTy.subst_unfold] at hw
    obtain ⟨b, hb, hwb⟩ :=
      Freshening.exists_of_freeVars_mem
        (show w ∈ LMonoTys.freeVars (args.map (LMonoTy.subst S)) from hw)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    obtain ⟨v, hv, hwv⟩ := ih a ha hwb
    exact ⟨v, Freshening.freeVars_mem_of_mem ha hv, hwv⟩

/-- `decomposeArrow` bottoms out on anything that is not an arrow. -/
theorem decomposeArrow_of_not_arrow (t : LMonoTy)
    (h : ∀ σ rest, t ≠ LMonoTy.tcons "arrow" [σ, rest]) : decomposeArrow t = ([], t) := by
  unfold decomposeArrow
  split
  · rename_i σ rest; exact absurd rfl (h σ rest)
  · rfl

/-- **A renaming of the variables commutes with `decomposeArrow`.** A map from a variable to a variable
    creates no arrow, because a variable never becomes one, and it destroys no arrow, because it keeps the head
    constructor. Therefore the spine of the arrows does not change. That fact is what moves a split point
    across the renaming. -/
theorem decomposeArrow_subst_of_renaming (S : Lambda.Subst)
    (hren : ∀ v, ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w) (t : LMonoTy) :
    decomposeArrow (LMonoTy.subst S t)
      = ((decomposeArrow t).1.map (LMonoTy.subst S),
         LMonoTy.subst S (decomposeArrow t).2) := by
  fun_induction decomposeArrow t with
  | case1 σ rest args ret hrec ih =>
    have harrow : LMonoTy.subst S (LMonoTy.tcons "arrow" [σ, rest])
        = LMonoTy.tcons "arrow" [LMonoTy.subst S σ, LMonoTy.subst S rest] := by
      rw [LMonoTy.subst_unfold]; simp
    rw [harrow]
    rw [show decomposeArrow (LMonoTy.tcons "arrow" [LMonoTy.subst S σ, LMonoTy.subst S rest])
        = ((LMonoTy.subst S σ) :: (decomposeArrow (LMonoTy.subst S rest)).1,
           (decomposeArrow (LMonoTy.subst S rest)).2) from by rw [decomposeArrow]]
    rw [ih, hrec]
    simp
  | case2 ty hne =>
    have hnotarrow : ∀ σ rest, LMonoTy.subst S ty ≠ LMonoTy.tcons "arrow" [σ, rest] := by
      intro σ rest heq
      cases ty with
      | ftvar v =>
        obtain ⟨w, hw⟩ := hren v
        rw [hw] at heq; simp at heq
      | bitvec n => rw [LMonoTy.subst_bitvec] at heq; simp at heq
      | tcons nm args =>
        rw [LMonoTy.subst_unfold] at heq
        simp only [LMonoTy.tcons.injEq] at heq
        obtain ⟨rfl, hargs⟩ := heq
        have hlen : args.length = 2 := by
          have := congrArg List.length hargs
          simpa using this
        match args, hlen with
        | [a, b], _ => exact absurd rfl (hne a b)
    rw [decomposeArrow_of_not_arrow (LMonoTy.subst S ty) hnotarrow]
    simp

/-- The fold that builds an arrow type is injective in *both* components, as soon as the two argument lists
    have the same length. The two base types need not be equal, and `foldr_arrow_inj_of_length_eq` needs them
    to be equal. That difference is what lets a proof split the arrow spine of a scheme at a point, match it
    against `concreteArgTys.foldr arrow τ`, and recover the argument types *and* the target type. -/
theorem foldr_arrow_inj (as bs : List LMonoTy) (A B : LMonoTy)
    (hlen : as.length = bs.length)
    (heq : as.foldr (fun σ acc => LMonoTy.arrow σ acc) A
         = bs.foldr (fun σ acc => LMonoTy.arrow σ acc) B) :
    as = bs ∧ A = B := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact ⟨rfl, heq⟩
    | cons b bs => simp at hlen
  | cons a as ih => cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.foldr_cons, LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq,
        and_true, true_and] at heq
      obtain ⟨rfl, hrest⟩ := heq
      obtain ⟨rfl, rfl⟩ := ih bs (by simpa using hlen) hrest
      exact ⟨rfl, rfl⟩

-- ── The matcher: the substitution after the inverse of the renaming ──

/-- A `lookup` through an association list whose keys come from `f`, when `f` is injective on the list of the
    keys. Without that condition, the first key that matches wins, and its value need not be the one that the
    caller wants. That case is exactly the collision that the hypothesis `hfreshNodup` of
    `schemeInstAt_of_opsConsistentR` excludes. -/
theorem lookup_map_of_nodup {β} (f : TyIdentifier → TyIdentifier) (g : TyIdentifier → β)
    (l : List TyIdentifier) (hnodup : (l.map f).Nodup) (v : TyIdentifier) (hv : v ∈ l) :
    (l.map (fun u => (f u, g u))).lookup (f v) = some (g v) := by
  induction l with
  | nil => simp at hv
  | cons w ws ih =>
    simp only [List.map_cons, List.lookup_cons]
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotmem, hnodup'⟩ := hnodup
    rcases List.mem_cons.mp hv with rfl | hvws
    · simp
    · by_cases hfv : f v = f w
      · exact absurd (hfv ▸ List.mem_map_of_mem hvws) hnotmem
      · simp only [show (f v == f w) = false from by simp [hfv]]
        exact ih hnodup' hvws

/-- **The matcher that `SchemeInstAt` needs.** It sends each *renamed* binder to the type that the
    substitution gives to the original binder. Therefore an application of it after the renaming gives the same
    result as that substitution. -/
def schemeMatcher (boundVars varsAlreadyInUse : List TyIdentifier)
    (tySubst : Lambda.Subst) : Lambda.Subst :=
  substScope (boundVars.map
    (fun v => (renameTyVar boundVars varsAlreadyInUse v, LMonoTy.subst tySubst (.ftvar v))))

theorem subst_schemeMatcher_ftvar (boundVars varsAlreadyInUse : List TyIdentifier)
    (tySubst : Lambda.Subst)
    (hnodup : (boundVars.map (renameTyVar boundVars varsAlreadyInUse)).Nodup)
    (v : TyIdentifier) (hv : v ∈ boundVars) :
    LMonoTy.subst (schemeMatcher boundVars varsAlreadyInUse tySubst)
        (LMonoTy.subst (freshenRenaming boundVars varsAlreadyInUse) (.ftvar v))
      = LMonoTy.subst tySubst (.ftvar v) := by
  have hlk : (boundVars.map (fun u => (renameTyVar boundVars varsAlreadyInUse u,
      LMonoTy.subst tySubst (LMonoTy.ftvar u)))).lookup
        (renameTyVar boundVars varsAlreadyInUse v)
      = some (LMonoTy.subst tySubst (.ftvar v)) :=
    lookup_map_of_nodup _ _ boundVars hnodup v hv
  rw [subst_freshenRenaming_ftvar, LMonoTy.subst_unfold]
  simp only [schemeMatcher, Freshening.find?_substScope_eq_lookup, hlk]

/-- **The matcher works.** At each type whose variables are binders of the scheme, the inverse of the renaming
    followed by the substitution is one substitution by `schemeMatcher`. -/
theorem subst_schemeMatcher (boundVars varsAlreadyInUse : List TyIdentifier)
    (tySubst : Lambda.Subst)
    (hnodup : (boundVars.map (renameTyVar boundVars varsAlreadyInUse)).Nodup)
    (t : LMonoTy) (hclosed : ∀ v ∈ t.freeVars, v ∈ boundVars) :
    LMonoTy.subst (schemeMatcher boundVars varsAlreadyInUse tySubst)
        (LMonoTy.subst (freshenRenaming boundVars varsAlreadyInUse) t)
      = LMonoTy.subst tySubst t :=
  subst_subst_of_pointwise _ _ _ t
    (fun v hv => subst_schemeMatcher_ftvar boundVars varsAlreadyInUse tySubst hnodup v
      (hclosed v hv))

/-- The split of an arrow type that nests to the right, at a point `k`. The result is the first `k` argument
    types and the remaining suffix. That point is the split point that `findPolymorphicOps` ranges over. -/
theorem foldr_arrow_split (l : List LMonoTy) (t : LMonoTy) (k : Nat) :
    l.foldr (fun σ acc => LMonoTy.arrow σ acc) t
      = (l.take k).foldr (fun σ acc => LMonoTy.arrow σ acc)
          ((l.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) t) := by
  rw [← List.foldr_append, List.take_append_drop]

/-- The inversion of `OpsConsistentR` at an `.op` node. Either the factory holds no operator of that name, or
    the annotation is an instance of the generic type of that operator. The statement *names* the instantiating
    substitution, and it names no implicit argument of the constructor. -/
theorem opsConsistentR_op_inv (F : @Factory LExprParams') (name : String)
    (annot : LMonoTy)
    (h : Lambda.OpsConsistentR F (.op () ⟨name, ()⟩ (some annot))) :
    F[name]? = none ∨
      ∃ (fn : LFunc LExprParams') (T : Lambda.Subst), F[name]? = some fn ∧
        annot = LMonoTy.subst T (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)) := by
  cases h with
  | op_notin h => exact Or.inl h
  | op_in hfn hty => exact Or.inr ⟨_, _, hfn, hty⟩

set_option maxHeartbeats 800000 in
/-- **`SchemeInstAt` from an `OpsConsistentR` of the caller.**

    This theorem is the intended route to the premise of `genLExpr_complete_poly_fullySpecShaped` about an
    instance of a scheme. A caller who holds `OpsConsistentR F` for the `.op` node, together with `PCtxWF` and
    the membership of the scheme in `pctx`, builds no matcher.

    The content is a change of the variables. `OpsConsistentR.op_in` gives a substitution `T` with
    `annot = subst T monoTy`, which is an instance of the *original* body of the scheme. `SchemeInstAt` asks
    for a matcher of the body *after* `freshenBoundVars` renames its binders. `schemeMatcher` is that matcher:
    it sends each renamed binder to the image of the original binder under `T`, which `subst_schemeMatcher`
    proves. The split point is the number of the arguments that the term applies, and
    `decomposeArrow_subst_of_renaming` moves the arrow spine of the scheme across the renaming.

    ### The premises, and why each of them is necessary

    - `hPctx` and `hmem` say *which* scheme of `pctx` the operator is, and they tie it to the factory. `hmem`
      also *is* the first part of `SchemeInstAt`.
    - `hops` is the `OpsConsistentR` premise, and it gives `T`. `HasTypeA'` cannot give `T`, because its `.op`
      rule accepts each annotation that the node carries. Therefore a well-typed term can carry an annotation
      that is not an instance of the scheme.
    - `hAnnot` gives the shape of the spine, which the typing derivation at the call site forces.
    - `hclosed`, `harity`, `hsplit` and `hdet` are decidable facts about the scheme and about the split point.
      They give closedness, a limit on the arity, a split point in range, and the determinacy of the split. For
      a concrete factory, `decide` or `simp` proves each of them.
    - `hfreshNodup` says that **the renaming sends no two binders to one name.** That is a true side condition.
      `freshenBoundVars` renames the binders that clash with the context, and it draws each replacement outside
      the context *and not outside the other binders*. Therefore it can send two different binders to one name.
      For an example, `freshenBoundVars ["a", "b"] (a → b) ["a"]` gives `(["b", "b"], b → b)`. In that case no
      matcher exists, because the two images under `T` would have to be equal. `SchemeInstAt` is then false, and
      the generator truly cannot reach the instance. -/
theorem schemeInstAt_of_opsConsistentR
    (F : @Factory LExprParams') (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (bctx : BVarCtx) (τ : LMonoTy) (name : String) (annot : LMonoTy)
    (concreteArgTys : List LMonoTy) (maxNumArgs : Nat)
    (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (hPctx : PCtxWF F pctx)
    (hmem : (name, Lambda.LTy.forAll boundVars monoTy) ∈ pctx)
    (hops : Lambda.OpsConsistentR F (.op () ⟨name, ()⟩ (some annot)))
    (hAnnot : annot = concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
    (hclosed : ∀ v ∈ monoTy.freeVars, v ∈ boundVars)
    (harity : (decomposeArrow monoTy).1.length ≤ maxNumArgs)
    (hsplit : concreteArgTys.length ≤ (decomposeArrow monoTy).1.length)
    (hfreshNodup : (boundVars.map (renameTyVar boundVars
      ((LMonoTy.freeVars τ ++ (generableTypesFromCtx bctx fctx octx).flatMap
        LMonoTy.freeVars).eraseDups))).Nodup)
    (hdet : ∀ σ ∈ (decomposeArrow monoTy).1.take concreteArgTys.length,
      ∀ v ∈ σ.freeVars,
      v ∈ (((decomposeArrow monoTy).1.drop concreteArgTys.length).foldr
        (fun σ acc => LMonoTy.arrow σ acc) (decomposeArrow monoTy).2).freeVars) :
    SchemeInstAt fctx octx pctx bctx τ name concreteArgTys maxNumArgs := by
  -- The scheme is the generic type of a factory function.
  obtain ⟨fn, hget, hlty⟩ := hPctx name (.forAll boundVars monoTy) hmem
  rw [LTy.forAll.injEq] at hlty
  obtain ⟨_, hmono⟩ := hlty
  -- `OpsConsistentR` gives the instantiating substitution `T`.
  obtain ⟨T, hTannot⟩ : ∃ T : Lambda.Subst,
      LMonoTy.subst T monoTy = concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ := by
    rcases opsConsistentR_op_inv F name annot hops with hnone | ⟨fn', T, hfn, hty⟩
    · rw [hget] at hnone; exact absurd hnone (by simp)
    · have hfneq : fn' = fn := Option.some.inj (hfn.symm.trans hget)
      rw [hfneq] at hty
      exact ⟨T, by rw [hmono, ← hty]; exact hAnnot⟩
  -- Name the arrow decomposition of the *original* body of the scheme.
  obtain ⟨origArgs, origRet, hdecEq⟩ : ∃ a b, decomposeArrow monoTy = (a, b) := ⟨_, _, rfl⟩
  rw [hdecEq] at harity hsplit hdet
  simp only at harity hsplit hdet
  have hmonoFold : monoTy = origArgs.foldr (fun σ acc => LMonoTy.arrow σ acc) origRet := by
    have h := decomposeArrow_foldr monoTy; rw [hdecEq] at h; simpa using h
  -- Each free variable of each part of the body of the scheme is a binder of the scheme.
  obtain ⟨hfvRet, hfvArg⟩ := decomposeArrow_freeVars_subset monoTy
  rw [hdecEq] at hfvRet hfvArg
  simp only at hfvRet hfvArg
  have hfvArgs : ∀ σ ∈ origArgs, ∀ v ∈ σ.freeVars, v ∈ boundVars :=
    fun σ hσ v hv => hclosed v (hfvArg σ hσ v hv)
  have hfvSuffix : ∀ v ∈ ((origArgs.drop concreteArgTys.length).foldr
      (fun σ acc => LMonoTy.arrow σ acc) origRet).freeVars, v ∈ boundVars := by
    intro v hv
    rcases mem_freeVars_foldr_arrow _ _ v hv with ⟨σ, hσ, hvσ⟩ | hvret
    · exact hclosed v (hfvArg σ (List.mem_of_mem_drop hσ) v hvσ)
    · exact hclosed v (hfvRet v hvret)
  -- Split the equation of the instance at the number of the applied arguments. The applied prefix gives the
  -- concrete argument types, and the remaining suffix gives the target type `τ`.
  obtain ⟨hprefixT, hτT⟩ : concreteArgTys
      = (origArgs.take concreteArgTys.length).map (LMonoTy.subst T) ∧
      τ = LMonoTy.subst T ((origArgs.drop concreteArgTys.length).foldr
        (fun σ acc => LMonoTy.arrow σ acc) origRet) := by
    refine foldr_arrow_inj _ _ _ _ (by simp; omega) ?_
    rw [← subst_foldr_arrow, ← foldr_arrow_split, ← hmonoFold]
    exact hTannot.symm
  -- Name the set of the names in use that the generator gives to `freshenBoundVars`.
  obtain ⟨viu, hviu⟩ : ∃ l, (LMonoTy.freeVars τ ++
      (generableTypesFromCtx bctx fctx octx).flatMap LMonoTy.freeVars).eraseDups = l := ⟨_, rfl⟩
  rw [hviu] at hfreshNodup
  unfold SchemeInstAt
  rw [hviu]
  -- The data of the renaming, and the matcher.
  refine ⟨boundVars, monoTy,
    boundVars.map (renameTyVar boundVars viu),
    LMonoTy.subst (freshenRenaming boundVars viu) monoTy,
    origArgs.map (LMonoTy.subst (freshenRenaming boundVars viu)),
    LMonoTy.subst (freshenRenaming boundVars viu) origRet,
    concreteArgTys.length, schemeMatcher boundVars viu T,
    hmem, rfl, ?_, by simpa using harity, by simp; omega, hclosed, ?_, ?_, ?_⟩
  · -- the arrow spine survives the renaming
    rw [decomposeArrow_subst_of_renaming _
        (fun v => ⟨_, subst_freshenRenaming_ftvar boundVars viu v⟩) monoTy, hdecEq]
  · -- the matcher matches the leftover suffix against `τ`
    rw [← List.map_drop, ← subst_foldr_arrow,
      subst_schemeMatcher _ _ T hfreshNodup _ hfvSuffix]
    exact hτT.symm
  · -- split determinacy transports across the renaming
    intro σ' hσ' v' hv'
    rw [← List.map_take] at hσ'
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hσ'
    obtain ⟨v, hv, hv'mem⟩ := freeVars_subst_exists _ σ v' hv'
    rw [← List.map_drop, ← subst_foldr_arrow]
    exact freeVars_subst_mono _ _ v (hdet σ hσ v hv) v' hv'mem
  · -- the applied prefix instantiates to the concrete argument types
    have hmapeq : (origArgs.take concreteArgTys.length).map
        (LMonoTy.subst (schemeMatcher boundVars viu T)
          ∘ LMonoTy.subst (freshenRenaming boundVars viu))
        = (origArgs.take concreteArgTys.length).map (LMonoTy.subst T) := by
      apply List.map_congr_left
      intro σ hσ
      exact subst_schemeMatcher _ _ T hfreshNodup σ
        (fun v hv => hfvArgs σ (List.mem_of_mem_take hσ) v hv)
    rw [← List.map_take, List.map_map, hmapeq]
    exact hprefixT

-- ── The premises about a scheme hold for a real scheme ───────────────
--
-- The premises of `schemeInstAt_of_opsConsistentR` about a scheme are `hclosed`, `harity`, `hsplit`, `hdet`
-- and `hfreshNodup`. Each of them is a decidable fact about the scheme and about the split point, so `decide`
-- proves each of them at a call site. The guards below confirm that on a real entry of `corePolyOps`, which is
-- `Sequence.append : ∀a. Seq a → Seq a → Seq a`. Therefore the premises are satisfiable, and they are not only
-- plausible.
--
-- Read the second guard about `hdet`. The determinacy holds even at a *full* application here, because the
-- variable `a` still occurs in the result type. Therefore `hdet` excludes more than a partial application. It
-- excludes exactly a split where a variable of the scheme is absent from the remaining suffix, as in
-- `Sequence.length : ∀a. Seq a → int` at the split point 1, and that is where the generator takes a random
-- sample.

private def seqOfA : LMonoTy := .tcons "Sequence" [.ftvar "a"]
private def appendScheme : LMonoTy := LMonoTy.arrow seqOfA (LMonoTy.arrow seqOfA seqOfA)

example : ∀ v ∈ appendScheme.freeVars, v ∈ ["a"] := by decide

example : (decomposeArrow appendScheme).1.length ≤ 3 := by decide

example : ∀ σ ∈ (decomposeArrow appendScheme).1.take 1, ∀ v ∈ σ.freeVars,
    v ∈ (((decomposeArrow appendScheme).1.drop 1).foldr
      (fun σ acc => LMonoTy.arrow σ acc) (decomposeArrow appendScheme).2).freeVars := by decide

example : ∀ σ ∈ (decomposeArrow appendScheme).1.take 2, ∀ v ∈ σ.freeVars,
    v ∈ (((decomposeArrow appendScheme).1.drop 2).foldr
      (fun σ acc => LMonoTy.arrow σ acc) (decomposeArrow appendScheme).2).freeVars := by decide

/-- A scheme with one binder can never suffer the collapse of the renaming. Therefore `hfreshNodup` holds for
    each scheme of `corePolyOps` that has one type argument. -/
example (viu : List TyIdentifier) : (["a"].map (renameTyVar ["a"] viu)).Nodup := by simp

/-- An `OpsConsistentR` of an application spine gives an `OpsConsistentR` of the head of that spine. The
    `.app` constructor is the only way to build the spine, so each step of the proof is one inversion. -/
theorem mkApps_opsConsistentR_inv (F : @Factory LExprParams') (base : LExpr')
    (args : List LExpr') (h : Lambda.OpsConsistentR F (mkApps base args)) :
    Lambda.OpsConsistentR F base := by
  induction args generalizing base with
  | nil => simpa only [mkApps, List.foldl_nil] using h
  | cons a rest ih =>
    have h' := ih (.app () base a) (by simpa only [mkApps, List.foldl_cons] using h)
    cases h' with
    | app hbase _ => exact hbase

/-- **The completeness of the polymorphic case from the two judgments, with no generator internal.**

    This is the statement at the level of the specification. A spine over a polymorphic operator is reachable
    from `HasTypeA'` *and* `OpsConsistentR`, together with decidable facts about the scheme. Those two
    judgments are the same two that the direction of soundness establishes, in `genLExpr_sound` and in
    `genLExpr_opsConsistentR_factory`. The hypotheses name no `findPolymorphicOps`, no `unifyTypes` and no
    `SchemeInstAt`, because `schemeInstAt_of_opsConsistentR` builds the witness inside the proof.

    **Why `OpsConsistentR` is a premise here.** It does not follow from `HasTypeA'`. The `.op` typing rule
    accepts each annotation that a node carries, so a well-typed term can carry an annotation that is not an
    instance of the scheme of the operator. The generator would never give such a term, and it is correctly
    not reachable. `OpsConsistentR` closes that gap, and it keeps the two directions symmetric. On the side of
    soundness, both judgments are *theorems* about a generated term. On the side of completeness, both are
    *assumptions* about the target term.

    The other premises are the bundle for the recursive completeness of each argument, as in each other
    statement of completeness here, the facts about the context of the samples, and the side conditions of
    `schemeInstAt_of_opsConsistentR` about the scheme. Those side conditions include `hfreshNodup`, which says
    that the renaming sends no two binders to one name, and `hdet`, which gives the determinacy of the split
    point. -/
theorem genLExpr_complete_poly_opsConsistentR
    (F : @Factory LExprParams') (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : ∃ m, τ ∈ SPMF.support (genLMonoTy (G := SPMF) tvars m)) (maxNumArgs : Nat)
    (name : String) (annot : LMonoTy) (args : List LExpr')
    (concreteArgTys : List LMonoTy)
    (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (hwt : HasTypeA' bctx (mkApps (.op () ⟨name, ()⟩ (some annot)) args) τ)
    (hops : Lambda.OpsConsistentR F (mkApps (.op () ⟨name, ()⟩ (some annot)) args))
    (sampledTys : List LMonoTy)
    (hLen : sampledTys.length = max maxNumArgs (maxBinders pctx))
    (hValid : ∀ σ ∈ sampledTys,
      ((generableTypesFromCtx bctx fctx octx).length > 0 →
        σ ∈ generableTypesFromCtx bctx fctx octx) ∧
      (¬((generableTypesFromCtx bctx fctx octx).length > 0) →
        σ ∈ SPMF.support (pickBaseType (G := SPMF))))
    (hAnnot : annot = concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
    (hArgLen : args.length = concreteArgTys.length)
    (hArgsComplete : List.Forall₂
      (fun arg σ => (∃ m, σ ∈ SPMF.support (genLMonoTy (G := SPMF) tvars m)) ∧
        emptyNames arg ∧ allVarsInCtx fctx octx arg ∧
        AllTypesSimple tvars (depth - 1) bctx arg ∧ termDepth bctx arg ≤ depth - 1)
      args concreteArgTys)
    (hgen : generableTypesFromCtx bctx fctx octx ≠ [])
    (hPctx : PCtxWF F pctx)
    (hmem : (name, Lambda.LTy.forAll boundVars monoTy) ∈ pctx)
    (hclosed : ∀ v ∈ monoTy.freeVars, v ∈ boundVars)
    (harity : (decomposeArrow monoTy).1.length ≤ maxNumArgs)
    (hsplit : concreteArgTys.length ≤ (decomposeArrow monoTy).1.length)
    (hfreshNodup : (boundVars.map (renameTyVar boundVars
      ((LMonoTy.freeVars τ ++ (generableTypesFromCtx bctx fctx octx).flatMap
        LMonoTy.freeVars).eraseDups))).Nodup)
    (hdet : ∀ σ ∈ (decomposeArrow monoTy).1.take concreteArgTys.length,
      ∀ v ∈ σ.freeVars,
      v ∈ (((decomposeArrow monoTy).1.drop concreteArgTys.length).foldr
        (fun σ acc => LMonoTy.arrow σ acc) (decomposeArrow monoTy).2).freeVars) :
    (mkApps (.op () ⟨name, ()⟩ (some annot)) args)
      ∈ SPMF.support
        (genLExpr (G := SPMF) fctx octx pctx tvars bctx depth τ maxNumArgs) :=
  genLExpr_complete_poly_fullySpecShaped fctx octx pctx tvars bctx depth τ hτ name annot args
    hwt sampledTys concreteArgTys hLen hValid hAnnot hArgLen hArgsComplete hgen
    (schemeInstAt_of_opsConsistentR F fctx octx pctx bctx τ name annot concreteArgTys
      maxNumArgs boundVars monoTy hPctx hmem
      (mkApps_opsConsistentR_inv F _ args hops) hAnnot hclosed harity hsplit hfreshNodup hdet)
