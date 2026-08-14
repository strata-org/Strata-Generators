import StrataGenerators.HasTypeAGen
import StrataGenerators.HasTypeAGen.Defs
import StrataGenerators.HasTypeAGen.IndirSupport
import StrataGenerators.HasTypeAGen.OpsConsistentBridge
import Strata.DL.Lambda.Denote.Assumptions

open Lambda RandomChoice ArbNat ArbChar ArbString SetGen

set_option linter.unusedSimpArgs false

/-!
# `OpsConsistentR` for generated `LExpr`s

This module establishes that the generator (`genLExpr` and friends) produces
terms satisfying Strata's *declarative* `OpsConsistentR` predicate — the inductive
specification that every `.op` type annotation is *some* instantiation of the
factory function's generic type. Together with `genLExpr_sound`/`genLExpr_complete`
(which handle `HasTypeA`) this makes the generator sound and complete with respect
to *both* `HasTypeA` and `OpsConsistentR`.

`OpsConsistentR` (`public` in Strata's `Assumptions.lean`) is named directly — no
local copy. The proofs are stated *directly* against `OpsConsistentR` and closed by
its constructors, so no operational `OpsConsistent` unfolding or
`OpsConsistent_OpsConsistentR` bridge is used. The only `module`-only helper they
need is `mem_get?_eq` (a Factory `nameMap` lookup), in
`HasTypeAGen/OpsConsistentBridge.lean`.

Working against the declarative `OpsConsistentR` (rather than the operational
`OpsConsistent`, whose `.op` check runs `opTypeSubst` and demands the annotation be
*reconstructible* by unification) is what makes this proof simple: `OpsConsistentR`'s
`.op_in` constructor asks only for the *existence* of an instantiating substitution,
and the generator builds every polymorphic annotation as exactly such an instance.
No ground-matching unification-completeness result is needed.

## Why the generator is `OpsConsistentR`

Every `.op` node a generated term can contain comes from one of two places:

* **`pickOp`** (inside `genLExprBase`): the annotation is exactly the *generic*
  factory type of the operator (as computed by `factoryOps`). It is therefore the
  identity instance `genericTy.subst []`, which `OpsConsistentR.op_in` accepts
  directly (`pickOp_opsConsistentR`). The same holds for the monomorphic Indir op
  node (`indir_op_opsConsistentR`).

* **`genIndirPoly`**: the annotation is `concreteArgTys.foldr arrow τ`, built as a
  substitution instance of the operator's generic type (a bound-variable freshening
  renaming composed with the generator's own substitution — see
  `docs/ops-consistent-capture-bug.md`). The forward-instance guard in
  `findPolymorphicOps` (`subst fullSubst retTy == τ`) ensures the instance targets `τ`;
  `findPolymorphicOps_instanceR` recovers a single witnessing substitution, discharged
  from a factory-well-formedness hypothesis `PCtxWF` (via
  `PolyOpsConsistentR_of_PCtxWF`), giving the unconditional
  `genLExpr_opsConsistentR_of_PCtxWF`. Unlike the old ground-only approach this
  permits annotations mentioning a free (non-quantified) type variable.

All compound cases (`.app`, `.ite`, `.abs`, `.eq`, `.quant`) are structural.
-/

-- ── `factoryOps` characterization ────────────────────────────────────

/-- Every operator entry produced by `factoryOps F` resolves to a factory
    function whose generic type is exactly the entry's type. Since `factoryOps`
    now builds the type as `mkArrow' fn.output fn.inputs.values` directly, the
    type equality is immediate — no arrow-spine reconciliation is needed. -/
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

/-- Well-formedness linking a polymorphic operator context `pctx` to the factory
    `F`: every `(name, lty)` in `pctx` is the polymorphic type scheme of some
    factory function `fn` (i.e. `lty = ∀ fn.typeArgs. mkArrow' fn.output fn.inputs.values`),
    and `F[name]? = some fn`.

    For the *declarative* `OpsConsistentR` relation, this is all we need — no
    `freeVars ⊆ typeArgs` invariant is required. `OpsConsistentR`'s `.op_in`
    constructor demands only the *existence* of a substitution turning the generic
    type into the annotation, and the generator builds its annotation as exactly
    such a substitution instance (see `findPolymorphicOps_instanceR`); it never runs
    `opTypeSubst`, so the monomorphic short-circuit that forced the extra invariant
    in the operational proof (`docs/ops-consistent-polymorphic-gap.md`) does not
    arise here. -/
def PCtxWF (F : @Factory LExprParams') (pctx : PolyOpCtx) : Prop :=
  ∀ (name : String) (lty : Lambda.LTy),
    (name, lty) ∈ pctx →
    ∃ (fn : LFunc LExprParams'), F[name]? = some fn ∧
      lty = .forAll fn.typeArgs (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))

/-- The polymorphic operator context extracted directly from a factory is always
    well-formed with respect to that factory. Since `factoryPolyOps` builds each
    entry as exactly the scheme `PCtxWF` demands, the proof is pure `filterMap`
    bookkeeping — no assumption required. This is what makes the factory
    generators unconditionally op-consistent even with polymorphic operators
    enabled (see `genLExpr_opsConsistentR_factory`). -/
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

-- ── Leaf-op consistency (`pickOp`) ───────────────────────────────────

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

/-- An op node emitted by `pickOp` on `factoryOps F` is `Lambda.OpsConsistentR`.
    The annotation `τ` equals the operator's generic factory type
    (`mkArrow' fn.output fn.inputs.values`), which is exactly the instance
    `OpsConsistentR.op_in` requires (with the empty/identity substitution). -/
theorem pickOp_opsConsistentR (F : @Factory LExprParams') (τ : LMonoTy) (name : String)
    (hmem : name ∈ opsOfType (factoryOps F) τ) :
    Lambda.OpsConsistentR F (.op () ⟨name, ()⟩ (some τ)) := by
  have hoctx : (name, τ) ∈ (factoryOps F).ops := mem_opsOfType _ _ _ hmem
  obtain ⟨fn, hget, hτ⟩ := factoryOps_mem_char F name τ hoctx
  -- `τ = genericTy` is the identity instance `genericTy.subst []`.
  exact .op_in (tySubst := []) hget (by rw [hτ]; exact (LMonoTy.subst_of_hasEmptyScopes (by simp) _).symm)

-- ── Public support characterizations for pick* (mirror private ones) ──

private theorem list_map_ne_nil_of_length_pos' {α β : Type} {xs : List α} {f : α → β}
    (h : xs.length > 0) : xs.map f ≠ [] := by
  intro heq
  apply List.ne_nil_of_length_pos h
  apply List.map_eq_nil_iff.mp heq

theorem mem_support_pickOp_iff' {octx : OpCtx} {τ : LMonoTy}
    {hv : (opsOfType octx τ).length > 0} {e : LExpr'} :
    e ∈ (pickOp (G := SetGen.Set) octx τ hv) ↔
      ∃ name ∈ opsOfType octx τ, e = .op () ⟨name, ()⟩ (some τ) := by
  change e ∈ SetGen.support (pickOp (G := SetGen.Set) octx τ hv) ↔ _
  simp only [pickOp, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv), List.mem_map]
  constructor
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩

/-- Any op node produced by `pickOp` on `factoryOps F` is `Lambda.OpsConsistentR`. -/
theorem pickOp_mem_opsConsistentR (F : @Factory LExprParams') (τ : LMonoTy)
    {hv : (opsOfType (factoryOps F) τ).length > 0} {e : LExpr'}
    (he : e ∈ (pickOp (G := SetGen.Set) (factoryOps F) τ hv)) :
    Lambda.OpsConsistentR F e := by
  rw [mem_support_pickOp_iff'] at he
  obtain ⟨name, hmem, rfl⟩ := he
  exact pickOp_opsConsistentR F τ name hmem


/-- Any node produced by `pickBVar` is a `.bvar`, hence `Lambda.OpsConsistentR`. -/
theorem pickBVar_mem_opsConsistentR (F : @Factory LExprParams') (bctx : BVarCtx) (τ : LMonoTy)
    {hv : (bvarsOfType bctx τ).length > 0} {e : LExpr'}
    (he : e ∈ (pickBVar (G := SetGen.Set) bctx τ hv)) :
    Lambda.OpsConsistentR F e := by
  change e ∈ SetGen.support (pickBVar (G := SetGen.Set) bctx τ hv) at he
  simp only [pickBVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv),
    List.mem_map] at he
  obtain ⟨i, _, rfl⟩ := he
  exact .bvar

/-- Any node produced by `pickFVar` is a `.fvar`, hence `Lambda.OpsConsistentR`. -/
theorem pickFVar_mem_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (τ : LMonoTy)
    {hv : (fvarsOfType fctx τ).length > 0} {e : LExpr'}
    (he : e ∈ (pickFVar (G := SetGen.Set) fctx τ hv)) :
    Lambda.OpsConsistentR F e := by
  change e ∈ SetGen.support (pickFVar (G := SetGen.Set) fctx τ hv) at he
  simp only [pickFVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv),
    List.mem_map] at he
  obtain ⟨name, _, rfl⟩ := he
  exact .fvar

private theorem norm_bool' : LMonoTy.bool = LMonoTy.tcons "bool" [] := rfl
private theorem norm_int' : LMonoTy.int = LMonoTy.tcons "int" [] := rfl
private theorem norm_string' : LMonoTy.string = LMonoTy.tcons "string" [] := rfl
private theorem norm_real' : LMonoTy.real = LMonoTy.tcons "real" [] := rfl
private theorem norm_arrow' (τ₁ τ₂ : LMonoTy) :
    LMonoTy.arrow τ₁ τ₂ = LMonoTy.tcons "arrow" [τ₁, τ₂] := rfl

-- ── Indir/IndirPoly support, needed by `genLExprBase_opsConsistentR` ──
--
-- The Indir/IndirPoly rules live inside `genLExprBase`, so everything
-- below is consumed by `genLExprBase_opsConsistentR` and has to precede it.
-- Previously it sat after that theorem, which was fine while the rules existed
-- only in `genLExpr`.

-- ── mkApps and mapM-argument consistency ─────────────────────────────

/-- `mkApps` of a `OpsConsistentR` base and `OpsConsistentR` args is
    `OpsConsistentR` (the declarative version, via the `.app` constructor). -/
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

/-- `mapM`-lifted op-consistency, parametric in the argument generator: if every
    term `genArg σ` can produce is `OpsConsistentR`, so is every element of a list
    the `mapM` produces. Parametric because `genLExpr` uses `genLExprBase` in
    argument position at the depth floor and *itself* above it. -/
theorem mapM_genArg_opsConsistentR (F : @Factory LExprParams')
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → Lambda.OpsConsistentR F a)
    (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set) genArg argTys)) :
    ∀ a ∈ args, Lambda.OpsConsistentR F a := by
  induction argTys generalizing args with
  | nil =>
    simp only [List.mapM_nil, SetGen.Set.mem_pure] at hargs
    subst hargs; intro a ha; simp at ha
  | cons σ rest ih =>
    simp only [List.mapM_cons, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at hargs
    obtain ⟨x, hx, tl, htl, rfl⟩ := hargs
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hArg σ a hx
    · exact ih tl htl a ha


-- ── Monomorphic Indir op-node consistency ────────────────────────────

/-- Public version of `findOpsInCtx` membership: an entry `(name, argTys)`
    corresponds to an octx entry with the reconstructed curried type. -/
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

/-- The op node in the monomorphic Indir rule (annotated with the reconstructed
    curried type from `findOpsInCtx (factoryOps F) τ`) is `Lambda.OpsConsistentR`.
    The annotation equals the operator's generic type, so it is the identity
    instance `genericTy.subst []` that `OpsConsistentR.op_in` requires. -/
theorem indir_op_opsConsistentR (F : @Factory LExprParams') (τ : LMonoTy)
    (name : String) (argTys : List LMonoTy)    (hmem : (name, argTys) ∈ findOpsInCtx (factoryOps F) τ) :
    Lambda.OpsConsistentR F
      (.op () ⟨name, ()⟩ (some (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) := by
  obtain ⟨hoctx, _⟩ := findOpsInCtx_mem' hmem
  obtain ⟨fn, hget, hty⟩ := factoryOps_mem_char F name _ hoctx
  exact .op_in (tySubst := []) hget (by rw [hty]; exact (LMonoTy.subst_of_hasEmptyScopes (by simp) _).symm)

-- ── Polymorphic IndirPoly op-node consistency ────────────────────────

/-- The assumption that every polymorphic-operator annotation `genIndirPoly`
    can emit for target `τ` is `OpsConsistentR`: for every candidate
    `(name, concreteArgTys)` in `findPolymorphicOps pctx τ generableTys sampledTys`,
    the op node annotated with `concreteArgTys.foldr arrow τ` is consistent.

    **This predicate is fully PROVEN** — see `PolyOpsConsistentR_of_PCtxWF`,
    which derives it from `PCtxWF F pctx` (a factory-well-formedness condition
    discharged for any real factory). It is kept as an explicit hypothesis on the
    general `genIndirPoly_opsConsistentR`/`genLExpr_opsConsistentR` below only so
    those theorems stay maximally general; the unconditional top-level result is
    `genLExpr_opsConsistentR_of_PCtxWF`.

    Against the *declarative* `OpsConsistentR` the proof is direct and needs no
    ground-matching machinery: the generator builds its annotation as
    `subst fullSubst (subst renameSubst genericTy)`, a genuine substitution
    *instance* of the operator's generic type, which is exactly the witness
    `OpsConsistentR.op_in` asks for (`findPolymorphicOps_instanceR`). The
    forward-instance guard in `findPolymorphicOps` (`subst fullSubst retTy == τ`)
    ensures the instance actually targets `τ`; unlike the old ground-only guard it
    permits annotations mentioning a free (non-quantified) type variable.

    It holds vacuously when `pctx = []` (see the `…_nil` results, which need no
    such assumption). -/
def PolyOpsConsistentR (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (bctx : BVarCtx) (fctx : FVarCtx) (τ : LMonoTy) (maxNumArgs : Nat := 3) : Prop :=
  ∀ (sampledTys : List LMonoTy) (name : String) (concreteArgTys : List LMonoTy),
    (name, concreteArgTys) ∈
      findPolymorphicOps pctx τ (generableTypesFromCtx bctx fctx (factoryOps F))
        sampledTys maxNumArgs →
    Lambda.OpsConsistentR F
      (.op () ⟨name, ()⟩ (some (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)))

/-- `decomposeArrow` is a right inverse of the right-nested-arrow fold. -/
theorem decomposeArrow_foldr (t : LMonoTy) :
    t = (decomposeArrow t).1.foldr (fun σ acc => LMonoTy.arrow σ acc) (decomposeArrow t).2 := by
  fun_induction decomposeArrow t with
  | case1 σ rest args ret hrec ih =>
    simp only [hrec, List.foldr_cons]
    show LMonoTy.arrow σ rest = LMonoTy.arrow σ _
    congr 1
    rw [hrec] at ih; simpa using ih
  | case2 ty hne => rfl

/-- `LMonoTys.subst` is the pointwise `map` of `LMonoTy.subst` (public restatement,
    since Strata's `LMonoTys.subst_eq_map` lives in a `module` file). -/
theorem LMonoTys_subst_map (S : Lambda.Subst) (args : List LMonoTy) :
    LMonoTys.subst S args = args.map (LMonoTy.subst S) := by
  have h := LMonoTy.subst_unfold S (LMonoTy.tcons "x" args)
  rw [LMonoTy.subst_tcons] at h
  simp only at h
  injection h with _ hh

/-- Substitution distributes over a right-nested arrow fold.

    `LMonoTys_subst_map` handles the `hasEmptyScopes` short-circuit once and for all, so
    unlike the previous version this proof needs no case split on it. -/
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

/-- The single-scope substitution that sends each free variable `v` of `P` to its
    image under the composite `subst T2 ∘ subst T1`. Applied to `P` (or any type
    whose free variables are all free in `P`) it reconstructs the composite; that
    is all `OpsConsistentR`'s existence witness needs — no groundness or
    well-formedness is required.

    A `Subst` scope is an opaque `Strata.Util.HMap`, so the scope is built from
    `composeWitnessBindings` through `substScope` rather than written as a list. -/
def composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst) : Lambda.Subst :=
  substScope (composeWitnessBindings P T1 T2)

/-- Looking up a free variable `v` of `P` in `composeWitnessScope P T1 T2` returns
    its composite image. -/
theorem find?_composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst)
    (v : TyIdentifier) (hv : v ∈ LMonoTy.freeVars P) :
    Strata.Util.HMaps.find? (composeWitnessScope P T1 T2) v
      = some (LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))) := by
  rw [composeWitnessScope, Freshening.find?_substScope_eq_lookup, composeWitnessBindings]
  -- `List.lookup` over `l.map (fun v => (v, g v))` at a key `v ∈ l` returns `g v`.
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

/-- **Composite-to-single-scope collapse.** If `mty`'s free variables are all free
    variables of `P`, then applying the single scope `composeWitnessScope P T1 T2` to
    `mty` equals applying the composite `subst T2 ∘ subst T1`.

    `LMonoTy.subst_unfold` absorbs the `hasEmptyScopes` short-circuit, so — unlike the
    previous version — the proof is a plain structural induction with no case split on
    whether the witness scope happens to be empty. -/
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

/-- **Composite-instance packaging (declarative).** If `A` equals the composite
    `subst T2 (subst T1 P)`, then there is a *raw* substitution `S` with
    `A = subst S P`. The witness is the single scope `composeWitnessScope P T1 T2`;
    unlike the operational proof this needs no `SubstWF` and no groundness, because
    `OpsConsistentR.op_in` accepts any `Subst`, not a well-formed `SubstInfo`. -/
theorem composite_instance_subst (A P : LMonoTy) (T1 T2 : Lambda.Subst)
    (hA : A = LMonoTy.subst T2 (LMonoTy.subst T1 P)) :
    ∃ S : Lambda.Subst, A = LMonoTy.subst S P := by
  refine ⟨composeWitnessScope P T1 T2, ?_⟩
  rw [hA]
  exact (subst_composeWitnessScope P T1 T2 P (fun v hv => hv)).symm

/-- The freshened body is a renaming (a substitution) applied to the original. -/
theorem freshenBoundVars_snd_eq_subst (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (contextVars : List TyIdentifier) :
    ∃ R : Lambda.Subst, (freshenBoundVars boundVars monoTy contextVars).2
      = LMonoTy.subst R monoTy := by
  unfold freshenBoundVars
  exact ⟨_, rfl⟩

/-- **Instance witness (declarative).** Every candidate `(name, concreteArgTys)`
    that `findPolymorphicOps` returns has, for the corresponding factory function
    `fn` (`F[name]? = some fn`), an annotation `A = concreteArgTys.foldr arrow τ`
    that is a substitution *instance* of `fn`'s generic type
    `mkArrow' fn.output fn.inputs.values` — i.e. there is a substitution `S` with
    `A = subst S genericTy`. That is exactly the witness `OpsConsistentR.op_in`
    requires.

    Compared with the operational version, this needs **no** groundness and no
    unification-completeness result: the forward-instance guard
    (`subst fullSubst retTy == τ`) gives the orientation equality directly (no
    unification-soundness argument), and the witness is assembled purely by
    composing the freshening renaming with the generator's substitution via
    `composite_instance_subst` (no `SubstWF`). Annotations mentioning a free type
    variable are handled uniformly. -/
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
  -- Step 1: unfold membership in `findPolymorphicOps` down to the success branch.
  -- The generator is now `pctx.flatMap` (each scheme contributes candidates at
  -- several split points), whose per-scheme body is `if arity > maxNumArgs then []`
  -- else a `filterMap` over the split points `k ∈ [0, arity]`. So membership peels
  -- as: a scheme `∈ pctx`, then (the arity guard held and) a split point `k` whose
  -- `Option` `do`-block returned `some (name, concreteArgTys)`.
  unfold findPolymorphicOps at hEntry
  simp only [List.mem_flatMap] at hEntry
  obtain ⟨⟨nm, boundVars, monoTy⟩, hmem, hfilt⟩ := hEntry
  -- Name the freshening result and its arrow decomposition (so the `let`s reduce).
  obtain ⟨freshBoundVars, freshMonoTy, hfreshEq⟩ :
      ∃ a b, freshenBoundVars boundVars monoTy
        (τ.freeVars ++ List.flatMap LMonoTy.freeVars generableTys).eraseDups = (a, b) :=
    ⟨_, _, rfl⟩
  obtain ⟨argTys, retTy, hdecEq⟩ :
      ∃ a b, decomposeArrow freshMonoTy = (a, b) := ⟨_, _, rfl⟩
  simp only [hfreshEq, hdecEq] at hfilt
  -- The arity `if` must have taken the `else` branch (membership in `[]` is false).
  split at hfilt
  · exact absurd hfilt (List.not_mem_nil)
  -- Now `hfilt` is membership in the split-point `filterMap`; extract the split
  -- point `k` and its `Option` `do`-block equation. The `do`-block has two `guard`s
  -- (undetermined-tyvars, then the forward-instance guard).
  rw [List.mem_filterMap] at hfilt
  obtain ⟨k, _, hopt⟩ := hfilt
  simp only [guard, bind, failure, pure, Option.pure_def, Option.bind_eq_some_iff,
    Option.ite_some_none_eq_some, Option.some.injEq, Prod.mk.injEq] at hopt
  obtain ⟨subst, hunif, _, ⟨hguard1, _⟩, _, ⟨hguard2, _⟩, hname, hcat⟩ := hopt
  subst hname
  -- Step 2: `PCtxWF` gives the factory function and the shape of its type.
  obtain ⟨fn, hget, hlty⟩ := hPctx nm (.forAll boundVars monoTy) hmem
  -- Injectivity of `.forAll`: boundVars = fn.typeArgs, monoTy = genericTy.
  rw [LTy.forAll.injEq] at hlty
  obtain ⟨hba, hmono⟩ := hlty
  have hgenericEq : monoTy = LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd) := hmono
  -- Step 3: the forward-instance guard *is* `subst fullSubst leftoverSuffix = τ`,
  -- where `leftoverSuffix = (argTys.drop k).foldr arrow retTy` is the un-applied
  -- suffix of the scheme's arrow type.
  have hunifEqFull : LMonoTy.subst
      (substScope ((findFreeTyVars freshBoundVars subst).zip sampledTys) ++ subst)
      ((argTys.drop k).foldr (fun σ acc => LMonoTy.arrow σ acc) retTy) = τ :=
    beq_iff_eq.mp hguard2
  -- Step 4: build the substitution witness.
  -- (a) `freshMonoTy = subst renameSubst monoTy` for the freshening renaming.
  obtain ⟨renameSubst, hfmt⟩ : ∃ R, freshMonoTy = LMonoTy.subst R monoTy := by
    obtain ⟨R, hR⟩ := freshenBoundVars_snd_eq_subst boundVars monoTy
      (τ.freeVars ++ List.flatMap LMonoTy.freeVars generableTys).eraseDups
    rw [hfreshEq] at hR; exact ⟨R, hR⟩
  -- (b) `A = subst fullSubst (subst renameSubst genericTy)`. The only delta from
  -- the fully-applied case is one `List.foldr_append`/`take_append_drop`: the
  -- scheme's arrow type splits as (applied prefix) ++ (leftover suffix) at `k`.
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
  -- Package into a single substitution witness (no groundness / no WF).
  obtain ⟨S, hS⟩ := composite_instance_subst
    (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
    (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))
    renameSubst (substScope ((findFreeTyVars freshBoundVars subst).zip sampledTys) ++ subst)
    hAeq
  exact ⟨fn, S, hget, hS⟩

/-- Under `PCtxWF`, the polymorphic-annotation assumption `PolyOpsConsistentR`
    holds — because every emitted annotation is a substitution instance of the
    operator's generic type (`findPolymorphicOps_instanceR`), which is exactly the
    witness `OpsConsistentR.op_in` (`OpsConsistentR.op_in`) demands. No case
    split on `typeArgs`, no groundness. -/
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
/-- The monomorphic Indir rule's output is `OpsConsistentR`: the op node's
    annotation is the operator's own generic type (`indir_op_opsConsistentR`) and
    the arguments come from `genArg`.

    Parametric in `genArg` for the same reason as the rest of `IndirSupport`:
    `genLExprBase` supplies its own recursive call at the smaller depth index. -/
theorem genIndir_opsConsistentR (F : @Factory LExprParams') (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → Lambda.OpsConsistentR F a)
    (h : (findOpsInCtx (factoryOps F) τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (genIndir (G := SetGen.Set) (factoryOps F) τ genArg h)) :
    Lambda.OpsConsistentR F e := by
  obtain ⟨nm, argTys, args, hmem, hargs, rfl⟩ :=
    genIndir_shape (factoryOps F) τ genArg h e he
  exact mkApps_opsConsistentR F _ args (indir_op_opsConsistentR F τ nm argTys hmem)
    (mapM_forall genArg hArg argTys args ((mem_mapM_iff' genArg argTys args).mpr hargs))

open StrataGenerators.IndirSupport in
/-- The polymorphic IndirPoly rule's output is `OpsConsistentR`, given the
    polymorphic-annotation assumption `PolyOpsConsistentR` (itself proven from
    `PCtxWF` by `PolyOpsConsistentR_of_PCtxWF`) and consistency of the fallback. -/
theorem genIndirPolyCore_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (bctx : BVarCtx) (τ : LMonoTy) (maxNumArgs : Nat)
    (hPoly : PolyOpsConsistentR F pctx bctx fctx τ maxNumArgs)
    (genArg : LMonoTy → SetGen.Set LExpr') (fallback : SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → Lambda.OpsConsistentR F a)
    (hFallback : ∀ a, a ∈ SetGen.support fallback → Lambda.OpsConsistentR F a)
    (e : LExpr')
    (he : e ∈ SetGen.support (genIndirPolyCore (G := SetGen.Set) fctx (factoryOps F) pctx
      bctx τ genArg fallback maxNumArgs)) :
    Lambda.OpsConsistentR F e := by
  rcases genIndirPolyCore_shape fctx (factoryOps F) pctx bctx τ genArg fallback maxNumArgs e he with
    ⟨sampled, nm, concreteArgTys, args, hmem, hargs, rfl⟩ | hfb
  · exact mkApps_opsConsistentR F _ args (hPoly sampled nm concreteArgTys hmem)
      (mapM_forall genArg hArg concreteArgTys args
        ((mem_mapM_iff' genArg concreteArgTys args).mpr hargs))
  · exact hFallback e hfb

set_option maxHeartbeats 1600000 in
theorem genLExprBase_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    -- The IndirPoly rule lives inside `genLExprBase`, so the
    -- polymorphic-annotation assumption this theorem needs is the same one
    -- `genLExpr_opsConsistentR` already takes — quantified over all binder
    -- contexts and target types, because the rule now fires at every subterm
    -- position rather than only at the root. `PolyOpsConsistentR_of_PCtxWF`
    -- discharges it for every type from a single `PCtxWF`, so the `PCtxWF`- and
    -- factory-derived corollaries below are unaffected.
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e := by
  rw [genLExprBase.eq_def] at he
  split at he
  case h_1 τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 (.arrow τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_arrow'] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, h⟩) | ((⟨hf, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩))
    · exact pickBVar_mem_opsConsistentR F bctx (.arrow τ₁ τ₂) h
    · exact h.elim
    · exact pickFVar_mem_opsConsistentR F fctx (.arrow τ₁ τ₂) h
    · exact h.elim
    · exact pickOp_mem_opsConsistentR F (.arrow τ₁ τ₂) h
    · exact h.elim
  case h_3 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 .bool) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_bool'] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (rfl | rfl) | ((⟨_, h⟩ | ⟨_, rfl | rfl⟩) | ((⟨hf, h⟩ | ⟨_, rfl | rfl⟩) | (⟨_, h⟩ | ⟨_, rfl | rfl⟩)))
    · exact .const
    · exact .const
    · exact pickBVar_mem_opsConsistentR F bctx .bool h
    · exact .const
    · exact .const
    · exact pickFVar_mem_opsConsistentR F fctx .bool h
    · exact .const
    · exact .const
    · exact pickOp_mem_opsConsistentR F .bool h
    · exact .const
    · exact .const
  case h_5 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 .int) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_int'] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩)))
    · exact .const
    · exact .const
    · exact pickBVar_mem_opsConsistentR F bctx .int h
    · exact .const
    · exact .const
    · exact pickFVar_mem_opsConsistentR F fctx .int h
    · exact .const
    · exact .const
    · exact pickOp_mem_opsConsistentR F .int h
    · exact .const
    · exact .const
  case h_9 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 .string) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_string'] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨k, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)))
    · exact .const
    · exact pickBVar_mem_opsConsistentR F bctx .string h
    · exact .const
    · exact pickFVar_mem_opsConsistentR F fctx .string h
    · exact .const
    · exact pickOp_mem_opsConsistentR F .string h
    · exact .const
  case h_11 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 .real) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_real'] at he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨r, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩)))
    · exact .const
    · exact pickBVar_mem_opsConsistentR F bctx .real h
    · exact .const
    · exact pickFVar_mem_opsConsistentR F fctx .real h
    · exact .const
    · exact pickOp_mem_opsConsistentR F .real h
    · exact .const
  case h_13 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 (.bitvec n)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨k, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)))
    · exact .const
    · exact pickBVar_mem_opsConsistentR F bctx (.bitvec n) h
    · exact .const
    · exact pickFVar_mem_opsConsistentR F fctx (.bitvec n) h
    · exact .const
    · exact pickOp_mem_opsConsistentR F (.bitvec n) h
    · exact .const
  case h_4 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) .bool) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_bool'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genBoolConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx (factoryOps F) tvars bctx n .bool) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) .bool),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)),
         (2, fun () => genEq (genGenerableTy fctx (factoryOps F) tvars bctx n) (genLExprBase fctx (factoryOps F) pctx tvars bctx n)),
         (2, fun () => genQuant .all (genGenerableTy fctx (factoryOps F) tvars bctx n)
           (fun τ' => genLExprBase fctx (factoryOps F) pctx tvars (τ' :: bctx) n)
           (fun τ' => genLExprBase fctx (factoryOps F) pctx tvars (τ' :: bctx) n .bool)),
         (2, fun () => genQuant .exist (genGenerableTy fctx (factoryOps F) tvars bctx n)
           (fun τ' => genLExprBase fctx (factoryOps F) pctx tvars (τ' :: bctx) n)
           (fun τ' => genLExprBase fctx (factoryOps F) pctx tvars (τ' :: bctx) n .bool)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .bool).length > 0 then pickBVar bctx .bool hv
           else genBoolConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .bool).length > 0 then pickFVar fctx .bool hf
           else genBoolConst),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .bool).length > 0 then pickOp (factoryOps F) .bool ho
           else genBoolConst),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) .bool).length > 0
           then genIndir (factoryOps F) .bool (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx .bool
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)) ]
      ) (by show 0 < 1+1+2+2+2+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genBoolConst, genApp, genIte, genEq, genQuant, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with rfl | rfl <;> exact .const
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · obtain ⟨τ', hτ'm, e₁, he₁, e₂, he₂, rfl⟩ := he
      exact .eq (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he₁) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he₂)
    · obtain ⟨τ', hτ'm, τ_tr, hτ_tr_m, tr, htr, body, hbody, rfl⟩ := he
      exact .quant (genLExprBase_opsConsistentR F fctx pctx tvars hPoly (τ' :: bctx) n _ _ htr) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly (τ' :: bctx) n _ _ hbody)
    · obtain ⟨τ', hτ'm, τ_tr, hτ_tr_m, tr, htr, body, hbody, rfl⟩ := he
      exact .quant (genLExprBase_opsConsistentR F fctx pctx tvars hPoly (τ' :: bctx) n _ _ htr) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly (τ' :: bctx) n _ _ hbody)
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickBVar_mem_opsConsistentR F bctx .bool h
      · exact .const
      · exact .const
    · rcases he with ⟨hf, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickFVar_mem_opsConsistentR F fctx .bool h
      · exact .const
      · exact .const
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickOp_mem_opsConsistentR F .bool h
      · exact .const
      · exact .const
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_6 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) .int) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_int'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genIntConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx (factoryOps F) tvars bctx n .int) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) .int),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .int)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .int)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .int).length > 0 then pickBVar bctx .int hv
           else genIntConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .int).length > 0 then pickFVar fctx .int hf
           else genIntConst),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .int).length > 0 then pickOp (factoryOps F) .int ho
           else genIntConst),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) .int).length > 0
           then genIndir (factoryOps F) .int (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n .int),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx .int
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n .int)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genIntConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩ <;> exact .const
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickBVar_mem_opsConsistentR F bctx .int h
      · exact .const
      · exact .const
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickFVar_mem_opsConsistentR F fctx .int h
      · exact .const
      · exact .const
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickOp_mem_opsConsistentR F .int h
      · exact .const
      · exact .const
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_10 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) .string) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_string'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genStrConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx (factoryOps F) tvars bctx n .string) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) .string),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .string)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .string)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .string).length > 0 then pickBVar bctx .string hv
           else genStrConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .string).length > 0 then pickFVar fctx .string hf
           else genStrConst),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .string).length > 0 then pickOp (factoryOps F) .string ho
           else genStrConst),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) .string).length > 0
           then genIndir (factoryOps F) .string (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n .string),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx .string
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n .string)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genStrConst, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨s, _, rfl⟩ := he; exact .const
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickBVar_mem_opsConsistentR F bctx .string h
      · exact .const
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickFVar_mem_opsConsistentR F fctx .string h
      · exact .const
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickOp_mem_opsConsistentR F .string h
      · exact .const
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_12 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) .real) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_real'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genRealConst (G := SetGen.Set)),
         (1, fun () => genApp (genAppArgTy fctx (factoryOps F) tvars bctx n .real) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) .real),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .real)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .real)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .real).length > 0 then pickBVar bctx .real hv
           else genRealConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .real).length > 0 then pickFVar fctx .real hf
           else genRealConst),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .real).length > 0 then pickOp (factoryOps F) .real ho
           else genRealConst),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) .real).length > 0
           then genIndir (factoryOps F) .real (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n .real),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx .real
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n .real)) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genRealConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨r, _, rfl⟩ := he; exact .const
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · exact pickBVar_mem_opsConsistentR F bctx .real h
      · exact .const
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · exact pickFVar_mem_opsConsistentR F fctx .real h
      · exact .const
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨r, _, rfl⟩⟩
      · exact pickOp_mem_opsConsistentR F .real h
      · exact .const
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_14 m n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (m + 1) (.bitvec n)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genBitvecConst (G := SetGen.Set) n),
         (1, fun () => genApp (genAppArgTy fctx (factoryOps F) tvars bctx m (.bitvec n)) (genLExprBase fctx (factoryOps F) pctx tvars bctx m) (.bitvec n)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx m .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx m (.bitvec n))
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx m (.bitvec n))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.bitvec n)).length > 0 then pickBVar bctx (.bitvec n) hv
           else genBitvecConst n),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.bitvec n)).length > 0 then pickFVar fctx (.bitvec n) hf
           else genBitvecConst n),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) (.bitvec n)).length > 0 then pickOp (factoryOps F) (.bitvec n) ho
           else genBitvecConst n),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) (.bitvec n)).length > 0
           then genIndir (factoryOps F) (.bitvec n) (genLExprBase fctx (factoryOps F) pctx tvars bctx m) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx m (.bitvec n)),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx (.bitvec n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx m)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx m (.bitvec n))) ]
      ) (by show 0 < 1+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genBitvecConst, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨k, _, rfl⟩ := he; exact .const
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickBVar_mem_opsConsistentR F bctx (.bitvec n) h
      · exact .const
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickFVar_mem_opsConsistentR F fctx (.bitvec n) h
      · exact .const
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickOp_mem_opsConsistentR F (.bitvec n) h
      · exact .const
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … m`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx m _ a ha) e he
  case h_2 n τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) (.arrow τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_arrow'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (4, fun () => genAbs (G := SetGen.Set) (genLExprBase fctx (factoryOps F) pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (1, fun () => genApp (genAppArgTy fctx (factoryOps F) tvars bctx n (.arrow τ₁ τ₂)) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) (.arrow τ₁ τ₂)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.arrow τ₁ τ₂))
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.arrow τ₁ τ₂))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.arrow τ₁ τ₂)).length > 0 then pickBVar bctx (.arrow τ₁ τ₂) hv
           else genAbs (genLExprBase fctx (factoryOps F) pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0 then pickFVar fctx (.arrow τ₁ τ₂) hf
           else genAbs (genLExprBase fctx (factoryOps F) pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) (.arrow τ₁ τ₂)).length > 0 then pickOp (factoryOps F) (.arrow τ₁ τ₂) ho
           else genAbs (genLExprBase fctx (factoryOps F) pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) (.arrow τ₁ τ₂)).length > 0
           then genIndir (factoryOps F) (.arrow τ₁ τ₂) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n (.arrow τ₁ τ₂)),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx (.arrow τ₁ τ₂)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.arrow τ₁ τ₂))) ]
      ) (by show 0 < 4+1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genAbs, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨body, hbody, rfl⟩ := he
      exact .abs (genLExprBase_opsConsistentR F fctx pctx tvars hPoly (τ₁ :: bctx) n _ _ hbody)
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickBVar_mem_opsConsistentR F bctx (.arrow τ₁ τ₂) h
      · exact .abs (genLExprBase_opsConsistentR F fctx pctx tvars hPoly (τ₁ :: bctx) n _ _ hbody)
    · rcases he with ⟨hf, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickFVar_mem_opsConsistentR F fctx (.arrow τ₁ τ₂) h
      · exact .abs (genLExprBase_opsConsistentR F fctx pctx tvars hPoly (τ₁ :: bctx) n _ _ hbody)
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickOp_mem_opsConsistentR F (.arrow τ₁ τ₂) h
      · exact .abs (genLExprBase_opsConsistentR F fctx pctx tvars hPoly (τ₁ :: bctx) n _ _ hbody)
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_7 name =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 (.ftvar name)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · exact pickBVar_mem_opsConsistentR F bctx (.ftvar name) h
    · exact pickFVar_mem_opsConsistentR F fctx (.ftvar name) h
    · exact pickOp_mem_opsConsistentR F (.ftvar name) h
    · exact absurd h (by simp)
    · exact pickFVar_mem_opsConsistentR F fctx (.ftvar name) h
    · exact pickBVar_mem_opsConsistentR F bctx (.ftvar name) h
    · exact pickOp_mem_opsConsistentR F (.ftvar name) h
    · exact absurd h (by simp)
    · exact pickOp_mem_opsConsistentR F (.ftvar name) h
    · exact pickBVar_mem_opsConsistentR F bctx (.ftvar name) h
    · exact pickFVar_mem_opsConsistentR F fctx (.ftvar name) h
    · exact absurd h (by simp)
  case h_8 n name =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) (.ftvar name)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx (factoryOps F) tvars bctx n (.ftvar name)) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) (.ftvar name)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.ftvar name))
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.ftvar name))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else if hf : (fvarsOfType fctx (.ftvar name)).length > 0 then pickFVar fctx (.ftvar name) hf
           else if ho : (opsOfType (factoryOps F) (.ftvar name)).length > 0 then pickOp (factoryOps F) (.ftvar name) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.ftvar name)).length > 0 then pickFVar fctx (.ftvar name) hf
           else if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) (.ftvar name)).length > 0 then pickOp (factoryOps F) (.ftvar name) ho
           else if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then pickBVar bctx (.ftvar name) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) (.ftvar name)).length > 0
           then genIndir (factoryOps F) (.ftvar name) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n (.ftvar name)),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx (.ftvar name)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.ftvar name))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · exact pickBVar_mem_opsConsistentR F bctx (.ftvar name) h
      · exact pickFVar_mem_opsConsistentR F fctx (.ftvar name) h
      · exact pickOp_mem_opsConsistentR F (.ftvar name) h
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickFVar_mem_opsConsistentR F fctx (.ftvar name) h
      · exact pickBVar_mem_opsConsistentR F bctx (.ftvar name) h
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickOp_mem_opsConsistentR F (.ftvar name) h
      · exact pickBVar_mem_opsConsistentR F bctx (.ftvar name) h
      · exact absurd h (by simp)
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_15 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 .regex) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · exact pickBVar_mem_opsConsistentR F bctx .regex h
    · exact pickFVar_mem_opsConsistentR F fctx .regex h
    · exact pickOp_mem_opsConsistentR F .regex h
    · exact absurd h (by simp)
    · exact pickFVar_mem_opsConsistentR F fctx .regex h
    · exact pickBVar_mem_opsConsistentR F bctx .regex h
    · exact pickOp_mem_opsConsistentR F .regex h
    · exact absurd h (by simp)
    · exact pickOp_mem_opsConsistentR F .regex h
    · exact pickBVar_mem_opsConsistentR F bctx .regex h
    · exact pickFVar_mem_opsConsistentR F fctx .regex h
    · exact absurd h (by simp)
  case h_16 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) .regex) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx (factoryOps F) tvars bctx n .regex) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) .regex),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .regex)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n .regex)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else if hf : (fvarsOfType fctx .regex).length > 0 then pickFVar fctx .regex hf
           else if ho : (opsOfType (factoryOps F) .regex).length > 0 then pickOp (factoryOps F) .regex ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx .regex).length > 0 then pickFVar fctx .regex hf
           else if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else default),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .regex).length > 0 then pickOp (factoryOps F) .regex ho
           else if hv : (bvarsOfType bctx .regex).length > 0 then pickBVar bctx .regex hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) .regex).length > 0
           then genIndir (factoryOps F) .regex (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n .regex),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx .regex
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n .regex)) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · exact pickBVar_mem_opsConsistentR F bctx .regex h
      · exact pickFVar_mem_opsConsistentR F fctx .regex h
      · exact pickOp_mem_opsConsistentR F .regex h
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickFVar_mem_opsConsistentR F fctx .regex h
      · exact pickBVar_mem_opsConsistentR F bctx .regex h
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickOp_mem_opsConsistentR F .regex h
      · exact pickBVar_mem_opsConsistentR F bctx .regex h
      · exact absurd h (by simp)
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_17 τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 (.map τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · exact pickBVar_mem_opsConsistentR F bctx (.map τ₁ τ₂) h
    · exact pickFVar_mem_opsConsistentR F fctx (.map τ₁ τ₂) h
    · exact pickOp_mem_opsConsistentR F (.map τ₁ τ₂) h
    · exact absurd h (by simp)
    · exact pickFVar_mem_opsConsistentR F fctx (.map τ₁ τ₂) h
    · exact pickBVar_mem_opsConsistentR F bctx (.map τ₁ τ₂) h
    · exact pickOp_mem_opsConsistentR F (.map τ₁ τ₂) h
    · exact absurd h (by simp)
    · exact pickOp_mem_opsConsistentR F (.map τ₁ τ₂) h
    · exact pickBVar_mem_opsConsistentR F bctx (.map τ₁ τ₂) h
    · exact pickFVar_mem_opsConsistentR F fctx (.map τ₁ τ₂) h
    · exact absurd h (by simp)
  case h_18 n τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) (.map τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx (factoryOps F) tvars bctx n (.map τ₁ τ₂)) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) (.map τ₁ τ₂)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.map τ₁ τ₂))
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.map τ₁ τ₂))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0 then pickFVar fctx (.map τ₁ τ₂) hf
           else if ho : (opsOfType (factoryOps F) (.map τ₁ τ₂)).length > 0 then pickOp (factoryOps F) (.map τ₁ τ₂) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0 then pickFVar fctx (.map τ₁ τ₂) hf
           else if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) (.map τ₁ τ₂)).length > 0 then pickOp (factoryOps F) (.map τ₁ τ₂) ho
           else if hv : (bvarsOfType bctx (.map τ₁ τ₂)).length > 0 then pickBVar bctx (.map τ₁ τ₂) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) (.map τ₁ τ₂)).length > 0
           then genIndir (factoryOps F) (.map τ₁ τ₂) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n (.map τ₁ τ₂)),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx (.map τ₁ τ₂)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.map τ₁ τ₂))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · exact pickBVar_mem_opsConsistentR F bctx (.map τ₁ τ₂) h
      · exact pickFVar_mem_opsConsistentR F fctx (.map τ₁ τ₂) h
      · exact pickOp_mem_opsConsistentR F (.map τ₁ τ₂) h
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickFVar_mem_opsConsistentR F fctx (.map τ₁ τ₂) h
      · exact pickBVar_mem_opsConsistentR F bctx (.map τ₁ τ₂) h
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickOp_mem_opsConsistentR F (.map τ₁ τ₂) h
      · exact pickBVar_mem_opsConsistentR F bctx (.map τ₁ τ₂) h
      · exact absurd h (by simp)
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_19 τ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 (.seq τ)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · exact pickBVar_mem_opsConsistentR F bctx (.seq τ) h
    · exact pickFVar_mem_opsConsistentR F fctx (.seq τ) h
    · exact pickOp_mem_opsConsistentR F (.seq τ) h
    · exact absurd h (by simp)
    · exact pickFVar_mem_opsConsistentR F fctx (.seq τ) h
    · exact pickBVar_mem_opsConsistentR F bctx (.seq τ) h
    · exact pickOp_mem_opsConsistentR F (.seq τ) h
    · exact absurd h (by simp)
    · exact pickOp_mem_opsConsistentR F (.seq τ) h
    · exact pickBVar_mem_opsConsistentR F bctx (.seq τ) h
    · exact pickFVar_mem_opsConsistentR F fctx (.seq τ) h
    · exact absurd h (by simp)
  case h_20 n τ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx (n + 1) (.seq τ)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genApp (G := SetGen.Set) (genAppArgTy fctx (factoryOps F) tvars bctx n (.seq τ)) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) (.seq τ)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) pctx tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.seq τ))
                              (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.seq τ))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.seq τ)).length > 0 then pickBVar bctx (.seq τ) hv
           else if hf : (fvarsOfType fctx (.seq τ)).length > 0 then pickFVar fctx (.seq τ) hf
           else if ho : (opsOfType (factoryOps F) (.seq τ)).length > 0 then pickOp (factoryOps F) (.seq τ) ho
           else default),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.seq τ)).length > 0 then pickFVar fctx (.seq τ) hf
           else if hv : (bvarsOfType bctx (.seq τ)).length > 0 then pickBVar bctx (.seq τ) hv
           else default),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) (.seq τ)).length > 0 then pickOp (factoryOps F) (.seq τ) ho
           else if hv : (bvarsOfType bctx (.seq τ)).length > 0 then pickBVar bctx (.seq τ) hv
           else default),
         (4, fun () =>
           if hi : (findOpsInCtx (factoryOps F) (.seq τ)).length > 0
           then genIndir (factoryOps F) (.seq τ) (genLExprBase fctx (factoryOps F) pctx tvars bctx n) hi
           else genLExprBase fctx (factoryOps F) pctx tvars bctx n (.seq τ)),
         (4, fun () =>
           genIndirPolyCore fctx (factoryOps F) pctx bctx (.seq τ)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n)
             (genLExprBase fctx (factoryOps F) pctx tvars bctx n (.seq τ))) ]
      ) (by show 0 < 1+2+2+2+2+4+4; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact .app (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hfn) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ harg)
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact .ite (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ hc) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ ht) (genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ _ he')
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · exact pickBVar_mem_opsConsistentR F bctx (.seq τ) h
      · exact pickFVar_mem_opsConsistentR F fctx (.seq τ) h
      · exact pickOp_mem_opsConsistentR F (.seq τ) h
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickFVar_mem_opsConsistentR F fctx (.seq τ) h
      · exact pickBVar_mem_opsConsistentR F bctx (.seq τ) h
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickOp_mem_opsConsistentR F (.seq τ) h
      · exact pickBVar_mem_opsConsistentR F bctx (.seq τ) h
      · exact absurd h (by simp)
    -- Indir / IndirPoly branches. The op node's annotation is a genuine
    -- instance of the operator's scheme (`indir_op_opsConsistentR` monomorphically,
    -- `hPoly` polymorphically) and the arguments come from `genLExprBase … n`,
    -- whose consistency is this theorem's own recursive call.
    · try simp only [mem_support_iff, SetGen.mem_dite] at he
      rcases he with ⟨_, he⟩ | ⟨_, he⟩
      · exact genIndir_opsConsistentR F _ _
          (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha) _ e he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ e he
    · try simp only [mem_support_iff] at he
      exact genIndirPolyCore_opsConsistentR F fctx pctx bctx _ _ (hPoly bctx _ 3) _ _
        (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n σ a ha)
        (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx n _ a ha) e he
  case h_21 =>
    -- Other type constructors (datatypes, abstract types, aliases). The branch is
    -- the three context leaves. A `pickOp` leaf's annotation is the operator's
    -- *generic* factory type, so it is the identity instance `OpsConsistentR.op_in`
    -- accepts; bvar/fvar leaves carry no `.op` node at all.
    --
    -- Every *named* case also carries Indir/IndirPoly branches, whose
    -- sub-cases need `hPoly` and the recursive hypothesis. This case needs neither:
    -- it is leaf-only by construction (see `genLExprBase`'s docstring there), which
    -- is why the discharge is three `pick*` lemmas and no induction.
    simp only [mem_oneOf_iff, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩))
    all_goals first
      | exact pickBVar_mem_opsConsistentR F bctx _ h
      | exact pickFVar_mem_opsConsistentR F fctx _ h
      | exact pickOp_mem_opsConsistentR F _ h
      | exact absurd h (by simp)
  termination_by depth
  decreasing_by all_goals simp_wf; omega

/-- Every argument produced by `mapM (genLExprBase fctx (factoryOps F) …)` is
    `Lambda.OpsConsistentR`. Specialization of `mapM_genArg_opsConsistentR`. -/
theorem mapM_genLExprBase_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m)
    (bctx : BVarCtx) (depth : Nat) (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set)
      (genLExprBase fctx (factoryOps F) pctx tvars bctx depth) argTys)) :
    ∀ a ∈ args, Lambda.OpsConsistentR F a :=
  mapM_genArg_opsConsistentR F _
    (fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx depth σ a ha) argTys args hargs


-- ── genIndirPoly consistency ─────────────────────────────────────────

set_option maxHeartbeats 800000 in
/-- Every expression in `genIndirPoly`'s support is `OpsConsistentR`, GIVEN the
    polymorphic-annotation assumption `PolyOpsConsistentR` (which is itself proven,
    from `PCtxWF`, by `PolyOpsConsistentR_of_PCtxWF`). Either a polymorphic operator
    was applied (op node consistent by `hPoly`, args by
    `mapM_genLExprBase_opsConsistentR`), or the generator fell back to
    `genLExprBase`. -/
theorem genIndirPoly_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat)
    -- All-contexts/all-types form: `genLExprBase` now fires IndirPoly at every
    -- subterm position, so the fallback needs the assumption at those types
    -- too, not just at `τ`. `PolyOpsConsistentR_of_PCtxWF` supplies all of them
    -- from one `PCtxWF`.
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → Lambda.OpsConsistentR F a)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ
        maxNumArgs genArg)) :
    Lambda.OpsConsistentR F e := by
  -- `genIndirPoly` is a thin wrapper around `genIndirPolyCore`, so the
  -- generator-parametric result applies: `genArg` consistency is `hArg` and the
  -- fallback is `genLExprBase … depth`.
  exact genIndirPolyCore_opsConsistentR F fctx pctx bctx τ maxNumArgs (hPoly bctx τ maxNumArgs)
    genArg _ hArg
    (fun a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx depth τ a ha) e he

-- ── Top-level: genLExpr consistency ──────────────────────────────────

set_option maxHeartbeats 800000 in
/-- **Main result (general polymorphic context).** Every expression in the
    support of `genLExpr` on a factory operator context `factoryOps F` satisfies
    Strata's declarative `OpsConsistentR F`. Combined with `genLExpr_sound` this
    gives soundness w.r.t. both `HasTypeA` and `OpsConsistentR`.

    Takes the polymorphic-annotation assumption `PolyOpsConsistentR` as a
    hypothesis for generality; it is discharged from `PCtxWF` by
    `PolyOpsConsistentR_of_PCtxWF`, giving the unconditional
    `genLExpr_opsConsistentR_of_PCtxWF`. For the common `pctx = []` case use
    `genLExpr_opsConsistentR_nil`. -/
theorem genLExpr_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    -- Quantified over *all* target types, not just `τ`: since factory applications
    -- now nest, the arguments of an application at `τ` are themselves
    -- generated at other types `σ`, and each needs its own polymorphic-annotation
    -- assumption. `PolyOpsConsistentR_of_PCtxWF` provides this for every type from a
    -- single `PCtxWF`, so the `PCtxWF`/factory-derived corollaries below are
    -- unaffected.
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e := by
  -- Induction on the depth index, as in `genLExpr_sound`: the Indir/IndirPoly
  -- arguments are drawn from `genLExpr … n`, so op-consistency of the argument
  -- generator at the smaller index is the induction hypothesis. Note `hPoly` is
  -- depth-independent, so it survives the generalization unchanged.
  induction depth generalizing τ e with
  | zero =>
    have hArg : ∀ σ a, a ∈ SetGen.support
        (genLExprBase (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx 0 σ) →
        Lambda.OpsConsistentR F a :=
      fun σ a ha => genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx 0 σ a ha
    unfold genLExpr at he
    simp only [mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨hpos, he⟩ | ⟨_, he⟩
    · rw [← mem_support_iff, mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx 0 τ e he
      rw [mem_support_pick_iff] at he
      rcases he with he | he
      · unfold genIndir at he
        simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
        obtain ⟨⟨name, argTys⟩, hentry_mem, args, hargs, rfl⟩ := he
        rw [← mem_support_iff, mem_support_elements_iff] at hentry_mem
        apply mkApps_opsConsistentR
        · exact indir_op_opsConsistentR F τ _ _ hentry_mem
        · exact mapM_genArg_opsConsistentR F _ hArg _ args hargs
      · exact genIndirPoly_opsConsistentR F fctx pctx tvars bctx 0 τ _ hPoly _ hArg e he
    · rw [pick_mem_iff] at he
      rcases he with he | he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx 0 τ e he
      · exact genIndirPoly_opsConsistentR F fctx pctx tvars bctx 0 τ _ hPoly _ hArg e he
  | succ n ih =>
    have hArg : ∀ σ a, a ∈ SetGen.support
        (genLExpr (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx n σ) →
        Lambda.OpsConsistentR F a :=
      fun σ a ha => ih σ a ha
    unfold genLExpr at he
    simp only [mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨hpos, he⟩ | ⟨_, he⟩
    · rw [← mem_support_iff, mem_support_frequency_iff] at he
      obtain ⟨_, g, hg, _, he⟩ := he
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx (n + 1) τ e he
      rw [mem_support_pick_iff] at he
      rcases he with he | he
      · unfold genIndir at he
        simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
        obtain ⟨⟨name, argTys⟩, hentry_mem, args, hargs, rfl⟩ := he
        rw [← mem_support_iff, mem_support_elements_iff] at hentry_mem
        apply mkApps_opsConsistentR
        · exact indir_op_opsConsistentR F τ _ _ hentry_mem
        · exact mapM_genArg_opsConsistentR F _ hArg _ args hargs
      · exact genIndirPoly_opsConsistentR F fctx pctx tvars bctx (n + 1) τ _ hPoly _ hArg e he
    · rw [pick_mem_iff] at he
      rcases he with he | he
      · exact genLExprBase_opsConsistentR F fctx pctx tvars hPoly bctx (n + 1) τ e he
      · exact genIndirPoly_opsConsistentR F fctx pctx tvars bctx (n + 1) τ _ hPoly _ hArg e he

-- Note: `genLExpr_opsConsistentR` above proves `Lambda.OpsConsistentR F e`
-- directly — Strata's declarative predicate, which is `public` in `Assumptions.lean`.
-- The proof is stated against `OpsConsistentR` throughout and closed by its
-- constructors; there is no operational `OpsConsistent` detour or `faithful` bridge.

/-- The `Factory`-wrapper generator `genLExprWithFactory` produces
    `OpsConsistentR` terms, given the polymorphic-annotation assumption
    `PolyOpsConsistentR`. -/
theorem genLExprWithFactory_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (pctx : PolyOpCtx)
    (hPoly : ∀ bc σ m, PolyOpsConsistentR F pctx bc fctx σ m) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExprWithFactory (G := SetGen.Set) fctx F tvars bctx depth τ pctx)) :
    Lambda.OpsConsistentR F e :=
  genLExpr_opsConsistentR F fctx pctx tvars bctx depth τ hPoly e he

/-- **Main result, parameterized by `PCtxWF` (no `PolyOpsConsistentR` assumption).**
    A well-formed polymorphic context (`PCtxWF F pctx` — every `pctx` entry is a
    factory function's generic scheme) is enough: `PolyOpsConsistentR` is *derived*
    via `PolyOpsConsistentR_of_PCtxWF`. So `genLExpr` on a factory produces
    `OpsConsistentR` (equivalently `OpsConsistentR`) terms for *any* polymorphic
    context that matches the factory. -/
theorem genLExpr_opsConsistentR_of_PCtxWF (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hPctx : PCtxWF F pctx) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e :=
  genLExpr_opsConsistentR F fctx pctx tvars bctx depth τ
    (fun bc σ m => PolyOpsConsistentR_of_PCtxWF F pctx bc fctx σ m hPctx) e he

/-- **Main result, factory-derived polymorphic context (no hypothesis).** When the
    polymorphic operator context is extracted directly from the factory via
    `factoryPolyOps F`, `PCtxWF` holds *by construction* (`PCtxWF_factoryPolyOps`),
    so `genLExpr` produces `OpsConsistentR` terms unconditionally — even with
    polymorphic operators enabled. This is the polymorphic analogue of
    `genLExpr_opsConsistentR_nil`: no `pctx = []` restriction and no side
    condition to discharge at the call site. -/
theorem genLExpr_opsConsistentR_factory (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) (factoryPolyOps F) tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e :=
  genLExpr_opsConsistentR_of_PCtxWF F fctx (factoryPolyOps F) tvars bctx depth τ
    (PCtxWF_factoryPolyOps F) e he

/-- The `Factory`-wrapper generator `genLExprWithFactory`, run with the factory's
    own polymorphic context `factoryPolyOps F`, produces `OpsConsistentR` terms
    unconditionally — no `PolyOpsConsistentR`/`PCtxWF` hypothesis needed. -/
theorem genLExprWithFactory_opsConsistentR_factory (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExprWithFactory (G := SetGen.Set) fctx F tvars bctx depth τ (factoryPolyOps F))) :
    Lambda.OpsConsistentR F e :=
  genLExpr_opsConsistentR_factory F fctx tvars bctx depth τ e he

-- ── Sorry-free corollary for the empty polymorphic context ───────────
-- The factory wrappers now default to `pctx := factoryPolyOps F` (covered
-- unconditionally by `genLExpr_opsConsistentR_factory`). The `pctx = []` results
-- below still apply to callers that *explicitly* pass an empty polymorphic
-- context: `findPolymorphicOps [] _ _ = []`, so `genIndirPoly` never emits a
-- polymorphic op and the polymorphic-annotation obligation is vacuous — giving a
-- result that does not even need `PCtxWF`.

@[simp] theorem findPolymorphicOps_nil (τ : LMonoTy) (g s : List LMonoTy) (m : Nat) :
    findPolymorphicOps [] τ g s m = [] := by unfold findPolymorphicOps; rfl

/-- `genIndirPoly` with an empty polymorphic context always falls back to
    `genLExprBase`, hence is `OpsConsistentR`. -/
theorem genIndirPoly_opsConsistentR_nil (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat) (genArg : LMonoTy → SetGen.Set LExpr')
    -- Needed because `genIndirPolyCore`'s *arguments* also come from `genArg`,
    -- and with `pctx = []` only the fallback fires, but the lemma is stated
    -- uniformly over both branches.
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → Lambda.OpsConsistentR F a)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) fctx (factoryOps F) [] tvars bctx depth τ
        maxNumArgs genArg)) :
    Lambda.OpsConsistentR F e := by
  -- With `pctx = []` the polymorphic-annotation assumption is vacuous:
  -- `findPolymorphicOps [] …` is empty, so no candidate membership can be produced
  -- and only `genIndirPolyCore`'s fallback branch is reachable.
  exact genIndirPolyCore_opsConsistentR F fctx [] bctx τ maxNumArgs
    (fun _ _ _ hmem => by rw [findPolymorphicOps_nil] at hmem; simp at hmem)
    genArg _ hArg
    (fun a ha => genLExprBase_opsConsistentR F fctx [] tvars
      (fun _ _ _ _ _ _ hmem => by
        rw [findPolymorphicOps_nil] at hmem; simp at hmem)
      bctx depth τ a ha) e he

set_option maxHeartbeats 800000 in
/-- **Main result, empty polymorphic context (fully `sorry`-free).** Every
    expression produced by `genLExpr` with `pctx = []` on a factory operator
    context satisfies `OpsConsistentR F` (equivalently Strata's
    `OpsConsistentR`; see the bridge note above). This covers the closed-term
    generators. -/
theorem genLExpr_opsConsistentR_nil (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) [] tvars bctx depth τ)) :
    Lambda.OpsConsistentR F e :=
  -- With `pctx = []` the polymorphic-annotation hypothesis is vacuous: there are no
  -- `pctx` entries, so `findPolymorphicOps [] …` is empty and no `hentry_mem` can be
  -- produced. Derive from the general theorem rather than repeating its depth
  -- induction (which is what this proof used to do by hand).
  genLExpr_opsConsistentR F fctx [] tvars bctx depth τ
    (fun _ _ _ _ _ _ hmem => by
      rw [findPolymorphicOps_nil] at hmem; simp at hmem)
    e he
