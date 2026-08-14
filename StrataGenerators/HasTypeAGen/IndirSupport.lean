import StrataGenerators.SetGen
import StrataGenerators.HasTypeAGen.Core
import Strata.DL.Lambda.LTyUnify

/-!
# Generator-parametric support lemmas for the Indir / IndirPoly rules

`genLExprBase` itself carries the Indir/IndirPoly rules in its
per-type `frequency` lists. That creates a proof-order problem: the four
"forward" results about `genLExprBase` —

  * `genLExprBase_sound`            (`HasTypeAGen.lean`)
  * `genLExprBase_termDepth_bound`  (`HasTypeAGen.lean`)
  * `genLExprBase_fvars_subset`     (`HasTypeAGen.lean`)
  * `genLExprBase_opsConsistentR`   (`HasTypeAGenOpsConsistent.lean`)

— each now need a corresponding fact about `genIndir` / `genIndirPolyCore`, but
the existing `genIndir_sound` / `genIndirPoly_*` lemmas are stated *downstream* of
them (and, in the `opsConsistentR` case, in a different file entirely).

This module breaks the cycle the same way `Core.lean` breaks it for the
generators themselves: every lemma here is **parametric in the argument generator
`genArg` and the fallback**, taking the property it needs as a hypothesis
(`hArg`, `hFallback`) rather than referring to `genLExprBase`. Each
`genLExprBase_*` proof then discharges `hArg`/`hFallback` with its *own* recursive
call at the smaller depth index `n`, which is exactly the induction hypothesis it
already has.

Consequently nothing in this file mentions `genLExprBase`, so it can sit before
both proof files, and each lemma is proved once instead of once per type × depth
case.
-/

open Lambda RandomChoice SetGen

namespace StrataGenerators.IndirSupport

-- ── Shared spine plumbing ───────────────────────────────────────────

/-- Membership in `List.mapM f l` on `SetGen.Set`: `args` is in the support iff
    each element is pointwise in the support of `f` at the corresponding input.

    (Duplicated from `HasTypeAGen.lean`'s `private mem_mapM_iff` so this module
    stays upstream of it; the two are the same statement.) -/
theorem mem_mapM_iff' (f : LMonoTy → SetGen.Set LExpr')
    (argTys : List LMonoTy) (args : List LExpr') :
    args ∈ (List.mapM (m := SetGen.Set) f argTys) ↔
    List.Forall₂ (fun arg σ => arg ∈ f σ) args argTys := by
  induction argTys generalizing args with
  | nil =>
    simp only [List.mapM_nil, SetGen.Set.mem_pure]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | cons σ rest ih =>
    simp only [List.mapM_cons, SetGen.Set.mem_bind, SetGen.Set.mem_pure]
    constructor
    · rintro ⟨x, hx, tl, htl, rfl⟩
      exact .cons hx ((ih _).mp htl)
    · intro h
      match args, h with
      | _ :: _, .cons harg htail =>
        exact ⟨_, harg, _, (ih _).mpr htail, rfl⟩

/-- Pointwise version of `mapM_forall` for a `genArg` whose guarantee is
    *conditional on the argument type*: if `genArg σ` only produces `P`-terms
    whenever `Q σ` holds, and every type in `argTys` satisfies `Q`, then every
    element of the produced list satisfies `P`.

    Needed because `genLExprBase_termDepth_bound` may only be invoked at a
    `SimpleType`, so the per-argument bound is conditional on the argument type
    being simple (`IndirArgTysSimple`). -/
theorem forall₂_forall_of_cond {P : LExpr' → Prop} {Q : LMonoTy → Prop}
    {genArg : LMonoTy → SetGen.Set LExpr'}
    (hArg : ∀ σ, Q σ → ∀ a, a ∈ SetGen.support (genArg σ) → P a)
    {args : List LExpr'} {argTys : List LMonoTy}
    (hQ : ∀ σ ∈ argTys, Q σ)
    (h : List.Forall₂ (fun arg σ => arg ∈ SetGen.support (genArg σ)) args argTys) :
    ∀ a ∈ args, P a := by
  induction h with
  | nil => intro a ha; simp at ha
  | @cons x σ xs σs hx hrest ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hArg σ (hQ σ (by simp)) a hx
    · exact ih (fun σ' hσ' => hQ σ' (by simp [hσ'])) a ha'

/-- Every element of a list produced by `mapM genArg` satisfies `P`, provided
    everything `genArg` can produce does. The workhorse behind the per-argument
    obligations of every lemma below. -/
theorem mapM_forall {P : LExpr' → Prop}
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → P a)
    (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set) genArg argTys)) :
    ∀ a ∈ args, P a := by
  induction argTys generalizing args with
  | nil =>
    simp only [List.mapM_nil, SetGen.Set.mem_pure] at hargs
    subst hargs; intro a ha; simp at ha
  | cons σ rest ih =>
    simp only [List.mapM_cons, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at hargs
    obtain ⟨x, hx, tl, htl, rfl⟩ := hargs
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hrest
    · exact hArg σ a hx
    · exact ih tl htl a hrest

/-- The **shape** of everything the Indir rule can emit: either an application
    spine `mkApps (.op … ) args` whose arguments all come from `genArg`, or
    (`genIndirPolyCore` only) the caller's fallback.

    Factoring the two rules' support down to this single disjunction is what lets
    the four `genLExprBase_*` proofs share one case analysis: each of them cares
    only about "a spine over an op node, with `genArg` arguments" versus "the
    fallback", never about `findOpsInCtx`/`findPolymorphicOps` internals. -/
theorem genIndir_shape (octx : OpCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (h : (findOpsInCtx octx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (genIndir (G := SetGen.Set) octx τ genArg h)) :
    ∃ (name : String) (argTys : List LMonoTy) (args : List LExpr'),
      (name, argTys) ∈ findOpsInCtx octx τ ∧
      List.Forall₂ (fun arg σ => arg ∈ SetGen.support (genArg σ)) args argTys ∧
      e = mkApps (.op () ⟨name, ()⟩
        (some (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) args := by
  unfold genIndir at he
  simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
  obtain ⟨entry, hentry_mem, args, hargs, rfl⟩ := he
  rw [← mem_support_iff, mem_support_elements_iff] at hentry_mem
  exact ⟨entry.1, entry.2, args, hentry_mem, (mem_mapM_iff' genArg entry.2 args).mp hargs, rfl⟩

/-- The shape of everything `genIndirPolyCore` can emit: a spine over a
    `findPolymorphicOps` candidate, or the caller's `fallback`. -/
theorem genIndirPolyCore_shape (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr') (fallback : SetGen.Set LExpr')
    (maxNumArgs : Nat) (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPolyCore (G := SetGen.Set) fctx octx pctx bctx τ genArg fallback maxNumArgs)) :
    (∃ (sampledTys : List LMonoTy) (name : String)
       (concreteArgTys : List LMonoTy) (args : List LExpr'),
       (name, concreteArgTys) ∈ findPolymorphicOps pctx τ
         (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs ∧
       List.Forall₂ (fun arg σ => arg ∈ SetGen.support (genArg σ)) args concreteArgTys ∧
       e = mkApps (.op () ⟨name, ()⟩
         (some (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) args)
    ∨ e ∈ SetGen.support fallback := by
  unfold genIndirPolyCore at he
  simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
             SetGen.mem_dite] at he
  obtain ⟨sampledTys, _, he⟩ := he
  rcases he with ⟨hpos, he⟩ | ⟨_, he⟩
  · obtain ⟨entry, hentry_mem, args, hargs, rfl⟩ := he
    rw [← mem_support_iff, mem_support_elements_iff] at hentry_mem
    exact Or.inl ⟨sampledTys, entry.1, entry.2, args, hentry_mem,
      (mem_mapM_iff' genArg entry.2 args).mp hargs, rfl⟩
  · exact Or.inr he

-- ── Well-typedness ──────────────────────────────────────────────────

/-- `mkApps` preserves typing via the iterated `app` rule. (Same statement as
    `HasTypeAGen.lean`'s `mkApps_hasType`, restated here to stay upstream.) -/
theorem mkApps_hasType' (bctx : BVarCtx) (base : LExpr') (args : List LExpr')
    (argTys : List LMonoTy) (τ : LMonoTy)
    (hbase : HasTypeA' bctx base (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))
    (hargs : List.Forall₂ (HasTypeA' bctx) args argTys) :
    HasTypeA' bctx (mkApps base args) τ := by
  induction hargs generalizing base with
  | nil => exact hbase
  | cons harg _ ih => exact ih _ (LExpr.HasTypeA.app hbase harg)

/-- Pointwise-membership implies pointwise-typing, given `hArg`. -/
private theorem forall₂_typed {bctx : BVarCtx}
    {genArg : LMonoTy → SetGen.Set LExpr'}
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → HasTypeA' bctx a σ)
    {args : List LExpr'} {argTys : List LMonoTy}
    (h : List.Forall₂ (fun arg σ => arg ∈ SetGen.support (genArg σ)) args argTys) :
    List.Forall₂ (HasTypeA' bctx) args argTys := by
  induction h with
  | nil => exact .nil
  | @cons a ty _ _ hmem _ ih => exact .cons (hArg ty a hmem) ih

/-- Soundness of the monomorphic Indir rule, parametric in `genArg`. -/
theorem genIndir_hasType (octx : OpCtx) (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → HasTypeA' bctx a σ)
    (h : (findOpsInCtx octx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (genIndir (G := SetGen.Set) octx τ genArg h)) :
    HasTypeA' bctx e τ := by
  obtain ⟨name, argTys, args, _, hargs, rfl⟩ := genIndir_shape octx τ genArg h e he
  exact mkApps_hasType' bctx _ args argTys τ .op (forall₂_typed hArg hargs)

/-- Soundness of the polymorphic IndirPoly rule, parametric in `genArg` and the
    fallback. The op node types at its annotation, and the annotation is by
    construction `concreteArgTys.foldr arrow τ`, so `mkApps` folds back to `τ`. -/
theorem genIndirPolyCore_hasType (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr') (fallback : SetGen.Set LExpr')
    (maxNumArgs : Nat)
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → HasTypeA' bctx a σ)
    (hFallback : ∀ a, a ∈ SetGen.support fallback → HasTypeA' bctx a τ)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPolyCore (G := SetGen.Set) fctx octx pctx bctx τ genArg fallback maxNumArgs)) :
    HasTypeA' bctx e τ := by
  rcases genIndirPolyCore_shape fctx octx pctx bctx τ genArg fallback maxNumArgs e he with
    ⟨_, name, concreteArgTys, args, _, hargs, rfl⟩ | hfb
  · exact mkApps_hasType' bctx _ args concreteArgTys τ .op (forall₂_typed hArg hargs)
  · exact hFallback e hfb

-- ── Free variables ──────────────────────────────────────────────────

/-- `getVars` of a spine is contained in `keys` when the head and every argument
    are. (Same statement as `HasTypeAGen.lean`'s `mkApps_fvars_subset`.) -/
theorem mkApps_getVars_subset (base : LExpr') (args : List LExpr')
    (keys : List (Lambda.Identifier Unit))
    (hbase : LExpr.LExpr.getVars base ⊆ keys) (hargs : ∀ a ∈ args, LExpr.LExpr.getVars a ⊆ keys) :
    LExpr.LExpr.getVars (mkApps base args) ⊆ keys := by
  induction args generalizing base with
  | nil => simpa [mkApps] using hbase
  | cons a rest ih =>
    simp only [mkApps, List.foldl_cons]
    apply ih
    · simp only [LExpr.LExpr.getVars]
      exact List.append_subset.mpr ⟨hbase, hargs a (by simp)⟩
    · intro x hx; exact hargs x (by simp [hx])

/-- The monomorphic Indir rule introduces no free variables of its own: the head
    is an `.op` node (no `getVars`) and the arguments come from `genArg`. -/
theorem genIndir_getVars_subset (octx : OpCtx) (τ : LMonoTy)
    (keys : List (Lambda.Identifier Unit))
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → LExpr.LExpr.getVars a ⊆ keys)
    (h : (findOpsInCtx octx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (genIndir (G := SetGen.Set) octx τ genArg h)) :
    LExpr.LExpr.getVars e ⊆ keys := by
  obtain ⟨name, argTys, args, _, hargs, rfl⟩ := genIndir_shape octx τ genArg h e he
  refine mkApps_getVars_subset _ args keys (by simp only [LExpr.LExpr.getVars]; exact List.nil_subset _) ?_
  exact mapM_forall genArg hArg argTys args ((mem_mapM_iff' genArg argTys args).mpr hargs)

/-- Likewise for IndirPoly, with the fallback's free variables assumed bounded. -/
theorem genIndirPolyCore_getVars_subset (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (bctx : BVarCtx) (τ : LMonoTy) (keys : List (Lambda.Identifier Unit))
    (genArg : LMonoTy → SetGen.Set LExpr') (fallback : SetGen.Set LExpr')
    (maxNumArgs : Nat)
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → LExpr.LExpr.getVars a ⊆ keys)
    (hFallback : ∀ a, a ∈ SetGen.support fallback → LExpr.LExpr.getVars a ⊆ keys)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPolyCore (G := SetGen.Set) fctx octx pctx bctx τ genArg fallback maxNumArgs)) :
    LExpr.LExpr.getVars e ⊆ keys := by
  rcases genIndirPolyCore_shape fctx octx pctx bctx τ genArg fallback maxNumArgs e he with
    ⟨_, name, concreteArgTys, args, _, hargs, rfl⟩ | hfb
  · refine mkApps_getVars_subset _ args keys
      (by simp only [LExpr.LExpr.getVars]; exact List.nil_subset _) ?_
    exact mapM_forall genArg hArg concreteArgTys args
      ((mem_mapM_iff' genArg concreteArgTys args).mpr hargs)
  · exact hFallback e hfb

end StrataGenerators.IndirSupport

-- ── Spine arity, and the depth budget a spine actually needs ─────────
--
-- `termDepth` charges **one level per `app` node**, so a fully-applied operator
-- of arity `k` costs `k` levels, not one. Formerly that did not matter: the
-- Indir rules lived only in `genLExpr`, and `genLExprBase_termDepth_bound` — the
-- theorem asserting `termDepth e ≤ depth` — only ever saw `genLExprBase`, whose
-- every branch is a single constructor.
--
-- With the rules folded into `genLExprBase` that statement is no longer
-- merely unproved, it is **false**: at `depth = 1` the Indir branch can emit
-- `Int.Add #1 #2`, whose `termDepth` is `2`. So the bound has to be restated
-- rather than re-proved, and the honest restatement charges each level the
-- maximum arity available, not `1`.
--
-- The budget is kept as an explicit recursive function rather than the closed
-- form `depth * K` so the arithmetic in the proof stays **linear**: goals are
-- discharged with `depthBudget K n` as an opaque atom, which `omega` can handle,
-- whereas `n * K` (with `K` a variable) it cannot.

namespace StrataGenerators.IndirSupport

/-- The largest number of arguments any operator in `octx` can be applied to,
    i.e. the longest argument prefix `findOpsInCtx` can return. Bounded by each
    entry's arrow nesting.

    The fold runs over `octx.ops`, the plain operator list. `OpCtx` also carries an
    index by type (`byType`), but the arity of a candidate depends only on the arrow
    nesting of its type, so the index plays no part here. -/
def opCtxArity (octx : OpCtx) : Nat :=
  (octx.ops.map (fun p => (decomposeArrow p.2).1.length)).foldl max 0

/-- `argsForResult` returns a prefix of `decomposeArrow`'s argument list, so its
    length is bounded by the full arity. -/
theorem argsForResult_length_le (fullTy τ : LMonoTy) (args : List LMonoTy)
    (h : argsForResult fullTy τ = some args) :
    args.length ≤ (decomposeArrow fullTy).1.length := by
  -- Mirror `argsForResult`'s own recursion (on the arrow spine, measured by
  -- `sizeOf`), not structural recursion on `LMonoTy`: the recursive call is on
  -- `rest`, which sits inside a `List LMonoTy` argument of `tcons`.
  unfold argsForResult at h
  split at h
  · rename_i σ rest
    split at h
    · rename_i args' hrest
      simp only [Option.some.injEq] at h
      subst h
      have hσ : (decomposeArrow (LMonoTy.tcons "arrow" [σ, rest])).1.length
          = (decomposeArrow rest).1.length + 1 := by
        simp only [decomposeArrow, List.length_cons]
      simp only [List.length_cons]
      rw [hσ]
      have := argsForResult_length_le rest τ args' hrest
      omega
    · simp at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; simp
    · simp at h
  termination_by sizeOf fullTy

/-- Any member of a list is `≤` the running `foldl max` of that list. -/
theorem le_foldl_max (l : List Nat) (init : Nat) (x : Nat) (hx : x ∈ l) :
    x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons a rest ih =>
    rcases List.mem_cons.mp hx with rfl | hrest
    · -- `x = a` is folded in at this step, and `foldl max` only grows after.
      have hmono : ∀ (rs : List Nat) (b : Nat), b ≤ rs.foldl max b := by
        intro rs
        induction rs with
        | nil => intro b; simp
        | cons c cs ih2 =>
          intro b
          simp only [List.foldl_cons]
          exact Nat.le_trans (by omega : b ≤ max b c) (ih2 _)
      simp only [List.foldl_cons]
      exact Nat.le_trans (by omega : x ≤ max init x) (hmono rest _)
    · simp only [List.foldl_cons]
      exact ih _ hrest

/-- Every candidate the monomorphic Indir rule can pick has arity at most
    `opCtxArity octx`. -/
theorem findOpsInCtx_length_le {octx : OpCtx} {τ : LMonoTy}
    {name : String} {argTys : List LMonoTy}
    (h : (name, argTys) ∈ findOpsInCtx octx τ) :
    argTys.length ≤ opCtxArity octx := by
  simp only [findOpsInCtx, List.mem_filterMap] at h
  obtain ⟨⟨n, ty⟩, hmem, hfilt⟩ := h
  simp only at hfilt
  split at hfilt
  · rename_i arg args hargs
    simp only [Option.some.injEq, Prod.mk.injEq] at hfilt
    obtain ⟨rfl, rfl⟩ := hfilt
    have hle := argsForResult_length_le ty τ (arg :: args) hargs
    -- `(decomposeArrow ty).1.length` is one of the values folded by `opCtxArity`.
    have hmem' : (decomposeArrow ty).1.length
        ∈ octx.ops.map (fun p => (decomposeArrow p.2).1.length) :=
      List.mem_map.mpr ⟨(n, ty), hmem, rfl⟩
    have : (decomposeArrow ty).1.length ≤ opCtxArity octx := by
      unfold opCtxArity
      exact le_foldl_max _ 0 _ hmem'
    omega
  · simp at hfilt

/-- Every candidate the polymorphic IndirPoly rule can pick has arity at most
    `maxNumArgs`: `findPolymorphicOps` skips schemes of greater arity, and returns
    a `take k` prefix with `k ≤ arity`. -/
theorem findPolymorphicOps_length_le {pctx : PolyOpCtx} {τ : LMonoTy}
    {generableTys sampledTys : List LMonoTy} {maxNumArgs : Nat}
    {name : String} {argTys : List LMonoTy}
    (h : (name, argTys) ∈ findPolymorphicOps pctx τ generableTys sampledTys maxNumArgs) :
    argTys.length ≤ maxNumArgs := by
  simp only [findPolymorphicOps, List.mem_flatMap] at h
  obtain ⟨⟨nm, lty⟩, _, hin⟩ := h
  cases lty with
  | forAll boundVars monoTy =>
    simp only at hin
    split at hin
    · simp at hin
    · rename_i harity
      simp only [List.mem_filterMap, List.mem_range] at hin
      obtain ⟨k, hk, hopt⟩ := hin
      -- The candidate is `(schemeArgTys.take k).map (subst …)`. Rather than peel
      -- the `Option` `do`-block by hand, note that *whatever* it returns, the
      -- second component is that `map`, so `cases` on the bind plus the two
      -- guards leaves an equation we can read the length off.
      -- Peel the `Option` `do`-block. `findPolymorphicOps` writes it in `do`
      -- notation over `Option`, which elaborates through `Option.bind` but not in
      -- a form `rw` matches directly, so normalize with `simp` first.
      simp only [bind, Option.bind_eq_some_iff,
        Option.some.injEq, Prod.mk.injEq, pure] at hopt
      -- Peel the remaining guard binds; the surviving conjunct equates `argTys`
      -- with `(schemeArgTys.take k).map (subst …)`, of length `min k arity`.
      -- The surviving conjunct equates `argTys` with
      -- `(schemeArgTys.take k).map (subst …)`, whose length is `min k arity`.
      -- Let `simp_all` find it rather than hard-coding the guard nesting.
      -- The surviving conjunct equates `argTys` with
      -- `(schemeArgTys.take k).map (subst …)`, of length `min k arity ≤ arity`.
      -- Extract just that equation, whatever guard nesting sits above it.
      -- The surviving conjunct equates `argTys` with
      -- `(schemeArgTys.take k).map (subst …)`, of length `min k arity ≤ arity`.
      -- `omega` can finish once the length equation is in scope, so let `simp_all`
      -- normalize the guard nesting and then read the bound off `List.length_take`.
      -- The last conjunct equates `argTys` with `(schemeArgTys.take k).map (subst …)`.
      -- `rfl` substitutes it into the goal directly, leaving `min k arity ≤ maxNumArgs`,
      -- which `harity` (from the `split` above) settles.
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hopt
      simp only [List.length_map, List.length_take]
      omega

/-- The depth budget a generator needs when each level may emit an application
    spine of arity up to `K`: `depthBudget K n = n * K`, written recursively so
    the proof's arithmetic stays linear in `depthBudget K n`. -/
def depthBudget (K : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => K + depthBudget K n

theorem depthBudget_mono_le (K : Nat) {m n : Nat} (h : m ≤ n) :
    depthBudget K m ≤ depthBudget K n := by
  induction n with
  | zero => simp_all
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact Nat.le_trans (ih (by omega)) (by simp only [depthBudget]; omega)
    · have : m = n + 1 := by omega
      subst this; exact Nat.le_refl _

/-- `1 ≤ K` makes each structural level (`abs`/`app`/`ite`/`eq`/`quant`) fit too. -/
theorem le_depthBudget_self (K : Nat) (hK : 1 ≤ K) (n : Nat) : n ≤ depthBudget K n := by
  induction n with
  | zero => simp [depthBudget]
  | succ n ih => simp only [depthBudget]; omega

end StrataGenerators.IndirSupport

-- ── Argument types the Indir rules can request ──────────────────────

namespace StrataGenerators.IndirSupport

/-- **Every argument type the Indir/IndirPoly rules can ask for at target `τ` is
    simple.**

    A side condition, not a theorem, and it has to be: `findOpsInCtx` reads
    argument types straight off `octx`'s arrow types, and `findPolymorphicOps`
    produces them by substituting *sampled* types into a scheme. Neither is
    constrained to `SimpleType` by anything in the generator, so a caller with an
    exotic `octx` entry (say a `tcons "Foo"` the generator does not handle) really
    can make the rules request a non-simple argument type.

    It is needed by `genLExprBase_termDepth_bound`, whose recursion is indexed by
    `SimpleType`: bounding a spine's depth means bounding each argument's depth,
    which means invoking that theorem at the argument's type.

    Discharging it is cheap in practice — for `coreMonoOps`/`corePolyOps` all
    argument types are built from `int`/`bool`/`string`/`real`/`regex`/`Sequence`/
    `Map`/arrows, hence simple — and it is stated per-target-type so the
    quantified-over-all-types form the recursive callers need is available. -/
def IndirArgTysSimple (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (bctx : BVarCtx) (τ : LMonoTy) (maxNumArgs : Nat) : Prop :=
  (∀ (name : String) (argTys : List LMonoTy),
    (name, argTys) ∈ findOpsInCtx octx τ → ∀ σ ∈ argTys, SimpleType σ) ∧
  (∀ (sampledTys : List LMonoTy) (name : String) (argTys : List LMonoTy),
    (name, argTys) ∈ findPolymorphicOps pctx τ
      (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs →
    ∀ σ ∈ argTys, SimpleType σ)

end StrataGenerators.IndirSupport

-- ── Generic spine-measure bound for the two rules ───────────────────
--
-- `termDepth` is defined in `HasTypeAGen.lean`, downstream of this module, so
-- these two lemmas are stated over an **abstract measure** `m : LExpr' → Nat`
-- with the one property the argument actually needs (`hspine`: a spine over an
-- `.op` head costs at most the argument bound plus the arity). `HasTypeAGen.lean`
-- instantiates `m := termDepth bctx` and discharges `hspine` with
-- `termDepth_mkApps_le`.

namespace StrataGenerators.IndirSupport

/-- The monomorphic Indir rule's output is bounded by `d + opCtxArity octx`, where
    `d` bounds everything `genArg` produces. -/
theorem genIndir_measure_le {m : LExpr' → Nat} (octx : OpCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr') (d : Nat)
    (hSimple : ∀ (name : String) (argTys : List LMonoTy),
      (name, argTys) ∈ findOpsInCtx octx τ → ∀ σ ∈ argTys, SimpleType σ)
    (hArg : ∀ σ, SimpleType σ → ∀ a, a ∈ SetGen.support (genArg σ) → m a ≤ d)
    (hspine : ∀ (nm : String) (annot : LMonoTy) (args : List LExpr'),
      (∀ a ∈ args, m a ≤ d) →
      m (mkApps (.op () ⟨nm, ()⟩ (some annot)) args) ≤ d + args.length)
    (h : (findOpsInCtx octx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (genIndir (G := SetGen.Set) octx τ genArg h)) :
    m e ≤ d + opCtxArity octx := by
  obtain ⟨nm, argTys, args, hmem, hargs, rfl⟩ := genIndir_shape octx τ genArg h e he
  -- Each argument sits at a type from `argTys`, which `hSimple` says is simple.
  have hall : ∀ a ∈ args, m a ≤ d :=
    forall₂_forall_of_cond hArg (hSimple nm argTys hmem) hargs
  have hlen : args.length = argTys.length := hargs.length_eq
  have harity := findOpsInCtx_length_le hmem
  refine Nat.le_trans (hspine nm _ args hall) ?_
  omega

/-- The polymorphic IndirPoly rule's output is bounded by `d + maxNumArgs`
    (`findPolymorphicOps` skips wider schemes), or by the fallback's own bound. -/
theorem genIndirPolyCore_measure_le {m : LExpr' → Nat} (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr') (fallback : SetGen.Set LExpr')
    (maxNumArgs : Nat) (d dfb : Nat)
    (hSimple : ∀ (sampledTys : List LMonoTy) (name : String) (argTys : List LMonoTy),
      (name, argTys) ∈ findPolymorphicOps pctx τ
        (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs →
      ∀ σ ∈ argTys, SimpleType σ)
    (hArg : ∀ σ, SimpleType σ → ∀ a, a ∈ SetGen.support (genArg σ) → m a ≤ d)
    (hFallback : ∀ a, a ∈ SetGen.support fallback → m a ≤ dfb)
    (hspine : ∀ (nm : String) (annot : LMonoTy) (args : List LExpr'),
      (∀ a ∈ args, m a ≤ d) →
      m (mkApps (.op () ⟨nm, ()⟩ (some annot)) args) ≤ d + args.length)
    (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPolyCore (G := SetGen.Set) fctx octx pctx bctx τ genArg fallback maxNumArgs)) :
    m e ≤ max (d + maxNumArgs) dfb := by
  rcases genIndirPolyCore_shape fctx octx pctx bctx τ genArg fallback maxNumArgs e he with
    ⟨_, nm, concreteArgTys, args, hmem, hargs, rfl⟩ | hfb
  · have hall : ∀ a ∈ args, m a ≤ d :=
      forall₂_forall_of_cond hArg (hSimple _ nm concreteArgTys hmem) hargs
    have hlen : args.length = concreteArgTys.length := hargs.length_eq
    have harity := findPolymorphicOps_length_le hmem
    refine Nat.le_trans (hspine nm _ args hall) ?_
    omega
  · have := hFallback e hfb
    omega

end StrataGenerators.IndirSupport
