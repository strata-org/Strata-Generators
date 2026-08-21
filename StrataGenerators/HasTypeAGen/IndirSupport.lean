import StrataGenerators.SetGen
import StrataGenerators.HasTypeAGen.Core
import Strata.DL.Lambda.LTyUnify

/-!
# The lemmas for the `Indir` and `IndirPoly` rules, over any argument generator

`genLExprBase` holds the `Indir` rule and the `IndirPoly` rule in the `frequency` list of each
type. This creates a question about the order of the proofs. Four results about
`genLExprBase` each need a matching fact about `genIndir` and about `genIndirPolyCore`:

  * `genLExprBase_sound`
  * `genLExprBase_termDepth_bound`
  * `genLExprBase_fvars_subset`
  * `genLExprBase_opsConsistentR`

The lemmas `genIndir_sound` and the `genIndirPoly_*` lemmas are *after* those four results,
and the one for `opsConsistentR` is even in another file.

This module answers that question in the same way as the core module for the generators
themselves. Each lemma here takes **the argument generator `genArg` and the fallback as
parameters**, and it takes the property that it needs as a hypothesis, which is `hArg` or
`hFallback`. No lemma here refers to `genLExprBase`. Each proof of a `genLExprBase_*` result
then discharges `hArg` and `hFallback` with its *own* recursive call at the smaller depth
index `n`, and that call is its induction hypothesis.

No definition in this file therefore mentions `genLExprBase`, and the file can come before
both proof files. Each lemma also has one proof, and not one proof for each pair of a type and
a depth.
-/

open Lambda RandomChoice SetGen

namespace StrataGenerators.IndirSupport

-- ── The shared lemmas about an application spine ─────────────────────

/-- Membership in the support of `List.mapM f l` at `SetGen.Set`. The support holds `args` exactly
    when each element of `args` is in the support of `f` at the matching input.

    The main proof file holds the same statement as a `private mem_mapM_iff`. This module has its own
    copy, so that it can come before that file. -/
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

/-- The form of `mapM_forall` for a `genArg` whose guarantee holds *only for some argument types*.
    If `genArg σ` gives only terms that satisfy `P` when `Q σ` holds, and each type in `argTys`
    satisfies `Q`, then each element of the list satisfies `P`.

    A proof needs this form, because it can apply `genLExprBase_termDepth_bound` only at a type that
    the generator can make. The bound for one argument therefore has the condition that the generator
    can make the type of that argument. -/
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

/-- Each element of a list from `mapM genArg` satisfies `P`, when each term that `genArg` can give
    satisfies `P`. Each lemma below uses this theorem for its obligation about one argument. -/
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

/-- The **shape** of each term that the `Indir` rule can emit. Such a term is an application spine
    `mkApps (.op … ) args`, and each of its arguments comes from `genArg`.

    This theorem, and the theorem for `genIndirPolyCore` below, reduce the support of the two rules to
    one disjunction. The four proofs of a `genLExprBase_*` result therefore share one case analysis.
    Each of them needs only the choice between a spine over an `.op` node with arguments from
    `genArg`, and the fallback. No proof needs the internals of `findOpsInCtx` or of
    `findPolymorphicOps`. -/
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

/-- The shape of each term that `genIndirPolyCore` can emit. Such a term is a spine over a candidate
    from `findPolymorphicOps`, or it comes from the `fallback` of the caller. -/
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

-- ── The typing of a spine ───────────────────────────────────────────

/-- `mkApps` keeps the typing, through repeated use of the `app` rule. The main proof file holds the
    same statement as `mkApps_hasType`. This module has its own copy, so that it can come before that
    file. -/
theorem mkApps_hasType' (bctx : BVarCtx) (base : LExpr') (args : List LExpr')
    (argTys : List LMonoTy) (τ : LMonoTy)
    (hbase : HasTypeA' bctx base (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))
    (hargs : List.Forall₂ (HasTypeA' bctx) args argTys) :
    HasTypeA' bctx (mkApps base args) τ := by
  induction hargs generalizing base with
  | nil => exact hbase
  | cons harg _ ih => exact ih _ (LExpr.HasTypeA.app hbase harg)

/-- With `hArg`, membership of each argument in a support gives the type of each argument. -/
private theorem forall₂_typed {bctx : BVarCtx}
    {genArg : LMonoTy → SetGen.Set LExpr'}
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → HasTypeA' bctx a σ)
    {args : List LExpr'} {argTys : List LMonoTy}
    (h : List.Forall₂ (fun arg σ => arg ∈ SetGen.support (genArg σ)) args argTys) :
    List.Forall₂ (HasTypeA' bctx) args argTys := by
  induction h with
  | nil => exact .nil
  | @cons a ty _ _ hmem _ ih => exact .cons (hArg ty a hmem) ih

/-- Soundness of the monomorphic `Indir` rule, over any argument generator `genArg`. -/
theorem genIndir_hasType (octx : OpCtx) (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr')
    (hArg : ∀ σ a, a ∈ SetGen.support (genArg σ) → HasTypeA' bctx a σ)
    (h : (findOpsInCtx octx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (genIndir (G := SetGen.Set) octx τ genArg h)) :
    HasTypeA' bctx e τ := by
  obtain ⟨name, argTys, args, _, hargs, rfl⟩ := genIndir_shape octx τ genArg h e he
  exact mkApps_hasType' bctx _ args argTys τ .op (forall₂_typed hArg hargs)

/-- Soundness of the polymorphic `IndirPoly` rule, over any argument generator `genArg` and any
    fallback. The `.op` node has the type of its annotation, and that annotation is by construction
    the chain of arrows from `concreteArgTys` to `τ`. `mkApps` therefore gives the type `τ`. -/
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

-- ── The free variables of a spine ───────────────────────────────────

/-- The `getVars` of a spine is a subset of `keys` when the `getVars` of the head and of each
    argument is a subset of `keys`. The main proof file holds the same statement as
    `mkApps_fvars_subset`. -/
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

/-- The monomorphic `Indir` rule adds no free variable of its own. The head is an `.op` node, whose
    `getVars` is empty, and the arguments come from `genArg`. -/
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

/-- The same claim for the `IndirPoly` rule. The hypothesis `hFallback` bounds the free variables of
    the fallback. -/
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

-- ── The arity of a spine, and the depth budget that a spine needs ────
--
-- `termDepth` counts **one level for each `app` node**, so an operator of arity `k` with each
-- argument present costs `k` levels and not one level.
--
-- The bound must therefore give each level the largest arity that is available, and not the value 1.
-- At `depth = 1`, the `Indir` branch can emit `Int.Add #1 #2`, whose `termDepth` is 2. A bound of
-- `termDepth e ≤ depth` is therefore false.
--
-- The budget is an explicit recursive function, and not the closed form `depth * K`, so that the
-- arithmetic in a proof stays **linear**. A goal then holds `depthBudget K n` as an opaque atom, and
-- `omega` can close such a goal. `omega` cannot close a goal that holds `n * K` with a variable `K`.

namespace StrataGenerators.IndirSupport

/-- The largest number of arguments that an operator in `octx` can take. This number is also the
    length of the longest list of arguments that `findOpsInCtx` can return. The depth of the arrows in
    the type of each entry bounds it.

    The fold runs over `octx.ops`, which is the plain list of operators. An `OpCtx` also holds an
    index by type, which is `byType`. The arity of a candidate depends only on the depth of the
    arrows in its type, so that index takes no part here. -/
def opCtxArity (octx : OpCtx) : Nat :=
  (octx.ops.map (fun p => (decomposeArrow p.2).1.length)).foldl max 0

/-- `argsForResult` returns a first part of the list of arguments from `decomposeArrow`, so the full
    arity bounds its length. -/
theorem argsForResult_length_le (fullTy τ : LMonoTy) (args : List LMonoTy)
    (h : argsForResult fullTy τ = some args) :
    args.length ≤ (decomposeArrow fullTy).1.length := by
  -- The proof follows the recursion of `argsForResult` itself, which runs over the chain of arrows
  -- and which `sizeOf` measures. It does not use structural recursion on an `LMonoTy`, because the
  -- recursive call is on `rest`, which is inside a `List LMonoTy` argument of a `tcons`.
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

/-- Each member of a list is not more than the result of a fold that takes the maximum over that
    list. -/
theorem le_foldl_max (l : List Nat) (init : Nat) (x : Nat) (hx : x ∈ l) :
    x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons a rest ih =>
    rcases List.mem_cons.mp hx with rfl | hrest
    · -- The fold takes `x` into the accumulator at this step, and the accumulator then only grows.
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

/-- The arity of each candidate that the monomorphic `Indir` rule can pick is not more than
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
    -- The length of the argument list of `ty` is one of the values that `opCtxArity` folds.
    have hmem' : (decomposeArrow ty).1.length
        ∈ octx.ops.map (fun p => (decomposeArrow p.2).1.length) :=
      List.mem_map.mpr ⟨(n, ty), hmem, rfl⟩
    have : (decomposeArrow ty).1.length ≤ opCtxArity octx := by
      unfold opCtxArity
      exact le_foldl_max _ 0 _ hmem'
    omega
  · simp at hfilt

/-- The arity of each candidate that the polymorphic `IndirPoly` rule can pick is not more than
    `maxNumArgs`. `findPolymorphicOps` skips a scheme of a larger arity, and it returns the first `k`
    arguments for a `k` that is not more than the arity. -/
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
      -- `findPolymorphicOps` writes its body in `do` notation over `Option`, which elaborates
      -- through `Option.bind`. `rw` does not match that form directly, so `simp` normalizes it
      -- first.
      simp only [bind, Option.bind_eq_some_iff,
        Option.some.injEq, Prod.mk.injEq, pure] at hopt
      -- The last part of `hopt` says that `argTys` is the first `k` types of the scheme, after a
      -- substitution. `rfl` puts that equation into the goal, which then reads
      -- `min k arity ≤ maxNumArgs`. The hypothesis `harity` from the `split` above closes it.
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hopt
      simp only [List.length_map, List.length_take]
      omega

/-- The depth budget that a generator needs when each level can emit an application spine of an arity
    up to `K`. The value is `n * K`, and the definition is recursive, so that the arithmetic in a
    proof stays linear in `depthBudget K n`. -/
def depthBudget (K : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => K + depthBudget K n

/-- The budget grows with the depth. -/
theorem depthBudget_mono_le (K : Nat) {m n : Nat} (h : m ≤ n) :
    depthBudget K m ≤ depthBudget K n := by
  induction n with
  | zero => simp_all
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact Nat.le_trans (ih (by omega)) (by simp only [depthBudget]; omega)
    · have : m = n + 1 := by omega
      subst this; exact Nat.le_refl _

/-- When `K` is 1 or more, the budget is also large enough for a term that has one structural level
    for each unit of depth. Examples of such a level are `abs`, `app`, `ite`, `eq` and `quant`. -/
theorem le_depthBudget_self (K : Nat) (hK : 1 ≤ K) (n : Nat) : n ≤ depthBudget K n := by
  induction n with
  | zero => simp [depthBudget]
  | succ n ih => simp only [depthBudget]; omega

end StrataGenerators.IndirSupport

-- ── A generic bound on the measure of a spine, for the two rules ─────
--
-- The two lemmas below hold for an **abstract measure** `m : LExpr' → Nat`. The proofs need only
-- one property of `m`, which the hypothesis `hspine` gives: the measure of a spine over an `.op`
-- head is not more than the bound on the arguments plus the arity. A caller instantiates `m` with
-- its own measure, and it then proves `hspine` for that measure.

namespace StrataGenerators.IndirSupport

/-- The measure of each term from the monomorphic `Indir` rule is not more than
    `d + opCtxArity octx`. Here `d` is a bound on the measure of each term that `genArg` gives. -/
theorem genIndir_measure_le {m : LExpr' → Nat} {tvars : List TyIdentifier}
    (octx : OpCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr') (d : Nat)
    (hSimple : ∀ (name : String) (argTys : List LMonoTy),
      (name, argTys) ∈ findOpsInCtx octx τ → ∀ σ ∈ argTys, ∃ k, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars k))
    (hArg : ∀ σ, (∃ k, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars k)) → ∀ a, a ∈ SetGen.support (genArg σ) → m a ≤ d)
    (hspine : ∀ (nm : String) (annot : LMonoTy) (args : List LExpr'),
      (∀ a ∈ args, m a ≤ d) →
      m (mkApps (.op () ⟨nm, ()⟩ (some annot)) args) ≤ d + args.length)
    (h : (findOpsInCtx octx τ).length > 0) (e : LExpr')
    (he : e ∈ SetGen.support (genIndir (G := SetGen.Set) octx τ genArg h)) :
    m e ≤ d + opCtxArity octx := by
  obtain ⟨nm, argTys, args, hmem, hargs, rfl⟩ := genIndir_shape octx τ genArg h e he
  -- Each argument has a type from `argTys`, and `hSimple` says that each such type is simple.
  have hall : ∀ a ∈ args, m a ≤ d :=
    forall₂_forall_of_cond hArg (hSimple nm argTys hmem) hargs
  have hlen : args.length = argTys.length := hargs.length_eq
  have harity := findOpsInCtx_length_le hmem
  refine Nat.le_trans (hspine nm _ args hall) ?_
  omega

/-- The measure of each term from the polymorphic `IndirPoly` rule is not more than `d + maxNumArgs`,
    because `findPolymorphicOps` skips a scheme of a larger arity. A term from the fallback keeps the
    bound of the fallback. -/
theorem genIndirPolyCore_measure_le {m : LExpr' → Nat} {tvars : List TyIdentifier}
    (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → SetGen.Set LExpr') (fallback : SetGen.Set LExpr')
    (maxNumArgs : Nat) (d dfb : Nat)
    (hSimple : ∀ (sampledTys : List LMonoTy) (name : String) (argTys : List LMonoTy),
      (name, argTys) ∈ findPolymorphicOps pctx τ
        (generableTypesFromCtx bctx fctx octx) sampledTys maxNumArgs →
      ∀ σ ∈ argTys, ∃ k, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars k))
    (hArg : ∀ σ, (∃ k, σ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars k)) → ∀ a, a ∈ SetGen.support (genArg σ) → m a ≤ d)
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
