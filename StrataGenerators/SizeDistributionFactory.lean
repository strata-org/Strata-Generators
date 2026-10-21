import StrataGenerators.SizeDistribution

/-!
# The coverage zero side with a factory

`StrataGenerators.SizeDistribution` proves "no draw below size 3 covers the seven forms" only for a
factory with no operator of positive arity, because a factory call `f(a₁ … aₖ)` is a spine of `k`
`app` nodes that the size does not pay for, so the size no longer bounds the height.

This module removes that hypothesis by counting compound *forms* instead of measuring height.
`compoundOf e` is the set of the five compound forms occurring in `e`.

* size 0 (`base_zero_cf`): no compound form.
* size 1 (`base_one_cf`, `lexpr_one_cf`): at most one. A size-1 node has leaf children, and a
  factory call over leaves contributes only `app`. This holds for **every** factory.
* size 2 (`base_two_cf`, `lexpr_two_cf`): at most four, when no monomorphic operator takes more
  than three arguments and the polymorphic rule applies at most three. A size-2 term is a node
  (`ite` has the most children, three) or a factory call (at most three arguments), over size-1
  terms with at most one form each: `1 + 3 · 1 = 4`.

Five compound forms do not fit in four, so `prob_genLExpr_covers_eq_zero_of_arity`: for every
free-variable context, binder context, target type and polymorphic context, a `genLExpr` draw of
size at most 2 covers with probability exactly 0. The Core factory satisfies the arity hypothesis
(`opCtxArity coreMonoOps = 3`, `opCtxArity_coreMonoOps` in `SizeDistributionProgram`).

The arity bound is where the argument is tight (by inspection, not machine-checked): an operator of four arguments, one of them of a
function type, lets a size-2 call `f (λx:bool. x) (ite c c c) (c = c) (∀x. c)` show every form.
-/

open Lambda RandomChoice SPMF NNReal ENNReal
open StrataGenerators.SizeDistribution StrataGenerators.IndirSupport

namespace StrataGenerators.SizeDistributionFactory

local notation "cf" => compoundOf

theorem mem_cf_app {f a : LExpr'} {F : Form} (h : F ∈ cf (.app () f a)) :
    F = .app ∨ F ∈ cf f ∨ F ∈ cf a := by
  simp only [compoundOf, formsOf, Finset.mem_filter, Finset.mem_insert, Finset.mem_union] at h ⊢
  tauto

/-- Every compound form of a spine is `app`, or a compound form of its head or of an argument. -/
theorem mem_cf_mkApps (base : LExpr') (args : List LExpr') (F : Form)
    (h : F ∈ cf (mkApps base args)) : F ∈ cf base ∨ F = .app ∨ ∃ a ∈ args, F ∈ cf a := by
  induction args generalizing base with
  | nil => exact Or.inl (by simpa [mkApps] using h)
  | cons a rest ih =>
    have hfold : mkApps base (a :: rest) = mkApps (LExpr.app () base a) rest := by
      simp only [mkApps, List.foldl_cons]
    rw [hfold] at h
    rcases ih _ h with h | h | ⟨b, hb, h⟩
    · rcases mem_cf_app h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨a, by simp, h⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨b, by simp [hb], h⟩)

theorem cf_op (m o ty) : cf (LExpr.op m o ty : LExpr') = ∅ := by
  simp [compoundOf, formsOf, rootForm, compoundForms]

/-- The union of the compound forms of a list of terms. -/
def cfs (args : List LExpr') : Finset Form := args.foldr (fun a acc => cf a ∪ acc) ∅

theorem mem_cfs {args : List LExpr'} {F : Form} : F ∈ cfs args ↔ ∃ a ∈ args, F ∈ cf a := by
  induction args with
  | nil => simp [cfs]
  | cons a rest ih =>
    simp only [cfs, List.foldr_cons, Finset.mem_union] at ih ⊢
    rw [ih]; simp

theorem card_cfs_le {args : List LExpr'} {b : Nat} (h : ∀ a ∈ args, (cf a).card ≤ b) :
    (cfs args).card ≤ args.length * b := by
  induction args with
  | nil => simp [cfs]
  | cons a rest ih =>
    simp only [cfs, List.foldr_cons, List.length_cons] at ih ⊢
    have h1 := h a (by simp)
    have h2 := ih fun x hx => h x (by simp [hx])
    have := Finset.card_union_le (cf a) (rest.foldr (fun a acc => cf a ∪ acc) ∅)
    nlinarith

/-- A factory call with at most three arguments, each of at most `b` compound forms, has at
most `1 + 3b`. -/
theorem card_cf_spine (m o ty) (args : List LExpr') (b : Nat) (hlen : args.length ≤ 3)
    (h : ∀ a ∈ args, (cf a).card ≤ b) :
    (cf (mkApps (LExpr.op m o ty) args)).card ≤ 1 + 3 * b := by
  have hsub : cf (mkApps (LExpr.op m o ty) args) ⊆ insert .app (cfs args) := by
    intro F hF
    rcases mem_cf_mkApps _ args F hF with h | h | h
    · simp [cf_op] at h
    · simp [h]
    · exact Finset.mem_insert_of_mem (mem_cfs.mpr h)
  have := Finset.card_le_card hsub
  have := Finset.card_insert_le Form.app (cfs args)
  have := card_cfs_le h
  nlinarith

/-- A call whose arguments show at most the form `app` shows at most `app`. -/
theorem cf_spine_sub_app (m o ty) (args : List LExpr') (h : ∀ a ∈ args, cf a ⊆ {.app}) :
    cf (mkApps (LExpr.op m o ty) args) ⊆ {.app} := by
  intro F hF
  rcases mem_cf_mkApps _ args F hF with h' | h' | ⟨a, ha, h'⟩
  · simp [cf_op] at h'
  · simp [h']
  · exact h a ha h'

/-- The direct children of a node. -/
def children : LExpr' → List LExpr'
  | .abs _ _ _ b => [b]
  | .quant _ _ _ _ tr b => [tr, b]
  | .app _ f a => [f, a]
  | .ite _ c t e => [c, t, e]
  | .eq _ a b => [a, b]
  | _ => []

/-- A node shows at most one compound form beyond those of its children. -/
theorem card_cf_node (e : LExpr') : (cf e).card ≤ 1 + (cfs (children e)).card := by
  have hsub : cf e ⊆ insert (rootForm e) (cfs (children e)) := by
    intro F hF
    cases e <;> simp only [compoundOf, formsOf, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton] at hF <;>
      simp only [children, Finset.mem_insert, mem_cfs, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, compoundOf, Finset.mem_filter, rootForm] <;>
      tauto
  exact le_trans (Finset.card_le_card hsub) (by
    have := Finset.card_insert_le (rootForm e) (cfs (children e)); omega)

theorem cf_of_isLeaf {e : LExpr'} (h : IsLeaf e) : cf e = ∅ := by
  cases e <;> simp_all [IsLeaf, rootForm, compoundOf, formsOf, compoundForms]

variable (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)

local notation "Gb" bctx:max n:max τ:max => genLExprBase (G := SPMF) fctx octx pctx tvars bctx n τ

theorem genIndir_cf (bctx : BVarCtx) (σ : LMonoTy) (g : LMonoTy → SPMF LExpr') (h) (b : Nat)
    (hK : opCtxArity octx ≤ 3)
    (hg : ∀ σ', IsSoundFor (g σ') (fun a => (cf a).card ≤ b)) :
    IsSoundFor (genIndir (G := SPMF) octx σ g h) (fun e => (cf e).card ≤ 1 + 3 * b) := by
  intro e he
  obtain ⟨nm, argTys, args, hmem, hargs, rfl⟩ := genIndir_shape octx σ g h e he
  refine card_cf_spine _ _ _ args b ?_ ?_
  · rw [hargs.length_eq]; exact le_trans (findOpsInCtx_length_le hmem) hK
  · exact forall₂_forall_of_cond (Q := fun _ => True) (fun σ' _ a ha => hg σ' a ha)
      (fun _ _ => trivial) hargs

theorem genIndir_cf_app (σ : LMonoTy) (g : LMonoTy → SPMF LExpr') (h)
    (hg : ∀ σ', IsSoundFor (g σ') (fun a => cf a ⊆ {.app})) :
    IsSoundFor (genIndir (G := SPMF) octx σ g h) (fun e => cf e ⊆ {.app}) := by
  intro e he
  obtain ⟨nm, argTys, args, hmem, hargs, rfl⟩ := genIndir_shape octx σ g h e he
  exact cf_spine_sub_app _ _ _ args (forall₂_forall_of_cond (Q := fun _ => True)
    (fun σ' _ a ha => hg σ' a ha) (fun _ _ => trivial) hargs)

theorem genIndirPolyCore_cf (bctx : BVarCtx) (σ : LMonoTy) (g : LMonoTy → SPMF LExpr')
    (fb : SPMF LExpr') (k : Nat) (hk : k ≤ 3) (b : Nat) (P : LExpr' → Prop)
    (hg : ∀ σ', IsSoundFor (g σ') (fun a => (cf a).card ≤ b)) (hfb : IsSoundFor fb P) :
    IsSoundFor (genIndirPolyCore (G := SPMF) fctx octx pctx bctx σ g fb k)
      (fun e => (cf e).card ≤ 1 + 3 * b ∨ P e) := by
  intro e he
  rcases genIndirPolyCore_shape _ _ _ _ _ _ _ _ e he with
    ⟨_, nm, argTys, args, hmem, hargs, rfl⟩ | hf
  · refine Or.inl (card_cf_spine _ _ _ args b ?_ ?_)
    · rw [hargs.length_eq]; exact le_trans (findPolymorphicOps_length_le hmem) hk
    · exact forall₂_forall_of_cond (Q := fun _ => True) (fun σ' _ a ha => hg σ' a ha)
        (fun _ _ => trivial) hargs
  · exact Or.inr (hfb e hf)

theorem genIndirPolyCore_cf_app (bctx : BVarCtx) (σ : LMonoTy) (g : LMonoTy → SPMF LExpr')
    (fb : SPMF LExpr') (k : Nat) (P : LExpr' → Prop)
    (hg : ∀ σ', IsSoundFor (g σ') (fun a => cf a ⊆ {.app})) (hfb : IsSoundFor fb P) :
    IsSoundFor (genIndirPolyCore (G := SPMF) fctx octx pctx bctx σ g fb k)
      (fun e => cf e ⊆ {.app} ∨ P e) := by
  intro e he
  rcases genIndirPolyCore_shape _ _ _ _ _ _ _ _ e he with
    ⟨_, nm, argTys, args, hmem, hargs, rfl⟩ | hf
  · exact Or.inl (cf_spine_sub_app _ _ _ args (forall₂_forall_of_cond (Q := fun _ => True)
      (fun σ' _ a ha => hg σ' a ha) (fun _ _ => trivial) hargs))
  · exact Or.inr (hfb e hf)

theorem base_zero_cf (bctx : BVarCtx) (σ : LMonoTy) :
    IsSoundFor (Gb bctx 0 σ) (fun e => cf e = ∅) :=
  fun e he => cf_of_isLeaf (zero_leaf fctx octx pctx tvars bctx σ e he)

theorem base_zero_cf_app (bctx : BVarCtx) (σ : LMonoTy) :
    IsSoundFor (Gb bctx 0 σ) (fun e => cf e ⊆ {.app}) :=
  fun e he => by
    show cf e ⊆ _
    rw [base_zero_cf fctx octx pctx tvars bctx σ e he]; exact Finset.empty_subset _

theorem pickBVar_cf (bc : BVarCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickBVar (G := SPMF) bc σ h) (fun e => cf e = ∅) :=
  fun e he => cf_of_isLeaf (pickBVar_leaf bc σ h e he)
theorem pickFVar_cf (fc : FVarCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickFVar (G := SPMF) fc σ h) (fun e => cf e = ∅) :=
  fun e he => cf_of_isLeaf (pickFVar_leaf fc σ h e he)
theorem pickOp_cf (oc : OpCtx) (σ : LMonoTy) (h) :
    IsSoundFor (pickOp (G := SPMF) oc σ h) (fun e => cf e = ∅) :=
  fun e he => cf_of_isLeaf (pickOp_leaf oc σ h e he)

/-- Close a leaf goal of a `walk` over `genLExprBase`: a constant, a term with a known compound
form set, or a node whose children all have bounded compound form sets. -/
macro "cf_close" : tactic => `(tactic| (
  try simp only [eq_self_iff_true, true_implies, forall_const] at *
  first
    | (rw [cf_of_isLeaf (Or.inl rfl)]; simp)
    | (rename_i h; rw [h]; simp)
    | (rename_i h; exact le_trans (Finset.card_le_card h) (by simp))
    | (refine le_trans (card_cf_node _) ?_; simp [children, cfs, *]; done)))

/-- **Size 1 shows at most one compound form**, in every context and for every factory. -/
theorem base_one_cf (bctx : BVarCtx) (τ : LMonoTy) :
    IsSoundFor (Gb bctx 1 τ) (fun e => (cf e).card ≤ 1) := by
  have hz : ∀ m bc σ, IsSoundFor (Gb bc m σ) (fun e => m = 0 → cf e = ∅) := by
    intro m bc σ e he hm; subst hm; exact base_zero_cf fctx octx pctx tvars bc σ e he
  have hI : ∀ m σ h, IsSoundFor (genIndir (G := SPMF) octx σ
      (genLExprBase (G := SPMF) fctx octx pctx tvars bctx m) h) (fun e => m = 0 → cf e ⊆ {.app}) := by
    intro m σ h e he hm; subst hm
    exact genIndir_cf_app octx σ _ h (base_zero_cf_app fctx octx pctx tvars bctx) e he
  have hP : ∀ m bc σ, IsSoundFor (genIndirPolyCore (G := SPMF) fctx octx pctx bc σ
      (genLExprBase (G := SPMF) fctx octx pctx tvars bc m) (Gb bc m σ) 3)
      (fun e => m = 0 → cf e ⊆ {.app}) := by
    intro m bc σ e he hm; subst hm
    rcases genIndirPolyCore_cf_app fctx octx pctx bc σ _ _ 3 _
      (base_zero_cf_app fctx octx pctx tvars bc) (base_zero_cf fctx octx pctx tvars bc σ) e he with
      h | h
    · exact h
    · rw [h]; exact Finset.empty_subset _
  rw [IsSoundFor.iff_obs, genLExprBase.eq_def]
  walk [(hz _ _ _).obs, (hI _ _ _).obs, (hP _ _ _).obs,
    (genAppArgTy_true fctx octx tvars _ _ _).obs,
    (genGenerableTy_true fctx octx tvars _ _).obs, (genLMonoTy_true tvars _).obs,
    natArbitrary_true.obs, genInterestingChar_true.obs, natArbGeom_true.obs,
    (pickBVar_cf _ _ _).obs, (pickFVar_cf _ _ _).obs, (pickOp_cf _ _ _).obs]
  all_goals cf_close

theorem card_cf_node_le (e : LExpr') (b : Nat) (h : ∀ c ∈ children e, (cf c).card ≤ b) :
    (cf e).card ≤ 1 + (children e).length * b :=
  le_trans (card_cf_node e) (Nat.add_le_add_left (card_cfs_le h) 1)

theorem card_cf_ite_le {c t e : LExpr'} {b : Nat} (hc : (cf c).card ≤ b) (ht : (cf t).card ≤ b)
    (he : (cf e).card ≤ b) : (cf (.ite () c t e)).card ≤ 1 + 3 * b := by
  have := card_cf_node_le (.ite () c t e) b (by simp [children]; exact ⟨hc, ht, he⟩)
  simpa [children] using this
theorem card_cf_eq_le {x y : LExpr'} {b : Nat} (hx : (cf x).card ≤ b) (hy : (cf y).card ≤ b) :
    (cf (.eq () x y)).card ≤ 1 + 2 * b := by
  have := card_cf_node_le (.eq () x y) b (by simp [children]; exact ⟨hx, hy⟩)
  simpa [children] using this
theorem card_cf_app_le {x y : LExpr'} {b : Nat} (hx : (cf x).card ≤ b) (hy : (cf y).card ≤ b) :
    (cf (.app () x y)).card ≤ 1 + 2 * b := by
  have := card_cf_node_le (.app () x y) b (by simp [children]; exact ⟨hx, hy⟩)
  simpa [children] using this
theorem card_cf_quant_le {k n ty} {x y : LExpr'} {b : Nat} (hx : (cf x).card ≤ b)
    (hy : (cf y).card ≤ b) : (cf (.quant () k n ty x y)).card ≤ 1 + 2 * b := by
  have := card_cf_node_le (.quant () k n ty x y) b (by simp [children]; exact ⟨hx, hy⟩)
  simpa [children] using this
theorem card_cf_abs_le {n ty} {x : LExpr'} {b : Nat} (hx : (cf x).card ≤ b) :
    (cf (.abs () n ty x)).card ≤ 1 + b := by
  have := card_cf_node_le (.abs () n ty x) b (by simp [children]; exact hx)
  simpa [children] using this

set_option maxHeartbeats 1600000 in
/-- **Size 2 shows at most four compound forms**, in every context, when no factory operator
takes more than three arguments. Every node at size 2 is a compound node or a factory call with
at most three children, each a size-1 term with at most one compound form. -/
theorem base_two_cf (hK : opCtxArity octx ≤ 3) (bctx : BVarCtx) (τ : LMonoTy) :
    IsSoundFor (Gb bctx 2 τ) (fun e => (cf e).card ≤ 4) := by
  have hz : ∀ m bc σ, IsSoundFor (Gb bc m σ) (fun e => m = 1 → (cf e).card ≤ 1) := by
    intro m bc σ e he hm; subst hm; exact base_one_cf fctx octx pctx tvars bc σ e he
  have hI : ∀ m σ h, IsSoundFor (genIndir (G := SPMF) octx σ
      (genLExprBase (G := SPMF) fctx octx pctx tvars bctx m) h)
      (fun e => m = 1 → (cf e).card ≤ 4) := by
    intro m σ h e he hm; subst hm
    exact genIndir_cf octx bctx σ _ h 1 hK (base_one_cf fctx octx pctx tvars bctx) e he
  have hP : ∀ m bc σ, IsSoundFor (genIndirPolyCore (G := SPMF) fctx octx pctx bc σ
      (genLExprBase (G := SPMF) fctx octx pctx tvars bc m) (Gb bc m σ) 3)
      (fun e => m = 1 → (cf e).card ≤ 4) := by
    intro m bc σ e he hm; subst hm
    rcases genIndirPolyCore_cf fctx octx pctx bc σ _ _ 3 le_rfl 1 _
      (base_one_cf fctx octx pctx tvars bc) (base_one_cf fctx octx pctx tvars bc σ) e he with
      h | h <;> omega
  rw [IsSoundFor.iff_obs, genLExprBase.eq_def]
  walk [(hz _ _ _).obs, (hI _ _ _).obs, (hP _ _ _).obs,
    (genAppArgTy_true fctx octx tvars _ _ _).obs,
    (genGenerableTy_true fctx octx tvars _ _).obs, (genLMonoTy_true tvars _).obs,
    natArbitrary_true.obs, genInterestingChar_true.obs, natArbGeom_true.obs,
    (pickBVar_cf _ _ _).obs, (pickFVar_cf _ _ _).obs, (pickOp_cf _ _ _).obs]
  all_goals (clear hz hI hP; try simp only [eq_self_iff_true, true_implies, forall_const] at *)
  all_goals (try omega)
  all_goals (try (rw [‹cf _ = ∅›]; simp))
  all_goals (try (rw [cf_of_isLeaf (Or.inl rfl)]; simp))
  all_goals (try with_reducible exact le_trans (card_cf_ite_le (b := 1) (by assumption) (by assumption) (by assumption)) (by omega))
  all_goals (try with_reducible exact le_trans (card_cf_eq_le (b := 1) (by assumption) (by assumption)) (by omega))
  all_goals (try with_reducible exact le_trans (card_cf_app_le (b := 1) (by assumption) (by assumption)) (by omega))
  all_goals (try with_reducible exact le_trans (card_cf_quant_le (b := 1) (by assumption) (by assumption)) (by omega))
  all_goals (try with_reducible exact le_trans (card_cf_abs_le (b := 1) (by assumption)) (by omega))

-- ── `genLExpr` ──────────────────────────────────────────────────────

/-- The argument generator `genLExpr` hands its two `Indir` rules (with `retryCont = id`). -/
noncomputable def lexprArg (bctx : BVarCtx) (k : Nat) : Nat → LMonoTy → SPMF LExpr'
  | 0 => genLExprBase (G := SPMF) fctx octx pctx tvars bctx 0
  | n + 1 => fun σ => genLExpr (G := SPMF) fctx octx pctx tvars bctx n σ k id

set_option linter.deprecated false in
/-- Every draw of `genLExpr` comes from the base generator at the same size, from the `Indir`
rule over `lexprArg`, or from the `IndirPoly` rule over `lexprArg` with the base generator as
fallback. -/
theorem genLExpr_cases (bctx : BVarCtx) (d : Nat) (τ : LMonoTy) (k : Nat) (e : LExpr')
    (he : e ∈ SPMF.support (genLExpr (G := SPMF) fctx octx pctx tvars bctx d τ k id)) :
    e ∈ SPMF.support (Gb bctx d τ) ∨
    (∃ h, e ∈ SPMF.support (genIndir (G := SPMF) octx τ (lexprArg fctx octx pctx tvars bctx k d) h)) ∨
    e ∈ SPMF.support (genIndirPolyCore (G := SPMF) fctx octx pctx bctx τ
      (lexprArg fctx octx pctx tvars bctx k d) (Gb bctx d τ) k) := by
  cases d <;>
  · unfold genLExpr at he
    dsimp only [id] at he
    unfold genIndirPoly at he
    split at he
    · rename_i h
      rw [mem_support_frequency_iff] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at he
      obtain ⟨w, g, hp, -, he⟩ := he
      rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inl he
      · simp only [RandomChoice.pick, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
          or_false] at he
        obtain ⟨g, hg, he⟩ := he
        rcases hg with rfl | rfl
        · exact Or.inr (Or.inl ⟨h, he⟩)
        · dsimp only at he; exact Or.inr (Or.inr he)
    · simp only [RandomChoice.pick, mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil,
        or_false] at he
      obtain ⟨g, hg, he⟩ := he
      rcases hg with rfl | rfl
      · exact Or.inl he
      · dsimp only at he; exact Or.inr (Or.inr he)

theorem lexpr_zero_cf (bctx : BVarCtx) (τ : LMonoTy) (k : Nat) :
    IsSoundFor (genLExpr (G := SPMF) fctx octx pctx tvars bctx 0 τ k id) (fun e => cf e ⊆ {.app}) := by
  intro e he
  rcases genLExpr_cases fctx octx pctx tvars bctx 0 τ k e he with h | ⟨h, h'⟩ | h
  · exact base_zero_cf_app fctx octx pctx tvars bctx τ e h
  · exact genIndir_cf_app octx τ _ h (base_zero_cf_app fctx octx pctx tvars bctx) e h'
  · rcases genIndirPolyCore_cf_app fctx octx pctx bctx τ _ _ k _
      (base_zero_cf_app fctx octx pctx tvars bctx) (base_zero_cf_app fctx octx pctx tvars bctx τ)
      e h with h | h <;> exact h

theorem lexpr_one_cf (bctx : BVarCtx) (τ : LMonoTy) (k : Nat) :
    IsSoundFor (genLExpr (G := SPMF) fctx octx pctx tvars bctx 1 τ k id)
      (fun e => (cf e).card ≤ 1) := by
  have happ : ∀ {e : LExpr'}, cf e ⊆ {.app} → (cf e).card ≤ 1 := fun h =>
    le_trans (Finset.card_le_card h) (by simp)
  intro e he
  rcases genLExpr_cases fctx octx pctx tvars bctx 1 τ k e he with h | ⟨h, h'⟩ | h
  · exact base_one_cf fctx octx pctx tvars bctx τ e h
  · exact happ (genIndir_cf_app octx τ _ h
      (fun σ => lexpr_zero_cf fctx octx pctx tvars bctx σ k) e h')
  · rcases genIndirPolyCore_cf_app fctx octx pctx bctx τ _ _ k _
      (fun σ => lexpr_zero_cf fctx octx pctx tvars bctx σ k)
      (base_one_cf fctx octx pctx tvars bctx τ) e h with h | h
    · exact happ h
    · exact h

theorem lexpr_two_cf (hK : opCtxArity octx ≤ 3) (bctx : BVarCtx) (τ : LMonoTy) (k : Nat)
    (hk : k ≤ 3) :
    IsSoundFor (genLExpr (G := SPMF) fctx octx pctx tvars bctx 2 τ k id)
      (fun e => (cf e).card ≤ 4) := by
  intro e he
  rcases genLExpr_cases fctx octx pctx tvars bctx 2 τ k e he with h | ⟨h, h'⟩ | h
  · exact base_two_cf fctx octx pctx tvars hK bctx τ e h
  · exact genIndir_cf octx bctx τ _ h 1 hK
      (fun σ => lexpr_one_cf fctx octx pctx tvars bctx σ k) e h'
  · rcases genIndirPolyCore_cf fctx octx pctx bctx τ _ _ k hk 1 _
      (fun σ => lexpr_one_cf fctx octx pctx tvars bctx σ k)
      (base_two_cf fctx octx pctx tvars hK bctx τ) e h with h | h <;> omega

/-- **The coverage zero side, for any factory of arity at most three.** For every free-variable
context, binder context, type, and polymorphic-operator context, a `genLExpr` draw of size at most
`2` never covers the seven forms, provided no monomorphic factory operator takes more than three
arguments and the polymorphic rule applies at most three (`maxNumArgs ≤ 3`, the default). The Core
factory satisfies the hypothesis (`opCtxArity coreMonoOps = 3`). The proof is a count: size 2
leaves room for one node and at most three children with one compound form each. -/
theorem prob_genLExpr_covers_eq_zero_of_arity (hK : opCtxArity octx ≤ 3) (bctx : BVarCtx)
    (τ : LMonoTy) (k : Nat) (hk : k ≤ 3) (n : Nat) (hn : n ≤ 2) :
    prob (genLExpr (G := SPMF) fctx octx pctx tvars bctx n τ k id) {e | Covers e} = 0 := by
  refine (prob_eq_zero_iff _ _).mpr fun e he hc => ?_
  have hsub : compoundForms ⊆ cf e := by
    intro F hF
    refine Finset.mem_filter.mpr ⟨hc ?_, hF⟩
    simp only [compoundForms, Finset.mem_insert, Finset.mem_singleton] at hF
    simp only [stlcForms, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h5 : compoundForms.card = 5 := by decide
  have hle := Finset.card_le_card hsub
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
  · have := Finset.card_le_card (lexpr_zero_cf fctx octx pctx tvars bctx τ k e he)
    simp at this; omega
  · have := lexpr_one_cf fctx octx pctx tvars bctx τ k e he; omega
  · have := lexpr_two_cf fctx octx pctx tvars hK bctx τ k hk e he; omega

end StrataGenerators.SizeDistributionFactory
