import StrataGenerators.HasTypeAGen
import StrataGenerators.HasTypeAGen.Defs
import StrataGenerators.HasTypeAGen.OpsConsistentDef

open Lambda RandomChoice ArbNat ArbChar ArbString SetGen

set_option linter.unusedSimpArgs false

/-!
# `OpsConsistent` for generated `LExpr`s

This module establishes that the generator (`genLExpr` and friends) produces
terms satisfying Strata's `OpsConsistent` predicate — the invariant that every
`.op` type annotation is a valid instantiation of the factory function's generic
type. Together with `genLExpr_sound`/`genLExpr_complete` (which handle
`HasTypeA`) this makes the generator sound and complete with respect to *both*
`HasTypeA` and `OpsConsistent`.

`OpsConsistent` (defined in a private section of Strata's `Assumptions.lean`) is
mirrored here as `Lambda.GenOpsConsistent`, proven definitionally identical by
`Lambda.GenOpsConsistent.faithful` (see `HasTypeAGen/OpsConsistentDef.lean`).

## Why the generator is `OpsConsistent`

Every `.op` node a generated term can contain comes from one of two places:

* **`pickOp`** (inside `genLExprBase`): the annotation is exactly the *generic*
  factory type of the operator (as computed by `factoryOps`). `opGeneric_opsConsistent`
  shows such annotations are consistent (unifying the generic type with itself
  gives the empty substitution).

* **`genIndirPoly`**: the annotation is `concreteArgTys.foldr arrow τ`. The
  bound-variable *freshening* fix (`docs/ops-consistent-capture-bug.md`) plus the
  *ground-only* instantiation fix (`docs/ops-consistent-polymorphic-gap.md`)
  guarantee it is a *ground* instance of the operator's generic type; then
  `unify_ground_instance` (a from-scratch unification-completeness result for
  ground matching, in `StrataGenerators/UnifyGroundInstance.lean`) shows
  `opTypeSubst` succeeds and reconstructs the annotation. This is discharged from
  a factory-well-formedness hypothesis `PCtxWF` (via `PolyOpsConsistent_of_PCtxWF`),
  giving the unconditional `genLExpr_opsConsistent_of_PCtxWF`.

All compound cases (`.app`, `.ite`, `.abs`, `.eq`, `.quant`) are structural.
-/

-- ── `factoryOps` characterization ────────────────────────────────────

/-- Every operator entry produced by `factoryOps F` resolves to a factory
    function whose generic type is exactly the entry's type — provided the
    function's output has a well-formed arrow spine (`ArrowSpineOK`), which all
    parser-produced factory functions satisfy. -/
theorem factoryOps_mem_char (F : @Factory LExprParams') (nm : String) (τ : LMonoTy)
    (hwf : ∀ f : LFunc LExprParams', f ∈ F.toArray.toList → ArrowSpineOK f.output)
    (h : (nm, τ) ∈ factoryOps F) :
    ∃ fn, F[nm]? = some fn ∧ τ = LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd) := by
  unfold factoryOps at h
  simp only [List.mem_filterMap] at h
  obtain ⟨fn, hfn_mem, hfn_eq⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at hfn_eq
  obtain ⟨hnm, hτ⟩ := hfn_eq
  subst hnm
  have hfn_mem' : fn ∈ F.toArray := Array.mem_def.mpr hfn_mem
  obtain ⟨hs, hget⟩ := Factory.mem_name_eq_getElem hfn_mem' rfl
  refine ⟨fn, Lambda.mem_get?_eq hs hget, ?_⟩
  rw [← hτ, ← ListMap.values_eq_map_snd]
  cases hv : fn.inputs.values with
  | nil => simp [LMonoTy.mkArrow']
  | cons ity irest =>
    show LMonoTy.mkArrow ity (irest ++ LMonoTy.destructArrow fn.output) = _
    -- `mkArrow ity (irest ++ destructArrow output) = mkArrow' output (ity :: irest)`
    have hspine : ArrowSpineOK fn.output := hwf fn hfn_mem
    clear hv hτ
    induction irest generalizing ity with
    | nil =>
      simp only [List.nil_append, LMonoTy.mkArrow'_cons, LMonoTy.mkArrow'_nil]
      exact Lambda.mkArrow_destructArrow fn.output hspine ity
    | cons a as ih =>
      rw [LMonoTy.mkArrow'_cons]
      show LMonoTy.arrow ity (LMonoTy.mkArrow a (as ++ LMonoTy.destructArrow fn.output)) = _
      rw [ih a]

-- ── Well-formedness of `pctx` and the factory ────────────────────────

/-- Well-formedness linking a polymorphic operator context `pctx` to the factory
    `F`: every `(name, lty)` in `pctx` is the polymorphic type scheme of some
    factory function `fn` (i.e. `lty = ∀ fn.typeArgs. mkArrow' fn.output fn.inputs.values`),
    and `F[name]? = some fn`.

    The final conjunct — every free type variable of the generic type is bound by
    `fn.typeArgs` — reflects Strata's real factory invariant `FuncWF`
    (`output_typevars_in_typeArgs`/`inputs_typevars_in_typeArgs`, see
    `Strata.DL.Util.Func`/`Strata.DL.Lambda.FactoryWF`). It is discharged for any
    parser-produced factory. It is *essential*: without it a *monomorphic* factory
    function (`typeArgs = []`) whose signature carries a free type variable (e.g.
    `g : α → α` with `typeArgs = []`, which no real `FuncWF` factory contains)
    would be admitted by `pctx`, reach the success branch of `polyOpsForResult`
    with a *ground* annotation `A ≠ genericTy`, yet — because `opTypeSubst`
    short-circuits to `some Subst.empty` for monomorphic functions —
    `GenOpsConsistent` would demand `A = genericTy`, which is false. The invariant
    rules this out: when `typeArgs = []` the generic type is ground, forcing
    `A = genericTy`. -/
def PCtxWF (F : @Factory LExprParams') (pctx : PolyOpCtx) : Prop :=
  ∀ (name : String) (lty : Lambda.LTy),
    (name, lty) ∈ pctx →
    ∃ (fn : LFunc LExprParams'), F[name]? = some fn ∧
      lty = .forAll fn.typeArgs (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)) ∧
      (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).freeVars ⊆ fn.typeArgs

/-- The factory is *output-well-formed* if every function's output type has a
    well-formed arrow spine. Real factories (built by the parser/type-checker)
    satisfy this; it is what `factoryOps_mem_char` needs. -/
def FactoryOutputWF (F : @Factory LExprParams') : Prop :=
  ∀ f : LFunc LExprParams', f ∈ F.toArray.toList → ArrowSpineOK f.output

-- ── Leaf-op consistency (`pickOp`) ───────────────────────────────────

/-- Membership in `opsOfType octx τ` implies `(name, τ) ∈ octx`. -/
theorem mem_opsOfType (octx : OpCtx) (τ : LMonoTy) (name : String)
    (h : name ∈ opsOfType octx τ) : (name, τ) ∈ octx := by
  unfold opsOfType at h
  simp only [List.mem_filterMap] at h
  obtain ⟨⟨x, ty⟩, hmem, heq⟩ := h
  split at heq
  · rename_i hty; simp only [Option.some.injEq] at heq
    have : ty = τ := beq_iff_eq.mp hty
    subst this; subst heq; exact hmem
  · simp at heq

/-- An op node emitted by `pickOp` on `factoryOps F` is `GenOpsConsistent`. The
    annotation `τ` equals the operator's generic factory type, so
    `opGeneric_opsConsistent` applies. -/
theorem pickOp_opsConsistent (F : @Factory LExprParams') (τ : LMonoTy) (name : String)
    (hFwf : FactoryOutputWF F)
    (hmem : name ∈ opsOfType (factoryOps F) τ) :
    Lambda.GenOpsConsistent F (.op () ⟨name, ()⟩ (some τ)) := by
  have hoctx : (name, τ) ∈ factoryOps F := mem_opsOfType _ _ _ hmem
  obtain ⟨fn, hget, hτ⟩ := factoryOps_mem_char F name τ hFwf hoctx
  subst hτ
  exact Lambda.opGeneric_opsConsistent F fn () ⟨name, ()⟩ hget

-- ── GenOpsConsistent structural unfolding (via faithful) ─────────────

@[simp] theorem gopc_const (F : @Factory LExprParams') (m) (c) :
    Lambda.GenOpsConsistent F (.const m c) := by
  show Lambda.GenOpsConsistent F (.const m c); unfold Lambda.GenOpsConsistent; trivial

@[simp] theorem gopc_boolConst (F : @Factory LExprParams') (m) (b) :
    Lambda.GenOpsConsistent F (.boolConst m b) := by
  unfold LExpr.boolConst; exact gopc_const F m _

@[simp] theorem gopc_intConst (F : @Factory LExprParams') (m) (k) :
    Lambda.GenOpsConsistent F (.intConst m k) := by
  unfold LExpr.intConst; exact gopc_const F m _

@[simp] theorem gopc_strConst (F : @Factory LExprParams') (m) (str) :
    Lambda.GenOpsConsistent F (.strConst m str) := by
  unfold LExpr.strConst; exact gopc_const F m _

@[simp] theorem gopc_realConst (F : @Factory LExprParams') (m) (r) :
    Lambda.GenOpsConsistent F (.realConst m r) := by
  unfold LExpr.realConst; exact gopc_const F m _

@[simp] theorem gopc_bitvecConst (F : @Factory LExprParams') (m) (w) (v) :
    Lambda.GenOpsConsistent F (.bitvecConst m w v) := by
  unfold LExpr.bitvecConst; exact gopc_const F m _

@[simp] theorem gopc_bvar (F : @Factory LExprParams') (m) (i) :
    Lambda.GenOpsConsistent F (.bvar m i) := by
  unfold Lambda.GenOpsConsistent; trivial

@[simp] theorem gopc_fvar (F : @Factory LExprParams') (m) (x) (ty) :
    Lambda.GenOpsConsistent F (.fvar m x ty) := by
  unfold Lambda.GenOpsConsistent; trivial

@[simp] theorem gopc_app (F : @Factory LExprParams') (m) (fn arg : LExpr') :
    Lambda.GenOpsConsistent F (.app m fn arg) ↔
      Lambda.GenOpsConsistent F fn ∧ Lambda.GenOpsConsistent F arg := by
  rw [show Lambda.GenOpsConsistent F (.app m fn arg)
        = (Lambda.GenOpsConsistent F fn ∧ Lambda.GenOpsConsistent F arg) from rfl]

@[simp] theorem gopc_abs (F : @Factory LExprParams') (m) (nm) (aty) (body : LExpr') :
    Lambda.GenOpsConsistent F (.abs m nm aty body) ↔ Lambda.GenOpsConsistent F body := by
  rw [show Lambda.GenOpsConsistent F (.abs m nm aty body)
        = Lambda.GenOpsConsistent F body from rfl]

@[simp] theorem gopc_ite (F : @Factory LExprParams') (m) (c t e : LExpr') :
    Lambda.GenOpsConsistent F (.ite m c t e) ↔
      Lambda.GenOpsConsistent F c ∧ Lambda.GenOpsConsistent F t ∧ Lambda.GenOpsConsistent F e := by
  rw [show Lambda.GenOpsConsistent F (.ite m c t e)
        = (Lambda.GenOpsConsistent F c ∧ Lambda.GenOpsConsistent F t ∧ Lambda.GenOpsConsistent F e) from rfl]

@[simp] theorem gopc_eq (F : @Factory LExprParams') (m) (e₁ e₂ : LExpr') :
    Lambda.GenOpsConsistent F (.eq m e₁ e₂) ↔
      Lambda.GenOpsConsistent F e₁ ∧ Lambda.GenOpsConsistent F e₂ := by
  rw [show Lambda.GenOpsConsistent F (.eq m e₁ e₂)
        = (Lambda.GenOpsConsistent F e₁ ∧ Lambda.GenOpsConsistent F e₂) from rfl]

@[simp] theorem gopc_quant (F : @Factory LExprParams') (m) (k) (nm) (qty) (tr body : LExpr') :
    Lambda.GenOpsConsistent F (.quant m k nm qty tr body) ↔
      Lambda.GenOpsConsistent F tr ∧ Lambda.GenOpsConsistent F body := by
  rw [show Lambda.GenOpsConsistent F (.quant m k nm qty tr body)
        = (Lambda.GenOpsConsistent F tr ∧ Lambda.GenOpsConsistent F body) from rfl]

-- ── Public support characterizations for pick* (mirror private ones) ──

private theorem list_map_ne_nil_of_length_pos' {α β : Type} {xs : List α} {f : α → β}
    (h : xs.length > 0) : xs.map f ≠ [] := by
  intro heq
  have : (xs.map f).length = 0 := by rw [heq]; rfl
  rw [List.length_map] at this; omega

theorem mem_support_pickOp_iff' {octx : OpCtx} {τ : LMonoTy}
    {hv : (opsOfType octx τ).length > 0} {e : LExpr'} :
    e ∈ (pickOp (G := SetGen.Set) octx τ hv) ↔
      ∃ name ∈ opsOfType octx τ, e = .op () ⟨name, ()⟩ (some τ) := by
  change e ∈ SetGen.support (pickOp (G := SetGen.Set) octx τ hv) ↔ _
  simp only [pickOp, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv), List.mem_map]
  constructor
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩
  · rintro ⟨name, hmem, rfl⟩; exact ⟨name, hmem, rfl⟩

/-- Any op node produced by `pickOp` on `factoryOps F` is `GenOpsConsistent`. -/
theorem pickOp_mem_opsConsistent (F : @Factory LExprParams') (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) {hv : (opsOfType (factoryOps F) τ).length > 0} {e : LExpr'}
    (he : e ∈ (pickOp (G := SetGen.Set) (factoryOps F) τ hv)) :
    Lambda.GenOpsConsistent F e := by
  rw [mem_support_pickOp_iff'] at he
  obtain ⟨name, hmem, rfl⟩ := he
  exact pickOp_opsConsistent F τ name hFwf hmem


/-- Any node produced by `pickBVar` is a `.bvar`, hence `GenOpsConsistent`. -/
theorem pickBVar_mem_opsConsistent (F : @Factory LExprParams') (bctx : BVarCtx) (τ : LMonoTy)
    {hv : (bvarsOfType bctx τ).length > 0} {e : LExpr'}
    (he : e ∈ (pickBVar (G := SetGen.Set) bctx τ hv)) :
    Lambda.GenOpsConsistent F e := by
  change e ∈ SetGen.support (pickBVar (G := SetGen.Set) bctx τ hv) at he
  simp only [pickBVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv),
    List.mem_map] at he
  obtain ⟨i, _, rfl⟩ := he
  simp

/-- Any node produced by `pickFVar` is a `.fvar`, hence `GenOpsConsistent`. -/
theorem pickFVar_mem_opsConsistent (F : @Factory LExprParams') (fctx : FVarCtx) (τ : LMonoTy)
    {hv : (fvarsOfType fctx τ).length > 0} {e : LExpr'}
    (he : e ∈ (pickFVar (G := SetGen.Set) fctx τ hv)) :
    Lambda.GenOpsConsistent F e := by
  change e ∈ SetGen.support (pickFVar (G := SetGen.Set) fctx τ hv) at he
  simp only [pickFVar, mem_support_elements_iff (list_map_ne_nil_of_length_pos' hv),
    List.mem_map] at he
  obtain ⟨name, _, rfl⟩ := he
  simp

private theorem norm_bool' : LMonoTy.bool = LMonoTy.tcons "bool" [] := rfl
private theorem norm_int' : LMonoTy.int = LMonoTy.tcons "int" [] := rfl
private theorem norm_string' : LMonoTy.string = LMonoTy.tcons "string" [] := rfl
private theorem norm_real' : LMonoTy.real = LMonoTy.tcons "real" [] := rfl
private theorem norm_arrow' (τ₁ τ₂ : LMonoTy) :
    LMonoTy.arrow τ₁ τ₂ = LMonoTy.tcons "arrow" [τ₁, τ₂] := rfl

set_option maxHeartbeats 1600000 in
theorem genLExprBase_opsConsistent (F : @Factory LExprParams') (fctx : FVarCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (e : LExpr')
    (hFwf : FactoryOutputWF F)
    (he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx depth τ)) :
    Lambda.GenOpsConsistent F e := by
  rw [genLExprBase.eq_def] at he
  split at he
  case h_1 τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 (.arrow τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_arrow'] at he
    simp only [genLExprBase, pick_mem_iff, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, h⟩) | ((⟨hf, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩))
    · exact pickBVar_mem_opsConsistent F bctx (.arrow τ₁ τ₂) h
    · exact h.elim
    · exact pickFVar_mem_opsConsistent F fctx (.arrow τ₁ τ₂) h
    · exact h.elim
    · exact pickOp_mem_opsConsistent F (.arrow τ₁ τ₂) hFwf h
    · exact h.elim
  case h_3 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 .bool) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_bool'] at he
    simp only [genLExprBase, pick_mem_iff, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (rfl | rfl) | ((⟨_, h⟩ | ⟨_, rfl | rfl⟩) | ((⟨hf, h⟩ | ⟨_, rfl | rfl⟩) | (⟨_, h⟩ | ⟨_, rfl | rfl⟩)))
    · simp
    · simp
    · exact pickBVar_mem_opsConsistent F bctx .bool h
    · simp
    · simp
    · exact pickFVar_mem_opsConsistent F fctx .bool h
    · simp
    · simp
    · exact pickOp_mem_opsConsistent F .bool hFwf h
    · simp
    · simp
  case h_5 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 .int) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_int'] at he
    simp only [genLExprBase, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩)))
    · simp
    · simp
    · exact pickBVar_mem_opsConsistent F bctx .int h
    · simp
    · simp
    · exact pickFVar_mem_opsConsistent F fctx .int h
    · simp
    · simp
    · exact pickOp_mem_opsConsistent F .int hFwf h
    · simp
    · simp
  case h_9 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 .string) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_string'] at he
    simp only [genLExprBase, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨k, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)))
    · simp
    · exact pickBVar_mem_opsConsistent F bctx .string h
    · simp
    · exact pickFVar_mem_opsConsistent F fctx .string h
    · simp
    · exact pickOp_mem_opsConsistent F .string hFwf h
    · simp
  case h_11 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 .real) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_real'] at he
    simp only [genLExprBase, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨num, _, den, _, rfl⟩ | ⟨num, _, den, _, rfl⟩) | ((⟨_, h⟩ | ⟨_, (⟨num, _, den, _, rfl⟩ | ⟨num, _, den, _, rfl⟩)⟩) | ((⟨hf, h⟩ | ⟨_, (⟨num, _, den, _, rfl⟩ | ⟨num, _, den, _, rfl⟩)⟩) | (⟨_, h⟩ | ⟨_, (⟨num, _, den, _, rfl⟩ | ⟨num, _, den, _, rfl⟩)⟩)))
    · simp
    · simp
    · exact pickBVar_mem_opsConsistent F bctx .real h
    · simp
    · simp
    · exact pickFVar_mem_opsConsistent F fctx .real h
    · simp
    · simp
    · exact pickOp_mem_opsConsistent F .real hFwf h
    · simp
    · simp
  case h_13 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 (.bitvec n)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure,
      mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨k, _, rfl⟩ | ((⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | ((⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)))
    · simp
    · exact pickBVar_mem_opsConsistent F bctx (.bitvec n) h
    · simp
    · exact pickFVar_mem_opsConsistent F fctx (.bitvec n) h
    · simp
    · exact pickOp_mem_opsConsistent F (.bitvec n) hFwf h
    · simp
  case h_4 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) .bool) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_bool'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genBoolConst (G := SetGen.Set)),
         (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) .bool),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .bool)),
         (2, fun () => genEq (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n)),
         (2, fun () => genQuant .all (genLMonoTy tvars n)
           (fun τ' => genLExprBase fctx (factoryOps F) tvars (τ' :: bctx) n)
           (fun τ' => genLExprBase fctx (factoryOps F) tvars (τ' :: bctx) n .bool)),
         (2, fun () => genQuant .exist (genLMonoTy tvars n)
           (fun τ' => genLExprBase fctx (factoryOps F) tvars (τ' :: bctx) n)
           (fun τ' => genLExprBase fctx (factoryOps F) tvars (τ' :: bctx) n .bool)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .bool).length > 0 then pickBVar bctx .bool hv
           else genBoolConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .bool).length > 0 then pickFVar fctx .bool hf
           else genBoolConst),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .bool).length > 0 then pickOp (factoryOps F) .bool ho
           else genBoolConst) ]
      ) (by show 0 < 1+4+2+2+2+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genBoolConst, genApp, genIte, genEq, genQuant, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with rfl | rfl <;> simp
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · obtain ⟨τ', hτ'm, e₁, he₁, e₂, he₂, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he₁,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he₂⟩
    · obtain ⟨τ', hτ'm, τ_tr, hτ_tr_m, tr, htr, body, hbody, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars (τ' :: bctx) n _ _ hFwf htr,
        genLExprBase_opsConsistent F fctx tvars (τ' :: bctx) n _ _ hFwf hbody⟩
    · obtain ⟨τ', hτ'm, τ_tr, hτ_tr_m, tr, htr, body, hbody, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars (τ' :: bctx) n _ _ hFwf htr,
        genLExprBase_opsConsistent F fctx tvars (τ' :: bctx) n _ _ hFwf hbody⟩
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickBVar_mem_opsConsistent F bctx .bool h
      · simp
      · simp
    · rcases he with ⟨hf, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickFVar_mem_opsConsistent F fctx .bool h
      · simp
      · simp
    · rcases he with ⟨_, h⟩ | ⟨_, rfl | rfl⟩
      · exact pickOp_mem_opsConsistent F .bool hFwf h
      · simp
      · simp
  case h_6 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) .int) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_int'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genIntConst (G := SetGen.Set)),
         (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) .int),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .int)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .int)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .int).length > 0 then pickBVar bctx .int hv
           else genIntConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .int).length > 0 then pickFVar fctx .int hf
           else genIntConst),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .int).length > 0 then pickOp (factoryOps F) .int ho
           else genIntConst) ]
      ) (by show 0 < 1+4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genIntConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩ <;> simp
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickBVar_mem_opsConsistent F bctx .int h
      · simp
      · simp
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickFVar_mem_opsConsistent F fctx .int h
      · simp
      · simp
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩⟩
      · exact pickOp_mem_opsConsistent F .int hFwf h
      · simp
      · simp
  case h_10 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) .string) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_string'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genStrConst (G := SetGen.Set)),
         (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) .string),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .string)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .string)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .string).length > 0 then pickBVar bctx .string hv
           else genStrConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .string).length > 0 then pickFVar fctx .string hf
           else genStrConst),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .string).length > 0 then pickOp (factoryOps F) .string ho
           else genStrConst) ]
      ) (by show 0 < 1+4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genStrConst, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨s, _, rfl⟩ := he; simp
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickBVar_mem_opsConsistent F bctx .string h
      · simp
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickFVar_mem_opsConsistent F fctx .string h
      · simp
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨s, _, rfl⟩⟩
      · exact pickOp_mem_opsConsistent F .string hFwf h
      · simp
  case h_12 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) .real) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_real'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genRealConst (G := SetGen.Set)),
         (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) .real),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .real)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .real)),
         (2, fun () =>
           if hv : (bvarsOfType bctx .real).length > 0 then pickBVar bctx .real hv
           else genRealConst),
         (2, fun () =>
           if hf : (fvarsOfType fctx .real).length > 0 then pickFVar fctx .real hf
           else genRealConst),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) .real).length > 0 then pickOp (factoryOps F) .real ho
           else genRealConst) ]
      ) (by show 0 < 1+4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genRealConst, genApp, genIte, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · rcases he with ⟨num, _, den, _, rfl⟩ | ⟨num, _, den, _, rfl⟩ <;> simp
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨num, _, den, _, rfl⟩ | ⟨num, _, den, _, rfl⟩⟩
      · exact pickBVar_mem_opsConsistent F bctx .real h
      · simp
      · simp
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨num, _, den, _, rfl⟩ | ⟨num, _, den, _, rfl⟩⟩
      · exact pickFVar_mem_opsConsistent F fctx .real h
      · simp
      · simp
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨num, _, den, _, rfl⟩ | ⟨num, _, den, _, rfl⟩⟩
      · exact pickOp_mem_opsConsistent F .real hFwf h
      · simp
      · simp
  case h_14 m n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (m + 1) (.bitvec n)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (1, fun () => genBitvecConst (G := SetGen.Set) n),
         (4, fun () => genApp (genLMonoTy tvars m) (genLExprBase fctx (factoryOps F) tvars bctx m) (.bitvec n)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx m .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx m (.bitvec n))
                              (genLExprBase fctx (factoryOps F) tvars bctx m (.bitvec n))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.bitvec n)).length > 0 then pickBVar bctx (.bitvec n) hv
           else genBitvecConst n),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.bitvec n)).length > 0 then pickFVar fctx (.bitvec n) hf
           else genBitvecConst n),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) (.bitvec n)).length > 0 then pickOp (factoryOps F) (.bitvec n) ho
           else genBitvecConst n) ]
      ) (by show 0 < 1+4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genBitvecConst, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨k, _, rfl⟩ := he; simp
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx m _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx m _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx m _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx m _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx m _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickBVar_mem_opsConsistent F bctx (.bitvec n) h
      · simp
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickFVar_mem_opsConsistent F fctx (.bitvec n) h
      · simp
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩
      · exact pickOp_mem_opsConsistent F (.bitvec n) hFwf h
      · simp
  case h_2 n τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) (.arrow τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    rw [norm_arrow'] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (4, fun () => genAbs (G := SetGen.Set) (genLExprBase fctx (factoryOps F) tvars (τ₁ :: bctx) n τ₂) τ₁),
         (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) (.arrow τ₁ τ₂)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n (.arrow τ₁ τ₂))
                              (genLExprBase fctx (factoryOps F) tvars bctx n (.arrow τ₁ τ₂))),
         (2, fun () =>
           if hv : (bvarsOfType bctx (.arrow τ₁ τ₂)).length > 0 then pickBVar bctx (.arrow τ₁ τ₂) hv
           else genAbs (genLExprBase fctx (factoryOps F) tvars (τ₁ :: bctx) n τ₂) τ₁),
         (2, fun () =>
           if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0 then pickFVar fctx (.arrow τ₁ τ₂) hf
           else genAbs (genLExprBase fctx (factoryOps F) tvars (τ₁ :: bctx) n τ₂) τ₁),
         (2, fun () =>
           if ho : (opsOfType (factoryOps F) (.arrow τ₁ τ₂)).length > 0 then pickOp (factoryOps F) (.arrow τ₁ τ₂) ho
           else genAbs (genLExprBase fctx (factoryOps F) tvars (τ₁ :: bctx) n τ₂) τ₁) ]
      ) (by show 0 < 4+4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genAbs, genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    · obtain ⟨body, hbody, rfl⟩ := he
      rw [gopc_abs]
      exact genLExprBase_opsConsistent F fctx tvars (τ₁ :: bctx) n _ _ hFwf hbody
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickBVar_mem_opsConsistent F bctx (.arrow τ₁ τ₂) h
      · rw [gopc_abs]
        exact genLExprBase_opsConsistent F fctx tvars (τ₁ :: bctx) n _ _ hFwf hbody
    · rcases he with ⟨hf, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickFVar_mem_opsConsistent F fctx (.arrow τ₁ τ₂) h
      · rw [gopc_abs]
        exact genLExprBase_opsConsistent F fctx tvars (τ₁ :: bctx) n _ _ hFwf hbody
    · rcases he with ⟨_, h⟩ | ⟨_, body, hbody, rfl⟩
      · exact pickOp_mem_opsConsistent F (.arrow τ₁ τ₂) hFwf h
      · rw [gopc_abs]
        exact genLExprBase_opsConsistent F fctx tvars (τ₁ :: bctx) n _ _ hFwf hbody
  case h_7 name =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 (.ftvar name)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · exact pickBVar_mem_opsConsistent F bctx (.ftvar name) h
    · exact pickFVar_mem_opsConsistent F fctx (.ftvar name) h
    · exact pickOp_mem_opsConsistent F (.ftvar name) hFwf h
    · exact absurd h (by simp)
    · exact pickFVar_mem_opsConsistent F fctx (.ftvar name) h
    · exact pickBVar_mem_opsConsistent F bctx (.ftvar name) h
    · exact pickOp_mem_opsConsistent F (.ftvar name) hFwf h
    · exact absurd h (by simp)
    · exact pickOp_mem_opsConsistent F (.ftvar name) hFwf h
    · exact pickBVar_mem_opsConsistent F bctx (.ftvar name) h
    · exact pickFVar_mem_opsConsistent F fctx (.ftvar name) h
    · exact absurd h (by simp)
  case h_8 n name =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) (.ftvar name)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (4, fun () => genApp (G := SetGen.Set) (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) (.ftvar name)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n (.ftvar name))
                              (genLExprBase fctx (factoryOps F) tvars bctx n (.ftvar name))),
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
           else default) ]
      ) (by show 0 < 4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · exact pickBVar_mem_opsConsistent F bctx (.ftvar name) h
      · exact pickFVar_mem_opsConsistent F fctx (.ftvar name) h
      · exact pickOp_mem_opsConsistent F (.ftvar name) hFwf h
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickFVar_mem_opsConsistent F fctx (.ftvar name) h
      · exact pickBVar_mem_opsConsistent F bctx (.ftvar name) h
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickOp_mem_opsConsistent F (.ftvar name) hFwf h
      · exact pickBVar_mem_opsConsistent F bctx (.ftvar name) h
      · exact absurd h (by simp)
  case h_15 =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 .regex) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · exact pickBVar_mem_opsConsistent F bctx .regex h
    · exact pickFVar_mem_opsConsistent F fctx .regex h
    · exact pickOp_mem_opsConsistent F .regex hFwf h
    · exact absurd h (by simp)
    · exact pickFVar_mem_opsConsistent F fctx .regex h
    · exact pickBVar_mem_opsConsistent F bctx .regex h
    · exact pickOp_mem_opsConsistent F .regex hFwf h
    · exact absurd h (by simp)
    · exact pickOp_mem_opsConsistent F .regex hFwf h
    · exact pickBVar_mem_opsConsistent F bctx .regex h
    · exact pickFVar_mem_opsConsistent F fctx .regex h
    · exact absurd h (by simp)
  case h_16 n =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) .regex) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (4, fun () => genApp (G := SetGen.Set) (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) .regex),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .regex)
                              (genLExprBase fctx (factoryOps F) tvars bctx n .regex)),
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
           else default) ]
      ) (by show 0 < 4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · exact pickBVar_mem_opsConsistent F bctx .regex h
      · exact pickFVar_mem_opsConsistent F fctx .regex h
      · exact pickOp_mem_opsConsistent F .regex hFwf h
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickFVar_mem_opsConsistent F fctx .regex h
      · exact pickBVar_mem_opsConsistent F bctx .regex h
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickOp_mem_opsConsistent F .regex hFwf h
      · exact pickBVar_mem_opsConsistent F bctx .regex h
      · exact absurd h (by simp)
  case h_17 τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 (.map τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · exact pickBVar_mem_opsConsistent F bctx (.map τ₁ τ₂) h
    · exact pickFVar_mem_opsConsistent F fctx (.map τ₁ τ₂) h
    · exact pickOp_mem_opsConsistent F (.map τ₁ τ₂) hFwf h
    · exact absurd h (by simp)
    · exact pickFVar_mem_opsConsistent F fctx (.map τ₁ τ₂) h
    · exact pickBVar_mem_opsConsistent F bctx (.map τ₁ τ₂) h
    · exact pickOp_mem_opsConsistent F (.map τ₁ τ₂) hFwf h
    · exact absurd h (by simp)
    · exact pickOp_mem_opsConsistent F (.map τ₁ τ₂) hFwf h
    · exact pickBVar_mem_opsConsistent F bctx (.map τ₁ τ₂) h
    · exact pickFVar_mem_opsConsistent F fctx (.map τ₁ τ₂) h
    · exact absurd h (by simp)
  case h_18 n τ₁ τ₂ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) (.map τ₁ τ₂)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (4, fun () => genApp (G := SetGen.Set) (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) (.map τ₁ τ₂)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n (.map τ₁ τ₂))
                              (genLExprBase fctx (factoryOps F) tvars bctx n (.map τ₁ τ₂))),
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
           else default) ]
      ) (by show 0 < 4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · exact pickBVar_mem_opsConsistent F bctx (.map τ₁ τ₂) h
      · exact pickFVar_mem_opsConsistent F fctx (.map τ₁ τ₂) h
      · exact pickOp_mem_opsConsistent F (.map τ₁ τ₂) hFwf h
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickFVar_mem_opsConsistent F fctx (.map τ₁ τ₂) h
      · exact pickBVar_mem_opsConsistent F bctx (.map τ₁ τ₂) h
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickOp_mem_opsConsistent F (.map τ₁ τ₂) hFwf h
      · exact pickBVar_mem_opsConsistent F bctx (.map τ₁ τ₂) h
      · exact absurd h (by simp)
  case h_19 τ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx 0 (.seq τ)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase, pick_mem_iff, mem_support_iff, SetGen.mem_dite,
               bot_mem_iff] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
      ((⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩) |
       (⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, h⟩⟩⟩))
    · exact pickBVar_mem_opsConsistent F bctx (.seq τ) h
    · exact pickFVar_mem_opsConsistent F fctx (.seq τ) h
    · exact pickOp_mem_opsConsistent F (.seq τ) hFwf h
    · exact absurd h (by simp)
    · exact pickFVar_mem_opsConsistent F fctx (.seq τ) h
    · exact pickBVar_mem_opsConsistent F bctx (.seq τ) h
    · exact pickOp_mem_opsConsistent F (.seq τ) hFwf h
    · exact absurd h (by simp)
    · exact pickOp_mem_opsConsistent F (.seq τ) hFwf h
    · exact pickBVar_mem_opsConsistent F bctx (.seq τ) h
    · exact pickFVar_mem_opsConsistent F fctx (.seq τ) h
    · exact absurd h (by simp)
  case h_20 n τ =>
    replace he : e ∈ SetGen.support (genLExprBase (G := SetGen.Set) fctx (factoryOps F) tvars bctx (n + 1) (.seq τ)) := by
      rw [genLExprBase.eq_def]; exact he
    simp only [genLExprBase] at he
    have hfreq : e ∈ SetGen.support (frequency
      ([ (4, fun () => genApp (G := SetGen.Set) (genLMonoTy tvars n) (genLExprBase fctx (factoryOps F) tvars bctx n) (.seq τ)),
         (2, fun () => genIte (genLExprBase fctx (factoryOps F) tvars bctx n .bool)
                              (genLExprBase fctx (factoryOps F) tvars bctx n (.seq τ))
                              (genLExprBase fctx (factoryOps F) tvars bctx n (.seq τ))),
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
           else default) ]
      ) (by show 0 < 4+2+2+2+2; omega)) := he
    rw [mem_support_frequency_iff] at hfreq
    obtain ⟨_, g, hg, _, he⟩ := hfreq
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [genApp, genIte, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite, bot_mem_iff] at he
    · obtain ⟨τ', hτ'm, arg, harg, fn, hfn, rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hfn,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf harg⟩
    · obtain ⟨c, hc, t, ht, e', he', rfl⟩ := he
      exact ⟨genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf hc,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf ht,
        genLExprBase_opsConsistent F fctx tvars bctx n _ _ hFwf he'⟩
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩⟩
      · exact pickBVar_mem_opsConsistent F bctx (.seq τ) h
      · exact pickFVar_mem_opsConsistent F fctx (.seq τ) h
      · exact pickOp_mem_opsConsistent F (.seq τ) hFwf h
      · exact absurd h (by simp)
    · rcases he with ⟨hf, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickFVar_mem_opsConsistent F fctx (.seq τ) h
      · exact pickBVar_mem_opsConsistent F bctx (.seq τ) h
      · exact absurd h (by simp)
    · rcases he with ⟨_, h⟩ | ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact pickOp_mem_opsConsistent F (.seq τ) hFwf h
      · exact pickBVar_mem_opsConsistent F bctx (.seq τ) h
      · exact absurd h (by simp)
  case h_21 =>
    simp only [mem_support_iff, SetGen.Set.mem_pure] at he; subst he; simp
  termination_by depth
  decreasing_by all_goals simp_wf; omega


-- ── mkApps and mapM-argument consistency ─────────────────────────────

/-- `mkApps` of a `GenOpsConsistent` base and `GenOpsConsistent` args is
    `GenOpsConsistent` (the op consistency propagates structurally through the
    left-nested applications). -/
theorem mkApps_opsConsistent (F : @Factory LExprParams') (base : LExpr') (args : List LExpr')
    (hbase : Lambda.GenOpsConsistent F base)
    (hargs : ∀ a ∈ args, Lambda.GenOpsConsistent F a) :
    Lambda.GenOpsConsistent F (mkApps base args) := by
  induction args generalizing base with
  | nil => simpa [mkApps] using hbase
  | cons a rest ih =>
    simp only [mkApps, List.foldl_cons]
    apply ih
    · rw [gopc_app]; exact ⟨hbase, hargs a (by simp)⟩
    · intro x hx; exact hargs x (by simp [hx])

/-- Every argument produced by `mapM (genLExprBase fctx (factoryOps F) …)` is
    `GenOpsConsistent`. -/
theorem mapM_genLExprBase_opsConsistent (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (hFwf : FactoryOutputWF F)
    (argTys : List LMonoTy) (args : List LExpr')
    (hargs : args ∈ (List.mapM (m := SetGen.Set)
      (genLExprBase fctx (factoryOps F) tvars bctx depth) argTys)) :
    ∀ a ∈ args, Lambda.GenOpsConsistent F a := by
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
    · exact genLExprBase_opsConsistent F fctx tvars bctx depth σ a hFwf hx
    · exact ih tl htl a ha

-- ── Monomorphic Indir op-node consistency ────────────────────────────

/-- Public version of `findOpsInCtx` membership: an entry `(name, argTys)`
    corresponds to an octx entry with the reconstructed curried type. -/
theorem findOpsInCtx_mem' {octx : OpCtx} {τ : LMonoTy}
    {name : String} {argTys : List LMonoTy}
    (h : (name, argTys) ∈ findOpsInCtx octx τ) :
    (name, argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) ∈ octx ∧ argTys ≠ [] := by
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
    curried type from `findOpsInCtx (factoryOps F) τ`) is `GenOpsConsistent`. -/
theorem indir_op_opsConsistent (F : @Factory LExprParams') (τ : LMonoTy)
    (name : String) (argTys : List LMonoTy) (hFwf : FactoryOutputWF F)
    (hmem : (name, argTys) ∈ findOpsInCtx (factoryOps F) τ) :
    Lambda.GenOpsConsistent F
      (.op () ⟨name, ()⟩ (some (argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ))) := by
  obtain ⟨hoctx, _⟩ := findOpsInCtx_mem' hmem
  obtain ⟨fn, hget, hty⟩ := factoryOps_mem_char F name _ hFwf hoctx
  rw [hty]
  exact Lambda.opGeneric_opsConsistent F fn () ⟨name, ()⟩ hget

-- ── Polymorphic IndirPoly op-node consistency ────────────────────────

/-- The assumption that every polymorphic-operator annotation `genIndirPoly`
    can emit for target `τ` is `GenOpsConsistent`: for every candidate
    `(name, concreteArgTys)` in `polyOpsForResult pctx τ generableTys sampledTys`,
    the op node annotated with `concreteArgTys.foldr arrow τ` is consistent.

    **This predicate is now fully PROVEN** — see `PolyOpsConsistent_of_PCtxWF`,
    which derives it from `PCtxWF F pctx` (a factory-well-formedness condition
    discharged for any real factory). It is kept as an explicit hypothesis on the
    general `genIndirPoly_opsConsistent`/`genLExpr_opsConsistent` below only so
    those theorems stay maximally general; the unconditional top-level result is
    `genLExpr_opsConsistent_of_PCtxWF`.

    The proof rests on two facts: (1) the *ground-only* instantiation fix in
    `polyOpsForResult` (see `docs/ops-consistent-polymorphic-gap.md`) makes every
    emitted annotation *ground*, hence a genuine instance of the operator's generic
    type; and (2) `unify_ground_instance` (in `StrataGenerators/UnifyGroundInstance.lean`)
    — a from-scratch proof of unification completeness for ground matching, which
    Strata itself does not provide — shows `LFunc.opTypeSubst` then succeeds and
    reconstructs the annotation. The earlier counterexample (`id : ∀α. α → α` at
    target `.ftvar "β"` producing the incoherent `β → β`) is no longer generated:
    that candidate is dropped because `β → β` is non-ground.

    It holds vacuously when `pctx = []` (see the `…_nil` results, which need no
    such assumption). -/
def PolyOpsConsistent (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (bctx : BVarCtx) (fctx : FVarCtx) (τ : LMonoTy) : Prop :=
  ∀ (sampledTys : List LMonoTy) (name : String) (concreteArgTys : List LMonoTy),
    (name, concreteArgTys) ∈
      polyOpsForResult pctx τ (generableTypesFromCtx bctx fctx (factoryOps F)) sampledTys →
    Lambda.GenOpsConsistent F
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

/-- Free variables of a right-nested arrow fold: the flattened arg free vars
    followed by the return type's free vars. -/
theorem freeVars_foldr_arrow (l : List LMonoTy) (t : LMonoTy) :
    (l.foldr (fun σ acc => LMonoTy.arrow σ acc) t).freeVars
      = l.flatMap LMonoTy.freeVars ++ t.freeVars := by
  have harrow : ∀ x y : LMonoTy, (LMonoTy.arrow x y).freeVars = x.freeVars ++ y.freeVars := by
    intro x y; simp [LMonoTy.arrow, LMonoTy.freeVars, LMonoTys.freeVars]
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.foldr_cons, List.flatMap_cons, List.append_assoc]
    show (LMonoTy.arrow a (as.foldr (fun σ acc => LMonoTy.arrow σ acc) t)).freeVars = _
    rw [harrow, ih]

/-- Substitution distributes over a right-nested arrow fold. -/
theorem subst_foldr_arrow (S : Lambda.Subst) (l : List LMonoTy) (t : LMonoTy) :
    LMonoTy.subst S (l.foldr (fun σ acc => LMonoTy.arrow σ acc) t)
      = (l.map (LMonoTy.subst S)).foldr (fun σ acc => LMonoTy.arrow σ acc)
          (LMonoTy.subst S t) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [LMonoTy.arrow, LMonoTy.subst_tcons]
    show LMonoTy.tcons "arrow"
        (LMonoTys.subst S [a, as.foldr (fun σ acc => LMonoTy.arrow σ acc) t]) = _
    rw [LMonoTys.subst_eq_substLogic]
    by_cases hS : Subst.hasEmptyScopes S
    · simp only [LMonoTys.substLogic_emptyS hS, LMonoTy.subst_emptyS hS]
      simp only [LMonoTy.subst_emptyS hS] at ih
      rw [ih]; rfl
    · simp only [LMonoTys.substLogic, hS, Bool.false_eq_true, ↓reduceIte]
      rw [ih]; rfl

/-- `LMonoTys.subst` is the pointwise `map` of `LMonoTy.subst` (public restatement,
    since Strata's `LMonoTys_subst_eq_map` lives in a `module` file). -/
theorem LMonoTys_subst_map (S : Lambda.Subst) (args : List LMonoTy) :
    LMonoTys.subst S args = args.map (LMonoTy.subst S) := by
  have h := LMonoTy.subst_unfold S (LMonoTy.tcons "x" args)
  rw [LMonoTy.subst_tcons] at h
  simp only at h
  injection h with _ hh

/-- Every free variable of `subst S mty` originates from some free variable `x` of
    `mty` via `subst S (.ftvar x)`. -/
theorem freeVars_subst_source (S : Lambda.Subst) :
    ∀ (mty : LMonoTy) (w : TyIdentifier), w ∈ LMonoTy.freeVars (LMonoTy.subst S mty) →
      ∃ x, x ∈ LMonoTy.freeVars mty ∧ w ∈ LMonoTy.freeVars (LMonoTy.subst S (.ftvar x)) := by
  intro mty
  by_cases hE : Subst.hasEmptyScopes S
  · intro w hw
    rw [LMonoTy.subst_emptyS hE] at hw
    exact ⟨w, hw, by rw [LMonoTy.subst_emptyS hE]; simp [LMonoTy.freeVars]⟩
  · have hEne : Subst.hasEmptyScopes S = false := Bool.eq_false_iff.mpr hE
    induction mty with
    | ftvar x => intro w hw; exact ⟨x, by simp [LMonoTy.freeVars], hw⟩
    | bitvec n => intro w hw; rw [LMonoTy.subst_bitvec] at hw; simp [LMonoTy.freeVars] at hw
    | tcons name args ih =>
      intro w hw
      rw [LMonoTy.subst_tcons] at hw
      simp only [LMonoTy.freeVars] at hw
      obtain ⟨ty', hty'mem, hty'w⟩ := LMonoTys.freeVars_exists hw
      rw [LMonoTys_subst_map] at hty'mem
      obtain ⟨ty, htymem, htyeq⟩ := List.mem_map.mp hty'mem
      obtain ⟨x, hxmem, hxw⟩ := ih ty htymem w (htyeq ▸ hty'w)
      exact ⟨x, by simp only [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset htymem hxmem, hxw⟩

/-- Substitution is monotone on free variables: if `v` is free in `mty`, then the
    image `subst S (.ftvar v)` contributes its free variables to `subst S mty`. -/
theorem freeVars_subst_ftvar_subset (S : Lambda.Subst) :
    ∀ (mty : LMonoTy) (v : TyIdentifier), v ∈ LMonoTy.freeVars mty →
      LMonoTy.freeVars (LMonoTy.subst S (.ftvar v)) ⊆ LMonoTy.freeVars (LMonoTy.subst S mty) := by
  intro mty
  by_cases hE : Subst.hasEmptyScopes S
  · intro v hv
    rw [LMonoTy.subst_emptyS hE, LMonoTy.subst_emptyS hE]
    intro w hw
    simp only [LMonoTy.freeVars, List.mem_singleton] at hw; subst hw; exact hv
  · have hEne : Subst.hasEmptyScopes S = false := Bool.eq_false_iff.mpr hE
    induction mty with
    | ftvar x =>
      intro v hv; simp only [LMonoTy.freeVars, List.mem_singleton] at hv; subst hv; exact fun _ h => h
    | bitvec n => intro v hv; simp [LMonoTy.freeVars] at hv
    | tcons name args ih =>
      intro v hv
      simp only [LMonoTy.freeVars] at hv
      obtain ⟨ty, htymem, hvty⟩ := LMonoTys.freeVars_exists hv
      refine (ih ty htymem v hvty).trans ?_
      rw [LMonoTy.subst_tcons]
      simp only [LMonoTy.freeVars]
      have : LMonoTy.subst S ty ∈ LMonoTys.subst S args := by
        rw [LMonoTys_subst_map]; exact List.mem_map_of_mem htymem
      exact LMonoTys.freeVars_mem_subset this

/-- The single-scope substitution that sends each free variable `v` of `P` to its
    image under the composite `subst T2 ∘ subst T1`. Because the composite maps
    every relevant variable to a *ground* type (when the composite result is
    ground), this single scope reconstructs the composite on `P` — and its
    well-formedness is trivial (all values ground ⇒ no key occurs in a value). -/
def composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst) : Lambda.SubstOne :=
  (LMonoTy.freeVars P).map (fun v => (v, LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))))

/-- Looking up a free variable `v` of `P` in `composeWitnessScope P T1 T2` returns
    its composite image. -/
theorem find?_composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst)
    (v : TyIdentifier) (hv : v ∈ LMonoTy.freeVars P) :
    Maps.find? [composeWitnessScope P T1 T2] v
      = some (LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))) := by
  unfold composeWitnessScope Maps.find?
  -- `Map.find?` over `l.map (fun v => (v, g v))` at a key `v ∈ l` returns `g v`.
  have key : ∀ (l : List TyIdentifier), v ∈ l →
      Map.find? (l.map (fun v => (v, LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))))) v
        = some (LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))) := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons w ws ih =>
      simp only [List.map_cons, Map.find?]
      by_cases hvw : w = v
      · subst hvw; simp
      · rw [if_neg hvw]
        rw [List.mem_cons] at hl
        rcases hl with h | h
        · exact absurd h.symm hvw
        · exact ih h
  rw [key (LMonoTy.freeVars P) hv]

/-- **Composite-to-single-scope collapse.** If `mty`'s free variables are all free
    variables of `P`, then applying the ground-valued single scope
    `composeWitnessScope P T1 T2` to `mty` equals applying the composite
    `subst T2 ∘ subst T1`. -/
theorem subst_composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst) :
    ∀ (mty : LMonoTy), (∀ v, v ∈ LMonoTy.freeVars mty → v ∈ LMonoTy.freeVars P) →
      LMonoTy.subst [composeWitnessScope P T1 T2] mty
        = LMonoTy.subst T2 (LMonoTy.subst T1 mty) := by
  intro mty hsub
  by_cases hE : Subst.hasEmptyScopes [composeWitnessScope P T1 T2]
  · -- Empty scope ⇒ `P` has no free variables ⇒ `mty` has none ⇒ both sides fixed.
    have hPnil : LMonoTy.freeVars P = [] := by
      cases hfv : LMonoTy.freeVars P with
      | nil => rfl
      | cons w ws =>
        exfalso
        change Subst.hasEmptyScopes [composeWitnessScope P T1 T2] = true at hE
        simp only [composeWitnessScope, hfv, List.map_cons, Subst.hasEmptyScopes,
          List.all_cons, Map.isEmpty] at hE
        simp at hE
    have hmtynil : ∀ v, v ∈ LMonoTy.freeVars mty → False := by
      intro v hv; have := hsub v hv; rw [hPnil] at this; simp at this
    rw [LMonoTy.subst_emptyS hE]
    rw [LMonoTy.subst_no_relevant_keys T1 mty (fun v hv _ => (hmtynil v hv).elim)]
    exact (LMonoTy.subst_no_relevant_keys T2 mty (fun v hv _ => (hmtynil v hv).elim)).symm
  · have hEne : Subst.hasEmptyScopes [composeWitnessScope P T1 T2] = false :=
      Bool.eq_false_iff.mpr hE
    induction mty with
    | ftvar v =>
      have hv := hsub v (by simp [LMonoTy.freeVars])
      rw [LMonoTy.subst]
      simp only [hEne, Bool.false_eq_true, ↓reduceIte]
      rw [find?_composeWitnessScope P T1 T2 v hv]
    | bitvec n => simp [LMonoTy.subst_bitvec]
    | tcons name args ih =>
      rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]
      congr 1
      rw [LMonoTys_subst_map, LMonoTys_subst_map, LMonoTys_subst_map, List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a ha (fun v hv => hsub v (by
        simp only [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset ha hv))

/-- **Ground-instance packaging.** If `A` is ground and equals the composite
    `subst T2 (subst T1 P)`, then there is a well-formed `SubstInfo S` with
    `A = subst S.subst P`. The witness is the ground-valued single scope
    `composeWitnessScope P T1 T2`; its `SubstWF` is trivial because every value is
    a *ground* subterm of `A` (`Subst.freeVars = []`). -/
theorem ground_composite_substInfo (A P : LMonoTy) (T1 T2 : Lambda.Subst)
    (hAg : A.freeVars = []) (hA : A = LMonoTy.subst T2 (LMonoTy.subst T1 P)) :
    ∃ S : SubstInfo, A = LMonoTy.subst S.subst P := by
  have hwf : SubstWF [composeWitnessScope P T1 T2] := by
    -- All values are ground, so `Subst.freeVars = []` and `SubstWF` holds.
    have hvals : Subst.freeVars [composeWitnessScope P T1 T2] = [] := by
      rw [Subst.freeVars, List.flatMap_eq_nil_iff]
      intro t ht
      -- `t` is a value of the scope, i.e. `subst T2 (subst T1 (ftvar v))` for some
      -- `v ∈ freeVars P`; it is a subterm-image inside the ground `A`.
      have hvalues : Maps.values [composeWitnessScope P T1 T2]
          = (LMonoTy.freeVars P).map (fun v => LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))) := by
        simp only [Maps.values, composeWitnessScope, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        induction (LMonoTy.freeVars P) with
        | nil => rfl
        | cons w ws ih => simp only [List.map_cons, Map.values]; rw [ih]
      rw [hvalues] at ht
      obtain ⟨v, hvmem, hvt⟩ := List.mem_map.mp ht
      -- The image `subst T2 (subst T1 (ftvar v))` is ground: its free vars are a
      -- subset of `A = subst T2 (subst T1 P)`'s free vars, which are [].
      have himg : (LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))).freeVars = [] := by
        have hvP : v ∈ LMonoTy.freeVars P := hvmem
        have h1 : LMonoTy.freeVars (LMonoTy.subst T1 (.ftvar v))
            ⊆ LMonoTy.freeVars (LMonoTy.subst T1 P) :=
          freeVars_subst_ftvar_subset T1 P v hvP
        rw [List.eq_nil_iff_forall_not_mem]
        intro w hw
        -- Find the source `x` of `w` in `subst T1 (ftvar v)`; it lies in `subst T1 P`,
        -- so `w`'s `T2`-image sits inside `A = subst T2 (subst T1 P)`, which is ground.
        obtain ⟨x, hxmem, hxw⟩ := freeVars_subst_source T2 (LMonoTy.subst T1 (.ftvar v)) w hw
        have hxP : x ∈ LMonoTy.freeVars (LMonoTy.subst T1 P) := h1 hxmem
        have hwA : w ∈ A.freeVars := by
          rw [hA]; exact freeVars_subst_ftvar_subset T2 (LMonoTy.subst T1 P) x hxP hxw
        rw [hAg] at hwA; simp at hwA
      simp only [← hvt]; exact himg
    rw [SubstWF]
    rw [hvals]
    simp
  refine ⟨⟨[composeWitnessScope P T1 T2], hwf⟩, ?_⟩
  rw [hA]
  exact (subst_composeWitnessScope P T1 T2 P (fun v hv => hv)).symm

/-- The freshened body is a renaming (a substitution) applied to the original. -/
theorem freshenBoundVars_snd_eq_subst (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (contextVars : List TyIdentifier) :
    ∃ R : Lambda.Subst, (freshenBoundVars boundVars monoTy contextVars).2
      = LMonoTy.subst R monoTy := by
  unfold freshenBoundVars
  exact ⟨_, rfl⟩

/-- **Instance witness.** Every candidate `(name, concreteArgTys)` that
    `polyOpsForResult` returns has, for the corresponding factory function `fn`
    (`F[name]? = some fn`, polymorphic), an annotation
    `A = concreteArgTys.foldr arrow τ` that is a *ground* substitution instance of
    `fn`'s generic type `mkArrow' fn.output fn.inputs.values`. The groundness comes
    from the `freeVars … == []` guard in `polyOpsForResult` (the ground-only fix);
    the instance witness comes from composing the bound-variable renaming
    (`freshenBoundVars`) with the substitution the generator applied
    (`fullSubst = (freeTyVars.zip sampledTys) :: subst`), collapsed into a single
    ground-valued scope via `ground_composite_substInfo`. Also forwards the
    generic type's free-vars-⊆-`typeArgs` invariant from `PCtxWF`, which the caller
    needs to handle the monomorphic (`typeArgs = []`) case. -/
theorem polyOpsForResult_instance (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (τ : LMonoTy) (generableTys sampledTys : List LMonoTy)
    (hPctx : PCtxWF F pctx)
    (name : String) (concreteArgTys : List LMonoTy)
    (hEntry : (name, concreteArgTys) ∈ polyOpsForResult pctx τ generableTys sampledTys) :
    ∃ (fn : LFunc LExprParams') (S : SubstInfo),
      F[name]? = some fn ∧
      (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).freeVars ⊆ fn.typeArgs ∧
      (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ).freeVars = [] ∧
      concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
        = LMonoTy.subst S.subst (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)) := by
  -- Step 1: unfold membership in `polyOpsForResult` down to the success branch.
  unfold polyOpsForResult at hEntry
  simp only [List.mem_filterMap] at hEntry
  obtain ⟨⟨nm, boundVars, monoTy⟩, hmem, hfilt⟩ := hEntry
  simp only [] at hfilt
  -- Peel the guards: the `argTys.isEmpty || length > 3` guard, then `unifyTypes`,
  -- then the `freeTyVars` guard, then the ground-only guard.
  split at hfilt
  · exact absurd hfilt (by simp)
  · rename_i hguard1
    split at hfilt
    · exact absurd hfilt (by simp)
    · rename_i subst hunif
      split at hfilt
      · exact absurd hfilt (by simp)
      · rename_i hguard2
        split at hfilt
        · rename_i hguard3
          -- success branch.  Extract the two equalities from `hfilt`.
          simp only [Option.some.injEq, Prod.mk.injEq] at hfilt
          obtain ⟨hname, hcat⟩ := hfilt
          subst hname
          -- Name the freshening result and its arrow decomposition.
          obtain ⟨freshBoundVars, freshMonoTy, hfreshEq⟩ :
              ∃ a b, freshenBoundVars boundVars monoTy
                (τ.freeVars ++ List.flatMap LMonoTy.freeVars generableTys).eraseDups = (a, b) :=
            ⟨_, _, rfl⟩
          obtain ⟨argTys, retTy, hdecEq⟩ :
              ∃ a b, decomposeArrow freshMonoTy = (a, b) := ⟨_, _, rfl⟩
          rw [hfreshEq] at hunif hguard1 hguard2 hguard3 hcat
          simp only at hunif hguard1 hguard2 hguard3 hcat
          rw [hdecEq] at hunif hguard1 hguard3 hcat
          simp only at hunif hguard1 hguard3 hcat
          -- Step 2: `PCtxWF` gives the factory function and the shape of its type.
          obtain ⟨fn, hget, hlty, hfvsub⟩ := hPctx nm (.forAll boundVars monoTy) hmem
          -- Injectivity of `.forAll`: boundVars = fn.typeArgs, monoTy = genericTy.
          rw [LTy.forAll.injEq] at hlty
          obtain ⟨hba, hmono⟩ := hlty
          -- Groundness (Step 4): from `hguard3`, `τ` is ground and every concrete
          -- arg type is ground, so the folded annotation is ground.
          rw [Bool.and_eq_true] at hguard3
          obtain ⟨hτg, hcatg⟩ := hguard3
          have hτground : τ.freeVars = [] := by simpa using hτg
          have hAground : (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ).freeVars = [] := by
            rw [freeVars_foldr_arrow, hτground, List.append_nil]
            rw [← hcat]
            -- every element of `map (subst fullSubst) argTys` is ground (from `hcatg`)
            rw [List.flatMap_eq_nil_iff]
            intro σ hσ
            have := List.all_eq_true.mp hcatg σ hσ
            simpa using this
          -- Step 5: build the substitution witness.
          -- (a) `freshMonoTy = subst renameSubst monoTy` for the freshening renaming.
          obtain ⟨renameSubst, hfmt⟩ : ∃ R, freshMonoTy = LMonoTy.subst R monoTy := by
            obtain ⟨R, hR⟩ := freshenBoundVars_snd_eq_subst boundVars monoTy
              (τ.freeVars ++ List.flatMap LMonoTy.freeVars generableTys).eraseDups
            rw [hfreshEq] at hR; exact ⟨R, hR⟩
          -- (b) The full substitution the generator applied.
          -- Establish `A = subst fullSubst (subst renameSubst genericTy)`.
          have hgenericEq : monoTy = LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd) := hmono
          -- `retTy.subst subst = τ` (τ ground + unification soundness on `subst`).
          have hunifEq : LMonoTy.subst subst retTy = τ := by
            unfold unifyTypes at hunif
            split at hunif
            · rename_i si hsi
              simp only [Option.some.injEq] at hunif
              subst hunif
              have := Lambda.LExpr.unify_makes_equal retTy τ SubstInfo.empty si hsi
              rw [Lambda.subst_ground si.subst τ hτground] at this
              exact this
            · exact absurd hunif (by simp)
          -- Every free var of `retTy` is a key of `subst` (else it survives into the
          -- ground `τ`); hence it is *not* among `freeTyVars` (= vars missing from
          -- `subst`), so the extra `zip` scope is irrelevant on `retTy`.
          have hretKey : ∀ v, v ∈ LMonoTy.freeVars retTy → Maps.find? subst v ≠ none := by
            intro v hv hnone
            by_cases h : Subst.hasEmptyScopes subst
            · -- `subst` is identity ⇒ `retTy = subst subst retTy = τ` is ground.
              rw [LMonoTy.subst_emptyS h] at hunifEq
              rw [hunifEq, hτground] at hv; simp at hv
            · have hne : Subst.hasEmptyScopes subst = false := Bool.eq_false_iff.mpr h
              have hsurv : v ∈ (LMonoTy.subst subst retTy).freeVars := by
                -- `v` maps to itself under `subst` (find? none), so it survives.
                have hid : LMonoTy.subst subst (.ftvar v) = .ftvar v := by
                  rw [LMonoTy.subst]; simp only [hne, Bool.false_eq_true, ↓reduceIte, hnone]
                have hsub := freeVars_subst_ftvar_subset subst retTy v hv
                rw [hid] at hsub
                exact hsub (by simp [LMonoTy.freeVars])
              rw [hunifEq, hτground] at hsurv; simp at hsurv
          -- `subst fullSubst retTy = subst subst retTy = τ`.
          have hunifEqFull : LMonoTy.subst
              ((findFreeTyVars freshBoundVars subst).zip sampledTys :: subst) retTy = τ := by
            rw [← hunifEq]
            apply LMonoTy.subst_ext
            intro v hv
            -- `v` is a key of `subst` ⇒ `v ∉ freeTyVars` ⇒ `find?` on the cons scope
            -- falls through to `subst`.
            have hvfind : Maps.find? subst v ≠ none := hretKey v hv
            have hvnz : Map.find? ((findFreeTyVars freshBoundVars subst).zip sampledTys) v = none := by
              -- keys of the `zip` scope ⊆ `freeTyVars`, which are vars with `find? subst = none`.
              cases hz : Map.find? ((findFreeTyVars freshBoundVars subst).zip sampledTys) v with
              | none => rfl
              | some t =>
                exfalso
                have hkey : v ∈ Map.keys ((findFreeTyVars freshBoundVars subst).zip sampledTys) :=
                  Map.find?_mem_keys _ hz
                have hzip : v ∈ findFreeTyVars freshBoundVars subst :=
                  Map.keys_zip_subset _ _ hkey
                unfold findFreeTyVars at hzip
                rw [List.mem_filter] at hzip
                have := hzip.2
                simp only [beq_iff_eq] at this
                exact hvfind this
            show Maps.find? ((findFreeTyVars freshBoundVars subst).zip sampledTys :: subst) v
              = Maps.find? subst v
            rw [Maps.find?, hvnz]
          -- `A = subst fullSubst freshMonoTy`, then `= subst fullSubst (subst renameSubst genericTy)`.
          have hAeq : concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
              = LMonoTy.subst ((findFreeTyVars freshBoundVars subst).zip sampledTys :: subst)
                  (LMonoTy.subst renameSubst
                    (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))) := by
            rw [← hgenericEq, ← hfmt]
            -- freshMonoTy = argTys.foldr arrow retTy
            have hfreshFold : freshMonoTy
                = argTys.foldr (fun σ acc => LMonoTy.arrow σ acc) retTy := by
              have := decomposeArrow_foldr freshMonoTy
              rw [hdecEq] at this; simpa using this
            rw [hfreshFold, subst_foldr_arrow, hunifEqFull, ← hcat]
          -- Package via the ground-instance builder.
          obtain ⟨S, hS⟩ := ground_composite_substInfo
            (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
            (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))
            renameSubst ((findFreeTyVars freshBoundVars subst).zip sampledTys :: subst)
            hAground hAeq
          exact ⟨fn, S, hget, hfvsub, hAground, hS⟩
        · exact absurd hfilt (by simp)

/-- Under `PCtxWF`, the polymorphic-annotation assumption `PolyOpsConsistent`
    holds — because the ground-only fix guarantees every emitted annotation is a
    ground instance of the operator's generic type
    (`polyOpsForResult_instance`), which is `OpsConsistent` by
    `opGroundInstance_opsConsistent`. -/
theorem PolyOpsConsistent_of_PCtxWF (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (bctx : BVarCtx) (fctx : FVarCtx) (τ : LMonoTy) (hPctx : PCtxWF F pctx) :
    PolyOpsConsistent F pctx bctx fctx τ := by
  intro sampledTys name concreteArgTys hEntry
  obtain ⟨fn, S, hget, hfvsub, hground, hinst⟩ :=
    polyOpsForResult_instance F pctx τ _ sampledTys hPctx name concreteArgTys hEntry
  by_cases hta : fn.typeArgs.isEmpty
  · -- Monomorphic: `typeArgs = []` ⇒ generic type is ground (its free vars ⊆ [] = [])
    -- ⇒ the annotation `A = genericTy.subst S = genericTy`, so `opGeneric` applies.
    have hgen_ground : (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).freeVars = [] := by
      have hnil : fn.typeArgs = [] := by rwa [List.isEmpty_iff] at hta
      rw [hnil] at hfvsub
      exact List.subset_nil.mp hfvsub
    have hAeq : concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
        = LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd) := by
      rw [hinst, Lambda.subst_ground S.subst _ hgen_ground]
    rw [hAeq]
    exact Lambda.opGeneric_opsConsistent F fn () ⟨name, ()⟩ hget
  · -- Polymorphic: the annotation is a ground instance of the generic type.
    exact Lambda.opGroundInstance_opsConsistent F fn () ⟨name, ()⟩ _ S hget
      (by simpa using hta) hground hinst

-- ── genIndirPoly consistency ─────────────────────────────────────────

set_option maxHeartbeats 800000 in
/-- Every expression in `genIndirPoly`'s support is `GenOpsConsistent`, GIVEN the
    polymorphic-annotation assumption `PolyOpsConsistent` (which is itself proven,
    from `PCtxWF`, by `PolyOpsConsistent_of_PCtxWF`). Either a polymorphic operator
    was applied (op node consistent by `hPoly`, args by
    `mapM_genLExprBase_opsConsistent`), or the generator fell back to
    `genLExprBase`. -/
theorem genIndirPoly_opsConsistent (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (hPoly : PolyOpsConsistent F pctx bctx fctx τ) (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.GenOpsConsistent F e := by
  unfold genIndirPoly at he
  simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure, SetGen.mem_dite] at he
  obtain ⟨sampledTys, _, he⟩ := he
  rcases he with ⟨hpos, he⟩ | ⟨_, he⟩
  · -- polymorphic operator applied
    obtain ⟨idx, ⟨_, hidx_hi⟩, args, hargs, rfl⟩ := he
    have hlt : idx.down.val <
        (polyOpsForResult pctx τ (generableTypesFromCtx bctx fctx (factoryOps F)) sampledTys).length := by omega
    have hentry_mem :
        (polyOpsForResult pctx τ (generableTypesFromCtx bctx fctx (factoryOps F)) sampledTys).getD idx.down.val ("", []) ∈
        polyOpsForResult pctx τ (generableTypesFromCtx bctx fctx (factoryOps F)) sampledTys := by
      have heq :
          (polyOpsForResult pctx τ (generableTypesFromCtx bctx fctx (factoryOps F)) sampledTys).getD idx.down.val ("", []) =
          (polyOpsForResult pctx τ (generableTypesFromCtx bctx fctx (factoryOps F)) sampledTys)[idx.down.val] := by
        simp [List.getD, List.getElem?_eq_getElem hlt]
      rw [heq]; exact List.getElem_mem hlt
    apply mkApps_opsConsistent
    · exact hPoly sampledTys _ _ hentry_mem
    · exact mapM_genLExprBase_opsConsistent F fctx tvars bctx depth hFwf _ args hargs
  · -- fallback to genLExprBase
    exact genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he

-- ── Top-level: genLExpr consistency ──────────────────────────────────

set_option maxHeartbeats 800000 in
/-- **Main result (general polymorphic context).** Every expression in the
    support of `genLExpr` on a factory operator context `factoryOps F` satisfies
    `GenOpsConsistent F`, hence — by `GenOpsConsistent.faithful` — Strata's
    `OpsConsistent F`. Combined with `genLExpr_sound` this gives soundness w.r.t.
    both `HasTypeA` and `OpsConsistent`.

    Takes the polymorphic-annotation assumption `PolyOpsConsistent` as a
    hypothesis for generality; it is discharged from `PCtxWF` by
    `PolyOpsConsistent_of_PCtxWF`, giving the unconditional
    `genLExpr_opsConsistent_of_PCtxWF`. For the common `pctx = []` case use
    `genLExpr_opsConsistent_nil`. -/
theorem genLExpr_opsConsistent (F : @Factory LExprParams') (fctx : FVarCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (hPoly : PolyOpsConsistent F pctx bctx fctx τ) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.GenOpsConsistent F e := by
  unfold genLExpr at he
  simp only [mem_support_iff, SetGen.mem_dite, pickBiased_mem_iff, pick_mem_iff] at he
  rcases he with ⟨hpos, he | (he | he)⟩ | ⟨_, he | he⟩
  · -- genLExprBase branch
    exact genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he
  · -- monomorphic Indir
    simp only [SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
    obtain ⟨idx, ⟨_, hidx_hi⟩, args, hargs, rfl⟩ := he
    have hlt : idx.down.val < (findOpsInCtx (factoryOps F) τ).length := by omega
    have hentry_mem : (findOpsInCtx (factoryOps F) τ).getD idx.down.val ("", []) ∈
        findOpsInCtx (factoryOps F) τ := by
      have heq : (findOpsInCtx (factoryOps F) τ).getD idx.down.val ("", []) =
          (findOpsInCtx (factoryOps F) τ)[idx.down.val] := by
        simp [List.getD, List.getElem?_eq_getElem hlt]
      rw [heq]; exact List.getElem_mem hlt
    apply mkApps_opsConsistent
    · exact indir_op_opsConsistent F τ _ _ hFwf hentry_mem
    · exact mapM_genLExprBase_opsConsistent F fctx tvars bctx depth hFwf _ args hargs
  · -- IndirPoly (with candidates)
    exact genIndirPoly_opsConsistent F fctx pctx tvars bctx depth τ hFwf hPoly e he
  · -- genLExprBase fallback (no monomorphic candidates)
    exact genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he
  · -- IndirPoly fallback
    exact genIndirPoly_opsConsistent F fctx pctx tvars bctx depth τ hFwf hPoly e he

-- ── Bridge to Strata's real `OpsConsistent` ──────────────────────────
--
-- `genLExpr_opsConsistent` above proves `Lambda.GenOpsConsistent F e`, the
-- `@[expose] public` copy of `OpsConsistent` defined in
-- `HasTypeAGen/OpsConsistentDef.lean`. Strata's actual `Lambda.OpsConsistent`
-- lives in a *private* section of `Assumptions.lean` and is not nameable from
-- this (non-`module`) file. The module-level theorem
-- `Lambda.GenOpsConsistent.faithful` machine-checks, at build time, that
-- `GenOpsConsistent F e = Lambda.OpsConsistent F e` for all `e`. Composing the
-- two therefore yields Strata's `OpsConsistent` for every generated term; the
-- restatement in terms of the private predicate can only be written inside a
-- `module` file that `import all`s `Assumptions` (see `OpsConsistentDef.lean`).

/-- The `Factory`-wrapper generator `genLExprWithFactory` produces
    `GenOpsConsistent` terms (equivalently, `OpsConsistent`; see note above),
    given the polymorphic-annotation assumption `PolyOpsConsistent`. -/
theorem genLExprWithFactory_opsConsistent (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (pctx : PolyOpCtx)
    (hFwf : FactoryOutputWF F) (hPoly : PolyOpsConsistent F pctx bctx fctx τ) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExprWithFactory (G := SetGen.Set) fctx F tvars bctx depth τ pctx)) :
    Lambda.GenOpsConsistent F e :=
  genLExpr_opsConsistent F fctx pctx tvars bctx depth τ hFwf hPoly e he

/-- **Main result, parameterized by `PCtxWF` (no `PolyOpsConsistent` assumption).**
    Under the ground-only instantiation fix, a well-formed polymorphic context
    (`PCtxWF F pctx` — every `pctx` entry is a factory function's generic scheme)
    is enough: `PolyOpsConsistent` is *derived* via `PolyOpsConsistent_of_PCtxWF`.
    So `genLExpr` on a factory produces `GenOpsConsistent` (equivalently
    `OpsConsistent`) terms for *any* polymorphic context that matches the factory. -/
theorem genLExpr_opsConsistent_of_PCtxWF (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (hPctx : PCtxWF F pctx) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.GenOpsConsistent F e :=
  genLExpr_opsConsistent F fctx pctx tvars bctx depth τ hFwf
    (PolyOpsConsistent_of_PCtxWF F pctx bctx fctx τ hPctx) e he

-- ── Sorry-free corollary for the empty polymorphic context ───────────
-- The closed-term generators (`genClosedLExprWithFactory`, and
-- `genLExprWithFactory` at its default `pctx := []`) use `pctx = []`. For that
-- case `polyOpsForResult [] _ _ = []`, so `genIndirPoly` never emits a
-- polymorphic op and the freshening obligation (`polyOp_opsConsistent`) is
-- vacuous — giving a fully `sorry`-free result.

@[simp] theorem polyOpsForResult_nil (τ : LMonoTy) (g s : List LMonoTy) :
    polyOpsForResult [] τ g s = [] := by unfold polyOpsForResult; rfl

/-- `genIndirPoly` with an empty polymorphic context always falls back to
    `genLExprBase`, hence is `GenOpsConsistent` — with no dependence on the
    freshening obligation. -/
theorem genIndirPoly_opsConsistent_nil (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) fctx (factoryOps F) [] tvars bctx depth τ)) :
    Lambda.GenOpsConsistent F e := by
  unfold genIndirPoly at he
  simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure, SetGen.mem_dite] at he
  obtain ⟨sampledTys, _, he⟩ := he
  -- Only the fallback branch survives (candidate list is empty).
  rcases he with ⟨hpos, _⟩ | ⟨_, he⟩
  · exact absurd hpos (by simp)
  · exact genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he

set_option maxHeartbeats 800000 in
/-- **Main result, empty polymorphic context (fully `sorry`-free).** Every
    expression produced by `genLExpr` with `pctx = []` on a factory operator
    context satisfies `GenOpsConsistent F` (equivalently Strata's `OpsConsistent`;
    see the bridge note above). This covers the closed-term generators. -/
theorem genLExpr_opsConsistent_nil (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) [] tvars bctx depth τ)) :
    Lambda.GenOpsConsistent F e := by
  unfold genLExpr at he
  simp only [mem_support_iff, SetGen.mem_dite, pickBiased_mem_iff, pick_mem_iff] at he
  rcases he with ⟨hpos, he | (he | he)⟩ | ⟨_, he | he⟩
  · exact genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he
  · simp only [SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
    obtain ⟨idx, ⟨_, hidx_hi⟩, args, hargs, rfl⟩ := he
    have hlt : idx.down.val < (findOpsInCtx (factoryOps F) τ).length := by omega
    have hentry_mem : (findOpsInCtx (factoryOps F) τ).getD idx.down.val ("", []) ∈
        findOpsInCtx (factoryOps F) τ := by
      have heq : (findOpsInCtx (factoryOps F) τ).getD idx.down.val ("", []) =
          (findOpsInCtx (factoryOps F) τ)[idx.down.val] := by
        simp [List.getD, List.getElem?_eq_getElem hlt]
      rw [heq]; exact List.getElem_mem hlt
    apply mkApps_opsConsistent
    · exact indir_op_opsConsistent F τ _ _ hFwf hentry_mem
    · exact mapM_genLExprBase_opsConsistent F fctx tvars bctx depth hFwf _ args hargs
  · exact genIndirPoly_opsConsistent_nil F fctx tvars bctx depth τ hFwf e he
  · exact genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he
  · exact genIndirPoly_opsConsistent_nil F fctx tvars bctx depth τ hFwf e he
