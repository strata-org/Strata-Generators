import StrataGenerators.HasTypeAGen
import StrataGenerators.HasTypeAGen.Defs
import StrataGenerators.HasTypeAGen.OpsConsistentDef

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

`OpsConsistentR` (defined in a private section of Strata's `Assumptions.lean`) is
mirrored here as `Lambda.GenOpsConsistentR`, proven equivalent by
`Lambda.GenOpsConsistentR.faithful` (see `HasTypeAGen/OpsConsistentDef.lean`).

Working against the declarative `OpsConsistentR` (rather than the operational
`OpsConsistent`, whose `.op` check runs `opTypeSubst` and demands the annotation be
*reconstructible* by unification) is what makes this proof simple: `OpsConsistentR`'s
`.op_in` constructor asks only for the *existence* of an instantiating substitution,
and the generator builds every polymorphic annotation as exactly such an instance.
No ground-matching unification-completeness result is needed.

## Why the generator is `OpsConsistentR`

Every `.op` node a generated term can contain comes from one of two places:

* **`pickOp`** (inside `genLExprBase`): the annotation is exactly the *generic*
  factory type of the operator (as computed by `factoryOps`). The reused
  operational lemma `opGeneric_opsConsistent` shows this annotation is even
  `GenOpsConsistent`; `GenOpsConsistent.toR` then bridges it to `GenOpsConsistentR`.
  The same bridge covers the (subsumed) monomorphic Indir op node.

* **`genIndirPoly`**: the annotation is `concreteArgTys.foldr arrow τ`, built as a
  substitution instance of the operator's generic type (a bound-variable freshening
  renaming composed with the generator's own substitution — see
  `docs/ops-consistent-capture-bug.md`). The forward-instance guard in
  `polyOpsForResult` (`subst fullSubst retTy == τ`) ensures the instance targets `τ`;
  `polyOpsForResult_instanceR` recovers a single witnessing substitution, discharged
  from a factory-well-formedness hypothesis `PCtxWF` (via
  `PolyOpsConsistentR_of_PCtxWF`), giving the unconditional
  `genLExpr_opsConsistentR_of_PCtxWF`. Unlike the old ground-only approach this
  permits annotations mentioning a free (non-quantified) type variable.

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

    For the *declarative* `OpsConsistentR` relation, this is all we need — no
    `freeVars ⊆ typeArgs` invariant is required. `OpsConsistentR`'s `.op_in`
    constructor demands only the *existence* of a substitution turning the generic
    type into the annotation, and the generator builds its annotation as exactly
    such a substitution instance (see `polyOpsForResult_instanceR`); it never runs
    `opTypeSubst`, so the monomorphic short-circuit that forced the extra invariant
    in the operational proof (`docs/ops-consistent-polymorphic-gap.md`) does not
    arise here. -/
def PCtxWF (F : @Factory LExprParams') (pctx : PolyOpCtx) : Prop :=
  ∀ (name : String) (lty : Lambda.LTy),
    (name, lty) ∈ pctx →
    ∃ (fn : LFunc LExprParams'), F[name]? = some fn ∧
      lty = .forAll fn.typeArgs (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))

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

/-- `mkApps` of a `GenOpsConsistentR` base and `GenOpsConsistentR` args is
    `GenOpsConsistentR` (the declarative version, via the `.app` constructor). -/
theorem mkApps_opsConsistentR (F : @Factory LExprParams') (base : LExpr') (args : List LExpr')
    (hbase : Lambda.GenOpsConsistentR F base)
    (hargs : ∀ a ∈ args, Lambda.GenOpsConsistentR F a) :
    Lambda.GenOpsConsistentR F (mkApps base args) := by
  induction args generalizing base with
  | nil => simpa [mkApps] using hbase
  | cons a rest ih =>
    simp only [mkApps, List.foldl_cons]
    apply ih
    · exact Lambda.GenOpsConsistentR.app hbase (hargs a (by simp))
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
    can emit for target `τ` is `GenOpsConsistentR`: for every candidate
    `(name, concreteArgTys)` in `polyOpsForResult pctx τ generableTys sampledTys`,
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
    `OpsConsistentR.op_in` asks for (`polyOpsForResult_instanceR`). The
    forward-instance guard in `polyOpsForResult` (`subst fullSubst retTy == τ`)
    ensures the instance actually targets `τ`; unlike the old ground-only guard it
    permits annotations mentioning a free (non-quantified) type variable.

    It holds vacuously when `pctx = []` (see the `…_nil` results, which need no
    such assumption). -/
def PolyOpsConsistentR (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (bctx : BVarCtx) (fctx : FVarCtx) (τ : LMonoTy) : Prop :=
  ∀ (sampledTys : List LMonoTy) (name : String) (concreteArgTys : List LMonoTy),
    (name, concreteArgTys) ∈
      polyOpsForResult pctx τ (generableTypesFromCtx bctx fctx (factoryOps F)) sampledTys →
    Lambda.GenOpsConsistentR F
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

/-- The single-scope substitution that sends each free variable `v` of `P` to its
    image under the composite `subst T2 ∘ subst T1`. Applied to `P` (or any type
    whose free variables are all free in `P`) it reconstructs the composite; that
    is all `OpsConsistentR`'s existence witness needs — no groundness or
    well-formedness is required. -/
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

/-- **Composite-instance packaging (declarative).** If `A` equals the composite
    `subst T2 (subst T1 P)`, then there is a *raw* substitution `S` with
    `A = subst S P`. The witness is the single scope `composeWitnessScope P T1 T2`;
    unlike the operational proof this needs no `SubstWF` and no groundness, because
    `OpsConsistentR.op_in` accepts any `Subst`, not a well-formed `SubstInfo`. -/
theorem composite_instance_subst (A P : LMonoTy) (T1 T2 : Lambda.Subst)
    (hA : A = LMonoTy.subst T2 (LMonoTy.subst T1 P)) :
    ∃ S : Lambda.Subst, A = LMonoTy.subst S P := by
  refine ⟨[composeWitnessScope P T1 T2], ?_⟩
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
    that `polyOpsForResult` returns has, for the corresponding factory function
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
theorem polyOpsForResult_instanceR (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (τ : LMonoTy) (generableTys sampledTys : List LMonoTy)
    (hPctx : PCtxWF F pctx)
    (name : String) (concreteArgTys : List LMonoTy)
    (hEntry : (name, concreteArgTys) ∈ polyOpsForResult pctx τ generableTys sampledTys) :
    ∃ (fn : LFunc LExprParams') (S : Lambda.Subst),
      F[name]? = some fn ∧
      concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
        = LMonoTy.subst S (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)) := by
  -- Step 1: unfold membership in `polyOpsForResult` down to the success branch.
  unfold polyOpsForResult at hEntry
  simp only [List.mem_filterMap] at hEntry
  obtain ⟨⟨nm, boundVars, monoTy⟩, hmem, hfilt⟩ := hEntry
  simp only [] at hfilt
  -- Peel the guards: the `argTys.isEmpty || length > 3` guard, then `unifyTypes`,
  -- then the `freeTyVars` guard, then the forward-instance guard.
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
          obtain ⟨fn, hget, hlty⟩ := hPctx nm (.forAll boundVars monoTy) hmem
          -- Injectivity of `.forAll`: boundVars = fn.typeArgs, monoTy = genericTy.
          rw [LTy.forAll.injEq] at hlty
          obtain ⟨hba, hmono⟩ := hlty
          have hgenericEq : monoTy = LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd) := hmono
          -- Step 3: the forward-instance guard *is* `subst fullSubst retTy = τ`.
          have hunifEqFull : LMonoTy.subst
              ((findFreeTyVars freshBoundVars subst).zip sampledTys :: subst) retTy = τ :=
            beq_iff_eq.mp hguard3
          -- Step 4: build the substitution witness.
          -- (a) `freshMonoTy = subst renameSubst monoTy` for the freshening renaming.
          obtain ⟨renameSubst, hfmt⟩ : ∃ R, freshMonoTy = LMonoTy.subst R monoTy := by
            obtain ⟨R, hR⟩ := freshenBoundVars_snd_eq_subst boundVars monoTy
              (τ.freeVars ++ List.flatMap LMonoTy.freeVars generableTys).eraseDups
            rw [hfreshEq] at hR; exact ⟨R, hR⟩
          -- (b) `A = subst fullSubst (subst renameSubst genericTy)`.
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
          -- Package into a single substitution witness (no groundness / no WF).
          obtain ⟨S, hS⟩ := composite_instance_subst
            (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ)
            (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))
            renameSubst ((findFreeTyVars freshBoundVars subst).zip sampledTys :: subst)
            hAeq
          exact ⟨fn, S, hget, hS⟩
        · exact absurd hfilt (by simp)

/-- Under `PCtxWF`, the polymorphic-annotation assumption `PolyOpsConsistentR`
    holds — because every emitted annotation is a substitution instance of the
    operator's generic type (`polyOpsForResult_instanceR`), which is exactly the
    witness `OpsConsistentR.op_in` (`GenOpsConsistentR.op_in`) demands. No case
    split on `typeArgs`, no groundness. -/
theorem PolyOpsConsistentR_of_PCtxWF (F : @Factory LExprParams') (pctx : PolyOpCtx)
    (bctx : BVarCtx) (fctx : FVarCtx) (τ : LMonoTy) (hPctx : PCtxWF F pctx) :
    PolyOpsConsistentR F pctx bctx fctx τ := by
  intro sampledTys name concreteArgTys hEntry
  obtain ⟨fn, S, hget, hinst⟩ :=
    polyOpsForResult_instanceR F pctx τ _ sampledTys hPctx name concreteArgTys hEntry
  exact Lambda.GenOpsConsistentR.op_in hget hinst

-- ── genIndirPoly consistency ─────────────────────────────────────────

set_option maxHeartbeats 800000 in
/-- Every expression in `genIndirPoly`'s support is `GenOpsConsistentR`, GIVEN the
    polymorphic-annotation assumption `PolyOpsConsistentR` (which is itself proven,
    from `PCtxWF`, by `PolyOpsConsistentR_of_PCtxWF`). Either a polymorphic operator
    was applied (op node consistent by `hPoly`, args by
    `mapM_genLExprBase_opsConsistent` bridged with `GenOpsConsistent.toR`), or the
    generator fell back to `genLExprBase`. -/
theorem genIndirPoly_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (hPoly : PolyOpsConsistentR F pctx bctx fctx τ) (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.GenOpsConsistentR F e := by
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
    apply mkApps_opsConsistentR
    · exact hPoly sampledTys _ _ hentry_mem
    · exact fun a ha => Lambda.GenOpsConsistent.toR _ _ (mapM_genLExprBase_opsConsistent F fctx tvars bctx depth hFwf _ args hargs a ha)
  · -- fallback to genLExprBase
    exact Lambda.GenOpsConsistent.toR _ _ (genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he)

-- ── Top-level: genLExpr consistency ──────────────────────────────────

set_option maxHeartbeats 800000 in
/-- **Main result (general polymorphic context).** Every expression in the
    support of `genLExpr` on a factory operator context `factoryOps F` satisfies
    `GenOpsConsistentR F`, hence — by `GenOpsConsistentR.faithful` — Strata's
    declarative `OpsConsistentR F`. Combined with `genLExpr_sound` this gives
    soundness w.r.t. both `HasTypeA` and `OpsConsistentR`.

    Takes the polymorphic-annotation assumption `PolyOpsConsistentR` as a
    hypothesis for generality; it is discharged from `PCtxWF` by
    `PolyOpsConsistentR_of_PCtxWF`, giving the unconditional
    `genLExpr_opsConsistentR_of_PCtxWF`. For the common `pctx = []` case use
    `genLExpr_opsConsistentR_nil`. -/
theorem genLExpr_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (hPoly : PolyOpsConsistentR F pctx bctx fctx τ) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.GenOpsConsistentR F e := by
  unfold genLExpr at he
  simp only [mem_support_iff, SetGen.mem_dite, pickBiased_mem_iff, pick_mem_iff] at he
  rcases he with ⟨hpos, he | (he | he)⟩ | ⟨_, he | he⟩
  · -- genLExprBase branch
    exact Lambda.GenOpsConsistent.toR _ _ (genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he)
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
    apply mkApps_opsConsistentR
    · exact Lambda.GenOpsConsistent.toR _ _ (indir_op_opsConsistent F τ _ _ hFwf hentry_mem)
    · exact fun a ha => Lambda.GenOpsConsistent.toR _ _ (mapM_genLExprBase_opsConsistent F fctx tvars bctx depth hFwf _ args hargs a ha)
  · -- IndirPoly (with candidates)
    exact genIndirPoly_opsConsistentR F fctx pctx tvars bctx depth τ hFwf hPoly e he
  · -- genLExprBase fallback (no monomorphic candidates)
    exact Lambda.GenOpsConsistent.toR _ _ (genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he)
  · -- IndirPoly fallback
    exact genIndirPoly_opsConsistentR F fctx pctx tvars bctx depth τ hFwf hPoly e he

-- ── Bridge to Strata's real `OpsConsistentR` ─────────────────────────
--
-- `genLExpr_opsConsistentR` above proves `Lambda.GenOpsConsistentR F e`, the
-- `public` copy of Strata's declarative `OpsConsistentR` defined in
-- `HasTypeAGen/OpsConsistentDef.lean`. Strata's actual `Lambda.OpsConsistentR`
-- lives in a *private* section of `Assumptions.lean` and is not nameable from
-- this (non-`module`) file. The module-level theorem
-- `Lambda.GenOpsConsistentR.faithful` machine-checks, at build time, that
-- `GenOpsConsistentR F e ↔ Lambda.OpsConsistentR F e` for all `e`. Composing the
-- two therefore yields Strata's `OpsConsistentR` for every generated term; the
-- restatement in terms of the private predicate can only be written inside a
-- `module` file that `import all`s `Assumptions` (see `OpsConsistentDef.lean`).

/-- The `Factory`-wrapper generator `genLExprWithFactory` produces
    `GenOpsConsistentR` terms (equivalently, `OpsConsistentR`; see note above),
    given the polymorphic-annotation assumption `PolyOpsConsistentR`. -/
theorem genLExprWithFactory_opsConsistentR (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (pctx : PolyOpCtx)
    (hFwf : FactoryOutputWF F) (hPoly : PolyOpsConsistentR F pctx bctx fctx τ) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExprWithFactory (G := SetGen.Set) fctx F tvars bctx depth τ pctx)) :
    Lambda.GenOpsConsistentR F e :=
  genLExpr_opsConsistentR F fctx pctx tvars bctx depth τ hFwf hPoly e he

/-- **Main result, parameterized by `PCtxWF` (no `PolyOpsConsistentR` assumption).**
    A well-formed polymorphic context (`PCtxWF F pctx` — every `pctx` entry is a
    factory function's generic scheme) is enough: `PolyOpsConsistentR` is *derived*
    via `PolyOpsConsistentR_of_PCtxWF`. So `genLExpr` on a factory produces
    `GenOpsConsistentR` (equivalently `OpsConsistentR`) terms for *any* polymorphic
    context that matches the factory. -/
theorem genLExpr_opsConsistentR_of_PCtxWF (F : @Factory LExprParams') (fctx : FVarCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (hPctx : PCtxWF F pctx) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) pctx tvars bctx depth τ)) :
    Lambda.GenOpsConsistentR F e :=
  genLExpr_opsConsistentR F fctx pctx tvars bctx depth τ hFwf
    (PolyOpsConsistentR_of_PCtxWF F pctx bctx fctx τ hPctx) e he

-- ── Sorry-free corollary for the empty polymorphic context ───────────
-- The closed-term generators (`genClosedLExprWithFactory`, and
-- `genLExprWithFactory` at its default `pctx := []`) use `pctx = []`. For that
-- case `polyOpsForResult [] _ _ = []`, so `genIndirPoly` never emits a
-- polymorphic op and the polymorphic-annotation obligation is vacuous — giving a
-- result that does not even need `PCtxWF`.

@[simp] theorem polyOpsForResult_nil (τ : LMonoTy) (g s : List LMonoTy) :
    polyOpsForResult [] τ g s = [] := by unfold polyOpsForResult; rfl

/-- `genIndirPoly` with an empty polymorphic context always falls back to
    `genLExprBase`, hence is `GenOpsConsistentR`. -/
theorem genIndirPoly_opsConsistentR_nil (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (e : LExpr')
    (he : e ∈ SetGen.support
      (genIndirPoly (G := SetGen.Set) fctx (factoryOps F) [] tvars bctx depth τ)) :
    Lambda.GenOpsConsistentR F e := by
  unfold genIndirPoly at he
  simp only [mem_support_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure, SetGen.mem_dite] at he
  obtain ⟨sampledTys, _, he⟩ := he
  -- Only the fallback branch survives (candidate list is empty).
  rcases he with ⟨hpos, _⟩ | ⟨_, he⟩
  · exact absurd hpos (by simp)
  · exact Lambda.GenOpsConsistent.toR _ _ (genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he)

set_option maxHeartbeats 800000 in
/-- **Main result, empty polymorphic context (fully `sorry`-free).** Every
    expression produced by `genLExpr` with `pctx = []` on a factory operator
    context satisfies `GenOpsConsistentR F` (equivalently Strata's
    `OpsConsistentR`; see the bridge note above). This covers the closed-term
    generators. -/
theorem genLExpr_opsConsistentR_nil (F : @Factory LExprParams') (fctx : FVarCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hFwf : FactoryOutputWF F) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx (factoryOps F) [] tvars bctx depth τ)) :
    Lambda.GenOpsConsistentR F e := by
  unfold genLExpr at he
  simp only [mem_support_iff, SetGen.mem_dite, pickBiased_mem_iff, pick_mem_iff] at he
  rcases he with ⟨hpos, he | (he | he)⟩ | ⟨_, he | he⟩
  · exact Lambda.GenOpsConsistent.toR _ _ (genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he)
  · simp only [SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
    obtain ⟨idx, ⟨_, hidx_hi⟩, args, hargs, rfl⟩ := he
    have hlt : idx.down.val < (findOpsInCtx (factoryOps F) τ).length := by omega
    have hentry_mem : (findOpsInCtx (factoryOps F) τ).getD idx.down.val ("", []) ∈
        findOpsInCtx (factoryOps F) τ := by
      have heq : (findOpsInCtx (factoryOps F) τ).getD idx.down.val ("", []) =
          (findOpsInCtx (factoryOps F) τ)[idx.down.val] := by
        simp [List.getD, List.getElem?_eq_getElem hlt]
      rw [heq]; exact List.getElem_mem hlt
    apply mkApps_opsConsistentR
    · exact Lambda.GenOpsConsistent.toR _ _ (indir_op_opsConsistent F τ _ _ hFwf hentry_mem)
    · exact fun a ha => Lambda.GenOpsConsistent.toR _ _ (mapM_genLExprBase_opsConsistent F fctx tvars bctx depth hFwf _ args hargs a ha)
  · exact genIndirPoly_opsConsistentR_nil F fctx tvars bctx depth τ hFwf e he
  · exact Lambda.GenOpsConsistent.toR _ _ (genLExprBase_opsConsistent F fctx tvars bctx depth τ e hFwf he)
  · exact genIndirPoly_opsConsistentR_nil F fctx tvars bctx depth τ hFwf e he
