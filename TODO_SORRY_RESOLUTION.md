# Plan to Resolve the 3 `sorry`s

## Discovery: Missing Precondition

The existing `SORRY_OBLIGATIONS.md` doesn't mention this, but resolving Sorry 1
requires a **new precondition** on `genIndirPoly_sound`:

```lean
(hSimplePctx : ∀ p ∈ pctx, match p.2 with | .forAll _ mono => SimpleType mono)
```

**Why**: `polyOpsForResult` extracts `argTys` via `decomposeArrow monoTy` (where
`monoTy` comes from the polymorphic type scheme), then applies `applySimpleSubst`
to each. To show the result is `SimpleType`, we need both:
- The original `argTy` is `SimpleType` (so `applySimpleSubst_simple` applies)
- The substitution maps to `SimpleType` values

The first requires `SimpleType monoTy` (from which `decomposeArrow` only peels
`.arrow` constructors, preserving `SimpleType`). Hence the precondition.

---

## Step 1: Helper Lemmas (insert before `genIndirPoly_sound`, ~line 1667)

### 1a. `applySimpleSubst_simple`

```lean
private theorem applySimpleSubst_simple (s : SimpleSubst) (ty : LMonoTy)
    (hTy : SimpleType ty)
    (hSubst : ∀ v t, (v, t) ∈ s → SimpleType t) :
    SimpleType (applySimpleSubst s ty) := by
  induction hTy with
  | bool => simp [applySimpleSubst, LMonoTy.bool]; exact .bool
  | int => simp [applySimpleSubst, LMonoTy.int]; exact .int
  | ftvar =>
    simp [applySimpleSubst]
    cases hl : List.lookup _ s with
    | none => exact .ftvar
    | some t => exact hSubst _ t (List.lookup_mem_keys_val hl)  -- or appropriate lemma
  | arrow _ _ ih₁ ih₂ =>
    simp [applySimpleSubst, LMonoTy.arrow]
    exact .arrow (ih₁ hSubst) (ih₂ hSubst)
```

**Note**: The `.ftvar` case needs `List.lookup x s = some t → (x, t) ∈ s`.
This is `List.mem_of_lookup_eq_some` or similar from Mathlib/Std.

### 1b. `syntacticSubtypes_simple`

```lean
private theorem syntacticSubtypes_simple (ty : LMonoTy) (hTy : SimpleType ty) :
    ∀ σ ∈ syntacticSubtypes ty, SimpleType σ := by
  induction hTy with
  | bool => simp [syntacticSubtypes, LMonoTy.bool]; intro _ h; exact h ▸ .bool
  | int => simp [syntacticSubtypes, LMonoTy.int]; intro _ h; exact h ▸ .int
  | ftvar => simp [syntacticSubtypes]; intro _ h; exact h ▸ .ftvar
  | arrow h₁ h₂ ih₁ ih₂ =>
    simp [syntacticSubtypes, LMonoTy.arrow]
    intro σ hσ
    rcases hσ with rfl | hσ
    · exact .arrow h₁ h₂
    · rcases List.mem_append.mp hσ with h | h
      · exact ih₁ σ h
      · exact ih₂ σ h
```

### 1c. `addNewTypes_simple`

```lean
private theorem addNewTypes_simple (fuel : Nat) (tys : List LMonoTy)
    (hAll : ∀ σ ∈ tys, SimpleType σ) :
    ∀ σ ∈ addNewTypes fuel tys, SimpleType σ := by
  induction fuel generalizing tys with
  | zero => simpa [addNewTypes]
  | succ n ih =>
    simp only [addNewTypes]
    split
    · exact hAll  -- newTys.isEmpty branch
    · apply ih
      intro σ hσ
      rcases List.mem_append.mp hσ with h | h
      · exact hAll σ h
      · -- σ ∈ newTys: it's retTy from some .arrow argTy retTy ∈ tys
        simp [List.mem_filterMap] at h
        obtain ⟨ty, hty_mem, hty_eq⟩ := h
        split at hty_eq <;> simp at hty_eq
        -- ty = .tcons "arrow" [argTy, retTy] = .arrow argTy σ
        have hSimple := hAll ty hty_mem
        exact (SimpleType_arrow_inv hSimple).2
```

### 1d. `generableTypesFromCtx_simple`

```lean
private theorem generableTypesFromCtx_simple
    (bctx : BVarCtx) (fctx : FVarCtx) (octx : OpCtx)
    (hBctx : ∀ τ ∈ bctx, SimpleType τ)
    (hFctx : ∀ p ∈ fctx, SimpleType p.2)
    (hOctx : ∀ p ∈ octx, SimpleType p.2) :
    ∀ σ ∈ generableTypesFromCtx bctx fctx octx, SimpleType σ := by
  unfold generableTypesFromCtx
  apply addNewTypes_simple
  intro σ hσ
  have hσ' := List.mem_eraseDups.mp hσ  -- eraseDups preserves membership
  rw [List.mem_flatMap] at hσ'
  obtain ⟨ty, hty_mem, hty_sub⟩ := hσ'
  -- ty ∈ bctx ++ fctx.map Prod.snd ++ octx.map Prod.snd
  have hSimpleTy : SimpleType ty := by
    rcases List.mem_append.mp hty_mem with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact hBctx ty h'
      · exact hFctx _ (List.mem_map_of_mem_snd h')  -- needs adaptation
    · exact hOctx _ (List.mem_map_of_mem_snd h)
  exact syntacticSubtypes_simple ty hSimpleTy σ hty_sub
```

### 1e. `decomposeArrow_simple`

```lean
private theorem decomposeArrow_simple (ty : LMonoTy) (hTy : SimpleType ty) :
    ∀ σ ∈ (decomposeArrow ty).1, SimpleType σ := by
  induction ty with
  | tcons name args =>
    match name, args with
    | "arrow", [σ₁, σ₂] =>
      simp [decomposeArrow]
      have ⟨h₁, h₂⟩ := SimpleType_arrow_inv hTy
      intro τ hτ
      rcases hτ with rfl | h
      · exact h₁
      · exact decomposeArrow_simple σ₂ h₂ τ h  -- recursive
    | _, _ => simp [decomposeArrow]
  | ftvar => simp [decomposeArrow]
  | bitvec => cases hTy  -- impossible
```

---

## Step 2: Add `hSimplePctx` to `genIndirPoly_sound` (line ~1684)

Change signature to:
```lean
theorem genIndirPoly_sound (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : SimpleType τ)
    (hSimpleOps : ∀ p ∈ octx, SimpleType p.2)
    (hSimplePctx : ∀ p ∈ pctx, match p.2 with | .forAll _ mono => SimpleType mono)
    (hSimpleGenerable : ∀ σ ∈ generableTypesFromCtx bctx fctx octx, SimpleType σ)
    ...
```

---

## Step 3: Fill Sorry 1 (line 1718) — `genIndirPoly_sound` candidates branch

Model after the monomorphic Indir proof (lines 1737-1769):

```lean
  · -- Candidates found
    simp only [SetGen.Set.mem_bind, SetGen.Set.mem_pure] at he
    obtain ⟨idx, ⟨_, hidx_hi⟩, args, hargs, rfl⟩ := he
    set ops := polyOpsForResult pctx τ (generableTypesFromCtx bctx fctx octx) sampledTys
    have hlt : idx.down < ops.length := by omega
    set entry := ops.getD idx.down ("", [])
    have hentry_eq : entry = ops[idx.down] := by
      simp [entry, List.getElem?_eq_getElem hlt]
    set name := entry.1
    set concreteArgTys := entry.2
    set fullArrowTy := concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ
    set base : LExpr' := .op () ⟨name, ()⟩ (some fullArrowTy)
    have hbase : HasTypeA' bctx base (concreteArgTys.foldr (fun σ acc => LMonoTy.arrow σ acc) τ) := .op
    have hforall₂ := (mem_mapM_iff
      (genLExprBase fctx octx tvars bctx depth) concreteArgTys args).mp hargs
    -- Key: show each concreteArgTy is SimpleType
    have hSimpleArgs : ∀ σ ∈ concreteArgTys, SimpleType σ := by
      -- concreteArgTys = argTys.map (applySimpleSubst fullSubst)
      -- where argTys come from decomposeArrow of a SimpleType monotype
      -- and fullSubst maps to SimpleType values (from hSimpleGenerable + hτ via unification)
      sorry -- This is the key sub-lemma about polyOpsForResult
    have hargs_typed : List.Forall₂ (HasTypeA' bctx) args concreteArgTys := by
      suffices h : ∀ (tys : List LMonoTy) (es : List LExpr'),
          (∀ σ ∈ tys, SimpleType σ) →
          List.Forall₂ (fun arg σ => arg ∈ (genLExprBase (G := SetGen.Set) fctx octx tvars bctx depth σ)) es tys →
          List.Forall₂ (HasTypeA' bctx) es tys from
        h concreteArgTys args hSimpleArgs hforall₂
      intro tys es hsimple hf₂
      induction hf₂ with
      | nil => exact .nil
      | @cons e ty _ _ hmem _ ih =>
        exact .cons
          (genLExprBase_sound fctx octx tvars bctx depth ty
            (hsimple ty List.mem_cons_self) e hmem)
          (ih (fun σ' hσ' => hsimple σ' (List.mem_cons_of_mem _ hσ')))
    exact mkApps_hasType bctx base args concreteArgTys τ hbase hargs_typed
```

The remaining `sorry` in `hSimpleArgs` requires a lemma about `polyOpsForResult`:

```lean
private theorem polyOpsForResult_args_simple
    (pctx : PolyOpCtx) (τ : LMonoTy) (generableTys sampledTys : List LMonoTy)
    (hτ : SimpleType τ)
    (hGenerable : ∀ σ ∈ generableTys, SimpleType σ)
    (hSampled : ∀ σ ∈ sampledTys, SimpleType σ)
    (hPctx : ∀ p ∈ pctx, match p.2 with | .forAll _ mono => SimpleType mono)
    (name : String) (argTys : List LMonoTy)
    (h : (name, argTys) ∈ polyOpsForResult pctx τ generableTys sampledTys) :
    ∀ σ ∈ argTys, SimpleType σ
```

This follows from:
1. `argTys = origArgTys.map (applySimpleSubst fullSubst)` by definition of `polyOpsForResult`
2. `origArgTys` come from `decomposeArrow monoTy` where `SimpleType monoTy` (from `hPctx`)
3. `fullSubst = composeSimpleSubst (freeTyVars.zip sampledTys) subst` where:
   - `subst` comes from `unifySimple retTy τ` — need a lemma that unifying two SimpleTypes produces a SimpleSubst mapping to SimpleTypes
   - `freeTyVars.zip sampledTys` maps to sampledTys values (SimpleType by `hSampled`)

This requires one more helper:
```lean
private theorem unifySimple_preserves_simple (t1 t2 : LMonoTy)
    (h1 : SimpleType t1) (h2 : SimpleType t2) (s : SimpleSubst)
    (hs : unifySimple t1 t2 = some s) :
    ∀ v t, (v, t) ∈ s → SimpleType t
```

---

## Step 4: Add preconditions to `genLExpr_sound` (line 1725)

```lean
theorem genLExpr_sound (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat)
    (τ : LMonoTy) (hτ : SimpleType τ)
    (hSimpleBctx : ∀ τ ∈ bctx, SimpleType τ)
    (hSimpleFctx : ∀ p ∈ fctx, SimpleType p.2)
    (hSimpleOps : ∀ p ∈ octx, SimpleType p.2)
    (hSimplePctx : ∀ p ∈ pctx, match p.2 with | .forAll _ mono => SimpleType mono)
    ...
```

Then lines 1772, 1777 become:
```lean
    exact genIndirPoly_sound fctx octx pctx tvars bctx depth τ hτ hSimpleOps hSimplePctx
      (generableTypesFromCtx_simple bctx fctx octx hSimpleBctx hSimpleFctx hSimpleOps) e he
```

---

## Step 5: `hSampled` — sampled types are SimpleType

In the genIndirPoly_sound proof, after `obtain ⟨sampledTys, _, he⟩ := he`, we need:
```lean
have hSampled : ∀ σ ∈ sampledTys, SimpleType σ
```

The sampled types are drawn from `generableTypesFromCtx` (via `getD ... .bool`).
- If `generableTys.length > 0`: result is `generableTys.getD idx.down .bool` — either in generableTys (SimpleType by `hSimpleGenerable`) or `.bool` (SimpleType)
- If `generableTys.length = 0`: result is `.bool` (SimpleType)

This requires destructuring the `mapM` on `List.replicate 3 ()` and reasoning about
each element. A helper lemma about membership in `List.mapM` on replicate may help.

---

## Difficulty Assessment

| Lemma | Difficulty | Notes |
|-------|-----------|-------|
| `applySimpleSubst_simple` | Medium | Structural induction, need `List.lookup` membership lemma |
| `syntacticSubtypes_simple` | Easy | Direct structural induction |
| `addNewTypes_simple` | Medium | Induction on fuel, need to handle filterMap |
| `generableTypesFromCtx_simple` | Easy | Composition of above |
| `decomposeArrow_simple` | Easy | Structural induction peeling arrows |
| `unifySimple_preserves_simple` | Hard | `unifySimple` is `partial` — may need `decreasing_by` or rely on `partial_fixpoint` equation lemmas |
| `polyOpsForResult_args_simple` | Medium | Unfolding filterMap/map, applying above |
| Sorry 1 (monadic destructuring) | Medium-Hard | Follow mono Indir pattern but more layers |
| Sorry 2 (both instances) | Easy | Direct application of `generableTypesFromCtx_simple` |

**Hardest part**: `unifySimple` is `partial def` — Lean may not generate useful equation lemmas for it. If proving `unifySimple_preserves_simple` directly is too hard, an alternative is to add it as an axiom (using `axiom` or `sorry`) temporarily, or restructure the proof to avoid needing properties of unification output.

**Alternative for `unifySimple`**: Since `unifySimple retTy τ = some subst` means `applySimpleSubst subst retTy = τ` (informally), and both `retTy` and `τ` are SimpleType, the substitution should only map variables to sub-terms of `τ` (or compositions thereof). A weaker approach: add `(hUnifySimple : ∀ ...) ` as a precondition, deferring that proof.
