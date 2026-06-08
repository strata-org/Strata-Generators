# Remaining `sorry` Obligations in `genIndirPoly_sound`

Two `sorry`s remain in `StrataGenerators/HasTypeAGen.lean` after adding the
IndirPoly rule. Both reduce to the same core obligation: **proving that
`applySimpleSubst` preserves `SimpleType` when the substitution maps type
variables to `SimpleType` values**.

---

## Sorry 1: Candidates branch of `genIndirPoly_sound` (line ~1718)

### Location
`StrataGenerators/HasTypeAGen.lean`, inside `theorem genIndirPoly_sound`,
the `⟨hpos, he⟩` branch (candidates were found).

### What needs to be proved
After the `simp` normalizes the support membership, the goal is:

```
HasTypeA' bctx e τ
```

where `e` comes from the support of the `choose >> mapM >> pure` pipeline.
Concretely, after destructuring:
- `e = mkApps (.op () ⟨name, ()⟩ (some fullArrowTy)) args`
- `fullArrowTy = concreteArgTys.foldr (fun σ acc => .arrow σ acc) τ`
- `args ∈ List.mapM (genLExprBase fctx octx tvars bctx depth) concreteArgTys`

### Proof strategy
1. **`obtain` the pieces**: Destructure `he` through the nested binds:
   - `choose 0 (ops.length - 1) _` gives `idx`
   - `List.mapM (genLExprBase ...) concreteArgTys` gives `args`
   - `pure (mkApps opExpr args)` gives `rfl`

2. **Type the op node**: `HasTypeA.op` gives
   `HasTypeA' bctx (.op () ⟨name,()⟩ (some fullArrowTy)) fullArrowTy`
   unconditionally (it reads the annotation).

3. **Type each argument**: By `mem_mapM_iff`, each `args[i]` is in
   `genLExprBase ... concreteArgTys[i]`. Apply `genLExprBase_sound` to get
   `HasTypeA' bctx args[i] concreteArgTys[i]` — this requires
   `SimpleType concreteArgTys[i]` (see **Core Lemma** below).

4. **Assemble**: `mkApps_hasType bctx _ args concreteArgTys τ hbase hargs`
   produces the final `HasTypeA' bctx e τ`.

### Difficulty
The `obtain` destructuring at step 1 is the main mechanical difficulty —
Lean's elaboration of the `do`-block inside `dite` produces a term whose
structure is opaque to `simp`/`obtain` without the right intermediate `let`
reduction lemmas. The proof for the monomorphic Indir rule (which has an
identical `choose >> mapM >> pure` pattern) works because the `dite`
condition is at the top level and the `do`-block is simpler (no preceding
`mapM` for type sampling).

---

## Sorry 2: `hSimpleGenerable` in `genLExpr_sound` (line ~1745, 1749)

### Location
`StrataGenerators/HasTypeAGen.lean`, inside `theorem genLExpr_sound`,
at the two calls `genIndirPoly_sound ... (fun σ _ => by sorry) ...`.

### What needs to be proved
```
∀ σ ∈ generableTypesFromCtx bctx fctx octx, SimpleType σ
```

### Proof strategy
Prove a standalone lemma:
```lean
theorem generableTypesFromCtx_simple
    (bctx : BVarCtx) (fctx : FVarCtx) (octx : OpCtx)
    (hBctx : ∀ τ ∈ bctx, SimpleType τ)
    (hFctx : ∀ p ∈ fctx, SimpleType p.2)
    (hOctx : ∀ p ∈ octx, SimpleType p.2) :
    ∀ σ ∈ generableTypesFromCtx bctx fctx octx, SimpleType σ
```

This requires:
1. `syntacticSubtypes` preserves `SimpleType` (structural induction on type).
2. `addNewTypes` preserves `SimpleType`: if `SimpleType (.arrow σ τ)` and
   `SimpleType σ` then `SimpleType τ` (by inversion on `SimpleType.arrow`).
3. `List.eraseDups` doesn't change membership (trivial).

Then in `genLExpr_sound`, supply `generableTypesFromCtx_simple` with
appropriate hypotheses (derivable from `hSimpleOps` and any future
preconditions on `bctx`/`fctx`).

---

## Core Lemma Needed by Both

```lean
theorem applySimpleSubst_simple (s : SimpleSubst) (ty : LMonoTy)
    (hTy : SimpleType ty)
    (hSubst : ∀ v t, (v, t) ∈ s → SimpleType t) :
    SimpleType (applySimpleSubst s ty)
```

**Proof sketch** (structural induction on `hTy`):
- `SimpleType.bool`: `applySimpleSubst s .bool = .bool` since
  `.bool = .tcons "bool" []` and `[].map f = []`. So `SimpleType.bool`.
- `SimpleType.int`: analogous.
- `SimpleType.ftvar`: `applySimpleSubst s (.ftvar name)` is either
  `s.lookup name` (a `SimpleType` by `hSubst`) or `.ftvar name`
  (a `SimpleType` by `SimpleType.ftvar`).
- `SimpleType.arrow h₁ h₂`: `applySimpleSubst s (.arrow τ₁ τ₂)` =
  `.arrow (applySimpleSubst s τ₁) (applySimpleSubst s τ₂)`.
  By IH, both sub-results are `SimpleType`. Apply `SimpleType.arrow`.

---

## Relevant Results in `Strata/DL/Lambda/LTyUnify.lean`

The Strata repo contains a full unification implementation with proofs. While
the generator uses its own lightweight `unifySimple` / `applySimpleSubst`
(to avoid importing the full `LTyUnify` module and its Mathlib-heavy
dependencies), several results from `LTyUnify.lean` provide useful reference
patterns or could be imported if the dependency constraint is relaxed:

### Type Substitution (`LMonoTy.subst`)
| Definition/Theorem | Signature | Relevance |
|---|---|---|
| `LMonoTy.subst` | `Subst → LMonoTy → LMonoTy` | Strata's official substitution; structurally identical to `applySimpleSubst` |
| `LMonoTy.subst_bool` | `subst S .bool = .bool` | Ground types are fixed points of substitution |
| `LMonoTy.subst_tcons` | `subst S (.tcons n args) = .tcons n (subst S <$> args)` | Substitution distributes into constructors |
| `LMonoTy.subst_unfold` | Full case-split expansion of `subst` | Reference for `applySimpleSubst` induction |
| `LMonoTy.subst_no_relevant_keys` | If no key of `S` is free in `ty`, then `subst S ty = ty` | Helps with fixed-point arguments |
| `LMonoTy.subst_idempotent` | `SubstWF S → subst S (subst S ty) = subst S ty` | Well-formed substitutions are idempotent |
| `LMonoTy.subst_ext` | Extensionality: equal on free vars ⟹ equal on type | Useful for relating `applySimpleSubst` to `LMonoTy.subst` |
| `subst_mkArrow'` | `subst S (mkArrow' ret ins) = mkArrow' (subst S ret) (map (subst S) ins)` | Substitution distributes over curried arrows |

### Substitution Composition and Absorption
| Definition/Theorem | Signature | Relevance |
|---|---|---|
| `Subst.apply` | `SubstOne → Subst → Subst` | Compose a single-scope substitution into an existing one |
| `Subst.absorbs` | `S_outer absorbs S_inner` iff applying `S_inner` then `S_outer` = applying `S_outer` alone | Key property for incremental unification |
| `LMonoTy.subst_absorbs` | If `S_outer` absorbs `S_inner`, then `subst S_outer (subst S_inner ty) = subst S_outer ty` | Composition collapse |
| `Subst.absorbs_refl` | Every well-formed substitution absorbs itself | |
| `Subst.absorbs_trans` | Absorption is transitive | |
| `composeSimpleSubst` (ours) | Analogous to `Subst.apply` but for `SimpleSubst` | Direct correspondence |

### Unification
| Definition/Theorem | Signature | Relevance |
|---|---|---|
| `Constraint.unifyOne` | `Constraint → SubstInfo → Except UnifyError (ValidSubstRelation ...)` | Full unification for one constraint |
| `Constraints.unify` | `Constraints → SubstInfo → Except UnifyError SubstInfo` | Top-level unification |
| `Constraint.unifyOne_sound` | If unification succeeds, `subst S_new t1 = subst S_new t2` | Correctness of unification |
| `Constraints.unify_sound` | All constraints satisfied after unification | Multi-constraint version |
| `Constraints.unify_absorbs` | Output substitution absorbs input | Monotonicity of unification |

### Polymorphic Type Operations
| Definition/Theorem | Signature | Relevance |
|---|---|---|
| `LTy.openFull` | `LTy → List LMonoTy → LMonoTy` | Instantiate all bound vars simultaneously |
| `LTy.open` | `TyIdentifier → LMonoTy → LTy → LTy` | Instantiate one bound var |
| `LTy.boundVars` | `LTy → List TyIdentifier` | Extract the quantified variables |
| `LMonoTy.freeVars` | `LMonoTy → List TyIdentifier` | Free type variables in a monotype |

### Potentially Useful for Bridging

If the import constraint on `Core.lean` (no `LTyUnify` import) were relaxed,
one could replace `unifySimple` / `applySimpleSubst` with Strata's
`Constraints.unify` / `LMonoTy.subst` and directly reuse the soundness
theorems. The file header comment in `Core.lean` states:

> **Important**: This file must NOT import `Strata.DL.Lambda.Factory` or anything
> from Mathlib/Batteries that would trigger the `List.Forall₂` conflict.

`LTyUnify.lean` does not import `Factory` or trigger this conflict, so it
*may* be safe to import — but this needs verification against the actual
`List.Forall₂` collision that motivates the constraint.
