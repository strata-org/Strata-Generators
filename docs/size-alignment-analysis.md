# Aligning Soundness and Completeness via Size/Depth

## Problem Statement

In `HasTypeAGen.lean`, the soundness and completeness theorems for `genLExpr` use different notions of "size":

- **Soundness** (`genLExpr_sound`): only proves well-typedness (`HasTypeA' bctx e τ`). It makes no claim about the depth/size of generated terms.
- **Completeness** (`genLExpr_complete`): requires `termDepth bctx e ≤ size` as a precondition.

The mismatch: the generator at `| 0, .arrow τ₁ τ₂ =>` can produce lambdas (with body generated at size 0), yielding terms with `termDepth ≥ 1`. These are well-typed (soundness holds), but fall outside the `termDepth ≤ 0` precondition of completeness. There is no theorem stating that `e ∈ support → termDepth e ≤ size`.

By contrast, `STLC.lean` achieves a tight bidirectional characterization:

```lean
e ∈ support (genTyped Γ depth τ) ↔ typing Γ e τ ∧ termDepth Γ e ≤ depth
```

## How STLC.lean Achieves Alignment

Three design choices work together:

1. **Generator fails at size 0 for arrows**: `| 0, .Fun _ _ => default`
2. **`termDepth` incorporates type depth**:
   ```lean
   | .Var x   => typDepth (Γ.getD x .Nat)
   | .Abs τ e => max (typDepth τ) (termDepth (τ :: Γ) e) + 1
   ```
3. **A separate `genTyped_termDepth_bound` theorem** proves `e ∈ support → termDepth e ≤ depth`, which combines with soundness to give the full `↔`.

The key insight: because variables carry their type's depth, a variable of type `Nat → Nat` has `termDepth = 1`. This means `indicesOfType` filters out variables whose type is too deep for the current size budget, and the generator never returns something it "shouldn't" be able to afford.

## Current State of `HasTypeAGen.lean`

### `termDepth` definition (line 1003)

```lean
private def termDepth (bctx : BVarCtx) : LExpr' → Nat
  | .boolConst () _       => 0
  | .intConst () _        => 0
  | .bvar () _            => 0      -- ← no type depth penalty
  | .fvar () _ _          => 0
  | .op () _ _            => 0
  | .abs () _ (some τ₁) body => termDepth (τ₁ :: bctx) body + 1
  | .app () fn arg        => max (termDepth bctx fn) (termDepth bctx arg) + 1
  | .ite () c t e         => max (termDepth bctx c) (max (termDepth bctx t) (termDepth bctx e)) + 1
  | .eq () e₁ e₂          => max (termDepth bctx e₁) (termDepth bctx e₂) + 1
  | .quant () _ _ (some τ) tr body =>
      max (monoTyDepth τ) (max (termDepth (τ :: bctx) tr) (termDepth (τ :: bctx) body)) + 1
  | _                     => 0
```

Notable: `bvar`, `fvar`, `op` all have depth 0 regardless of their type. The `abs` case does not include `monoTyDepth τ₁` (unlike STLC). Only `quant` incorporates type depth.

### Generator at size 0 for arrows (line 176)

When no bvar/fvar/op of the target arrow type exists, the generator falls back to constructing a lambda:
```lean
| 0, .arrow τ₁ τ₂ =>
    ...
    else do
      let body ← genLExpr fctx octx tvars (τ₁ :: bctx) 0 τ₂
      pure (.abs () "" (some τ₁) body)
```

This produces terms with `termDepth ≥ 1` at size 0 — the source of the misalignment.

## Approaches Considered

### Approach A: Fail at size 0 for arrows (direct STLC port)

**Change**: `| 0, .arrow τ₁ τ₂ => default`

**Problem**: A `bvar` of arrow type has `termDepth = 0` in the current definition. If the generator returns `default` at size 0 for all arrow types, it can't generate these bvars — but they *should* be generable (they satisfy `termDepth ≤ 0`). To fix this, you'd need to incorporate `monoTyDepth` into `termDepth` for `bvar`:

```lean
| .bvar () i => monoTyDepth (bctx.getD i .bool)
```

This creates a cascade: a bvar of type `(α → β) → γ` would have depth 2, requiring size ≥ 2 just to return a variable lookup. For LExpr this is impractical because:
- Type variables (`ftvar`) have depth 0, so even `α → β` has depth 1
- The context frequently contains arrow-typed entries (from surrounding lambdas)
- Generator success rate at low sizes would drop significantly

### Approach B: Make `abs` cost 0 in `termDepth`

**Change**: `| .abs () _ (some τ₁) body => termDepth (τ₁ :: bctx) body`

**Problem**: `termDepth` would no longer provide structural decrease — arbitrarily nested lambdas could all have depth 0. This is exactly the incoherence that the STLC doc describes fixing (see `docs/llm_stlc_generator_synthesis.md`, lines 120-124).

### Approach C (Recommended): Remove lambda fallbacks at size 0, keep current `termDepth`

**Generator change**: At size 0 for arrows, allow bvar/fvar/op returns but fall back to `default` (not lambda construction) when none exist:

```lean
| 0, .arrow τ₁ τ₂ =>
  let bvars := bvarsOfType bctx (.arrow τ₁ τ₂)
  pick
    (fun () => if hv : bvars.length > 0 then pickBVar bctx _ hv else default)
    (fun () => pick
      (fun () => if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0
                 then pickFVar fctx _ hf else default)
      (fun () => if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0
                 then pickOp octx _ ho else default))
```

**`termDepth` unchanged.** Bvar/fvar/op remain depth 0; abs remains depth ≥ 1.

**Why this works:**

| Size 0, arrow type | Generated terms | `termDepth` |
|---|---|---|
| bvar of arrow type | ✓ (via `pickBVar`) | 0 ≤ 0 ✓ |
| fvar of arrow type | ✓ (via `pickFVar`) | 0 ≤ 0 ✓ |
| op of arrow type | ✓ (via `pickOp`) | 0 ≤ 0 ✓ |
| lambda | ✗ (returns `default`) | would be ≥ 1 |

At size `n+1`, the abs case generates body at size `n`; by IH `termDepth body ≤ n`, so `termDepth (abs body) = termDepth body + 1 ≤ n + 1`.

## Target Theorem Structure (After Approach C)

### Bounded soundness (new)

```lean
theorem genLExpr_termDepth_bound (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (size : Nat) (τ : LMonoTy)
    (hτ : SimpleType τ) (e : LExpr')
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars bctx size τ)) :
    termDepth bctx e ≤ size
```

### Combined characterization

```lean
def wellFormedBounded (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (size : Nat) (τ : LMonoTy) (e : LExpr') : Prop :=
  HasTypeA' bctx e τ ∧ emptyNames e ∧ allVarsInCtx fctx octx e ∧
  AllTypesSimple tvars size bctx e ∧ termDepth bctx e ≤ size

theorem genLExpr_support (...) :
    e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars bctx size τ) ↔
    wellFormedBounded fctx octx tvars bctx size τ e
```

This mirrors the STLC's `genTyped_support` theorem. The extra conjuncts (`emptyNames`, `allVarsInCtx`, `AllTypesSimple`) reflect the richer LExpr language — the STLC doesn't need them because it has no intermediate-type generation and no name/context constraints.

## Proof Impact Assessment

### Soundness (`genLExpr_sound`)

The `| 0, _, SimpleType.arrow ...` case simplifies: no more abs sub-cases. Only bvar/fvar/op, which already have straightforward proofs.

### Bounded soundness (`genLExpr_termDepth_bound`, new)

Follows the same case structure as soundness. Key cases:
- Base atoms (boolConst, intConst, bvar, fvar, op): immediate from `termDepth = 0`.
- Abs at `n+1`: recursive call at size `n`, IH gives `termDepth body ≤ n`, add 1.
- App/ite/eq/quant at `n+1`: recursive calls at size `n`, IH + `max` arithmetic.

### Completeness (`genLExpr_complete`)

The `| 0, _, SimpleType.arrow ...` case shrinks: currently handles bvar/fvar/op/abs. After the change, only bvar/fvar/op remain (abs is excluded by `termDepth ≤ 0`). The `n+1` arrow case is unchanged.

### `AllTypesSimple`

No changes needed — it already requires `n+1` for abs/app/ite/eq/quant constructors.

## Practical Considerations

**Generator efficiency**: Returning `default` instead of constructing a lambda at size 0 means the generator may fail more often when the context lacks arrow-typed bvars/fvars/ops. With a backtracking monad, this is recovered automatically. With `Plausible.Gen` (non-backtracking), the caller at size `n+1` would need to retry. In practice, the size-0 arrow case is typically reached from *within* a lambda body (where the context already has the binder's type), so a bvar is usually available.

**Comparison with quant**: The `quant` case already incorporates `monoTyDepth τ` in `termDepth` because `genLMonoTy` consumes fuel proportional to type depth when generating the quantifier's type annotation. The `abs` case doesn't need this because the type annotation `τ₁` is the *target* type (passed in from the caller), not freshly generated.
