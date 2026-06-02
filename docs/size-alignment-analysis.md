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

## `LExpr.size` from the Strata repo

The Strata `LExpr` module defines its own `size` function (`Strata/DL/Lambda/LExpr.lean:559`):

```lean
def size (T : LExprParamsT) (e : LExpr T) : Nat :=
  match e with
  | .const .. | .op .. | .bvar .. | .fvar .. => 1
  | .abs _ _ _ e' => 1 + size T e'
  | .quant _ _ _ _ _ e' => 1 + size T e'
  | .app _ e1 e2 => 1 + size T e1 + size T e2
  | .ite _ c t f => 1 + size T c + size T t + size T f
  | .eq _ e1 e2 => 1 + size T e1 + size T e2
```

This is a **sum-based node count** (total AST nodes). Key observations:
- Every node contributes at least 1.
- Multi-child nodes accumulate *all* children's sizes (e.g., `app` is `1 + size fn + size arg`).
- `quant` does **not** count the trigger sub-expression in its size — only the body.

### Comparison: `LExpr.size` vs `termDepth`

| Property | `LExpr.size` | `termDepth` |
|---|---|---|
| Combination | sum (additive) | max (depth) |
| Leaves | 1 | 0 |
| `abs _ _ _ body` | `1 + size body` | `termDepth body + 1` |
| `app _ fn arg` | `1 + size fn + size arg` | `max (depth fn) (depth arg) + 1` |
| `ite _ c t e` | `1 + size c + size t + size e` | `max c (max t e) + 1` |
| `eq _ e₁ e₂` | `1 + size e₁ + size e₂` | `max (depth e₁) (depth e₂) + 1` |
| `quant _ _ _ τ tr body` | `1 + size body` (trigger ignored) | `max (monoTyDepth τ) (max (depth tr) (depth body)) + 1` |
| Context-dependence | none | yes (bctx for recursive calls) |
| Type depth | not incorporated | only for `quant` |

### Why `LExpr.size` cannot serve as the generator's fuel bound

The generator's `size` parameter acts as a **depth** control: at `| n + 1, .arrow τ₁ τ₂ =>`, the recursive calls pass `n` to *each* child independently:

```lean
| n + 1, .arrow τ₁ τ₂ =>
    ...
    let body ← genLExpr fctx octx tvars (τ₁ :: bctx) n τ₂       -- abs
    ...
    let arg ← genLExpr fctx octx tvars bctx n τ'                 -- app (arg)
    let fn  ← genLExpr fctx octx tvars bctx n (.arrow τ' ...)    -- app (fn)
    ...
    let c ← genLExpr fctx octx tvars bctx n .bool                -- ite
    let t ← genLExpr fctx octx tvars bctx n (.arrow τ₁ τ₂)      -- ite
    let e ← genLExpr fctx octx tvars bctx n (.arrow τ₁ τ₂)      -- ite
```

Each child gets the *full* budget `n`, not a fraction of it. This is the signature of depth-bounded generation: the budget bounds tree height, not total node count. For example, with `size = 2`, the generator can produce:

```
app (app (bvar 0) (boolConst true)) (intConst 42)
```

This has `termDepth = 2` but `LExpr.size = 5` (three leaves at 1 each, two `app` nodes each adding 1). If we tried to prove `LExpr.size e ≤ size` for generated `e`, it would fail — `LExpr.size` grows exponentially with depth for branching nodes.

**Quantitative bound**: A balanced binary tree of depth `d` has `LExpr.size = 2^(d+1) - 1`. So `genLExpr` at fuel `n` can produce expressions with `LExpr.size` up to `O(3^n)` (ternary branching from `ite`), while `termDepth ≤ n` always holds.

### Relationship: `termDepth ≤ LExpr.size`

For all expressions, `termDepth bctx e ≤ LExpr.size T e` (since depth ≤ node count for any tree). But the converse gap can be arbitrarily large. This means:
- A bound on `termDepth` is *weaker* than a bound on `LExpr.size`.
- The generator controls depth, not total size — `termDepth` is the correct measure.
- `LExpr.size` would be the right measure for a generator that *splits* fuel among children (fuel-splitting/size-bounded generation), but that's not our design.

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

### Approach D: Use `LExpr.size` as the measure (fuel-splitting generator)

**Idea**: Redesign the generator to split fuel among children (like QuickChick's sized generators), and use `LExpr.size` as the bound.

**Why not**: This would be a fundamental redesign of the generator architecture:
1. The generator would need to *choose* how to split budget `n` among children (e.g., for `app`, decide `k` such that `fn` gets budget `k` and `arg` gets budget `n - k - 1`).
2. The completeness theorem becomes harder: you must show that *for every* valid split, the generator can produce the corresponding sub-expression.
3. The depth-bounded approach produces more diverse terms at small fuel values (a balanced tree at depth 3 requires only fuel 3, vs fuel 15 with node-count budgeting).
4. The existing proofs (soundness, completeness, `AllTypesSimple`) are all structured around depth recursion.

Fuel-splitting would be appropriate if we wanted hard bounds on output size (e.g., for fuzzing with bounded-length inputs), but for property-based testing where we want structural diversity, depth-bounded generation is standard.

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

## Implementation Status (Approach C Applied)

Approach C has been implemented. The generator, soundness theorem, and completeness theorem now use a consistent `depth` parameter whose operational meaning matches `termDepth` exactly.

### Why the depth measures now coincide

The key claim is: **for every expression `e` in the support of `genLExpr ... depth τ`, we have `termDepth bctx e ≤ depth`**. This follows from the structure of the generator after the Option C change, by induction on `depth`:

**Base case (`depth = 0`)**:

For each type `τ`, the generator at depth 0 only produces leaf expressions:
- `.bool` / `.int`: produces `boolConst`, `intConst`, `bvar`, `fvar`, `op` — all have `termDepth = 0`.
- `.arrow τ₁ τ₂`: produces `bvar`, `fvar`, or `op` (or fails with `default`) — all have `termDepth = 0`.
- `.ftvar name`: produces `bvar`, `fvar`, or `op` (or fails) — all have `termDepth = 0`.

Before the change, the `.arrow` case at depth 0 could produce `abs () "" (some τ₁) body` where `body` was generated at depth 0. Even though `body` has `termDepth = 0`, the wrapping `abs` adds 1, giving `termDepth = 1 > 0`. This violated the expected bound. Now, with `default` instead of the lambda fallback, no compound expression is produced at depth 0.

**Inductive case (`depth = n + 1`)**:

Every compound constructor recurses at depth `n`:
- `abs`: body generated at depth `n` → by IH, `termDepth body ≤ n` → `termDepth (abs body) = termDepth body + 1 ≤ n + 1`.
- `app`: fn and arg both generated at depth `n` → by IH, both ≤ `n` → `max(...) + 1 ≤ n + 1`.
- `ite`: all three children generated at depth `n` → `max(max(...)) + 1 ≤ n + 1`.
- `eq`: both children at depth `n` → `max(...) + 1 ≤ n + 1`.
- `quant`: type `τ'` generated by `genLMonoTy tvars n` has `monoTyDepth τ' ≤ n`; trigger and body generated at depth `n` → `max(monoTyDepth τ', max(depth tr, depth body)) + 1 ≤ n + 1`.
- Leaf cases (bvar/fvar/op/const) in the `n+1` branches: `termDepth = 0 ≤ n + 1`.

This is not yet a formally proved theorem (a `genLExpr_termDepth_bound` theorem), but it follows mechanically from the generator structure and is the missing piece for the full `↔` characterization.

### How the three theorems relate

After implementing Approach C, the theorem landscape is:

```
genLExpr_sound:    e ∈ support(genLExpr ... depth τ) → HasTypeA' bctx e τ
                                                       ∧ emptyNames e
                                                       ∧ allVarsInCtx ...
                                                       ∧ AllTypesSimple ...

genLExpr_complete: HasTypeA' bctx e τ
                   ∧ emptyNames e
                   ∧ allVarsInCtx ...
                   ∧ AllTypesSimple tvars depth bctx e
                   ∧ termDepth bctx e ≤ depth
                   → e ∈ support(genLExpr ... depth τ)

genLExpr_termDepth_bound (not yet proved):
                   e ∈ support(genLExpr ... depth τ) → termDepth bctx e ≤ depth
```

The three combine to give:
```
e ∈ support(genLExpr ... depth τ) ↔ wellFormedBounded ... depth τ e
```

The `termDepth_bound` theorem is the "glue" — without it, soundness is strictly weaker than the backward direction of completeness (soundness doesn't bound depth), so you can't derive the `↔` from `→` and `←` alone.

### Why `AllTypesSimple` and `termDepth` use the same `depth` parameter

Both `AllTypesSimple tvars depth bctx e` and `termDepth bctx e ≤ depth` decrease by 1 at each compound constructor. This is not a coincidence — they both track the generator's fuel consumption:

- `AllTypesSimple tvars n (τ₁ :: bctx) body` at level `n` means: all *intermediate* types in `body` (those generated by `genLMonoTy n` during expression generation) have depth ≤ `n` and are simple. The generator at level `n+1` calls `genLMonoTy n` to produce intermediate types, then recurses at level `n` for sub-expressions.

- `termDepth bctx e ≤ n` at level `n` means: the expression tree has at most `n` levels of compound constructors above any leaf.

Both track the same resource: how many "levels" of the generator were consumed. `AllTypesSimple` constrains the *types* at each level, while `termDepth` constrains the *structure*. Together they fully characterize the generator's output at a given depth.

### The naming convention

Throughout the codebase, the generator parameter is now named `depth` (not `size`) to reflect its operational meaning: it bounds tree depth, not tree size. The completeness hypothesis is `hdepth : termDepth bctx e ≤ depth` and the termination measure is `termination_by (depth, sizeOf τ)`.

The word "size" is reserved for `LExpr.size` (node count) when we need it in Tyche visualizations or comparison discussions.
