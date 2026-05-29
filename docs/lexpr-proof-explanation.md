# Proof of Soundness and Completeness for the LExpr Generator

This document explains the correctness proofs for the well-typed `LExpr` random generator in
[`StrataGenerators/LExprGen.lean`](StrataGenerators/LExprGen.lean).

## Overview

We prove two main results:

1. **`genLMonoTy` is sound and complete** — it generates exactly the "simple types" (built from
   `bool`, `int`, and `arrow`) of bounded depth.
2. **`genLExpr` is sound** — every expression it generates is well-typed under the given context.

The proofs use Basalt's `SetGen` framework, which interprets generators as `Set α` (predicates
`α → Prop`). Under this interpretation, a generator's "support" is the set of all values it can
produce. Proving soundness means showing that every value in the support satisfies a property;
completeness means showing every value satisfying the property is in the support.

## The SetGen Framework

The key idea: instantiate the generator monad `G` to `SetGen.Set` (a type alias for `α → Prop`).
Under this interpretation:

- `pure a` becomes the singleton `{a}` (i.e., `fun b => b = a`)
- `bind s f` becomes `fun b => ∃ a ∈ s, b ∈ f a`
- `pick x y` becomes `x ∪ y` (set union)
- `choose lo hi _` becomes `{n | lo ≤ n ∧ n ≤ hi}`

Simp lemmas like `mem_support_pick_iff`, `SetGen.Set.mem_bind`, and `SetGen.Set.mem_pure`
decompose membership in these combinators into logical propositions suitable for `rcases`.

## Proof Structure

### Part 1: `genLMonoTy_support` (biconditional)

**Statement:**
```
τ ∈ support (genLMonoTy n) ↔ SimpleType τ ∧ monoTyDepth τ ≤ n
```

**Strategy:** Induction on the fuel parameter `n`.

- **Forward direction (→):** Unfold `genLMonoTy` via simp with its equation lemmas and
  `mem_support_pick_iff`. The hypothesis `he` decomposes into disjuncts — one per `pick` branch.
  Each branch directly witnesses which `SimpleType` constructor applies.

- **Backward direction (←):** Case-split on `SimpleType τ`:
  - `bool` / `int`: These are immediate base cases of `pick`.
  - `arrow hs₁ hs₂`: Use the depth bound to show both sub-types satisfy the induction
    hypothesis, then reassemble using the `bind` branch for `genLMonoTy`.

- **Zero case, arrow contradiction:** If `SimpleType (.arrow τ₁ τ₂)` but `monoTyDepth ≤ 0`,
  we derive `False` via `monoTyDepth.eq_1` (which says
  `monoTyDepth (.tcons "arrow" [τ₁, τ₂]) = max ... + 1 ≤ 0`).

### Part 2: `genLExpr_sound` (soundness)

**Statement:**
```
SimpleType τ → e ∈ support (genLExpr bctx size τ) → WellTyped bctx e τ
```

**Strategy:** Well-founded recursion on `(size, sizeOf τ)`, case-splitting on
`(size, τ, hτ)` — six cases total: `{0, n+1} × {bool, int, arrow}`.

For each case:

1. **Normalize the type abbreviation** with `rw [norm_bool]` / `rw [norm_int]` / `rw [norm_arrow]`.
   This is necessary because Lean's equation lemmas for `genLExpr` are keyed on the expanded
   `.tcons` form (see [below](#the-abbreviation-problem)).

2. **Simplify membership** with
   `simp only [genLExpr, pick_mem_iff, SetGen.Set.mem_bind, SetGen.Set.mem_pure, ...]`.
   This unfolds the generator into a nested disjunction of existential statements.

3. **Decompose with `rcases`** into one sub-goal per generator branch (e.g., `boolConst`,
   `ite`, `eq`, `app`, `quant`, `pickBVar`).

4. **Apply the corresponding `WellTyped` constructor** and recurse. Each recursive call goes
   to a strictly smaller `(size, sizeOf τ)` pair:
   - Succ cases: `n + 1 → n` (size decreases).
   - Zero/arrow case: `(0, .arrow τ₁ τ₂) → (0, τ₂)` (type gets smaller since
     `sizeOf τ₂ < sizeOf (.arrow τ₁ τ₂)`).

### Auxiliary lemmas

#### `bvarsOfType_mem_iff`

Bridges the helper list `bvarsOfType bctx τ` (which computes de Bruijn indices of type `τ`)
to the `List.getElem?` operation on the context:

```
i ∈ bvarsOfType bctx τ ↔ bctx[i]? = some τ
```

Proved by induction on the context list, tracking a base-index offset.

#### `pickBVar_sound` / `pickBVar_complete`

- **Sound:** If `e ∈ support (pickBVar bctx τ hv)`, then `e = .bvar () i` for some `i` with
  `bctx[i]? = some τ`. This follows from `bvarsOfType_mem_iff` and the fact that `choose`
  picks a valid index into the `bvarsOfType` list.

- **Complete:** If `bctx[i]? = some τ`, then `.bvar () i` is in the support. We find the
  position of `i` in the `bvarsOfType` list (via `List.getElem_of_mem`) and show that
  `choose` can select that position.

#### `genLMonoTy_simple`

A corollary extracting just the `SimpleType` part from `genLMonoTy_support`:
```
τ ∈ support (genLMonoTy n) → SimpleType τ
```

Used in `genLExpr_sound` when the generator picks a random type via `genLMonoTy` — we need to
know the generated type is `SimpleType` to recurse.

## The Abbreviation Problem

Strata defines type constructors as abbreviations:
```lean
abbrev LMonoTy.bool := .tcons "bool" []
abbrev LMonoTy.arrow τ₁ τ₂ := .tcons "arrow" [τ₁, τ₂]
```

When `genLExpr` pattern-matches on `.arrow τ₁ τ₂`, Lean's equation compiler generates lemmas
with the expanded form in their LHS:
```
genLExpr.eq_1 : genLExpr bctx 0 (LMonoTy.tcons "arrow" [τ₁, τ₂]) = ...
```

After case-splitting on `SimpleType τ`, the hypothesis mentions `LMonoTy.arrow τ₁ τ₂`. Although
this is *definitionally equal* to `LMonoTy.tcons "arrow" [τ₁, τ₂]`, `simp`/`rw` require
*syntactic* equality to fire. The `norm_arrow` rewrite lemma bridges this gap:
```lean
private theorem norm_arrow (τ₁ τ₂) : LMonoTy.arrow τ₁ τ₂ = LMonoTy.tcons "arrow" [τ₁, τ₂] := rfl
```

This problem does not arise in Basalt's STLC example because `typ.Fun` is a proper inductive
constructor, not an abbreviation.

## Termination

`genLExpr_sound` uses `termination_by (size, sizeOf τ)` with lexicographic ordering:

- All `n+1` cases recurse with `n` → first component decreases.
- The `0, .arrow τ₁ τ₂` case recurses on `τ₂` → second component decreases
  (since `sizeOf τ₂ < sizeOf (.tcons "arrow" [τ₁, τ₂])`).

The `decreasing_by` tactic handles both cases: plain `omega` for the size decrease, and
`simp_all [LMonoTy.arrow]; omega` for the type-size decrease (which needs to unfold the
abbreviation to expose the `sizeOf` arithmetic).

## What Is and Isn't Proved

**Proved:**
- `genLMonoTy` is sound and complete for `SimpleType τ ∧ monoTyDepth τ ≤ n`.
- `genLExpr` is sound: every generated expression is well-typed.

**Not proved (future work):**
- Completeness of `genLExpr` (every well-typed expression of bounded size is generable).
- That the generator terminates with probability 1 (would require the `SPMF` interpretation
  rather than `SetGen`).
- Coverage of the full Strata type system (we restrict to `SimpleType` — no type variables,
  polymorphism, or user-defined type constructors).
