# Refactoring generators to use `elements`

## Status

- Updated Basalt to latest `ernest/combinators` (commit `f89129f`) which includes `elements`
- Added `support_elements` and `mem_support_elements_iff` lemmas to `StrataGenerators/SetGen/Support.lean`
- ✅ All 6 generators updated to use `elements` (pickBVar, pickFVar, pickOp, pickTyVar, pickBitvecWidth, Char.arbitrary)
- ✅ All proofs updated (soundness, completeness, termDepth bound)
- ✅ Build passes

## Basalt's `elements` combinator

```lean
def elements [Gen G] [Inhabited α] (xs : List α) : G α := do
  let i ← ULift.down <$> RandomChoice.choose 0 (xs.length - 1) (by omega)
  return xs[i]!
```

Key support lemma (in `Basalt/SPMF/Support.lean`, ported to `SetGen/Support.lean`):
```lean
theorem mem_support_elements_iff [Inhabited α] {xs : List α} (hne : xs ≠ []) :
    a ∈ support (elements xs : Set α) ↔ a ∈ xs
```

## Generators to update in `HasTypeAGen/Core.lean`

All follow the pattern: `choose 0 (xs.length - 1); return xs[idx]` → `elements xs` (or `f <$> elements xs`).

### 1. `pickTyVar` (line 163)

Before:
```lean
def pickTyVar [Gen G] (tvars : List TyIdentifier) (_h : tvars.length > 0) : G LMonoTy := do
  let idx ← choose 0 (tvars.length - 1) (by omega)
  pure (.ftvar (tvars.getD idx.down ""))
```

After:
```lean
def pickTyVar [Gen G] [Inhabited LMonoTy] (tvars : List TyIdentifier) (_h : tvars.length > 0) : G LMonoTy :=
  LMonoTy.ftvar <$> elements tvars
```

### 2. `pickBitvecWidth` (line 170)

Before:
```lean
def pickBitvecWidth [Gen G] : G LMonoTy := do
  let idx ← choose 0 (bitvecWidths.length - 1) (by native_decide)
  pure (.bitvec (bitvecWidths.getD idx.down 32))
```

After:
```lean
def pickBitvecWidth [Gen G] [Inhabited LMonoTy] : G LMonoTy :=
  LMonoTy.bitvec <$> elements bitvecWidths
```

### 3. `pickBVar` (line 120)

Before:
```lean
def pickBVar [Gen G] (bctx : BVarCtx) (τ : LMonoTy) (_h : ...) : G LExpr' := do
  let indices := bvarsOfType bctx τ
  let idx ← choose 0 (indices.length - 1) (by omega)
  pure (.bvar () (indices.getD idx.down 0))
```

After:
```lean
def pickBVar [Gen G] [Inhabited LExpr'] (bctx : BVarCtx) (τ : LMonoTy) (_h : ...) : G LExpr' :=
  elements ((bvarsOfType bctx τ).map (.bvar () ·))
```

### 4. `pickFVar` (line 133)

After:
```lean
def pickFVar [Gen G] [Inhabited LExpr'] (fctx : FVarCtx) (τ : LMonoTy) (_h : ...) : G LExpr' :=
  elements ((fvarsOfType fctx τ).map (fun name => .fvar () ⟨name, ()⟩ (some τ)))
```

### 5. `pickOp` (line 144)

After:
```lean
def pickOp [Gen G] [Inhabited LExpr'] (octx : OpCtx) (τ : LMonoTy) (_h : ...) : G LExpr' :=
  elements ((opsOfType octx τ).map (fun name => .op () ⟨name, ()⟩ (some τ)))
```

### 6. `Char.arbitrary` (line 251)

After:
```lean
def Char.arbitrary [Gen G] [Inhabited Char] : G Char :=
  elements alphanumChars
```

## Proofs to update in `HasTypeAGen.lean`

The proofs for `pickBVar_sound`, `pickBVar_complete`, `pickFVar_sound`, `pickFVar_complete`,
`pickOp_sound`, `pickOp_complete`, `pickTyVar_mem`, `pickTyVar_complete`, `pickBitvecWidth_mem`,
`pickBitvecWidth_complete` all currently use:

```lean
simp only [pickXxx, mem_support_iff, Set.mem_bind, Set.mem_pure]
```

With `elements`, they should simplify to:

```lean
simp only [pickXxx, mem_support_map_iff, mem_support_elements_iff (by simp [...])]
```

The key insight: `mem_support_elements_iff` gives `a ∈ support (elements xs) ↔ a ∈ xs`,
and `mem_support_map_iff` gives `b ∈ support (f <$> x) ↔ ∃ a ∈ support x, b = f a`.

So for e.g. `pickBVar`, soundness becomes:
- `e ∈ support (elements (... .map (.bvar () ·)))` 
- ↔ `e ∈ (bvarsOfType bctx τ).map (.bvar () ·)` (by `mem_support_elements_iff`)
- ↔ `∃ i ∈ bvarsOfType bctx τ, e = .bvar () i` (by `List.mem_map`)

And completeness becomes:
- Need to show `.bvar () i ∈ support (elements (...))` given `i ∈ bvarsOfType bctx τ`
- By `mem_support_elements_iff`, suffices to show `.bvar () i ∈ (bvarsOfType bctx τ).map (.bvar () ·)`
- Which follows from `List.mem_map.mpr ⟨i, hmem, rfl⟩`

## Note on `Inhabited` constraint

`elements` requires `[Inhabited α]`. This means adding `[Inhabited LExpr']` or
`[Inhabited LMonoTy]` constraints to the pick helpers. Since `LExpr'` likely already has
a `Deriving Inhabited` or you can add a manual instance (e.g. `instance : Inhabited LExpr' := ⟨.boolConst () false⟩`), this should be straightforward. Check if instances already exist.

## `CmdHasTypeAGen/Core.lean`

This file doesn't have any direct candidates — it uses `choose` for picking from `ctx`
(line 81-82) but wraps it in more complex logic. No change needed here.
