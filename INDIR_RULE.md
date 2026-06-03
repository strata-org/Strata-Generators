# Indir Rule for Well-Typed LExpr Generation

## Summary

This adds the **Indir rule** from [Palka et al. 2011](https://doi.org/10.1145/1982595.1982615) to the generator of well-typed `LExpr`s. The Indir rule generates fully-applied operator applications without type guessing, producing expressions like `Int.Add #1 #2` directly rather than relying on the App rule to randomly guess the intermediate type `Int`.

## What changed

### `HasTypeAGen/Core.lean`

- **`genLExprBase`** (renamed from `genLExpr`): the original generator, unchanged in logic. Handles Var, Lam, App (with random type), Ite, Eq, Quant rules.

- **New helpers** for the Indir rule:
  - `argsForResult fullTy τ` — peels arrows off `fullTy` and checks if the result type is `τ`. Returns `some [σ₁, ..., σₙ]` if `fullTy = σ₁ → ... → σₙ → τ`.
  - `opsReturning octx τ` — finds all operators in `octx` whose result type (after full application) is `τ`, requiring at least one argument.
  - `mkApps base args` — builds left-nested application `((base arg₁) arg₂) ...`.

- **`genLExpr`** (new): wraps `genLExprBase` with a `pick` against the Indir rule. When `opsReturning octx τ` is non-empty, non-deterministically chooses between:
  1. **Indir**: pick a random operator returning `τ`, generate all arguments at their determined types via `genLExprBase`.
  2. **Standard**: delegate to `genLExprBase`.

- **`genClosedLExpr`**: unchanged interface, now uses the new `genLExpr`.

### `HasTypeAGen/Defs.lean`

- `genLExprWithFactory` and `genClosedLExprWithFactory` now use `genLExpr` (with Indir).
- Removed the old `genLExprIndirWithFactory` / `genClosedLExprIndirWithFactory` wrappers.

### `HasTypeAGen.lean` (proofs)

- All existing proofs (`genLExprBase_sound`, `genLExprBase_termDepth_bound`, `genLExprBase_complete`) renamed to reference `genLExprBase`. They are unchanged in content and fully proved.

- New helper theorems (all proved):
  - `SimpleType_arrow_inv` — inversion for `SimpleType` at arrow types (works around the `LMonoTy.arrow` abbreviation issue).
  - `argsForResult_eq` — correctness of `argsForResult`.
  - `simpleType_of_foldr_mem` — SimpleType propagates through iterated arrows.
  - `mkApps_hasType` — iterated `HasTypeA.app`.
  - `opsReturning_mem` — membership characterization for `opsReturning`.

- **`genLExpr_sound`** — soundness of the new `genLExpr`. The standard-generation branch delegates to `genLExprBase_sound`. The Indir branch has one `sorry`.

## The remaining `sorry`

In `HasTypeAGen.lean`, the Indir case of `genLExpr_sound`:

```lean
theorem genLExpr_sound (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat)
    (τ : LMonoTy) (hτ : SimpleType τ)
    (hSimpleOps : ∀ p ∈ octx, SimpleType p.2)
    (e : LExpr')
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx tvars bctx depth τ)) :
    HasTypeA' bctx e τ := by
  unfold genLExpr at he
  simp only [mem_support_iff, SetGen.mem_dite, pick_mem_iff] at he
  rcases he with ⟨hpos, he | he⟩ | ⟨_, he⟩
  · -- Indir path: fully-applied operator
    sorry
  · exact genLExprBase_sound fctx octx tvars bctx depth τ hτ e he
  · exact genLExprBase_sound fctx octx tvars bctx depth τ hτ e he
```

### Why it's sorry'd

The Indir branch uses `List.foldrM` to generate arguments inline:

```lean
let args ← argTys.foldrM (init := ([] : List LExpr')) fun σ acc => do
  let arg ← genLExprBase fctx octx tvars bctx depth σ
  pure (arg :: acc)
```

After `simp` unfolds `genLExpr`, `he` in the Indir branch has the form:

```
∃ idx, ..., ∃ args, args ∈ support (argTys.foldrM ...) ∧ e = mkApps base args
```

To complete the proof, you need:

1. **A `foldrM` support lemma for `SetGen.Set`**: something like
   ```lean
   theorem SetGen.Set.mem_foldrM {f : α → β → Set β} {init : β} {l : List α} {b : β} :
       b ∈ (l.foldrM f init) ↔ <characterization involving support of each f call>
   ```
   This doesn't exist in the current `SetGen` library. The characterization is:
   the result is reachable iff there exist intermediate values `b₀ = init, b₁ ∈ f aₙ b₀, ..., bₙ ∈ f a₁ bₙ₋₁` with `b = bₙ`.

2. **Once you have that**, the proof is: destructure the `foldrM` membership into individual `genLExprBase` memberships, apply `genLExprBase_sound` to each, assemble into `List.Forall₂`, then apply `mkApps_hasType`.

### How to fix it

**Option A (recommended)**: Replace `foldrM` with a named recursive helper `genIndirArgs` defined *before* `genLExpr` in Core.lean. This restores the old proof structure (simple induction on the arg list) without adding an extra user-facing name. Mark it `private` so it doesn't pollute the namespace:

```lean
private def genIndirArgs [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) :
    List LMonoTy → G (List LExpr')
  | [] => pure []
  | τ :: rest => do
    let arg ← genLExprBase fctx octx tvars bctx depth τ
    let args ← genIndirArgs fctx octx tvars bctx depth rest
    pure (arg :: args)
```

Then in `genLExpr`, replace the `foldrM` with `genIndirArgs`. The soundness proof becomes a straightforward induction (same as the previously-proved `genIndirArgs_sound`).

**Option B**: Add a `SetGen.Set.mem_foldrM` lemma to `SetGen/Support.lean` characterizing `List.foldrM` support in terms of pointwise membership. This is more general but more work.
