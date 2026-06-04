# Indir Rule for Well-Typed LExpr Generation

## Summary

This adds the **Indir rule** from [Palka et al. 2011](https://doi.org/10.1145/1982595.1982615) to the generator of well-typed `LExpr`s. The Indir rule generates fully-applied operator applications without type guessing, producing expressions like `Int.Add #1 #2` directly rather than relying on the App rule to randomly guess the intermediate type `Int`.

## What changed

### `HasTypeAGen/Core.lean`

- **`genLExprBase`** (renamed from `genLExpr`): the original generator, unchanged in logic. Handles Var, Lam, App (with random type), Ite, Eq, Quant rules.

- **New helpers** for the Indir rule:
  - `argsForResult fullTy τ` — peels arrows off `fullTy` and checks if the result type is `τ`. Returns `some [σ₁, ..., σₙ]` if `fullTy = σ₁ → ... → σₙ → τ`.
  - `findOpsInCtx octx τ` — finds all operators in `octx` whose result type (after full application) is `τ`, requiring at least one argument.
  - `mkApps base args` — builds left-nested application `((base arg₁) arg₂) ...`.

- **`genLExpr`** (new): wraps `genLExprBase` with a `pick` against the Indir rule. When `findOpsInCtx octx τ` is non-empty, non-deterministically chooses between:
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
  - `mem_foldrM_cons_iff` — characterizes membership in `List.foldrM` (with the cons-accumulator pattern) on `SetGen.Set` as `List.Forall₂` of pointwise memberships.
  - `findOpsInCtx_mem` — if `(name, argTys) ∈ findOpsInCtx octx τ`, then the operator's full curried type is in `octx` and `argTys` is non-empty.

- **`genLExpr_sound`** — soundness of the new `genLExpr`. Fully proved (no sorry). The standard-generation branch delegates to `genLExprBase_sound`. The Indir branch:
  1. Destructures the membership witness to obtain the chosen operator index and generated args.
  2. Uses `findOpsInCtx_mem` to recover that the operator's full type is in `octx`.
  3. Uses `mem_foldrM_cons_iff` to convert the `foldrM` membership into `List.Forall₂` of individual `genLExprBase` memberships.
  4. Applies `genLExprBase_sound` pointwise (by induction on the `Forall₂`) using `simpleType_of_foldr_mem` to discharge `SimpleType` obligations for each argument type.
  5. Assembles the final typing judgement via `mkApps_hasType`.

## Design notes

### Why `mem_foldrM_cons_iff` instead of Batteries' `satisfiesM_foldrM`

Batteries provides `List.satisfiesM_foldrM` which uses a monotone-motive `SatisfiesM` predicate. For our use case (characterizing *exact membership* in a `SetGen.Set`-valued `foldrM`), we need an iff, not just a forward implication. `SatisfiesM` for `Set` gives `∀ a ∈ s, p a` (universal over the set), but we need the converse direction too — that any list satisfying the pointwise condition *is* in the `foldrM` support. The direct inductive proof on the type list is short (6 lines per direction) and avoids contorting `SatisfiesM` into a biconditional.

### Why not a named recursive helper (`genIndirArgs`)

The INDIR_RULE.md previously suggested replacing `foldrM` with a named helper to simplify the proof. With `mem_foldrM_cons_iff` in hand, the `foldrM` formulation works directly and keeps the generator definition concise — no auxiliary function needed.
