# Strata Generators

## Using `fun_induction` for generator soundness proofs

When proving soundness (i.e., a generator only produces values satisfying some spec), use the `fun_induction` tactic to induct on the generator's recursion structure.

### Pattern

```lean
theorem genFoo_sound : ∀ (size : ℕ) (τ : Ty) (e : Expr),
    e ∈ SetGen.support (genFoo size τ) → HasType e τ := by
  intro size τ e H
  fun_induction genFoo (G := SetGen.Set) size τ generalizing e with
  | case1 => ...
  | case2 => ...
  | case3 size' ih_nat ih_bool => ...
  | case4 size' ih_nat ih_bool => ...
```

### Key rules

1. **Use `generalizing e`** so the IHs are universally quantified over `e` (and `H`, which depends on it). Without `generalizing`, the IHs get specialized to the fixed `e` introduced before `fun_induction` and become useless for sub-expressions. Alternatively, don't introduce `e`/`H` before `fun_induction` and use `intro e H` inside each case arm.

2. **Supply `(G := SetGen.Set)`** to resolve the `[Gen G]` typeclass instance, since the function is polymorphic over the generator monad.

3. **Case names are `case1`, `case2`, ...** corresponding to the match arms in definition order. Use comments or check `#check genFoo.induct` to see what each case represents.

4. **IHs are named per recursive call site**, e.g. `ih_nat` and `ih_bool` if the generator recurses at both types. They have type `∀ e, e ∈ support (genFoo size' τ) → Spec e τ`.

5. **After `fun_induction`, use `simp only [mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H`** to normalize the membership hypothesis into a disjunction of existentials, then `rcases` to destructure.

### When NOT to use `fun_induction`

For monotonicity or completeness proofs where the goal also contains the generator at a different size, `fun_induction` provides little benefit — the hard part is constructing membership in the goal (via `dsimp only [genFoo]` + `rw [mem_support_pick_iff]` chains), which is identical either way. Use manual `induction`/`cases` for those.
