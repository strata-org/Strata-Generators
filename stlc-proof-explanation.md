# Soundness and Completeness Proofs for the STLC Generator

This document explains the proof ideas behind the soundness and completeness theorems for the STLC generator in `Basalt/Examples/STLC.lean`.

## The Key Insight: `SetGen.Set` as a Verification Oracle

The entire approach rests on one elegant trick: `SetGen.Set α` is just `α → Prop` — a plain set (predicate). The generator code (`genTyped`, `genType`, etc.) is **polymorphic** over a `Gen` typeclass, so the *same code* can be instantiated with:

1. A real random generator (for testing)
2. `SetGen.Set` (for proving)

When instantiated at `SetGen.Set`, monadic operations become set operations:
- `pure a` = the singleton `{a}`
- `x >>= f` = `{b | ∃ a ∈ x, b ∈ f a}` (relational composition)
- `pick x y` = `x ∪ y` (union — nondeterministic choice becomes "both branches")
- `default` = `∅` (failure/empty)

So `SetGen.support (genTyped Γ size τ)` is literally **the set of all terms the generator could ever produce** — every possible execution path, unioned together. No probability reasoning needed.

## Soundness (`genTyped_sound`)

**Goal:** If `e ∈ support(genTyped Γ size τ)`, then `typing Γ e τ`.

**Proof strategy:** Induction on `size`, case-split on `τ`.

At each step, `simp` unfolds the generator definition and rewrites membership using the set-theoretic lemmas:
- `pick_mem_iff` turns `∈ pick x y` into `∈ x ∨ ∈ y`
- `mem_dite` handles the `if` branches
- `mem_support_bind_iff` decomposes bind into existentials

This decomposes the membership hypothesis into a disjunction — one case per generator branch (Const, Add, App, Abs, Var).

For each branch, the proof destructures the existentials from `>>=` (bind = `∃ intermediate value`) and applies the corresponding typing rule. For recursive sub-generators, the inductive hypothesis gives the typing of subterms. For `pickVar`, a helper (`pickVar_typing`) shows the chosen index has a valid `lookup` in the context — it works by showing `indicesOfType` only returns indices where the context has the right type.

### What `pick_mem_iff` does concretely

`pick` is the generator's nondeterministic choice combinator. In a real random generator, `pick f g` flips a coin and runs either `f ()` or `g ()`. But at `SetGen.Set`, `pick` becomes set union:

```lean
theorem pick_mem_iff {x y : Set α} (a : α) :
    a ∈ (pick (fun () => x) (fun () => y) : Set α) ↔ a ∈ x ∨ a ∈ y
```

When proving soundness and you have `e ∈ support (pick ...)`, applying `pick_mem_iff` gives you `e ∈ branch1 ∨ e ∈ branch2`, which you then case-split on. Each case corresponds to one constructor of the term language.

It turns "I don't know which random path was taken" into "let me consider each path separately" — exactly what you need for a proof by cases over the generator's structure.

## Completeness (`genTyped_complete`)

**Goal:** If `typing Γ e τ`, then `e ∈ support(genTyped Γ size τ)` for large enough `size`.

This is harder because you need to show every well-typed term is reachable by *some* execution path.

### Two-part strategy

1. **Define `termSize`** — a measure of how "deep" a term is relative to its context. Variables contribute their type's depth (since the generator needs enough budget to handle function types in scope). This is the crucial design choice.

2. **Prove the auxiliary `genTyped_complete_aux`**: induction on the *typing derivation* (`htyp`), with the hypothesis that `termSize Γ e ≤ size` and `typDepth τ ≤ size`.

   For each typing rule, you show the term lands in the right `pick` branch:
   - `TConst`: lands in the `Const` branch (trivially, since `Nat.arbitrary` generates all naturals)
   - `TAbs`: lands in the `Abs` branch — the guard `typDepth τ > size+1` is false (by hypothesis), and the recursive IH handles the body
   - `TApp`: lands in the `App` branch — the intermediate type `τ1` is in `genType`'s support (by `genType_support`), and both subterms are in `genTyped`'s support (by IH)
   - `TVar`: lands in the `Var` branch — `pickVar_complete` shows the variable's index is among those returned by `indicesOfType`, using `lookup_mem_indicesOfType`

The wrapper theorem `genTyped_complete` just instantiates `size := termSize Γ e`, which satisfies both preconditions by `typDepth_le_termSize_of_typing` and `le_rfl`.

## Why `termSize` matters

The generator guards against unbounded recursion with `if typDepth τ > size then default`. Completeness requires showing this guard is never hit for the "right" size. `termSize` is carefully defined so that:
- For `App e1 e2` at type `τ2`: the function `e1` has type `Fun τ1 τ2`, so `typDepth(Fun τ1 τ2) ≤ termSize Γ e1 ≤ size` — the intermediate type fits within budget
- For `Var x` at type `τ`: `typDepth τ = typDepth(Γ[x])` which is exactly how `termSize` measures variables

This ensures the size parameter decreases properly through recursive calls while remaining large enough to avoid the guard.

## Summary

The proofs work because the `SetGen.Set` instantiation converts the generator into a pure set-comprehension, letting you reason about reachability with standard set/logic tactics. Soundness is straightforward structural decomposition; completeness requires the `termSize` measure to witness that every well-typed term fits within the generator's size budget.
