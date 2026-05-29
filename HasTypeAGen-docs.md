# HasTypeA Generator: Architecture and Proof Structure

This document explains how the random generator of well-typed terms in
`StrataGenerators/HasTypeAGen.lean` works, how it relates to the `HasTypeA`
typing rules, and what auxiliary lemmas are needed for the soundness and
completeness proofs.

## Background: `dite` (Decidable If-Then-Else)

In Lean 4, `dite` is the dependent if-then-else combinator:
```lean
dite (p : Prop) [Decidable p] (t : p → α) (e : ¬p → α) : α
```
Written as `if h : p then t h else e h`, it lets both branches access a proof
of the condition (or its negation). We use `dite` extensively in the generator
to guard branches on whether witnesses exist — e.g.,
`if hv : (bvarsOfType bctx τ).length > 0 then pickBVar bctx τ hv else ...`
passes the length proof `hv` to `pickBVar` which requires it.

In proofs, `dite` membership is decomposed by `mem_support_dite_iff`:
```
a ∈ support (dite p t e) ↔ (∃ h : p, a ∈ support (t h)) ∨ (∃ h : ¬p, a ∈ support (e h))
```

## The `HasTypeA` Typing Rules

Strata's `LExpr.HasTypeA` is a typing judgement for annotated lambda
expressions. Given a bound-variable context `Δ : List LMonoTy` (where
`Δ[i]?` gives the type of `bvar i`), the rules are:

| Rule | Expression | Type |
|------|-----------|------|
| `const` | `.const m c` | `c.ty` (determined by the constant) |
| `op` | `.op m o (some ty)` | `ty` (from annotation) |
| `fvar` | `.fvar m x (some ty)` | `ty` (from annotation) |
| `bvar` | `.bvar m i` | `t` where `Δ[i]? = some t` |
| `abs` | `.abs m name (some aty) body` | `.arrow aty rty` where `body : rty` under `aty :: Δ` |
| `app` | `.app m fn arg` | `rty` where `fn : .arrow aty rty` and `arg : aty` |
| `ite` | `.ite m c t e` | `τ` where `c : .bool`, `t : τ`, `e : τ` |
| `eq` | `.eq m e1 e2` | `.bool` where `e1 : τ` and `e2 : τ` |
| `quant` | `.quant m k name (some qty) tr body` | `.bool` where `tr : τ_tr` and `body : .bool` under `qty :: Δ` |

Key properties used in our proofs:
- **Determinism** (`HasTypeA_unique` from Strata): if `e : τ₁` and `e : τ₂`
  then `τ₁ = τ₂`. This follows from `typeCheck` being a function.
- **Equivalence with `typeCheck`** (`HasTypeA_iff_typeCheck`): the inductive
  relation is equivalent to the computable `typeCheck` function returning `some τ`.

## Generator Architecture

### Type Generator: `genLMonoTy`

Generates types from the fragment `SimpleType` (bool, int, arrow, ftvar) with
bounded depth. The `tvars` parameter controls which free type variable names
may appear.

**Structure** (applying Palamedes optimization rules 5/6 — lifting `dite` out
of `pick`):
```
genLMonoTy tvars 0 =
  if tvars.length > 0 then
    pick bool (pick int (pickTyVar tvars))
  else
    pick bool int

genLMonoTy tvars (n+1) =
  if tvars.length > 0 then
    pick bool (pick int (pick (arrow (genLMonoTy n) (genLMonoTy n)) (pickTyVar tvars)))
  else
    pick bool (pick int (arrow (genLMonoTy n) (genLMonoTy n)))
```

The `dite` is at the top level (not nested inside `pick`) so that
`mem_support_dite_iff` can decompose membership goals cleanly.

### Expression Generator: `genLExpr`

Generates well-typed expressions by pattern-matching on (size, target type):

- **Base types at size 0** (bool, int, ftvar): pick from literals (bool/int
  only) and available bvars/fvars/ops of the right type.
- **Arrow types at size 0**: pick from bvars/fvars/ops, with `abs` as fallback.
- **All types at size n+1**: additionally try `app` (with a random intermediate
  type from `genLMonoTy n`), `ite`, and for bool: `eq` and `quant`.

Each branch uses `pick` to non-deterministically choose between alternatives
and `dite` guards to check whether witnesses exist (e.g., whether there are
bvars of the right type). When no witness exists, the branch falls through to
a default or another alternative.

## Soundness Theorem

```lean
theorem genLExpr_sound : ∀ e ∈ support (genLExpr fctx octx tvars bctx size τ),
    HasTypeA' bctx e τ
```

**Proof strategy**: Structural induction on `(size, τ)`. After `simp` unfolds
the generator and decomposes `pick`/`dite` membership, `rcases` destructs the
disjunction into cases for each generator branch, then applies the appropriate
`HasTypeA` constructor.

### Auxiliary lemmas for soundness

| Lemma | Purpose |
|-------|---------|
| `pickBVar_sound` | Any bvar from `pickBVar` is well-typed (uses `bvarsOfType_mem_iff`) |
| `pickFVar_sound` | Any fvar from `pickFVar` is well-typed |
| `pickOp_sound` | Any op from `pickOp` is well-typed |
| `pickTyVar_mem` | Any type from `pickTyVar` is `.ftvar name` with `name ∈ tvars` |
| `genLMonoTy_simple` | Any type from `genLMonoTy` satisfies `SimpleType` |
| `norm_bool`, `norm_int`, `norm_arrow` | Normalize type abbreviations so `simp [genLExpr]` equation lemmas can match |

## Completeness Theorem

```lean
theorem genLExpr_complete :
    HasTypeA' bctx e τ → emptyNames e → allVarsInCtx fctx octx e →
    AllTypesSimple tvars size bctx e → termDepth bctx e ≤ size →
    e ∈ support (genLExpr fctx octx tvars bctx size τ)
```

**Preconditions** (beyond well-typing):
- `emptyNames e`: all binder names are `""` (the generator only produces empty names)
- `allVarsInCtx fctx octx e`: all free variables and operators mentioned in `e`
  appear in the contexts
- `AllTypesSimple tvars size bctx e`: all intermediate type annotations in `e`
  are simple, have bounded depth, and use only ftvar names from `tvars`
- `termDepth bctx e ≤ size`: the expression fits within the fuel budget

**Proof strategy**: Structural induction on `(size, τ)`. For each case, first
`simp` unfolds the generator to expose the `pick`/`dite` structure as a
disjunction, then `cases hats` destructs `AllTypesSimple` to determine what
form `e` takes, then navigates to the appropriate disjunct.

### Auxiliary lemmas for completeness

| Lemma | Purpose |
|-------|---------|
| `pickBVar_complete` | If `bctx[i]? = some τ`, then `.bvar () i` is in `pickBVar`'s support |
| `pickFVar_complete` | If `(x, τ) ∈ fctx`, then the fvar is in `pickFVar`'s support |
| `pickOp_complete` | If `(o, τ) ∈ octx`, then the op is in `pickOp`'s support |
| `pickTyVar_complete` | If `name ∈ tvars`, then `.ftvar name` is in `pickTyVar`'s support |
| `genLMonoTy_support` | Full iff characterization of `genLMonoTy`'s support |
| `HasTypeA_unique` (from Strata) | Typing is deterministic — used to unify intermediate types |
| `eq_hasType_bool` | Inversion: `.eq` always has type `.bool` |
| `quant_hasType_bool` | Inversion: `.quant` always has type `.bool` |
| `Nat_arbitrary_support_set` | Every `Nat` is in `Nat.arbitrary`'s support (for int completeness) |
| `Int_cover` | Every `Int` is reachable as `↑k` or `-(↑k + 1)` |

### The `genLMonoTy_support` lemma

```lean
theorem genLMonoTy_support :
    τ ∈ support (genLMonoTy tvars n) ↔
      SimpleType τ ∧ monoTyDepth τ ≤ n ∧ allFtvarsIn tvars τ
```

This is the key bridge between the type generator and the expression
generator's completeness proof. It characterizes exactly which types
`genLMonoTy` can produce. The proof uses:

| Lemma | Purpose |
|-------|---------|
| `allFtvarsIn_bool`, `allFtvarsIn_int` | Base types trivially satisfy `allFtvarsIn` |
| `allFtvarsIn_ftvar`, `allFtvarsIn_ftvar_inv` | Bridge between `allFtvarsIn (.ftvar name)` and `name ∈ tvars` |
| `allFtvarsIn_arrow` | Decompose `allFtvarsIn` for arrow types into conjunction |

## The `AllTypesSimple` Predicate

This inductive predicate is the main "fragment characterization" for
completeness. It captures the invariant that all intermediate type annotations
in an expression (those produced by `genLMonoTy`) are:
1. Simple types (`SimpleType τ'`)
2. Of bounded depth (`monoTyDepth τ' ≤ n`)
3. Using only ftvars from `tvars` (`allFtvarsIn tvars τ'`)

Without this predicate, the completeness theorem would need to universally
quantify over all possible intermediate types, which is impossible — the
generator can only produce types from `genLMonoTy`'s support.

## Context Specification Lemmas

| Lemma | Statement |
|-------|-----------|
| `bvarsOfType_go_spec` | Characterizes `bvarsOfType.go` via offset arithmetic |
| `bvarsOfType_mem_iff` | `i ∈ bvarsOfType bctx τ ↔ bctx[i]? = some τ` |
| `fvarsOfType_mem_iff` | `x ∈ fvarsOfType fctx τ ↔ (x, τ) ∈ fctx` |
| `opsOfType_mem_iff` | `x ∈ opsOfType octx τ ↔ (x, τ) ∈ octx` |

These connect the list-filtering operations used in the generator to the
semantic membership predicates used in the typing rules.

## Design Decisions

### Why `dite` outside `pick` (Palamedes rules 5/6)

The original `genLMonoTy` had `dite` nested inside `pick`:
```
pick bool (pick int (if tvars.length > 0 then pickTyVar else bool))
```

After `simp` unfolded `pick`, Lean's kernel reduced the `dite` to
`Decidable.rec`, producing a term that `rcases` couldn't destructs.
Moving `dite` to the outermost level lets `mem_support_dite_iff` decompose
it before `pick_mem_iff` processes the inner structure.

### Why `HasTypeA_unique` instead of custom inversion lemmas

The typing relation is deterministic (provable via `typeCheck`), so
`HasTypeA_unique hwt .const` directly derives contradictions like
`.bool = .int` when a constant has the wrong type. For `eq`/`quant`
(whose constructors have complex premises that block `HasTypeA_unique`),
minimal inversion lemmas `eq_hasType_bool` and `quant_hasType_bool` are
retained — they're one-line `cases` proofs.

### Why `set_option linter.unusedSimpArgs false`

The completeness proof uses a uniform simp set
`[LConst.ty, LMonoTy.bool, LMonoTy.int, LMonoTy.arrow]` across many
impossibility cases. Different cases need different subsets, but maintaining
per-case simp sets would be fragile under refactoring. The linter suppression
accepts this trade-off.
