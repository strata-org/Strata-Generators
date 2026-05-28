# Finishing the `ftvar` Completeness Proof in `HasTypeAGen.lean`

## Current State (2026-05-28)

The `HasTypeA` generator now supports rigid type variables (`LMonoTy.ftvar name`)
via a `tvars : List TyIdentifier` palette parameter. **Soundness is fully proved.**
Completeness has sorrys in two places:

1. `genLMonoTy_support` (line 645) — the iff characterization of the type generator
2. `genLExpr_complete` — the `ftvar` cases (lines 1337-1338) plus `allFtvarsIn`
   obligations in existing `app`/`eq`/`quant` cases (lines 1135-1298)

All completeness sorrys ultimately depend on `genLMonoTy_support`.

## The `dite`-inside-`pick` Simp Issue

### The Problem

`genLMonoTy` uses a `dite` (decidable if-then-else) inside a `pick` branch:

```lean
pick (fun () => pure .bool)
     (fun () =>
       pick (fun () => pure .int)
            (fun () =>
              if h : tvars.length > 0 then pickTyVar tvars h
              else pure .bool))
```

After `simp only [genLMonoTy, mem_support_pick_iff, mem_support_pure_iff]`,
the outer `pick` is decomposed into a disjunction, but the inner `dite` remains
as a `Decidable.rec` term that `rcases` cannot destructure:

```
h✝ : Decidable.rec (fun h => (fun h => pure LMonoTy.bool) h)
  (fun h => (fun h => pickTyVar tvars h) h) (Nat.decLt 0 tvars.length) τ
```

Adding `SetGen.mem_dite` or `mem_support_dite_iff` to the simp set does NOT help
because after `mem_support_pick_iff` unfolds `pick`, the membership goal is about
the *raw* `dite` term, not about `support (dite ...)`. The `SetGen.mem_dite` lemma
is about `a ∈ (dite p t e : Set α)` which matches, but the `Decidable.rec` form
doesn't syntactically match the `dite` pattern after Lean's reduction.

### Root Cause

The issue is that Lean's kernel reduces `dite p t e` (where `p := tvars.length > 0`
and `[Decidable p]` is `Nat.decLt 0 tvars.length`) into `Decidable.rec ...` before
`simp` can apply `mem_dite`. The `@[simp]` lemma `SetGen.mem_dite` expects the
unreduced `dite` form.

### Proposed Fixes (pick one)

#### Option A: Restructure `genLMonoTy` to avoid `dite` inside `pick`

Move the `dite` to the outermost level:

```lean
def genLMonoTy [Gen G] (tvars : List TyIdentifier) : Nat → G LMonoTy
  | 0 =>
    if h : tvars.length > 0 then
      pick (fun () => pure .bool)
           (fun () => pick (fun () => pure .int)
                           (fun () => pickTyVar tvars h))
    else
      pick (fun () => pure .bool)
           (fun () => pure .int)
  | n + 1 => ...
```

**Pros:** The outermost `dite` is decomposed first (via `split` or `simp [genLMonoTy]`
which produces two subgoals), and then `mem_support_pick_iff` works cleanly within
each branch.

**Cons:** Code duplication in the generator; more equation lemmas; the proof needs
`split` before `simp`.

#### Option B: Write manual unfolding lemmas

```lean
theorem genLMonoTy_zero_eq (tvars : List TyIdentifier) :
    genLMonoTy (G := SetGen.Set) tvars 0 =
      if h : tvars.length > 0 then
        {.bool, .int} ∪ SetGen.support (pickTyVar tvars h)
      else {.bool, .int} := by ...

theorem genLMonoTy_succ_eq (tvars : List TyIdentifier) (n : Nat) :
    support (genLMonoTy (G := SetGen.Set) tvars (n+1)) = ... := by ...
```

Then `genLMonoTy_support` rewrites via these lemmas instead of `simp [genLMonoTy]`.

**Pros:** No generator restructuring needed.
**Cons:** Manual characterization lemmas duplicate the logic.

#### Option C: Use `simp` with `dite_eq_ite` + `ite` reduction

Try `simp only [..., dite_eq_ite, ite_mem_iff]` or `split` after the initial simp
to case-split on `tvars.length > 0` within the proof, producing two subgoals where
the `dite` is resolved.

**Recommendation:** Option A is cleanest. The `dite` at the top level is the
natural structure — the generator's behavior is genuinely different when `tvars`
is empty vs non-empty, and making that explicit at the definition level simplifies
all downstream proofs.

## The `allFtvarsIn` Obligations in `genLExpr_complete`

### What They Are

In the existing `app`/`eq`/`quant` cases of `genLExpr_complete`, intermediate types
`τ'` are shown to be in the support of `genLMonoTy tvars n` via:

```lean
(genLMonoTy_support tvars n τ').mpr ⟨hsτ', hdτ', sorry⟩
```

The third conjunct `sorry` needs to prove `allFtvarsIn tvars τ'`. This requires
a hypothesis that all ftvar names in intermediate types used by the expression
belong to `tvars`.

### How to Discharge Them

The `AllTypesSimple` inductive (line ~793) characterizes expressions in the
generator's fragment. It currently constrains intermediate types with
`SimpleType τ' ∧ monoTyDepth τ' ≤ n`. For completeness with `ftvar`, extend it:

```lean
inductive AllTypesSimple (tvars : List TyIdentifier) : Nat → BVarCtx → LExpr' → Prop where
  | app : SimpleType τ' → monoTyDepth τ' ≤ n → allFtvarsIn tvars τ' →
          AllTypesSimple tvars n bctx fn →
          AllTypesSimple tvars n bctx arg →
          AllTypesSimple tvars (n + 1) bctx (.app () fn arg)
  ...
```

Then the `allFtvarsIn tvars τ'` obligation comes directly from the `AllTypesSimple`
hypothesis in the completeness theorem.

**Alternatively**, add `allFtvarsIn tvars τ'` as a standalone hypothesis to
`genLExpr_complete` and propagate it. But threading it through `AllTypesSimple`
is more natural since that inductive already captures "what the generator can
produce."

## The `ftvar` Cases in `genLExpr_complete`

### `| 0, _, SimpleType.ftvar =>`

Need to show that a well-typed `HasTypeA' bctx e (.ftvar name)` expression `e`
(satisfying `AllTypesSimple`, `emptyNames`, `allVarsInCtx`, depth ≤ 0) is in the
support of `genLExpr ... 0 (.ftvar name)`.

At size 0, the only possible expressions are:
- `bvar i` where `bctx[i]? = some (.ftvar name)`
- `fvar x (some (.ftvar name))` where `(x, .ftvar name) ∈ fctx`
- `op o (some (.ftvar name))` where `(o, .ftvar name) ∈ octx`

The proof pattern is identical to the existing `| 0, _, SimpleType.bool =>` case:
case-split on `hats` (which tells you what form `e` takes), then show the
expression lands in the appropriate `pickBVar`/`pickFVar`/`pickOp` branch.

Key subtlety: the generator has nested `dite` fallbacks. To show membership, you
need to exhibit which `dite` branch fires. For `bvar`:
- If `bvars.length > 0` (which it is, since `i ∈ bvarsOfType ...`), the first
  branch fires and `pickBVar_complete` finishes it.

### `| n + 1, _, SimpleType.ftvar =>`

Same as the `n + 1` cases for `bool`/`int` but without literal fallbacks. The
structure is:
- `app`: show fn and arg are in the support of recursive calls
- `ite`: show c, t, e are in the support
- `bvar`/`fvar`/`op`: same as size-0

## Connection to Palamedes Optimization Rules

The `dite`-inside-`pick` issue is a specific instance of a general pattern identified
in the Palamedes paper (Goldstein et al., PLDI 2026, "The Search for Constrained
Random Generators"). Their optimization rules in Figure 11 directly address this:

### Applicable Rules

**Rules (5) and (6): Lifting assumes out of picks**

```
pick (assume b in x) y  ~~>  if b then pick x y else y     (5)
pick x (assume b in y)  ~~>  if b then pick x y else x     (6)
```

Our `dite` inside `pick` is exactly this pattern. The `if h : tvars.length > 0`
guard acts as an `assume` — when false, that branch produces nothing useful
(falls back to a duplicate of another branch). Applying rules (5)/(6) moves the
guard outside, which is precisely our "Option A" restructuring.

**Rules (3) and (4): Lifting assumes out of binds**

```
(assume b in x) >>= f   ~~>  assume b in (x >>= f)        (3)
x >>= (λ a => assume b in (f a))  ~~>  assume b in (x >>= f)   (4, if a ∉ fv(b))
```

These apply to the `app` branch in `genLExpr`:

```lean
do
  let τ' ← genLMonoTy tvars n      -- may produce ftvar with no witness
  let arg ← genLExpr ... n τ'      -- hits `default` (= ∅) if ftvar unwatchable
  let fn  ← genLExpr ... n (.arrow τ' goal)
  pure (.app () fn arg)
```

When `genLMonoTy` picks an ftvar that has no witness in context, `genLExpr ... τ'`
is effectively `assume False in ...` — it produces `∅` and poisons the whole bind
chain. In Palamedes terms, there's an implicit `assume (witnessable τ')` buried
inside the bind. Rule (4) would lift it out, and then rule (5)/(6) would remove it
from the pick entirely (since an always-false assume makes the branch dead).

In practice, this means: if we restructure so that `genLMonoTy` only produces
ftvar names that ARE witnessable (i.e., the palette is pre-filtered to only
include names with witnesses in `bctx`/`fctx`/`octx`), the implicit assume is
always true and can be eliminated. This is a **runtime efficiency** optimization
(avoids wasted generation attempts) and also simplifies the completeness proof
(no need to reason about the empty-support case).

**Rules (1) and (2): Monad laws**

Not directly applicable — we don't have `pure v >>= f` patterns.

### Non-Applicable Machinery

The recursion scheme machinery (Section 4 — folds, unfolds, `List.unfold`,
`List.accu`) does not apply. Our generators use fuel-bounded recursion on a depth
parameter, not structural recursion over an inductive datatype in the predicate.
Our `genLExpr` is already in the direct "unfolded" style that Palamedes would
synthesize FROM a fold-based predicate.

### Recommended Refactoring Strategy

Apply rules (5)/(6) uniformly across both `genLMonoTy` and `genLExpr`:

1. **`genLMonoTy`**: Move `if h : tvars.length > 0` to the outermost level of each
   depth case. Two equation lemmas per case (tvars empty vs non-empty), each with
   clean `pick` trees containing no `dite`.

2. **`genLExpr` ftvar case**: Move all `dite` guards (`bvars.length > 0`,
   `fvarsOfType ...`, `opsOfType ...`) to the top of each `pick` tree. Structure:

   ```lean
   | 0, .ftvar name =>
     if hv : (bvarsOfType bctx (.ftvar name)).length > 0 then
       pick (fun () => pickBVar bctx _ hv)
            (fun () => if hf : ... then pickFVar ... else pickBVar ...)
     else if hf : (fvarsOfType fctx (.ftvar name)).length > 0 then
       pick (fun () => pickFVar fctx _ hf)
            (fun () => if ho : ... then pickOp ... else pickFVar ...)
     else if ho : (opsOfType octx (.ftvar name)).length > 0 then
       pickOp octx _ ho
     else
       default   -- truly unreachable: support is ∅
   ```

   This eliminates nested `dite` entirely. Each branch of `pick` is unconditionally
   productive. The `default` only appears at the very bottom as a totality witness.

3. **Effect on proofs**: After restructuring, `simp [genLExpr]` produces subgoals
   already split on the `dite` conditions. Within each subgoal, `pick_mem_iff`
   decomposes cleanly into disjunctions over productive branches. No
   `Decidable.rec` terms appear.

### Impact on Support

Palamedes's Lemma 3.3 guarantees that rules (1)-(6) preserve support. The
restructured generators produce exactly the same set of values — the refactoring
is purely about proof tractability and runtime efficiency (avoiding dead branches),
not about changing what can be generated.

## File Locations

- Generator: `StrataGenerators/HasTypeAGen.lean`
- `genLMonoTy_support`: line 642
- `genLExpr_complete`: line 975
- `AllTypesSimple`: line ~793
- `SetGen.mem_dite`: `StrataGenerators/SetGen/Core.lean:57`
- `mem_support_dite_iff`: `StrataGenerators/SetGen/Support.lean:62`

## Build Command

```bash
lake build StrataGenerators.HasTypeAGen
```

Currently builds successfully with 2 `sorry` warnings (line 645, line 975).
