# Generator Distribution Analysis: Using `RandomChoice.coin` to Fix Size Bias

## Problem

The `genLExpr` generator in `HasTypeAGen.lean` produces overwhelmingly trivial terms.
Empirical analysis (2000 samples at depth=3) shows:

- **54.6% of terms are trivial constants** (depth 0, size 1)
- Mean depth is 1.29 despite a budget of 3 (43% utilization)
- 87.8% of generated types have type_depth=0 (plain `bool` or `int`)
- Only 12.2% of target types are arrows (which force nontrivial structure)

This is the same class of issue described in the "Using Kiro to Synthesize a Correct
STLC Generator" document, though our generator does NOT have Kiro's "wrong size notion"
bug (our depth parameter correctly bounds term depth; arrow types never appear at depth 0).

## Root Cause

The generator uses nested binary `pick` (50/50 coin flip) to choose between alternatives.
For `bool` at depth `n+1`:

```
pick
  (bool constant)          -- 50% chance → DONE, trivial
  (pick
    (ite ...)              -- 25% chance → recurses
    (pick
      (eq ...)             -- 12.5%
      (pick
        (app ...)          -- 6.25%
        (pick ...))))      -- 6.25%
```

At every recursive level, there's a 50% chance of immediately returning a base-case
constant, regardless of remaining depth budget. The type generator (`genLMonoTy`) has
the same structure, causing simple types (bool/int) to dominate, which in turn means
most expression generators never need to produce anything complex.

## Proposed Fix: Replace `pick` with `coin` at Key Sites

Basalt provides `RandomChoice.coin (r : Rat) : m Bool`, which is a weighted binary
choice (returns `true` with probability `r`). The idea is to replace the top-level
`pick` in recursive cases with `coin (1/4)` or similar, reducing the probability of
taking the trivial base-case branch when depth > 0:

```lean
-- Current (50% trivial at every level):
| n + 1, .bool =>
  pick
    (fun () => pick (fun () => pure (.boolConst () true))
                    (fun () => pure (.boolConst () false)))
    (fun () => pick (fun () => ...) ...)

-- Proposed (25% trivial when depth remains):
| n + 1, .bool => do
  let trivial ← coin (1/4)
  if trivial then
    pick (fun () => pure (.boolConst () true))
         (fun () => pure (.boolConst () false))
  else
    pick (fun () => ...) (pick (fun () => ...) ...)
```

## Impact on Proofs

### Soundness: Minimal changes
Soundness only requires that each reachable branch produces a well-typed term.
Since `coin` has the same support as `pick` (both branches are reachable for any
`0 < r < 1`), the proof structure is unchanged. At each site where `pick_mem_iff`
is used, substitute `coin_mem_iff`.

### Completeness: Minimal changes
Completeness requires that every well-typed term is reachable via *some* branch.
Again, since both branches of `coin r` are in the support (for valid `r`), the
existing "`right; left; ...`" proof navigation still works.

### What's needed

1. **One new lemma** (`coin_mem_iff` for `SetGen.Set`):
   ```lean
   theorem coin_mem_iff {r : Rat} (hr_pos : 0 < r.num) (hr_lt : r.num < r.den) :
       a ∈ (coin r >>= f : Set α) ↔ a ∈ f true ∨ a ∈ f false
   ```
   This follows directly from the existing `mem_choose` lemma since `coin` is
   defined in terms of `choose`.

2. **Mechanical substitution** at proof sites: replace `pick_mem_iff` with
   `coin_mem_iff` wherever `pick` was changed to `coin`. The disjunctive
   structure (`∨`) is identical, so downstream `left`/`right` tactics don't change.

3. **No structural refactoring** of proofs — the proof skeleton (unfold generator,
   show each branch is sound/reachable) remains the same.

## Alternative Approach: Force Depth Usage

A more aggressive fix would restructure the generator so depth `n+1` *always*
takes a recursive step (no base cases allowed except at depth 0):

```lean
genLExpr ... 0 .bool := pick (pure true) (pure false)
genLExpr ... (n+1) .bool :=
  pick (ite ...) (pick (eq ...) (pick (app ...) ...))  -- no constants here
```

This guarantees full depth utilization but changes the semantics: it becomes
"generate at exactly depth n" rather than "at most depth n". The completeness
statement changes, and a wrapper selecting a random depth would be needed.
This approach requires more substantial proof refactoring.

## Recommendation

Start with the `coin` approach. It's a minimal change (swap `pick` for `coin` at
the first branch point of each recursive case), preserves the proof structure, and
directly addresses the 50% trivial-at-every-level compounding problem. A weight of
`1/4` for the trivial branch would shift the expected distribution substantially:

- P(trivial) drops from 50% → 25% at each level
- Expected depth utilization increases from ~43% → ~70%+
- The generator remains sound and complete with the same proof skeleton
