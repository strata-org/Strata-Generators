# A counterexample to completeness of type inference (`LExpr.resolve`)

## The property under test

> **Completeness of type inference:** if we erase all type annotations on a
> well-typed term, can type inference recover a most-general type (one the
> original type is a substitution instance of)?

We test this with the `genLExpr`-based generator: generate a well-typed term `e`
of type `τ`, fully erase its type annotations (`eraseAllTypes`), run
`LExpr.resolve` on the result, and check that resolution succeeds with an
inferred type that `τ` is an instance of (`isInstanceOf τ inferred`).

- Plausible property: `prop_resolve_after_erase` in `PlausibleTestMain.lean`.
- Tyche panel: "Counterexamples: erase types then resolve" in `TycheMain.lean`.

## Verdict: it is *incomplete*, but *sound*

Across ~21k generated closed terms:

- **fail (resolve errored):** present (~0.3–0.5% of generated terms)
- **fail (resolve succeeded but inferred a wrong / too-specific type): 0**
- **quantifier-free failures: 0**

So inference never returns a *wrong* type — every counterexample is `resolve`
**erroring out on a typeable term**. That is an *incompleteness* (rejects a
well-typed term), not a *soundness* bug (would be: accepts an ill-typed term or
infers a wrong type).

## The counterexample class

Every counterexample is an **erased quantifier whose body's inferred type is the
bound variable's (fresh) type variable** — canonically:

```
original (annotated):  ∃bool. %0        : bool      -- i.e. ∃x:bool. x
erased:                ∃_. %0
resolve:               ERROR: Quantifier body has non-Boolean type: $__ty0
```

`∀` behaves identically (`∀_. %0` → same error). The failure shows up at any
nesting depth and inside larger terms; the `$__ty<n>` suffix in the message just
reflects the quantifier's binder depth. Representative erased forms seen:

```
∃_. %0                                  → Quantifier body has non-Boolean type: $__ty0
∀_. ∀_. %0                              → Quantifier body has non-Boolean type: $__ty1
λ_. ∀_. %0                              → Quantifier body has non-Boolean type: $__ty1
Bool.And (∃_. %0) #false                → Quantifier body has non-Boolean type: $__ty0
if ∀_. %0 then "" else "5BB"            → Quantifier body has non-Boolean type: $__ty0
```

### Sharper characterization: it's the *body*, not the quantifier

The incompleteness only bites when the quantifier **body's type mentions the
bound variable's fresh type variable** (and isn't otherwise forced to `bool`).
An erased quantifier whose body is independently `bool` resolves fine:

```
∃_. #false   (i.e. ∃x. false)   → OK, inferred type bool
∀_. #true                       → OK, inferred type bool
∃_. %0       (i.e. ∃x. x)       → ERROR: Quantifier body has non-Boolean type: $__ty0
```

So `∃x. false` is a good *contrasting* "passes" example to place next to the
`∃x. x` counterexample: the only difference is whether the body's inferred type
depends on the erased binder.

## Root cause

In `resolveAux`, the quantifier case (Strata `Strata/DL/Lambda/LExprT.lean:284`):

```lean
let ety := et.toLMonoTy            -- the body's inferred type
...
if ety != LMonoTy.bool then do     -- SYNTACTIC disequality check
  .error f!"Quantifier body has non-Boolean type: {ety}"
else
  .ok (.quant ⟨m, xty⟩ qk name xty triggersClosed etclosed, Env)
```

Two things combine on the `∃x. x` case:

1. **No unification.** When the binder annotation is erased, `typeBoundVar`
   (`LExprT.lean:143`) gives the bound variable a **fresh type variable** `?a`.
   For `∃x. x` the body is that variable, so `ety = ?a`. The rule checks
   `ety != bool` *syntactically* — `?a ≠ bool` — and errors, instead of solving
   the constraint `?a = bool` (which would succeed and pin the binder to `bool`).
2. **Pending substitution not applied.** Line 276 reads `et.toLMonoTy` directly,
   without applying `Env.stateSubstInfo.subst` (contrast the `abs` case at
   `LExprT.lean:252`, which does). So even a substitution forcing `?a = bool`
   elsewhere would not be reflected in `ety` here.

### Contrast: the `ite` case does it right

The analogous "this subterm must be `bool`" obligation in the `ite` case
(`LExprT.lean:306`) is discharged by **unification**, not a syntactic check:

```lean
let S ← Constraints.unify [(cty, LMonoTy.bool), (tty, ety)] Env.stateSubstInfo ...
```

That asymmetry between the `quant` and `ite` cases is the bug.

## Why it does not affect real Core programs

The Core surface grammar **requires** a type annotation on every quantifier
binder (`bind_mk := v " : " tp` in `DDMTransform/Grammar.lean`) and the body
must be `bool`. So `∃x. x` (untyped binder) is not expressible in Core source.
With the annotation present, `typeBoundVar` uses it instead of inventing `?a`,
and resolution succeeds. Confirmed end-to-end with `Core.typeCheck` on a
`#strata` program:

```
procedure p() spec { ensures (exists x : bool :: x); } { };   -- Type checking succeeded
procedure p() spec { ensures (exists x : int  :: x); } { };   -- ERROR: Encountered int when bool expected
```

The bug only surfaces on **internally constructed / fully type-erased** terms —
exactly what the erase-then-resolve property produces.

## Suggested fix (upstream)

Make the `quant` case mirror `ite`: replace the `ety != bool` guard with
`Constraints.unify [(ety, LMonoTy.bool)] Env.stateSubstInfo`, threading the
resulting substitution back into `Env`. This lets `resolve` accept `∃x. x` by
inferring the binder type as `bool`, aligning it with every other "must be bool"
position.

Caveats:
- This lives in the vendored dependency `Strata` (pinned at `ngernest/Strata`
  rev `43d90cf40`), not in this repo — a fix belongs upstream, with a regression
  test on the erased `∃x. x` term.
- Severity is low (completeness only, no soundness impact), so the alternative
  is to keep treating `resolve`-failure as a vacuous pass (as the Tyche panel's
  scoring originally did, and as `prop_resolve_after_erase` could be relaxed to).

## How to reproduce

- **Plausible** (prints verbatim resolve errors on failure):
  `lake build test-lexpr && .lake/build/bin/test-lexpr 1000 60`
  → the "erasing type annotations … recovers the same type" property fails and
  prints the `Quantifier body has non-Boolean type` messages with the erased
  terms, plus a tally of distinct messages.
- **Tyche** (dense counterexample panel):
  `lake build tyche-viz && .lake/build/bin/tyche-viz 1000 tyche_output.jsonl`
  → open the "Counterexamples: erase types then resolve" panel; features
  `failure_mode` (all `resolve_failed`) and `has_quantifier` (all `yes`).
