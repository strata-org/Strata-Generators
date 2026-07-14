# Type inference is incomplete for quantifiers (`∃x. x` fails to infer)

## Summary

The following incompleteness in Lambda's type inference (`LExpr.resolve`) was found
via property-based testing of a **completeness** property: if we take a well-typed
term, erase all of its type annotations, and run type inference on the result, then
inference should recover a (most-general) type that the original type is an instance
of.

`resolve` currently **rejects** the type-erased term `∃x. x`, erroring with

```
Quantifier body has non-Boolean type: $__ty0
```

even though `∃(x : bool). x` is well-typed and inference *should* be able to recover
the annotation by inferring the binder's type as `bool`. `∀` behaves identically.

Note that this is an *incompleteness* (a typeable term is rejected), **not** a
*soundness* bug: across the generated terms, inference never returned a *wrong* or
too-specific type — every counterexample is `resolve` erroring on a term that does
have a type. As a bonus, PBT (via Plausible) shrinks to the **minimal**
counterexample `∃x. x` (`expr_size` 2), which points straight at the root cause.

## The counterexample class

Every counterexample is an **erased quantifier whose body's inferred type is the
bound variable's (fresh) type variable** — canonically:

```
original (annotated):  ∃bool. %0      -- i.e. ∃(x : bool). x
erased:                ∃_. %0         -- i.e. ∃x. x
resolve:               ERROR: Quantifier body has non-Boolean type: $__ty0
```

The failure appears at any nesting depth and inside larger terms (the `$__ty<n>`
suffix just reflects the binder depth). Representative erased forms found by PBT:

```
∃_. %0                                  → Quantifier body has non-Boolean type: $__ty0
∀_. %0                                  → Quantifier body has non-Boolean type: $__ty0
Bool.And (∃_. %0) (#true == #true)      → Quantifier body has non-Boolean type: $__ty0
Bool.Or #false (∃_. %0)                 → Quantifier body has non-Boolean type: $__ty0
if ∀_. %0 then "P" else "chA"           → Quantifier body has non-Boolean type: $__ty0
λ_. λ_. ∃_. if #true then %0 else #false → Quantifier body has non-Boolean type: …
```

### It's the *body*, not the quantifier

The incompleteness only bites when the quantifier **body's inferred type mentions
the bound variable's fresh type variable** (and isn't otherwise forced to `bool`).
An erased quantifier whose body is independently `bool` resolves fine — a good
contrasting "passes" example:

```
∃_. #false   (i.e. ∃x. false)   → OK, inferred type bool
∀_. #true                       → OK, inferred type bool
∃_. %0       (i.e. ∃x. x)       → ERROR: Quantifier body has non-Boolean type: $__ty0
```

The only difference is whether the body's inferred type depends on the erased binder.

## Reproduce (self-contained)

To reproduce, paste the following into a new file `Repro.lean` and run
`lake env lean Repro.lean` in a repo where Strata is imported. This example
constructs the erased `LExpr`s directly and runs `LExpr.resolve` on them (no
generator needed). Expected output is in the trailing comments.

```lean
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.LExprTypeEnv

open Lambda
open Lambda.LTy.Syntax

/-- `LExpr` params used by the generators: `Unit` metadata on both slots. -/
abbrev P : LExprParams := ⟨Unit, Unit⟩
abbrev E := LExpr (LExprParams.mono P)

/-- Known types + context for `resolve` (arrow, bool, int, string, real, …). -/
def knownTypes : KnownTypes :=
  makeKnownTypes ([t[∀a b. %a → %b],
    t[bool], t[int], t[string], t[real], t[regex],
    t[∀n. bitvec n], t[∀a b. Map %a %b], t[∀a. Sequence %a]].map (·.toKnownType!))

def ctx : LContext P :=
  { LContext.default with knownTypes := knownTypes }

/-- Run `resolve` on a fully type-erased expression and report the outcome. -/
def tryResolve (name : String) (e : E) : IO Unit := do
  match LExpr.resolve ctx TEnv.default e with
  | .ok (resolved, _) =>
    IO.println s!"{name}: OK, inferred type = {Std.Format.pretty (Std.ToFormat.format resolved.toLMonoTy)}"
  | .error msg => IO.println s!"{name}: ERROR: {msg}"

-- Erased `∃x. x`: quantifier with no binder annotation, body = bound var (bvar 0).
-- (The trigger slot is unused here; `#true` is a well-typed placeholder.)
def existsXX : E := .quant () .exist "" none (.boolConst () true) (.bvar () 0)

-- Erased `∀x. x`.
def forallXX : E := .quant () .all "" none (.boolConst () true) (.bvar () 0)

-- Contrast (resolves fine): erased `∃x. false` — body is independently `bool`.
def existsXFalse : E := .quant () .exist "" none (.boolConst () true) (.boolConst () false)

#eval tryResolve "∃x. x    " existsXX      -- ERROR: Quantifier body has non-Boolean type: $__ty0
#eval tryResolve "∀x. x    " forallXX      -- ERROR: Quantifier body has non-Boolean type: $__ty0
#eval tryResolve "∃x. false" existsXFalse  -- OK, inferred type = bool
```

## Observed

```
∃x. x    : ERROR: Quantifier body has non-Boolean type: $__ty0
∀x. x    : ERROR: Quantifier body has non-Boolean type: $__ty0
∃x. false: OK, inferred type = bool
```

## Expected

The erased `∃x. x` (and `∀x. x`) should resolve, inferring the binder type as
`bool` — recovering `∃(x : bool). x`. Instead `resolve` errors.

## Root cause

In `resolveAux`, the quantifier case (Strata `Strata/DL/Lambda/LExprT.lean`, ~line 284):

```lean
let ety := et.toLMonoTy            -- the body's inferred type
...
if ety != LMonoTy.bool then do     -- SYNTACTIC disequality check
  .error f!"Quantifier body has non-Boolean type: {ety}"
else
  .ok (.quant ⟨m, xty⟩ qk name xty triggersClosed etclosed, Env)
```

Two things combine on the `∃x. x` case:

1. **No unification.** When the binder annotation is erased, `typeBoundVar` gives the
   bound variable a **fresh type variable** `?a`. For `∃x. x` the body is that
   variable, so `ety = ?a`. The rule checks `ety != bool` *syntactically* — `?a ≠ bool`
   — and errors, instead of solving the constraint `?a = bool` (which would succeed
   and pin the binder to `bool`).
2. **Pending substitution not applied.** `ety` is read from `et.toLMonoTy` directly,
   without applying the pending substitution in `Env`. So even a substitution that
   forces `?a = bool` elsewhere would not be reflected here.

### Contrast: the `ite` case does it right

The analogous "this subterm must be `bool`" obligation in the `ite` case discharges
the constraint by **unification**, not a syntactic check:

```lean
let S ← Constraints.unify [(cty, LMonoTy.bool), (tty, ety)] Env.stateSubstInfo ...
```

That asymmetry between the `quant` and `ite` cases is the bug.

## Suggested fix

Make the `quant` case mirror `ite`: replace the `ety != LMonoTy.bool` guard with a
call that **unifies `ety` and `bool`**, threading the resulting substitution back into
`Env`:

```lean
let S ← Constraints.unify [(ety, LMonoTy.bool)] Env.stateSubstInfo ...
```

This lets `resolve` accept `∃x. x` by inferring the binder type as `bool`, aligning
it with every other "must be bool" position. It will require some proof changes, but
these should be modest.

## Why it does not affect real Core programs

The Core surface grammar **requires** a type annotation on every quantifier binder
(`bind_mk := v " : " tp` in `DDMTransform/Grammar.lean`) and the body must be `bool`.
So `∃x. x` (untyped binder) is not expressible in Core source; with the annotation
present, `typeBoundVar` uses it instead of inventing `?a`, and resolution succeeds.
Confirmed end-to-end with `Core.typeCheck` on a `#strata` program:

```
procedure p() spec { ensures (exists x : bool :: x); } { };   -- Type checking succeeded
procedure p() spec { ensures (exists x : int  :: x); } { };   -- ERROR: Encountered int when bool expected
```

The bug only surfaces on **internally constructed / fully type-erased** terms —
exactly what the erase-then-resolve completeness property produces.

## How to reproduce

- **Plausible** (prints verbatim resolve errors on failure):
  the `prop_resolve_after_erase` property in `PlausibleTestMain.lean` fails and prints
  the `Quantifier body has non-Boolean type` messages alongside the (shrunk) erased
  terms.
- **Tyche** (dense counterexample panel):
  the "Counterexamples: erase types then resolve" panel in `TycheMain.lean` (see
  `tyche_output.jsonl`); features `failure_mode` (all `resolve_failed`) and
  `has_quantifier` (all `yes`).

## Notes

- This lives in the vendored dependency `Strata` (`Strata/DL/Lambda/LExprT.lean`), not
  in this repo — a fix belongs upstream, with a regression test on the erased `∃x. x`
  term.
- Severity is low (completeness only, no soundness impact).
