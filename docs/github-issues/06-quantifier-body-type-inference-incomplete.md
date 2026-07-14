# Type inference is incomplete for LExprs

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


Every counterexample is an erased quantifier whose body's inferred type is the
bound variable's (fresh) type variable, specifically:

```
original (annotated):  ∃bool. %0      -- i.e. ∃(x : bool). x
erased:                ∃_. %0         -- i.e. ∃x. x
resolve:               ERROR: Quantifier body has non-Boolean type: $__ty0
```

The failure appears at any nesting depth and inside larger terms (the `$__ty<n>`
suffix just reflects the binder depth). Here are some other representative countrexamples found by PBT:

```
∃_. %0                                  → Quantifier body has non-Boolean type: $__ty0
∀_. %0                                  → Quantifier body has non-Boolean type: $__ty0
Bool.And (∃_. %0) (#true == #true)      → Quantifier body has non-Boolean type: $__ty0
Bool.Or #false (∃_. %0)                 → Quantifier body has non-Boolean type: $__ty0
if ∀_. %0 then "P" else "chA"           → Quantifier body has non-Boolean type: $__ty0
λ_. λ_. ∃_. if #true then %0 else #false → Quantifier body has non-Boolean type: …
```

## Reproduce (self-contained)

To reproduce, paste the following self-contained example into a new file `Repro.lean` and run
`lake env lean Repro.lean` in a repo where Strata is imported. 

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
`bool` — recovering `∃(x : bool). x`. Instead, `LExpr.resolve` errors.
