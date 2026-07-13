# Unapplied builtin operator has no concrete syntax (prints untypeable `re.none()`)

## Summary

An unapplied builtin operator such as `Bool.Not` is a well-typed `LExpr.op` of type
`bool -> bool`, but `Core.formatProgram` emits `re.none()` (a `regex`) for it, which
then fails to re-typecheck. Triggered purely by the printer — no parse step needed.

## Reproduce (self-contained)

Paste into `Repro.lean` and run `lake env lean Repro.lean`. Uses only Strata
functions.

```lean
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate

open Lambda Core Strata

/-- Wrap an expression as the body of `function f () : bool { … }` and print it. -/
def showBody (e : Core.Expression.Expr) : IO Unit := do
  let prog : Core.Program :=
    { decls := [ .func { name := ⟨"f", ()⟩, inputs := [], output := .bool, body := some e } .empty ] }
  IO.println (Core.formatProgram prog).pretty

-- Unapplied builtin operator `Bool.Not`
#eval showBody (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool)))
-- Contrast (NOT a bug): the *applied* operator round-trips via notation
#eval showBody (.app () (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool))) (.boolConst () true))
```

## Observed

```
-- unapplied Bool.Not  →  emits the untypeable fallback re.none()
program Core;

function f () : bool {
  re.none()
}
-- Errors encountered during conversion:
-- Unsupported construct in lopToExpr: 0-ary op not found: Bool.Not

-- contrast: applied Bool.Not  →  !true  (correct; re-parses to the same AST)
program Core;

function f () : bool {
  !true
}
```

## Root cause

1. The printer renders a bare `.op` node via `lopToExpr name []` (empty args) —
   `Strata/Languages/Core/DDMTransform/FormatCore.lean:576`.
2. `lopToExpr` dispatches on `args.length` (`FormatCore.lean:529-534`); with
   `args = []`, `Bool.Not` routes to `handleZeroaryOps` — even though it *is*
   handled when applied (`handleUnaryOps`, `FormatCore.lean:322`).
3. `handleZeroaryOps` (`FormatCore.lean:290-299`) knows only three regex constants;
   `Bool.Not` hits the `_` branch, logs `"0-ary op not found"`, and emits
   `re.none()`.

**This is one issue, not two.** The *applied* operator round-trips fine via
notation (`!true` above). The operator simply has **no name-form concrete syntax at
all** — neither `Bool.Not true` nor `Bool.Not(true)` parses; the only surface form
is the notation `!b` from `Grammar.lean:87` (`fn not (b : bool) : bool => "!" b`),
which is mandatorily saturated. So this is not "printer chose notation over a name
it could have used"; there is no name-form. The single defect is that the printer
(and grammar) have **no representation for the bare, unapplied operator**.

## Expected

Either an unapplied builtin operator should print to *some* parseable, correctly
typed form, or it should be rejected at the source (never produced) rather than
silently mis-printed.

## Suggested fix

Eta-expand unapplied operators on print (`Bool.Not` → `fun x => !x`), or handle it
upstream (don't produce bare operators at function-value positions). This is
arguably a surface-syntax feature request rather than a print bug — filing for
tracking.

## Related

See also the sibling issue "non-terminating real literal prints as `0.0`", another
printer-side defect on function bodies (a value-corruption soundness bug).
