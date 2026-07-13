# Non-terminating real literal prints as `0.0` (value corruption / soundness bug)

## Summary

In Strata Core, the `real` type is represented using Lean `rat`s (rational numbers), 
but printed as decimals using `Decimal.FromRat`.
For rational numbers whose decimal representation is nonterminating (e.g. `1/3` is `0.333...`), `Decimal.fromRat` returns `None,` and the pretty-printer prints `0.0` instead (the default decimal value), 
so `1/3` is rendered as the string `"0.0"` instead, a different value.

This bug was found via property-based testing using a generator for random well-typed Strata Core functions.

## Reproduce (self-contained)

To reproduce, paste the following into a new file `Repro.lean` and run `lake env lean Repro.lean`. 
The following example uses only Strata functions.

```lean
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate

open Lambda Core Strata

/-- Wrap an expression as the body of `function f () : bool { … }` and print it. -/
def showBody (e : Core.Expression.Expr) : IO Unit := do
  let prog : Core.Program :=
    { decls := [ .func { name := ⟨"f", ()⟩, inputs := [], output := .bool, body := some e } .empty ] }
  IO.println (Core.formatProgram prog).pretty

-- Non-terminating-decimal real literal 1/3
#eval showBody (.realConst () (1/3 : Rat))
```

## Observed

```
-- realConst 1/3  →  0.0  (WRONG VALUE)
program Core;

function f () : bool {
  0.0
}
-- Errors encountered during conversion:
-- Unsupported construct in lconstToExpr: unsupported real: 1/3
```
