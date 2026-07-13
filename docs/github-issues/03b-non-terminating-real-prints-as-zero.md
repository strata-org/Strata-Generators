# Non-terminating real literal prints as `0.0` (value corruption / soundness bug)

## Summary

`Core.formatProgram` prints a real literal whose denominator is not a product of
2s and 5s (e.g. `1/3`) as `0.0`. The printed term has a **different value** from the
original — a soundness bug, not merely an unparseable output. Triggered purely by
the printer — no parse step needed.

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

## Root cause

1. `Strata/Languages/Core/DDMTransform/FormatCore.lean:272-277` — `lconstToExpr`
   for `.realConst r` calls `StrataDDM.Decimal.fromRat r`; on `none` it logs
   `"unsupported real"` and emits `.realLit default ⟨default, default⟩` — a
   **default `Decimal`** (line 277).
2. `StrataDDM/StrataDDM/Util/DecimalRat.lean:45-54` — `fromRat` returns `none`
   when the denominator has a prime factor other than 2 or 5, so `1/3` is
   unrepresentable as a terminating decimal.
3. `default : Decimal` is `{ mantissa := 0, exponent := 0 }`
   (`StrataDDM/StrataDDM/Util/Decimal.lean:16-19`), and `Decimal.toString` renders
   it as `"0.0"` (`Decimal.lean:31-35`).

So `1/3` prints as `0.0`. Unlike the syntactic round-trip bugs, this produces a
*wrong* program rather than an unparseable one — it silently changes the term's
value.

## Expected

The printed real literal must denote the same value as the AST (`1/3`), or printing
must fail loudly rather than substituting `0.0`.

## Suggested fix

Print unrepresentable rationals losslessly (e.g. as a division expression or an
exact rational literal) instead of substituting a default `Decimal`; at minimum,
raise an error rather than silently emitting `0.0`.

## Priority

High — this is a printer **correctness** defect (value corruption), more serious
than the syntactic round-trip failures which merely produce unparseable output.

## Related

See also the sibling issue "unapplied builtin operator has no concrete syntax",
another printer-side defect on function bodies (an unparseable-output bug).
