# Unapplied builtin operator has no concrete syntax (prints untypeable `re.none()`)

## Summary

An unapplied builtin operator such as `Bool.Not` is a well-typed `LExpr.op` of type
`bool -> bool`, but `Core.formatProgram` emits `re.none()` (a `regex`) for it, which
then fails to re-typecheck. Triggered purely by the printer — no parse step needed.

## Reproduce (self-contained)

Paste into `Repro.lean` and run `lake env lean Repro.lean`. Uses only Strata
functions. Expected output is in the trailing comments.

```lean
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda Core Strata
open StrataDDM (initDialect)

/-- Wrap an expression as the body of `function f () : bool { … }` and print it. -/
def showBody (e : Core.Expression.Expr) : IO Unit := do
  let prog : Core.Program :=
    { decls := [ .func { name := ⟨"f", ()⟩, inputs := [], output := .bool, body := some e } .empty ] }
  IO.println (Core.formatProgram prog).pretty

/-- Parse a Core source string, then re-format it via Strata's own printer. -/
def roundtrip (src : String) : IO Unit := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  let ictx := StrataDDM.Parser.stringInputContext ⟨"repro"⟩ src
  try
    let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" ictx
    let (ast, errs) := TransM.run Inhabited.default (Strata.translateProgram sp)
    if !errs.isEmpty then
      IO.println s!"TRANSLATE ERROR: {(toString errs).replace "\n" " "}"
    else
      IO.println s!"OK; reformatted = {(Core.formatProgram ast).pretty.replace "\n" " "}"
  catch e =>
    IO.println s!"PARSE ERROR: {(toString e).replace "\n" " "}"

-- (1) The printer side: unapplied Bool.Not emits the untypeable fallback re.none().
#eval showBody (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool)))
--  program Core;
--  function f () : bool {
--    re.none()
--  }
--  -- Errors encountered during conversion:
--  -- Unsupported construct in lopToExpr: 0-ary op not found: Bool.Not

-- (2) There is no source syntax to print TO: the "natural" name-form is unparseable.
#eval roundtrip "function f () : bool -> bool { Bool.Not }"
--  PARSE ERROR: Parse errors: 1:31: Unknown expr identifier Bool.Not

-- (3) Contrast (NOT a bug): the APPLIED operator round-trips fine via notation.
#eval showBody (.app () (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool))) (.boolConst () true))
--  program Core;
--  function f () : bool {
--    !true
--  }
#eval roundtrip "function f () : bool { !true }"
--  OK; reformatted = program Core;  function f () : bool {   !true }
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
all** — the "natural" printout `function f () : bool -> bool { Bool.Not }` does not
parse (`Unknown expr identifier Bool.Not`, step (2) above), and neither does
`Bool.Not true` nor `Bool.Not(true)`. The only surface form is the notation `!b`
from `Grammar.lean:87` (`fn not (b : bool) : bool => "!" b`), which is mandatorily
saturated. So this is not "printer chose notation over a name it could have used";
there is no name-form to choose. The single defect is that the printer (and
grammar) have **no representation for the bare, unapplied operator** — the printer
is handed an AST it genuinely cannot render into any parseable Core program.

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
