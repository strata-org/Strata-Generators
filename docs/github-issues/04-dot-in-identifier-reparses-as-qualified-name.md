# Type parameters containing `.` fail to round-trip (misparsed as qualified names)

## Summary

`.` is a legal identifier character, so a type variable named `F.pl` is a valid
identifier value and the printer emits it bare. But `.` is also the qualified-name
separator, so on re-parse `F.pl` is read as *dialect `F`, name `pl`* — an
undeclared qualified reference — and rejected.

## Root cause

- `StrataDDM/StrataDDM/Parser.lean:124-125` — `strataIsIdRest` includes `'.'`, so
  `F.pl` is a legal identifier *value*.
- `StrataDDM/StrataDDM/BuiltinDialects/Init.lean:81-89` — a type name parses as a
  `QualifiedIdent`, whose explicit form is `Ident "." Ident` (a dialect-qualified
  reference).

The variable *is* declared in the `<...>` binder, so this is the dot-driven
misparse, not a genuine scoping error.

## Reproduce (self-contained)

```lean
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda Core Strata
open StrataDDM (initDialect)

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
      IO.println s!"OK; reformatted =\n{(Core.formatProgram ast).pretty}"
  catch e =>
    IO.println s!"PARSE ERROR: {(toString e).replace "\n" " "}"

#eval roundtrip "function f<F.pl>() : F.pl;"
```

## Observed

```
PARSE ERROR: Parse errors:   1:21: Undeclared type or category F.pl.
```

## Expected

A type variable whose name contains `.` and is bound in the `<...>` list should
round-trip. Either the printer should quote such names (pipe-delimit them) so they
lex as a single identifier, or `.` should not be a legal bare-identifier character.

## Suggested fix

Two options: (a) pipe-quote identifiers containing `.` at both binding and use
sites in the printer, or (b) a spec decision to exclude `.` from
`strataIsIdRest`. This is a genuine tension between the identifier lexer
(`Parser.lean:124-125`) and qualified-name syntax (`Init.lean:81-89`).
