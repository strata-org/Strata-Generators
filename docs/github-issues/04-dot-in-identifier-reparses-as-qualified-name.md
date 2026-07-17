# Type parameters containing `.` fail to round-trip (misparsed as qualified names)

## Summary

The following bug was found via property-based testing when testing the property
that randomly generated well-typed Strata Core functions should round-trip (i.e. 
printing a function and parsing it again should yield the same AST).

`.` is a legal character for identifiers, and a type parameter to a function called `F.pl` is a valid
identifier and is pretty-printed as-is. However, `.` is also the separator for qualified names,
so when upon re-parsing, `F.pl` is read as *dialect `F`, name `pl`*, which is interpreted
as an undeclared qualified reference and subsequently rejected by the parser.

## Reproduce (self-contained)

To reproduce, paste the following self-contained example into a new file `Repro.lean` and run `lake env lean Repro.lean` in a 
repo where Strata is imported.
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
 
