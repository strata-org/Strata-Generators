# Function type parameters of the form `<s...` collide with the `<s` (signed-less-than) operator

## Summary

When a type parameter to a function begins with `s`, e.g. in 

```
function f<s> (...) : int { ... }
```

the parser fails to parse this function, as `<s` is the concrete syntax 
for the signed less-than operator over bit-vectors.

Notably, if we add a space before the type parameter `s`, e.g. in 

```
function f< s> (...) : int { ... }
```

the function parses successfully.

This issue was identified via property-based testing (generating 1000 random 
well-typed Strata Core functions), and I believe this issue affects any function type parameters whose name begins with `s`.


## Reproduce (self-contained)

To reproduce this issue, create a new file `Repro.lean` containing the following, and run `lake env lean Repro.lean` in any Lean environment 
where Strata is imported.

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

-- What the printer emits for a type arg named `s`: fails to parse.
#eval roundtrip "function f<s> () : int;"
-- Adding a space allows the function to parse
#eval roundtrip "function f< s> () : int;"
```

## Observed

```
-- #1: printer output does not parse
PARSE ERROR: Parse errors:   1:10: unexpected token '<s'; expected Core.Bindings

-- #2: with a space it parses, and reprints as f<s>
OK; reformatted =
program Core;

function f<s> () : int;
```

## Expected

The function declaration `function f<s> () : int;` should be parse-able.
