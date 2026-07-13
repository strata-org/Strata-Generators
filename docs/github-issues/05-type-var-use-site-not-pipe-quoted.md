# Type parameters with `|`/`\` in their names fail to round-trip (use site not pipe-quoted)

**Background:** 
In Strata, identifiers containing special characters (e.g. `|`, `\`,
`'`, or a space) can be pipe-quoted by wrapping `|...|`, 
which causes the parser to treat it as one single identifier.

**Bug:**
Consider the following function declaration (emitted by the pretty-printer), 
whose AST was generated randomly using a generator for well-typed Strata Core functions.
The following declaration is printed by the pretty-printer:

```
-- Here, `A\|L` is the name of a type parameter
function f<|A\|L|> () : A|L; 
```

Note that that for type parameter identifiers containing special characters, 
the pretty-printer pipe-quotes it when it is bound (`<|A\|L|>`) but
emits it without by at its **use** site (`: A|L`). 
The latter occurrence is unparseable and the parser fails to aprse this declaration,
violating the round-trip property that a pretty-printed function declaration should also 
parse successfully.

## Reproduce (self-contained)

To reproduce, paste the following self-contained example into a new file `Repro.lean`, and run `lake env lean Repro.lean` in a repo where Strata is imported.

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

-- Use site bare (what the printer emits): fails to parse.
#eval roundtrip "function f<|A\\|L|> () : A|L;"
-- Both sites quoted: parses (the value is legal), but the reprint bares the use
-- site again, so it does not round-trip (mismatch).
#eval roundtrip "function f<|A\\|L|> () : |A\\|L|;"
```

(The `\\` in the Lean string literals is a single backslash in the source being
parsed.)

## Observed

```
-- #1: bare use site does not parse
PARSE ERROR: Parse errors:   1:26: unterminated pipe-delimited identifier

-- #2: both sites quoted parses, but reprint bares the use site (A|L) → mismatch
OK; reformatted =
program Core;

function f<|A\|L|> () : A|L;
```

## Expected

A type variable whose name needs pipe delimiters at its binding site should be
pipe-quoted at its **use** site too, so the printed program round-trips.
