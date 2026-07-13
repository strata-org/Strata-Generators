# Type-variable use site is not pipe-quoted (binding site is)

## Summary

The printer pipe-quotes an identifier at its **binding** site (`<|A\|L|>`) but
emits it **bare** at its **use** site (`: A|L`). When the name contains `|` or `\`
(both legal identifier *values*), the bare use position is unparseable, so the
reprint fails (or, when both sites are quoted in the source, the reprint differs
from the input — a mismatch).

## Root cause

The use-site renderer does not pipe-quote:

- `Strata/Languages/Core/DDMTransform/FormatCore.lean:209` —
  `lmonoTyToCoreType`'s `.ftvar name => .tvar default name` passes the raw name
  value through, with no `needsPipeDelimiters` check.

The binding site *does* quote, so the asymmetry is what breaks round-tripping.

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

## Suggested fix

In the `.ftvar` rendering path (`FormatCore.lean:209`), apply the same
`needsPipeDelimiters` check used at the binding site. One fix here also covers the
leading-digit and dot-name use-site variants.
