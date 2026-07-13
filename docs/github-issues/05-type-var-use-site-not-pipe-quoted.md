# Type parameters with `|`/`\` in their names fail to round-trip (use site not pipe-quoted)

## Summary

The printer pipe-quotes an identifier at its **binding** site (`<|A\|L|>`) but
emits it **bare** at its **use** site (`: A|L`). When the name contains `|` or `\`
(both legal identifier *values*), the bare use position is unparseable, so the
reprint fails (or, when both sites are quoted in the source, the reprint differs
from the input — a mismatch).

## Background: why pipe-quoting exists and how Strata does it

An identifier that is a "simple symbol" (starts with a letter/`_`/`$`, and contains
only alphanumerics plus a fixed set of extras) can be written bare. Anything else —
a name that starts with a digit, or contains a special character such as `|`, `\`,
`'`, or a space — must be **pipe-delimited** (the SMT-LIB 2.6 quoted-symbol form
`|…|`) so the lexer reads it as a single identifier token rather than mis-tokenizing
it. `|` and `\` inside the name are themselves escaped (`\|`, `\\`).

Strata already implements this in the DDM formatter,
`StrataDDM/StrataDDM/Format.lean`:

- `needsPipeDelimiters (s : String) : Bool` (`Format.lean:43-48`) — true when `s`
  is empty, starts with a non-`isIdBegin` char, or contains any non-`isIdContinue`
  char.
- `escapePipeIdent` (`Format.lean:54-58`) — escapes `\`→`\\` and `|`→`\|`.
- `formatIdent` / `quoteIdent` (`Format.lean:65-73`) — wrap in `|…|` **iff**
  `needsPipeDelimiters` holds; otherwise emit the name bare.

Crucially, this quoting fires automatically only when a name flows through an
`Ident`-typed grammar slot (the DDM formatter calls `formatIdent` on `Ident`
atoms). The **binding** site of a type parameter is such a slot —
`op type_var (name : Ident) : TypeVar => name;`
(`Strata/Languages/Core/DDMTransform/Grammar.lean:58`) — so `f<|A\|L|>` comes out
correctly quoted. The **use** site does not go through an `Ident` slot: the raw
name string is placed directly into a type node, bypassing `quoteIdent`.

## Root cause

The use-site renderer builds the type node from the raw name, with no
`needsPipeDelimiters` / `quoteIdent` step:

- `Strata/Languages/Core/DDMTransform/FormatCore.lean:209` —
  `lmonoTyToCoreType`'s `.ftvar name => .tvar default name` passes the raw `name`
  value straight through.

So the same type variable is quoted at its binding site (via the `Ident` slot and
`formatIdent`) but emitted bare at its use site (via `.tvar` on the raw string).
That asymmetry is what breaks round-tripping.

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

Route the use-site name through the same quoting the binding site already uses. In
the `.ftvar` rendering path (`FormatCore.lean:209`), apply `quoteIdent` (or the
`needsPipeDelimiters`-guarded `|…|` wrapping) from `StrataDDM/StrataDDM/Format.lean`
before constructing the `.tvar` node, so `.tvar default name` becomes
`.tvar default (quoteIdent name)` (or equivalent). Reusing the existing helper keeps
the two sites consistent by construction. One fix here also covers the leading-digit
and dot-name use-site variants (any name for which `needsPipeDelimiters` is true).
