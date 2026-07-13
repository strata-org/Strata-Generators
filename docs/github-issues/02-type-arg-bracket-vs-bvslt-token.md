# `<s`-initial type argument collides with the `<s` (signed-less-than) token

## Summary

When a type-argument name begins with `s`, the printed `<...>` type-argument list
is mis-lexed: the maximal-munch tokenizer grabs `<s` (the signed-less-than
bitvector operator) before `<` can open the type-argument bracket. The printer
emits `function f<s> () : int;`, which its own parser then rejects.

## Root cause

Two grammar tokens collide under maximal munch:

- Type arguments print with `<...>` brackets —
  `Strata/Languages/Core/DDMTransform/Grammar.lean:62`:
  `op type_args (...) : TypeArgs => "<" args ">";`
- Signed-less-than is the token `<s` —
  `Strata/Languages/Core/DDMTransform/Grammar.lean:187`:
  `fn bvslt (…) => @[prec(20), leftassoc] a " <s " b;`

So `f<s>` lexes as `f` · `<s` · `s>`: the `<s` operator token is grabbed before `<`
can open the bracket. The parser then expects bindings after `f`.

Inserting a space (`f< s>`) defeats the maximal munch and parses; the space is
*not* folded into the name (the lexer stores trailing whitespace separately, and an
identifier's value spans only id-characters — `StrataDDM/StrataDDM/Parser.lean`),
so `f< s>` parses with type parameter `s` and reprints as `f<s>`.

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

-- What the printer emits for a type arg named `s`: fails to parse.
#eval roundtrip "function f<s> () : int;"
-- Adding a space defeats the maximal munch (parses; name is still `s`).
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

`function f<s> () : int;` should parse: the `<` opening a type-argument list should
not be swallowed into the `<s` operator token.

## Suggested fix

Tokenizer/precedence adjustment so `<` opening a `TypeArgs` list is recognized
ahead of `<s` in that position (e.g. require surrounding whitespace for the `<s`
infix operator, or make the type-arg opener a distinct token). Self-contained and
easy to demonstrate: `f<s>` fails, `f< s>` parses.

## Notes

Affects any type-variable name starting with `s` — which the identifier generators
readily produce — so this is not a special-character edge case.
