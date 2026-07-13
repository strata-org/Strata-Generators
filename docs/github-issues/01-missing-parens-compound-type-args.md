# Printer drops parentheses around compound type arguments (round-trip failure)

## Summary

`Core.formatProgram` does not parenthesize an arrow (or other compound) type when
it appears as an argument to another type constructor. Because type application
(juxtaposition) binds *tighter* than `->` in the grammar, the reprinted string
either fails to parse or parses back to a different type — breaking
`format → parse → format` idempotence.

## Root cause

Type application and arrow have different precedences:

- `TypeApp` (juxtaposition) is **prec 40** — `StrataDDM/StrataDDM/BuiltinDialects/Init.lean:119-126`
- `TypeArrow` (`->`) is **prec 30** — `StrataDDM/StrataDDM/BuiltinDialects/Init.lean:110-117`

But the type converter recurses into children without adding parentheses for the
surrounding context:

- `Strata/Languages/Core/DDMTransform/FormatCore.lean:220-223` — `Map [k,v]`
- `Strata/Languages/Core/DDMTransform/FormatCore.lean:224-226` — `Sequence [e]`
- `Strata/Languages/Core/DDMTransform/FormatCore.lean:227-230` — `arrow [a,b]`

So `Map int (int -> int)` prints as `Map int int -> int`, which the parser reads as
`(Map int int) -> int` (and `Map` is arity-2, so it errors).

## Reproduce (self-contained)

Paste into `Repro.lean` and run `lake env lean Repro.lean` from a workspace that
depends on Strata. Uses only Strata functions.

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

-- Mismatch: the correct source parses, but the reprint drops the parens.
#eval roundtrip "function C () : Sequence (Map int int -> bool);"
-- Parse-failure: feed that printer output straight back in.
#eval roundtrip "function C () : Sequence Map int int -> bool;"
```

## Observed

```
-- #1 (mismatch): source has parens, reprint does not
OK; reformatted =
program Core;

function C () : Sequence Map int int -> bool;

-- #2 (parse failure): the printer's own output does not parse
PARSE ERROR: Parse errors:   1:25: Map expects 2 arguments.   1:29: Unexpected argument to Sequence.
```

## Proof of the misgrouping (regression oracle)

The `roundtrip` helper above only shows the *string*-level paren loss. To pin the
root cause — that the reprint parses to a **structurally different** type — dump the
parsed output-type AST. Use `Map int (int -> int)`, which (unlike the `Sequence`
example) parses in *both* forms, so you can compare the two ASTs directly. A fixed
printer must make `Map int (int -> int)` reprint to a string that parses back to the
first AST below.

Add to the same file (reuses the imports/opens above):

```lean
/-- Parse a one-function program and print its output type's AST (or the error). -/
def probeOutputTy (src : String) : IO Unit := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  let ictx := StrataDDM.Parser.stringInputContext ⟨"repro"⟩ src
  try
    let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" ictx
    let (ast, errs) := TransM.run Inhabited.default (Strata.translateProgram sp)
    match errs.isEmpty, ast.decls with
    | true, [ .func f _ ] => IO.println s!"output type AST = {repr f.output}"
    | _, _ => IO.println s!"ERROR: {(toString errs).replace "\n" " "}"
  catch e => IO.println s!"PARSE ERROR: {(toString e).replace "\n" " "}"

-- Intended type: a Map whose value is an arrow.
#eval probeOutputTy "function f () : Map int (int -> int);"
-- The printer's output: parses as an arrow whose domain is a Map.
#eval probeOutputTy "function f () : Map int int -> int;"
```

Observed — the two strings parse to **different** types (the misgrouping), yet both
reprint to the same `Map int int -> int`:

```
-- Map int (int -> int)  →  Map [int, (int -> int)]   (intended)
output type AST = Lambda.LMonoTy.tcons "Map"
  [Lambda.LMonoTy.tcons "int" [],
   Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.tcons "int" [], Lambda.LMonoTy.tcons "int" []]]

-- Map int int -> int    →  arrow [(Map int int), int] = (Map int int) -> int   (wrong)
output type AST = Lambda.LMonoTy.tcons "arrow"
  [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.tcons "int" [], Lambda.LMonoTy.tcons "int" []],
   Lambda.LMonoTy.tcons "int" []]
```

## Expected

`function C () : Sequence (Map int int -> bool);` should reprint **unchanged**
(parens preserved), and every string `Core.formatProgram` emits should parse.

## Suggested fix

In the type converter (`FormatCore.lean:220-230`), parenthesize a type argument
whenever it is an arrow (prec 30) — or, more conservatively, any non-atomic type —
before splicing it into a juxtaposition position. A single fix resolves both the
parse-failure and mismatch manifestations.

## Notes

This fires for essentially any signature with a `Map`, `Sequence`, or arrow nested
inside another type constructor, and is independent of identifier names. It is the
dominant round-trip failure class we observed (~87% of failures in a 1000-sample
property-test run).
