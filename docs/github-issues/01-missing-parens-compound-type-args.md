# Printer drops parentheses around compound type arguments (round-trip failure)

## Summary

`Core.formatProgram` does not parenthesize an arrow (or other compound) type when
it appears as an argument to another type constructor. Because type application
binds *tighter* than `->` in the grammar, the reprinted string
either fails to parse or parses back to a different type, violating 
the round-trip property that parsing & pretty-printing should yield the same Core program.

For example, given the type `Map int (int -> int)`, the pretty-printer renders it as `Map int int -> int`. 
When we parse this type, since type application binds tighter than `->` in Core's grammar, 
the type is parsed as `(Map int int) -> int` instead, which is a different type. 
This bug applies whenever we have an arrow type that is a type argument to a type constructor (e.g. `Map` or `Sequence`).

## Reproduce (self-contained)

Paste the following into `Repro.lean` and run `lake env lean Repro.lean` from a workspace that
depends on Strata. This example uses only Strata functions. Expected output is in the trailing
comments.

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

-- (1) Round-trip failure
#eval roundtrip "function C () : Sequence Map int int -> bool;"
--  PARSE ERROR: Parse errors: 1:25: Map expects 2 arguments. 1:29: Unexpected argument to Sequence.

-- (2) Highlights how the unparenthesized `Map int int -> int` can be misparsed.
-- A fixed printer must make (3a) reprint to a string that parses back to the (3a) AST.

-- (2a) Intended type: a Map whose value is an arrow.
#eval probeOutputTy "function f () : Map int (int -> int);"
--  output type AST = Lambda.LMonoTy.tcons "Map"
--    [Lambda.LMonoTy.tcons "int" [],
--     Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.tcons "int" [], Lambda.LMonoTy.tcons "int" []]]

-- (2b) The printer's output: parses as (Map int int) -> int — Wrong structure.
#eval probeOutputTy "function f () : Map int int -> int;"
--  output type AST = Lambda.LMonoTy.tcons "arrow"
--    [Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.tcons "int" [], Lambda.LMonoTy.tcons "int" []],
--     Lambda.LMonoTy.tcons "int" []]
```

## Expected
`function C () : Sequence (Map int int -> bool);` should reprint unchanged, and every string `Core.formatProgram` emits should parse.
