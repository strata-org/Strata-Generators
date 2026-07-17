# Unapplied `Bool.Not` operator fails to print

## Summary

Consider this Strata Core function:

```
-- Note: this function is not directly expressible in the concrete syntax (see below)
function f () : bool -> bool { Bool.Not } 
```

In the grammar for Core, `Bool.Not` appears in the concrete syntax as `!b`, where it must appear along with its argument `b` (i.e. `Bool.Not` can only be printed if it is applied). 
When `Bool.Not` is unapplied, `Core.formatProgram` prints `re.none()` (which has a different type) instead,
which violates the round-trip property that printing + parsing should yield the same AST.
This bug was found via property-based testing using a generator for random well-typed Strata Core functions.

## Reproduce (self-contained)

To reproduce, paste the following into a new file `Repro.lean` and run `lake env lean Repro.lean`. 
This following example uses only Strata functions. Expected output is in the trailing comments.

```lean
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda Core Strata
open StrataDDM (initDialect)

/-- Helper function: wraps an expression as the body of `function f () : bool { … }` and prints it. -/
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

-- (1) The printer side: unapplied Bool.Not causes printer to print `re.none()` instead
#eval showBody (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool)))
--  program Core;
--  function f () : bool {
--    re.none()
--  }
--  -- Errors encountered during conversion:
--  -- Unsupported construct in lopToExpr: 0-ary op not found: Bool.Not

-- (2) The following function fails to parse (no concrete syntax for unapplied Bool.Not)
#eval roundtrip "function f () : bool -> bool { Bool.Not }"
--  PARSE ERROR: Parse errors: 1:31: Unknown expr identifier Bool.Not

-- (3) Contrast (NOT a bug): when Bool.Not is applied, the following function passes the round-trip property
#eval showBody (.app () (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool))) (.boolConst () true))
--  program Core;
--  function f () : bool {
--    !true
--  }
#eval roundtrip "function f () : bool { !true }"
--  OK; reformatted = program Core;  function f () : bool {   !true }
```
