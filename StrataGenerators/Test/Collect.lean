import StrataGenerators.Test.Registry

/-!
# The collection of the registry

The two term elaborators that turn the records of the attributes in
`StrataGenerators.Test.Registry` into ordinary Lean values. They are in their own module,
because Lean cannot *evaluate* an `initialize` value in the module that declares it, and these
elaborators evaluate `propertyTag` and the other extensions.

One line gives a driver its whole knowledge of the suite:

```lean
def registry : List TestDecl := strata_registry%
```
-/

open Lean

namespace StrataGenerators.Test

open Elab Term in
/-- Expands to the `List TestDecl` of each `@[strata_property]` and `@[strata_properties]`
    declaration that this module sees. This is the whole suite, and no one keeps a list by hand
    that can go out of date.

    The elaborator splices a `@[strata_properties]` list in place. A report therefore cannot
    tell the two attributes apart. -/
elab "strata_registry%" : term => do
  let chunks ← (registryEntries (← getEnv)).mapM fun
    | .single n => `(term| [($(mkIdent n) : TestDecl)])
    | .many n   => `(term| ($(mkIdent n) : List TestDecl))
  elabTerm (← `(List.flatten [$chunks,*])) none

open Elab Term in
/-- Expands to the `List Diagnostic` of each `@[strata_diagnostic]` declaration that this
    module sees. -/
elab "strata_diagnostics%" : term => do
  let terms ← (diagnosticEntries (← getEnv)).mapM fun n =>
    `(term| ($(mkIdent n) : Diagnostic))
  elabTerm (← `([$terms,*])) none

open Elab Command in
/-- Checks that the module which holds this command imports each `.lean` file under
    `StrataTests/`. The command gives an error that names each file that the module does not
    import.

    A file that no module imports is the condition that needs a command. Without this check, a
    new property file that no one imports leaves the suite green, and the suite tests one thing
    less than it claims. A new property in a file that *exists* changes no import, so this
    command acts only when someone adds or removes a file.

    The command has two limits. If it cannot read the directory, it passes. An out-of-tree
    build or a different working directory can cause this, and neither is a mistake of the
    author of a property. The check also runs only when Lean *elaborates this module again*. A
    new file does not make a cached `StrataTests.olean` stale, so a warm local build does not
    see it. Neither limit matters for the purpose of the check: CI builds from a fresh
    checkout, and a local `lake test` writes the root again before the build. -/
elab "#verify_test_root" : command => do
  let dir : System.FilePath := "StrataTests"
  let entries ← liftM (m := IO) (do
    if ← dir.isDir then (← dir.readDir).toList |> pure else pure [])
  let expected := entries.filterMap fun e =>
    if e.path.extension == some "lean" then
      e.path.fileStem.map fun stem => `StrataTests ++ Name.mkSimple stem
    else none
  let imported := (← getEnv).header.moduleNames
  let missing := expected.filter fun m => !imported.contains m
  unless missing.isEmpty do
    let lines := missing.map (s!"import {·}")
    throwError "`StrataTests.lean` is out of date: \
      {missing.length} property file(s) are not imported, so their properties are not \
      in the suite.\n\nRun `lake exe write-test-imports`, and commit the result. \
      The missing lines are:\n\n{String.intercalate "\n" lines}"

end StrataGenerators.Test
