import StrataGenerators.Test.Registry

/-!
# Collecting the registry

The two term elaborators that turn what the attributes of
`StrataGenerators.Test.Registry` recorded into ordinary Lean values. They live in
their own module because an `initialize` value cannot be *evaluated* in the module
that declares it, and these elaborators evaluate `propertyTag` and friends.

A driver's whole knowledge of the suite is one line:

```lean
def registry : List TestDecl := strata_registry%
```
-/

open Lean

namespace StrataGenerators.Test

open Elab Term in
/-- Expands to the `List TestDecl` of every `@[strata_property]` and
    `@[strata_properties]` declaration visible from here — the whole suite, with no
    hand-maintained list that can fall out of date.

    A `@[strata_properties]` list is spliced in place, so from a report's point of
    view the two attributes are interchangeable.

    An attribute's `(seed := N)` argument becomes a `withSeed` around the declaration —
    over each member, for a list. The pin is therefore applied *here* rather than being
    carried through the run as a second, parallel notion of what a property's seed is:
    what a driver folds over is a plain `List TestDecl` whose `seed` fields are already
    the ones the attributes asked for. -/
elab "strata_registry%" : term => do
  let chunks ← (registryEntries (← getEnv)).mapM fun
    | .single n none      => `(term| [($(mkIdent n) : TestDecl)])
    | .single n (some s)  => `(term| [withSeed $(quote s) ($(mkIdent n) : TestDecl)])
    | .many n none        => `(term| ($(mkIdent n) : List TestDecl))
    | .many n (some s)    =>
      `(term| (($(mkIdent n) : List TestDecl).map (withSeed $(quote s))))
  elabTerm (← `(List.flatten [$chunks,*])) none

open Elab Term in
/-- Expands to the `List Diagnostic` of every `@[strata_diagnostic]` declaration
    visible from here. -/
elab "strata_diagnostics%" : term => do
  let terms ← (diagnosticEntries (← getEnv)).mapM fun n =>
    `(term| ($(mkIdent n) : Diagnostic))
  elabTerm (← `([$terms,*])) none

open Elab Command in
/-- Check that every `.lean` file under `StrataTests/` is imported by the module this
    command appears in, and error naming the ones that are not.

Silent absence is the failure mode worth spending a command on: without this, a
    property file added but never imported leaves the suite green, having tested one
    thing less than it claims. Adding a property to an *existing* file changes no
    import, so this only ever fires when a file is added or removed.

    Two honest limitations. Reading the directory is best-effort: if it cannot be read
    (an out-of-tree build, a different working directory) the command passes rather than
    failing on something that is not a property author's mistake. And the check only
    runs when this module is *re-elaborated* — adding a file does not invalidate a
    cached `StrataTests.olean`, so a warm local build will not see it. Neither matters
    for what the check is for: CI builds from a fresh checkout, and a local `lake test`
    regenerates the root before building. -/
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
