/-!
# The `StrataTests.lean` import root

This module writes the import root, and it checks that the root is fresh. The work is
plain file IO: it reads a directory and it writes a text file of `import` lines. It uses
no metaprogramming. `StrataGenerators.Test.Registry` holds the attribute and
`StrataGenerators.Test.Collect` holds the collector.

Lean links statically. Therefore a driver sees a `@[strata_property]` declaration only if
the driver imports the module that holds the declaration, directly or indirectly. This is
the same need as `mod tests;` in Rust, or as a file in a Dune library in OCaml. This
module writes the import list from the contents of the `StrataTests/` directory, so the
author of a property does not edit the root.

Three consumers use this module:

* `lake exe write-test-imports` rewrites the root on demand.
* Both drivers refuse to run against a stale root. They rewrite the root and ask you to
  run them again, because the linker built the binary from the old root.
* `#verify_test_root` in the generated root fails the **build** on a stale root. See
  `StrataGenerators.Test.Collect`.

The driver check and the build check overlap on purpose. The build check is exact,
because it compares the list against the modules that Lean imported. However, it runs
only when Lean elaborates the root again, and a warm local build with an unchanged root
skips it. The driver check is textual and it always runs. Together, the two checks make
sure that the suite tests each property file.

You must run the generator again only when you **add or remove** a file under
`StrataTests/`. If you add a property to a file that exists, the imports do not change.
-/

namespace StrataGenerators.Test.ImportRoot

/-- The comment block at the start of the generated root. -/
def header : String :=
"-- GENERATED FILE. Do not edit it by hand.
--
-- Run `lake exe write-test-imports` again after you add or remove a file under
-- `StrataTests/`. If you add a property to a file that exists, the imports do not
-- change.
--
-- Lean links statically. Therefore a driver sees a `@[strata_property]` declaration
-- only if the driver imports the module that holds the declaration, directly or
-- indirectly. This file is that import. It is the same need as `mod tests;` in Rust, or
-- as a file in a Dune library in OCaml. A generator writes this file, so the author of
-- a property does not edit it.
"

/-- The guard at the end of the generated root. It fails the build when the import list
    is stale. -/
def footer : String :=
"
-- This guard fails the build if the list above does not hold a file that is under
-- `StrataTests/`. Therefore the suite cannot miss a new property file.
#verify_test_root
"

/-- The directory that holds the property files. -/
def dir : System.FilePath := "StrataTests"

/-- The path of the generated root. -/
def rootPath : System.FilePath := "StrataTests.lean"

/-- The module name of each `.lean` file under `StrataTests/`. The names are in sorted
    order, so the generated root does not change with the order that the file system
    gives. -/
def testModules : IO (Array String) := do
  let mut names := #[]
  for entry in ← dir.readDir do
    if entry.path.extension == some "lean" then
      if let some stem := entry.path.fileStem then
        names := names.push s!"StrataTests.{stem}"
  return names.qsort (· < ·)

/-- The correct contents of the generated root. -/
def expectedRoot : IO String := do
  let mods ← testModules
  return header ++ String.join (mods.toList.map (s!"import {·}\n")) ++ footer

/-- Rewrites the root if the correct contents differ from the current contents. Returns
    `true` if it wrote the file, and the number of modules in the list. -/
def regenerate : IO (Bool × Nat) := do
  let contents ← expectedRoot
  let mods ← testModules
  let current ← if ← rootPath.pathExists then IO.FS.readFile rootPath else pure ""
  if current == contents then
    return (false, mods.size)
  IO.FS.writeFile rootPath contents
  return (true, mods.size)

/-- The setup check for a driver. If the root is stale, this rewrites the root and
    returns `true`. A result of `true` tells the driver to stop, because the linker built
    the binary from the old root. You must then run the driver again.

    If the module cannot read `StrataTests/`, it reports that the root is fresh. An
    out-of-tree build or a different working directory can cause this, and neither is a
    mistake of the author of a property. -/
def ensureFresh : IO Bool := do
  if !(← dir.isDir) then
    return false
  let (rewritten, count) ← regenerate
  if rewritten then
    IO.println s!"StrataTests.lean was stale; regenerated it ({count} modules)."
    IO.println "Re-run to pick up the change."
  return rewritten

end StrataGenerators.Test.ImportRoot
