/-!
# The `StrataTests.lean` import root

Writing the import root, and the check that it is fresh. This is plain file IO: a
directory listing, and a text file of `import` lines. None of it is metaprogramming.
The metaprogramming lives in `StrataGenerators.Test.Registry` (the attribute) and
`StrataGenerators.Test.Collect` (the collector).

Lean links statically, so a `@[strata_property]` declaration is visible to a driver
only if the driver transitively imports the module it lives in — the analogue of
`mod tests;` in Rust, or of a file being part of a Dune library in OCaml. This module
writes that import list from the contents of the `StrataTests/` directory, so it is
not a file a property author edits.

Three consumers share it, which is why it lives here rather than in one of them:

* `lake exe write-test-imports`, to rewrite the root on demand;
* both drivers, which refuse to run against a stale root — they rewrite it and ask to
  be re-run, since the binary they are executing was already linked from the old one;
* `#verify_test_root` in the generated root itself (see
  `StrataGenerators.Test.Collect`), which fails the *build* on a stale root and is
  what catches the case CI cares about.

The driver check and the build check overlap on purpose. The build check is exact,
because it compares against the modules Lean actually imported, but it only runs when
the root is re-elaborated — a warm local build with an unchanged root skips it. The
driver check is textual and always runs. Between them, a property file cannot go
silently untested either locally or in CI.

Regeneration is needed only when a file is **added or removed** under `StrataTests/`.
Adding a property to an existing file changes no import.
-/

namespace StrataGenerators.Test.ImportRoot

/-- The banner on the generated root. -/
def header : String :=
"-- GENERATED FILE — do not edit by hand.
--
-- Regenerate with `lake exe write-test-imports` after you add or remove a file under
-- `StrataTests/`. Adding a property to an existing file needs no regeneration.
--
-- Why this file exists: Lean links statically, so a `@[strata_property]` declaration
-- is only visible to the driver if the driver transitively imports the module it
-- lives in. This file is that import — the analogue of `mod tests;` in Rust, or of a
-- file being part of a Dune library in OCaml. It is generated rather than
-- hand-maintained precisely so that it is not a file a property author has to edit.
"

/-- The trailing guard, which fails the build when the list above is stale. -/
def footer : String :=
"
-- Fails the build if a file under `StrataTests/` is missing from the list above, so a
-- property file added without regenerating this root cannot go silently untested.
#verify_test_root
"

/-- The directory holding the property files. -/
def dir : System.FilePath := "StrataTests"

/-- The generated root's path. -/
def rootPath : System.FilePath := "StrataTests.lean"

/-- Every `.lean` file under `StrataTests/`, as module names, sorted so the generated
    root is stable under whatever order a directory listing returns. -/
def testModules : IO (Array String) := do
  let mut names := #[]
  for entry in ← dir.readDir do
    if entry.path.extension == some "lean" then
      if let some stem := entry.path.fileStem then
        names := names.push s!"StrataTests.{stem}"
  return names.qsort (· < ·)

/-- The text the root should have. -/
def expectedRoot : IO String := do
  let mods ← testModules
  return header ++ String.join (mods.toList.map (s!"import {·}\n")) ++ footer

/-- Rewrite the root if its contents would change. Returns whether it did, and how
    many modules it lists. -/
def regenerate : IO (Bool × Nat) := do
  let contents ← expectedRoot
  let mods ← testModules
  let current ← if ← rootPath.pathExists then IO.FS.readFile rootPath else pure ""
  if current == contents then
    return (false, mods.size)
  IO.FS.writeFile rootPath contents
  return (true, mods.size)

/-- A driver's setup check. When the root is stale this rewrites it and returns
    `true`, meaning "do not run: the binary was linked from the old root, so re-run".

    Best-effort: if `StrataTests/` cannot be read — an out-of-tree build, a different
    working directory — this reports fresh rather than failing on something that is not
    a property author's mistake. -/
def ensureFresh : IO Bool := do
  if !(← dir.isDir) then
    return false
  let (rewritten, count) ← regenerate
  if rewritten then
    IO.println s!"StrataTests.lean was stale; regenerated it ({count} modules)."
    IO.println "Re-run to pick up the change."
  return rewritten

end StrataGenerators.Test.ImportRoot
