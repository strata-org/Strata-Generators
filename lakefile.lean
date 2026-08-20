import Lake
open Lake DSL System

package «strata-generators» where
  version := v!"0.1.0"
  testDriver := "test"

require "strata-org" / "Strata" @ git "main"

require "hgoldstein95" / "basalt" @ git "lean-4.29"

-- Strata is on Lean 4.29.1, but mainline LSpec is on 4.31, so we depend on a fork
-- of LSpec that is on 4.29.
require "ngernest" / "LSpec" @ git "aa07f8c"

@[default_target]
lean_lib «StrataGenerators» where
  globs := #[.andSubmodules `StrataGenerators]

/-- The property files. Globbed, so a new file under `StrataTests/` is built without
    a configuration change; `StrataTests.lean` (the import root the drivers read) is
    regenerated from this directory by the `test` script below.

    A default target, so a plain `lake build` — which is all CI runs, since the suite
    reports known counterexamples and would fail it — still compiles every property. -/
@[default_target]
lean_lib «StrataTests» where
  globs := #[.andSubmodules `StrataTests]

lean_exe «strata-generators» where
  root := `Main

/-- The reference driver: the registry rendered by the package's own reporter, with no
    test-framework dependency. -/
lean_exe «strata-test» where
  root := `TestRunner

/-- The same registry rendered by LSpec, so a rendering discrepancy is visible. -/
lean_exe «lspec-test» where
  root := `LSpecTestRunner

-- ── Test-root generation ──────────────────────────────────────────────
--
-- Lean links statically, so a `@[strata_property]` declaration is visible to a driver
-- only if the driver transitively imports the module it lives in. `StrataTests.lean`
-- is that import, and it is *generated* from the directory listing rather than
-- hand-maintained, so adding a property really is a one-file change.
--
-- This is the same approach `tasty-discover` takes for Haskell and that Cargo takes
-- for a crate's `tests/` directory: discovery happens in the build tool, because it is
-- the build tool that decides what gets compiled.

/-- The banner on the generated root, and the marker that it is safe to overwrite. -/
private def rootHeader : String :=
"-- GENERATED FILE — do not edit by hand.
--
-- `lake test` regenerates this from the contents of `StrataTests/` before building,
-- so a new property file is picked up with no edit here. Run `lake run testRoot` to
-- regenerate it on its own.
--
-- Why it exists at all: Lean links statically, so a `@[strata_property]` declaration
-- is only visible to the driver if the driver transitively imports the module it
-- lives in. This file is that import — the analogue of `mod tests;` in Rust, or of a
-- file being part of a Dune library in OCaml. It is generated rather than
-- hand-maintained precisely so that it is not a file a property author has to edit.
"

/-- Every `.lean` file under `StrataTests/`, as module names, sorted so the generated
    root is stable under a directory listing's order. -/
private def testModules : IO (Array String) := do
  let mut names := #[]
  for entry in ← (FilePath.mk "StrataTests").readDir do
    if entry.path.extension == some "lean" then
      if let some stem := entry.path.fileStem then
        names := names.push s!"StrataTests.{stem}"
  return names.qsort (· < ·)

/-- Write `StrataTests.lean` if its contents would change. Returns whether it did. -/
private def writeTestRoot : IO Bool := do
  let mods ← testModules
  let contents := rootHeader ++ String.join (mods.toList.map (s!"import {·}\n"))
    ++ "\n-- Fails the build if a file under `StrataTests/` is missing from the list\n\
       -- above, so a property file added without regenerating this root cannot go\n\
       -- silently untested. Run `lake run testRoot` to regenerate.\n\
       #verify_test_root\n"
  let path : FilePath := "StrataTests.lean"
  let current ← if ← path.pathExists then IO.FS.readFile path else pure ""
  if current == contents then
    return false
  IO.FS.writeFile path contents
  return true

/-- Regenerate `StrataTests.lean` from the directory listing. -/
script testRoot do
  if ← writeTestRoot then
    IO.println "StrataTests.lean regenerated."
  else
    IO.println "StrataTests.lean is up to date."
  return 0

/-- The `lake test` driver: regenerate the import root, then build and run the
    reference driver. Regenerating first is what makes a new property file be picked
    up by `lake test` alone. -/
script test args do
  if ← writeTestRoot then
    IO.println "StrataTests.lean regenerated from StrataTests/."
  let ws ← getWorkspace
  let some exe := ws.root.findLeanExe? `«strata-test»
    | error "strata-test executable not found"
  let exeFile ← runBuild exe.fetch
  env exeFile.toString args.toArray
