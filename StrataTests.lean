-- GENERATED FILE — do not edit by hand.
--
-- Regenerate with `lake exe write-test-imports` after you add or remove a file under
-- `StrataTests/`. Adding a property to an existing file needs no regeneration.
--
-- Why this file exists: Lean links statically, so a `@[strata_property]` declaration
-- is only visible to the driver if the driver transitively imports the module it
-- lives in. This file is that import — the analogue of `mod tests;` in Rust, or of a
-- file being part of a Dune library in OCaml. It is generated rather than
-- hand-maintained precisely so that it is not a file a property author has to edit.
import StrataTests.Adt
import StrataTests.Alias
import StrataTests.Cmd
import StrataTests.Diagnostics
import StrataTests.Example
import StrataTests.Expr
import StrataTests.Function
import StrataTests.Lift
import StrataTests.Mutual
import StrataTests.Phase
import StrataTests.Printer
import StrataTests.Proc
import StrataTests.Program
import StrataTests.Stmt
import StrataTests.Transforms

-- Fails the build if a file under `StrataTests/` is missing from the list above, so a
-- property file added without regenerating this root cannot go silently untested.
#verify_test_root
