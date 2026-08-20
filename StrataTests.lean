-- GENERATED FILE — do not edit by hand.
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

-- Fails the build if a file under `StrataTests/` is missing from the list
-- above, so a property file added without regenerating this root cannot go
-- silently untested. Run `lake run testRoot` to regenerate.
#verify_test_root
