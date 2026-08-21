-- GENERATED FILE. Do not edit it by hand.
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
import StrataTests.Adt
import StrataTests.Alias
import StrataTests.Cmd
import StrataTests.Diagnostics
import StrataTests.Example
import StrataTests.Expr
import StrataTests.Function
import StrataTests.Lift
import StrataTests.Monomorphization
import StrataTests.Mutual
import StrataTests.Phase
import StrataTests.Printer
import StrataTests.Proc
import StrataTests.Program
import StrataTests.Stmt
import StrataTests.Transforms

-- This guard fails the build if the list above does not hold a file that is under
-- `StrataTests/`. Therefore the suite cannot miss a new property file.
#verify_test_root
