import StrataGenerators.Test.ImportRoot

/-!
# `lake exe write-test-imports`

This executable writes the `import` list of `StrataTests.lean` from the contents of the
`StrataTests/` directory. It runs no test and it uses no metaprogramming. It reads a
directory and it writes a text file. For the logic, see
`StrataGenerators.Test.ImportRoot`.

Run it when you add a file to `StrataTests/`, or when you remove a file. If you add a
property to a file that exists, the imports do not change.

This executable does **not** import `StrataTests`. Therefore it builds when
`StrataTests.lean` names a module that does not exist. This is the reason why the work
is here and not in a test driver.
-/

def main : IO UInt32 := do
  let (rewritten, count) ← StrataGenerators.Test.ImportRoot.regenerate
  if rewritten then
    IO.println s!"StrataTests.lean rewritten ({count} modules)."
  else
    IO.println s!"StrataTests.lean is up to date ({count} modules)."
  return 0
