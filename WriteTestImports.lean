import StrataGenerators.Test.ImportRoot

/-!
# `lake exe write-test-imports`

Writes the `import` list of `StrataTests.lean` from the contents of the `StrataTests/`
directory. It runs no test and it does no metaprogramming: it lists a directory and it
writes a text file. See `StrataGenerators.Test.ImportRoot` for the logic.

Run it when you add a file to `StrataTests/`, or when you remove one. To add a property
to a file that exists changes no import, so you do not need it then.

This executable does **not** import `StrataTests`. Therefore it still builds when
`StrataTests.lean` names a module that no longer exists, which is the state a deleted
property file leaves behind. That is why the work is here, and not in a test driver.
-/

def main : IO UInt32 := do
  let (rewritten, count) ← StrataGenerators.Test.ImportRoot.regenerate
  if rewritten then
    IO.println s!"StrataTests.lean rewritten ({count} modules)."
  else
    IO.println s!"StrataTests.lean is up to date ({count} modules)."
  return 0
