import StrataGenerators.Test.Root

/-!
# `lake exe gen-test-root`

Rewrites the `StrataTests.lean` import root from the contents of `StrataTests/`.
Needed only when a file is added or removed there; adding a property to an existing
file changes no import. See `StrataGenerators.Test.Root`.
-/

def main : IO UInt32 := do
  let (rewritten, count) ← StrataGenerators.Test.Root.regenerate
  if rewritten then
    IO.println s!"StrataTests.lean regenerated ({count} modules)."
  else
    IO.println s!"StrataTests.lean is up to date ({count} modules)."
  return 0
