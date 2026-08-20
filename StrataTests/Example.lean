import StrataGenerators.Test

/-!
# A worked example

This file exists to be copied. It is one property, complete: the check, the
generator it draws from, and the name — with nothing registered anywhere else.

```
lake test -- --list                       # confirm it was picked up
lake test -- --only=example --quick       # run just this one
```

To add your own, copy this file under `StrataTests/`, rename the declarations, and
run `lake test`. The `lake test` script regenerates the `StrataTests.lean` import
root from the directory, so there is no list to add yourself to.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.TestSupport

/-- The reducible size of a program is at least its declaration count.

    A modest claim, but a load-bearing one: `sizeProgram` is the measure the
    whole-program shrinker reports progress against, so a size that could ignore
    declarations would make the shrinker's reduction figures meaningless. -/
def checkSizeAtLeastDecls (p : Core.Program) : Bool :=
  p.decls.length ≤ sizeProgram p

/-- Registering the property. The four arguments are the whole interface: a unique
    name (the report label and the Tyche panel title), the report group, the
    generator, and the check. -/
@[strata_property]
def sizeAtLeastDecls : TestDecl :=
  .property "example: sizeProgram is at least the declaration count" "example"
    Gens.program (fun gp => checkSizeAtLeastDecls gp.prog)
