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

/-- Registering the property. `forAll` picks the generator the way Plausible and
    QuickCheck do: from the **type** of the argument. `GenProgram` carries
    `Arbitrary`/`Repr`/`Shrinkable` instances, so annotating the binder is all it takes
    to select the whole-program generator, its renderer and its shrinker. -/
@[strata_property]
def sizeAtLeastDecls : TestDecl :=
  .forAll "example: sizeProgram is at least the declaration count" "example"
    (fun (gp : GenProgram) => checkSizeAtLeastDecls gp.prog)

/-- The same claim as a `Prop`, run by Plausible's `Testable` instance for it, exactly
    as `#test` would. Use this spelling when the `Prop` form buys something the `Bool`
    form cannot express: more than one `∀`, or a `Decidable` hypothesis used as a
    guard. The cost is that no Tyche panel can be derived, because a `Prop` does not
    expose the type it quantifies over. -/
@[strata_property]
def sizeAtLeastDeclsProp : TestDecl :=
  .check "example: sizeProgram bound, stated as a Prop" "example"
    (∀ gp : GenProgram, gp.prog.decls.length ≤ sizeProgram gp.prog)
