import StrataGenerators.Test

/-!
# A worked example

This file exists to be copied. Each property here is complete on its own: the check,
the type it draws from, and the name — with nothing registered anywhere else.

```
lake test -- --list                        # confirm it was picked up
lake test -- --only="example:" --quick     # run just this group
```

To add your own, put it in whatever file under `StrataTests/` it belongs in — this one,
another, or a new one — and run `lake test`. A new *file* also needs
`lake exe gen-test-root`, which rewrites the `StrataTests.lean` import root from the
directory listing, so there is no list you maintain by hand.
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

/-- Registering the property. A name and a check, and nothing else.

    `forAll` picks the generator the way Plausible and QuickCheck do: from the **type**
    of the argument. `GenProgram` carries `Arbitrary`/`Repr`/`Shrinkable` instances, so
    annotating the binder is all it takes to select the whole-program generator, its
    renderer and its shrinker.

    The report group is the name's `example:` prefix. It is derived, not declared, so it
    cannot disagree with the name. -/
@[strata_property]
def sizeAtLeastDecls : TestDecl :=
  .forAll "example: sizeProgram is at least the declaration count"
    (fun (gp : GenProgram) => checkSizeAtLeastDecls gp.prog)

/-- The same claim as a `Prop`, run by Plausible's `Testable` instance for it, exactly
    as `#test` would. Use this spelling when the `Prop` form buys something the `Bool`
    form cannot express: more than one `∀`, or a `Decidable` hypothesis used as a
    guard. The cost is that no Tyche panel can be derived, because a `Prop` does not
    expose the type it quantifies over. -/
@[strata_property]
def sizeAtLeastDeclsProp : TestDecl :=
  .check "example: sizeProgram bound, stated as a Prop"
    (∀ gp : GenProgram, gp.prog.decls.length ≤ sizeProgram gp.prog)
