import StrataGenerators.Test

/-!
# A worked example

Copy this file when you write a new property. The property here is complete on its own.
It holds the check, the type that it draws from, and the name. No other file holds a part
of it.

```
lake test -- --list                        # make sure that the suite found it
lake test -- --only="example:" --quick     # run only this group
```

To add your own property, put it in the file under `StrataTests/` that fits it best. This
can be this file, another file, or a new file. Then run `lake test`. For a new *file*,
also run `lake exe write-test-imports`. That executable writes the import root
`StrataTests.lean` from the contents of the directory, so you keep no list by hand.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.TestSupport

/-- The size of a program is not less than the number of its declarations.

    `sizeProgram` is the measure that the whole-program shrinker uses to report its
    progress. A size that can ignore declarations would make those figures useless.

    This property states the claim inline as a `Prop`. Plausible reads the shape of the
    proposition, so a draw that falsifies the claim reports the comparison itself, such as
    `issue: 3 ≤ 2 does not hold`. A check that returns a `Bool` reports only
    `issue: false does not hold`.

    Therefore use an inline `Prop` for a claim that is an equality or an order. Use a
    named `check*` predicate in a `*/TestSupport` module when the check is long, when more
    than one property uses it, when a `#guard` must pin it, or when a special Tyche panel
    needs it. Such a predicate returns a `Bool`, and this position accepts a `Bool`
    without a change, because `Bool` coerces to `Prop`. -/
@[strata_property]
def sizeAtLeastDecls : TestDecl :=
  .property "example: sizeProgram is at least the declaration count"
    (fun (gp : GenProgram) => gp.prog.decls.length ≤ sizeProgram gp.prog)
