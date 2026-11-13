import StrataGenerators.Test.Types
import StrataGenerators.Test.Registry
import StrataGenerators.Test.Collect
import StrataGenerators.Test.Report
import StrataGenerators.Test.TycheReport
import StrataGenerators.Test.Cli
import StrataGenerators.Test.Family
import StrataGenerators.Test.Driver
import StrataGenerators.Test.ImportRoot
import StrataGenerators.Test.Generators

/-!
# `StrataGenerators.Test`: the front end for a property test

This is the one import that you need to write a property. It exports each part that the author
of a property needs: the `TestDecl` type, the `@[strata_property]` attribute, and the catalog of
generators `Generators`.

## How to write a property

Put the property in any file under `StrataTests/`. The file can be new or it can exist already,
and it can hold one property or forty properties:

```lean
import StrataGenerators.Test

open StrataGenerators.Test

@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent"
    fun (gp : GenProgram) => myPass (myPass gp.prog) = myPass gp.prog
```

A name and a check are the whole registration. `lake test` runs the property, reports it under a
`mypass` group, and gives it a Tyche panel. You edit no other file. `lake test -- --list` shows
what the harness found, and `lake test -- --only="mypass:" --quick` runs only this group.

The check is a decidable `Prop`, so a claim reads as the statement that it is. A draw that
falsifies the claim then reports the comparison, and not the word `false`. The report gives
`issue: 3 ≤ 2 does not hold` in place of `issue: false does not hold`. A predicate that returns
a `Bool` also works, because `Bool` coerces to `Prop`. You can therefore give a named `check*`
helper to `.property` without a change, and most properties in this suite do that.

Lean chooses the generator in the way that Plausible and QuickCheck choose it: **by the type of
the quantified value**. `GenProgram` has `Arbitrary`, `Repr` and `Shrinkable` instances, so a type
annotation on the binder selects the whole-program generator, its printer and its shrinker at one
time.

The report group is the `area` part of a name of the form `area: description`. The group comes
from the name and no one declares it, so the two cannot disagree. A prefix that no property used
before makes a new group.

## The generator instances

You can use a type with `property` as soon as Plausible can sample it:

| instance | what it gives |
|---|---|
| `Arbitrary α` | how to draw a value |
| `Repr α` | how the report prints a counterexample |
| `Shrinkable α` | how the shrinker reduces a counterexample |
| `TycheFeatures α` | the Tyche axes. It is optional, because a catch-all instance gives none. |

Lean also resolves the `Decidable` instance of the check at the registration site. That site is
where the resolution must happen. Plausible receives the `Prop` without a decision, so
`PrintableProp` still sees the shape and the message can name both sides of a comparison. The
Tyche panel and the shrinker receive the decided form, because they must classify each sample and
not only test it. Both instances travel with the property in `Body.sampled`.

`TycheFeatures` is an addition of this package, for the same reason that the other three are
classes. An axis such as `num_decls`, `decl_kinds` or `rejection_cause` is a fact about the
*type* and not about one claim. One instance therefore gives each later property the axes that
separate a vacuous draw from a live one. `StrataGenerators.Test.Generators` holds the instances
for the shapes of this package, and `StrataGenerators.TestScaffold` holds the generators.

To sample a type in a way that its default instances do not give, name a `PropertyRunner` with
`TestDecl.forAll`. This is the `forAll` of QuickCheck, which also names its generator.
`Generators.program.withRender …` keeps each axis and it changes only the printer. This is the
only reason for a property to name a `PropertyRunner`.

## The other shapes

`TestDecl.property` is the only entry point that you need for a property which quantifies over
one generated value, and almost every property has that shape. Three other shapes cover the
other cases:

* `TestDecl.witness` takes a closed `Bool`. Use it for a claim whose best statement is one
  program that you build, or one operator. A random sample would hide which case the claim
  covers.
* `TestDecl.witnesses` takes a *fixed and finite* input space. It scores one element at a time,
  and Tyche lists the space in place of a sample.
* `TestDecl.action` takes an `IO` action that drives itself. Use it for an oracle that is a
  subprocess, or for an oracle that must print its own diagnostics between the draws. Add
  `gate := some "smt"` when the action needs a live solver.

`@[strata_properties]` registers a `List TestDecl` at one time. `family T [ … ]` is sugar that
builds such a list when the entries share an input type. It names `T` one time, and it expands
each entry to its own `TestDecl.property`. An entry is therefore a decidable `Prop` that the
suite scores in the same way as a property that stands alone. There is one way to state a check
in the whole API, and a family is no exception.

`TestDecl.forAll` is the form that names a `PropertyRunner`.

`@[strata_diagnostic]` registers a `Diagnostic`, which is a report that prints and never gates
the exit code. Use it for a statistic about coverage, or for a count that locates an error.

`docs/writing-properties.md` gives the long form, and it says how the harness finds your file.
-/
