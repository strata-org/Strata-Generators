import StrataGenerators.Test.Types
import StrataGenerators.Test.Registry
import StrataGenerators.Test.Collect
import StrataGenerators.Test.Report
import StrataGenerators.Test.TycheReport
import StrataGenerators.Test.Cli
import StrataGenerators.Test.Root
import StrataGenerators.Test.Generators

/-!
# `StrataGenerators.Test` — the property-test front end

The single import for writing a property. Everything a property author needs is
re-exported here: the `TestDecl` type, the `@[strata_property]` attribute, and the
generator catalog `Generators`.

## Writing a property

Any file under `StrataTests/` — an existing one or a new one, one property or forty:

```lean
import StrataGenerators.Test

open StrataGenerators.Test

/-- My pass does not change a program it has already changed. -/
def checkMyPassIdempotent (p : Core.Program) : Bool :=
  myPass (myPass p) == myPass p

@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent" fun (gp : GenProgram) => checkMyPassIdempotent gp.prog
```

A name and a check. That is the whole registration: `lake test` runs it, reports it
under a `mypass` group, and gives it a Tyche panel — with no other file edited.
`lake test -- --list` shows what the harness picked up;
`lake test -- --only="mypass:" --quick` iterates on just this group.

The generator is chosen the way Plausible and QuickCheck choose it: **by the type of
the quantified value**. `GenProgram` carries `Arbitrary`/`Repr`/`Shrinkable` instances,
so annotating the binder selects the whole-program generator, its renderer and its
shrinker at once.

The report group is the `area` of an `area: description` name — derived, never declared,
so it cannot disagree with the name. A prefix nothing has used before simply creates a
new group.

## The generator instances

A type is usable with `property` as soon as Plausible can sample it:

| instance | supplies |
|---|---|
| `Arbitrary α` | how to draw a value |
| `Repr α` | how a counterexample is printed |
| `Shrinkable α` | how a counterexample is reduced |
| `TycheFeatures α` | the Tyche axes (optional; a catch-all instance gives none) |

`TycheFeatures` is this package's addition, for the same reason the other three are
classes: `num_decls`, `decl_kinds` and `rejection_cause` are facts about the *type*,
not about any one claim, so declaring them once gives every later property the axes
that tell a vacuous draw from a live one. The instances for this package's shapes are
in `StrataGenerators.Test.Generators`; the generators themselves are in
`StrataGenerators.TestScaffold`.

To sample a type in a way its default instances do not, name a `PropertyRunner`
explicitly with `TestDecl.forAll` — the explicit-generator sense of QuickCheck's
`forAll`. `Generators.program.withRender …` keeps every axis and changes only the
printer. That is the only reason a property ever mentions a `PropertyRunner`.

## The other shapes

`TestDecl.property` is the only entry point you need for a property that quantifies
over one generated value, which is nearly all of them. Three other shapes exist for the
cases that are not:

* `TestDecl.witness` — a closed `Bool`. For a claim whose sharpest statement is one
  constructed program or one operator, where sampling would only obscure which case is
  at stake.
* `TestDecl.witnesses` — a *fixed finite* input space, scored element by element and
  enumerated (not sampled) in Tyche.
* `TestDecl.action` — a self-driving `IO` action, for an oracle that is a subprocess or
  that must interleave its own diagnostics with generation. Pair it with
  `gate := some "smt"` when it needs a live solver.

`@[strata_properties]` registers a `List TestDecl` at once; `family` pairs each name
with its check in one line, for a family that shares an input type. `familyOf` and
`TestDecl.forAll` are the variants that name a `PropertyRunner` explicitly.

`@[strata_diagnostic]` registers a `Diagnostic`: a report that prints and never gates
the exit code, for a coverage statistic or a localisation tally.

See `docs/writing-properties.md` for the longer version, including how the harness
discovers your file.
-/
