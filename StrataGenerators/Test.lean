import StrataGenerators.Test.Types
import StrataGenerators.Test.Registry
import StrataGenerators.Test.Collect
import StrataGenerators.Test.Report
import StrataGenerators.Test.TycheReport
import StrataGenerators.Test.Cli
import StrataGenerators.Test.Gens

/-!
# `StrataGenerators.Test` — the property-test front end

The single import for writing a property. Everything a property author needs is
re-exported here: the `TestDecl` type, the `@[strata_property]` attribute, and the
generator catalog `Gens`.

## Writing a property

One file, anywhere under `StrataTests/`:

```lean
import StrataGenerators.Test

open StrataGenerators.Test

/-- My pass does not change a program it has already changed. -/
def checkMyPassIdempotent (p : Core.Program) : Bool :=
  myPass (myPass p) == myPass p

@[strata_property]
def myPassIdempotent : TestDecl :=
  .forAll "mypass: the pass is idempotent" fun (gp : GenProgram) => checkMyPassIdempotent gp.prog
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

## Stating the property as a `Prop`

`TestDecl.check` takes a `Prop` and runs it through the `Testable` instance Plausible
synthesizes for it — the same elaboration `#test` and `Plausible.Testable.check` use,
`mk_decorations` included:

```lean
@[strata_property]
def myPropShaped : TestDecl :=
  .check "mypass: idempotent under any fuel"
    (∀ gp : GenProgram, ∀ n : Nat, myPass n gp.prog = myPass (n + 1) (myPass n gp.prog))
```

Reach for this when the `Prop` form buys something the `Bool` form cannot express:
more than one `∀`, a `Decidable` hypothesis used as a guard, or a type whose
`SampleableExt` instance samples through a proxy. The cost is that no Tyche panel can
be derived, since a `Prop` does not expose the type it quantifies over.

## The generator instances

A type is usable with `forAll` as soon as Plausible can sample it:

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
in `StrataGenerators.Test.Gens`; the generators themselves are in
`StrataGenerators.TestScaffold`.

To sample a type in a way its default `Arbitrary` instance does not, pass a `GenSpec`
explicitly with `TestDecl.property` — `Gens.program.withRender …` keeps every axis and
changes only the rendering.

## The other shapes

Most properties are a `Bool` check over a sampled type, which is what
`TestDecl.forAll` builds. Three other shapes exist for the cases that are not:

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
`TestDecl.property` are the variants that take an explicit `GenSpec`.

`@[strata_diagnostic]` registers a `Diagnostic`: a report that prints and never gates
the exit code, for a coverage statistic or a localisation tally.

See `docs/writing-properties.md` for the longer version, including how the harness
discovers your file.
-/
