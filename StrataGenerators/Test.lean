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
  .property "mypass: the pass is idempotent" "mypass" Gens.program checkMyPassIdempotent
```

`lake test` then runs it, reports it under a `mypass` group, and gives it a Tyche
panel — with no other file edited. `lake test -- --list` shows what the harness
picked up; `lake test -- --only=mypass --quick` iterates on just this one.

The four arguments are the whole interface: the property's **name** (unique across
the suite; it is the report label and the Tyche panel title), the **report group**,
the **generator** its input is drawn from, and the **check**.

## The other shapes

Most properties are a `Bool` check over a generator, which is what
`TestDecl.property` builds. Three other shapes exist for the cases that are not:

* `TestDecl.witness` — a closed `Bool`. For a claim whose sharpest statement is
  one constructed program or one operator, where sampling would only obscure which
  case is at stake.
* `TestDecl.witnesses` — a *fixed finite* input space, scored element by element
  and enumerated (not sampled) in Tyche.
* `TestDecl.action` — a self-driving `IO` action, for an oracle that is a
  subprocess or that must interleave its own diagnostics with generation. Pair it
  with `gate := some "smt"` when it needs a live solver.

`@[strata_properties]` registers a `List TestDecl` at once, for a family that
shares one generator and differs only in the check.

`@[strata_diagnostic]` registers a `Diagnostic`: a report that prints and never
gates the exit code, for a coverage statistic or a localisation tally.

## Choosing a generator

`Gens` holds one entry per shape the package generates — expression, command,
function, statement list, procedure list, whole program, datatype block. Prefer the
smallest shape that can express the claim; reach for `Gens.program` when the claim
spans more than one declaration. A generator of your own is a `GenSpec` you define
in your own file; nothing in `Gens` is privileged.

See `docs/writing-properties.md` for the longer version, including how the
harness discovers your file.
-/
