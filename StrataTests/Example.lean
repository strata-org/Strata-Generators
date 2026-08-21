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

    So prefer an inline `Prop` for a claim whose shape is an equality or an order. Prefer
    a named `check*` predicate in a `*/TestSupport` module when the check is long, is
    reused, is worth pinning with a `#guard`, or is shared with a bespoke Tyche panel;
    such a predicate usually returns a `Bool` and is accepted here unchanged, since
    `Bool` coerces to `Prop`.

    A named predicate can return `Prop` instead and keep the readable counterexample, at
    the cost of two rules that are easy to trip over: it must be an `abbrev` (a `def` is
    not reducible enough for `DecidablePred` to synthesize at the registration site), and
    the equality must sit at the predicate's *top level* (an outermost `∀ x ∈ …` renders
    as `⋯`). `docs/writing-properties.md` spells both out. -/
@[strata_property]
def sizeAtLeastDecls : TestDecl :=
  .property "example: sizeProgram is at least the declaration count"
    (fun (gp : GenProgram) => gp.prog.decls.length ≤ sizeProgram gp.prog)
