import StrataGenerators.Test

/-!
# A worked example

This file exists to be copied. The property here is complete on its own: the check,
the type it draws from, and the name — with nothing registered anywhere else.

```
lake test -- --list                        # confirm it was picked up
lake test -- --only="example:" --quick     # run just this group
lake test -- --only="example:" --seed=7    # …reproducibly, reporting the seed on a failure
```

To add your own, put it in whatever file under `StrataTests/` it belongs in — this one,
another, or a new one — and run `lake test`. A new *file* also needs
`lake exe write-test-imports`, which rewrites the `StrataTests.lean` import root from the
directory listing, so there is no list you maintain by hand.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.TestSupport

/-- The reducible size of a program is at least its declaration count.

    A modest claim, but a load-bearing one: `sizeProgram` is the measure the whole-program
    shrinker reports progress against, so a size that could ignore declarations would make
    the shrinker's reduction figures meaningless.

    Stated inline as a `Prop`. A failing draw then reports the comparison itself —
    `issue: 3 ≤ 2 does not hold` — because Plausible reads the shape of the proposition.
    A `Bool`-valued check reports only `issue: false does not hold`.

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
