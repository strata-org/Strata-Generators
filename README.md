# Random generators for Strata Core programs 

This repo contains random generators for well-typed [Strata](https://github.com/strata-org/strata)
Core programs. These generators are built using the [Basalt](https://github.com/hgoldstein95/basalt) Lean 
framework, which allows us to prove these generators sound and complete with respect to Strata Core's typing relations.

Specifically, the repo contains generators for the following fragment of Strata Core:
- Expressions (`LExpr`s) (typing relation: `HasTypeA`)
  - Note: our `LExpr` generator targets the `HasTypeA` typing relation (which pertains to well-annotated locally nameless terms), not `HasTypeA`
- Commands (typing relation: `CmdHasTypeA`)
- Functions (typing relation: `FunctionHasTypeA`)
- Statements & statement sequences (typing relation: `StmtHasTypeA`, `StmtsHasTypeA`)
- Procedures (typing relation: `ProcHasTypeA`)
- Whole programs (typing relation: `ProgramHasTypeA`)

## Generator Interpretations
Basalt generators are polymorphic in their monad (see the [Basalt repo](https://github.com/hgoldstein95/basalt) for more details): this means they can be interpreted differently for execution / proofs. 

- To run these generators, we interpret them using `Plausible`'s `Gen` monad. 
- To prove properties about the generators, we interpret them using `SetGen`, which reasons about
a generator's *support* (the set of all values that can be produced by the generator)

**Note**: Basalt allows reasoning about generators' distributions via another interpretation (`SPMF`, in 
which generators are viewed as sub-probability mass functions), but this repo does not use this interpretation at the moment. `SetGen.lean` contains `SetGen` variants of some `SPMF` results that appear 
in the Basalt source code, which are required for proofs about Strata generators.

### Organization

Each generator is split into a `Core.lean` (containing the generator's executable code) and a
separate proof file. For example, for the `LExpr` generator, `HasTypeAGen/Core.lean` contains 
the actual code for the generator, while `HasTypeAGen.lean` contains the generator's correctness proofs. 
This allows us to avoid importing both Strata and Batteries (imported transitively via Mathlib) 
in the same file, as `List.Forall₂` is defined by both libraries. 

## Dependencies

- `Strata`
- `Basalt` (used for proving generators correct)
- `Plausible` (used to run generators)
- `LSpec` (Lean testing framework; used by the `test` driver that `lake test` runs. The
  alternate `test-plain` driver needs nothing beyond `Plausible`)
- (Optionally) An SMT solver (cvc5 or z3) to test Strata properties related to SMT encoding, which are not run by default
  - See the [installation instructions in the Strata repository](https://github.com/strata-org/strata#smt-solvers) on how to install cvc5/z3

## Building

1. Resolve dependencies and fetch prebuilt artifacts:
   ```bash
   lake update
   lake exe cache get
   ```
2. Build:
   ```bash
   lake build
   ```
3. Run a small amount of tests (note the `--quick` flag):
   ```
   lake test -- --quick
   ```


## Running tests using these generators

```bash
lake test -- --quick
```

`--quick` runs 100 trials per property at a maximum input size of 40. Omit it and the
full suite — 145+ properties — takes 10+ minutes.

To configure the run, pass arguments through after `--`:

```bash
lake test -- [numTrials] [maxSize] [flags]
```

- `numTrials` (default 1000) — random test cases per property
- `maxSize` (default 100) — maximum size parameter for generation (controls the depth
  of the generated AST)

Flags (all optional; the Tyche visualization pass is on by default):

- `--quick` — 100 trials, maximum size 40, no Tyche pass. A positional argument has
  higher precedence, so `--quick 500` gives 500 trials and keeps the rest of the preset.
- `--only=SUBSTRING` — run only the properties whose name contains `SUBSTRING`.
  Repeatable. This is the loop to iterate in while writing one property: it also skips
  the diagnostics and writes no Tyche file. Since a report group is a name prefix,
  `--only="lift:"` selects the `lift` group exactly.
- `--list` — print the registry (name, group, gate, expectation) and exit without running
  anything. The answer to "did my property get picked up?", and to "what is known to
  fail?"
- `--known-failure=NAME` — treat the property called `NAME` as known to fail for this
  run: suppress its counterexample and stop it gating the exit code. Repeatable, and it
  takes a whole property name rather than a substring. The committed form is
  `.knownFailure` on the declaration, which also carries the reason — see
  [`docs/writing-properties.md`](./docs/writing-properties.md).
- `--no-tyche` — omit Tyche visualizations (i.e. only run tests).
- `--tyche-out=PATH` — output path for the JSONL file Tyche ingests (default
  `tyche_output.jsonl`).
- `--tyche-samples=N` — samples visualized per Tyche panel (default 1000).
- `--smt` — also run the properties whose oracle is a real SMT solver. Requires a local
  `cvc5` or `z3`; if none can be launched the harness errors out with a non-zero exit
  code. Without the flag those properties are reported as `SKIP`, never as passes.

The exit code is the property verdict. Diagnostics and the Tyche pass never affect it.

You can also build and run the driver directly:

```bash
lake build test
.lake/build/bin/test [numTrials] [maxSize] [flags]
```

`lake test -- --list` prints the full list of properties tested; each one is declared
in a file under [`StrataTests/`](./StrataTests).

### LSpec-free driver (`test-plain`)

`lake test` runs the LSpec driver. A second driver renders the *same* registry through
the package's own reporter, and depends on `Plausible` and nothing else:

```bash
lake build test-plain
.lake/build/bin/test-plain [numTrials] [maxSize] [flags]
```

It exists to keep the LSpec dependency droppable: LSpec reaches this package only
through a fork pinned to Lean 4.29, because mainline LSpec is on 4.31.

Both drivers fold the same `List TestDecl`, and everything except the rendering is
`StrataGenerators.Test.Driver`, shared by both. So they cannot disagree about *what* is
tested, and a discrepancy could only be in the printing.

## Adding a new property

A property — its check, its generator, and its name — goes in whatever file under
[`StrataTests/`](./StrataTests) you think it belongs in: an existing one or a new one,
one property or forty. You do not edit any file in `StrataGenerators/`.

```lean
import StrataGenerators.Test

open StrataGenerators.Test

@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent"
    fun (gp : GenProgram) => myPass (myPass gp.prog) = myPass gp.prog
```

A name and a check. That is the whole registration. `lake test` discovers it, reports it under a `mypass`
group, and gives it a Tyche panel.

The check is a decidable `Prop`, so a failing draw reports the comparison itself
(`issue: 3 ≤ 2 does not hold`) rather than the word `false`. A `Bool`-valued `check*`
helper is accepted unchanged, since `Bool` coerces to `Prop`.

The generator is chosen the way Plausible and QuickCheck choose it: by the **type** of
the quantified value. `GenProgram` carries the `Arbitrary`/`Repr`/`Shrinkable` instances
Plausible needs, so annotating the binder selects the whole-program generator, its
printer and its shrinker at once. The report group is the name's `mypass:` prefix,
derived rather than declared.

```bash
lake test -- --list                     # confirm it was picked up
lake test -- --only="mypass:" --quick   # run just this group
```

[`StrataTests/Example.lean`](./StrataTests/Example.lean) is a working copy of this
shape, and **[`docs/writing-properties.md`](./docs/writing-properties.md)** is the
full guide: how the harness discovers your file, which input types are generable, how
to make a new type generable with the four instances, the three non-sampled property shapes (a single
witness, a finite input space, a self-driving `IO` action), opt-in gates such as
`--smt`, registering a family at once, marking a property that is known to fail against a
Strata defect, custom Tyche panels, and diagnostics.

### When the property is right and Strata is wrong

Mark it, rather than deleting it or letting it hold up a merge:

```lean
@[strata_property]
def myPassOutputTypechecks : TestDecl :=
  (TestDecl.property "mypass: the output typechecks"
     fun (gp : GenProgram) => checkMyPassOutputTypechecks gp.prog).knownFailure
    "strata-org/Strata#123: the pass drops a type annotation on a nested call"
```

It then reports `? XFAIL`, prints no counterexample, and does not gate the exit code —
but **if it ever passes, the run fails** and asks you to drop the mark, so the fix cannot
go unnoticed. Use `.rareFailure` instead for a property that fails only on an occasional
draw; it gates in neither direction. `lake test -- --list` prints every mark and its
reason.

## Tyche visualization

One can visualize the generators' output distributions with
[Tyche](https://github.com/tyche-pbt/tyche-extension), a VS Code extension for
inspecting property-based testing generators.

### Generating samples

The test driver writes Tyche panels by default, so a plain run produces the
JSONL file alongside the property-test results:

```bash
lake build test
.lake/build/bin/test [numTrials] [maxSize]
```

Use these CLI flags to control the output:

- `--tyche-samples=N` (default: 1000) — number of samples per generator
- `--tyche-out=PATH` (default: `tyche_output.jsonl`) — output file path

The Tyche visualizations dominate the runtime of the `lake test` executable. 
By default, the `--quick` CLI flag suppresses Tyche visualizations.
To get the smaller no. of trials via the `--quick` flag while still 
having Tyche visualizations, pass the following CLI args manually
to the test executable:

```bash
.lake/build/bin/test 100 40 --tyche-samples=200
```

### Viewing Tyche visualizations

Open VS Code, press `Cmd+Shift+P` (on macOS), run
`Tyche: Open`, and select the generated `.jsonl` file. Tyche displays
interactive histograms and distribution charts for each property.

### Adding a Tyche visualization for a new property

There is nothing to add. A registered property gets a panel derived from its input
type's instances: `Repr` draws the sample, `TycheFeatures` gives the axes, the
property's verdict is the mark's status, and `Shrinkable` minimizes a failing sample
before display.

So the way to improve a panel is to improve the type's `TycheFeatures` instance — see
[`StrataGenerators/Test/Generators.lean`](./StrataGenerators/Test/Generators.lean), where each
shape's axes are declared once and shared by every property over it. Include at least
one axis that explains *why* a property failed (`rejection_cause`, `decl_kinds`,
`func_shape`), since that is what separates a vacuous pass from a real one.

A handful of panels cannot be derived: one whose oracle is itself an `IO` action (a
solver run, a format→parse round-trip), or one whose breakdown reports something the
generated input alone does not determine (which pipeline phase lied, which printer
site refused). Those live in
[`TycheViz.lean`](./StrataGenerators/TycheViz.lean) and are attached to their property
with `withPanel`, in the `StrataTests/` file that declares it:

```lean
@[strata_property]
def myProp : TestDecl :=
  (TestDecl.property "mypass: …"
    (fun (gp : GenProgram) => checkMine gp.prog)).withPanel myPanelAction
```

`myPanelAction : IO β` for any `β` with a `Tyche.TycheSample` instance; the panel takes
its title from the property's `name`, so the two cannot drift apart. For a property
whose input space is *finite*, use `withEnumeratedPanel` instead, which emits one mark
per element rather than sampling the space with replacement.

#### Checking that the Tyche visualizations appear
Run the following to produce the Tyche visualizations with a small no. of tests:

```bash
lake build test
.lake/build/bin/test 100 40 --tyche-samples=200
```

Then, in VS Code, do `Cmd+Shift+P` → `Tyche: Open`, and click on the relevant panel.

## License

The contents of this repository are licensed under the terms of either
the Apache-2.0 or MIT license, at your choice. See
[LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for
details of the two licenses.