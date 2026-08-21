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
- `LSpec` (Lean testing framework, we use LSpec's test harnesses to run tests)
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
3. Run a small amount of tests (note the `--quick` flag, which runs each property with 100 random inputs):
   ```
   lake test -- --quick
   ```


## Running tests using these generators 

To run a test executable, which tests a variety of properties using these Strata Core generators,
run `lake test -- --quick`. (The `--quick` flag minimizes the no. of tests run, if we omit this flag,
the entire test suite, consisting of 80+ properites, takes 10+ minutes to run.)

This executable runs a Plausible test suite via LSpec, and visualizes test results using [Tyche](https://github.com/tyche-pbt/tyche-extension), a VS Code extension for
inspecting property-based testing generators.

If you want to manually configure the no. of trials / size of inputs, you can pass
them through to the test driver after `--`:

```bash
lake test -- [numTrials] [maxSize] [flags]
```

Alternatively, you can also build & run the test executable directly as follows:

```bash
lake build test
.lake/build/bin/test [numTrials] [maxSize] [flags]
```

- `numTrials` (default: 1000) — number of random test cases per property
- `maxSize` (default: 100) — maximum size parameter for generation (controls
  the depth of the generated AST)

Flags (all optional; the Tyche visualization pass is on by default):

- `--quick` runs a small no. of tests with a small size, prioritizing fast results. 
  Currently, this flag runs 100 trials for each property, where each input has a maximum size of 40.
  This flag omits Tyche visualizations:
- `--no-tyche`: omit Tyche visualizations (i.e. only run tests)
- `--tyche-out=PATH`: output filepath for JSON files storing test metadata which is ingested by Tyche (this defaults to `tyche_output.jsonl`)
- `--tyche-samples=N` — no. of test samples visualized per Tyche panel (default 1000)
- `--smt` — Tests properties related to Strata SMT encodings. This CLI flag requires a local installation of an SMT solver (cvc5/z3). 
  If `--smt` is passed but the SMT solver cannot be run, the test harness emits an error and exits with a non-zero exit code.

See [`Properties.lean`](./StrataGenerators/Properties.lean) for the full list of properties tested.

### LSpec-free harness (`test-plain`)

There is a second test executable, `test-plain`, that does not depend on LSpec. 
All properties, generators and CLI flags are shared with the default test runner (the one inovked by doing `lake test`).

To run the alternate `test-plain` harness, do:
```bash
lake build test-plain
.lake/build/bin/test-plain [numTrials] [maxSize] [--smt]
```

`test-plain` keeps the LSpec dependency droppable. LSpec reaches this package only through a
fork that is pinned to Lean 4.29, because mainline LSpec is on Lean 4.31.

## Tuning the generators' distributions

The generators are sound *and* complete, so every sample is well-typed and every well-typed program is
reachable. Neither law says how *often* a shape appears, and the properties in the suite are not equally
sensitive to all shapes. A property whose interesting precondition holds on 2% of samples spends 98% of
its budget on a trivial case. A property whose precondition never holds passes vacuously.

Every generator that the suite draws from therefore carries Basalt's `@[tunable]` attribute, which makes
each `frequency` branch weight a runtime value:

```lean
-- 24 : 2 in favour of `loop`, so a loop-elimination pass gets loops to eliminate
def stmtLoopHeavy : Tuning := withWeights stmtDefault [(StmtIdx.loop, 24)]
```

- [`TuningProfiles.lean`](./StrataGenerators/TuningProfiles.lean) holds one named `Tuning` per job the
  suite has to do. It gives the desirable distribution per property family, the flat index tables that
  a profile is written in, and the tuned entry points that the harnesses draw from.
- [`ProgramTuning.lean`](./StrataGenerators/ProgramTuning.lean) holds the same for whole programs. It
  is a separate module because the program generator's proof files import Mathlib.
- [`SetGen/TuningPrototypes.lean`](./StrataGenerators/SetGen/TuningPrototypes.lean) proves one theorem
  per generator that tuning **preserves behaviour**. At `SetGen.Set` the tuned generator is *equal* to
  the untuned one for every `θ`. Every soundness and completeness result therefore carries over by one
  `rw`, and no profile can make a program shape unreachable.
- [`SetGen/Tuning.lean`](./StrataGenerators/SetGen/Tuning.lean) holds the reweighting lemmas that those
  proofs run on, and one recipe per recursion form.
- [`SetGen/TuningWalkthrough.lean`](./StrataGenerators/SetGen/TuningWalkthrough.lean) is where to start
  if you want to *use* tuning on a generator of your own.

### Measuring a distribution (`dist-report`)

The weights above come from measurement rather than from judgement. `dist-report` samples each family's
generator under each profile, and reports how often the shapes that the properties discriminate on
appear. It also reports `1st-try`, the fraction of draws that succeed with no retry, because a profile
that steers into failure-prone shapes buys its coverage with generation time.

```bash
lake exe dist-report [samples] [maxSize] [--stmt] [--proc] [--cmd] [--expr] [--prog]
```

A property names the distribution it is checked over in its registration attribute, so a choice of
weighting is a one-line change where the property is declared. A claim checked under *two* weightings
registers two properties, and each has its own verdict, its own line in the report and its own Tyche
panel:

```lean
@[strata_property (tunings := [("default", stmtDefault), ("loop-heavy", stmtLoopHeavy)])]
def loopElimPreservesTyping : TestDecl :=
  .property "stmt: LoopElim preserves typeability"
    fun (gs : GenStmts) => checkLoopElimPreservesTyping gs.stmts
```

`(tuning := θ)` is the single-weighting form, and `θ` is an ordinary term, so
`(tuning := withWeights stmtDefault [(StmtIdx.loop, 30)])` works for a one-off. `StrataTests/Stmt.lean`
uses this for both `LoopElim` properties, and `StrataTests/Monomorphization.lean` uses it for five
`mono:` properties. [`docs/writing-properties.md`](./docs/writing-properties.md#choosing-the-distribution)
is the guide.

Only some input types can be tuned. `StrataGenerators.Test.Generators` lists them: the statement,
procedure, command, expression and whole-program shapes. A tuning on a type with no `TunableGen`
instance is an error at the declaration, and the message names the type, rather than a tuning that is
silently ignored.

## Adding a new property

Properties to test are defined in the `StrataTests/` directory. 
As an end-user of this library, you can add properites to either an existing file in `StrataTests/`, 
or create a new file in `StrataTests/`.

To add a new property (e.g. to test that a new pass `myPass` is idempotent), add the following:

```lean
import StrataGenerators.Test

open Core
open StrataGenerators.Test

-- This registers a new property
-- As the user, you can customize the name for the property in the string 
-- (Note that this name must be unique among all properties in the test suite)
@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent"
    fun (gp : GenProgram) => myPass (myPass gp.prog) = myPass gp.prog
```
(For another example, see `StrataTests/Example.lean`.)

See "Choosing the input type" below for instructions on how to pick the right type
to be generated. Note that the body of the function should be a `Prop` that is decidable 
(or alternatively a function that returns `Bool`). In our experience, functions 
that are decidable `Prop`s have better error messages (coming from the Plausible property-based testing library).

The `@[strata_property]` attribute records the test declaration, allowing 
the test driver to pick it up.


If you added / removed a file in `StrataTests/`, run the following in order to populate 
the test executable (`StrataTests.lean`) with the appropriate import statements.
Note that users should not modify `StrataTests.lean` by hand.

```
lake exe write-test-imports
```

Then, run the following:

```
# This lists all properties in the test suite, to confirm your new property was registered
lake test -- --list    

# Test only properties whose names begin with the substring "mypass:"
lake test -- --only="mypass:" --quick

# Test all properties (with only 100 inputs per property to minimize time spent)
lake test -- --quick
```

## Choosing the input type

These are the types in the Strata Core AST for which we support random generation. 
Each type corresponds to a fragment of the Strata Core language.

All of these types already have instances of the `Arbitrary`, `Repr`, `Shrinkable` and `TycheFeatures` 
typeclasses, allowing them to be randomly generated, pretty-printed, shrunk (minimized when a counterexample 
to a property is found) and visualized using the Tyche VS code extension (see the `Tyche visualization` section below).

The function argument in the property should be one of the following types:

| Type | Term produced by random generation |
|---|---|
| `TypedExpr` | a well-typed expression with its type, over `defaultFCtx` |
| `ClosedTypedExpr` | a well-typed closed expression (no free variables) |
| `ResolveTypedExpr` | a closed expression over `coreOpCtx` |
| `GenCmdWithCtx` / `GenCmdsWithCtx` | a command, or a command sequence, with its input & output contexts |
| `GenFunction` / `ClosedGenFunction` | a function (pure), with free variables coming from `defaultFCtx` or no free variables (closed function) |
| `GenStmts` | a well-typed sequence of statements |
| `GenProcs` | a list of well-typed procedures |
| `GenProgram` | an entire well-typed Strata Core program, including top-level declarations (Algebraic data type definitions, abstract types, type aliases, axioms) |
| `GenAdtBlock` / `GenIndepBlock` | a `mutual … end` datatype block containing (possibly mutually recursive) ADT definitions |

If the Strata Core AST changes in the future and we gain new type definitions, to support these new types, 
users need to implement instances of the `Arbitrary, Repr, Shrinkable, TycheFeatures` typeclasses for it.

## Defining families of properties
If multiple properties share the same input type (e.g. stating multiple properties about the `LoopElim` transformation over statements), 
we can define them using the `@[strata_properties]` attribute, like so:

```lean
-- Each property is an entry in a list passed to `family`, specifically 
-- a tuple consisting of the property name and the actual property function
@[strata_properties]
def stmtTransforms : List TestDecl :=
  family GenStmts
    [ ("stmt: LoopElim preserves typeability", fun gs => checkLoopElimPreservesTyping gs.stmts),
      ("stmt: LoopElim eliminates all loops",  fun gs => checkLoopElimZeroLoops gs.stmts) ]
```

Note the use of `family` macro, which allows us to define a list of properties (instead of defining properties one by one). 

## Marking individual properties as known to fail
If a property is known to fail, we can prefix the property using the `knownFailure` function and supply 
a string containing the failure reason, like so:

```lean
@[strata_property]
def myPassOutputTypechecks : TestDecl :=
  knownFailure "strata-org/Strata#123: the pass drops a type annotation on a nested call" <|
    TestDecl.property "mypass: the output typechecks"
      fun (gp : GenProgram) => checkMyPassOutputTypechecks gp.prog
```

The test suite then avoids reporting counterexamples that cause this property to fail,
facilitating bug triage.

If the property is part of a `family`, we add `.knownFailure "<failure_reason>"` as
an extra component of the tuple corresponding to the property. For example, 
using the `stmtTransform`s example above, if we wanted to mark the `LoopElim eliminates all loops` 
property as known to fail, we would do this:

```lean
def stmtTransforms' : List TestDecl :=
  family genStmts [
    ("stmt: LoopElim eliminates all loops",  fun gs => checkLoopElimZeroLoops gs.stmts, 
    .knownFailure "<failure_reason>"),
    ...
  ]
```


## Tyche visualization

One can visualize the generators' output distributions with
[Tyche](https://github.com/tyche-pbt/tyche-extension), a VS Code extension for
inspecting property-based testing generators.

### Generating samples

The boilerplate code to produce Tyche visualizations are automatically added
when a new property is registered. By default, the test driver updates the Tyche panels
in VS Code (the `--quick` / `--no-tyche` CLI flags suppress this behavior).

To add auxiliary information to a Tyche panel, modify the 
instance of the `TycheFeatures` typeclass for the type being generated 
(see
[`StrataGenerators/Test/Generators.lean`](./StrataGenerators/Test/Generators.lean) for details).
For example, one can add a feature that explains why a property-based test failed (`rejection_cause`).

To further control the Tyche visualizations, use these CLI flags:

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