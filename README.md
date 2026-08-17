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

## Properties tested & bugs found
See `properties_bugs_found.md` for a complete list!

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
3. Run a small amount of tests (note the `--quick` flag):
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

## Adding a new property

Properties are listed in
[`Properties.lean`](./StrataGenerators/Properties.lean) and invoked from [`TestMain.lean`](./TestMain.lean). 

To add a new property:

1. Put the property (an `α → Bool` function, where `α` is the type 
   produced by the generator) in the relevant `*.TestSupport` module (e.g.
   `ProcedureHasTypeAGen/TestSupport.lean`).
   
2. Define a string containing the name of the property in `PropertyNames` namespace
   in `Properties.lean` (e.g. `expr`, `cmd`, ...), then add this string to
   `PropertyNames.all` (at the bottom of `Properties.lean`). This string is the name of the
   property that is displayed in `stdout` / Tyche when the test harness is run.

3. Add the property to the test suite in `TestMain.lean`:
   - For a pure `α → Bool` property, wrap it as a `Prop` (e.g. `def prop_foo : Prop := check_foo … = true`), 
     and add a `checkIO PropertyNames.yourName (∀ x, your_prop x)` expression to the relevant 
     test suite in `TestMain.lean`.
   - For an `IO`-based check (e.g. a property that requires an external tool to run, like an SMT solver), 
     add the property using an `.individualIO PropertyNames.yourName none action .done` expression in `TestMain.lean`. 
     The SMT/concrete-eval agreement property
     ([`HasTypeAGen/SmtEval.lean`](./StrataGenerators/HasTypeAGen/SmtEval.lean),
     gated behind `--smt`) is a worked example.

4. (Optional, for visualizing test results in Tyche) See [Adding a panel for a new
   property](#adding-a-panel-for-a-new-property) for details.

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

Note: the following steps assume the property is already defined in the test harness
(see [Adding a new property](#adding-a-new-property) on how to add a new property).

#### 1. Define the type containing the data to be visualized

This type is typically a `structure` that contains the generated value,
along with auxiliary featuers that cannot be recomputed, e.g.:

```lean
structure PropResult where
  value   : MyThing       -- Value produced by generator
  passed  : Bool          -- No. of trials passed
  genSize : Nat           -- The generator size `value` was sampled at
```

If several properties share the same `PropResult` type, define an extra `tag` field 
in the `structure` and distinguish them using the name of the visualization distinguish 
(see `StmtPropResult` and `ProcPropResult` for an example of how this is done).

#### 2. Implement an instance of `Tyche.TycheSample` typeclass for the type defined in step (1)

```lean
instance : Tyche.TycheSample PropResult where
  toSample r :=
    { representation := formatMyThing r.value              -- Function for serializing `r.value`
      status         := if r.passed then .passed else .failed
      statusReason   := if r.passed then "" else explainFailure r.value
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        ("cause",   .nominal (classifyCause r.value)),     -- Why a property failed
        ("size",    .ordinal (sizeOf r.value)) ] }
```

- **`representation`**: If generating random Strata Core programs, use 
  Strata Core's own pretty-printer (`Core.formatProgram`, `formatStmts`, `formatFunc`) .
- **`status`**: this must be the same property function that is invoked by the test harnes
  (i.e. a function in the relevant `*.TestSupport` module).
- **`features`**: `.nominal` for grouping, `.ordinal` / `.continuous` for
  distributions. Include at least one field that explains why a property failed
  (e.g. `rejection_cause`, `measure_no_body`, `violating_phases`, `error_sites`).
  For samples that pass a property vacuously, use an explicit `"—"` indicator
  rather than treating them as trials that passed.

#### 3. Write the generator wrapper

An `IO MyPropResult`. Reuse an existing draw (`genStmtsForTyche`,
`genProcsForTyche`, `genProgramForTyche`) rather than a fresh generator call, so
the panel samples the same distribution as its neighbours, and vary the generator
size per sample. If the property's counterexamples are shrinkable, minimize on
failure and recompute the features from the minimized value, so they describe what
is actually displayed:

```lean
def generatorWrapper (prop : MyThing → Bool) : IO PropResult := do
  let (x, genSize) ← genMyThingForTyche -- Invoke the actual generator`
  if prop x then
    return { value := x, passed := true, genSize }
  else
    -- `minimizeProcsCounterexample` / `minimizeProgramCounterexample` keep every
    -- candidate well-typed *and* still-failing, so the verdict is unchanged.
    return { value := minimizeMyCounterexample prop 200 x, passed := false, genSize }
```

#### 4. Register it in `runTychePanels`

Add the following expression in the `runTychePanels` function in `TycheViz.lean`:
```lean
panel PropertyNames.myProperty (generatorWrapper myProperty)
```

Alternatively, if the property belongs to an existing list of `Property`s in
[`Properties.lean`](./StrataGenerators/Properties.lean) 
(e.g. `StmtTransforms`), you can iterate over them like so:


```lean
for p in Properties.stmtTransforms do
  panel p.name (genStmtProp p.name p.check)
```

Note that `panel` defaults to `--tyche-samples` samples. 
To override this option, pass `(count := n)` .

**For properties with a finite and small no. of inputs**:
For properties whose input space is finite and small (e.g., all bitvectors of width 4),
use the `enumerate` function instead of `panel`. 
The `enumerate` function performs one trial per element in the input space, 
as opposed to running `--tyche-samples` times:

```lean
enumerate PropertyNames.printerBvIntConversions bvIntConversionSamples
```

The test oracle for these properties is a conjunction over all elements
in the input space (e.g. `checkBvIntConversionsPrint`). 

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
