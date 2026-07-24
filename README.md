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

## Running tests using these generators 

To run a test executable, which tests a variety of properties using these Strata Core generators,
run `lake test`. 

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

- `--no-tyche` — skip the Tyche visualization pass (property tests only)
- `--tyche-out=PATH` — Tyche JSONL output path (default `tyche_output.jsonl`)
- `--tyche-samples=N` — samples per Tyche panel (default 1000)

See [`Properties.lean`](./StrataGenerators/Properties.lean) for the full list of properties tested.

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

### Viewing results

Open VS Code, press `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS), run
`Tyche: Open`, and select the generated `.jsonl` file. Tyche displays
interactive histograms and distribution charts for each property.

### Adding Tyche support to a new generator

1. Import `StrataGenerators.Tyche`.
2. Implement a `Tyche.TycheSample` instance for your generated type:
   ```lean
   instance : Tyche.TycheSample MyType where
     toSample x :=
       { representation := toString x
         features := [
           ("size", .ordinal (computeSize x)),
           ("kind", .nominal (classifyKind x))
         ] }
   ```
3. Call `Tyche.run` with your `IO` generator action and a `Tyche.Config`.

## License

The contents of this repository are licensed under the terms of either
the Apache-2.0 or MIT license, at your choice. See
[LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for
details of the two licenses.
