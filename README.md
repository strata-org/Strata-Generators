# Random generators for Strata Core programs 

This repo contains random generators for well-typed [Strata](https://github.com/strata-org/strata)
Core programs. These generators are built using the [Basalt](https://github.com/hgoldstein95/basalt) Lean 
framework, which allows us to prove these generators sound and complete with respect to their typing relations.

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
in the same file, as `List.Forall₂` is defined by both libraries. Additionally, since 
the proof files need Mathlib tactics, the generator
definitions live in Mathlib-free `Core` modules and expose flat contexts (e.g.
an `OpCtx = List (String × LMonoTy)`) instead of importing Strata's `Factory`.

## Dependencies

- `Strata`
- `Basalt`
- `Plausible`

## Building

1. Resolve dependencies:
   ```bash
   lake update
   ```
2. Fetch prebuilt Mathlib artifacts (avoids compiling Mathlib from scratch):
   ```bash
   lake exe cache get
   ```
3. Build:
   ```bash
   make build
   ```

### Makefile targets

| Target | Description |
|--------|-------------|
| `make build` | Build all Lean sources (`lake build`) |
| `make tyche` | Build and run the Tyche visualization executable |
| `make test` | Build and run the Plausible test suite |

## Property-based testing

Run the property-based test suite (via Basalt's `PlausibleGen`, which makes the
generators executable under `Plausible.Gen`):

```bash
lake build test-lexpr
.lake/build/bin/test-lexpr [numTrials] [maxSize]
```

- `numTrials` (default: 1000) — number of random test cases per property
- `maxSize` (default: 100) — maximum size parameter for generation (controls
  expression/statement depth)

The harness exercises properties across all four generators — expression
type-safety (typecheck, preservation, progress, type-erasure round-trip),
command well-typedness and store-type preservation, function typechecking and
soundness of `Function.typeCheck`, and statement-transform passes (LoopElim,
ANF, DetToKleene). Expression generation covers both **open terms** (free
variables from a fixed context: `x : bool`, `f : int -> bool`, `n : int`) and
**closed terms**, using operators from `IntBoolFactory`.

A few properties are *expected* to find counterexamples — for instance,
`progress` and `normalization`: `LExpr.eval` gets stuck on quantifiers in
condition position (e.g. `if (forall x. e) then ...`) and on equality of
lambdas with non-identical bodies. Progress and preservation follow the
Software Foundations convention of being stated for the empty typing context.

## Tyche visualization

Visualize the generators' output distributions with
[Tyche](https://github.com/tyche-pbt/tyche-extension), a VS Code extension for
inspecting property-based testing generators.

### Generating samples

```bash
lake build tyche-viz
.lake/build/bin/tyche-viz [numSamples] [outputPath]
```

- `numSamples` (default: 1000) — number of samples per generator
- `outputPath` (default: `tyche_output.jsonl`) — output file path

The depth parameter is varied uniformly over [1, 5] across samples so that
visualizations cover the full range of generator behavior. Each sample records
`gen_depth` as a feature.

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
