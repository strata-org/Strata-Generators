# strata-generators

Random generators for [Strata](https://github.com/strata-org/strata) via [Basalt](https://github.com/hgoldstein95/basalt), with proved soundness and completeness.

## Well-typed generators

Two generators produce well-typed Strata `LExpr`s with proved soundness, using different variable representations:

- **[`HasTypeAGen.lean`](./StrataGenerators/HasTypeAGen.lean)** — Generator of well-typed terms (using De Bruijn indices) satisfying the `HasTypeA` relation. Lambda bodies use `bvar i` directly; the context is a positional list (`BVarCtx = List LMonoTy`). No fresh names needed.
- **[`HasTypeGen.lean`](./StrataGenerators/HasTypeGen.lean)** — (**Outdated**) Generator of well-typed terms (using the locally-nameless representation) satisfying the `HasType` relation. Lambda bodies are built with free variables (`fvar`), then closed over with `varClose`. A monotonic counter supplies fresh binder names, and the soundness proof must establish freshness and the `varOpen`/`varClose` roundtrip.

`HasTypeAGen` targets `HasTypeA` (an annotated, de Bruijn typing relation). `HasTypeGen` targets the real `HasType` from `Strata.DL.Lambda.LExprTypeSpec` (locally-nameless, with polymorphic schemes instantiated via `tinst`).

A lightweight definitions-only module ([`HasTypeAGen/Defs.lean`](./StrataGenerators/HasTypeAGen/Defs.lean)) provides the generator functions without Mathlib dependencies, enabling coexistence with `Strata.DL.Lambda.LExprEval` (which would otherwise conflict via `List.Forall₂`).

## STLC generator

[`StrataGenerators/STLC.lean`](./StrataGenerators/STLC.lean) contains a standalone STLC (simply-typed lambda calculus with naturals and addition) generator with full soundness and completeness proofs. Ported from the internal Basalt repo.

## Plausible integration

Basalt's [`PlausibleGen`](https://github.com/hgoldstein95/basalt/blob/main/Basalt/PlausibleGen.lean) module establishes `Plausible.Gen` as an instance of Basalt's `Gen` typeclass. This allows any generator written polymorphically over Basalt's `Gen` class to be instantiated at Plausible's `Gen` for executable property-based testing.

## Dependencies

- `Strata`
- `Basalt`
  - In order for GitHub Actions to function properly, this repo depends on Harry's public Basalt repo on GitHub, not the AWS-internal fork. As a result, the `SetGen` portions of our internal Basalt fork (which aren't in the public-facing repo) have been manually copied over to this repo.
- `Plausible` (transitively via Mathlib)

## Building

1. Run `lake update` to resolve dependencies.

2. Fetch prebuilt Mathlib build artifacts (avoids compiling Mathlib from scratch):
   ```bash
   lake exe cache get
   ```

3. Build:
   ```bash
   lake build
   ```

## Property-based testing

Run property-based tests against `LExpr.eval` using Plausible generators:

```bash
lake build test-lexpr
.lake/build/bin/test-lexpr [numTrials] [maxSize]
```

- `numTrials` (default: 1000) — number of random test cases per property
- `maxSize` (default: 100) — maximum size parameter for generation (controls expression depth)

The test executable checks seven properties:

| Property | Status | Description |
|----------|--------|-------------|
| `typecheck` | PASS | Generated expressions typecheck to the expected type |
| `preservation` | PASS | Types are preserved under `LExpr.eval` |
| `progress` | FALSIFIED | Eval makes progress or input is already a value |
| `normalization` | FALSIFIED | Evaluation produces a canonical value |
| `eval_idempotent` | PASS | `LExpr.eval` is idempotent |
| `eval_monotone` | PASS | `LExpr.eval` is monotonic in the amount of fuel (supplying more fuel to `LExpr.eval` should produce the same result) |
| `closedness_preservation` | PASS | Evaluation preserves whether a term is closed or not (i.e. no free variables are introduced during evaluation) |
| `size_non_increase` | PASS | `LExpr.size` does not increase after evaluation (no factory = no inlining, so every reduction eliminates structure) |

The `progress` and `normalization` properties are expected to find counterexamples:
`LExpr.eval` is a partial evaluator that gets stuck on quantifiers in condition
position (e.g. `if ∀x. e then ...`) and on equality of lambdas with non-identical
bodies (where `LExpr.eql` conservatively returns "inconclusive").

The generators are instantiated at `Plausible.Gen` (via Basalt's `PlausibleGen`), which
provides size-varying random generation — the size parameter increases across trials,
exercising both small and large expressions.

## Tyche Visualization

You can visualize the output distribution of the generators using
[Tyche](https://github.com/tyche-pbt/tyche-extension), a VS Code extension
for inspecting property-based testing generators.

### Tyche setup

Install the [Tyche extension](https://marketplace.visualstudio.com/items?itemName=hgoldstein95.tyche)
   in VS Code.

### Generating samples

Build and run the visualization executable:

```bash
lake build tyche-viz
.lake/build/bin/tyche-viz [numSamples] [outputPath]
```

- `numSamples` (default: 1000) — number of samples per generator
- `outputPath` (default: `tyche_output.jsonl`) — output file path

This saves the following data to the `.jsonl` file:

- Distribution of random types produced by `genLMonoTy` (Lambda monotypes)
- Distribution of terms produced by `genLExpr` (well-typed terms satisfying `HasTypeA`)
   - (features: depth, size, expr kind, type kind)
- Property: Terms generated by `genLExpr` actually typecheck with the expected type
- Property: Type preservation under evaluation (using Strata's `LExpr.eval`)

### Viewing results

Open VS Code, press `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS), run
`Tyche: Open`, and select the generated `.jsonl` file (e.g. the example `tyche_output.jsonl` file in this repo). Tyche will display
interactive histograms and distribution charts for each generator property.

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

## Documentation

Design notes and proof explanations live in [`docs/`](./docs/):

| File | Description |
|------|-------------|
| [`HasTypeAGen-docs.md`](./docs/HasTypeAGen-docs.md) | Architecture and proof structure of the `HasTypeA` generator (de Bruijn) |
| [`stlc-proof-explanation.md`](./docs/stlc-proof-explanation.md) | Proof explanation for the STLC generator |
| [`generator-distribution-analysis.md`](./docs/generator-distribution-analysis.md) | Analysis of the trivial-term bias in the LExpr generator and proposed `coin`-based fix |
| [`hastype-gen-plan.md`](./docs/hastype-gen-plan.md) | Design plan for the `HasType` generator (locally-nameless) |

## Module structure

```
StrataGenerators/
  HasTypeAGen.lean          -- HasTypeA generator + soundness/completeness proofs
  HasTypeAGen/Defs.lean     -- Generator definitions only (no Mathlib, for use with LExprEval)
  HasTypeGen.lean           -- HasType generator (locally-nameless)
  STLC.lean                 -- STLC generator + proofs (ported from internal Basalt)
  SetGen.lean               -- SetGen framework (vendored from Basalt)
  SetGen/                   -- SetGen internals
  Tyche.lean                -- Tyche visualization support
TycheMain.lean              -- Tyche visualization executable
PlausibleTestMain.lean      -- Property-based test executable (Plausible + LExpr.eval)
```