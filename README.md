# strata-generators

(Work in progress) Experiments with random generators for [Strata](https://github.com/strata-org/strata) via [Basalt](https://github.com/hgoldstein95/basalt).

## Well-typed generators

Two generators produce well-typed Strata `LExpr`s with proved soundness, using different variable representations:

- **[`HasTypeAGen.lean`](./StrataGenerators/HasTypeAGen.lean)** -- Generator of well-typed terms satisfying the `HasTypeA` relation, with soundness, completeness, and depth-bound proofs. Uses de Bruijn indices for bound variables and the locally-nameless representation for free variables (matching Strata's `LExpr`).
- **[`HasTypeGen.lean`](./StrataGenerators/HasTypeGen.lean)** -- (**Outdated**) Generator of well-typed terms satisfying the `HasType` relation. Uses a monotonic counter for fresh binder names and `varOpen`/`varClose` for the locally-nameless roundtrip.

### HasTypeAGen module structure

The `HasTypeAGen` generator is split across several files to work around an import conflict (`List.Forall2` is defined in both `Strata.DL.Util.List` and Batteries):

| File | Imports | Purpose |
|------|---------|---------|
| [`HasTypeAGen/Core.lean`](./StrataGenerators/HasTypeAGen/Core.lean) | `Basalt.Gen`, Strata (no Factory, no Mathlib) | Canonical definitions: `genLExpr`, `genLMonoTy`, helpers, types |
| [`HasTypeAGen/Defs.lean`](./StrataGenerators/HasTypeAGen/Defs.lean) | Core + `Strata.DL.Lambda.Factory` | `Factory`-accepting wrappers: `genLExprWithFactory`, `factoryOps` |
| [`HasTypeAGen/TestSupport.lean`](./StrataGenerators/HasTypeAGen/TestSupport.lean) | Defs + `LExprEval` + `IntBoolFactory` | Shared test utilities: `intBoolFactory`, `eval`, `isValue`, `defaultFCtx` |
| [`HasTypeAGen.lean`](./StrataGenerators/HasTypeAGen.lean) | Core + `SetGen` + Mathlib | Soundness, completeness, and `termDepth` bound proofs |

**Why the split**: `Factory` transitively imports `Strata.DL.Util.List` (which defines `List.Forall2`), conflicting with Batteries (imported via Mathlib). The proof file needs Mathlib tactics, so it cannot import `Factory`. The solution: `Core.lean` defines `genLExpr` taking a flat `OpCtx` (just a `List (String x LMonoTy)`), and `Defs.lean` provides `genLExprWithFactory` which converts a `Factory` to `OpCtx` via `factoryOps`.

### Key theorems

```lean
-- Soundness: generated terms are well-typed
theorem genLExpr_sound : e ∈ support (genLExpr ...) → HasTypeA' bctx e τ

-- Completeness: all well-typed terms within the depth budget are generated
theorem genLExpr_complete : HasTypeA' bctx e τ ∧ termDepth bctx e ≤ depth ∧ ... → e ∈ support (genLExpr ...)

-- Depth bound: generated terms never exceed the depth budget
theorem genLExpr_termDepth_bound : e ∈ support (genLExpr ...) → termDepth bctx e ≤ depth
```

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
   make build
   ```

### Makefile targets

| Target | Description |
|--------|-------------|
| `make build` | Build all Lean sources (`lake build`) |
| `make tyche` | Build and run the Tyche visualization executable |
| `make test` | Build and run the Plausible test suite |

## Property-based testing

Run property-based tests against `LExpr.eval` using Plausible generators:

```bash
lake build test-lexpr
.lake/build/bin/test-lexpr [numTrials] [maxSize]
```

- `numTrials` (default: 1000) -- number of random test cases per property
- `maxSize` (default: 100) -- maximum size parameter for generation (controls expression depth)

The test harness generates both **open terms** (with free variables from a fixed context: `x : bool`, `f : int -> bool`, `n : int`) and **closed terms** (no free variables), using operators from `IntBoolFactory` (integer arithmetic, comparisons, boolean logic).

| Property | Terms | Status | Description |
|----------|-------|--------|-------------|
| `typecheck` | open | PASS | Generated expressions typecheck to the expected type |
| `type_preservation` | closed | PASS | Types are preserved under `LExpr.eval` |
| `progress` | closed | FALSIFIED | Eval makes progress or input is already a value |
| `normalization` | closed | FALSIFIED | Evaluation produces a canonical value |
| `eval_idempotent` | open | PASS | `LExpr.eval` is idempotent |
| `eval_monotone` | open | PASS | `eval 100 e == eval 50 (eval 50 e)` |
| `closedness_preservation` | open | PASS | Eval does not introduce new free variables |
| `size_non_increase` | open | PASS | `LExpr.size` does not increase after evaluation |

Progress, preservation, and normalization use closed terms following the Software Foundations convention (these properties are stated for the empty typing context).

The `progress` and `normalization` properties are expected to find counterexamples: `LExpr.eval` gets stuck on quantifiers in condition position (e.g. `if (forall x. e) then ...`) and on equality of lambdas with non-identical bodies.

## Tyche Visualization

You can visualize the output distribution of the generators using [Tyche](https://github.com/tyche-pbt/tyche-extension), a VS Code extension for inspecting property-based testing generators.

### Generating samples

Build and run the visualization executable:

```bash
lake build tyche-viz
.lake/build/bin/tyche-viz [numSamples] [outputPath]
```

- `numSamples` (default: 1000) -- number of samples per generator
- `outputPath` (default: `tyche_output.jsonl`) -- output file path

The depth parameter is varied uniformly over [1, 5] across samples so that visualizations cover the full range of generator behavior. Each sample records `gen_depth` as a feature.

### Viewing results

Open VS Code, press `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS), run `Tyche: Open`, and select the generated `.jsonl` file. Tyche displays interactive histograms and distribution charts for each property.

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
| [`size-alignment-analysis.md`](./docs/size-alignment-analysis.md) | Analysis of the depth/size mismatch and the Option C fix that aligns soundness/completeness |
| [`HasTypeAGen-docs.md`](./docs/HasTypeAGen-docs.md) | Architecture and proof structure of the `HasTypeA` generator |
| [`stlc-proof-explanation.md`](./docs/stlc-proof-explanation.md) | Proof explanation for the STLC generator |
| [`generator-distribution-analysis.md`](./docs/generator-distribution-analysis.md) | Analysis of the trivial-term bias in the LExpr generator and proposed `coin`-based fix |
| [`llm_stlc_generator_synthesis.md`](./docs/llm_stlc_generator_synthesis.md) | Notes on using Kiro to synthesize a correct STLC generator |
| [`strata-import-collision.md`](./docs/strata-import-collision.md) | Details of the `List.Forall2` import conflict between Strata and Batteries |
| [`hastype-gen-plan.md`](./docs/hastype-gen-plan.md) | Design plan for the `HasType` generator (locally-nameless) |

## Module structure

```
StrataGenerators/
  HasTypeAGen.lean              -- Soundness/completeness/depth-bound proofs
  HasTypeAGen/
    Core.lean                   -- Definition of the `genLExpr` generator
    Defs.lean                   -- `genLExprWithFactory` (variant of the generator which takes in a Strata Lambda `Factory`)
    TestSupport.lean            -- Shared test utilities (eval, isValue, intBoolFactory)
  HasTypeGen.lean               -- HasType generator (locally-nameless, outdated)
  STLC.lean                     -- STLC generator + proofs
  SetGen.lean                   -- SetGen framework (vendored from Basalt)
  SetGen/                       -- SetGen internals
  Tyche.lean                    -- Tyche JSONL serialization support
TycheMain.lean                  -- Tyche visualization executable
PlausibleTestMain.lean          -- Property-based test executable
```
