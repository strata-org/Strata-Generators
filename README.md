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
- `--smt` — add the SMT/concrete-eval agreement property (off by default). This
  property cross-checks the in-Lean evaluator against an SMT semantics, so it
  needs a live solver (default `cvc5`; `z3` also works) on `PATH`; it is excluded
  from the default run and CI for that reason. If `--smt` is passed but the solver
  cannot be launched, the driver prints an error and exits non-zero rather than
  silently reporting a green "0 checked" suite.

See [`Properties.lean`](./StrataGenerators/Properties.lean) for the full list of properties tested.

### LSpec-free harness (`test-plain`)

There is a second test executable, `test-plain`, that runs the exact same
properties without depending on LSpec, to evaluate whether the LSpec dependency
could be dropped. It shares all its properties, generators, and CLI with the
LSpec driver via [`TestScaffold.lean`](./StrataGenerators/TestScaffold.lean), and
runs them through a small Plausible-only harness
([`PlainHarness.lean`](./StrataGenerators/PlainHarness.lean)) instead of LSpec:

```bash
lake build test-plain
.lake/build/bin/test-plain [numTrials] [maxSize] [--smt]
```

It accepts the same positional args and `--smt` flag, reports the same pass/fail
verdicts and exit code as `test`, and prints a simpler `PASS/FAIL (n/m)` line per
property. It has no Tyche pass (the `--tyche-*` flags are accepted but ignored),
and it is **not** registered as the `lake test` driver — `test` (LSpec) remains
the driver.

## Adding a new property

Properties are catalogued in
[`Properties.lean`](./StrataGenerators/Properties.lean) and run from the single
test driver [`TestMain.lean`](./TestMain.lean). The name and the pass/fail check
are kept separate so the LSpec assertion and the Tyche panel for a property can
never drift apart. To add one:

1. **Write the check.** Put the decision procedure — a `check* : α → Bool` on
   whatever the generator produces (`LExpr'`, `Cmd Expression`, `List Statement`,
   `Function`, `List Procedure`, …) — in the relevant `*.TestSupport` module (e.g.
   `HasTypeAGen/TestSupport.lean`, `CmdHasTypeAGen/TestSupport.lean`,
   `StmtHasTypeAGen/TestSupport.lean`, `ProcedureHasTypeAGen/TestSupport.lean`).
   Keeping the check there means both the LSpec suite and the Tyche panel evaluate
   the *same* function.

2. **Name it.** Add a `String` constant to the matching `PropertyNames.*` group
   in `Properties.lean` (naming scheme: `"area: description"`, where `area` is
   one of `expr` / `cmd` / `function` / `stmt` / `proc`), then add the constant to
   `PropertyNames.all` — the `#guard` there enforces that no two properties share
   a name.

3. **Pair name ↔ check (when both harnesses run the identical `Bool` check).**
   If the LSpec assertion and the Tyche panel run a byte-identical predicate, add
   a `Property` bundle entry to the appropriate list in the `Properties`
   namespace (`cmdSingleVerdict`, `stmtTransforms`, or `procTransforms`). Each
   harness iterates that list, so the pairing is defined exactly once. Properties
   whose two views genuinely differ (or that only one harness runs) keep just the
   shared *name* here and state their logic in `TestMain.lean`.

4. **Add it to the suite in `TestMain.lean`.**
   - For a pure `α → Bool` property, wrap it as a `Prop` (`prop_* te := check* … = true`)
     and add a `checkIO PropertyNames.yourName (∀ x, prop_your x)` node to the
     relevant `*Suite`. Properties from a `Property` bundle are folded in
     automatically via `foldr` over the bundle list.
   - For an `IO`-based check (one that runs in `IO`, shrinks its own
     counterexamples, or needs an external tool), give it the
     `(success, passed, attempted, errorMsg)` shape and add it as a
     `.individualIO PropertyNames.yourName none action .done` node. The
     SMT/concrete-eval agreement property
     ([`HasTypeAGen/SmtEval.lean`](./StrataGenerators/HasTypeAGen/SmtEval.lean),
     gated behind `--smt`) is a worked example.

5. **(Optional) Add a Tyche panel** in
   [`TycheViz.lean`](./StrataGenerators/TycheViz.lean), referencing the same
   `PropertyNames.*` constant so the LSpec result and the panel share a label.

The exit code is the LSpec verdict, so any property added to a `*Suite` gates
`lake test`; always-run *diagnostics* (which report but don't gate) are called
after `lspecIO` in `main`.

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
