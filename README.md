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

- `--quick` gives a fast preset for a short cycle of work. It selects 100 trials, a
  maximum size of 40, and no Tyche pass. A measurement gives about 16 seconds for
  the preset, against about 7 minutes for the default settings. Use `--quick` to
  find a defect, and use the default settings to gate a merge.

  A positional argument has a higher precedence than `--quick`. Therefore
  `--quick 500` gives 500 trials, and it keeps the other two parts of the preset.
  To get the Tyche pass together with the other parts of the preset, give the
  trials and the size as positional arguments and do not use `--quick`.
- `--no-tyche` — omit Tyche visualizations (i.e. only run tests)
- `--tyche-out=PATH` — output filepath for JSON files storing test metadata which is ingested by Tyche (this defaults to `tyche_output.jsonl`)
- `--tyche-samples=N` — no. of test samples visualized per Tyche panel (default 1000)
- `--smt` — Tests properties related to Strata SMT encodings. This CLI flag requires a local installation of an SMT solver (cvc5/z3). 
  If `--smt` is passed but the SMT solver cannot be run, the test harness emits an error and exits with a non-zero exit code.

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

It accepts the same positional args and the `--smt` and `--quick` flags, reports the same pass/fail
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
   one of `expr` / `cmd` / `function` / `stmt` / `proc` / `program` / `phase` /
   `printer` / `adt` / `alias` / `mutual`), then add the constant to
   `PropertyNames.all` — the `#guard` there enforces that no two properties share
   a name.

3. **Pair name ↔ check (when both harnesses run the identical `Bool` check).**
   If the LSpec assertion and the Tyche panel run a byte-identical predicate, add
   a `Property` bundle entry to the appropriate list in the `Properties`
   namespace (`cmdSingleVerdict`, `stmtTransforms`, `procTransforms`,
   `adtBlockChecks`, `mutualIndepChecks`, or `aliasChecks`). Each
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
   `PropertyNames.*` constant so the LSpec result and the panel share a label, and
   scoring the sample with the same `check*` predicate so the two views cannot
   disagree. See [Adding a panel for a new
   property](#adding-a-panel-for-a-new-property) for the walkthrough.

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

The Tyche pass is the larger part of the time of a run. `--no-tyche` and
`--quick` both hold it off, and **neither writes the JSONL file** — so a file left
at `--tyche-out` by an earlier run stays there, and opening it shows that older
run's panels with no indication they are stale. To get `--quick`'s trials and size
*with* panels, pass them positionally instead of using the flag:

```bash
.lake/build/bin/test 100 40 --tyche-samples=200
```

### Viewing results

Open VS Code, press `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS), run
`Tyche: Open`, and select the generated `.jsonl` file. Tyche displays
interactive histograms and distribution charts for each property.

### Adding a panel for a new property

Every panel lives in
[`TycheViz.lean`](./StrataGenerators/TycheViz.lean) — one per property — and
`runTychePanels` writes them all into a single JSONL handle after the LSpec suite.
Adding one is four steps. (This assumes the property itself already exists; see
[Adding a new property](#adding-a-new-property) for that half, and note the panel
must *reuse* that property's `check*` predicate rather than restate it.)

#### 1. Define the sample type

A structure holding the generated value plus anything the features need that
cannot be recomputed purely. `TycheSample.toSample` is a **pure** function, so
any `IO` fact — a parse attempt, a solver call — has to be computed in the
generator and stored:

```lean
structure MyPropResult where
  value   : MyThing
  passed  : Bool          -- from the shared `check*`, see below
  genSize : Nat           -- the generator size this was drawn at
```

If several properties share a sample shape, give the structure a `tag` field and
let the panel title distinguish them — `StmtPropResult` and `ProcPropResult` do
this, using the tag as the name of the pass/fail feature.

#### 2. Implement `Tyche.TycheSample`

```lean
instance : Tyche.TycheSample MyPropResult where
  toSample r :=
    { representation := formatMyThing r.value              -- a reproducer
      status         := if r.passed then .passed else .failed
      statusReason   := if r.passed then "" else explainFailure r.value
      features := [
        ("verdict", .nominal (if r.passed then "pass" else "fail")),
        ("cause",   .nominal (classifyCause r.value)),     -- *why* it is red
        ("size",    .ordinal (sizeOf r.value)) ] }
```

- **`representation`** — prefer Strata's own printer (`Core.formatProgram`,
  `formatStmts`, `formatFunc`), so a mark is text you can paste back into a file
  and re-run. `stmtRepr` / `procsRepr` are the in-repo helpers for this.
- **`status`** — must be the shared `check*` predicate from the relevant
  `*.TestSupport` module: the *same function* the Plausible harness asserts.
  Re-deriving a verdict here is the one thing that breaks the invariant that a
  panel and its `checkIO` counterpart always agree, and it breaks it silently.
- **`statusReason`** — Tyche shows it on the mark; put the one-line "why" there
  (the offending codepoints, the parser's error, the phases that lied).
- **`features`** — `.nominal` for grouping, `.ordinal` / `.continuous` for
  distributions. Include at least one feature that explains why a mark is red
  (`rejection_cause`, `measure_no_body`, `violating_phases`, `error_sites` are the
  existing ones), and give **vacuous** samples an explicit `"—"` rather than
  scoring them as passes — a property that holds trivially on most draws should
  look different from one that holds substantively.

#### 3. Write the generator wrapper

An `IO MyPropResult`. Reuse an existing draw (`genStmtsForTyche`,
`genProcsForTyche`, `genProgramForTyche`) rather than a fresh generator call, so
the panel samples the same distribution as its neighbours, and vary the generator
size per sample. If the property's counterexamples are shrinkable, minimize on
failure and recompute the features from the minimized value, so they describe what
is actually displayed:

```lean
def genMyProp (check : MyThing → Bool) : IO MyPropResult := do
  let (x, genSize) ← genMyThingForTyche
  if check x then
    return { value := x, passed := true, genSize }
  else
    -- `minimizeProcsCounterexample` / `minimizeProgramCounterexample` keep every
    -- candidate well-typed *and* still-failing, so the verdict is unchanged.
    return { value := minimizeMyCounterexample check 200 x, passed := false, genSize }
```

#### 4. Register it in `runTychePanels`

```lean
panel PropertyNames.myProperty (genMyProp myCheck)
```

If the property belongs to a shared `Property` bundle in
[`Properties.lean`](./StrataGenerators/Properties.lean), iterate the bundle
instead, so name↔check stays paired in exactly one place:

```lean
for p in Properties.stmtTransforms do
  panel p.name (genStmtProp p.name p.check)
```

`panel` defaults to `--tyche-samples` marks; pass `(count := n)` to override.

#### Fixed finite input spaces: `enumerate`, not `panel`

A property whose input space is a fixed finite set rather than a distribution — a
constructed witness, the registered bitvector widths, the eighteen `Bv↔Int`
operators — uses `enumerate` (`Tyche.writeInto`) instead of `panel`
(`Tyche.runInto`). It emits one mark per element, once, because sampling a
constant space just repeats the same few marks `--tyche-samples` times:

```lean
enumerate PropertyNames.printerBvIntConversions bvIntConversionSamples
```

Score each element with the shared **per-element** check whose conjunction *is*
the property (`checkBvIntConversionPrints` vs `checkBvIntConversionsPrint`), so
the panel and the Plausible verdict still come from one function — and so the
panel shows the *shape* of a gap where the property's single `Bool` can only
report that a gap exists.

#### When the failure cause is not in the value

Some properties fail for a reason the generated value does not contain — the
shrinker then minimizes to an empty program, which is an honest witness but a mute
one. Those panels append a rendered diagnostic to `representation` and record its
counts as extra features: see `procFactoryStrippedDiagnostic` (factory entries
retaining preconditions) and `phaseChangedFlagDiagnostic` (which pipeline phase
misreported its `changed` flag). If a red mark would otherwise show nothing but
`program Core;`, this is the pattern to follow.

#### Checking that the panel actually appears

`--quick` and `--no-tyche` write **no file**, so verify with a run that does:

```bash
lake build test
.lake/build/bin/test 100 40 --tyche-samples=200
python3 -c "
import json, collections
c = collections.Counter(json.loads(l)['property'] for l in open('tyche_output.jsonl'))
print(len(c), 'panels'); [print(f'{n:5d}  {p}') for p, n in c.items()]
"
```

Then open it: `Ctrl+Shift+P` → `Tyche: Open`. The extension groups by property and
keeps the latest `run_start` per property, with no minimum-sample filter, so even a
one-mark panel is listed.

#### One-off panels outside the suite

To explore a single generator without adding it to the suite, implement
`TycheSample` as above and call `Tyche.run` with your `IO` action and a
`Tyche.Config` — it writes its own standalone JSONL file rather than joining
`runTychePanels`' shared one.

## License

The contents of this repository are licensed under the terms of either
the Apache-2.0 or MIT license, at your choice. See
[LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for
details of the two licenses.
