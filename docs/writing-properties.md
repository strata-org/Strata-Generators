# Writing a property

Everything about a property lives in one file that you create. You never edit a
file in `StrataGenerators/`.

## The short version

Create `StrataTests/MyPass.lean`:

```lean
import StrataGenerators.Test

open Core
open StrataGenerators.Test

/-- My pass does not change a program it has already changed. -/
def checkMyPassIdempotent (p : Core.Program) : Bool :=
  myPass (myPass p) == myPass p

@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent" "mypass" Gens.program checkMyPassIdempotent
```

Then:

```bash
lake test -- --list                    # confirm it was picked up
lake test -- --only=mypass --quick     # run just this one
lake test                              # run everything
```

`StrataTests/Example.lean` is a complete, working copy of this shape.

The four arguments to `TestDecl.property` are the whole interface:

| argument | meaning |
|---|---|
| `"mypass: the pass is idempotent"` | the property's name. Unique across the suite; it is the report label *and* the Tyche panel title. |
| `"mypass"` | the report group. A string nothing has seen before simply creates a new group. |
| `Gens.program` | the generator the input is drawn from. |
| `checkMyPassIdempotent` | the check: `α → Bool`, where `α` is what the generator produces. |

Naming convention: `area: description`, lower case, where `area` matches the report
group. A failing line then reads as a sentence.

## How it gets picked up

`@[strata_property]` records the declaration in an environment extension, and the
driver expands `strata_registry%` to the list of everything recorded in its imports.
That is the same mechanism Lake uses for `@[test_driver]`, and the same idea as
`ppx_quick_test`'s module-initialisation inventory or Rust `quickcheck`'s
`#[quickcheck]`.

Lean links statically, so a declaration is only *visible* to the driver if the driver
transitively imports the module it lives in — the analogue of `mod tests;` in Rust.
That last hop is the generated `StrataTests.lean` import root, which the `lake test`
script rewrites from the contents of `StrataTests/` before it builds. So dropping a
file into `StrataTests/` is enough; you never edit `StrataTests.lean` (and `lake run
testRoot` regenerates it on its own if you want to build without running).

Two properties may not share a name — the driver refuses to run and names the
duplicates, because two properties under one name would collapse their Tyche panels
and make a result line ambiguous.

## Choosing a generator

`StrataGenerators.Test.Gens` holds one entry per shape the package generates:

| generator | produces |
|---|---|
| `Gens.typedExpr` | a well-typed expression with its type, over `defaultFCtx` |
| `Gens.closedExpr` | the same, closed (no free variables) |
| `Gens.resolveExpr` | a closed expression over `coreOpCtx`, for erase/resolve round-trips |
| `Gens.cmd` / `Gens.cmds` | one command, or a command sequence, with its contexts |
| `Gens.function` / `Gens.closedFunction` | a function, against `defaultFCtx` or closed |
| `Gens.stmts` | a well-typed statement list |
| `Gens.procs` | a list of well-typed procedures forming an acyclic call DAG |
| `Gens.program` | a whole well-typed program: every declaration kind |
| `Gens.adtBlock` / `Gens.indepBlock` | a `mutual … end` datatype block, ordinary or pairwise independent |

Prefer the smallest shape that can state the claim: a smaller shape gives smaller
counterexamples and faster runs. Reach for `Gens.program` when the claim spans more
than one declaration — a pass that reads the axioms, or a body that calls a datatype's
derived functions, cannot be expressed on a statement list at all.

### Defining your own

A generator is a `GenSpec α`, and nothing in `Gens` is privileged — define one in
your own file if you need a shape the catalog does not have:

```lean
def myShape : GenSpec MyType :=
  { label := "my shape"
    gen := myGenerator          -- a `Plausible.Gen MyType`
    render := myPrinter         -- how a counterexample is displayed
    shrink := myShrinker        -- one-step reductions, smaller first
    features := myFeatures }    -- Tyche axes, computed from the input
```

If your type already has `Arbitrary`/`Repr`/`Shrinkable` instances, use
`GenSpec.ofInstances "my shape" MyType myFeatures` instead — that is what every entry
in `Gens` is.

Two fields are worth spending effort on:

* **`shrink`** costs you nothing if omitted, but a property without a shrinker reports
  whatever raw draw first failed. If your candidates must satisfy an invariant to be
  meaningful (well-typedness, say), filter them inside `shrink` — the existing
  shrinkers all re-run Strata's own typechecker, so a reported counterexample is
  always a well-typed program.
* **`features`** is what tells a *vacuous* pass from a real one. A property about
  axioms is uninformative on a program that declares none, and the `decl_kinds` axis is
  what makes that visible in Tyche. Put facts about the *input* here (it is shared by
  every property drawn from the generator), not facts about your claim.

## The other three shapes of property

Most properties are a `Bool` check over a generator. Three cases are not.

### A single constructed witness

When the sharpest statement of a claim is one specific program or one operator,
sampling only obscures which case is at stake:

```lean
@[strata_property]
def bv128Prints : TestDecl :=
  .witness "printer: bitvec 128 literals are printable" "printer" checkBv128LiteralPrints
```

### A fixed finite input space

Scored element by element, and *enumerated* rather than sampled in Tyche — so the
panel shows the shape of the gap where a single `Bool` could only report that a gap
exists:

```lean
@[strata_property]
def allWidths : TestDecl :=
  .witnesses "printer: every typecheckable bitvec width is printable" "printer"
    (List.range 64) toString checkWidthPrints
```

### A self-driving `IO` action

For an oracle that is a subprocess, or one that must interleave its own diagnostics
with generation. It reports `(passed, samples, total, message)`:

```lean
@[strata_property]
def smtAgreement : TestDecl :=
  .action "expr: SMT/concrete eval agreement (closed)" "expr"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.SmtEval.smtEvalAgreementAction cfg.numTrials cfg.maxSize)
    (gate := some "smt")
```

`gate := some "smt"` makes the property opt-in: it runs only under `--smt`, and is
otherwise reported as `SKIP` — never as a pass, so an absent solver cannot read as
green.

## Registering several at once

When a family shares one generator and differs only in the check, `family` pairs each
name with its check in one reviewable line, and `@[strata_properties]` registers the
list:

```lean
@[strata_properties]
def stmtTransforms : List TestDecl :=
  family "stmt" Gens.stmts
    [ ("stmt: LoopElim preserves typeability", fun gs => checkLoopElimPreservesTyping gs.stmts),
      ("stmt: LoopElim eliminates all loops",  fun gs => checkLoopElimZeroLoops gs.stmts) ]
```

Prefer `@[strata_property]` for a standalone property, so its name is greppable from
its own declaration.

## Tyche panels

A registered property gets a panel automatically, built from its `GenSpec`: the
renderer draws the sample, the features are the axes, the verdict is the mark's
status, and a failing sample is minimized with the shrinker before display. There is
nothing to register.

If your panel needs more than that — an `IO` oracle, or a breakdown of *why* a sample
failed that the input alone does not determine — attach your own writer, which then
lives next to the property rather than in a central list:

```lean
@[strata_property]
def myProp : TestDecl :=
  (TestDecl.property "mypass: …" "mypass" Gens.program checkMine).withPanel myPanelAction
```

`myPanelAction : IO β` for any `β` with a `Tyche.TycheSample` instance. The panel's
title comes from the property's own `name`, so the two cannot drift.

## Diagnostics

A measurement rather than a claim — a coverage statistic, a localisation tally — is a
`Diagnostic`. It prints and never affects the exit code, and is discovered the same
way:

```lean
@[strata_diagnostic]
def myCoverage : Diagnostic where
  name := "How often my pass actually fires:"
  run cfg := printMyCoverage (min cfg.numTrials 60)
```

Reach for this when the failure mode you are worried about is a *silent regression to
zero* — a property that stays green because nothing it cares about was ever generated.
No `True`-valued property catches that.

## Running

```bash
lake test -- [numTrials] [maxSize] [flags]
```

| flag | effect |
|---|---|
| `--quick` | 100 trials, max size 40, no Tyche pass. A positional argument wins, so `--quick 500` gives 500 trials and keeps the rest. |
| `--only=SUBSTRING` | run only properties whose name contains it. Repeatable. |
| `--suite=NAME` | run only the named report groups. Repeatable. |
| `--list` | print the registry and exit. The answer to "did my property get picked up?" |
| `--smt` | enable the `smt` gate (needs `cvc5` or `z3` on `PATH`). |
| `--no-tyche` | skip the Tyche pass. |
| `--tyche-out=PATH` | Tyche JSONL output path (default `tyche_output.jsonl`). |
| `--tyche-samples=N` | samples per panel (default 1000). |

`--only=… --quick` is the loop to iterate in: it runs one property, skips the
diagnostics, and writes no Tyche file.

Note that the suite is **not** seed-deterministic, and a few properties fail on
roughly one draw in several hundred. Never conclude anything from comparing one run to
one run.

## Where things live

| | |
|---|---|
| `StrataTests/*.lean` | the properties and diagnostics — the only place you add one |
| `StrataTests.lean` | generated import root; rewritten by `lake test` |
| `StrataGenerators/Test/Types.lean` | `TestDecl`, `GenSpec`, `Body`, and the runner |
| `StrataGenerators/Test/Registry.lean` | the three attributes |
| `StrataGenerators/Test/Collect.lean` | `strata_registry%` / `strata_diagnostics%` |
| `StrataGenerators/Test/Gens.lean` | the generator catalog and its Tyche axes |
| `StrataGenerators/Test/Report.lean` | grouping, printing, exit code |
| `StrataGenerators/Test/TycheReport.lean` | the derived panel |
| `StrataGenerators/Test/Cli.lean` | the flags |
| `StrataGenerators/TestScaffold.lean` | the wrapper types and their instances |
| `TestRunner.lean` | the driver `lake test` runs |
| `LSpecTestRunner.lean` | the same registry, rendered by LSpec |
