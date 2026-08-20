# Writing a property

A property goes in whatever file under `StrataTests/` you think it belongs in — an
existing one or a new one, one property or forty. You never edit a file in
`StrataGenerators/`.

## The short version

Add this to any file under `StrataTests/`, or create a new one:

```lean
import StrataGenerators.Test

open Core
open StrataGenerators.Test

/-- My pass does not change a program it has already changed. -/
def checkMyPassIdempotent (p : Core.Program) : Bool :=
  myPass (myPass p) == myPass p

@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent" fun (gp : GenProgram) => checkMyPassIdempotent gp.prog
```

Then:

```bash
lake test -- --list                     # confirm it was picked up
lake test -- --only="mypass:" --quick   # run just this group
lake test                               # run everything
```

`StrataTests/Example.lean` is a complete, working copy of this shape.

The two arguments to `TestDecl.property` are the whole interface:

| argument | meaning |
|---|---|
| `"mypass: the pass is idempotent"` | the name. Unique across the suite; it is the report line, the Tyche panel title, and — through its `mypass:` prefix — the report group. |
| `fun (gp : GenProgram) => …` | the check. **The annotation picks the generator.** |

There is no group argument. A report group is the `area` of an `area: description` name,
derived rather than declared, so it cannot disagree with the name. A prefix nothing has
used before simply creates a new group, and `--only="mypass:"` selects that group
exactly.

The generator is chosen the way Plausible and QuickCheck choose it — by the type of the
quantified value, not by naming a generator. `GenProgram` carries the
`Arbitrary`/`Repr`/`Shrinkable` instances Plausible needs, so annotating the binder
selects the whole-program generator, its renderer and its shrinker at once. Annotate
it: without the annotation Lean has no way to fix the type, and instance resolution
fails.

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
That last hop is the generated `StrataTests.lean` import root.

**Adding a property to an existing file needs nothing**: the import list does not
change. If you **add or remove a file** under `StrataTests/`, regenerate the root:

```bash
lake exe gen-test-root
```

You never edit `StrataTests.lean` by hand. Forgetting is not silent: the driver
rewrites a stale root and asks to be re-run, and `#verify_test_root` in the root fails
the build. After *removing* a file you must regenerate before the build succeeds,
since the root still imports a module that no longer exists — Lake reports that as a
plain `bad import`, so run `lake exe gen-test-root` when you see it.

Two properties may not share a name — the driver refuses to run and names the
duplicates, because two properties under one name would collapse their Tyche panels
and make a result line ambiguous.

## Choosing the input type

These are the types the package can generate. Annotate your binder with one of them:

| type | produces |
|---|---|
| `TypedExpr` | a well-typed expression with its type, over `defaultFCtx` |
| `ClosedTypedExpr` | the same, closed (no free variables) |
| `ResolveTypedExpr` | a closed expression over `coreOpCtx`, for erase/resolve round-trips |
| `GenCmdWithCtx` / `GenCmdsWithCtx` | one command, or a command sequence, with its contexts |
| `GenFunction` / `ClosedGenFunction` | a function, against `defaultFCtx` or closed |
| `GenStmts` | a well-typed statement list |
| `GenProcs` | a list of well-typed procedures forming an acyclic call DAG |
| `GenProgram` | a whole well-typed program: every declaration kind |
| `GenAdtBlock` / `GenIndepBlock` | a `mutual … end` datatype block, ordinary or pairwise independent |

Prefer the smallest shape that can state the claim: a smaller shape gives smaller
counterexamples and faster runs. Reach for `GenProgram` when the claim spans more than
one declaration — a pass that reads the axioms, or a body that calls a datatype's
derived functions, cannot be expressed on a statement list at all.

Note that the *distinctions* between these types are load-bearing, not cosmetic.
Progress and preservation are only true on `ClosedTypedExpr`; `GenIndepBlock` draws
blocks whose datatypes cannot mention one another. Picking the wrong one gives you a
property that fails for a reason unrelated to your claim.

### Making a new type generable

Give it the three instances Plausible asks for, plus the optional fourth:

```lean
instance : Arbitrary MyType := ⟨myGenerator⟩
instance : Repr MyType := ⟨fun x _ => myPrinter x⟩
instance : Shrinkable MyType := ⟨myShrinker⟩
instance : TycheFeatures MyType := ⟨myFeatures⟩
```

`property` then accepts `fun (x : MyType) => …` with nothing further declared. Two of
these are worth spending effort on:

* **`Shrinkable`** may be `⟨fun _ => []⟩`, but a property without a shrinker reports
  whatever raw draw first failed. If your candidates must satisfy an invariant to be
  meaningful (well-typedness, say), filter them inside `shrink` — the existing
  shrinkers all re-run Strata's own typechecker, so a reported counterexample is always
  a well-typed program.
* **`TycheFeatures`** is what tells a *vacuous* pass from a real one. A property about
  axioms is uninformative on a program that declares none, and the `decl_kinds` axis is
  what makes that visible in Tyche. Put facts about the *type* here; they are shared by
  every property over it.

### Deviating from the default

A `PropertyRunner` bundles the generator, the printer, the shrinker and the Tyche axes
for one input type. `TestDecl.property` builds it from the instances, so you never name
one — except for the rare property that wants something else. Then use `TestDecl.forAll`,
which is the explicit-generator sense of QuickCheck's `forAll`:

```lean
@[strata_property]
def myProp : TestDecl :=
  .forAll "proc: …"
    (Generators.procs.withRender fun gp => procsRepr gp.procs ++ myDiagnostic gp.procs)
    (fun gp => checkMine gp.procs)
```

`Generators.*` holds the default runner for each type above, so you rarely build one
from scratch. `PropertyRunner.ofInstances MyType` is that default; `withRender` and
`withFeatures` adjust it. Exactly one property in the suite needs this
(`proc: PrecondElim factory entries are stripped`, whose minimized witness is the empty
program, so its counterexample needs a diagnostic view instead).

## The other three shapes of property

`TestDecl.property` is the only entry point you need for a property that quantifies over
one generated value, which is nearly all of them. Three cases are not that.

### A single constructed witness

When the sharpest statement of a claim is one specific program or one operator,
sampling only obscures which case is at stake:

```lean
@[strata_property]
def bv128Prints : TestDecl :=
  .witness "printer: bitvec 128 literals are printable" checkBv128LiteralPrints
```

### A fixed finite input space

Scored element by element, and *enumerated* rather than sampled in Tyche — so the
panel shows the shape of the gap where a single `Bool` could only report that a gap
exists:

```lean
@[strata_property]
def allWidths : TestDecl :=
  .witnesses "printer: every typecheckable bitvec width is printable"
    (List.range 64) toString checkWidthPrints
```

### A self-driving `IO` action

For an oracle that is a subprocess, or one that must interleave its own diagnostics
with generation. It reports `(passed, samples, total, message)`:

```lean
@[strata_property]
def smtAgreement : TestDecl :=
  .action "expr: SMT/concrete eval agreement (closed)"
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
  family
    [ ("stmt: LoopElim preserves typeability",
       fun (gs : GenStmts) => checkLoopElimPreservesTyping gs.stmts),
      ("stmt: LoopElim eliminates all loops",
       fun gs => checkLoopElimZeroLoops gs.stmts) ]
```

The annotation on the first entry fixes the type for the whole list. `familyOf` is the
variant that names a `PropertyRunner` explicitly.

Prefer `@[strata_property]` for a standalone property, so its name is greppable from
its own declaration.

## Tyche panels

A registered property gets a panel automatically, built from its `PropertyRunner` —
which for almost every property is the one its input type's instances induce: `Repr` draws the sample, `TycheFeatures` gives the axes, the verdict is the
mark's status, and `Shrinkable` minimizes a failing sample before display. There is
nothing to register.

If your panel needs more than that — an `IO` oracle, or a breakdown of *why* a sample
failed that the input alone does not determine — attach your own writer, which then
lives next to the property rather than in a central list:

```lean
@[strata_property]
def myProp : TestDecl :=
  (TestDecl.property "mypass: …"
    (fun (gp : GenProgram) => checkMine gp.prog)).withPanel myPanelAction
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
| `--only=SUBSTRING` | run only properties whose name contains it. Repeatable. `--only="lift:"` selects the `lift` group. |
| `--list` | print the registry and exit. The answer to "did my property get picked up?" |
| `--smt` | enable the `smt` gate (needs `cvc5` or `z3` on `PATH`). |
| `--no-tyche` | skip the Tyche pass. |
| `--tyche-out=PATH` | Tyche JSONL output path (default `tyche_output.jsonl`). |
| `--tyche-samples=N` | samples per panel (default 1000). |

`--only=… --quick` is the loop to iterate in: it runs one property or one group, skips
the diagnostics, and writes no Tyche file.

Note that the suite is **not** seed-deterministic, and a few properties fail on
roughly one draw in several hundred. Never conclude anything from comparing one run to
one run.

## Where things live

| | |
|---|---|
| `StrataTests/*.lean` | the properties and diagnostics — the only place you add one |
| `StrataTests.lean` | generated import root; rewritten by `lake test` |
| `StrataGenerators/Test/Types.lean` | `TestDecl`, `PropertyRunner`, `Body`, and `runSampled` |
| `StrataGenerators/Test/Registry.lean` | the three attributes |
| `StrataGenerators/Test/Collect.lean` | `strata_registry%` / `strata_diagnostics%` |
| `StrataGenerators/Test/Generators.lean` | the `TycheFeatures` instances and the default `PropertyRunner`s |
| `StrataGenerators/Test/Report.lean` | grouping, printing, exit code |
| `StrataGenerators/Test/TycheReport.lean` | the derived panel |
| `StrataGenerators/Test/Cli.lean` | the flags |
| `StrataGenerators/TestScaffold.lean` | the wrapper types and their instances |
| `TestRunner.lean` | the driver `lake test` runs |
| `LSpecTestRunner.lean` | the same registry, rendered by LSpec |
