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

@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent"
    fun (gp : GenProgram) => myPass (myPass gp.prog) = myPass gp.prog
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
| `fun (gp : GenProgram) => …` | the check, a decidable `Prop`. **The annotation picks the generator.** |

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

## `Prop` or `Bool`

The check is a decidable `Prop`, and a `Bool`-valued predicate is accepted unchanged,
since `Bool` coerces to `Prop`. The difference is the failure message, because Plausible
reads the *shape* of the proposition:

| you write | a failing draw reports |
|---|---|
| `fun gp => sizeProgram gp.prog ≤ 2` | `issue: 3 ≤ 2 does not hold` |
| `fun gp => gp.prog.decls.length = 99` | `issue: 0 = 99 does not hold` |
| `fun gp => checkMine gp.prog` (a `Bool`) | `issue: false does not hold` |
| `fun gp => checkMine gp.prog` (an `abbrev … : Prop`, top level `=`) | `issue: ["f"] = [] does not hold` |
| `fun gp => checkMine gp.prog` (a `Prop`, top level `∀ x ∈ …`) | `issue: ⋯ does not hold` |

So state the claim inline as a `Prop` where its shape is an equality or an order. Reach
for a named `check*` predicate in a `*/TestSupport` module when the check is long, is
reused, is worth pinning with a `#guard`, or is shared with a bespoke Tyche panel — most
of this suite is in that position, which is why most of it returns `Bool`.

A `family` entry is scored exactly the same way, so this table applies there too.

### A named predicate that returns `Prop`

The last two rows are the same predicate, and they show that the two options above are
not the only ones: a named `check*` predicate can return `Prop` and keep the readable
counterexample. `StrataGenerators/MonomorphizeFns.lean` is the worked example. Three
things are needed, and none of them is guessable from the error you get without them.

**1. `abbrev`, not `def`.** Typeclass resolution unfolds reducible definitions only, so a
plain `def … : Prop` is opaque to it and the property fails to register:

```
failed to synthesize instance of type class
  DecidablePred fun gp => checkMine gp.prog
```

Note where that error lands: at the `TestDecl.property` call, not at the definition. The
definition compiles fine on its own, so a module can build green and still refuse to be
registered. `abbrev` (or `@[reducible] def`) fixes it.

**2. No `match` on a scrutinee that is not a constructor.** This is not decidable:

```lean
abbrev checkMine (p : Program) : Prop :=
  match runMyPass p with            -- stuck: `p` is a variable, so this cannot reduce
  | none => True
  | some p' => f p' = []
```

`DecidablePred` is `∀ x, Decidable (check x)`, elaborated with `x` a variable, so the
match never reduces and no instance exists. Write `∀ p' ∈ runMyPass p, f p' = []`
instead — bounded quantification over an `Option` is decidable — or project through
`Option.getD` / `Option.elim`, which is what the next point wants anyway.

**3. `abbrev` alone buys nothing; the *top level* has to be the equality.** This is the
trap, because it costs you the benefit silently rather than failing. `PrintableProp`
reads the outermost shape, and a bounded `∀` is not a shape it renders — so
`∀ p' ∈ runMyPass p, f p' = []` reports `issue: ⋯ does not hold`, exactly as a `Bool`
would. Push the `Option` handling into a total helper, using the *vacuous* value as the
default, so the `=` ends up on top:

```lean
def onOutput (p : Program) (dflt : α) (f : Program → α) : α :=
  ((runMyPass p).map f).getD dflt

abbrev checkMine (p : Program) : Prop := onOutput p [] f = []
```

Same meaning — a pass that raised a diagnostic still makes no claim — and now a failure
names what went wrong: `issue: ["f"] = [] does not hold`.

The same reasoning favours stating a claim as `namesOf x = []` rather than as
`List.all`, and as a length equality rather than through a `nodup` helper: in each case
the equality is what prints the offending value. A guard belongs on the left of a `→`
(`progTypeChecks p = true → …`) rather than inside a `||`, for the same reason.

One API edge: `TestDecl.witnesses` takes a `Bool`-valued `check`, so a `Prop`-valued
predicate needs `decide (…)` there. `TestDecl.property` and `family` take the `Prop`
directly.

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
lake exe write-test-imports
```

You never edit `StrataTests.lean` by hand. Forgetting is not silent: the driver
rewrites a stale root and asks to be re-run, and `#verify_test_root` in the root fails
the build. After *removing* a file you must regenerate before the build succeeds,
since the root still imports a module that no longer exists — Lake reports that as a
plain `bad import`, so run `lake exe write-test-imports` when you see it.

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

When a family shares an input type and differs only in the check, `family` names the type
once and pairs each name with its check in one reviewable line; `@[strata_properties]`
registers the list:

```lean
@[strata_properties]
def stmtTransforms : List TestDecl :=
  family GenStmts
    [ ("stmt: LoopElim preserves typeability", fun gs => checkLoopElimPreservesTyping gs.stmts),
      ("stmt: LoopElim eliminates all loops",  fun gs => checkLoopElimZeroLoops gs.stmts) ]
```

Naming the type in the `family GenStmts` position is what lets the entries drop their
binder annotations.

`family` is a macro, and that is deliberate. A function would receive the entries as one
list, and the `Decidable`/`Testable` instances a check needs are resolved *per check*, at
the site where the check is written — which a list handed to a function does not provide.
The macro expands each entry to its own `TestDecl.property`, so an entry is a decidable
`Prop` and reports a failure as precisely as a standalone property does. A function
`family` could only take the decided form, and every entry would report
`issue: false does not hold`.

For a family whose entries want an explicit `PropertyRunner`, write the list out with
`TestDecl.forAll` instead; there is no `familyOf`.

Prefer `@[strata_property]` for a standalone property, so its name is greppable from
its own declaration.

## A property that is known to fail

Sometimes the property is right and Strata is wrong. Marking it as a known failure keeps
it in the suite — watching the defect, ready to report the fix — without holding a merge
hostage to a bug that is already reported:

```lean
@[strata_property]
def myPassOutputTypechecks : TestDecl :=
  knownFailure "strata-org/Strata#123: the pass drops a type annotation on a nested call" <|
    TestDecl.property "mypass: the output typechecks"
      fun (gp : GenProgram) => checkMyPassOutputTypechecks gp.prog
```

`knownFailure` is a prefix rather than a method, so the mark is the first thing you read
and the property needs no parentheses around it.

A marked property prints `? XFAIL`, its counterexample is suppressed, and it does not
gate the exit code. **If it ever passes, the run fails** and tells you to drop the mark —
so a fixed defect cannot go unnoticed, which is the whole reason to mark a property
rather than delete or comment it out.

Inside a `family`, give the `Expectation` as a third component of the entry instead. A
prefix cannot address one entry of a list, and lifting the member out would cost the
family its shape — so the member stays where its neighbours can be read in order:

```lean
      ("lift: the minted snapshot names are fresh",
       fun gp => checkLiftFreshSnapshotNames gp.prog,
       .knownFailure "reported upstream: `StringGenState.gen` is a bare counter, so a \
minted snapshot name can collide with a name already in the program"),
```

Put the upstream issue in the reason. It replaces the counterexample on the report line,
so it is the only explanation a reader gets for why a red property reads as green.

### When not to mark

`knownFailure` says the property fails on *every* run at the default trial count. Do not
use it for a property that fails only on an occasional draw: such a property passes on
most runs, so the mark reports "expected to fail, but passed" and turns the suite red on
exactly the runs that went well.

Leave that property unmarked, and pin the defect with a `#guard` on a hand-built witness
instead. `adt: no datatype derives the same function name twice` is the example in the
tree — it needs two field names differing by a trailing `!`, which a draw almost never
produces, so `AdtLaws.bangFieldWitness` is the real pin and the property is a net around
it.

### Marking one for a single run

```bash
lake test -- --known-failure="mypass: the output typechecks" --quick
```

Repeatable, and it takes a **whole property name** rather than a substring — unlike
`--only=`, since a substring would claim that every property in a group must fail, and
the ones that hold would then be reported as failures. A name matching nothing is an
error rather than a silent no-op. Use this while triaging; use `knownFailure` for what
gets committed, since only the declaration can carry a reason.

`--list` prints every mark and its reason, so the registry is the answer to "what is
known to fail?".

## Tyche panels

A registered property gets a panel automatically, built from its `PropertyRunner` —
which for almost every property is the one its input type's instances induce — and from
the check's `Decidable` instance, since a panel must classify every sample: `Repr` draws the sample, `TycheFeatures` gives the axes, the verdict is the
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
| `--list` | print the registry, with each property's expectation, and exit. The answer to "did my property get picked up?" |
| `--known-failure=NAME` | treat the property called `NAME` as known to fail for this run. Repeatable; whole name, not a substring. |
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
| `LSpecTestRunner.lean` | the driver `lake test` runs, rendering through LSpec |
| `PlainTestRunner.lean` | the same registry, LSpec-free; kept as a backup |
| `StrataGenerators/Test/Driver.lean` | everything both drivers do except the rendering |
