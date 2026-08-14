import StrataGenerators.TestScaffold
import StrataGenerators.TycheViz
import StrataGenerators.HasTypeAGen.SmtStringEscaping
import StrataGenerators.HasTypeAGen.DecimalAgreement
import StrataGenerators.AdtLawsSmt
import LSpec

/-!
# Property-based tests using the Strata generators (LSpec driver)

The reference test driver for this package, registered as the `lake test`
driver. It exercises the expression, command, function, and statement generators
in *two* complementary ways from a single run:

1. **Plausible + LSpec** — each property is a `Bool` check asserted over many
   randomly-generated inputs; `LSpec.lspecIO` prints a per-suite `✓/×` summary and
   returns the exit code (`0` all-pass, `1` on any failure).
2. **Tyche visualization** — the same properties are sampled and written as Tyche
   JSONL panels for interactive exploration (see `StrataGenerators.TycheViz`).

Every property's *pass/fail decision* comes from a shared `check*` predicate in the
`*.TestSupport` modules, so the LSpec assertion and the Tyche panel for a given
property always agree; only the Tyche-specific visualization scaffolding (feature
breakdowns) lives separately.

All the properties, generators, IO checks, diagnostics, and the CLI parser are
defined in the harness-independent `StrataGenerators.TestScaffold`, shared with
the Plausible-only `PlainTestMain` so the two drivers cannot drift. This file adds
only the LSpec-specific `main` (the `checkIO`/`lspecIO` suite assembly).

## Usage

```bash
lake test -- [numTrials] [maxSize] [flags]
```

or, equivalently:

```bash
lake build test && .lake/build/bin/test [numTrials] [maxSize] [flags]
```

Positional arguments configure the Plausible run (`numTrials` = trials per
property, default 1000; `maxSize` = max generator size, default 100). Flags:

- `--quick` selects a fast preset: 100 trials, a maximum size of 40, and no Tyche
  pass. A positional argument has a higher precedence, so `--quick 500` gives 500
  trials and keeps the other two parts of the preset.
- `--no-tyche` — skip the Tyche visualization pass (it runs by default).
- `--tyche-out=PATH` — Tyche JSONL output path (default `tyche_output.jsonl`).
- `--tyche-samples=N` — samples per Tyche panel (default 1000).
- `--smt` — add the SMT/concrete-eval agreement property (off by default; needs
  a live `cvc5`/`z3` solver on `PATH`, so it is not part of the default run or CI).

The exit code is always the LSpec verdict; the Tyche pass never affects it.

## How the tests are run

The two format→parse round-trip checks are not plain `Prop`s: they run in `IO`,
shrink counterexamples, and print minimal reproducers. They are wrapped as
custom `TestSeq.individualIO` nodes so they join the same `lspecIO` suite.
-/

open Lambda RandomChoice ArbNat Basalt.PlausibleGen Plausible Core Imperative
open Strata Strata.CoreDDM
open StrataDDM (initDialect)
open LSpec (TestSeq checkIO lspecIO group test)

def main (args : List String) : IO UInt32 := do
  let cli := parseArgs args
  let numTrials := cli.numTrials
  let maxSize := cli.maxSize
  let cfg : Configuration := { numInst := numTrials, maxSize }

  -- `--smt` needs a live SMT solver on `PATH`. The agreement property runs each
  -- solver in `SmtEval.agreementSolvers`, so exit with an error only when it can
  -- launch none of them. Without this check the suite reports a green
  -- "0/0 checked". When only some solvers are absent, the property itself names
  -- them in its report, because each absent solver costs coverage: cvc5 and z3
  -- give different verdicts on a malformed string literal.
  if cli.smtEnabled then
    let available ← StrataGenerators.SmtEval.availableAgreementSolvers
    if available.isEmpty then
      IO.eprintln s!"error: --smt requires an SMT solver on PATH, but none of {String.intercalate ", " StrataGenerators.SmtEval.agreementSolvers} could be launched."
      IO.eprintln "Install one (e.g. cvc5 or z3) and ensure it is on PATH, or run without --smt."
      return 1
    let absent := StrataGenerators.SmtEval.agreementSolvers.filter (fun s => !available.contains s)
    unless absent.isEmpty do
      IO.eprintln s!"warning: --smt will skip these solvers (not on PATH): {String.intercalate ", " absent}"

  IO.println s!"Running property-based tests ({numTrials} trials, max size {maxSize})..."
  IO.println ""

  -- Expression-generator properties. The SMT/concrete-eval agreement check
  -- (`--smt`) is an IO-based `.individualIO` node — it runs the SMT solver per
  -- generated term rather than a pure `Prop` — and is appended only when the flag
  -- is set, since it needs a live `cvc5`/`z3` on `PATH` (see `SmtEval`).
  let exprSmtTail : TestSeq :=
    if cli.smtEnabled then
      .individualIO PropertyNames.exprSmtEvalAgreement none
        (StrataGenerators.SmtEval.smtEvalAgreementAction numTrials maxSize) .done
    else .done
  let exprSuite : TestSeq :=
    checkIO PropertyNames.exprTypecheck
      (∀ te : TypedExpr, prop_typecheck te) (cfg := cfg) $
    checkIO PropertyNames.exprPreservation
      (∀ te : ClosedTypedExpr, prop_preservation te) (cfg := cfg) $
    checkIO PropertyNames.exprProgress
      (∀ te : ClosedTypedExpr, prop_progress te) (cfg := cfg) $
    checkIO PropertyNames.exprFvarsPreserved
      (∀ te : TypedExpr, prop_closedness_preservation te) (cfg := cfg) $
    checkIO PropertyNames.exprResolveAfterErase
      (∀ te : ResolveTypedExpr, prop_resolve_after_erase te) (cfg := cfg) ++
    -- This property needs no solver, because its oracle is "printable ASCII",
    -- which is the requirement of SMT-LIB itself. Therefore it joins the suite
    -- always, and not under `--smt`. EXPECT IT TO FAIL until somebody corrects the
    -- SMT escape function.
    .individualIO PropertyNames.exprSmtStringEscaping none
      (StrataGenerators.SmtStringEscaping.escapingAction numTrials) .done ++
    -- Two unit properties about the `Rat`/`Decimal` boundary. Each needs no
    -- solver, because each states an invariant of a pure function in the SMT
    -- dialect. EXPECT BOTH TO FAIL until `Factory.eq` compares a real by value.
    .individualIO PropertyNames.realDecimalEqFold none
      (StrataGenerators.DecimalAgreement.eqFoldAction numTrials) .done ++
    .individualIO PropertyNames.realDecimalTrichotomy none
      (StrataGenerators.DecimalAgreement.trichotomyAction numTrials) .done ++
    exprSmtTail

  -- Command-generator properties. The four single-verdict properties are folded
  -- from the shared `Properties.cmdSingleVerdict` bundle (name↔check paired in one
  -- place, also driving the Tyche panels), so their names can never be attached to
  -- the wrong check. Context-growth and eval-agreement have distinct shapes and
  -- are stated directly.
  let cmdTail : TestSeq :=
    checkIO PropertyNames.cmdContextGrowth
      (∀ gc : GenCmdsWithCtx, prop_cmds_context_growth gc) (cfg := cfg) $
    checkIO PropertyNames.cmdEvalRunAgreement
      (∀ gc : GenCmdWithCtx, prop_cmd_eval_run_agreement gc) (cfg := cfg)
  let cmdSuite : TestSeq :=
    Properties.cmdSingleVerdict.foldr
      (fun p rest => checkIO p.name
        (∀ gc : GenCmdWithCtx, p.check (gc.cmd, gc.inCtx) = true) (cfg := cfg) rest)
      cmdTail

  -- Function-generator properties. The two format→parse round-trip checks below
  -- run in `IO` and shrink/print their own reproducers, so they join the suite as
  -- custom `TestSeq.individualIO` nodes rather than `checkIO` `Prop`s. The
  -- special-character probe is a diagnostic (see below) and is not part of this
  -- gating suite.
  let functionSuite : TestSeq :=
    checkIO PropertyNames.fnFvarsAnnotated
      (∀ gf : GenFunction, prop_function_fvars_annotated gf) (cfg := cfg) $
    -- Property 1: Function.typeCheck_annotated_sound
    checkIO PropertyNames.fnTypeCheckSound
      (∀ gf : ClosedGenFunction, prop_function_typeCheck_annotated_sound gf) (cfg := cfg) $
    -- Property 3: type preservation under evaluation (Step.type_preserved / StepStar.type_preserved)
    checkIO PropertyNames.fnBodyPreservation
      (∀ gf : ClosedGenFunction, prop_function_body_preservation gf) (cfg := cfg) $
    -- Function typechecker completeness. FAILS on the measure-without-body gap
    -- (spec permits it, algorithm rejects it) — the function-level analogue of the
    -- statement `funcDecl` gap (#1), asserted honestly as a real failure.
    checkIO PropertyNames.fnTypeCheckComplete
      (∀ gf : ClosedGenFunction, prop_function_typeCheck_complete gf) (cfg := cfg) $
    -- Every typeCheck rejection is a measure-without-body function (pins the gap).
    checkIO PropertyNames.fnRejectionOnlyMeasure
      (∀ gf : ClosedGenFunction, prop_function_rejection_only_measure gf) (cfg := cfg) $
    -- Property 2: pretty-print / parse round-trip (IO-based, shrinks + prints reproducers)
    .individualIO PropertyNames.fnRoundtrip none
      (roundtripFunctionAction numTrials maxSize) .done

  -- Statement-generator properties (transforms + typechecker). The six transform
  -- / typechecker properties (#1, #3, #4, #5a, #5b, #9) are folded from the shared
  -- `Properties.stmtTransforms` bundle (name↔check paired in one place, also
  -- driving the Tyche panels), so their names can never be attached to the wrong
  -- check. #1 FAILS honestly on the funcDecl gap (the spec's funcDecl rule is
  -- strictly more permissive than the algorithm) — a genuine spec/algorithm
  -- divergence surfaced as a real failure. #6 (Kleene definedness) has a richer
  -- Tyche panel, so it is stated directly here.
  let stmtSuite : TestSeq :=
    Properties.stmtTransforms.foldr
      (fun p rest => checkIO p.name
        (∀ gs : GenStmts, p.check gs.stmts = true) (cfg := cfg) rest)
      (checkIO PropertyNames.stmtKleeneDefinedIff
        (∀ gs : GenStmts, prop_stmt_kleene_defined_iff gs) (cfg := cfg))

  -- Procedure-generator ↔ transform-pass properties. The twenty-eight checks
  -- (seven FilterProcedures, thirteen PrecondElim, eight ANFEncoder — one per
  -- named field of the three `*PhaseCorrect` structures in
  -- `Strata/Transform/CustomSpecifications.lean`) are folded from the shared
  -- `Properties.procTransforms` bundle. Each runs its pass on the program
  -- assembled from a generated procedure list and inspects the result. Four checks
  -- FAIL honestly, pinning real defects rather than masking them (exactly like the
  -- statement `#1` and function-completeness gaps):
  -- `proc: FilterProcedures changed flag is faithful` (the pass hardcodes
  -- `changed := true` even when it removes nothing); `proc: PrecondElim changed
  -- flag is faithful` (the `.funcDecl` branch inserts a `$$wf` block for
  -- obligations in a declared function's body yet reports unchanged); `proc:
  -- PrecondElim factory entries are stripped` (the spec field is unsatisfiable for
  -- a run seeded with `Core.Factory`, whose partial builtins carry the very
  -- preconditions the pass exists to discharge); and `proc: PrecondElim factory
  -- strips declared functions` (the pass pushes each declared function into the
  -- factory *before* stripping its preconditions).
  let procSuite : TestSeq :=
    Properties.procTransforms.foldr
      (fun p rest => checkIO p.name
        (∀ gp : GenProcs, p.check gp.procs = true) (cfg := cfg) rest)
      .done

  -- Whole-program-generator properties, folded from the shared
  -- `Properties.programChecks` and `Properties.programADTProps` bundles. Counterexamples are minimized by the
  -- whole-program shrinker (`Shrinkable GenProgram`), which keeps every candidate
  -- well-typed by re-running Strata's own `Program.typeCheck`. Two checks FAIL
  -- honestly. `typechecker accepts generated programs` fails on either of two
  -- reachable rejection causes (one generator limitation, one genuine Strata gap —
  -- the third classified cause, `distinct-fvar`, is unreachable from `genProgram`);
  -- each counterexample's `Repr` tags which cause it hit, since those are
  -- precisely the programs the shrinker cannot minimize (its oracle is the checker
  -- under test). `typeCheck output re-typechecks` fails
  -- intermittently (~1 draw in 500) and its witness *does* shrink.
  --
  -- `programADTProps` adds the four across-declaration checks that watch the
  -- ADT-derived-call path: a function/procedure body may call the constructors,
  -- testers and field accessors of a datatype declared *earlier* in the same
  -- program. All four pass, and unlike the five conditional invariants above they
  -- are unconditional, so they stay non-vacuous on a gap-bearing draw.
  let programSuite : TestSeq :=
    (Properties.programChecks ++ Properties.programADTProps).foldr
      (fun p rest => checkIO p.name
        (∀ gp : GenProgram, p.check gp.prog = true) (cfg := cfg) rest)
      .done

  -- Pipeline-phase `changed`-flag properties. Two shapes:
  --
  --   * the two no-op witnesses, which take no generated input at all — each is a
  --     single constructed program on which the phase provably cannot change
  --     anything, so the check is a closed `Bool` asserted with `test`;
  --   * the two sweeps over generated procedure lists, folded like `procTransforms`.
  --
  -- Three of the four FAIL honestly, pinning the four hardcoded-`changed := true`
  -- sites (`FilterProcedures.lean:82`, `IrrelevantAxioms.lean:81`,
  -- `Verifier.lean:1510` and `:1517`). `phase: non-hardcoded pipeline phases have
  -- a faithful changed flag` is the one expected to PASS: it is the regression
  -- guard on the phases that compute the flag correctly today.
  let phaseSuite : TestSeq :=
    Properties.phaseNoOpWitnesses.foldr
      (fun (nameAndWitness : String × StrataGenerators.PhaseChangedFlag.NoOpWitness) rest =>
        test nameAndWitness.1 nameAndWitness.2.check rest)
      (Properties.phaseChangedFlags.foldr
        (fun p rest => checkIO p.name
          (∀ gp : GenProcs, p.check gp.procs = true) (cfg := cfg) rest)
        .done)

  -- Printer-expressiveness properties (#69 P2, #48). The two targeted witnesses
  -- are closed `Bool`s (a `bitvec 128` literal; the eighteen `Bv↔Int` conversion
  -- operators), and the whole-program property quantifies over `GenProgram` — the
  -- same wrapper as `programSuite`, so its counterexamples shrink whenever the
  -- draw typechecks. All three FAIL honestly: the printer substitutes a
  -- placeholder and logs an error instead of failing, so an unprintable construct
  -- can round-trip as a *different* program. See `printerErrorDiagnostic` below
  -- for which constructs are responsible.
  let printerSuite : TestSeq :=
    Properties.printerWitnesses.foldr
      (fun (nameAndCheck : String × Bool) rest =>
        test nameAndCheck.1 nameAndCheck.2 rest)
      (checkIO PropertyNames.printerNoConversionError
        (∀ gp : GenProgram,
          StrataGenerators.PrinterCoverage.checkProgramPrintsWithoutError gp.prog = true)
        (cfg := cfg) .done)

  -- Properties for the eight Core transform passes that carry no correctness proof
  -- (issue #69: `StructuredToUnstructured`, `LoopElim`,
  -- `InsertLoopInvariantAsserts`, `CommonSubexprElim`, `FunctionInlining`,
  -- `ProcedureInlining`, `IrrelevantAxioms`, plus the unproven postconditions of
  -- `NondetElim` and `LoopInitHoist`), folded from the shared
  -- `Properties.unprovenTransforms` bundle. Each runs its pass on a whole generated
  -- program — needed because three of the passes read a declaration other than a
  -- procedure — and counterexamples are minimized by the whole-program shrinker.
  --
  -- SEVERAL FAIL honestly. Four are the defects the bug report files
  -- (`docs/strata-unproven-transform-bugs.md`): `loop: LoopElim mints distinct block
  -- labels` (the pass puts one `loopElim_havoc_{n}` block statement into its output
  -- two times); `procInline: inlining introduces no duplicate label` (the wrapper
  -- label reaches no counter, and the label renaming sits inside the fold over
  -- `var_map`); `procInline: the output typechecks` (an `old x` expression is copied
  -- verbatim while `x` is renamed); and `procInline: symbolic evaluation loses no
  -- obligation` (the callee's `requires` is dropped — the unsound one, repo issue
  -- #107). The three `procInline` ones are rare on generated input, so a short run
  -- may show them green.
  --
  -- The two `s2u:` failures — `every block is reachable from the entry` and `a
  -- cfg-bodied procedure prints` — are expected red ticks that the report
  -- deliberately does NOT file as defects. Do not read them as findings.
  --
  -- `CommonSubexprElim` fires on 0 of 200 generated programs, since no generated
  -- body holds a duplicated subexpression, so all four CSE properties are vacuous
  -- here and the `#guard`s in `ProgramGen/UnprovenTransforms` are what test them.
  let unprovenSuite : TestSeq :=
    Properties.unprovenTransforms.foldr
      (fun p rest => checkIO p.name
        (∀ gp : GenProgram, p.check gp.prog = true) (cfg := cfg) rest)
      .done

  -- The two laws of an algebraic datatype (injectivity, disjointness). Three
  -- shapes:
  --
  --   * the two pure companions plus the eliminator-scoping property, folded from
  --     `Properties.adtBlockChecks` over ordinary generated blocks. Only the last
  --     FAILS, and it is a real defect: `elimFuncs` leaves another datatype's type
  --     parameters free in `d$Elim`'s type whenever the block's parameter lists
  --     differ (28 of 60 ordinary blocks);
  --   * the two solver-backed law properties, appended only under `--smt`, which
  --     share one run of the pipeline per block (one program yields the obligations
  --     of every family, so splitting them would double the solver work) and are
  --     tallied per family;
  --   * the unscreened query-acceptance property, also `--smt`, which FAILS on the
  --     two encoder defects (`bitvec 0`; a name that is not a bare SMT-LIB symbol).
  -- The law tallies are computed *before* the suite is assembled rather than inside
  -- the two nodes, because one run of the pipeline per block yields the obligations
  -- of every law family at once: computing them per node would run every solver
  -- query twice for identical coverage.
  let adtTallies ← if cli.smtEnabled then
      (StrataGenerators.AdtLawsSmt.runLawTallies numTrials
        StrataGenerators.SmtEval.solverName).map some
    else pure none
  let adtSmtTail : TestSeq :=
    match adtTallies with
    | none => .done
    | some (inj, disjT, _, notes) =>
      .individualIO PropertyNames.adtInjSmt none
        (pure (StrataGenerators.AdtLawsSmt.tallyToNode "injectivity" inj notes))
        (.individualIO PropertyNames.adtDisjSmt none
          (pure (StrataGenerators.AdtLawsSmt.tallyToNode
                   "disjointness (tester form)" disjT notes))
          (.individualIO PropertyNames.adtSolverAcceptsQuery none
            (StrataGenerators.AdtLawsSmt.adtSolverAcceptsQueryAction numTrials
              StrataGenerators.SmtEval.solverName)
            .done))
  let adtSuite : TestSeq :=
    Properties.adtBlockChecks.foldr
      (fun p rest => checkIO p.name
        (∀ gb : GenAdtBlock, p.check gb.block = true) (cfg := cfg) rest)
      adtSmtTail

  -- Eager versus incremental type-alias resolution. Same input shape as
  -- `programSuite`, so counterexamples go through the whole-program shrinker. Both
  -- pass; the work that makes them non-vacuous is `introduceAlias`, since a raw
  -- generated program never *uses* the aliases it declares.
  let aliasSuite : TestSeq :=
    Properties.aliasChecks.foldr
      (fun p rest => checkIO p.name
        (∀ gp : GenProgram, p.check gp.prog = true) (cfg := cfg) rest)
      .done

  -- `mutual … end` blocks whose datatypes are *not* mutually recursive: accepted,
  -- usable, interchangeable with the split form, and printable. All four pass —
  -- which is the answer to the question the suite was written to ask.
  let mutualSuite : TestSeq :=
    Properties.mutualIndepChecks.foldr
      (fun p rest => checkIO p.name
        (∀ gb : GenIndepBlock, p.check gb.block = true) (cfg := cfg) rest)
      .done

  let exitCode ← lspecIO (.ofList [
    ("expr", [exprSuite]),
    ("cmd", [cmdSuite]),
    ("function", [functionSuite]),
    ("stmt", [stmtSuite]),
    ("proc", [procSuite]),
    ("program", [programSuite]),
    ("phase", [phaseSuite]),
    ("printer", [printerSuite]),
    ("transforms", [unprovenSuite]),
    ("adt", [adtSuite]),
    ("alias", [aliasSuite]),
    ("mutual", [mutualSuite])
  ]) []

  -- Always-run diagnostics (do not gate the exit code):
  --
  -- Surface the actual `resolve` error messages behind any resolve-after-erase
  -- counterexamples. The standard Plausible failure output only shows one shrunk
  -- term; here we sample fresh terms and print the resolve errors verbatim so the
  -- failure mode (e.g. "Quantifier body has non-Boolean type") is visible.
  IO.println ""
  IO.println "Resolve-after-erase error diagnostics:"
  let _ ← printResolveErrors numTrials maxSize

  -- Special-character identifier probe: minimal reproducers per position, using
  -- legal identifiers that contain special (non-alphanumeric) characters
  -- (`genQuotedName`). Reported as a diagnostic (known limitation), not gated.
  IO.println ""
  IO.println "Special-character identifier round-trip diagnostics:"
  let (probeFail, probeOk) ← specialCharProbeDiagnostic numTrials maxSize
  if probeFail == 0 then
    IO.println s!"  PASS ({probeOk} ident/position round-trips)"
  else
    IO.println s!"  FOUND {probeFail} failing ident/position cases ({probeOk} ok) — see reproducers above"

  -- ADT-derived-call coverage: how often a generated body actually calls a
  -- constructor / tester / field accessor of an earlier datatype. A distribution,
  -- not an assertion, so it never gates the exit code — but a silent regression to
  -- zero is exactly the failure mode no passing property would catch.
  IO.println ""
  IO.println "Datatype-block coverage (adt: / mutual: suites):"
  printDatatypeBlockCoverage (min numTrials 40)

  IO.println ""
  IO.println "ADT-derived-function call coverage:"
  printDerivedCallCoverage (min numTrials 60) (min maxSize 20)

  -- Printer conversion-error tally: which constructs `Core.formatProgram` cannot
  -- express, most frequent first. This is the localisation behind the `printer:`
  -- suite — the gating property says *that* the printer failed, this says *what*
  -- it could not print. Not gated (the property above does the gating).
  IO.println ""
  IO.println "Printer conversion-error diagnostics:"
  let _ ← printerErrorDiagnostic numTrials maxSize

  -- Whole-program shrinker diagnostic. The program properties exercise the
  -- `Shrinkable GenProgram` instance only unreliably — the reliable failure is
  -- unshrinkable by construction, and the shrinkable one fires on ~1 draw in 500 —
  -- so without this the instance can go untouched for a whole run. Reports the
  -- reduction achieved and the two invariants (all emitted candidates well-typed;
  -- none stranding a `requires`). Diagnostic, not gated.
  IO.println ""
  IO.println "Whole-program shrinker diagnostics:"
  let (_, shrinkIllTyped, shrinkStranded) ← programShrinkDiagnostic numTrials
  if shrinkIllTyped == 0 && shrinkStranded == 0 then
    IO.println "    PASS (every candidate well-typed, no stranded `requires`)"
  else
    IO.println "    SHRINKER BUG — see counts above"

  -- Tyche visualization pass (on by default; disable with `--no-tyche`). Writes
  -- one JSONL panel per property to `cli.tycheOut`, using the *same* shared
  -- `check*` verdicts as the LSpec suite above. Never affects the exit code.
  if cli.tycheEnabled then
    IO.println ""
    IO.println s!"Generating Tyche visualizations ({cli.tycheSamples} samples/panel)..."
    let startTime ← IO.monoMsNow
    let handle ← IO.FS.Handle.mk cli.tycheOut .write
    runTychePanels handle cli.tycheSamples startTime
    IO.println s!"Tyche output written to {cli.tycheOut}"
    IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
  else
    IO.println ""
    -- Name the flag that actually held the pass off. `--quick` disables it too, and
    -- reporting `--no-tyche` for a `--quick` run sends you looking for a flag you
    -- did not pass — or, worse, at a stale `tycheOut` from an earlier run, since no
    -- file is written here at all.
    if args.contains "--quick" then
      IO.println s!"Tyche visualizations disabled (--quick); no file written, so {cli.tycheOut} — if it exists — is from an earlier run."
      IO.println "For the preset's trials/size *with* panels, pass them positionally instead: 100 40"
    else
      IO.println "Tyche visualizations disabled (--no-tyche)."

  return exitCode
