import StrataGenerators.TestScaffold
import StrataGenerators.TycheViz
import StrataGenerators.HasTypeAGen.SmtStringEscaping
import StrataGenerators.HasTypeAGen.DecimalAgreement
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
    -- always, and not under `--smt`.
    .individualIO PropertyNames.exprSmtStringEscaping none
      (StrataGenerators.SmtStringEscaping.escapingAction numTrials) .done ++
    -- Two unit properties about the `Rat`/`Decimal` boundary. Each needs no
    -- solver, because each states an invariant of a pure function in the SMT
    -- dialect.
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
    -- Function typechecker completeness — the function-level analogue of the
    -- statement `funcDecl` gap.
    checkIO PropertyNames.fnTypeCheckComplete
      (∀ gf : ClosedGenFunction, prop_function_typeCheck_complete gf) (cfg := cfg) $
    -- Every typeCheck rejection is a measure-without-body function (pins the gap).
    checkIO PropertyNames.fnRejectionOnlyMeasure
      (∀ gf : ClosedGenFunction, prop_function_rejection_only_measure gf) (cfg := cfg) $
    -- Property 2: pretty-print / parse round-trip (IO-based, shrinks + prints reproducers)
    .individualIO PropertyNames.fnRoundtrip none
      (roundtripFunctionAction numTrials maxSize) .done

  -- Statement-generator properties (transforms + typechecker). The six transform
  -- / typechecker properties are folded from the shared
  -- `Properties.stmtTransforms` bundle (name↔check paired in one place, also
  -- driving the Tyche panels), so their names can never be attached to the wrong
  -- check. Kleene definedness has a richer Tyche panel, so it is stated directly
  -- here.
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
  -- assembled from a generated procedure list and inspects the result.
  let procSuite : TestSeq :=
    Properties.procTransforms.foldr
      (fun p rest => checkIO p.name
        (∀ gp : GenProcs, p.check gp.procs = true) (cfg := cfg) rest)
      .done

  -- Whole-program-generator properties, folded from the shared
  -- `Properties.programChecks` and `Properties.programADTProps` bundles. Counterexamples are minimized by the
  -- whole-program shrinker (`Shrinkable GenProgram`), which keeps every candidate
  -- well-typed by re-running Strata's own `Program.typeCheck`. For
  -- `typechecker accepts generated programs`, each counterexample's `Repr` tags
  -- which of the classified rejection causes it hit, since those are precisely the
  -- programs the shrinker cannot minimize (its oracle is the checker under test).
  --
  -- `programADTProps` adds the four across-declaration checks that watch the
  -- ADT-derived-call path: a function/procedure body may call the constructors,
  -- testers and field accessors of a datatype declared *earlier* in the same
  -- program. Unlike the five conditional invariants above these are
  -- unconditional, so they stay non-vacuous on a gap-bearing draw.
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
  -- The first three pin the four hardcoded-`changed := true` sites
  -- (`FilterProcedures.lean`, `IrrelevantAxioms.lean`, and the two in
  -- `Verifier.lean`). `phase: non-hardcoded pipeline phases have a faithful changed
  -- flag` is the regression guard on the phases that compute the flag correctly
  -- today.
  let phaseSuite : TestSeq :=
    Properties.phaseNoOpWitnesses.foldr
      (fun (nameAndWitness : String × StrataGenerators.PhaseChangedFlag.NoOpWitness) rest =>
        test nameAndWitness.1 nameAndWitness.2.check rest)
      (Properties.phaseChangedFlags.foldr
        (fun p rest => checkIO p.name
          (∀ gp : GenProcs, p.check gp.procs = true) (cfg := cfg) rest)
        .done)

  -- Printer-expressiveness properties. The two targeted witnesses
  -- are closed `Bool`s (a `bitvec 128` literal; the eighteen `Bv↔Int` conversion
  -- operators), and the whole-program property quantifies over `GenProgram` — the
  -- same wrapper as `programSuite`, so its counterexamples shrink whenever the
  -- draw typechecks. The printer substitutes a placeholder and logs an error
  -- instead of failing, so an unprintable construct can round-trip as a *different*
  -- program. See `printerErrorDiagnostic` below for which constructs are
  -- responsible.
  let printerSuite : TestSeq :=
    Properties.printerWitnesses.foldr
      (fun (nameAndCheck : String × Bool) rest =>
        test nameAndCheck.1 nameAndCheck.2 rest)
      (checkIO PropertyNames.printerNoConversionError
        (∀ gp : GenProgram,
          StrataGenerators.PrinterCoverage.checkProgramPrintsWithoutError gp.prog = true)
        (cfg := cfg) .done)

  -- Properties for the eight Core transform passes that carry no correctness proof
  -- (`StructuredToUnstructured`, `LoopElim`,
  -- `InsertLoopInvariantAsserts`, `CommonSubexprElim`, `FunctionInlining`,
  -- `ProcedureInlining`, `IrrelevantAxioms`, plus the unproven postconditions of
  -- `NondetElim` and `LoopInitHoist`), folded from the shared
  -- `Properties.unprovenTransforms` bundle. Each runs its pass on a whole generated
  -- program — needed because three of the passes read a declaration other than a
  -- procedure — and counterexamples are minimized by the whole-program shrinker.
  --
  -- The three `procInline` properties are rare on generated input, so a short run
  -- may not reach them.
  --
  -- `CommonSubexprElim` fires on 0 of 200 generated programs, since no generated
  -- body holds a duplicated subexpression, so all four CSE properties are vacuous
  -- here and the `#guard`s in `ProgramGen/UnprovenTransforms` are what test them.
  --
  -- The last three (`loop:`/`nondetElim:`/`hoist: symbolic evaluation loses no
  -- obligation`) run each loop pass through `LoopElim`, because the evaluator
  -- refuses a loop, and then through Strata's symbolic evaluator. Each compares
  -- the obligations it emits against the same chain without the pass. All three
  -- are live on 390 of 400 draws, and they are what found the eighth defect, which
  -- is in the **evaluator** rather than in any pass: a nondeterministic guard
  -- is named after the current path-condition depth instead of by a counter, so a
  -- second `if *` at the same depth silently drops every obligation to the end of
  -- the procedure. It surfaced as obligations *reappearing* after `NondetElim`,
  -- which is why all three are stated as containment; the `#guard`s pin the defect
  -- itself.
  let unprovenSuite : TestSeq :=
    Properties.unprovenTransforms.foldr
      (fun p rest => checkIO p.name
        (∀ gp : GenProgram, p.check gp.prog = true) (cfg := cfg) rest)
      .done

  -- The thirteen properties for `LiftInternalFuncDecls`, the lambda
  -- lifting pass that hoists internal `funcDecl`s to closed top-level functions.
  -- Each injects a *capturing* internal function into the generated program — a
  -- generated `funcDecl` is always closed, since `genFuncDeclStmt` draws its bodies
  -- with `genFunction []`, so without the injection the pass has nothing to capture
  -- and every property would be vacuous — and sweeps the fifteen shapes of
  -- `LiftFuncDecls.allScenarios`.
  --
  -- `lift: the injected declaration is really lifted` is coverage, not a claim about
  -- the pass: it is what keeps the other twelve meaningful, since each of them skips
  -- a run the pass refused.
  let liftSuite : TestSeq :=
    Properties.liftFuncDecls.foldr
      (fun p rest => checkIO p.name
        (∀ gp : GenProgram, p.check gp.prog = true) (cfg := cfg) rest)
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
    ("lift", [liftSuite])
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
