import StrataGenerators.TestScaffold
import StrataGenerators.PlainHarness
import StrataGenerators.HasTypeAGen.SmtStringEscaping
import StrataGenerators.HasTypeAGen.DecimalAgreement

/-!
# Property-based tests using the Strata generators (LSpec-free driver)

A **second** test executable that reproduces the LSpec-based `TestMain` suite
*without depending on LSpec*, to evaluate whether the LSpec dependency could be
dropped in the future. The LSpec `test` executable remains the registered `lake
test` driver and the reference "nice harness"; this one is functionally
equivalent — same properties, same generators, same pass/fail verdicts, same
exit-code semantics — but its runner is the ~small Plausible-only reimplementation
in `StrataGenerators.PlainHarness` rather than `LSpec.checkIO`/`lspecIO`.

Both drivers import all their properties, generators, IO checks, diagnostics, and
the CLI parser from the shared `StrataGenerators.TestScaffold`, so they cannot
drift. The only differences here versus `TestMain`:

- the runner is `PlainHarness.runSuites` (not `lspecIO`);
- properties are `IO PlainHarness.Result` values (not `LSpec.TestSeq` nodes);
- there is **no Tyche pass** (that scaffolding is LSpec-independent but not part
  of the dependency-de-risking exercise; the `--no-tyche` / `--tyche-*` flags are
  still accepted and ignored, so the CLI is compatible).

The always-run diagnostics (resolve-after-erase errors, special-character probe)
run identically to `TestMain`, and — as there — never gate the exit code.

## Usage

```bash
lake build test-plain && .lake/build/bin/test-plain [numTrials] [maxSize] [flags]
```

Positional args and flags mirror `TestMain`. `--smt` adds the SMT/concrete-eval
agreement property, and it needs a live solver on `PATH`. `--quick` selects the
fast preset: 100 trials and a maximum size of 40. This executable is **not**
registered as the `lake test` driver — LSpec's `test` stays the driver for now.
-/

open Lambda RandomChoice ArbNat Basalt.PlausibleGen Plausible Core Imperative
open Strata Strata.CoreDDM
open StrataDDM (initDialect)
open StrataGenerators.PlainHarness

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
  -- give different verdicts on a malformed string literal. Mirrors `TestMain`.
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
  -- (`--smt`) is an IO-based property — it runs the SMT solver per generated term
  -- — and is appended only when the flag is set, since it needs a live
  -- `cvc5`/`z3` on `PATH` (see `SmtEval`).
  let exprSmtTail : List (IO Result) :=
    if cli.smtEnabled then
      [runIOProperty PropertyNames.exprSmtEvalAgreement
        (StrataGenerators.SmtEval.smtEvalAgreementAction numTrials maxSize)]
    else []
  let exprSuite : List (IO Result) :=
    [ runProperty PropertyNames.exprTypecheck
        (∀ te : TypedExpr, prop_typecheck te) cfg,
      runProperty PropertyNames.exprPreservation
        (∀ te : ClosedTypedExpr, prop_preservation te) cfg,
      runProperty PropertyNames.exprProgress
        (∀ te : ClosedTypedExpr, prop_progress te) cfg,
      runProperty PropertyNames.exprFvarsPreserved
        (∀ te : TypedExpr, prop_closedness_preservation te) cfg,
      runProperty PropertyNames.exprResolveAfterErase
        (∀ te : ResolveTypedExpr, prop_resolve_after_erase te) cfg,
      -- This property needs no solver, because its oracle is "printable ASCII",
      -- which is the requirement of SMT-LIB itself. Therefore it runs always, and
      -- not under `--smt`. EXPECT IT TO FAIL until somebody corrects the SMT
      -- escape function.
      runIOProperty PropertyNames.exprSmtStringEscaping
        (StrataGenerators.SmtStringEscaping.escapingAction numTrials),
      -- Two unit properties about the `Rat`/`Decimal` boundary. Each needs no
      -- solver, because each states an invariant of a pure function in the SMT
      -- dialect. EXPECT BOTH TO FAIL until `Factory.eq` compares a real by value.
      runIOProperty PropertyNames.realDecimalEqFold
        (StrataGenerators.DecimalAgreement.eqFoldAction numTrials),
      runIOProperty PropertyNames.realDecimalTrichotomy
        (StrataGenerators.DecimalAgreement.trichotomyAction numTrials)
    ] ++ exprSmtTail

  -- Command-generator properties. The four single-verdict properties are folded
  -- from the shared `Properties.cmdSingleVerdict` bundle (name↔check paired in one
  -- place), so their names can never be attached to the wrong check.
  -- Context-growth and eval-agreement have distinct shapes and are stated
  -- directly.
  let cmdTail : List (IO Result) :=
    [ runProperty PropertyNames.cmdContextGrowth
        (∀ gc : GenCmdsWithCtx, prop_cmds_context_growth gc) cfg,
      runProperty PropertyNames.cmdEvalRunAgreement
        (∀ gc : GenCmdWithCtx, prop_cmd_eval_run_agreement gc) cfg ]
  let cmdSuite : List (IO Result) :=
    Properties.cmdSingleVerdict.map
      (fun p => runProperty p.name
        (∀ gc : GenCmdWithCtx, p.check (gc.cmd, gc.inCtx) = true) cfg)
    ++ cmdTail

  -- Function-generator properties. The format→parse round-trip check runs in `IO`
  -- and shrinks/prints its own reproducers, so it joins the suite as a
  -- `runIOProperty` rather than a `runProperty` `Prop`. The special-character
  -- probe is a diagnostic (see below) and is not part of this gating suite.
  let functionSuite : List (IO Result) :=
    [ runProperty PropertyNames.fnFvarsAnnotated
        (∀ gf : GenFunction, prop_function_fvars_annotated gf) cfg,
      -- Property 1: Function.typeCheck_annotated_sound
      runProperty PropertyNames.fnTypeCheckSound
        (∀ gf : ClosedGenFunction, prop_function_typeCheck_annotated_sound gf) cfg,
      -- Property 3: type preservation under evaluation
      runProperty PropertyNames.fnBodyPreservation
        (∀ gf : ClosedGenFunction, prop_function_body_preservation gf) cfg,
      -- Function typechecker completeness. FAILS on the measure-without-body gap
      -- (spec permits it, algorithm rejects it), asserted honestly as a real failure.
      runProperty PropertyNames.fnTypeCheckComplete
        (∀ gf : ClosedGenFunction, prop_function_typeCheck_complete gf) cfg,
      -- Every typeCheck rejection is a measure-without-body function (pins the gap).
      runProperty PropertyNames.fnRejectionOnlyMeasure
        (∀ gf : ClosedGenFunction, prop_function_rejection_only_measure gf) cfg,
      -- Property 2: pretty-print / parse round-trip (IO-based, shrinks + prints reproducers)
      runIOProperty PropertyNames.fnRoundtrip
        (roundtripFunctionAction numTrials maxSize) ]

  -- Statement-generator properties (transforms + typechecker). The six transform
  -- / typechecker properties (#1, #3, #4, #5a, #5b, #9) are folded from the shared
  -- `Properties.stmtTransforms` bundle. #1 FAILS honestly on the funcDecl gap. #6
  -- (Kleene definedness) is stated directly.
  let stmtSuite : List (IO Result) :=
    Properties.stmtTransforms.map
      (fun p => runProperty p.name
        (∀ gs : GenStmts, p.check gs.stmts = true) cfg)
    ++ [ runProperty PropertyNames.stmtKleeneDefinedIff
          (∀ gs : GenStmts, prop_stmt_kleene_defined_iff gs) cfg ]

  -- Procedure-generator ↔ transform-pass properties, folded from the shared
  -- `Properties.procTransforms` bundle (same twenty-eight checks as `TestMain`,
  -- one per named field of the three `*PhaseCorrect` specs). Four FAIL honestly:
  -- the hardcoded-`changed` bug in FilterProcedures, the `.funcDecl`-branch
  -- `changed` bug in PrecondElim, and the two factory-stripping properties (an
  -- unsatisfiable spec field, plus the pass pushing unstripped functions into the
  -- factory).
  let procSuite : List (IO Result) :=
    Properties.procTransforms.map
      (fun p => runProperty p.name
        (∀ gp : GenProcs, p.check gp.procs = true) cfg)

  -- Whole-program-generator properties, folded from the shared
  -- `Properties.programChecks` and `Properties.programADTProps` bundles (the same
  -- ten checks as `TestMain`).
  -- Counterexamples are minimized by the whole-program shrinker, which keeps every
  -- candidate well-typed via Strata's own `Program.typeCheck`. Two checks FAIL
  -- honestly: `typechecker accepts generated programs` on any of three documented
  -- rejection causes, and `typeCheck output re-typechecks` intermittently (~1 draw
  -- in 500, and unlike the former its witness does shrink). The four
  -- `programADTProps` checks all pass: they watch the across-declaration
  -- ADT-derived-call path (a body calling the constructors, testers and accessors of
  -- a datatype declared earlier) and, being unconditional, stay non-vacuous on a
  -- gap-bearing draw.
  let programSuite : List (IO Result) :=
    (Properties.programChecks ++ Properties.programADTProps).map
      (fun p => runProperty p.name
        (∀ gp : GenProgram, p.check gp.prog = true) cfg)

  -- Pipeline-phase `changed`-flag properties. The two no-op witnesses take no
  -- generated input (each is a constructed program on which the phase provably
  -- cannot change anything), so they run as `runUnitProperty`; the two sweeps over
  -- generated procedure lists are folded like `procTransforms`. Three of the four
  -- FAIL honestly, pinning the four hardcoded-`changed := true` sites
  -- (`FilterProcedures.lean:82`, `IrrelevantAxioms.lean:81`, `Verifier.lean:1510`
  -- and `:1517`). `phase: non-hardcoded pipeline phases have a faithful changed
  -- flag` is the one expected to PASS — the regression guard on the phases that
  -- compute the flag correctly today.
  let phaseSuite : List (IO Result) :=
    Properties.phaseNoOpWitnesses.map
      (fun (nw : String × StrataGenerators.PhaseChangedFlag.NoOpWitness) =>
        runUnitProperty nw.1 nw.2.check)
    ++ Properties.phaseChangedFlags.map
      (fun p => runProperty p.name
        (∀ gp : GenProcs, p.check gp.procs = true) cfg)

  -- Printer-expressiveness properties (#69 P2, #48). Two targeted witnesses (a
  -- `bitvec 128` literal; the eighteen `Bv↔Int` conversion operators) plus the
  -- whole-program property over `GenProgram` — the same wrapper as `programSuite`,
  -- so its counterexamples shrink whenever the draw typechecks. All three FAIL
  -- honestly: the printer substitutes a placeholder and logs an error instead of
  -- failing, so an unprintable construct can round-trip as a *different* program.
  -- See `printerErrorDiagnostic` below for which constructs are responsible.
  let printerSuite : List (IO Result) :=
    Properties.printerWitnesses.map
      (fun (nc : String × Bool) => runUnitProperty nc.1 nc.2)
    ++ [ runProperty PropertyNames.printerNoConversionError
           (∀ gp : GenProgram,
             StrataGenerators.PrinterCoverage.checkProgramPrintsWithoutError gp.prog = true)
           cfg ]

  -- Properties for the eight Core transform passes that have no correctness proof
  -- (issue #69), folded from the shared `Properties.unprovenTransforms` bundle (the
  -- same forty-five checks as `TestMain`). Each runs its pass on a whole generated
  -- program; counterexamples shrink through the same whole-program shrinker.
  -- The four defects the bug report files all show up here as honest failures:
  -- `loop: LoopElim mints distinct block labels` (the pass emits one minted label two
  -- times), `procInline: inlining introduces no duplicate label` (two independent
  -- causes), `procInline: the output typechecks` (an `old x` expression escapes the
  -- renaming) and `procInline: symbolic evaluation loses no obligation` (the callee's
  -- `requires` is dropped — the unsound one, repo issue #107). The `procInline` three
  -- are rare on generated input, so a short run may show them green. The two `s2u:`
  -- failures (`every block is reachable from the entry`, `a cfg-bodied procedure
  -- prints`) are expected red ticks the report does NOT file as defects.
  -- `CommonSubexprElim` fires on 0 of 200 generated programs, so all four CSE
  -- properties are vacuous here and `#guard`s test them instead.
  -- The last three (`… symbolic evaluation loses no obligation`, §2.9) run each of
  -- `InsertLoopInvariantAsserts`, `NondetElim` and `LoopInitHoist` through `LoopElim`
  -- and then Strata's symbolic evaluator; all three pass, and they found the eighth
  -- defect — in the evaluator, not the passes
  -- (`docs/strata-symbolic-eval-nondet-collision.md`).
  let unprovenSuite : List (IO Result) :=
    Properties.unprovenTransforms.map
      (fun p => runProperty p.name
        (∀ gp : GenProgram, p.check gp.prog = true) cfg)

  let exitCode ← runSuites [
    ("expr", exprSuite),
    ("cmd", cmdSuite),
    ("function", functionSuite),
    ("stmt", stmtSuite),
    ("proc", procSuite),
    ("program", programSuite),
    ("phase", phaseSuite),
    ("printer", printerSuite),
    ("transforms", unprovenSuite)
  ]

  -- Always-run diagnostics (do not gate the exit code):
  --
  -- Surface the actual `resolve` error messages behind any resolve-after-erase
  -- counterexamples.
  IO.println ""
  IO.println "Resolve-after-erase error diagnostics:"
  let _ ← printResolveErrors numTrials maxSize

  -- Special-character identifier probe: minimal reproducers per position, using
  -- legal identifiers that contain special characters (`genQuotedName`). Reported
  -- as a diagnostic (known limitation), not gated.
  IO.println ""
  IO.println "Special-character identifier round-trip diagnostics:"
  let (probeFail, probeOk) ← specialCharProbeDiagnostic numTrials maxSize
  if probeFail == 0 then
    IO.println s!"  PASS ({probeOk} ident/position round-trips)"
  else
    IO.println s!"  FOUND {probeFail} failing ident/position cases ({probeOk} ok) — see reproducers above"

  -- ADT-derived-call coverage, identical to `TestMain`'s (the two drivers share
  -- the report so they cannot drift). A distribution, never gated.
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

  -- Whole-program shrinker diagnostic (same as `TestMain`): exercises the
  -- `Shrinkable GenProgram` instance, which a green run of the program properties
  -- would otherwise leave untouched. Diagnostic, not gated.
  IO.println ""
  IO.println "Whole-program shrinker diagnostics:"
  let (_, shrinkIllTyped, shrinkStranded) ← programShrinkDiagnostic numTrials
  if shrinkIllTyped == 0 && shrinkStranded == 0 then
    IO.println "    PASS (every candidate well-typed, no stranded `requires`)"
  else
    IO.println "    SHRINKER BUG — see counts above"

  return exitCode
