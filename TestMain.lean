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
open LSpec (TestSeq checkIO lspecIO group)

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

  let exitCode ← lspecIO (.ofList [
    ("expr", [exprSuite]),
    ("cmd", [cmdSuite]),
    ("function", [functionSuite]),
    ("stmt", [stmtSuite]),
    ("proc", [procSuite])
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
    IO.println "Tyche visualizations disabled (--no-tyche)."

  return exitCode
