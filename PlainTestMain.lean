import StrataGenerators.TestScaffold
import StrataGenerators.PlainHarness

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

Positional args and flags mirror `TestMain` (`--smt` adds the SMT/concrete-eval
agreement property; it needs a live solver on `PATH`). This executable is **not**
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

  -- `--smt` needs a live SMT solver on `PATH`. Fail fast with a clear message
  -- and a non-zero exit code if the flag is set but the configured solver
  -- (`StrataGenerators.SmtEval.solverName`, default `cvc5`) can't be launched,
  -- rather than silently reporting a green "0/0 checked" suite. Mirrors `TestMain`.
  if cli.smtEnabled then
    unless ← StrataGenerators.SmtEval.solverAvailable do
      IO.eprintln s!"error: --smt requires the SMT solver '{StrataGenerators.SmtEval.solverName}' on PATH, but it could not be launched."
      IO.eprintln "Install it (e.g. cvc5 or z3) and ensure it is on PATH, or run without --smt."
      return 1

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
        (∀ te : ResolveTypedExpr, prop_resolve_after_erase te) cfg
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

  let exitCode ← runSuites [
    ("expr", exprSuite),
    ("cmd", cmdSuite),
    ("function", functionSuite),
    ("stmt", stmtSuite),
    ("proc", procSuite)
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

  return exitCode
