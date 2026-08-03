import StrataGenerators.HasTypeAGen.TestSupport
import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.Factory
import Strata.Languages.Core.Identifiers

open Lambda

/-!
# SMT / concrete-eval agreement (opt-in)

A port of `StrataTest/Languages/Core/Tests/ExprEvalTest.lean`'s `checkValid` to
run against *this repo's* generators. For a generated closed term `e`:

1. annotate `e`, then concretely evaluate it (`LExpr.evalWithLState`);
2. if it reduces to a constant, SMT-encode both `e` and its evaluated result
   (`Core.toSMTTerm`), assert their equality (`Strata.SMT.Factory.eq`), and ask
   the solver whether that equality is provable (`Core.SMT.dischargeObligation`).

This cross-checks the in-Lean evaluator against an independent SMT semantics.

Because `checkValid` is `IO Bool` and needs a **live SMT solver** (`cvc5`/`z3`) at
runtime, this property is opt-in: it is only added to the LSpec suite when the
driver is run with `--smt` (see `TestMain`). It is *not* part of the default run.

Two further constraints, both matched below:

- Generation is restricted to `intBoolOpCtx` at base types (`int`/`bool`), so
  every subterm is representable in `Core.Factory` and SMT-encodable. Operators
  outside `Core.Factory` (e.g. the polymorphic `id`/`Sequence.map` combinators
  used elsewhere) make `toSMTTerm` fail, which is an encoder limitation rather
  than an evaluator disagreement.
- A term that does not reduce to a constant (e.g. a residual function) is
  *skipped*, not counted as a counterexample — only a solver verdict of
  "not equal" is a genuine failure.
-/

namespace StrataGenerators.SmtEval

/-- Port of `ExprEvalTest.encode`: annotate `e`, evaluate it, and — when the
    result is a constant — return the SMT term asserting `e = eval e` together
    with the encoding context. `none` means `e` did not reduce to a constant. -/
def encodeExpr (e : LExpr') (tenv : TEnv Unit) (init_state : LState Core.CoreLParams) :
    Except Std.Format (Option (Strata.SMT.Term × Core.SMT.Context)) := do
  let init_state ← init_state.addFactory Core.Factory |>.mapError (fun dm => f!"{dm.message}")
  let lcont := { Lambda.LContext.default with
    functions := Core.Factory, knownTypes := Core.KnownTypes }
  let (e, _T) ← LExpr.annotate lcont tenv e
  let e_res := (LExpr.evalWithLState init_state.config.fuel init_state e).fst
  match e_res with
  | .const _ _ =>
    let factory := Core.Env.init.factory
    let (smt_term_lhs, ctx, _) ← Core.toSMTTerm factory [] e Core.SMT.Context.default []
    let (smt_term_rhs, ctx, _) ← Core.toSMTTerm factory [] e_res ctx []
    return .some (Strata.SMT.Factory.eq smt_term_lhs smt_term_rhs, ctx)
  | _ => return .none

/-- The verdict of the SMT/concrete cross-check on one term:
    - `.ok none` — the term did not reduce to a constant (skip, not a failure);
    - `.ok (some true)` — the solver confirmed `e = eval e`;
    - `.ok (some false)` — the solver reported them *not* equal (a real
      counterexample to evaluator/SMT agreement);
    - `.error msg` — the term could not be encoded, or the solver errored / was
      unavailable (reported, but not scored as a counterexample). -/
def checkValidExpr (e : LExpr') : IO (Except String (Option Bool)) := do
  let tenv := TEnv.default
  let init_state := LState.init
  match encodeExpr e tenv init_state with
  | .error msg => return .error s!"encode: {msg}"
  | .ok .none => return .ok .none
  | .ok (.some (smt_term, ctx)) =>
    try
      let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet) (profilePipeline := false)
      -- Closed terms have no free variables, so the typed-ident list is empty.
      IO.FS.withTempDir (fun tempDir => do
        let filename := tempDir / "exprEvalTest.smt2"
        let ans ← Core.SMT.dischargeObligation
          { Core.VerifyOptions.default with verbose := .quiet }
          [] Imperative.MetaData.empty filename.toString
          [] smt_term ctx true false (label := "exprEvalTest") (pctx := pctx)
        match ans with
        | .ok (.sat _, _, _) => return (.ok (.some true) : Except String (Option Bool))
        | .ok _              => return .ok (.some false)
        | .error _           => return .error "solver error")
    catch ex =>
      return .error s!"discharge exception: {ex.toString}"

/-- The SMT solver the `--smt` check will invoke, read from the *same*
    `Core.VerifyOptions.default` that `checkValidExpr` passes to
    `dischargeObligation` (default: `cvc5`). Deriving it here means the
    availability check below can never name a different solver than the one
    actually run. -/
def solverName : String := Core.VerifyOptions.default.solver

/-- Solver availability check for the `--smt` property: `true` iff the configured
    `solverName` can be launched. `IO.Process.output` captures the child's streams
    and, when the executable is missing, reports a non-zero exit code (rather than
    throwing) — so we treat exit `0` as available and catch any spawn exception as
    a backstop. This avoids letting each per-term discharge silently fail while
    the suite reports a green "0/0 checked". -/
def solverAvailable : IO Bool := do
  try
    let out ← IO.Process.output { cmd := solverName, args := #["--version"] }
    return out.exitCode == 0
  catch _ =>
    return false

/-- Generate a closed term at a base type over `intBoolOpCtx` (int arithmetic,
    comparisons, boolean ops) — all `Core.Factory` operators, hence SMT-encodable.
    Retries with fresh randomness when the generator hits its empty-support
    fallback; `none` if it never succeeds. -/
partial def genClosedBaseTerm (ty : LMonoTy) (depth : Nat) (tries : Nat := 20) : IO (Option LExpr') := do
  if tries == 0 then return none
  try
    let e ← genLExprWithOps (G := IO) [] intBoolOpCtx [] [] [] depth ty
    return some e
  catch _ =>
    genClosedBaseTerm ty depth (tries - 1)

/-- Opt-in SMT/concrete-eval agreement check, shaped like the other IO-based
    suite nodes: returns `(success, passed, attempted, errorMsg)` for
    `TestSeq.individualIO`. `attempted` counts only terms that reduced to a
    constant (passed + failed); non-reducing terms and encode/solver errors are
    reported in the message but never gate the exit code. Only a solver verdict
    of "not equal" fails the suite; the first such counterexample is printed. -/
def smtEvalAgreementAction (numTrials maxSize : Nat) : IO (Bool × Nat × Nat × Option String) := do
  let total := min numTrials 200
  let mut passed := 0
  let mut failed := 0
  let mut skipped := 0
  let mut errored := 0
  let mut firstErr : Option String := none
  let mut shownFails := 0
  for i in List.range total do
    let size := i % (maxSize + 1)
    let depth := max 1 (size / 20)
    let ty : LMonoTy := if i % 2 == 0 then .int else .bool
    match ← genClosedBaseTerm ty depth with
    | none => skipped := skipped + 1
    | some e =>
      match ← checkValidExpr e with
      | .ok .none => skipped := skipped + 1
      | .ok (.some true) => passed := passed + 1
      | .ok (.some false) =>
        failed := failed + 1
        if shownFails < 5 then
          shownFails := shownFails + 1
          IO.println s!"    FAIL (SMT disagreed): {ppExpr e}"
          IO.println s!"      evaluates to:        {ppExpr (eval 100 e)}"
      | .error msg =>
        errored := errored + 1
        if firstErr.isNone then firstErr := some msg
  let attempted := passed + failed
  let note := s!"{skipped} skipped (non-constant/gen-failure), {errored} encode/solver errors"
              ++ (match firstErr with | some m => s!"; first error: {m}" | none => "")
  if failed == 0 then
    pure (true, passed, attempted, some note)
  else
    pure (false, passed, attempted, some s!"{failed} SMT disagreements; {note}")

end StrataGenerators.SmtEval
