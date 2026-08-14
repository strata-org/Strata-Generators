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
driver is run with `lake test -- --smt` (see `TestMain`). It is *not* part of the default run.

Two further constraints, which the code below matches:

- Generation uses only the operators that live in `Core.Factory` and that have an
  SMT encoding. An operator outside `Core.Factory` makes `toSMTTerm` fail.
  Examples are the polymorphic `id` and `Sequence.map` combinators that other
  properties use. Such a failure is a limit of the encoder, and not a disagreement
  of the evaluator.
- A term that does not reduce to a constant, such as a residual function, is
  *skipped*. It is not a counterexample. Only a solver verdict of "not equal" is a
  true failure.

## Base-type coverage

`baseTypeSchedule` gives each base type that this property can truly check:
`int`, `bool`, `string`, `real`, and `bv{1,8,16,32,64}`. Each type generates over
the **same** operator context, `coreOpCtx`, which is the whole of Strata's
`Core.Factory`. Only the target type differs between the entries. The schedule
excludes `regex` on purpose, and provably so. Read `baseTypeSchedule`. `regex`
still occurs as the type of a *subterm*.

The width of this coverage is the point. It is what exercises the adversarial
primitive generators in `StrataGenerators.PrimitiveGens`, which give non-ASCII
strings and boundary-biased bitvectors. It also turns the properties about the SMT
encoding into executable checks. Those properties are about the bitvector overflow
predicates, of which the five unsigned and division ones have no correctness
theorem, and about strings and UTF-8, where Lean interprets `Str.Length` as a
count of *codepoints* and the solver interprets it as a count of *characters*.

## Why the check runs more than one solver

The two solvers give **different verdicts** on the same malformed query, so the
choice of solver decides whether this property finds the escape defect at all.
The defect emits a non-ASCII literal as raw UTF-8. Then:

- **cvc5** rejects the literal with a parse error. The harness reports that error,
  but it does not score it, because an unencodable term is a limit of the encoder
  and not a disagreement of the evaluator. Therefore the property reports **green**
  at type `string` against cvc5, although the defect is present.
- **z3** accepts the literal, and it then measures `str.len` in bytes. That
  contradicts the count of codepoints from `Str.Length` in Lean. The harness
  *scores* that contradiction, so the property **fails** and names the term.

A run against cvc5 alone therefore hides a true defect behind an unscored error.
For this reason the check runs each solver in `agreementSolvers` on each term. It
also names each solver that this machine cannot launch, so that an absent solver
does not become a silent loss of coverage.

The harness reports a tally for each type, and it names each type that gave no
checkable term. It does so because silent vacuity, which is a property that
passes because it never truly ran, is the failure mode that this suite is most
exposed to. In an earlier example of that failure mode, the ANF properties passed
on 599 of 600 inputs that were no-ops.
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
    let (smt_term_lhs, ctx, _) ← Core.toSMTTerm factory [] e Core.SMT.Context.default .empty
    let (smt_term_rhs, ctx, _) ← Core.toSMTTerm factory [] e_res ctx .empty
    return .some (Strata.SMT.Factory.eq smt_term_lhs smt_term_rhs, ctx)
  | _ => return .none

/-- The verdict of the SMT/concrete cross-check on one term:
    - `.ok none` — the term did not reduce to a constant (skip, not a failure);
    - `.ok (some true)` — the solver confirmed `e = eval e`;
    - `.ok (some false)` — the solver reported them *not* equal (a real
      counterexample to evaluator/SMT agreement);
    - `.error msg` — the term could not be encoded, or the solver errored / was
      unavailable (reported, but not scored as a counterexample).

    `solver` names the executable to run. It defaults to
    `Core.VerifyOptions.default.solver`, which is `cvc5`. The choice of solver
    changes the verdict on a term whose SMT-LIB form is malformed: cvc5 gives a
    parse error, which becomes `.error`, and z3 accepts the query and can then
    disagree, which becomes `.ok (some false)`. Read `smtEvalAgreementAction`. -/
def checkValidExpr (e : LExpr')
    (solver : String := Core.VerifyOptions.default.solver) :
    IO (Except String (Option Bool)) := do
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
          { Core.VerifyOptions.default with verbose := .quiet, solver := solver }
          [] Imperative.MetaData.empty filename.toString
          [] smt_term ctx true false (label := "exprEvalTest") (pctx := pctx)
        match ans with
        | .ok (.sat _, _, _) => return (.ok (.some true) : Except String (Option Bool))
        | .ok _              => return .ok (.some false)
        | .error _           => return .error "solver error")
    catch ex =>
      return .error s!"discharge exception: {ex.toString}"

/-- The default SMT solver, read from the *same* `Core.VerifyOptions.default` that
    `checkValidExpr` passes to `dischargeObligation`. The value is `cvc5`. This
    definition makes sure that the availability check below can never name a
    different solver than the one that the check runs. -/
def solverName : String := Core.VerifyOptions.default.solver

/-- The solvers that the agreement property runs, in order.

    The property runs **each** solver on **each** term, because the two solvers
    disagree about a malformed string literal, and the disagreement is the point.
    cvc5 rejects such a literal with a parse error, which the harness reports but
    does not score. z3 accepts the literal and then measures `str.len` in bytes,
    which contradicts the count of codepoints from `Str.Length` in Lean. The
    harness scores that contradiction. Therefore a run against cvc5 alone hides a
    true defect behind an unscored error. -/
def agreementSolvers : List String := [solverName, "z3"]

/-- Solver availability check: the result is `true` if and only if `solver` can be
    launched. `IO.Process.output` captures the streams of the child process. When
    the executable is absent, it reports a non-zero exit code instead of an
    exception. Therefore the check treats exit `0` as available, and it catches any
    exception from the spawn as a backstop. Without this check, each discharge of a
    term fails silently while the suite reports a green "0/0 checked". -/
def solverAvailableNamed (solver : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd := solver, args := #["--version"] }
    return out.exitCode == 0
  catch _ =>
    return false

/-- Availability check for the default solver. -/
def solverAvailable : IO Bool := solverAvailableNamed solverName

/-- The solvers from `agreementSolvers` that this machine can launch. The
    agreement property runs only these, and it names each absent solver in its
    report, so that a missing solver is visible and does not become silent loss of
    coverage. -/
def availableAgreementSolvers : IO (List String) :=
  agreementSolvers.filterM solverAvailableNamed

-- ── The base-type schedule ────────────────────────────────────────────
--
-- The schedule covers each base type that has an SMT encoding. That coverage is
-- what exercises the adversarial primitive generators
-- (`StrataGenerators.PrimitiveGens`) and the properties about bitvector overflow
-- and about strings and UTF-8.
--
-- Generation uses `coreOpCtx`, which is `factoryOps coreFactory`: every operator
-- that Strata's Core truly defines. Earlier versions of this file held four
-- hand-written contexts, one for bitvectors, one for the interpreted string
-- operators, one for the uninterpreted ones, and one for `real`. Each was a
-- transcription of names and types out of `Core.Factory`, and each could drift
-- from it. `coreOpCtx` cannot drift, because it *is* the factory.
--
-- Every operator in `coreOpCtx` satisfies the first condition that this property
-- needs: it lives in `Core.Factory`, so `addFactory` in `encodeExpr` can reduce
-- it. The second condition, an SMT encoding, does not hold for every operator. An
-- operator without one gives an error with the prefix `encode:`. The harness
-- *reports that error but does not score it*. Therefore an absent encoding becomes
-- a skip, and not a false counterexample, and the schedule needs no list of which
-- operators have an encoding.

/-- The bitvector widths that `Core.Factory` registers. The list keeps width `1`
    on purpose. At width 1, `INT_MIN`, `allOnes` and `-1` collapse to one value,
    which is the discrepancy in the `SDivOverflow` encoding.

    Width `2` is **absent**, although `Factory.lean` *defines* the operators at
    width 2. Compare `ExpandBVOpFuncDefs[1, 2, 8, …]` with
    `ExpandBVOpFuncNames [1,8,…]` in `WFFactoryArray`. That gap is a known defect,
    and `Bv2.*` confirms it: the name resolves to no factory entry. -/
def registeredBvWidths : List Nat := [1, 8, 16, 32, 64]

/-- The base type to test, with the operator context to generate it over.

    Each entry is a triple of a label, a type and an `octx`. Each entry uses the
    **same** `octx`, which is `coreOpCtx`, the whole of `Core.Factory`. Only the
    target type differs between entries.

    One shared context is what makes each operator reachable at the type where its
    *result* lives. An operator on strings whose result is not a string is
    reachable only at the type of that result: `Str.Length` is `string → int`, so
    it can head only a term of type `int`, and `Str.PrefixOf` can head only a term
    of type `bool`. A per-type context that holds only the operators *named* for
    that type therefore hides `Str.Length` from every entry, and the property never
    builds a term such as `Str.Length "é"`. Then it cannot compare a count of
    codepoints in Lean against a count of bytes in the solver, which is the
    sharpest test of the escape function. A measurement confirms this: `Str.Length`
    appeared in 0 of 40 terms of type `int` over the earlier context for `int` and
    `bool` alone.

    The bitvector entries are per-width, because `Core.Factory` names each
    bitvector operator by width. The width of the entry selects the target type,
    and `coreOpCtx` supplies the operators at each registered width.

    The schedule keeps `regex` **absent** as a top-level type, on purpose,
    although `regex` is a base type and `pickBaseType` generates it. *This*
    property can test nothing at type `regex`. `regex` has no constant form,
    because `LConst` has no constructor for it, and Core interprets no `Re.*`
    operator. Therefore a term of type `regex` can never reduce to a constant, and
    the harness skips it 100% of the time. An entry for `regex` reports a permanent
    `regex:0` that nobody can correct, and thus it trains the reader to ignore the
    warning about vacuity. That warning must stay believable. `regex` still occurs
    as the type of a *subterm*, through `Str.InRegEx` and `Str.ToRegEx`. To test it
    directly, use a solver-only property about the regex laws. Two structural facts
    support this decision: `Denote.lean` gives `regex` no denotation, and
    `SMT/Translate.lean` refuses to reflect it. -/
def baseTypeSchedule : List (String × LMonoTy × OpCtx) :=
  [ ("int",    .int,    coreOpCtx)
  , ("bool",   .bool,   coreOpCtx)
  , ("string", .string, coreOpCtx)
  , ("real",   .real,   coreOpCtx) ]
  ++ registeredBvWidths.map (fun w =>
       (s!"bv{w}", (.bitvec w : LMonoTy), coreOpCtx))

/-- Generate a closed term of type `ty` over the operator context `octx`. If the
    generator hits its fallback for an empty support, try again with new
    randomness. The result is `none` if no try succeeds. -/
partial def genClosedBaseTerm (octx : OpCtx) (ty : LMonoTy) (depth : Nat)
    (tries : Nat := 20) : IO (Option LExpr') := do
  if tries == 0 then return none
  try
    let e ← genLExprWithOps (G := IO) [] octx [] [] [] depth ty
    return some e
  catch _ =>
    genClosedBaseTerm octx ty depth (tries - 1)

/-- The agreement check between the concrete evaluator and SMT. The user opts in
    with `--smt`. The result has the shape of the other suite nodes that use `IO`:
    `(success, passed, attempted, errorMsg)` for `TestSeq.individualIO`.
    `attempted` counts only the terms that reduced to a constant, which is
    `passed + failed`. The message reports each term that did not reduce, and each
    error from the encoder or the solver, but those never gate the exit code. Only
    a solver verdict of "not equal" fails the suite, and the harness prints the
    first few such counterexamples.

    **The check runs every solver in `availableAgreementSolvers` on every term.**
    One solver is not enough. A term whose SMT-LIB form holds a malformed string
    literal gives a parse error on cvc5, and the harness reports that error without
    a score. The same term parses on z3, which then measures `str.len` in bytes and
    contradicts the count of codepoints from `Str.Length` in Lean. The harness
    scores that contradiction as a counterexample. Therefore a run against cvc5
    alone reports green on a true defect, and only the run against z3 finds it.

    The report gives a tally for each pair of a solver and a type. It also names
    each solver that this machine cannot launch, and each type that gave no
    checkable term. -/
def smtEvalAgreementAction (numTrials maxSize : Nat) : IO (Bool × Nat × Nat × Option String) := do
  let total := min numTrials 200
  let schedule := baseTypeSchedule
  let solvers ← availableAgreementSolvers
  let absent := agreementSolvers.filter (fun s => !solvers.contains s)
  if solvers.isEmpty then
    return (false, 0, 0,
      some s!"no solver available: none of {String.intercalate ", " agreementSolvers} could be launched")
  let mut passed := 0
  let mut failed := 0
  let mut skipped := 0
  let mut errored := 0
  let mut firstErr : Option String := none
  let mut shownFails := 0
  -- One tally for each pair of a solver and a type. Thus a pair that gives no
  -- checkable term is visible as `0 checked`, and it does not hide behind a
  -- healthy total. Silent vacuity is the failure mode that these properties are
  -- most exposed to.
  let mut perCell : List (String × String × Nat × Nat) := []
  for (label, ty, octx) in schedule do
    -- Each type gets its own part of the budget. Thus a new type makes the
    -- coverage wider, and it does not dilute the coverage of `int` and `bool`.
    let perTypeTrials := max 1 (total / schedule.length)
    let mut cell : List (String × Nat × Nat) := solvers.map (fun s => (s, 0, 0))
    for i in List.range perTypeTrials do
      let size := i % (maxSize + 1)
      let depth := max 1 (size / 20)
      match ← genClosedBaseTerm octx ty depth with
      | none => skipped := skipped + 1
      | some e =>
        -- Run the *same* term through each solver. A term is generated once and
        -- checked many times, so the solvers see identical input and a difference
        -- between their verdicts is a fact about the solvers, and not about the
        -- draw.
        for solver in solvers do
          match ← checkValidExpr e solver with
          | .ok .none => skipped := skipped + 1
          | .ok (.some true) =>
            passed := passed + 1
            cell := cell.map (fun (s, p, f) => if s == solver then (s, p + 1, f) else (s, p, f))
          | .ok (.some false) =>
            failed := failed + 1
            cell := cell.map (fun (s, p, f) => if s == solver then (s, p, f + 1) else (s, p, f))
            if shownFails < 5 then
              shownFails := shownFails + 1
              IO.println s!"    FAIL (SMT disagreed) [{label}, {solver}]: {ppExpr e}"
              IO.println s!"      evaluates to:        {ppExpr (eval 100 e)}"
          | .error msg =>
            errored := errored + 1
            if firstErr.isNone then firstErr := some s!"[{label}, {solver}] {msg}"
    perCell := perCell ++ cell.map (fun (s, p, f) => (s, label, p, f))
  let attempted := passed + failed
  let breakdown := String.intercalate "; "
    (solvers.map (fun s =>
      let cells := perCell.filter (fun (s', _, _, _) => s' == s)
      let inner := String.intercalate ", " (cells.map (fun (_, l, p, f) =>
        if f == 0 then s!"{l}:{p}" else s!"{l}:{p}/{f}✗"))
      s!"{s} ({inner})"))
  let vacuous := perCell.filterMap (fun (s, l, p, f) =>
    if p + f == 0 then some s!"{l}@{s}" else none)
  let vacuousNote :=
    if vacuous.isEmpty then ""
    else s!"; NO checkable terms for: {String.intercalate " " vacuous}"
  let absentNote :=
    if absent.isEmpty then ""
    else s!"; SOLVER NOT AVAILABLE (skipped): {String.intercalate " " absent}"
  let note := s!"by solver and type ({breakdown}); {skipped} skipped "
              ++ s!"(non-constant/gen-failure), {errored} encode/solver errors"
              ++ vacuousNote ++ absentNote
              ++ (match firstErr with | some m => s!"; first error: {m}" | none => "")
  if failed == 0 then
    pure (true, passed, attempted, some note)
  else
    pure (false, passed, attempted, some s!"{failed} SMT disagreements; {note}")

end StrataGenerators.SmtEval
