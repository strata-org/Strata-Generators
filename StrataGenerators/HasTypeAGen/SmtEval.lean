import StrataGenerators.HasTypeAGen.TestSupport
import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.Factory
import Strata.Languages.Core.Identifiers

open Lambda

/-!
# Symbolic and concrete evaluation agree, under a gate

This module runs the `checkValid` check of upstream against the generators of *this*
repository. For a generated closed term `e`, the check does two steps:

1. It annotates `e`, and it then evaluates `e` concretely with `LExpr.evalWithLState`.
2. If `e` reduces to a constant, it encodes both `e` and the result of the evaluation with
   `Core.toSMTTerm`, it asserts that the two are equal with `Strata.SMT.Factory.eq`, and it
   asks the solver whether that equality is provable, through
   `Core.SMT.dischargeObligation`.

The check therefore compares the evaluator in Lean against the separate semantics of SMT.

The check is an `IO Bool` and it needs a **live SMT solver**, which is `cvc5` or `z3`, at run
time. A gate therefore controls this property: the suite holds it only when the driver runs
with `lake test -- --smt`. It is *not* a part of the default run.

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
  and not a disagreement of the evaluator. So nothing is scored at type `string`
  against cvc5, although the defect is present.
- **z3** accepts the literal, and it then measures `str.len` in bytes. That
  contradicts the count of codepoints from `Str.Length` in Lean. The harness
  *scores* that contradiction and names the term.

A run against cvc5 alone therefore hides a true defect behind an unscored error.
For this reason the check runs each solver in `agreementSolvers` on each term. It
also names each solver that this machine cannot launch, so that an absent solver
does not become a silent loss of coverage.

The harness reports a count for each type, and it names each type that gave no term that it
can check. It does so because silent vacuity is the failure mode that this suite meets most
often. Silent vacuity is a property that holds because it never really ran.
-/

namespace StrataGenerators.SmtEval

/-- Annotates `e` and evaluates it. When the result is a constant, the function returns the SMT term
    that asserts that `e` equals the result, and the context of the encoder. A result of `none` means
    that `e` did not reduce to a constant. This function follows the `encode` function of the
    upstream test. -/
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

/-- The verdict of the comparison between SMT and concrete evaluation, for one term. There are four
    results:
    - `.ok none`: the term did not reduce to a constant. This is a skip and not a failure.
    - `.ok (some true)`: the solver confirmed that `e` equals the result of the evaluation.
    - `.ok (some false)`: the solver reported that the two are *not* equal. This is a real
      counterexample to the agreement between the evaluator and SMT.
    - `.error msg`: the encoder could not write the term, or the solver gave an error, or the solver
      is absent. The report gives the message, and it scores no counterexample.

    `solver` names the executable to run. Its default value is
    `Core.VerifyOptions.default.solver`, which is `cvc5`. The choice of solver changes the verdict on
    a term whose SMT-LIB form is not well formed. cvc5 gives a parse error, which becomes an
    `.error`. z3 accepts the query, and it can then disagree, which becomes `.ok (some false)`. See
    `smtEvalAgreementAction`. -/
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
      -- A closed term holds no free variable, so the list of typed identifiers is empty.
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

-- ── The schedule over the base types ──────────────────────────────────
--
-- The schedule covers each base type that has an SMT encoding. That coverage is what exercises the
-- adversarial primitive generators, and the properties about the overflow of a bitvector and about
-- strings and UTF-8.
--
-- The draws use `coreOpCtx`, which is `factoryOps coreFactory` and therefore each operator that
-- Strata Core defines. `coreOpCtx` cannot differ from the factory, because it *is* the factory. A
-- separate context for each type, which a person writes as a list of names and types, can differ
-- from the factory.
--
-- Each operator in `coreOpCtx` meets the first condition that this property needs: `Core.Factory`
-- holds it, so `addFactory` inside `encodeExpr` can reduce it. The second condition, an SMT
-- encoding, does not hold for each operator. An operator with no encoding gives an error whose
-- message starts with `encode:`. The harness *gives that error in its report and it scores nothing*.
-- An absent encoding therefore becomes a skip, and not a false counterexample, and the schedule
-- needs no list of the operators that have an encoding.

/-- The bitvector widths that `Core.Factory` registers. The list holds the width `1` on purpose. At
    width 1, `INT_MIN`, `allOnes` and `-1` are one value, and that is the difference in the encoding
    of `SDivOverflow`.

    The width `2` is **absent**, although upstream *defines* the operators at width 2. Compare the
    list of definitions, which holds `1`, `2`, `8` and more widths, with the list of names in
    `WFFactoryArray`, which holds `1`, `8` and more widths but not `2`. That difference is a known
    defect, and a name such as `Bv2.*` shows it: the name resolves to no entry of the factory. -/
def registeredBvWidths : List Nat := [1, 8, 16, 32, 64]

/-- Each base type to test, with the operator context for the draws at that type.

    Each entry is a triple of a label, a type and an `octx`. Each entry uses the **same** `octx`,
    which is `coreOpCtx` and therefore the whole of `Core.Factory`. Only the target type differs
    between two entries.

    One shared context is what makes each operator reachable at the type of its *result*. An
    operator on strings whose result is not a string is reachable only at the type of that result.
    `Str.Length` has the type `string → int`, so it can head a term of the type `int` only, and
    `Str.PrefixOf` can head a term of the type `bool` only. A separate context for each type, which
    holds only the operators *named* for that type, therefore hides `Str.Length` from each entry, and
    the property never builds a term such as `Str.Length "é"`. It then cannot compare a count of
    codepoints in Lean against a count of bytes in the solver, and that comparison is the sharpest
    test of the escape function.

    There is one entry for each bitvector width, because `Core.Factory` names each bitvector operator
    with its width. The width of an entry selects the target type, and `coreOpCtx` gives the
    operators at each registered width.

    The schedule holds **no** entry for `regex` as a top-level type, on purpose, although `regex` is
    a base type and `pickBaseType` gives it. *This* property can test nothing at the type `regex`.
    `regex` has no constant form, because `LConst` has no constructor for it, and Core interprets no
    `Re.*` operator. A term of the type `regex` can therefore never reduce to a constant, and the
    harness skips each such term. An entry for `regex` would report a permanent `regex:0` that no one
    can correct, and it would teach a reader to ignore the warning about vacuity. That warning must
    stay useful. `regex` still occurs as the type of a *subterm*, through `Str.InRegEx` and
    `Str.ToRegEx`. To test the type directly, write a property that only a solver discharges, about
    the laws of a regular expression. Two facts in the code support this decision: the denotational
    semantics gives `regex` no denotation, and the translation to SMT refuses it. -/
def baseTypeSchedule : List (String × LMonoTy × OpCtx) :=
  [ ("int",    .int,    coreOpCtx)
  , ("bool",   .bool,   coreOpCtx)
  , ("string", .string, coreOpCtx)
  , ("real",   .real,   coreOpCtx) ]
  ++ registeredBvWidths.map (fun w =>
       (s!"bv{w}", (.bitvec w : LMonoTy), coreOpCtx))

/-- Makes a closed term of the type `ty` over the operator context `octx`. If the generator reaches
    its fallback for an empty support, the function tries again with new randomness. The result is
    `none` when no attempt succeeds. -/
partial def genClosedBaseTerm (octx : OpCtx) (ty : LMonoTy) (depth : Nat)
    (tries : Nat := 20) : IO (Option LExpr') := do
  if tries == 0 then return none
  try
    let e ← genLExprWithOps (G := IO) [] octx [] [] [] depth ty
    return some e
  catch _ =>
    genClosedBaseTerm octx ty depth (tries - 1)

/-- The check that the concrete evaluator and SMT agree. The `--smt` gate enables it. The result has
    the shape of the other suite nodes that use `IO`, which is
    `(success, passed, attempted, errorMsg)`. `attempted` counts only the terms that reduced to a
    constant, so it is the sum of `passed` and the number of failures. The message gives each term
    that did not reduce, and each error from the encoder or from the solver, and none of those change
    the exit code. Only a verdict of "not equal" from the solver makes the suite fail, and the harness
    prints the first few such counterexamples.

    **The check runs each solver in `availableAgreementSolvers` on each term.** One solver is not
    enough. A term whose SMT-LIB form holds a string literal that is not well formed gives a parse
    error on cvc5, and the harness reports that error and scores nothing. The same term parses on z3,
    which then measures `str.len` in bytes and contradicts the count of codepoints from `Str.Length`
    in Lean. The harness scores that contradiction as a counterexample. A run against cvc5 alone
    therefore passes on a true defect, and only the run against z3 finds it.

    The report gives a count for each pair of a solver and a type. It also names each solver that this
    machine cannot start, and each type that gave no term that the check can use. -/
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
  -- There is one count for each pair of a solver and a type. A pair that gives no term for the check
  -- is therefore visible as `0 checked`, and it does not hide behind a good total. Silent vacuity is
  -- the failure mode that these properties meet most often.
  let mut perCell : List (String × String × Nat × Nat) := []
  for (label, ty, octx) in schedule do
    -- Each type gets its own part of the budget. A new type therefore makes the coverage wider, and
    -- it does not reduce the coverage of `int` and of `bool`.
    let perTypeTrials := max 1 (total / schedule.length)
    let mut cell : List (String × Nat × Nat) := solvers.map (fun s => (s, 0, 0))
    for i in List.range perTypeTrials do
      let size := i % (maxSize + 1)
      let depth := max 1 size
      match ← genClosedBaseTerm octx ty depth with
      | none => skipped := skipped + 1
      | some e =>
        -- Run the *same* term through each solver. The code draws a term one time and checks it many
        -- times, so each solver sees the same input. A difference between two verdicts is therefore a
        -- fact about the solvers, and not about the draw.
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
