import StrataGenerators.AdtLaws
import StrataGenerators.HasTypeAGen.SmtEval

/-!
# The ADT laws against a live solver, under a gate

For a generated `mutual … end` block, `StrataGenerators.AdtLaws` builds a Core program
whose proof obligations are the laws of injectivity and disjointness of the constructors
of the block. This module discharges those obligations with a real solver. A **gate**
therefore controls it, in the same way as `StrataGenerators.SmtEval`, whose conventions it
follows: the suite holds these properties only under `--smt`.

## What counts as a failure

Each obligation has one of three outcomes, and only the second one makes a law property
fail:

* **proved.** `VCResult.isSuccess` holds, so the solver established validity.
* **refuted.** The solver returned a verdict, and the verdict was not "valid". This is a
  counterexample to the law, and the report prints the block.
* **refused.** The query got no verdict. The cause is an error from the encoder, a parse
  error from the solver, or a crash. The report gives the cause and it scores nothing,
  which is how `SmtEval.checkValidExpr` treats an `.error`. A query that the encoder cannot
  write is a limit of the encoder, and not a datatype whose constructors are not injective.

A refusal has no score, so a law property can in principle pass and check nothing. Two
things prevent that. The `blockIsSmtSafe` screen removes the two *known* defects of the
encoder, so a refusal is a new cause and worth a read. The guard against vacuity also
makes a law family with zero checked obligations **fail**, and it says so.

## The third property: does the solver accept the query at all?

`adtSolverAcceptsQuery` is the property with no screen. It draws blocks with no safety
screen, and it asks only whether each emitted query reached a verdict. Two separate defects
break it, and a legal Core datatype causes each one:

1. **`bitvec 0`.** `pickBitvecWidth` draws a width with no bound, so a field of the type
   `bitvec 0` occurs. Core typechecks it. The encoder then emits `(_ BitVec 0)`, and
   SMT-LIB 2.6 needs a positive index. cvc5 reports `Illegal bitvector size: 0`, and z3
   reports `bit-vector size must be greater than zero`.
2. **A `'` in an identifier.** The identifier alphabet of Core holds `'`, which is not a
   simple-symbol character of SMT-LIB. The encoder writes the name of a datatype, of a
   constructor and of a field without a change, and it does not quote the name as `|c'x|`.
   It already quotes a type variable elsewhere. cvc5 reports `Error finding token`.

Hand-built witnesses, `bv0Witness` and `quoteWitness`, pin both defects, and the generated
draws also reach them. The causes therefore stay clear on a run whose random blocks miss
them, and a fix has a fixed input to run against.
-/

open Lambda Core Imperative

namespace StrataGenerators.AdtLawsSmt

open StrataGenerators.AdtLaws

/-- The verdict on one obligation. -/
inductive Verdict where
  | proved
  | refuted
  /-- The query got no verdict, and the message names the cause. -/
  | refused (cause : String)
  deriving Inhabited

/-- The outcome of a `VCResult` as one short line.

    The line is not the *first* line of the output. A crash of the solver prints
    `🚨 SMT Solver Crash! stderr:` first, and it puts the useful part on a later line, such as
    `Illegal bitvector size: 0` or `Error finding token`. The first line alone therefore
    reports each different defect under one cause that a reader cannot tell apart. This
    function joins the lines and then cuts the result, so the causes stay separate, and that
    is the purpose of the report of `adtSolverAcceptsQuery`. -/
private def outcomeHead (r : Core.VCResult) : String :=
  let words := (r.formatOutcome.splitOn "\n").flatMap (·.splitOn " ")
  -- Drop the path of the temporary `.smt2` file, and the line and column that follow it. Both
  -- differ for each obligation and for each run, so a report that keeps them shows one cause
  -- as many causes.
  let words := words.filter (fun w => !w.isEmpty && !(w.splitOn "/").length.pred > 0
                                      && !(w.splitOn ".smt2").length.pred > 0)
  ((String.intercalate " " words).take 140).trimAscii.toString

/-- The verdict for one `VCResult`. An `.error` outcome is a refusal, and its cause is an error
    from the encoder, a crash of the solver, or a timeout. An `.ok` outcome that succeeded is
    `proved`. Each other `.ok` outcome is a verdict that the obligation is not valid, which is
    `refuted`. -/
def classify (r : Core.VCResult) : Verdict :=
  match r.outcome with
  | .error _ => .refused (outcomeHead r)
  | .ok _ => if r.isSuccess then .proved else .refuted

/-- Runs the whole Core verification pipeline on `p` with `solver`. The result holds one entry
    for each obligation. The result is one cause of a refusal when the pipeline itself threw.
    `emitDatatypes` raises an `IO.userError` for a field with an arrow type, and a type error
    arrives in the same way. -/
def verifyLawProgram (solver : String) (p : Program) :
    IO (Except String (Array Core.VCResult)) := do
  try
    IO.FS.withTempDir fun dir => do
      let res ← (Core.verify p dir
                  (options := { Core.VerifyOptions.quiet with solver })).toIO
                  (fun m => IO.userError (toString (m.format none)))
      return .ok res
  catch e =>
    return .error (e.toString.splitOn "\n").head!

/-- The counts for one law: proved, refuted and refused. -/
structure Tally where
  proved  : Nat := 0
  refuted : Nat := 0
  refused : Nat := 0
  deriving Inhabited

/-- Adds one verdict to the counts. -/
def Tally.add (t : Tally) : Verdict → Tally
  | .proved => { t with proved := t.proved + 1 }
  | .refuted => { t with refuted := t.refuted + 1 }
  | .refused _ => { t with refused := t.refused + 1 }

/-- The number of obligations that got a verdict, which is the sum of the proved obligations and
    the refuted ones. -/
def Tally.checked (t : Tally) : Nat := t.proved + t.refuted

/-- The counts as one line, for a report. -/
def Tally.format (t : Tally) : String :=
  s!"{t.proved} proved, {t.refuted} REFUTED, {t.refused} refused"

/-- Draws a block that passes both screens, or gives `none` after `tries` attempts.

    The draw uses `maxSize := 0`. At a larger size, `genArgTy` can emit an arrow, and
    `validateDatatypesForSMT` then refuses the whole block. Most of the budget would go to
    draws that no solver sees. `adtSolverAcceptsQueryAction` uses the larger sizes, because it
    wants those refusals. -/
partial def drawSafeBlock (tries : Nat := 25) : IO (Option (MutualDatatype Unit)) := do
  if tries == 0 then return none
  let block ← DatatypeGen.sample (maxSize := 0)
  if blockAccepted block && blockIsSmtSafe block && !(lawProgram block).snd.isEmpty then
    return some block
  else drawSafeBlock (tries - 1)

/-- Runs the two law properties together, over one sequence of draws.

    The two properties share a run, because they share each expensive step. One block, one
    program and one run of `Core.verify` give the obligations of all three law families. A
    separate run for each property would double the solver work and give the same coverage.
    The function then counts the verdicts *for each family*, and each property reads its own
    counts.

    The result is `(injTally, disjTesterTally, disjAppTally, notes)`. The report gives the third
    count, and no property asserts on it. The evaluator folds those obligations to `true`
    before the solver sees them, as `AdtLaws.checkDisjFoldsDuringSymEval` states, so their
    `proved` count says something about the evaluator and not about SMT. -/
def runLawTallies (numTrials : Nat) (solver : String) :
    IO (Tally × Tally × Tally × List String) := do
  let blocks := min numTrials 12
  let mut inj : Tally := {}
  let mut disjT : Tally := {}
  let mut disjA : Tally := {}
  let mut notes : List String := []
  let mut drawn := 0
  for _ in List.range blocks do
    match ← drawSafeBlock with
    | none =>
      notes := notes ++ ["a draw found no block passing the screens in 25 tries"]
    | some block =>
      drawn := drawn + 1
      let (prog, _) := lawProgram block
      match ← verifyLawProgram solver prog with
      | .error cause =>
        notes := notes ++ [s!"pipeline error: {cause}"]
      | .ok results =>
        for r in results do
          let v := classify r
          match LawKind.ofLabel r.obligation.label with
          | some .inj => inj := inj.add v
          | some .disjTester => disjT := disjT.add v
          | some .disjApp => disjA := disjA.add v
          | none => pure ()
          match v with
          | .refuted =>
            notes := notes ++
              [s!"REFUTED {r.obligation.label} on block {Std.format (Core.TypeDecl.data block)}"]
          | .refused cause =>
            notes := notes ++ [s!"refused {r.obligation.label}: {cause}"]
          | .proved => pure ()
  notes := notes ++ [s!"{drawn}/{blocks} blocks drawn; solver {solver}"]
  return (inj, disjT, disjA, notes)

/-- The tuple that a driver needs for a suite node: `(success, passed, attempted, note)`. A
    family with zero checked obligations fails, because a law property that checked nothing is
    a loss of coverage and not a pass. -/
def tallyToNode (kind : String) (t : Tally) (notes : List String) :
    Bool × Nat × Nat × Option String :=
  let note := s!"{kind}: {t.format}"
    ++ (if notes.isEmpty then "" else "; " ++ String.intercalate "; " (notes.take 6))
  if t.checked == 0 then
    (false, 0, 0, some s!"NO obligation was checked (vacuous) — {note}")
  else
    (t.refuted == 0, t.proved, t.checked, some note)

/-! ## The property with no screen: does each emitted query reach a verdict? -/

/-- The witness block from `AdtLaws` that has a `bitvec 0` field. `AdtLaws` holds it, because
    `#guard` statements there pin the *pure* half of the defect: Core accepts the block, and
    the screen for SMT safety sees it. Those statements need no solver, and this module runs
    the block against a live solver. -/
def bv0Witness : MutualDatatype Unit := AdtLawsWitnesses.bv0Block

/-- The witness block from `AdtLaws` whose names hold `'`. `AdtLaws` holds it for the same
    reason as `bv0Witness`. -/
def quoteWitness : MutualDatatype Unit := AdtLawsWitnesses.quoteBlock

/-- Draws a block whose law program the pipeline can at least *attempt*. Three conditions must
    hold: `addMutualBlock` accepts the block; the block holds no arrow type, because the
    pipeline otherwise throws before an obligation exists; and the block gives at least one
    obligation. There is no screen on a width or on a name, and those are what this property is
    about. -/
partial def drawAttemptableBlock (sz : Nat) (tries : Nat := 25) :
    IO (Option (MutualDatatype Unit)) := do
  if tries == 0 then return none
  let block ← DatatypeGen.sample (maxSize := sz)
  if blockAccepted block && blockIsSmtEligible block && !(lawProgram block).snd.isEmpty then
    return some block
  else drawAttemptableBlock sz (tries - 1)

/-- **Each law query that the encoder emits reaches a verdict from the solver.** The
    documentation of this module gives the two defects that break this property.

    The action runs the two hand-built witnesses first, so the report names the two causes on
    each run and not only on a lucky draw. It then runs generated blocks.

    `attempted` counts the obligations, and `passed` counts the obligations that got a verdict
    of either kind. The note lists each different cause of a refusal, and this is what makes
    the property a *report* on the coverage of the encoder, and not only a verdict. -/
def adtSolverAcceptsQueryAction (numTrials : Nat) (solver : String) :
    IO (Bool × Nat × Nat × Option String) := do
  let mut total := 0
  let mut verdicts := 0
  let mut causes : List String := []
  let mut witnessNotes : List String := []
  let run := fun (label : String) (block : MutualDatatype Unit) => do
    let (prog, _) := lawProgram block
    match ← verifyLawProgram solver prog with
    | .error cause => return (label, 0, 0, [cause])
    | .ok results =>
      let mut n := 0
      let mut v := 0
      let mut cs : List String := []
      for r in results do
        n := n + 1
        match classify r with
        | .refused c => cs := cs ++ [c]
        | _ => v := v + 1
      return (label, n, v, cs)
  for (label, block) in [("bitvec-0 witness", bv0Witness), ("quoted-name witness", quoteWitness)] do
    let (_, n, v, cs) ← run label block
    total := total + n
    verdicts := verdicts + v
    causes := causes ++ cs
    witnessNotes := witnessNotes ++ [s!"{label}: {v}/{n} got a verdict"]
  -- Generated blocks, over a schedule of sizes. Size 0 gives the shape that the law properties
  -- use, and the larger sizes give a `Map` field type and a `Sequence` field type.
  for i in List.range (min numTrials 8) do
    match ← drawAttemptableBlock (i % 3) with
    | none => pure ()
    | some block =>
      let (_, n, v, cs) ← run "generated" block
      total := total + n
      verdicts := verdicts + v
      causes := causes ++ cs
  let distinct := causes.eraseDups
  let note := s!"{verdicts}/{total} obligations got a verdict; "
    ++ String.intercalate "; " witnessNotes
    ++ (if distinct.isEmpty then "" else
        s!"; {distinct.length} distinct refusal cause(s): "
        ++ String.intercalate " | " (distinct.take 4))
  return (verdicts == total, verdicts, total, some note)

end StrataGenerators.AdtLawsSmt
