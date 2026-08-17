import StrataGenerators.AdtLaws
import StrataGenerators.HasTypeAGen.SmtEval

/-!
# Running the ADT laws against a live solver (opt-in)

`StrataGenerators.AdtLaws` builds, for a generated `mutual … end` block, a Core
program whose proof obligations are exactly the injectivity and disjointness laws
of the block's constructors. This module discharges them with a real solver, so —
like `StrataGenerators.SmtEval`, whose conventions it follows — it is **opt-in**:
the properties are added to the suite only under `--smt`.

## What counts as a failure

Three outcomes per obligation, and only the middle one fails a law property:

* **proved** — `VCResult.isSuccess`, i.e. the solver established validity.
* **refuted** — the solver returned a verdict, and it was not "valid". This is a
  counterexample to the law, and the block is printed.
* **refused** — the query never got a verdict: an encoder error, a solver parse
  error, or a crash. Reported with its cause, never scored, exactly as
  `SmtEval.checkValidExpr` treats `.error`. An unencodable query is a limit of the
  encoder, not a datatype whose constructors fail to be injective.

Because "refused" is unscored, a law property could in principle pass while
checking nothing. Two things prevent that: the `blockIsSmtSafe` screen (which
excludes the two *known* encoder defects, so a refusal is a new cause worth
reading), and the vacuity guard — a law family with zero checked obligations
**fails** and says so.

## The third property: is the query even accepted?

`adtSolverAcceptsQuery` is the deliberately unscreened counterpart: it draws
blocks with no safety screen at all and asks only whether every emitted query
reached a verdict. It **fails honestly**, on two independent defects that a legal
Core datatype triggers:

1. **`bitvec 0`.** `pickBitvecWidth` draws an unbounded width, so a field of
   type `bitvec 0` occurs. Core typechecks it; the encoder emits `(_ BitVec 0)`,
   whose index SMT-LIB 2.6 requires to be positive. cvc5: `Illegal bitvector size:
   0`; z3: `bit-vector size must be greater than zero`.
2. **`'` in an identifier.** Core's identifier alphabet includes `'`, which is not
   an SMT-LIB simple-symbol character, and the encoder emits a datatype /
   constructor / field name verbatim rather than pipe-quoting it (`|c'x|`), which
   it already does elsewhere for type variables. cvc5: `Error finding token`.

Both are pinned by hand-built witnesses (`bv0Witness`, `quoteWitness`) as well as
by the generated draws, so the causes stay identified even on a run whose random
blocks happen to miss them, and so a fix can be checked against a fixed input.
-/

open Lambda Core Imperative

namespace StrataGenerators.AdtLawsSmt

open StrataGenerators.AdtLaws

/-- The verdict on one obligation. -/
inductive Verdict where
  | proved
  | refuted
  /-- The query got no verdict; the message names the cause. -/
  | refused (cause : String)
  deriving Inhabited

/-- A `VCResult`'s outcome as one line, truncated.

    Not the *first* line: a solver crash prints `🚨 SMT Solver Crash! stderr:` and
    puts the informative part — `Illegal bitvector size: 0`, `Error finding token` —
    on a later line, so taking the head would report every distinct defect under one
    indistinguishable cause. Flattening and truncating keeps the causes apart, which
    is the whole point of `adtSolverAcceptsQuery`'s report. -/
private def outcomeHead (r : Core.VCResult) : String :=
  let words := (r.formatOutcome.splitOn "\n").flatMap (·.splitOn " ")
  -- Drop the temporary `.smt2` path and the line:column it carries: both differ per
  -- obligation and per run, so keeping them would report one cause as many.
  let words := words.filter (fun w => !w.isEmpty && !(w.splitOn "/").length.pred > 0
                                      && !(w.splitOn ".smt2").length.pred > 0)
  ((String.intercalate " " words).take 140).trimAscii.toString

/-- Classify one `VCResult`. A `.error` outcome is a refusal (encoder error,
    solver crash, timeout); a successful `.ok` is `proved`; any other `.ok` is a
    verdict that the obligation is not valid, i.e. `refuted`. -/
def classify (r : Core.VCResult) : Verdict :=
  match r.outcome with
  | .error _ => .refused (outcomeHead r)
  | .ok _ => if r.isSuccess then .proved else .refuted

/-- Run the whole Core verification pipeline on `p` with `solver`, returning the
    per-obligation results, or a single refusal cause when the pipeline itself
    threw (`emitDatatypes` raises `IO.userError` for an arrow-typed field, and a
    type error surfaces the same way). -/
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

/-- Per-law tallies: proved, refuted, refused. -/
structure Tally where
  proved  : Nat := 0
  refuted : Nat := 0
  refused : Nat := 0
  deriving Inhabited

def Tally.add (t : Tally) : Verdict → Tally
  | .proved => { t with proved := t.proved + 1 }
  | .refuted => { t with refuted := t.refuted + 1 }
  | .refused _ => { t with refused := t.refused + 1 }

def Tally.checked (t : Tally) : Nat := t.proved + t.refuted

def Tally.format (t : Tally) : String :=
  s!"{t.proved} proved, {t.refuted} REFUTED, {t.refused} refused"

/-- Draw a block that passes both screens, or `none` after `tries` attempts.

    The size schedule is `maxSize := 0`: at any larger size `genArgTy` can emit an
    arrow, which `validateDatatypesForSMT` refuses for the whole block, and the
    measured eligible fraction drops from 40/40 to about 5/40 — three quarters of
    the budget would go to draws that never reach a solver. Larger sizes are
    exercised by `adtSolverAcceptsQueryAction`, which wants exactly those
    refusals. -/
partial def drawSafeBlock (tries : Nat := 25) : IO (Option (MutualDatatype Unit)) := do
  if tries == 0 then return none
  let block ← DatatypeGen.sample (maxSize := 0)
  if blockAccepted block && blockIsSmtSafe block && !(lawProgram block).snd.isEmpty then
    return some block
  else drawSafeBlock (tries - 1)

/-- The two law properties, run together on one draw sequence.

    They share a run because they share every expensive step: one block, one
    program, one pipeline run through `Core.verify` yields the obligations of all
    three law families at once, and splitting them into two properties would double
    the solver work for identical coverage. The verdicts are then *tallied per
    family*, and each property reads its own tally.

    Returns `(injTally, disjTesterTally, disjAppTally, notes)`. The third is
    reported but not asserted on: those obligations are folded to `true` before the
    solver sees them (see `AdtLaws.checkDisjFoldsDuringSymEval`), so their `proved`
    count says something about the evaluator, not about SMT. -/
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

/-- The suite node shape the harnesses expect: `(success, passed, attempted,
    note)`. A family with zero checked obligations fails: a law property that
    checked nothing is a coverage loss, not a pass. -/
def tallyToNode (kind : String) (t : Tally) (notes : List String) :
    Bool × Nat × Nat × Option String :=
  let note := s!"{kind}: {t.format}"
    ++ (if notes.isEmpty then "" else "; " ++ String.intercalate "; " (notes.take 6))
  if t.checked == 0 then
    (false, 0, 0, some s!"NO obligation was checked (vacuous) — {note}")
  else
    (t.refuted == 0, t.proved, t.checked, some note)

/-! ## The unscreened property: does every emitted query reach a verdict? -/

/-- The two witness blocks, from `AdtLaws`: a `bitvec 0` field, and names holding
    `'`. They live there because the *pure* half of each defect — that the block is
    Core-legal, and that the SMT-safety screen sees it — is pinned by `#guard`s that
    need no solver. Here they are run against a live one. -/
def bv0Witness : MutualDatatype Unit := AdtLawsWitnesses.bv0Block
def quoteWitness : MutualDatatype Unit := AdtLawsWitnesses.quoteBlock

/-- Draw a block whose law program is at least *attemptable* — accepted by
    `addMutualBlock`, arrow-free (else the pipeline throws before any obligation
    exists) and contributing at least one obligation — but with no screen on
    widths or names, which is what this property is about. -/
partial def drawAttemptableBlock (sz : Nat) (tries : Nat := 25) :
    IO (Option (MutualDatatype Unit)) := do
  if tries == 0 then return none
  let block ← DatatypeGen.sample (maxSize := sz)
  if blockAccepted block && blockIsSmtEligible block && !(lawProgram block).snd.isEmpty then
    return some block
  else drawAttemptableBlock sz (tries - 1)

/-- **Every emitted law query reaches a solver verdict.** FAILS honestly: see the
    module doc for the two causes. Runs the two hand-built witnesses first (so the
    causes are named on every run, not only on a lucky draw), then generated
    blocks.

    `attempted` counts obligations, `passed` counts obligations that got a verdict
    of either kind. The note lists each distinct refusal cause, which is what makes
    the property a *report* on encoder coverage rather than only a red tick. -/
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
  -- Generated blocks, over a size schedule: size 0 is the shape the law
  -- properties use, the larger sizes bring `Map`/`Sequence` field types.
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
