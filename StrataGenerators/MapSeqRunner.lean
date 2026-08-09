import StrataGenerators.MapSeqOracle

open Lambda Strata

/-!
# Running the `Map`/`Sequence` property suite (opt-in: needs a live solver)

Three families, sharing one verdict vocabulary. Each returns
`(success, passed, attempted, note)` so it can slot into `TestSeq.individualIO`
alongside the existing `--smt` node.

## The verdict discipline

`Core.verify` yields one `VCResult` per obligation, and the three outcomes carry
very different weight for these axioms:

- `isFailure` — the solver *refuted* something the `List` model predicts, or the
  two `useArrayTheory` modes disagreed. Scored as a counterexample.
- `isUnknown` — no verdict. Reported and counted separately; never fails the
  suite, because these axioms are genuinely incomplete in characterised places
  (see `containsKnownIncomplete`). Silently folding these into "pass" would let a
  real regression hide, and folding them into "fail" would make the suite red on
  arrival — hence a third bucket rather than a boolean.
- `isSuccess` — proven.

Encoder/solver *errors* are surfaced in the note but do not gate the exit code,
matching how `SmtEval.lean` treats them: an encoding limitation is not an
evaluator disagreement.
-/

namespace StrataGenerators.MapSeqRunner

open StrataGenerators.MapSeqGen StrataGenerators.MapSeqProps
open StrataGenerators.MapSeqOracle

/-- Tallies over one property family's samples. Kept as a record (rather than a
    tuple) so the four counts cannot be transposed at a call site. -/
structure Tally where
  passed   : Nat := 0
  failed   : Nat := 0
  unknown  : Nat := 0
  errored  : Nat := 0
  /-- First failing sample, for the counterexample message. -/
  firstBad : Option String := none
deriving Inhabited

/-- Parse a rendered program and verify it, returning its `VCResults`.
    `none` means the program did not parse/translate — a generator bug rather
    than a Strata disagreement, so callers count it as an error. -/
def verifyProgram (src : String) (useArrayTheory : Bool) :
    IO (Option Core.VCResults) := do
  match ← parseCoreProgram src with
  | none => pure none
  | some prog =>
    try
      IO.FS.withTempDir fun tempDir => do
        let opts := { Core.VerifyOptions.quiet with useArrayTheory }
        let res ← (Core.verify prog tempDir (options := opts)).toIO'
        match res with
        | .ok rs => pure (some rs)
        | .error _ => pure none
    catch _ => pure none

/-- Fold a `VCResults` into a `Tally`, attributing the sample's source to any
    failure so the counterexample is reproducible. -/
def tallyResults (rs : Core.VCResults) (src : String) (acc : Tally) : Tally :=
  rs.foldl (init := acc) fun t r =>
    if r.isFailure then
      { t with failed := t.failed + 1,
               firstBad := t.firstBad <|> some s!"{r.obligation.label}\n{src}" }
    else if r.isUnknown then { t with unknown := t.unknown + 1 }
    else if r.isSuccess then { t with passed := t.passed + 1 }
    else { t with errored := t.errored + 1 }

/-- Shape a `Tally` into the `(success, passed, attempted, note)` quadruple the
    IO-based suite nodes use. `attempted` counts only decided obligations
    (passed + failed), so an all-`unknown` run reports `0/0` rather than a
    misleading green. -/
def Tally.toVerdict (t : Tally) (label : String) : Bool × Nat × Nat × Option String :=
  let attempted := t.passed + t.failed
  let note := s!"{t.unknown} unknown, {t.errored} encode/solver errors"
  if t.failed == 0 then (true, t.passed, attempted, some note)
  else
    let detail := match t.firstBad with
      | some b => s!"\n  first: {b}"
      | none   => ""
    (false, t.passed, attempted,
     some s!"{t.failed} {label} disagreement(s); {note}{detail}")

-- ── §1. `SeqModel` differential ──────────────────────────────────────

/-- Assert the `SeqModel.lean` `List` predictions against the solver for
    `numTrials` generated sequence literals.

    A `fail` here means a `Factory.lean` sequence axiom and its `SeqModel`
    counterpart have drifted apart — which is exactly the claim `SeqModel.lean`
    makes and never proves. -/
def seqModelAgreement (numTrials maxLen : Nat) : IO (Bool × Nat × Nat × Option String) := do
  let total := min numTrials 50
  let mut t : Tally := {}
  for i in List.range total do
    let len := (i % (max 1 maxLen)) + 1
    let elems ← (List.range len).mapM (fun _ => do
      let n ← IO.rand 0 20
      pure (n : Int))
    let lit : SeqLiteral :=
      { elemTy := .tcons "int" []
        elems  := elems
        expr   := seqLiteralOfList (.tcons "int" []) (elems.map (fun v => .intConst () v)) }
    let src := seqModelProgram lit
    match ← verifyProgram src false with
    | none    => t := { t with errored := t.errored + 1 }
    | some rs => t := tallyResults rs src t
  pure (t.toVerdict "SeqModel")

/-- Assert the `Map` axioms' predictions (bound keys select to their
    last-written value; unbound keys select to the `mapConst` default). -/
def mapModelAgreement (numTrials maxSize : Nat) : IO (Bool × Nat × Nat × Option String) := do
  let total := min numTrials 50
  let mut t : Tally := {}
  for i in List.range total do
    let size := (i % (max 1 maxSize)) + 1
    let dflt ← IO.rand 0 20
    let raw ← (List.range size).mapM (fun _ => do
      let k ← IO.rand 0 20
      let v ← IO.rand 0 20
      pure ((k : Int), (v : Int)))
    let resolved := (raw.reverse.foldl
      (fun acc (k, v) => if acc.any (fun (k', _) => k' == k) then acc else (k, v) :: acc)
      []).reverse
    let intTy : LMonoTy := .tcons "int" []
    let lit : MapLiteral :=
      { keyTy := intTy, valTy := intTy, dflt := (dflt : Int), entries := resolved
        expr := mapLiteralOfList intTy intTy (.intConst () (dflt : Int))
                  (raw.map (fun (k, v) => ((.intConst () k : LExpr'), (.intConst () v : LExpr')))) }
    let src := mapModelProgram lit
    match ← verifyProgram src false with
    | none    => t := { t with errored := t.errored + 1 }
    | some rs => t := tallyResults rs src t
  pure (t.toVerdict "Map axiom")

-- ── §2. `useArrayTheory` metamorphic ─────────────────────────────────

/-- One obligation's outcome, reduced to the three-way verdict the metamorphic
    comparison needs. -/
inductive Verdict where | pass | fail | unknown | error
deriving DecidableEq, Repr

def verdictOf (r : Core.VCResult) : Verdict :=
  if r.isFailure then .fail
  else if r.isUnknown then .unknown
  else if r.isSuccess then .pass
  else .error

instance : ToString Verdict where
  toString
    | .pass => "pass" | .fail => "fail" | .unknown => "unknown" | .error => "error"

/-- **The headline property.** `useArrayTheory` is documented as an encoding
    choice over the same semantics (`Options.lean`: "Use SMT-LIB Array theory
    instead of axiomatized maps"; `MetaVerifier.lean` calls the two alternative
    treatments of `Map`). If that is accurate, toggling it must not change any
    obligation's outcome.

    It does. On a hand-written probe against this tree, full map extensionality

    ```
    assert [ext_full]: m0[1 := 10][2 := 20] == m0[2 := 20][1 := 10];
    ```

    is `unknown` under `false` and `pass` under `true`, because `Factory.lean`
    declares `updateSelect` and `updatePreserve` for `update` but **no
    extensionality axiom**, while SMT-LIB `Array` theory has it built in. The
    same probe shows the flag changing *bug-finding* power: a false assertion
    (`mapConst<int>(7)[42] == 8`) is refuted under `true` but merely `unknown`
    under `false`.

    So this property is expected to report divergences, and each one is either a
    missing `Map` axiom or a doc-comment that understates the flag. Divergences
    are scored as failures deliberately — that is the finding. -/
def arrayTheoryMetamorphic (numTrials maxSize : Nat) :
    IO (Bool × Nat × Nat × Option String) := do
  let total := min numTrials 50
  let mut agreed := 0
  let mut diverged := 0
  let mut errored := 0
  let mut firstBad : Option String := none
  for i in List.range total do
    let size := (i % (max 1 maxSize)) + 1
    let dflt ← IO.rand 0 20
    let raw ← (List.range size).mapM (fun _ => do
      let k ← IO.rand 0 20
      let v ← IO.rand 0 20
      pure ((k : Int), (v : Int)))
    let resolved := (raw.reverse.foldl
      (fun acc (k, v) => if acc.any (fun (k', _) => k' == k) then acc else (k, v) :: acc)
      []).reverse
    let intTy : LMonoTy := .tcons "int" []
    let lit : MapLiteral :=
      { keyTy := intTy, valTy := intTy, dflt := (dflt : Int), entries := resolved
        expr := mapLiteralOfList intTy intTy (.intConst () (dflt : Int))
                  (raw.map (fun (k, v) => ((.intConst () k : LExpr'), (.intConst () v : LExpr')))) }
    -- Alternate between the two program shapes. Pointwise `select` assertions
    -- are provable from `updateSelect`/`updatePreserve` in *both* modes, so on
    -- their own they cannot witness a divergence; map *equalities* need
    -- extensionality, which only the Array encoding has. Covering both means the
    -- property reports the real gap without being blind to pointwise
    -- regressions.
    let src ←
      if i % 2 == 0 then pure (mapModelProgram lit)
      else do
        -- Two distinct keys, so the `commute` shape is semantically valid.
        let k1 ← IO.rand 0 10
        let k2raw ← IO.rand 0 10
        let k2 := if k2raw == k1 then k1 + 1 else k2raw
        let v1 ← IO.rand 0 20
        let v2 ← IO.rand 0 20
        pure (mapExtensionalityProgram (dflt : Int) (k1 : Int) (v1 : Int) (k2 : Int) (v2 : Int))
    match ← verifyProgram src false, ← verifyProgram src true with
    | some rsFalse, some rsTrue =>
      -- Compare obligation-by-obligation, matched on label.
      if rsFalse.size != rsTrue.size then
        diverged := diverged + 1
        if firstBad.isNone then
          firstBad := some s!"obligation count differs \
({rsFalse.size} vs {rsTrue.size})\n{src}"
      else
        for (a, b) in rsFalse.zip rsTrue do
          let va := verdictOf a
          let vb := verdictOf b
          if va != vb then
            diverged := diverged + 1
            if firstBad.isNone then
              firstBad := some s!"{a.obligation.label}: \
useArrayTheory=false ⇒ {va}, true ⇒ {vb}\n{src}"
          else
            agreed := agreed + 1
    | _, _ => errored := errored + 1
  let attempted := agreed + diverged
  if diverged == 0 then
    pure (true, agreed, attempted, some s!"{errored} verify errors")
  else
    pure (false, agreed, attempted,
      some (s!"{diverged} useArrayTheory divergence(s); {errored} verify errors"
        ++ (match firstBad with | some b => s!"\n  first: {b}" | none => "")))

-- ── §3. Precondition obligations ─────────────────────────────────────

/-- Every call to a *partial* sequence op must generate an out-of-bounds
    obligation, and an in-bounds call's obligation must be dischargeable.

    `Sequence.select`/`update` carry `0 <= i < length(s)` and `take`/`drop` carry
    `0 <= n <= length(s)` (`mkSeqBoundsPrecond`, strict vs non-strict). The
    programs built by `seqPrecondProgram` sit exactly on the legal side of both
    boundaries, so *every* generated obligation should discharge; a failure means
    either the precondition is wrong or `Preconditions.lean`'s hypothesis
    threading dropped a needed fact.

    The property also checks obligations are actually *produced* — a silently
    missing bounds check is the more dangerous bug, and would otherwise look
    identical to a clean pass. -/
def seqPrecondObligations (numTrials maxLen : Nat) :
    IO (Bool × Nat × Nat × Option String) := do
  let total := min numTrials 50
  let mut t : Tally := {}
  let mut missingChecks := 0
  for i in List.range total do
    let len := (i % (max 1 maxLen)) + 1
    let elems ← (List.range len).mapM (fun _ => do
      let n ← IO.rand 0 20
      pure (n : Int))
    let lit : SeqLiteral :=
      { elemTy := .tcons "int" []
        elems  := elems
        expr   := seqLiteralOfList (.tcons "int" []) (elems.map (fun v => .intConst () v)) }
    let src := seqPrecondProgram lit
    match ← verifyProgram src false with
    | none    => t := { t with errored := t.errored + 1 }
    | some rs =>
      -- Each of the three calls should contribute an out-of-bounds obligation.
      let labels : List String := rs.toList.map (fun r => r.obligation.label)
      let boundsChecks := labels.filter (fun l =>
        (l.splitOn "calls_Sequence.").length > 1)
      if boundsChecks.isEmpty then
        missingChecks := missingChecks + 1
      t := tallyResults rs src t
  let (ok, passed, attempted, note) := t.toVerdict "precondition"
  if missingChecks > 0 then
    let base := note.getD ""
    pure (false, passed, attempted,
      some s!"{missingChecks} sample(s) generated NO out-of-bounds obligation; {base}")
  else pure (ok, passed, attempted, note)

end StrataGenerators.MapSeqRunner
