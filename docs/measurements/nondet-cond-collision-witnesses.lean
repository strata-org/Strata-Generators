import StrataGenerators.TestScaffold
import StrataGenerators.ProgramGen.UnprovenTransforms

open Plausible
open Lambda Core Imperative
open Strata Strata.CoreDDM
open StrataGenerators
open StrataGenerators.Program.TestSupport
open StrataGenerators.Procedure.TestSupport
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Program.UnprovenTransforms

/-! How often does a *randomly generated* well-typed program hit the evaluator's
    `$__nondet_cond_` collision (repo issue #113,
    `docs/strata-symbolic-eval-nondet-collision.md`)?

    The `#guard`s in `ProgramGen/UnprovenTransforms` pin the defect on hand-built
    input, and `checkNondetElimSymbolicNoLoss` passes on generated input — it is a
    *containment* claim, and this defect makes the obligation set grow, so the
    property cannot report it. This script asks the question the property cannot:
    on how many generated draws does the evaluator actually drop something?

    The oracle is `NondetElim`: all it does is replace every `if *` with a havoc of
    its own monotonically-counted variable, so it cannot *add* an obligation. If
    running it makes the obligation set grow, the evaluator dropped one.

    Each witness is then minimized with the repository's own whole-program
    shrinker, which re-runs `Program.typeCheck` on every candidate, so the reported
    witness is small *and* well-typed.

    Measured over two independent runs. The search stops at the third witness, so
    the denominator is "draws needed to find three" and not a fixed sample: three
    witnesses appeared within the first 2241 and 1172 typechecking draws
    respectively, i.e. very roughly one draw in 400-750.

    In every witness of both runs the baseline emitted **zero** obligations, so what
    is lost is not a fraction of the program's proof burden but all of it. Two are
    worth naming:

    * `ensures [post]: false` plus two empty `if *` — unverifiable by construction,
      nothing to check. This is the shape the `#guard`s in
      `ProgramGen/UnprovenTransforms` now pin.
    * two empty `if *` followed by a `while` carrying two invariants and a
      `decreases` clause: all **six** of its verification conditions (two entry, two
      maintain, measure lower bound, measure decrease) disappear together, even
      though that loop's own guard is deterministic.

    Run: `lake env lean --run docs/measurements/nondet-cond-collision-witnesses.lean` -/

def pp (p : Program) : String := (Core.formatProgram p).pretty

/-- The evaluator dropped an obligation on `p` iff removing every `if *` — which is
    all `NondetElim` does — recovers one the baseline never emitted. Both sides run
    the production chain `InsertLoopInvariantAsserts` then `LoopElim`, since the
    evaluator refuses a loop. -/
def dropsObligation (p : Program) : Bool :=
  progTypeChecks p && !hasNondetMeasureLoop p &&
    (match vcElimObligationLabels p, vcElimObligationLabels (nondetElimProgram p) with
     | some before, some after => after.length > before.length
     | _, _ => false)

def report (tag : String) (p : Program) : IO Unit := do
  let before := vcElimObligationLabels p
  let after := vcElimObligationLabels (nondetElimProgram p)
  IO.println s!"--- {tag} (size {sizeProgram p})"
  IO.println (pp p)
  IO.println s!"    obligations WITHOUT NondetElim: count={(before.map (·.length))} labels={before}"
  IO.println s!"    obligations WITH    NondetElim: count={(after.map (·.length))} labels={after}"

def main : IO Unit := do
  let trials := 6000
  let maxSize := 30
  let mut found := 0
  let mut scanned := 0
  for i in List.range trials do
    if found ≥ 3 then continue
    let size := i % (maxSize + 1)
    let gp ← try Gen.run (Arbitrary.arbitrary (α := GenProgram)) size
             catch _ => pure ⟨{ decls := [] }⟩
    if gp.prog.decls.isEmpty then continue
    if !progTypeChecks gp.prog then continue
    scanned := scanned + 1
    if !dropsObligation gp.prog then continue
    found := found + 1
    IO.println ""
    IO.println s!"################ witness {found} (draw {i}, size param {size})"
    let small := minimizeProgramWhile dropsObligation 200 gp.prog
    report "SHRUNK witness" small
    IO.println s!"    (the original draw had size {sizeProgram gp.prog})"
  IO.println ""
  IO.println s!"scanned {scanned} typechecking draws; {found} lose obligations"
