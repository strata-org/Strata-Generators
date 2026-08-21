import StrataGenerators.Test

/-!
# `LiftInternalFuncDecls` — lambda lifting with declaration-site capture

Each property injects a *capturing* internal function into the generated program —
`genFuncDeclStmt` draws its bodies with `genFunction []`, so a generated `funcDecl`
is always closed and the pass would have nothing to capture — and sweeps the fifteen
shapes of `LiftFuncDecls.allScenarios`.

Only `LiftInternalFuncDeclsCorrect.lean`'s `run_noFuncDecl` is proved upstream (that
is `lift: no procedure body holds a funcDecl`); the other twelve claims are unproved.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.LiftFuncDecls

/-- The thirteen `LiftInternalFuncDecls` properties.

    The first is coverage rather than a claim about the pass: it scores that the
    injection really *was* lifted, so a draw the pass refuses cannot leave the other
    twelve vacuous in silence — which it did, on 5 of 20 draws, before
    `normalizeAmbient`. -/
@[strata_properties]
def liftFuncDecls : List TestDecl :=
  family GenProgram
    [ -- coverage first: the rest mean nothing without it
      ("lift: the injected declaration is really lifted",
       fun gp => checkLiftInjectionFires gp.prog),
      -- P1 — closedness, the property the pass exists for
      ("lift: every hoisted function is closed",
       fun gp => checkLiftAllFuncsClosed gp.prog),
      ("lift: every function satisfies LFuncClosed",
       fun gp => checkLiftStrataClosed gp.prog),
      -- P2/P3/P4 — the traversal
      ("lift: no procedure body holds a funcDecl",
       fun gp => checkLiftNoResidualFuncDecl gp.prog),
      ("lift: the pass is idempotent",
       fun gp => checkLiftIdempotent gp.prog),
      ("lift: a funcDecl-free program is unchanged",
       fun gp => checkLiftIdentityWithoutFuncDecl gp.prog),
      -- P5/P10 — the emitted signature
      ("lift: the captured parameters lead",
       fun gp => checkLiftParamsLead gp.prog),
      ("lift: no hoisted function has a free type var",
       fun gp => checkLiftTypeArgsClosed gp.prog),
      -- P6/P7 — name hygiene and scope correctness (the two defects). Both are marked
      -- known failures: each fails reliably at the default trial count, so neither
      -- gates the exit code and neither prints a counterexample. `lift: the output
      -- typechecks` is deliberately *not* marked — it holds on the current pass, and
      -- marking it would fail the run.
      ("lift: the minted snapshot names are fresh",
       fun gp => checkLiftFreshSnapshotNames gp.prog,
       .knownFailure "reported upstream: `StringGenState.gen` is a bare counter, so a \
minted snapshot name can collide with a name already in the program"),
      ("lift: the output typechecks",
       fun gp => checkLiftOutputTypechecks gp.prog),
      ("lift: every snapshot is used in scope",
       fun gp => checkLiftSnapshotsInScope gp.prog,
       .knownFailure "reported upstream: a snapshot can be emitted outside the scope \
that uses it"),
      -- P8 — the Johnsson fixpoint against an independent Def 4.6 implementation
      ("lift: the fixpoint matches Def 4.6",
       fun gp => checkLiftFixpointMatchesReference gp.prog),
      -- P12 — rejection completeness
      ("lift: only the documented triggers are rejected",
       fun gp => checkLiftRejectsOnlyKnownTriggers gp.prog) ]
