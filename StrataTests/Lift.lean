import StrataGenerators.Test

/-!
# `LiftInternalFuncDecls`: lambda lifting with capture at the declaration site

Each property puts an internal function that *captures* a variable into the generated
program. `genFuncDeclStmt` draws its bodies with `genFunction []`, so a generated
`funcDecl` is always closed and the pass finds nothing to capture. Each property then
sweeps the fifteen shapes of `LiftFuncDecls.allScenarios`.

Upstream proves only `run_noFuncDecl`, which is the property `lift: no procedure body
holds a funcDecl`. The other twelve claims have no proof.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.LiftFuncDecls

/-- The thirteen properties of `LiftInternalFuncDecls`.

    The first property gives coverage, and it makes no claim about the pass. It scores
    that the pass really lifted the function that the property put into the program.
    Without it, a draw that the pass refuses can make the other twelve properties vacuous,
    and nothing reports this. -/
@[strata_properties]
def liftFuncDecls : List TestDecl :=
  family GenProgram
    [ -- The coverage property comes first. The other properties mean nothing without it.
      ("lift: the injected declaration is really lifted",
       fun gp => checkLiftInjectionFires gp.prog),
      -- P1: closedness, which is the reason for the pass
      ("lift: every hoisted function is closed",
       fun gp => checkLiftAllFuncsClosed gp.prog),
      ("lift: every function satisfies LFuncClosed",
       fun gp => checkLiftStrataClosed gp.prog),
      -- P2, P3 and P4: the traversal
      ("lift: no procedure body holds a funcDecl",
       fun gp => checkLiftNoResidualFuncDecl gp.prog),
      ("lift: the pass is idempotent",
       fun gp => checkLiftIdempotent gp.prog),
      ("lift: a funcDecl-free program is unchanged",
       fun gp => checkLiftIdentityWithoutFuncDecl gp.prog),
      -- P5 and P10: the signature that the pass emits
      ("lift: the captured parameters lead",
       fun gp => checkLiftParamsLead gp.prog),
      ("lift: no hoisted function has a free type var",
       fun gp => checkLiftTypeArgsClosed gp.prog),
      -- P6 and P7: name hygiene and correctness of the scope. A `.knownFailure` mark
      -- gives the defect that each of the two properties finds.
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
      -- P8: the Johnsson fixpoint against a separate implementation of Definition 4.6
      ("lift: the fixpoint matches Def 4.6",
       fun gp => checkLiftFixpointMatchesReference gp.prog),
      -- P12: completeness of the rejections
      ("lift: only the documented triggers are rejected",
       fun gp => checkLiftRejectsOnlyKnownTriggers gp.prog) ]
