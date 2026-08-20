import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Command-generator properties

Four single-verdict claims about one generated command, plus two whose shape
differs: context growth quantifies over a command *sequence*, and symbolic/concrete
agreement has a richer panel of its own.
-/

open Lambda Core Imperative
open StrataGenerators.Test

/-- The four single-verdict command properties. Each takes a command paired with the
    context it was generated against; the first two ignore the context. -/
@[strata_properties]
def cmdSingleVerdict : List TestDecl :=
  [ ("cmd: init var not in RHS",
     fun (gc : GenCmdWithCtx) => checkInitFreshNotInRhs gc.cmd),
    ("cmd: expressions typecheck",
     fun gc => checkExprTypechecks gc.cmd),
    ("cmd: set preserves variable",
     fun gc => checkSetPreservesVar gc.cmd gc.inCtx),
    ("cmd: store type preservation under eval",
     fun gc => checkStoreTypePreservation gc.cmd gc.inCtx) ].map
  fun (name, check) =>
    (TestDecl.forAll name "cmd" check).withPanel
      (genCmdProp (fun c ctx => check ⟨c, ctx, cmdOutCtx ctx c⟩))

/-- For a generated command sequence, the output context is the input context with
    the newly defined variables prepended — in reverse order, since `init` conses
    onto the front. -/
@[strata_property]
def cmdContextGrowth : TestDecl :=
  .forAll "cmd: context growth matches inits" "cmd"
    (fun (gc : GenCmdsWithCtx) => checkContextGrowth gc.inCtx gc.outCtx gc.cmds)

/-- Whenever concrete execution (`Cmd.run`) succeeds, symbolic simulation
    (`Cmd.eval`) also succeeds, with the same store. -/
@[strata_property]
def cmdEvalRunAgreement : TestDecl :=
  (TestDecl.forAll "cmd: symbolic/concrete eval agreement" "cmd"
    (fun (gc : GenCmdWithCtx) => checkEvalRunAgreement gc.cmd gc.inCtx)).withPanel
    genAndCheckEvalRunAgreement
