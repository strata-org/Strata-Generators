import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Properties of the command generator

Four properties give one verdict about one generated command. Two more properties have a
different shape. The property for the growth of the context quantifies over a *sequence* of
commands. The property for the agreement of symbolic and concrete evaluation has a larger
panel of its own.
-/

open Lambda Core Imperative
open StrataGenerators.Test

/-- The four command properties that give one verdict. Each property receives a command
    and the context that the generator used for it. The first two properties ignore the
    context. -/
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
    (TestDecl.property name (fun gc => check gc = true)).withPanel
      (genCmdProp (fun c ctx => check ⟨c, ctx, cmdOutCtx ctx c⟩))

/-- For a generated sequence of commands, the output context is the input context and the
    new variables. The new variables come first, in reverse order, because `init` adds each
    variable to the front. -/
@[strata_property]
def cmdContextGrowth : TestDecl :=
  .property "cmd: context growth matches inits"
    (fun (gc : GenCmdsWithCtx) => checkContextGrowth gc.inCtx gc.outCtx gc.cmds)

/-- If concrete execution with `Cmd.run` succeeds, then symbolic simulation with
    `Cmd.eval` also succeeds and it gives the same store. -/
@[strata_property]
def cmdEvalRunAgreement : TestDecl :=
  (TestDecl.property "cmd: symbolic/concrete eval agreement"
    (fun (gc : GenCmdWithCtx) => checkEvalRunAgreement gc.cmd gc.inCtx)).withPanel
    genAndCheckEvalRunAgreement
