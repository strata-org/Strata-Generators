import StrataGenerators.Test
import StrataGenerators.MonomorphizeFns

open Core
open StrataGenerators.Test
open StrataGenerators.Mono

@[strata_properties]
def monoProperties : List TestDecl :=
    family GenProgram
        -- The pass gives a program, or it raises a diagnostic. One property scores that choice, here, so that a
        -- diagnostic cannot silently empty each property below.
        [ ("mono: the pass returns a program", fun gp => checkMonoSucceeds gp.prog),
        -- The three claims of the tests of Strata, over the generator, together with idempotence.
        ("mono: no top-level function keeps its type parameters",
            fun gp => checkMonoAllFuncsMonomorphic gp.prog),
        ("mono: no factory entry keeps its type parameters",
            fun gp => checkMonoFactoryMonomorphic gp.prog),
        ("mono: output of monomorphization typechecks", fun gp => checkMonoOutputTypechecks gp.prog),
        ("mono: monomorphization pass is idempotent", fun gp => checkMonoIdempotent gp.prog),
        -- The `funcDecl` statement, and the form of that claim with no restriction.
        ("mono: a statement-declared body's references are rewritten",
            fun gp => checkMonoStmtFuncDeclRefsRewritten gp.prog),
        ("mono: no reference to a dropped polymorphic original survives",
            fun gp => checkMonoNoPolyRefsSurvive gp.prog),
        -- A type declaration changes only through the functions that it derives.
        ("mono: type declarations pass through unchanged",
            fun gp => checkMonoTypeDeclsUnchanged gp.prog),
        ("mono: a polymorphic datatype is still polymorphic after the pass",
            fun gp => checkMonoPolyDatatypesRemain gp.prog),
        ("mono: a polymorphic datatype's derived functions are rewritten",
            fun gp => checkMonoDerivedOpsRewritten gp.prog),
        -- The convention for a name, at the level of a program.
        ("mono: every specialization's base name was polymorphic in the input",
            fun gp => checkMonoMangledBaseWasPolymorphic gp.prog),
        ("mono: the output declares no name twice",
            fun gp => checkMonoOutputNamesNodup gp.prog),
        ("mono: a program with no polymorphic function is unchanged",
            fun gp => checkMonoNoPolyProgramUnchanged gp.prog),
        ("mono: the declarations the pass does not add keep their order",
            fun gp => checkMonoDeclOrderPreserved gp.prog),
        -- The preservation of the semantics, which ignores the convention for a name.
        ("mono: evaluation agrees before and after the pass",
            fun gp => checkMonoEvalAgreement gp.prog) ]
