import StrataGenerators.Test
import StrataGenerators.MonomorphizeFns

open Core
open StrataGenerators.Test
open StrataGenerators.Mono
open StrataGenerators.ProgramTuning

@[strata_properties]
def monoProperties : List TestDecl :=
    family GenProgram
        -- The pass either returns or raises a diagnostic; scored once, here, so that a
        -- diagnostic cannot quietly make every property below vacuous.
        [ ("mono: the pass returns a program", fun gp => checkMonoSucceeds gp.prog),
        -- Group A — upstream's three goldens, quantified, plus idempotence.
        ("mono: no top-level function keeps its type parameters",
            fun gp => checkMonoAllFuncsMonomorphic gp.prog),
        ("mono: no factory entry keeps its type parameters",
            fun gp => checkMonoFactoryMonomorphic gp.prog),
        ("mono: output of monomorphization typechecks", fun gp => checkMonoOutputTypechecks gp.prog),
        ("mono: monomorphization pass is idempotent", fun gp => checkMonoIdempotent gp.prog),
        -- The statement-level funcDecl, and its unrestricted form.
        ("mono: a statement-declared body's references are rewritten",
            fun gp => checkMonoStmtFuncDeclRefsRewritten gp.prog),
        ("mono: no reference to a dropped polymorphic original survives",
            fun gp => checkMonoNoPolyRefsSurvive gp.prog),
        -- Type declarations: specialized only through their derived functions.
        ("mono: type declarations pass through unchanged",
            fun gp => checkMonoTypeDeclsUnchanged gp.prog),
        ("mono: a polymorphic datatype is still polymorphic after the pass",
            fun gp => checkMonoPolyDatatypesRemain gp.prog),
        ("mono: a polymorphic datatype's derived functions are rewritten",
            fun gp => checkMonoDerivedOpsRewritten gp.prog),
        -- Group C — the naming convention, at program level.
        ("mono: every specialization's base name was polymorphic in the input",
            fun gp => checkMonoMangledBaseWasPolymorphic gp.prog),
        ("mono: the output declares no name twice",
            fun gp => checkMonoOutputNamesNodup gp.prog),
        ("mono: a program with no polymorphic function is unchanged",
            fun gp => checkMonoNoPolyProgramUnchanged gp.prog),
        ("mono: the declarations the pass does not add keep their order",
            fun gp => checkMonoDeclOrderPreserved gp.prog),
        -- Semantics preservation, modulo the naming convention.
        ("mono: evaluation agrees before and after the pass",
            fun gp => checkMonoEvalAgreement gp.prog) ]

/-- The three specialization properties, checked a second time under a distribution that makes a
    polymorphic function common. `MonomorphizeFunctions` is the identity on a program that declares
    none, and then each of these three holds for a reason that has nothing to do with the pass.
    `progPolyHeavy` takes the rate of such a program from 63% to 82%.

    `mono: a program with no polymorphic function is unchanged` is deliberately absent. It wants the
    opposite input, and this weighting would make it vacuous. -/
@[strata_properties]
def monoPolyHeavyProperties : List TestDecl :=
    (family GenProgram
        [ ("mono: a statement-declared body's references are rewritten",
            fun gp => checkMonoStmtFuncDeclRefsRewritten gp.prog),
        ("mono: no reference to a dropped polymorphic original survives",
            fun gp => checkMonoNoPolyRefsSurvive gp.prog),
        ("mono: every specialization's base name was polymorphic in the input",
            fun gp => checkMonoMangledBaseWasPolymorphic gp.prog) ]).flatMap
      (TestDecl.underTuningsOf [("poly-heavy", progPolyHeavy)])

/-- The two datatype properties, under the weighting that makes a polymorphic datatype common
    (44% to 82%). These need a different profile from the three above: a declaration is a function
    or a datatype block, so raising one rate lowers the other. -/
@[strata_properties]
def monoDatatypeHeavyProperties : List TestDecl :=
    (family GenProgram
        [ ("mono: a polymorphic datatype is still polymorphic after the pass",
            fun gp => checkMonoPolyDatatypesRemain gp.prog),
        ("mono: a polymorphic datatype's derived functions are rewritten",
            fun gp => checkMonoDerivedOpsRewritten gp.prog) ]).flatMap
      (TestDecl.underTuningsOf [("datatype-heavy", progDatatypeHeavy)])
