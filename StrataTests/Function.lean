import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Properties of the function generator

These properties cover the soundness and the completeness of `Function.typeCheck`, the
preservation of the type of a function body under evaluation, and the round trip from
`format` to `parse`.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Stmt.TestSupport

/-- Each free variable in the body and in the measure of a generated function has an
    annotation that agrees with the type map of the context that the generator used. This
    holds because `pickFVar` always emits an `fvar` node with the annotation `some τ`, where
    `τ` is the type that the variable has in the context. -/
@[strata_property]
def fnFvarsAnnotated : TestDecl :=
  (TestDecl.property "function: fvars annotated by context type map"
    (fun (gf : GenFunction) => functionFvarsAnnotatedBy (fctxToTyMap gf.fctx) gf.func)).withPanel
    genAndCheckFunctionFvarsAnnotated

/-- Soundness of the type checker for a function: if `Function.typeCheck C Env func`
    returns `.ok (func', _)`, then `func'` satisfies the type relation `FuncHasTypeA C Γ`
    for every `Γ`. Upstream states this claim as `Function.typeCheck_annotated_sound`, and
    its proof there is a `sorry`. -/
@[strata_property]
def fnTypeCheckSound : TestDecl :=
  (TestDecl.property
    "function: typeCheck output satisfies FuncHasTypeA (typeCheck_annotated_sound)"
    (fun (gf : ClosedGenFunction) => checkTypeCheckAnnotatedSound gf.func)).withPanel
    genAndCheckFunctionTypeCheckSound

/-- Evaluation of a function body keeps the type of the body. Upstream states this claim as
    `Step.type_preserved`, `StepStar.type_preserved` and `eval_denote_sound`. -/
@[strata_property]
def fnBodyPreservation : TestDecl :=
  (TestDecl.property "function: body type preserved under eval"
    (fun (gf : ClosedGenFunction) => checkFunctionBodyPreservation gf.func)).withPanel
    genAndCheckFunctionBodyPreservation

/-- Completeness of the type checker for a function, which is the dual of its soundness.
    `genFunction` is sound, because its output satisfies `FuncHasType'`. Therefore
    `Function.typeCheck` must accept each generated function.

    It does not accept all of them. The specification lets a function have a measure and no
    body, and the algorithm rejects such a function. This property states the full claim, so
    it reports the gap and does not hide it. -/
@[strata_property]
def fnTypeCheckComplete : TestDecl :=
  (TestDecl.property "function: typeCheck accepts generated functions (completeness)"
    (fun (gf : ClosedGenFunction) => checkFunctionTypeCheckerComplete gf.func)).withPanel
    genAndCheckFunctionTypeCheckComplete

/-- Each function that `Function.typeCheck` rejects has a measure and no body. This property
    pins the one known gap in completeness, and it finds a *second* cause if one appears. -/
@[strata_property]
def fnRejectionOnlyMeasure : TestDecl :=
  .property "function: typeCheck rejections are only measure-without-body"
     (fun (gf : ClosedGenFunction) => funcRejectionImpliesMeasureNoBody gf.func)

/-- The sequence of pretty-print, parse and pretty-print again is a fixed point.

    This is an action and not a sampled property. It shrinks its own counterexamples, and it
    prints a small reproducer for each one. It also separates a failure of the parser from a
    difference between the two printed forms. A failure of the parser counts as a *failure*
    and not as a vacuous pass, because `genIdentName` makes only legal Core identifiers.
    Output that the parser rejects therefore means that the printer wrote legal text that no
    parser accepts. -/
@[strata_property]
def fnRoundtrip : TestDecl :=
  (TestDecl.action "function: pretty-print/parse round-trip"
    (fun cfg => ActionResult.ofTuple <$>
      roundtripFunctionAction cfg.numTrials cfg.maxSize)).withPanel
    genAndCheckFunctionRoundtrip
