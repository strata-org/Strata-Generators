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

    It does not accept all of them. The specification allows a measure on any function and an
    open polymorphic instance, and the algorithm rejects a measure on a function that is not
    recursive and an instance whose type nothing fixes. This property treats a rejection with
    either message as a known gap, and fails on any other rejection. Its panel records the
    plain verdict of the checker. -/
@[strata_property]
def fnTypeCheckComplete : TestDecl :=
  (TestDecl.property "function: typeCheck accepts generated functions (completeness)"
    (fun (gf : ClosedGenFunction) => checkFunctionTypeCheckerCompleteUpToGaps gf.func)).withPanel
    genAndCheckFunctionTypeCheckComplete

/-- Each function that `Function.typeCheck` rejects has a known cause: a measure with no body
    or no recursive call, or an open polymorphic instance. This property pins the known gaps in
    completeness, and it finds a new cause if one appears. -/
@[strata_property]
def fnRejectionOnlyMeasure : TestDecl :=
  .property "function: typeCheck rejections are only the known gaps"
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
