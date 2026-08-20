import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Function-generator properties

Soundness and completeness of `Function.typeCheck`, type preservation of a function
body under evaluation, and the format→parse round-trip.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Stmt.TestSupport

/-- Every free variable in a generated function's body and measure is annotated
    consistently with the type map derived from the fvar context it was generated
    against. Holds because `pickFVar` always emits `fvar` nodes annotated with
    `some τ`, for exactly the `τ` the variable carries in the context. -/
@[strata_property]
def fnFvarsAnnotated : TestDecl :=
  (TestDecl.forAll "function: fvars annotated by context type map" "function"
    (fun (gf : GenFunction) => functionFvarsAnnotatedBy (fctxToTyMap gf.fctx) gf.func)).withPanel
    genAndCheckFunctionFvarsAnnotated

/-- `Function.typeCheck_annotated_sound`, the `sorry`'d theorem at
    `Strata/Languages/Core/FunctionTypeSpecSound.lean`: if
    `Function.typeCheck C Env func = .ok (func', _)` then `func'` satisfies
    `FuncHasTypeA C Γ` for any `Γ`. -/
@[strata_property]
def fnTypeCheckSound : TestDecl :=
  (TestDecl.forAll
    "function: typeCheck output satisfies FuncHasTypeA (typeCheck_annotated_sound)"
    "function"
    (fun (gf : ClosedGenFunction) => checkTypeCheckAnnotatedSound gf.func)).withPanel
    genAndCheckFunctionTypeCheckSound

/-- Type preservation of a function body under evaluation — `Step.type_preserved` /
    `StepStar.type_preserved` / `eval_denote_sound`. -/
@[strata_property]
def fnBodyPreservation : TestDecl :=
  (TestDecl.forAll "function: body type preserved under eval" "function"
    (fun (gf : ClosedGenFunction) => checkFunctionBodyPreservation gf.func)).withPanel
    genAndCheckFunctionBodyPreservation

/-- Completeness, dual to soundness above: `genFunction` is proven sound (its output
    satisfies `FuncHasType'`), so `Function.typeCheck` should accept every generated
    function. It does not — the spec permits a measure without a body, and the
    algorithm rejects it. Asserted unweakened, so the gap is reported rather than
    masked. The `funcDecl` gap in the statement suite is the syntactic-statement
    analogue of exactly this. -/
@[strata_property]
def fnTypeCheckComplete : TestDecl :=
  (TestDecl.forAll "function: typeCheck accepts generated functions (completeness)"
    "function"
    (fun (gf : ClosedGenFunction) => checkFunctionTypeCheckerComplete gf.func)).withPanel
    genAndCheckFunctionTypeCheckComplete

/-- Every `typeCheck` rejection is a measure-without-body function. This is what
    pins the sole known completeness gap: were a *second* cause to appear, this goes
    red while the property above stays red for the same reason it already was. -/
@[strata_property]
def fnRejectionOnlyMeasure : TestDecl :=
  .forAll "function: typeCheck rejections are only measure-without-body" "function"
     (fun (gf : ClosedGenFunction) => funcRejectionImpliesMeasureNoBody gf.func)

/-- Pretty-print → parse → re-print is a fixed point.

    A self-driving action rather than a sampled property: it shrinks its own
    counterexamples and prints minimal reproducers as it goes, distinguishing a parse
    failure from a re-print mismatch. A parse failure is scored as a *failure*, not a
    vacuous pass — `genIdentName` produces only legal Core identifiers, so output that
    does not parse back means the printer emitted legal-but-unparseable text. -/
@[strata_property]
def fnRoundtrip : TestDecl :=
  (TestDecl.action "function: pretty-print/parse round-trip" "function"
    (fun cfg => ActionResult.ofTuple <$>
      roundtripFunctionAction cfg.numTrials cfg.maxSize)).withPanel
    genAndCheckFunctionRoundtrip
