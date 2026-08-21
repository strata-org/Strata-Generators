import StrataGenerators.Test
import StrataGenerators.TycheViz
import StrataGenerators.HasTypeAGen.SmtStringEscaping
import StrataGenerators.HasTypeAGen.DecimalAgreement

/-!
# Properties of the expression generator

These properties cover the type safety of `LExpr.eval` and the soundness of the
expression generator. The first two properties are the standard type-safety theorems. The
other properties test the evaluator that a fuel bound limits, and they follow the
theorems of `Strata.DL.Lambda.Semantics`.

Two of those theorems have no property here:

* `eval_StepStar` gives soundness against the small-step relation `Step`. The existential
  witness `∃ e', StepStar … e e'` needs a search for an expression that `e` can reach.
  Idempotence, monotonicity and preservation together take the place of it.
* `eval_eraseMetadata_invariant` gives invariance under a change of the metadata. The
  metadata type of this package is `Unit`, so `eraseMetadata` is the identity function
  and the property is trivial.
-/

open Lambda Core Imperative
open StrataGenerators.Test

/-- Soundness of the generator: each expression that it makes typechecks at the type that
    it received. This holds for an open term and for a closed term, because `HasTypeA`
    trusts the annotation on a free variable. -/
@[strata_property]
def exprTypecheck : TestDecl :=
  .property "expr: generated terms typecheck"
    (fun (te : TypedExpr) => LExpr.typeCheck (T := LExprParams') [] te.expr == some te.ty)

/-- Preservation on a closed term: if `e` has the type `τ` in the empty context, and `e`
    evaluates to `e'`, then `e'` also has the type `τ`. -/
@[strata_property]
def exprPreservation : TestDecl :=
  (TestDecl.property "expr: preservation under eval (closed)"
    (fun (te : ClosedTypedExpr) => checkPreservation te.expr te.ty)).withPanel genAndEval

/-- Progress on a closed term: a closed term that is well-typed is a value, or it can
    take a step.

    `LExpr.eval` has no reduction rule for `∀` and no reduction rule for `∃`. Therefore a
    term such as `if (∀x. e) then …` can take no step. -/
@[strata_property]
def exprProgress : TestDecl :=
  (TestDecl.property "expr: progress (closed)"
    (fun (te : ClosedTypedExpr) => checkProgress te.expr)).withPanel genAndCheckProgress

/-- Evaluation adds no *new* free variable. A variable that is in the context can occur
    in the input and in the output, but evaluation must not add a variable. -/
@[strata_property]
def exprFvarsPreserved : TestDecl :=
  (TestDecl.property "expr: eval preserves fvars"
    (fun (te : TypedExpr) => checkFvarsPreserved te.expr)).withPanel genAndCheckFvarPreservation

/-- After the erasure of *all* type annotations, `resolve` infers a principal type, and
    the original type is a substitution instance of that type. For example, `resolve`
    gives the type `?a -> ?a` to a fully erased `λx. x`, and `int -> int` is an instance
    of that type. Therefore the check is the instance relation and not syntactic equality.

    `resolve` can also fail on a fully erased quantifier whose body type is the bound
    variable itself, such as `∃x. x`. Without the annotation on the binder, `resolve`
    gives the variable a fresh type variable `?a` and infers `?a` as the type of the body.
    It then rejects the quantifier, because the rule for a quantifier checks that the body
    type is literally `bool` and does not unify the body type with `bool`. This is an
    incompleteness of `resolve` and not a violation of soundness. Therefore a failure of
    `resolve` counts as a vacuous pass. The `expr: resolve` diagnostic prints the error
    messages of the counterexamples. -/
@[strata_property]
def exprResolveAfterErase : TestDecl :=
  (TestDecl.property "expr: resolve after type erasure"
    (fun (te : ResolveTypedExpr) => checkResolveAfterErase te.expr te.ty)).withPanel
    genAndCheckResolveAfterErase

/-- Each SMT string literal that Strata emits holds only printable ASCII characters.

    The property needs no solver, because the oracle is the rule for a string literal in
    SMT-LIB 2.6. The property is not vacuous, because `genInterestingString` draws
    characters that are not ASCII. -/
@[strata_property]
def exprSmtStringEscaping : TestDecl :=
  (TestDecl.action "expr: SMT string literals are printable ASCII"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.SmtStringEscaping.escapingAction cfg.numTrials)).withPanel
    genEscapingSample

/-- The boundary between `Rat` and `Decimal` in the SMT dialect. Two different forms can
    write one value. When the evaluator folds an equality of two such forms, the result
    agrees with the equality of the two values.

    The property needs no solver, because it is an invariant of a pure function. It is not
    vacuous, because the generator builds a *second form* of one value. Two independent
    draws are almost never equal. -/
@[strata_property]
def realDecimalEqFold : TestDecl :=
  (TestDecl.action "real: Decimal eq fold agrees with value equality"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.DecimalAgreement.eqFoldAction cfg.numTrials)).withPanel
    (genDecimalPairProp StrataGenerators.DecimalAgreement.checkEqFold)

/-- The comparator for `Decimal` gives a total order on values. -/
@[strata_property]
def realDecimalTrichotomy : TestDecl :=
  (TestDecl.action "real: Decimal comparator is a total order"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.DecimalAgreement.trichotomyAction cfg.numTrials)).withPanel
    (genDecimalPairProp StrataGenerators.DecimalAgreement.checkTrichotomy)

/-- Symbolic evaluation and concrete evaluation agree on a closed term. A solver
    discharges the obligation, so the `--smt` gate controls the property. The solver
    `cvc5` or `z3` must be on the `PATH`. -/
@[strata_property]
def exprSmtEvalAgreement : TestDecl :=
  TestDecl.action "expr: SMT/concrete eval agreement (closed)"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.SmtEval.smtEvalAgreementAction cfg.numTrials cfg.maxSize)
    (gate := some "smt")
