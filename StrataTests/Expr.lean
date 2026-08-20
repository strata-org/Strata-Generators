import StrataGenerators.Test
import StrataGenerators.TycheViz
import StrataGenerators.HasTypeAGen.SmtStringEscaping
import StrataGenerators.HasTypeAGen.DecimalAgreement

/-!
# Expression-generator properties

Type safety of `LExpr.eval` (`Strata.DL.Lambda.LExprEval`) and soundness of the
expression generator. The first two correspond to the standard type-safety
theorems; the rest exercise the fuel-bounded evaluator, following the theorems of
`Strata.DL.Lambda.Semantics`.

Two theorems there are deliberately not covered:

* `eval_StepStar` — soundness with respect to the small-step relation `Step`. The
  existential witness (`∃ e', StepStar … e e'`) would need a search for a reachable
  expression; idempotence, monotonicity and preservation together stand in for it.
* `eval_eraseMetadata_invariant` — invariance under metadata changes. Our metadata
  type is `Unit`, so `eraseMetadata` is the identity (proved in
  `LExprEvalTests.lean`) and the property holds trivially.
-/

open Lambda Core Imperative
open StrataGenerators.Test

/-- Soundness of the generator: every generated expression typechecks at the type it
    was generated for. Holds for open as well as closed terms, since `HasTypeA`
    trusts fvar annotations. -/
@[strata_property]
def exprTypecheck : TestDecl :=
  .property "expr: generated terms typecheck" "expr" Gens.typedExpr
    (fun te => LExpr.typeCheck (T := LExprParams') [] te.expr == some te.ty)

/-- Preservation, on closed terms: if `∅ ⊢ e : τ` and `e →* e'` then `∅ ⊢ e' : τ`. -/
@[strata_property]
def exprPreservation : TestDecl :=
  (TestDecl.property "expr: preservation under eval (closed)" "expr" Gens.closedExpr
    (fun te => checkPreservation te.expr te.ty)).withPanel genAndEval

/-- Progress, on closed terms: a well-typed closed term is a value or can step.

    Falsified by quantifiers: `LExpr.eval` has no reduction rule for `∀`/`∃`, so
    `if (∀x. e) then …` gets stuck. -/
@[strata_property]
def exprProgress : TestDecl :=
  (TestDecl.property "expr: progress (closed)" "expr" Gens.closedExpr
    (fun te => checkProgress te.expr)).withPanel genAndCheckProgress

/-- Evaluation introduces no *new* free variables. Variables already in the context
    may appear in the input and the output; eval may not invent one. -/
@[strata_property]
def exprFvarsPreserved : TestDecl :=
  (TestDecl.property "expr: eval preserves fvars" "expr" Gens.typedExpr
    (fun te => checkFvarsPreserved te.expr)).withPanel genAndCheckFvarPreservation

/-- After erasing *all* type annotations, `resolve` infers a principal type of which
    the original is a substitution instance (a fully-erased `λx. x` resolves to
    `?a -> ?a`, of which `int -> int` is an instance) — so the check is the instance
    relation, not syntactic equality.

    `resolve` may legitimately *fail* on a fully-erased quantifier whose body type is
    exactly the bound variable (`∃x. x`): with the binder annotation gone it assigns
    a fresh type variable `?a`, infers the body's type as `?a`, and rejects the
    quantifier because its rule checks the body type is literally `bool` rather than
    unifying it with `bool`. That is an incompleteness of `resolve` on erased
    quantifiers rather than a soundness violation, so resolve-failure counts as a
    vacuous pass. The `expr: resolve` diagnostic prints the error messages behind
    any counterexamples. -/
@[strata_property]
def exprResolveAfterErase : TestDecl :=
  (TestDecl.property "expr: resolve after type erasure" "expr" Gens.resolveExpr
    (fun te => checkResolveAfterErase te.expr te.ty)).withPanel
    genAndCheckResolveAfterErase

/-- Every SMT string literal Strata emits is printable ASCII.

    This needs no solver: the oracle is SMT-LIB 2.6's own requirement on string
    literals. It is non-vacuous only because `genInterestingString` draws non-ASCII
    characters — under Basalt's alphanumeric `String.arbitrary` it would not be. -/
@[strata_property]
def exprSmtStringEscaping : TestDecl :=
  (TestDecl.action "expr: SMT string literals are printable ASCII" "expr"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.SmtStringEscaping.escapingAction cfg.numTrials)).withPanel
    genEscapingSample

/-- The `Rat`/`Decimal` boundary in the SMT dialect: folding an equality of two
    spellings of one value agrees with equality of the values. Needs no solver — it
    is an invariant of a pure function. Non-vacuous only because the generator builds
    a *second spelling* of one value; two independent draws are almost never equal. -/
@[strata_property]
def realDecimalEqFold : TestDecl :=
  (TestDecl.action "real: Decimal eq fold agrees with value equality" "expr"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.DecimalAgreement.eqFoldAction cfg.numTrials)).withPanel
    (genDecimalPairProp StrataGenerators.DecimalAgreement.checkEqFold)

/-- The `Decimal` comparator is a total order. -/
@[strata_property]
def realDecimalTrichotomy : TestDecl :=
  (TestDecl.action "real: Decimal comparator is a total order" "expr"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.DecimalAgreement.trichotomyAction cfg.numTrials)).withPanel
    (genDecimalPairProp StrataGenerators.DecimalAgreement.checkTrichotomy)

/-- Symbolic/concrete evaluation agreement on closed terms, discharged by a real
    solver. Gated on `--smt`, since it needs a live `cvc5`/`z3` on `PATH`. Ported
    from `StrataTest/Languages/Core/Tests/ExprEvalTest.lean`. -/
@[strata_property]
def exprSmtEvalAgreement : TestDecl :=
  TestDecl.action "expr: SMT/concrete eval agreement (closed)" "expr"
    (fun cfg => ActionResult.ofTuple <$>
      StrataGenerators.SmtEval.smtEvalAgreementAction cfg.numTrials cfg.maxSize)
    (gate := some "smt")
