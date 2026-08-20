import StrataGenerators.Test

/-!
# Whole-program-generator properties

`genProgram` produces a whole well-typed Core `Program` — every declaration kind,
with the ambient context threaded across the declaration fold — and is proven sound
against the declarative spec `ProgramHasTypeA` (`ProgramGen.SoundProgram`). Unlike
the procedure-list shape, it exercises abstract types, aliases, axioms, `distinct`,
datatype blocks and functions too.

It is also the only place the ADT-derived-function work is observable end to end: a
datatype block extends the operator vocabulary, and *later* functions and procedures
draw from it, so their bodies can call the block's constructors, testers and
accessors.

Counterexamples are minimized by the whole-program shrinker, which keeps every
candidate well-typed by re-running Strata's own `Program.typeCheck`. The one
exception is `typechecker accepts generated programs`: its failure *is* oracle
rejection, so no smaller candidate survives the filter and the witness is reported
unshrunk — with the `rejection_cause` axis and the `Repr`'s status note naming the
gap responsible.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport

/-- The six whole-program properties: the typechecker accepts them; the classified
    rejection causes are the complete list; and four invariants of a well-typed
    program. The last four are conditional on the input typechecking — vacuous on a
    gap-bearing draw, a genuine claim otherwise — and, unlike the first, a
    counterexample to any of them *is* shrinkable. -/
@[strata_properties]
def programChecks : List TestDecl :=
  family "program" Gens.program
    [ ("program: typechecker accepts generated programs",
       fun gp => checkProgramTypeCheckerComplete gp.prog),
      ("program: typechecker rejections are only the known gaps",
       fun gp => checkProgramRejectionIsKnownGap gp.prog),
      ("program: getNames of a well-typed program are distinct",
       fun gp => checkProgramNamesNodup gp.prog),
      ("program: typeCheck output re-typechecks",
       fun gp => checkProgramTypeCheckIdempotent gp.prog),
      ("program: stripMetaData preserves typeability",
       fun gp => checkProgramStripMetaPreservesTyping gp.prog),
      ("program: eraseTypes preserves typeability",
       fun gp => checkProgramEraseTypesPreservesTyping gp.prog) ]

/-- The four claims that only make sense *across* declarations, so no sub-generator
    shape can express them.

    Unlike the conditional invariants above, these are **unconditional**: each is
    established by the generator's fold rather than by the typechecker accepting the
    draw, so they stay non-vacuous on the programs that trip a documented
    completeness gap. That is what makes them the checks that actually watch the
    ADT-derived-call path. -/
@[strata_properties]
def programADTProps : List TestDecl :=
  family "program" Gens.program
    [ ("program: declared names are globally distinct",
       fun gp => checkNamesNodup gp.prog),
      ("program: datatype blocks pass addMutualBlock",
       fun gp => checkDatatypeBlocksAccepted gp.prog),
      ("program: called ADT functions are declared",
       fun gp => checkCalledDerivedAreDeclared gp.prog),
      ("program: ADT calls follow the datatype declaration",
       fun gp => checkDerivedCallsFollowDeclaration gp.prog) ]
