import StrataGenerators.Test

/-!
# Properties of the whole-program generator

`genProgram` makes a complete and well-typed Core `Program`. It emits every kind of
declaration, and it threads the ambient context through the fold over the declarations. It is
sound against the declarative specification `ProgramHasTypeA`. It also covers abstract types,
aliases, axioms, `distinct`, datatype blocks and functions, which the shape of a list of
procedures does not.

This generator is also the only place that shows the derived functions of a datatype from end
to end. A datatype block adds to the vocabulary of operators, and *later* functions and
procedures draw from that vocabulary. The body of such a declaration can therefore call a
constructor, a tester or an accessor of the block.

The whole-program shrinker reduces a counterexample. It keeps each candidate well-typed,
because it runs `Program.typeCheck` again on the candidate. The property
`typechecker accepts generated programs` is the one exception. A counterexample to it is a
program that the oracle rejects, so no smaller candidate passes the filter, and the report
gives the witness without a reduction. The `rejection_cause` axis and the status note of the
`Repr` instance name the gap.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport

/-- The six properties for a whole program. The type checker accepts each generated program.
    The classified causes of a rejection are the complete list. The other four properties are
    invariants of a well-typed program.

    Those four properties have the type check of the input as a condition. They are vacuous
    on a draw that holds a gap, and a real claim on every other draw. The shrinker can also
    reduce a counterexample to any of the four. -/
@[strata_properties]
def programChecks : List TestDecl :=
  family GenProgram
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

/-- The four claims that hold only *across* declarations. No shape of a smaller generator can
    state them.

    These four claims are **unconditional**. The fold of the generator establishes each one,
    and the acceptance of the draw by the type checker does not. Therefore they stay
    non-vacuous on a program that reaches a documented gap in completeness, and they are the
    checks that watch a call to a derived function of a datatype. -/
@[strata_properties]
def programADTProps : List TestDecl :=
  family GenProgram
    [ ("program: declared names are globally distinct",
       fun gp => checkNamesNodup gp.prog),
      ("program: datatype blocks pass addMutualBlock",
       fun gp => checkDatatypeBlocksAccepted gp.prog),
      ("program: called ADT functions are declared",
       fun gp => checkCalledDerivedAreDeclared gp.prog),
      ("program: ADT calls follow the datatype declaration",
       fun gp => checkDerivedCallsFollowDeclaration gp.prog) ]
