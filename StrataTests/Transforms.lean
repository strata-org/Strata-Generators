import StrataGenerators.Test

/-!
# The Core transform passes that have no correctness proof

`Strata/Transform/` holds 23 files, and only four passes have a companion file for
correctness. These properties cover the passes that have no such file and no theorem in
their own file: `StructuredToUnstructured`, `LoopElim`, `InsertLoopInvariantAsserts`,
`CommonSubexprElim`, `FunctionInlining`, `ProcedureInlining` and `IrrelevantAxioms`. They
also cover the two passes whose main postcondition a module document states but no theorem
proves: `NondetElim` and `LoopInitHoist`. `TerminationCheck` has no property here, because
its properties need a recursive function to be non-vacuous, and the generator cannot build
one.

Each property receives a whole generated `Program`. Therefore the passes that read a
declaration other than a procedure get real input, and not a list of statements that cannot
hold such a declaration. `IrrelevantAxioms` reads the axioms and the call graph of the
functions, `ProcedureInlining` reads the declaration of the callee, and `FunctionInlining`
reads the body of a function.

Two limits apply to these results:

* `CommonSubexprElim` acts only on a subexpression that occurs two or more times, and a
  generated body rarely holds one. The four `cse:` properties are therefore silent on most
  runs, and the `#guard`s in `ProgramGen/UnprovenTransforms` are what cover the pass on each
  build. A `cse:` property that holds means that the run did not reach the pass, and it does
  not mean that the pass is correct. The pass also hoists a subexpression that it extracts
  above the declaration of a local variable that the subexpression mentions.
* The three `procInline:` properties need a sample that holds a call, and such a sample is
  rare. A short run may not reach them.

The last three properties send each loop pass through `LoopElim`, because the evaluator
refuses a loop, and then through the symbolic evaluator of Strata. They compare the
obligations against the same chain without the pass. They state containment and not equality.
They also show a defect in the **evaluator** and not in a pass: the evaluator names a
nondeterministic guard after the current depth of the path condition, and not with a counter.
A second `if *` at the same depth therefore drops every obligation from that point to the end
of the procedure.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.UnprovenTransforms

/-- The forty-five properties for the passes that have no correctness proof. -/
@[strata_properties]
def unprovenTransforms : List TestDecl :=
  family GenProgram
    [ -- IrrelevantAxioms: the oracle for relevance
      ("axioms: IrrelevantAxioms removes only axioms",
       fun gp => checkAxiomsOnlyAxRemoved gp.prog),
      ("axioms: IrrelevantAxioms preserves declaration order",
       fun gp => checkAxiomsOrderPreserved gp.prog),
      ("axioms: every retained axiom is relevant",
       fun gp => checkAxiomsRetainedRelevant gp.prog),
      ("axioms: every removed axiom is irrelevant",
       fun gp => checkAxiomsRemovedIrrelevant gp.prog),
      ("axioms: a removed axiom mentions no reachable function",
       fun gp => checkAxiomsRemovedNotSeedReachable gp.prog),
      ("axioms: the pruned program typechecks",
       fun gp => checkAxiomsPrunedTypechecks gp.prog),
      -- The semantic companion to the five syntactic properties for axioms. An axiom is an
      -- assumption and never an obligation, so the removal of an axiom must leave the proof
      -- obligations *exactly* equal. This is necessary for the `modelPreserving` annotation
      -- of the pass, but it is not sufficient. If the pass removes an axiom that an
      -- obligation needs, the obligation stays but no proof for it exists, and only a solver
      -- can see this.
      ("axioms: pruning leaves the proof obligations unchanged",
       fun gp => checkAxiomsObligationsUnchanged gp.prog),
      -- StructuredToUnstructured: structural properties of the control-flow graph that it
      -- emits
      ("s2u: every goto target is a block label",
       fun gp => checkS2uNoDanglingLabel gp.prog),
      ("s2u: block labels are distinct",
       fun gp => checkS2uLabelsNodup gp.prog),
      ("s2u: the entry label exists",
       fun gp => checkS2uEntryExists gp.prog),
      ("s2u: exactly one finish block",
       fun gp => checkS2uOneFinish gp.prog),
      ("s2u: every block is reachable from the entry",
       fun gp => checkS2uAllReachable gp.prog),
      ("s2u: the command count does not shrink",
       fun gp => checkS2uCmdCountGrows gp.prog),
      ("s2u: a cfg-bodied procedure prints",
       fun gp => checkS2uCfgPrintable gp.prog),
      -- DetToKleene: the measure that the transform drops
      ("kleene: a measure-carrying loop translates (the measure is dropped)",
       fun gp => checkKleeneMeasureAccepted gp.prog),
      -- LoopElim and InsertLoopInvariantAsserts: the count of the verification conditions
      ("loop: the inserted assert count is exact",
       fun gp => checkLoopVcAssertCount gp.prog),
      ("loop: every loop is bare after the pass",
       fun gp => checkLoopBareAfterPass gp.prog),
      ("loop: InsertLoopInvariantAsserts is idempotent",
       fun gp => checkLoopVcIdempotent gp.prog),
      ("loop: insertedAssertAssumes is faithful",
       fun gp => checkLoopVcStatFaithful gp.prog),
      ("loop: no verification condition is lost through LoopElim",
       fun gp => checkLoopVcSurvivesElim gp.prog),
      ("loop: a nondet loop with a measure is rejected",
       fun gp => checkLoopNondetMeasureThrows gp.prog),
      ("loop: LoopElim mints distinct block labels",
       fun gp => checkLoopBlockLabelsNodup gp.prog),
      ("loop: erasedLoops is faithful",
       fun gp => checkLoopElimStatFaithful gp.prog),
      -- CommonSubexprElim: fresh names and order
      ("cse: no fresh name is declared twice",
       fun gp => checkCseFreshNamesFresh gp.prog),
      ("cse: the assert labels are preserved",
       fun gp => checkCseAssertLabelsPreserved gp.prog),
      -- This is a claim about the order, and not the claim that each name is bound before
      -- its first use. An exact statement of the second claim needs a traversal that knows
      -- the scopes. `cse: the output typechecks` covers part of it, because the checker
      -- rejects a reference that comes before its declaration.
      ("cse: the fresh declarations are in index order",
       fun gp => checkCseFreshDeclOrder gp.prog),
      ("cse: the output typechecks",
       fun gp => checkCseOutputTypechecks gp.prog),
      -- FunctionInlining: a transform on expressions only
      ("funcInline: fuel 0 is the identity",
       fun gp => checkInlineFuelZeroIdentity gp.prog),
      ("funcInline: more fuel never un-inlines",
       fun gp => checkInlineFuelMonotone gp.prog),
      ("funcInline: the type is preserved",
       fun gp => checkInlineTypePreserved gp.prog),
      ("funcInline: no free variable is introduced",
       fun gp => checkInlineCaptureFree gp.prog),
      -- The concrete evaluator keeps the value. This is the strongest of the five
      -- properties, because it constrains the *meaning* of the result and not only its
      -- shape.
      ("funcInline: evaluation agrees before/after inlining",
       fun gp => checkInlineEvalAgreement gp.prog),
      -- ProcedureInlining: fresh labels
      ("procInline: inlining introduces no duplicate label",
       fun gp => checkInlineProcLabelsNodup gp.prog),
      ("procInline: no assert is lost",
       fun gp => checkInlineProcAssertsNotLost gp.prog),
      ("procInline: visitedCalls and inlinedCalls are faithful",
       fun gp => checkInlineProcStatsFaithful gp.prog),
      ("procInline: the output typechecks",
       fun gp => checkInlineProcTypechecks gp.prog),
      ("procInline: preserves call-graph WF",
       fun gp => checkInlineProcAnalysisPreserved gp.prog),
      -- Agreement under the executable *symbolic* evaluator of Strata. The property states
      -- containment and not equality, because the pass copies the obligations of the callee
      -- to each call site by design.
      ("procInline: symbolic evaluation loses no obligation",
       fun gp => checkInlineProcSymbolicAgreement gp.prog),
      -- NondetElim and LoopInitHoist: the postconditions that neither file proves
      ("nondetElim: no nondet guard is left",
       fun gp => checkNondetElimNoNondetGuard gp.prog),
      ("nondetElim: the fresh guard names are distinct",
       fun gp => checkNondetElimFreshNames gp.prog),
      ("hoist: no loop body holds an init",
       fun gp => checkHoistNoLoopBodyInits gp.prog),
      ("hoist: uniqueInits is preserved",
       fun gp => checkHoistPreservesUniqueInits gp.prog),
      -- The three loop passes under the symbolic evaluator
      ("loop: symbolic evaluation loses no obligation through InsertLoopInvariantAsserts",
       fun gp => checkLoopVcSymbolicNoLoss gp.prog),
      -- The property states containment and not equality, because of a defect in the
      -- evaluator and not in the pass. The evaluator names a nondeterministic guard after
      -- the current depth of the path condition, and not with a counter. A second `if *` at
      -- the same depth therefore declares the name again, the path gives an error, and the
      -- evaluator drops every obligation from that point to the end of the procedure without
      -- a message. `NondetElim` removes each `if *`, so the dropped obligations come back
      -- and the set of obligations grows.
      ("nondetElim: symbolic evaluation loses no obligation",
       fun gp => checkNondetElimSymbolicNoLoss gp.prog),
      ("hoist: symbolic evaluation loses no obligation",
       fun gp => checkHoistSymbolicNoLoss gp.prog) ]
