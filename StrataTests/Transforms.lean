import StrataGenerators.Test

/-!
# The Core transform passes that carry no correctness proof

`Strata/Transform/` holds 23 files and only four passes have a correctness
companion. These properties cover the ones that have no correctness file and no
theorem in-file (`StructuredToUnstructured`, `LoopElim`,
`InsertLoopInvariantAsserts`, `CommonSubexprElim`, `FunctionInlining`,
`ProcedureInlining`, `IrrelevantAxioms`), plus the two whose headline postcondition
is stated in a module doc but never proven (`NondetElim`, `LoopInitHoist`).
`TerminationCheck` is not covered: its properties need a recursive function to be
non-vacuous, which the generator cannot yet build.

Each takes a whole generated `Program`, so the passes that read a declaration other
than a procedure — the axioms and the function call graph for `IrrelevantAxioms`, the
callee declaration for `ProcedureInlining`, a function body for `FunctionInlining` —
are exercised on real input rather than on a statement list that cannot express them.

Two caveats worth reading before trusting a green result:

* `CommonSubexprElim` fires on 0 of 200 generated programs, since no generated body
  holds a duplicated subexpression, so all four `cse:` properties are vacuous here
  and the `#guard`s in `ProgramGen/UnprovenTransforms` are what test them.
* the three `procInline:` properties need a sample that holds a call, which is rare,
  so a short run may not reach them.

The last three properties run each loop pass through `LoopElim` (the evaluator
refuses a loop) and then through Strata's symbolic evaluator, comparing the
obligations against the same chain without the pass. They are stated as containment
rather than equality, and they are what found a defect in the **evaluator** rather
than in any pass: a nondeterministic guard is named after the current path-condition
depth instead of by a counter, so a second `if *` at the same depth silently drops
every obligation to the end of the procedure.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Program.UnprovenTransforms

/-- The forty-five properties for the unproven passes. -/
@[strata_properties]
def unprovenTransforms : List TestDecl :=
  family "transforms" Gens.program
    [ -- IrrelevantAxioms — the relevance oracle
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
      -- The semantic counterpart to the five syntactic axiom properties: an axiom is
      -- an assumption, never an obligation, so pruning one must leave the proof
      -- obligations *exactly* equal. Necessary but not sufficient for the pass's
      -- `modelPreserving` annotation — pruning an axiom some obligation needed leaves
      -- that obligation present but unprovable, which only a solver can see.
      ("axioms: pruning leaves the proof obligations unchanged",
       fun gp => checkAxiomsObligationsUnchanged gp.prog),
      -- StructuredToUnstructured — structural properties of the emitted CFG
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
      -- DetToKleene — the measure the transform silently drops
      ("kleene: a measure-carrying loop translates (the measure is dropped)",
       fun gp => checkKleeneMeasureAccepted gp.prog),
      -- LoopElim + InsertLoopInvariantAsserts — accounting of the verification conditions
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
      -- CommonSubexprElim — fresh names and ordering (vacuous on generated input)
      ("cse: no fresh name is declared twice",
       fun gp => checkCseFreshNamesFresh gp.prog),
      ("cse: the assert labels are preserved",
       fun gp => checkCseAssertLabelsPreserved gp.prog),
      -- The order claim, and not "bound before its first use": stating the latter
      -- exactly needs a scope-aware traversal, and `cse: the output typechecks`
      -- covers part of it, since the checker rejects a reference that precedes its
      -- declaration.
      ("cse: the fresh declarations are in index order",
       fun gp => checkCseFreshDeclOrder gp.prog),
      ("cse: the output typechecks",
       fun gp => checkCseOutputTypechecks gp.prog),
      -- FunctionInlining — a pure expression transform
      ("funcInline: fuel 0 is the identity",
       fun gp => checkInlineFuelZeroIdentity gp.prog),
      ("funcInline: more fuel never un-inlines",
       fun gp => checkInlineFuelMonotone gp.prog),
      ("funcInline: the type is preserved",
       fun gp => checkInlineTypePreserved gp.prog),
      ("funcInline: no free variable is introduced",
       fun gp => checkInlineCaptureFree gp.prog),
      -- Value preservation under the concrete evaluator — the sharpest of the five,
      -- since it constrains the *meaning* of the result and not only its shape.
      ("funcInline: evaluation agrees before/after inlining",
       fun gp => checkInlineEvalAgreement gp.prog),
      -- ProcedureInlining — freshening of the labels
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
      -- Agreement under Strata's executable *symbolic* evaluator, as containment
      -- rather than equality, because inlining duplicates the callee's obligations at
      -- each call site by design.
      ("procInline: symbolic evaluation loses no obligation",
       fun gp => checkInlineProcSymbolicAgreement gp.prog),
      -- NondetElim + LoopInitHoist — the postconditions neither file proves
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
      -- Containment and not equality *because of a defect in the evaluator, not the
      -- pass*: `StatementEval.lean` names a nondeterministic guard after the current
      -- path-condition depth instead of using a counter, so a second `if *` at the
      -- same depth re-declares the name, the path errors, and every obligation from
      -- there to the end of the procedure is dropped with no diagnostic. `NondetElim`
      -- removes every `if *`, so the dropped obligations come back and the set grows.
      ("nondetElim: symbolic evaluation loses no obligation",
       fun gp => checkNondetElimSymbolicNoLoss gp.prog),
      ("hoist: symbolic evaluation loses no obligation",
       fun gp => checkHoistSymbolicNoLoss gp.prog) ]
