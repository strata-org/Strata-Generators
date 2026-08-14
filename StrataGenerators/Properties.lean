import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.StmtHasTypeAGen.TestSupport
import StrataGenerators.ProcedureHasTypeAGen.TestSupport
import StrataGenerators.PhaseChangedFlag
import StrataGenerators.PrinterCoverage
-- Supplies the six whole-program check predicates (and the shrinker backing the
-- `Shrinkable GenProgram` instance).
import StrataGenerators.ProgramGen.Shrink
-- Supplies the ADT-derived-call check predicates.
import StrataGenerators.ProgramGen.TestSupport
-- Supplies the forty-two check predicates for the Core transform passes that have
-- no correctness proof.
import StrataGenerators.ProgramGen.UnprovenTransforms
-- Supplies the thirteen check predicates for `LiftInternalFuncDecls`.
import StrataGenerators.ProgramGen.LiftFuncDecls

/-!
# Shared property catalog

Single source of truth for the string that identifies each generator property in
the test results *and* — where the LSpec assertion and the Tyche panel evaluate
the same boolean check — for the name↔check pairing itself.

Both the LSpec suite and the Tyche panels (both in the merged `TestMain` driver,
the latter via `StrataGenerators.TycheViz`) reference the `PropertyNames.*`
constants, so a property carries the *same* label in the LSpec output and the
Tyche panels — cross-referencing a result between the two never depends on two
hand-copied strings staying in sync.

The `Property` bundles below go one step further for the families where the LSpec
assertion and the Tyche panel run an *identical* `Bool` predicate (the four
single-verdict command panels and the six statement transforms): the name and the
check are paired in exactly one place, so a call site never has the bare string in
scope to attach to the wrong predicate, and the two views cannot disagree about
which check a name denotes. Properties whose harness shapes genuinely differ
(expr/function props, the richer eval-agreement and Kleene-definedness panels)
keep only a shared *name* here; their test logic stays with each view.

Naming scheme: `area: description`, where `area` is one of `expr` / `cmd` /
`function` / `stmt` / `proc` / `program` / `phase` / `printer`. A handful of
properties are exercised by only one harness (noted per entry); they still live
here so the catalog is the one place property names are spelled.
-/

open Lambda Core Imperative
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Procedure.TestSupport
open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport
open StrataGenerators.Program.UnprovenTransforms
open StrataGenerators.Program.LiftFuncDecls

/-- A property under test, bundling its canonical name with the shared boolean
    check both harnesses evaluate on a generated `α`. Pairing name↔check in one
    place makes it structurally impossible to associate a name with the wrong
    check: neither harness handles the bare string, only the whole bundle. -/
structure Property (α : Type) where
  name  : String
  check : α → Bool

namespace PropertyNames

-- ── Expression-generator properties ──────────────────────────────────
/-- Plausible-only (soundness of the generator; no Tyche panel). -/
def exprTypecheck         : String := "expr: generated terms typecheck"
def exprPreservation      : String := "expr: preservation under eval (closed)"
def exprProgress          : String := "expr: progress (closed)"
def exprFvarsPreserved    : String := "expr: eval preserves fvars"
def exprResolveAfterErase : String := "expr: resolve after type erasure"
/-- Opt-in (`--smt`); requires a live SMT solver. Ported from
    `StrataTest/Languages/Core/Tests/ExprEvalTest.lean`. -/
def exprSmtEvalAgreement  : String := "expr: SMT/concrete eval agreement (closed)"
/-- The oracle is "the emitted literal is printable ASCII", which is the
    requirement of SMT-LIB 2.6+ itself, so the property needs no solver and runs in
    the default suite. It is non-vacuous only because `genInterestingString` draws
    non-ASCII characters; under Basalt's alphanumeric `String.arbitrary` it would
    not be. -/
def exprSmtStringEscaping : String := "expr: SMT string literals are printable ASCII"

/-- The property needs no solver. It is non-vacuous only because the generator
    builds a second spelling of one value; a pair of independent draws is almost
    never equal. -/
def realDecimalEqFold : String := "real: Decimal eq fold agrees with value equality"
def realDecimalTrichotomy : String := "real: Decimal comparator is a total order"

-- ── Command-generator properties ─────────────────────────────────────
def cmdInitFresh             : String := "cmd: init var not in RHS"
def cmdExprTypecheck         : String := "cmd: expressions typecheck"
def cmdSetPreservesVar       : String := "cmd: set preserves variable"
def cmdStoreTypePreservation : String := "cmd: store type preservation under eval"
def cmdEvalRunAgreement      : String := "cmd: symbolic/concrete eval agreement"
/-- Plausible-only (statement-sequence property). -/
def cmdContextGrowth         : String := "cmd: context growth matches inits"

-- ── Function-generator properties ────────────────────────────────────
def fnFvarsAnnotated    : String := "function: fvars annotated by context type map"
def fnTypeCheckSound    : String := "function: typeCheck output satisfies FuncHasTypeA (typeCheck_annotated_sound)"
def fnTypeCheckComplete : String := "function: typeCheck accepts generated functions (completeness)"
/-- Plausible-only (pins the sole known completeness gap to measure-without-body). -/
def fnRejectionOnlyMeasure : String := "function: typeCheck rejections are only measure-without-body"
def fnRoundtrip         : String := "function: pretty-print/parse round-trip"
def fnBodyPreservation  : String := "function: body type preserved under eval"
def fnIdentProbe        : String := "function: special-character identifier round-trip"

-- ── Statement-generator properties ───────────────────────────────────
def stmtTypecheck          : String := "stmt: typechecker accepts generated statements"
def stmtLoopElimPreserves  : String := "stmt: LoopElim preserves typeability"
def stmtLoopElimZeroLoops  : String := "stmt: LoopElim eliminates all loops"
def stmtAnfIdempotent      : String := "stmt: ANF is idempotent"
def stmtAnfPreservesTyping : String := "stmt: ANF preserves typeability"
def stmtKleeneDefinedIff   : String := "stmt: DetToKleene defined iff supported"
def stmtMapExprsId         : String := "stmt: mapExprs id = id"

-- ── Procedure-generator ↔ transform-pass properties ──────────────────
-- Exercised against three Core transform passes (FilterProcedures, PrecondElim,
-- ANFEncoder). There is now one property per *named field* of the
-- three `*PhaseCorrect` structures in `Strata/Transform/CustomSpecifications.lean`
-- — including the `ChangedFlagValid` and `PreservesCachedAnalysesWF` fields shared
-- by all three — so the coverage of those specs is complete rather than partial.
-- See the module doc of `ProcedureHasTypeAGen/TestSupport` for the full analysis
-- and for which properties run on the mixed-declaration program shape.

-- FilterProcedures — `FilterProcedurePhaseCorrect`
def procFilterDeclsSublist   : String := "proc: FilterProcedures output decls are a sublist"
def procFilterTargetsRetained : String := "proc: FilterProcedures retains targets"
def procFilterCalleeClosure  : String := "proc: FilterProcedures retains callee closures"
def procFilterOnlyProcsRemoved : String := "proc: FilterProcedures removes only procedures"
def procFilterUnreachableRemoved : String := "proc: FilterProcedures removes unreachable procs"
def procFilterChangedFlag    : String := "proc: FilterProcedures changed flag is faithful"
def procFilterAnalysisPreserved : String := "proc: FilterProcedures preserves call-graph WF"

-- PrecondElim — `PrecondElimPhaseCorrect`
def procPrecondGeneratedWF   : String := "proc: PrecondElim $wf procs are well-formed"
def procPrecondStripped      : String := "proc: PrecondElim strips all preconditions"
def procPrecondNonProcDecls  : String := "proc: PrecondElim preserves type/ax/distinct decls"
def procPrecondProcsPreserved : String := "proc: PrecondElim preserves procedures (name+spec)"
def procPrecondFuncsPreserved : String := "proc: PrecondElim preserves functions (name+body+sig)"
def procPrecondNoDeclsRemoved : String := "proc: PrecondElim removes no declarations"
def procPrecondOrderPreserved : String := "proc: PrecondElim preserves declaration order"
def procPrecondChangedFlag   : String := "proc: PrecondElim changed flag is faithful"
def procPrecondCallSiteAsserts : String := "proc: PrecondElim asserts every partial call"
def procPrecondFactoryGrows  : String := "proc: PrecondElim factory only grows"
def procPrecondFactoryComplete : String := "proc: PrecondElim factory has every declared function"
def procPrecondFactoryStripped : String := "proc: PrecondElim factory entries are stripped"
def procPrecondDeclaredFactoryStripped : String :=
  "proc: PrecondElim factory strips declared functions"
def procPrecondAnalysisPreserved : String := "proc: PrecondElim preserves call-graph WF"

-- ANFEncoder — `ANFEncoderPhaseCorrect`
def procAnfDeclsLength       : String := "proc: ANFEncoder preserves declaration count"
def procAnfNonProcsUnchanged : String := "proc: ANFEncoder leaves non-procedures unchanged"
def procAnfHeadersPreserved  : String := "proc: ANFEncoder preserves procedure headers+specs"
def procAnfFreshVarsDet      : String := "proc: ANFEncoder fresh vars are deterministic"
def procAnfOrderPreserved    : String := "proc: ANFEncoder preserves declaration order"
def procAnfControlFlow       : String := "proc: ANFEncoder does not change control flow"
def procAnfChangedFlag       : String := "proc: ANFEncoder changed flag is faithful"
def procAnfAnalysisPreserved : String := "proc: ANFEncoder preserves call-graph WF"

-- ── Pipeline-phase `changed`-flag properties (uniform over every phase) ───
-- See `StrataGenerators.PhaseChangedFlag`. Four phases hardcode `changed := true`
-- (`FilterProcedures`, `RemoveIrrelevantAxioms`, `typeCheck`, `symbolicEval`).
-- The `proc:` catalog above pins `FilterProcedures` and `PrecondElim`
-- individually; these state the contract *uniformly over a phase list*, so a
-- phase added later is covered without a new property being written.

def phaseIrrelevantAxiomsNoOp : String :=
  "phase: RemoveIrrelevantAxioms changed flag is faithful on a no-op"
def phaseFilterNoOp : String :=
  "phase: FilterProcedures changed flag is faithful on a no-op"
/-- Uniform sweep over every phase of `corePipelinePhases` plus
    `RemoveIrrelevantAxioms`. This is the regression gate that catches a *newly
    added* hardcoding phase. -/
def phaseAllChangedFlag : String :=
  "phase: every pipeline phase has a faithful changed flag"
/-- Every phase *except* the four known hardcoded-`true` sites; it is what guards
    the honestly-computing phases against regression. -/
def phaseHonestChangedFlag : String :=
  "phase: non-hardcoded pipeline phases have a faithful changed flag"

-- ── Printer-expressiveness properties ────────────────────────────────
-- See `StrataGenerators.PrinterCoverage`. The oracle is "the printer logged no
-- conversion error", which needs no parser and names the offending construct.

def printerNoConversionError : String :=
  "printer: no conversion error on generated programs"
def printerBv128Literal : String :=
  "printer: bitvec 128 literals are printable"
def printerBvIntConversions : String :=
  "printer: Bv/Int conversion operators are printable"
def printerBvWidthAgreement : String :=
  "printer: every typecheckable bitvec width is printable"

-- ── Whole-program-generator properties ───────────────────────────────
-- `genProgram` produces a whole `Program` (every declaration kind, real ambient
-- context threaded across the fold) and is proven sound against `ProgramHasTypeA`.
-- The first property below states that the typechecker accepts them; the second
-- pins the classified rejection causes as the complete list; the remaining four are
-- invariants of a well-typed program. See the module doc of `ProgramGen/Shrink`.

def programTypecheck : String := "program: typechecker accepts generated programs"
def programRejectionKnownGap : String :=
  "program: typechecker rejections are only the known gaps"
-- The four invariants of a well-typed program. Each is conditional on the input
-- typechecking (so vacuous on a gap-bearing draw, a genuine claim otherwise), and
-- — unlike `programTypecheck` — a counterexample to any of them IS shrinkable,
-- since its failure does not depend on the oracle rejecting the program.
def programNamesNodup      : String := "program: getNames of a well-typed program are distinct"
def programTypeCheckIdem   : String := "program: typeCheck output re-typechecks"
def programStripMeta       : String := "program: stripMetaData preserves typeability"
def programEraseTypes      : String := "program: eraseTypes preserves typeability"

-- ── ADT-derived-call properties ──────────────────────────────────────
-- `ProgramGen.genProgram` folds every declaration kind into one `Program`. These
-- are the properties that only make sense *across* declarations, so no
-- sub-generator suite can express them. Unlike `programNamesNodup` above, the
-- name-distinctness claim here is *unconditional*: the generator threads one
-- reserved-name set across the whole fold, so it holds even on a draw the
-- typechecker rejects.
def programAllNamesNodup   : String := "program: declared names are globally distinct"
def programBlocksAccepted  : String := "program: datatype blocks pass addMutualBlock"
def programDerivedResolve  : String := "program: called ADT functions are declared"
def programDerivedOrdered  : String := "program: ADT calls follow the datatype declaration"

-- ── The eight unproven Core transform passes ─────────────────────────
-- `Strata/Transform/` holds 23 files, and only four passes have a correctness
-- companion. These properties cover the eight that have no correctness file and no
-- theorem in-file (`StructuredToUnstructured`, `LoopElim`,
-- `InsertLoopInvariantAsserts`, `CommonSubexprElim`, `FunctionInlining`,
-- `ProcedureInlining`, `IrrelevantAxioms`), plus the two whose headline
-- postcondition is stated in a module doc but never proven (`NondetElim`,
-- `LoopInitHoist`). `TerminationCheck` is not covered: its properties need a
-- recursive function to be non-vacuous, which the generator cannot make yet
--.
--
-- Each property takes a whole generated `Program`, so the passes that read a
-- declaration other than a procedure (the axioms and the function call graph for
-- `IrrelevantAxioms`, the callee declaration for `ProcedureInlining`, a function
-- body for `FunctionInlining`) are exercised on real input rather than on a
-- statement list that cannot express them.
--
-- `CommonSubexprElim` fires on 0 of 200 generated programs, since no generated
-- body holds a duplicated subexpression, so the two `cse:` properties that need a
-- duplicate are pinned by a hand-built body instead. See
-- `ProgramGen/UnprovenTransforms` for the analysis of each.

-- IrrelevantAxioms — the relevance oracle (the `changed` flag is covered separately)
def axiomsOnlyAxRemoved      : String := "axioms: IrrelevantAxioms removes only axioms"
def axiomsOrderPreserved     : String := "axioms: IrrelevantAxioms preserves declaration order"
def axiomsRetainedRelevant   : String := "axioms: every retained axiom is relevant"
def axiomsRemovedIrrelevant  : String := "axioms: every removed axiom is irrelevant"
def axiomsRemovedUnreachable : String :=
  "axioms: a removed axiom mentions no reachable function"
def axiomsPrunedTypechecks   : String := "axioms: the pruned program typechecks"
/-- The semantic counterpart to the five syntactic axiom properties: an axiom is an
    assumption, never an obligation, so pruning one must leave the proof obligations
    *exactly* equal. Necessary but not sufficient for the pass's `modelPreserving`
    annotation — pruning an axiom some obligation needed leaves that obligation
    present but unprovable, which only a solver can see. -/
def axiomsObligationsUnchanged : String :=
  "axioms: pruning leaves the proof obligations unchanged"

-- StructuredToUnstructured — structural properties of the emitted CFG
def s2uNoDanglingLabel : String := "s2u: every goto target is a block label"
def s2uLabelsNodup     : String := "s2u: block labels are distinct"
def s2uEntryExists     : String := "s2u: the entry label exists"
def s2uOneFinish       : String := "s2u: exactly one finish block"
def s2uAllReachable    : String := "s2u: every block is reachable from the entry"
def s2uCmdCountGrows   : String := "s2u: the command count does not shrink"
def s2uCfgPrintable    : String := "s2u: a cfg-bodied procedure prints"

-- DetToKleene — the measure the transform silently drops
def kleeneMeasureAccepted : String :=
  "kleene: a measure-carrying loop translates (the measure is dropped)"

-- LoopElim + InsertLoopInvariantAsserts — accounting of the verification conditions
def loopVcAssertCount     : String := "loop: the inserted assert count is exact"
def loopBareAfterPass     : String := "loop: every loop is bare after the pass"
def loopVcIdempotent      : String := "loop: InsertLoopInvariantAsserts is idempotent"
def loopVcStatFaithful    : String := "loop: insertedAssertAssumes is faithful"
def loopVcSurvivesElim    : String := "loop: no verification condition is lost through LoopElim"
def loopNondetMeasure     : String := "loop: a nondet loop with a measure is rejected"
def loopBlockLabelsNodup  : String := "loop: LoopElim mints distinct block labels"
def loopElimStatFaithful  : String := "loop: erasedLoops is faithful"

-- CommonSubexprElim — fresh names and ordering. All four are VACUOUS on generated
-- input: CSE fires on 0 of 200 draws, since no generated body holds a duplicated
-- subexpression. `#guard`s pin each one on a hand-built body that does.
def cseFreshNamesFresh      : String := "cse: no fresh name is declared twice"
def cseAssertLabelsPreserved : String := "cse: the assert labels are preserved"
/-- The order claim, and not "bound before its first use": stating the latter
    exactly needs a scope-aware traversal. `cseOutputTypechecks` covers part of it,
    since the checker rejects a reference that precedes its declaration. -/
def cseFreshDeclOrder       : String := "cse: the fresh declarations are in index order"
def cseOutputTypechecks     : String := "cse: the output typechecks"

-- FunctionInlining — a pure expression transform
def inlineFuelZeroIdentity : String := "funcInline: fuel 0 is the identity"
def inlineFuelMonotone     : String := "funcInline: more fuel never un-inlines"
def inlineTypePreserved    : String := "funcInline: the type is preserved"
def inlineCaptureFree      : String := "funcInline: no free variable is introduced"
/-- Value preservation under the concrete evaluator — the sharpest of the five, since
    it constrains the *meaning* of the result and not only its shape. Requires the
    evaluator to be allowed to unfold the same functions the transform does; see
    `inlineEvalFactory`. -/
def inlineEvalAgreement    : String := "funcInline: evaluation agrees before/after inlining"

-- ProcedureInlining — freshening of the labels
def inlineProcLabelsNodup      : String := "procInline: inlining introduces no duplicate label"
def inlineProcAssertsNotLost   : String := "procInline: no assert is lost"
def inlineProcStatsFaithful    : String := "procInline: visitedCalls and inlinedCalls are faithful"
def inlineProcTypechecks       : String := "procInline: the output typechecks"
def inlineProcAnalysisPreserved : String := "procInline: preserves call-graph WF"
/-- Agreement is stated under Strata's executable *symbolic* evaluator (the
    `symbolicEval` phase of `corePipelinePhases`), as containment rather than
    equality, because inlining duplicates the callee's obligations at each call site
    by design. -/
def inlineProcSymbolicAgreement : String :=
  "procInline: symbolic evaluation loses no obligation"

-- NondetElim + LoopInitHoist — the postconditions neither file proves
def nondetElimNoNondetGuard : String := "nondetElim: no nondet guard is left"
def nondetElimFreshNames    : String := "nondetElim: the fresh guard names are distinct"
def hoistNoLoopBodyInits    : String := "hoist: no loop body holds an init"
def hoistPreservesUniqueInits : String := "hoist: uniqueInits is preserved"

-- The three loop passes under the symbolic evaluator. Each runs `LoopElim` after
-- the pass to get the loop-free program the evaluator requires, and compares the
-- obligations it emits against the same chain without the pass. All three are
-- stated as containment ("no obligation is lost"), since each pass may
-- legitimately add one; see §2.9 of `ProgramGen/UnprovenTransforms`.
def loopVcSymbolicNoLoss : String :=
  "loop: symbolic evaluation loses no obligation through InsertLoopInvariantAsserts"
/-- Containment and not equality *because of a defect in the evaluator, not the
    pass*: `StatementEval.lean` names a nondeterministic guard after the
    current path-condition depth instead of using a counter, so a second `if *` at
    the same depth re-declares the name, the path errors, and every obligation from
    there to the end of the procedure is dropped with no diagnostic. `NondetElim`
    removes every `if *`, so the dropped obligations come back and the set grows. -/
def nondetElimSymbolicNoLoss : String :=
  "nondetElim: symbolic evaluation loses no obligation"
def hoistSymbolicNoLoss : String :=
  "hoist: symbolic evaluation loses no obligation"

-- LiftInternalFuncDecls — lambda lifting with declaration-site capture
def liftInjectionFires     : String := "lift: the injected declaration is really lifted"
def liftFuncsClosed        : String := "lift: every hoisted function is closed"
def liftStrataClosed       : String := "lift: every function satisfies LFuncClosed"
def liftNoResidualDecl     : String := "lift: no procedure body holds a funcDecl"
def liftIdempotent         : String := "lift: the pass is idempotent"
def liftIdentityNoDecl     : String := "lift: a funcDecl-free program is unchanged"
def liftParamsLead         : String := "lift: the captured parameters lead"
def liftFreshNames         : String := "lift: the minted snapshot names are fresh"
def liftOutputTypechecks   : String := "lift: the output typechecks"
def liftSnapshotsInScope   : String := "lift: every snapshot is used in scope"
def liftFixpointMatchesRef : String := "lift: the fixpoint matches Def 4.6"
def liftTypeArgsClosed     : String := "lift: no hoisted function has a free type var"
def liftRejectsOnlyKnown   : String := "lift: only the documented triggers are rejected"

/-- Every catalog name, for the no-duplicate-names guard below. -/
def all : List String :=
  [ exprTypecheck, exprPreservation, exprProgress, exprFvarsPreserved,
    exprResolveAfterErase, exprSmtEvalAgreement, exprSmtStringEscaping,
    realDecimalEqFold, realDecimalTrichotomy,
    cmdInitFresh, cmdExprTypecheck, cmdSetPreservesVar, cmdStoreTypePreservation,
    cmdEvalRunAgreement, cmdContextGrowth,
    fnFvarsAnnotated, fnTypeCheckSound, fnTypeCheckComplete, fnRejectionOnlyMeasure,
    fnRoundtrip, fnBodyPreservation, fnIdentProbe,
    stmtTypecheck, stmtLoopElimPreserves, stmtLoopElimZeroLoops, stmtAnfIdempotent,
    stmtAnfPreservesTyping, stmtKleeneDefinedIff, stmtMapExprsId,
    procFilterDeclsSublist, procFilterTargetsRetained, procFilterCalleeClosure,
    procFilterOnlyProcsRemoved, procFilterUnreachableRemoved, procFilterChangedFlag,
    procFilterAnalysisPreserved,
    procPrecondGeneratedWF, procPrecondStripped, procPrecondNonProcDecls,
    procPrecondProcsPreserved, procPrecondFuncsPreserved, procPrecondNoDeclsRemoved,
    procPrecondOrderPreserved, procPrecondChangedFlag, procPrecondCallSiteAsserts,
    procPrecondFactoryGrows, procPrecondFactoryComplete, procPrecondFactoryStripped,
    procPrecondDeclaredFactoryStripped, procPrecondAnalysisPreserved,
    procAnfDeclsLength, procAnfNonProcsUnchanged, procAnfHeadersPreserved,
    procAnfFreshVarsDet, procAnfOrderPreserved, procAnfControlFlow,
    procAnfChangedFlag, procAnfAnalysisPreserved,
    phaseIrrelevantAxiomsNoOp, phaseFilterNoOp, phaseAllChangedFlag,
    phaseHonestChangedFlag,
    printerNoConversionError, printerBv128Literal, printerBvIntConversions,
    printerBvWidthAgreement,
    programTypecheck, programRejectionKnownGap, programNamesNodup,
    programTypeCheckIdem, programStripMeta, programEraseTypes,
    programAllNamesNodup, programBlocksAccepted, programDerivedResolve,
    programDerivedOrdered,
    axiomsOnlyAxRemoved, axiomsOrderPreserved, axiomsRetainedRelevant,
    axiomsRemovedIrrelevant, axiomsRemovedUnreachable, axiomsPrunedTypechecks,
    axiomsObligationsUnchanged,
    s2uNoDanglingLabel, s2uLabelsNodup, s2uEntryExists, s2uOneFinish,
    s2uAllReachable, s2uCmdCountGrows, s2uCfgPrintable,
    kleeneMeasureAccepted,
    loopVcAssertCount, loopBareAfterPass, loopVcIdempotent, loopVcStatFaithful,
    loopVcSurvivesElim, loopNondetMeasure, loopBlockLabelsNodup, loopElimStatFaithful,
    cseFreshNamesFresh, cseAssertLabelsPreserved, cseFreshDeclOrder, cseOutputTypechecks,
    inlineFuelZeroIdentity, inlineFuelMonotone, inlineTypePreserved, inlineCaptureFree,
    inlineEvalAgreement,
    inlineProcLabelsNodup, inlineProcAssertsNotLost, inlineProcStatsFaithful,
    inlineProcTypechecks, inlineProcAnalysisPreserved, inlineProcSymbolicAgreement,
    nondetElimNoNondetGuard, nondetElimFreshNames,
    hoistNoLoopBodyInits, hoistPreservesUniqueInits,
    loopVcSymbolicNoLoss, nondetElimSymbolicNoLoss, hoistSymbolicNoLoss,
    liftInjectionFires, liftFuncsClosed, liftStrataClosed, liftNoResidualDecl,
    liftIdempotent, liftIdentityNoDecl, liftParamsLead, liftFreshNames,
    liftOutputTypechecks, liftSnapshotsInScope, liftFixpointMatchesRef,
    liftTypeArgsClosed, liftRejectsOnlyKnown ]

-- No two properties share a name (a copy/paste slip that pointed two properties
-- at the same label would collapse their panels/results silently).
#guard (all.eraseDups).length == all.length

end PropertyNames

/-!
## Shared name↔check bundles

The two families below run byte-identical `Bool` predicates in both harnesses, so
each name is paired with its check exactly once here. Each harness iterates the
list — Tyche renders one panel per bundle, Plausible folds one `checkIO` per
bundle — so the pairing is defined in one reviewable line and cannot drift.
-/

namespace Properties

/-- The four single-verdict command properties: each is a command paired with its
    generating context, scored by a shared predicate (the first two ignore the
    context). The richer eval-agreement panel is *not* here — its Tyche shape
    differs — but shares its name via `PropertyNames.cmdEvalRunAgreement`. -/
def cmdSingleVerdict : List (Property (Cmd Expression × VarCtx)) :=
  [ ⟨PropertyNames.cmdInitFresh,             fun (c, _)   => checkInitFreshNotInRhs c⟩,
    ⟨PropertyNames.cmdExprTypecheck,         fun (c, _)   => checkExprTypechecks c⟩,
    ⟨PropertyNames.cmdSetPreservesVar,       fun (c, ctx) => checkSetPreservesVar c ctx⟩,
    ⟨PropertyNames.cmdStoreTypePreservation, fun (c, ctx) => checkStoreTypePreservation c ctx⟩ ]

/-- The six statement-transform / typechecker properties, each a well-typed
    statement list scored by a shared predicate. The Kleene-definedness property
    is *not* here — its Tyche panel records extra breakdown — but shares its
    name via `PropertyNames.stmtKleeneDefinedIff`. -/
def stmtTransforms : List (Property (List Statement)) :=
  [ ⟨PropertyNames.stmtTypecheck,          checkTypeCheckerComplete⟩,
    ⟨PropertyNames.stmtLoopElimPreserves,  checkLoopElimPreservesTyping⟩,
    ⟨PropertyNames.stmtLoopElimZeroLoops,  checkLoopElimZeroLoops⟩,
    ⟨PropertyNames.stmtAnfIdempotent,      checkAnfIdempotent⟩,
    ⟨PropertyNames.stmtAnfPreservesTyping, checkAnfPreservesTyping⟩,
    ⟨PropertyNames.stmtMapExprsId,         checkMapExprsId⟩ ]

/-- The twenty-eight procedure/transform properties — one per named field of the
    three `*PhaseCorrect` structures in
    `Strata/Transform/CustomSpecifications.lean` — each a generated procedure
    *list* (assembled into a `Program`) scored by a shared predicate. Every check
    runs the relevant pass on the program and inspects the result (some on the
    mixed-declaration program shape, so that the function- and
    non-procedure-declaration fields are not vacuous — see
    `ProcedureHasTypeAGen/TestSupport`); the shapes are identical across both
    harnesses, so name↔check is paired once here.
 -/
def procTransforms : List (Property (List Core.Procedure)) :=
  [ -- FilterProcedures
    ⟨PropertyNames.procFilterDeclsSublist,      checkFilterDeclsSublist⟩,
    ⟨PropertyNames.procFilterTargetsRetained,   checkFilterTargetsRetained⟩,
    ⟨PropertyNames.procFilterCalleeClosure,     checkFilterCalleeClosureRetained⟩,
    ⟨PropertyNames.procFilterOnlyProcsRemoved,  checkFilterOnlyProcsRemoved⟩,
    ⟨PropertyNames.procFilterUnreachableRemoved, checkFilterUnreachableRemoved⟩,
    ⟨PropertyNames.procFilterChangedFlag,       checkFilterChangedFlagValid⟩,
    ⟨PropertyNames.procFilterAnalysisPreserved, checkFilterAnalysisPreserving⟩,
    -- PrecondElim
    ⟨PropertyNames.procPrecondGeneratedWF,      checkPrecondGeneratedWF⟩,
    ⟨PropertyNames.procPrecondStripped,         checkPrecondPreconditionsStripped⟩,
    ⟨PropertyNames.procPrecondNonProcDecls,     checkPrecondNonProcDeclsPreserved⟩,
    ⟨PropertyNames.procPrecondProcsPreserved,   checkPrecondProceduresPreserved⟩,
    ⟨PropertyNames.procPrecondFuncsPreserved,   checkPrecondFunctionsPreserved⟩,
    ⟨PropertyNames.procPrecondNoDeclsRemoved,   checkPrecondNoDeclsRemoved⟩,
    ⟨PropertyNames.procPrecondOrderPreserved,   checkPrecondOrderPreserved⟩,
    ⟨PropertyNames.procPrecondChangedFlag,      checkPrecondChangedFlagValid⟩,
    ⟨PropertyNames.procPrecondCallSiteAsserts,  checkPrecondCallSiteAsserts⟩,
    ⟨PropertyNames.procPrecondFactoryGrows,     checkPrecondFactoryGrows⟩,
    ⟨PropertyNames.procPrecondFactoryComplete,  checkPrecondFactoryComplete⟩,
    ⟨PropertyNames.procPrecondFactoryStripped,  checkPrecondFactoryStripped⟩,
    ⟨PropertyNames.procPrecondDeclaredFactoryStripped,
                                                checkPrecondDeclaredFactoryStripped⟩,
    ⟨PropertyNames.procPrecondAnalysisPreserved, checkPrecondAnalysisPreserving⟩,
    -- ANFEncoder
    ⟨PropertyNames.procAnfDeclsLength,          checkAnfDeclsLength⟩,
    ⟨PropertyNames.procAnfNonProcsUnchanged,    checkAnfNonProcsUnchanged⟩,
    ⟨PropertyNames.procAnfHeadersPreserved,     checkAnfHeadersPreserved⟩,
    ⟨PropertyNames.procAnfFreshVarsDet,         checkAnfFreshVarsDet⟩,
    ⟨PropertyNames.procAnfOrderPreserved,       checkAnfOrderPreserved⟩,
    ⟨PropertyNames.procAnfControlFlow,          checkAnfControlFlowPreserved⟩,
    ⟨PropertyNames.procAnfChangedFlag,          checkAnfChangedFlagValid⟩,
    ⟨PropertyNames.procAnfAnalysisPreserved,    checkAnfAnalysisPreserving⟩ ]

/-- The two `changed`-flag properties that quantify over generated procedure
    lists. Same input shape as `procTransforms`, so both harnesses fold them the
    same way; kept in a separate bundle because they sweep *phase lists* rather
    than testing one named pass.

    `phaseAllChangedFlag` sweeps every phase, including `typeCheck` and
    `symbolicEval`; `phaseHonestChangedFlag` sweeps only the rest and is the
    regression guard. -/
def phaseChangedFlags : List (Property (List Core.Procedure)) :=
  [ ⟨PropertyNames.phaseAllChangedFlag,
     StrataGenerators.PhaseChangedFlag.checkAllPhasesChangedFlag⟩,
    ⟨PropertyNames.phaseHonestChangedFlag,
     StrataGenerators.PhaseChangedFlag.checkHonestPhasesChangedFlag⟩ ]

/-- The `changed`-flag properties with **no** generated input: each is a single
    constructed no-op witness (a phase plus a program it provably cannot change),
    whose verdict is the closed `Bool` `NoOpWitness.check`. Paired with names here
    for the same reason as the bundles above — neither harness ever handles the bare
    string.

    The bundle carries the whole witness rather than just its `Bool` so the Tyche
    panel can *display* the program the verdict was computed on: the two Plausible
    harnesses read `.check`, the panel reads `.check` and the phase/program too, and
    there is still only one copy of each witness. -/
def phaseNoOpWitnesses : List (String × StrataGenerators.PhaseChangedFlag.NoOpWitness) :=
  [ (PropertyNames.phaseIrrelevantAxiomsNoOp,
     StrataGenerators.PhaseChangedFlag.irrelevantAxiomsNoOp),
    (PropertyNames.phaseFilterNoOp,
     StrataGenerators.PhaseChangedFlag.filterNoOp) ]

/-- The printer-expressiveness properties with no generated input: the two
    confirmed gaps at factory-registered widths, plus the typechecker-vs-printer
    width divergence — each a closed `Bool`, since each is a claim about a
    specific width or operator rather than about a sampled program. -/
def printerWitnesses : List (String × Bool) :=
  [ (PropertyNames.printerBv128Literal,
     StrataGenerators.PrinterCoverage.checkBv128LiteralPrints),
    (PropertyNames.printerBvIntConversions,
     StrataGenerators.PrinterCoverage.checkBvIntConversionsPrint),
    (PropertyNames.printerBvWidthAgreement,
     StrataGenerators.PrinterCoverage.checkAllWidthsAgree) ]

/-- The six whole-program properties, each a generated `Program` scored by a shared
    predicate. The first states that the typechecker accepts them; the second pins
    the three program-level completeness gaps as the complete list of rejection
    causes; the last four are invariants of a well-typed program (vacuous on a
    gap-bearing draw).

    Counterexamples are minimized by the whole-program shrinker
    (`StrataGenerators.ProgramGen.Shrink`), which keeps every candidate well-typed
    by re-running Strata's own `Program.typeCheck`. The one exception is
    `programTypecheck`: its failures rest on the oracle *rejecting* the program, so
    no smaller candidate survives the filter and the witness is reported
    unshrunk — with a tag naming the gap (see the `Repr` for `GenProgram`). The
    other five shrink normally. -/
def programChecks : List (Property Core.Program) :=
  [ ⟨PropertyNames.programTypecheck,          checkProgramTypeCheckerComplete⟩,
    ⟨PropertyNames.programRejectionKnownGap,  checkProgramRejectionIsKnownGap⟩,
    ⟨PropertyNames.programNamesNodup,         checkProgramNamesNodup⟩,
    ⟨PropertyNames.programTypeCheckIdem,      checkProgramTypeCheckIdempotent⟩,
    ⟨PropertyNames.programStripMeta,          checkProgramStripMetaPreservesTyping⟩,
    ⟨PropertyNames.programEraseTypes,         checkProgramEraseTypesPreservesTyping⟩ ]

/-- **ADT-derived-call properties.** Both harnesses run the identical
    `Bool` check on a generated `Core.Program`, so name↔check is paired once here.

    Unlike the five conditional invariants in `programChecks`, these are
    *unconditional*: each is established by the fold itself rather than by the
    typechecker accepting the draw, so they stay non-vacuous on the ~60% of programs
    that trip one of the documented completeness gaps. That is what makes them the
    checks that actually watch the ADT-derived-call path. -/
def programADTProps : List (Property Core.Program) :=
  [ ⟨PropertyNames.programAllNamesNodup,  checkNamesNodup⟩,
    ⟨PropertyNames.programBlocksAccepted, checkDatatypeBlocksAccepted⟩,
    ⟨PropertyNames.programDerivedResolve, checkCalledDerivedAreDeclared⟩,
    ⟨PropertyNames.programDerivedOrdered, checkDerivedCallsFollowDeclaration⟩ ]

/-- The forty-five properties for the Core transform passes that carry no
    correctness proof, each a generated `Program` scored by a shared
    predicate from `ProgramGen/UnprovenTransforms`. The shapes are identical across
    both harnesses, so name↔check is paired once here.

    The last three are the obligation-preservation properties of §2.9, which run
    `InsertLoopInvariantAsserts`, `NondetElim` and `LoopInitHoist` each through
    `LoopElim` and then Strata's symbolic evaluator, and check that no proof
    obligation is lost. They pin a soundness defect in the **evaluator** that no
    other property here sees: a nondeterministic guard is named after the current
    path-condition depth rather than by a counter, so a second `if *` at the same
    depth silently drops every obligation to the end of the procedure.

    Counterexamples are minimized by the same whole-program shrinker the
    `programChecks` bundle uses (`Shrinkable GenProgram`), which keeps every
    candidate well-typed by re-running Strata's own `Program.typeCheck`. Unlike
    `programTypecheck`, whose failure *is* oracle rejection, each failure here is a
    property of a pass applied to a well-typed program, so a smaller well-typed
    witness exists and the minimizer reports it.

    `cseOutputTypechecks` and `cseFreshNamesFresh` are reachable only under a
    `#guard`, since `CommonSubexprElim` fires on no generated program at all. -/
def unprovenTransforms : List (Property Core.Program) :=
  [ -- IrrelevantAxioms (§2.1) — the relevance oracle
    ⟨PropertyNames.axiomsOnlyAxRemoved,      checkAxiomsOnlyAxRemoved⟩,
    ⟨PropertyNames.axiomsOrderPreserved,     checkAxiomsOrderPreserved⟩,
    ⟨PropertyNames.axiomsRetainedRelevant,   checkAxiomsRetainedRelevant⟩,
    ⟨PropertyNames.axiomsRemovedIrrelevant,  checkAxiomsRemovedIrrelevant⟩,
    ⟨PropertyNames.axiomsRemovedUnreachable, checkAxiomsRemovedNotSeedReachable⟩,
    ⟨PropertyNames.axiomsPrunedTypechecks,   checkAxiomsPrunedTypechecks⟩,
    ⟨PropertyNames.axiomsObligationsUnchanged, checkAxiomsObligationsUnchanged⟩,
    -- StructuredToUnstructured (§2.2) — the emitted CFG
    ⟨PropertyNames.s2uNoDanglingLabel,       checkS2uNoDanglingLabel⟩,
    ⟨PropertyNames.s2uLabelsNodup,           checkS2uLabelsNodup⟩,
    ⟨PropertyNames.s2uEntryExists,           checkS2uEntryExists⟩,
    ⟨PropertyNames.s2uOneFinish,             checkS2uOneFinish⟩,
    ⟨PropertyNames.s2uAllReachable,          checkS2uAllReachable⟩,
    ⟨PropertyNames.s2uCmdCountGrows,         checkS2uCmdCountGrows⟩,
    ⟨PropertyNames.s2uCfgPrintable,          checkS2uCfgPrintable⟩,
    -- DetToKleene (§2.3) — the dropped measure
    ⟨PropertyNames.kleeneMeasureAccepted,    checkKleeneMeasureAccepted⟩,
    -- LoopElim + InsertLoopInvariantAsserts (§2.4) — the verification conditions
    ⟨PropertyNames.loopVcAssertCount,        checkLoopVcAssertCount⟩,
    ⟨PropertyNames.loopBareAfterPass,        checkLoopBareAfterPass⟩,
    ⟨PropertyNames.loopVcIdempotent,         checkLoopVcIdempotent⟩,
    ⟨PropertyNames.loopVcStatFaithful,       checkLoopVcStatFaithful⟩,
    ⟨PropertyNames.loopVcSurvivesElim,       checkLoopVcSurvivesElim⟩,
    ⟨PropertyNames.loopNondetMeasure,        checkLoopNondetMeasureThrows⟩,
    ⟨PropertyNames.loopBlockLabelsNodup,     checkLoopBlockLabelsNodup⟩,
    ⟨PropertyNames.loopElimStatFaithful,     checkLoopElimStatFaithful⟩,
    -- CommonSubexprElim (§2.5) — fresh names and ordering
    ⟨PropertyNames.cseFreshNamesFresh,       checkCseFreshNamesFresh⟩,
    ⟨PropertyNames.cseAssertLabelsPreserved, checkCseAssertLabelsPreserved⟩,
    ⟨PropertyNames.cseFreshDeclOrder,        checkCseFreshDeclOrder⟩,
    ⟨PropertyNames.cseOutputTypechecks,      checkCseOutputTypechecks⟩,
    -- FunctionInlining (§2.6) — a pure expression transform
    ⟨PropertyNames.inlineFuelZeroIdentity,   checkInlineFuelZeroIdentity⟩,
    ⟨PropertyNames.inlineFuelMonotone,       checkInlineFuelMonotone⟩,
    ⟨PropertyNames.inlineTypePreserved,      checkInlineTypePreserved⟩,
    ⟨PropertyNames.inlineCaptureFree,        checkInlineCaptureFree⟩,
    ⟨PropertyNames.inlineEvalAgreement,      checkInlineEvalAgreement⟩,
    -- ProcedureInlining (§2.7) — freshening of the labels
    ⟨PropertyNames.inlineProcLabelsNodup,    checkInlineProcLabelsNodup⟩,
    ⟨PropertyNames.inlineProcAssertsNotLost, checkInlineProcAssertsNotLost⟩,
    ⟨PropertyNames.inlineProcStatsFaithful,  checkInlineProcStatsFaithful⟩,
    ⟨PropertyNames.inlineProcTypechecks,     checkInlineProcTypechecks⟩,
    ⟨PropertyNames.inlineProcAnalysisPreserved, checkInlineProcAnalysisPreserved⟩,
    ⟨PropertyNames.inlineProcSymbolicAgreement, checkInlineProcSymbolicAgreement⟩,
    -- NondetElim + LoopInitHoist (§2.8) — the unproven postconditions
    ⟨PropertyNames.nondetElimNoNondetGuard,  checkNondetElimNoNondetGuard⟩,
    ⟨PropertyNames.nondetElimFreshNames,     checkNondetElimFreshNames⟩,
    ⟨PropertyNames.hoistNoLoopBodyInits,     checkHoistNoLoopBodyInits⟩,
    ⟨PropertyNames.hoistPreservesUniqueInits, checkHoistPreservesUniqueInits⟩,
    -- The three loop passes under the symbolic evaluator (§2.9)
    ⟨PropertyNames.loopVcSymbolicNoLoss,     checkLoopVcSymbolicNoLoss⟩,
    ⟨PropertyNames.nondetElimSymbolicNoLoss, checkNondetElimSymbolicNoLoss⟩,
    ⟨PropertyNames.hoistSymbolicNoLoss,      checkHoistSymbolicNoLoss⟩ ]

/-- The thirteen properties for `LiftInternalFuncDecls`, the lambda
    lifting pass that hoists internal `funcDecl`s to closed top-level functions.
    Each takes a generated `Program`, injects a *capturing* internal function into
    it — `genFuncDeclStmt` draws its bodies with `genFunction []`, so a generated
    `funcDecl` is always closed and the pass would have nothing to capture — and
    sweeps the fifteen shapes of `LiftFuncDecls.allScenarios`.

    Only `LiftInternalFuncDeclsCorrect.lean`'s `run_noFuncDecl` is proved upstream
    (that is `liftNoResidualDecl`); the other twelve claims are unproved.

    `liftInjectionFires` is coverage rather than a claim about the pass: it scores
    that the injection really was lifted, so a draw the pass refuses cannot leave the
    other twelve vacuous in silence (it did, on 5 of 20 draws, before
    `normalizeAmbient`). -/
def liftFuncDecls : List (Property Core.Program) :=
  [ -- coverage first: the rest mean nothing without it
    ⟨PropertyNames.liftInjectionFires,     checkLiftInjectionFires⟩,
    -- P1 — closedness, the property the pass exists for
    ⟨PropertyNames.liftFuncsClosed,        checkLiftAllFuncsClosed⟩,
    ⟨PropertyNames.liftStrataClosed,       checkLiftStrataClosed⟩,
    -- P2/P3/P4 — the traversal
    ⟨PropertyNames.liftNoResidualDecl,     checkLiftNoResidualFuncDecl⟩,
    ⟨PropertyNames.liftIdempotent,         checkLiftIdempotent⟩,
    ⟨PropertyNames.liftIdentityNoDecl,     checkLiftIdentityWithoutFuncDecl⟩,
    -- P5/P10 — the emitted signature
    ⟨PropertyNames.liftParamsLead,         checkLiftParamsLead⟩,
    ⟨PropertyNames.liftTypeArgsClosed,     checkLiftTypeArgsClosed⟩,
    -- P6/P7 — name hygiene and scope correctness (the two defects)
    ⟨PropertyNames.liftFreshNames,         checkLiftFreshSnapshotNames⟩,
    ⟨PropertyNames.liftOutputTypechecks,   checkLiftOutputTypechecks⟩,
    ⟨PropertyNames.liftSnapshotsInScope,   checkLiftSnapshotsInScope⟩,
    -- P8 — the Johnsson fixpoint against an independent Def 4.6 implementation
    ⟨PropertyNames.liftFixpointMatchesRef, checkLiftFixpointMatchesReference⟩,
    -- P12 — rejection completeness
    ⟨PropertyNames.liftRejectsOnlyKnown,   checkLiftRejectsOnlyKnownTriggers⟩ ]

end Properties
