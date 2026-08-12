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
/-- **FAILS honestly.** The SMT-LIB escape function `escapeSMTStringLit` has a
    guard that is a predicate for *8-bit* printability. Therefore it gives each
    codepoint of U+00A1 or more as raw UTF-8. cvc5 rejects such a literal outright,
    and z3 measures it incorrectly, because `str.len` counts bytes and not
    codepoints. The property needs no solver, because its oracle is "the emitted
    literal is printable ASCII", which is the requirement of SMT-LIB 2.6+ itself.
    Thus the property runs in the default suite, and nobody can skip it. It is
    non-vacuous only because `genInterestingString` draws non-ASCII characters.
    Under `String.arbitrary` of Basalt, which is alphanumeric only, the property
    passes on each input, and that is how the defect stayed unknown. The property
    must turn green after a correction to the escape function. -/
def exprSmtStringEscaping : String := "expr: SMT string literals are printable ASCII"

/-- **FAILS honestly.** `Factory.eq` folds a comparison of two literals by
    *structural* equality, and `Decimal`, the representation of a real in the SMT
    dialect, has no normal form. Therefore two spellings of one value, such as
    `3e0` and `30e-1`, fold to `false`, which puts a false fact into the term. The
    path for `Int` is correct, because `Int` is canonical, and `eq_correct_int`
    proves it. There is no `eq_correct_real`. The property needs no solver. It is
    non-vacuous only because the generator builds a second spelling of one value; a
    pair of independent draws is almost never equal. The defect is **latent**: each
    real literal of Core reaches SMT through `Decimal.fromRat`, which normalizes,
    so no path in Strata reaches it today. -/
def realDecimalEqFold : String := "real: Decimal eq fold agrees with value equality"
/-- **FAILS honestly.** `Factory.eq` on a real is structural, but `TermPrim.lt` is
    by value. Therefore, for two spellings of one value, each of `lt` in both
    directions and the fold of `eq` is `false`, so no one of the three holds and
    the comparator is not a total order. One correction fixes this and
    [[realDecimalEqFold]]: make `eq` compare by value. Normalization of `Decimal`
    fixes the fold alone, and leaves `eq` and `lt` on different notions of
    equality. Latent for the same reason, and `TermPrim.lt` has no caller in the
    tree. -/
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
def stmtTypecheck          : String := "stmt: typechecker accepts generated statements (#1)"
def stmtLoopElimPreserves  : String := "stmt: LoopElim preserves typeability (#3)"
def stmtLoopElimZeroLoops  : String := "stmt: LoopElim eliminates all loops (#4)"
def stmtAnfIdempotent      : String := "stmt: ANF is idempotent (#5a)"
def stmtAnfPreservesTyping : String := "stmt: ANF preserves typeability (#5b)"
def stmtKleeneDefinedIff   : String := "stmt: DetToKleene defined iff supported (#6)"
def stmtMapExprsId         : String := "stmt: mapExprs id = id (#9)"

-- ── Procedure-generator ↔ transform-pass properties ──────────────────
-- Exercised against three Core transform passes (FilterProcedures, PrecondElim,
-- ANFEncoder). There is now one property per *named field* of the
-- three `*PhaseCorrect` structures in `Strata/Transform/CustomSpecifications.lean`
-- — including the `ChangedFlagValid` and `PreservesCachedAnalysesWF` fields shared
-- by all three — so the coverage of those specs is complete rather than partial.
-- FOUR of these FAIL honestly, pinning real defects rather than masking them:
--   * `procFilterChangedFlag` — FilterProcedures hardcodes `changed := true` even
--     when it removes nothing;
--   * `procPrecondChangedFlag` — PrecondElim's `.funcDecl` branch inserts a `$$wf`
--     block for obligations in a declared function's *body* while deriving
--     `changed` only from the declaration's own preconditions;
--   * `procPrecondFactoryStripped` — the field as written is unsatisfiable for a
--     realistically seeded run: `Core.Factory`'s 58 partial builtins keep the very
--     preconditions the pass exists to discharge (a spec bug);
--   * `procPrecondDeclaredFactoryStripped` — the same claim restricted to the
--     program's *own* declarations, which isolates the pass-side cause: each
--     declared function is pushed into the factory before being stripped.
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

/-- **FAILS honestly.** `RemoveIrrelevantAxioms` on a program with no axioms at
    all cannot prune anything, yet `IrrelevantAxioms.lean:81` returns
    `(true, pruned)` unconditionally. -/
def phaseIrrelevantAxiomsNoOp : String :=
  "phase: RemoveIrrelevantAxioms changed flag is faithful on a no-op"
/-- **FAILS honestly.** Restates the already-reported `FilterProcedures` bug on a
    constructed all-targets witness, so the uniform sweep is self-contained. -/
def phaseFilterNoOp : String :=
  "phase: FilterProcedures changed flag is faithful on a no-op"
/-- **FAILS honestly.** Uniform sweep over every phase of `corePipelinePhases`
    plus `RemoveIrrelevantAxioms`; red while any of the four known sites stands.
    This is the regression gate that catches a *newly added* hardcoding phase. -/
def phaseAllChangedFlag : String :=
  "phase: every pipeline phase has a faithful changed flag"
/-- Every phase *except* the four known hardcoded-`true` sites. Expected to PASS;
    it is what guards the honestly-computing phases against regression. -/
def phaseHonestChangedFlag : String :=
  "phase: non-hardcoded pipeline phases have a faithful changed flag"

-- ── Printer-expressiveness properties (#69 P2, #48) ──────────────────────
-- See `StrataGenerators.PrinterCoverage`. The oracle is "the printer logged no
-- conversion error", which needs no parser and names the offending construct.

/-- **FAILS honestly (~50% of programs at the `GenProgram` bounds; ~86% at
    `numDecls = 6`).** `Core.formatProgram` substitutes a placeholder and logs an
    error rather than failing, so an unprintable construct can round-trip
    "successfully" as a *different* program. -/
def printerNoConversionError : String :=
  "printer: no conversion error on generated programs"
/-- **FAILS honestly.** `bitvec 128` is factory-registered with a grammar
    production, but `lconstToExpr` logs `unsupported bitvec width: 128`. -/
def printerBv128Literal : String :=
  "printer: bitvec 128 literals are printable"
/-- **FAILS honestly (18/18).** No `Bv{w}.ToInt` / `Bv{w}.ToUInt` / `Int.ToBv{w}`
    is printable at any registered width — no grammar production, no printer arm. -/
def printerBvIntConversions : String :=
  "printer: Bv/Int conversion operators are printable"
/-- **FAILS honestly (60/64 widths) — closes out #48.** `Function.typeCheck`
    accepts `bitvec w` for every `w`, but the printer supports exactly
    `[1, 8, 16, 32, 64]`. Note this is *not* the powers of two: `2`, `4` and `128`
    all typecheck and all fail to print. -/
def printerBvWidthAgreement : String :=
  "printer: every typecheckable bitvec width is printable"

-- ── Whole-program-generator properties ───────────────────────────────
-- `genProgram` produces a whole `Program` (every declaration kind, real ambient
-- context threaded across the fold) and is proven sound against `ProgramHasTypeA`.
-- The first property below therefore SHOULD hold and FAILS honestly, on either of
-- two reachable rejection causes (the third classified cause, `distinct-fvar`, is
-- unreachable from `genProgram`); the second pins the classified
-- causes as the complete list; the remaining four are invariants of a well-typed
-- program, three of which hold while `programTypeCheckIdem` fails intermittently.
-- See the module doc of `ProgramGen/Shrink`.

/-- **FAILS honestly** (~40% of draws) on the program-level completeness gaps:
    measure-without-body and the hypothetical `corePolyOps` schemes. -/
def programTypecheck : String := "program: typechecker accepts generated programs"
def programRejectionKnownGap : String :=
  "program: typechecker rejections are only the known gaps"
-- The four invariants of a well-typed program. Each is conditional on the input
-- typechecking (so vacuous on a gap-bearing draw, a genuine claim otherwise), and
-- — unlike `programTypecheck` — a counterexample to any of them IS shrinkable,
-- since its failure does not depend on the oracle rejecting the program.
def programNamesNodup      : String := "program: getNames of a well-typed program are distinct"
/-- **FAILS intermittently** (~1 in 500 single-function draws): the checker's output
    keeps a freshened type variable for a type parameter used only in a body binder
    annotation, while restoring `typeArgs` without it. -/
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
    programDerivedOrdered ]

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
    context). The richer eval-agreement panel (#5) is *not* here — its Tyche shape
    differs — but shares its name via `PropertyNames.cmdEvalRunAgreement`. -/
def cmdSingleVerdict : List (Property (Cmd Expression × VarCtx)) :=
  [ ⟨PropertyNames.cmdInitFresh,             fun (c, _)   => checkInitFreshNotInRhs c⟩,
    ⟨PropertyNames.cmdExprTypecheck,         fun (c, _)   => checkExprTypechecks c⟩,
    ⟨PropertyNames.cmdSetPreservesVar,       fun (c, ctx) => checkSetPreservesVar c ctx⟩,
    ⟨PropertyNames.cmdStoreTypePreservation, fun (c, ctx) => checkStoreTypePreservation c ctx⟩ ]

/-- The six statement-transform / typechecker properties, each a well-typed
    statement list scored by a shared predicate. The Kleene-definedness property
    (#6) is *not* here — its Tyche panel records extra breakdown — but shares its
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

    All pass on generated input EXCEPT four, which fail honestly: the two
    `*ChangedFlag` properties (real `changed`-flag bugs in FilterProcedures and
    PrecondElim) and the two `*FactoryStripped` properties (an unsatisfiable spec
    field, and the pass pushing unstripped functions into the factory). -/
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

    `phaseAllChangedFlag` is expected to FAIL (`typeCheck` and `symbolicEval` are
    in the swept list and both hardcode `true`); `phaseHonestChangedFlag` is
    expected to PASS and is the actual regression guard. -/
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
    width divergence of #48 — each a closed `Bool`, since each is a claim about a
    specific width or operator rather than about a sampled program. -/
def printerWitnesses : List (String × Bool) :=
  [ (PropertyNames.printerBv128Literal,
     StrataGenerators.PrinterCoverage.checkBv128LiteralPrints),
    (PropertyNames.printerBvIntConversions,
     StrataGenerators.PrinterCoverage.checkBvIntConversionsPrint),
    (PropertyNames.printerBvWidthAgreement,
     StrataGenerators.PrinterCoverage.checkAllWidthsAgree) ]

/-- The six whole-program properties, each a generated `Program` scored by a shared
    predicate. The first FAILS honestly on the three program-level completeness
    gaps; the second pins those three as the complete list of causes; the last four
    are invariants of a well-typed program (vacuous on a gap-bearing draw), three of
    which hold while `programTypeCheckIdem` FAILS intermittently — the checker's own
    output is not always re-checkable.

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

    All four pass on generated input, and — unlike the five conditional invariants
    in `programChecks` — they are *unconditional*: each is established by the fold
    itself rather than by the typechecker accepting the draw, so they stay
    non-vacuous on the ~60% of programs that trip one of the documented
    completeness gaps. That is what makes them the checks that actually watch the
    ADT-derived-call path; `programTypecheck` cannot, since it fails on those
    draws for reasons unrelated to this generator. -/
def programADTProps : List (Property Core.Program) :=
  [ ⟨PropertyNames.programAllNamesNodup,  checkNamesNodup⟩,
    ⟨PropertyNames.programBlocksAccepted, checkDatatypeBlocksAccepted⟩,
    ⟨PropertyNames.programDerivedResolve, checkCalledDerivedAreDeclared⟩,
    ⟨PropertyNames.programDerivedOrdered, checkDerivedCallsFollowDeclaration⟩ ]

end Properties
