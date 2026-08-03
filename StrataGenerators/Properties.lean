import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.StmtHasTypeAGen.TestSupport
import StrataGenerators.ProcedureHasTypeAGen.TestSupport

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
`function` / `stmt` / `proc`. A handful of properties are exercised by only one
harness (noted per entry); they still live here so the catalog is the one place
property names are spelled.
-/

open Lambda Core Imperative
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Procedure.TestSupport

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

/-- Every catalog name, for the no-duplicate-names guard below. -/
def all : List String :=
  [ exprTypecheck, exprPreservation, exprProgress, exprFvarsPreserved,
    exprResolveAfterErase, exprSmtEvalAgreement,
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
    procAnfChangedFlag, procAnfAnalysisPreserved ]

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

end Properties
