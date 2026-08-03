-- Only the *code* modules are imported here — never a proof/`TestSupport` sibling
-- that pulls in Mathlib. `ProcedureHasTypeAGen.Core` gives the generator and the
-- Core AST; `HasTypeAGen.TestSupport` gives the operator contexts `coreMonoOps` /
-- `corePartialOps` (Mathlib-free); the three `Strata.Transform.*` modules are the
-- passes under test. Importing `StmtHasTypeAGen.TestSupport` here would make this
-- file unimportable alongside the transform passes (both Strata and Batteries
-- define `List.Forall₂`).
import StrataGenerators.ProcedureHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.Transform.FilterProcedures
import Strata.Transform.PrecondElim
import Strata.Transform.ANFEncoder
import Strata.Languages.Core.Factory

open Lambda Core Imperative

/-!
# Shared test support for the `genProcedure` generator vs. Core transform passes

Utilities shared between the LSpec property suite and the Tyche panels (both in
the merged `TestMain` driver) for property-based testing of `genProcedure`
(defined in `ProcedureHasTypeAGen/Core.lean`), which generates well-typed Strata
Core procedures (`Procedure`) satisfying the `ProcHasTypeA` typing relation. The
generator is proven both **sound** and **complete** w.r.t. that relation (see
`ProcedureHasTypeAGen.lean`), so every generated procedure is a certified
well-typed input — an ideal oracle input for the three Core *transformation*
passes exercised here:

- **FilterProcedures** (`filterProceduresPipelinePhase`) — removes procedures
  unreachable from a target entry set.
- **PrecondElim** (`precondElimPipelinePhase`) — strips partial-function
  preconditions and emits well-formedness (`$$wf`) checks.
- **ANFEncoder** (`anfEncoderPipelinePhase`) — hoists sub-expressions into fresh
  A-normal-form `init`s.

## Relationship to the declarative specification

Every check predicate below is the executable image of **one named field** of the
three `*PhaseCorrect` structures in the specification file
`Strata/Transform/CustomSpecifications.lean` (branch `jlee/transform-specs`), and
the coverage is now *complete*: each field of

- `Core.FilterProcedures.FilterProcedurePhaseCorrect` (`filterCorrect`'s five
  `FilterCorrect` fields, `changedFlagValid`, `analysisPreserving`),
- `Core.PrecondElim.PrecondElimPhaseCorrect` (`precondElimCorrect`'s seven
  `PrecondElimCorrect` fields, `factoryCorrect`'s three
  `PrecondElimFactoryCorrect` fields, `changedFlagValid`, `analysisPreserving`),
- `Core.ANFEncoder.ANFEncoderPhaseCorrect` (`anfCorrect`'s six
  `ANFEncoderCorrect` fields, `changedFlagValid`, `analysisPreserving`)

has a `check*` counterpart here, named after the spec field and carrying the
field name in its docstring. Three shared obligations recur across all three
passes and are therefore decided once, by predicates reused by all three:

- `ChangedFlagValid pass` — `changed = true ↔ progOut ≠ progIn`, decided with the
  derived `DecidableEq Program` (see the honest-failure notes below);
- `PreservesCachedAnalysesWF pass` — `CallGraphWF cgIn progIn → CallGraphWF cgOut
  progOut`, decided by `callGraphWF` below, which is a field-by-field executable
  transcription of the spec's `CallGraphWF` structure;
- `Sublist`-shaped order properties, decided by Lean's `Decidable (List.Sublist
  ..)` instance directly on `Decl` / on the declaration-name list — the spec's own
  formulation, not a hand-rolled proxy.

## Two program shapes

The spec fields quantify over *all* declaration kinds, but `genProcedure`
produces procedures only, so a program assembled purely from generated
procedures leaves the function- and non-procedure-declaration fields
(`onlyProcsRemoved`, `nonProcDeclsPreserved`, `functionsPreserved`,
`noDeclsRemoved`, `factoryComplete`, `nonProcsUnchanged`) vacuous. Two
assemblies are therefore provided:

- `mkProgram ps` — one `.proc` declaration per generated procedure. Used by every
  property whose spec field concerns procedures, ordering, or the `changed` flag.
- `mkMixedProgram ps` — the same procedures, but with each body's inline
  `funcDecl` statements **lifted** to top-level `.func` declarations (dropping the
  now-redundant inline declaration, deduplicated by name so PrecondElim's
  "already in factory" guard cannot fire), preceded by a fixed `.type`, `.ax` and
  `.distinct` declaration. Used by exactly the six fields above, so they bite on
  real generated function declarations instead of passing vacuously. Nothing is
  invented: the lifted functions are the ones `genFunction` drew (see point 3
  below), merely relocated from statement position to declaration position.

## What the current generator can and cannot exercise

`genProcedure` builds a *single* procedure with a structured body drawn from
`genStmtChain`, at the operator context `TestScaffold` hands it: `corePartialOps`,
i.e. `coreMonoOps` plus the four precondition-bearing `Int.Safe{Div,Mod,DivT,ModT}`
operators. Three facts about that body shape bound what these properties can test:

1. **Procedure calls, wired into an acyclic call DAG (issue #37).** `genCallStmt`
   (`StmtHasTypeAGen/Core.lean`, proven sound in `GenCallStmtSound.lean`) emits
   `call` statements against a non-empty `procs : ProcSigCtx`, and `genProcedure`
   now threads such a context into `genStmtChain`
   (`ProcedureHasTypeAGen/Core.lean`). The two harnesses (`TestScaffold.genProcsWith`
   and `TycheViz.genProcsForTyche`) exploit this by generating the procedures
   *left to right*: body `i` is generated against the front-aligned signatures of
   the already-generated monomorphic siblings `0..i-1` (named `P0…P{i-1}`, matching
   the `relabelProcs` renaming), so no cycles or self-recursion arise. Only
   monomorphic siblings (`typeArgs = []`) become call targets — both `genCallStmt`
   and `ProcSigCorresponds` require the callee to be monomorphic.

   So a generated program's call graph now carries real edges: `call P{j}` for
   `j < i` appears in body `i`, procedure `0` is still a leaf, and the callee-closure
   / call-graph dimensions of `FilterCorrect.calleeClosureRetained`,
   `FilterProcedures`/`PrecondElim` `PreservesCachedAnalysesWF` are no longer
   vacuous on generated input. The hand-built `callerCalleeProgram` guard is kept as
   a deterministic pin of a fixed multi-edge shape.

   Because a body may reach a non-target through the call graph, `callerTargets`
   below (a *strict subset* of the procedures) no longer implies every non-target
   is unreachable. That is handled where it matters: `checkFilterUnreachableRemoved`
   already compares against the transitive *closure* `targets ++
   cgIn.getAllCalleesClosure targets`, so a non-target reachable from a target is
   correctly *not* obliged to disappear (see `callerTargets`).

2. **Partial-function calls, but only in bodies.** Because `corePartialOps`
   carries the `Int.Safe*` operators — each of which has a `y ≠ 0` precondition in
   `Core.Factory` — generated expressions *do* invoke partial functions, so
   PrecondElim genuinely fires (empirically on ~6% of generated programs) rather
   than running as a no-op. But on the `mkProgram` shape the obligations land
   exclusively **inside procedure bodies**: a generated procedure's contract
   clauses are also drawn from the same context, yet `mkContractWFProc` only emits
   a `$$wf` *procedure* when a contract clause calls a partial function, which is
   rarer still and was not observed over 2000 samples. On the `mkMixedProgram`
   shape, by contrast, a lifted function whose body or precondition calls a
   partial function *does* produce a top-level `$$wf` procedure via
   `mkFuncWFProc` — which is what makes `checkPrecondGeneratedWF` non-vacuous.

3. **Declared preconditions, over formals only.** `genFunction` emits an optional
   `requires` clause drawn over the function's own formal parameters (mandatory:
   `FuncWF.precond_freevars` requires a precondition's free variables to be a
   subset of the input names), biased 3:1 toward clauses that actually mention a
   formal. So an inline `funcDecl` can be *declared* partial, not merely call a
   partial operator — which is what makes PrecondElim's precondition-*stripping*
   path (`preconditionsStripped`), the factory properties, and
   `functionsPreserved` reachable from generated input.

## The three honest failures

### `ChangedFlagValid` for FilterProcedures

`filterProceduresPipelinePhase` hardcodes its return to `(true, filtered)`
(FilterProcedures.lean:82). So when the target set already covers every
procedure — nothing is removed and `progOut = progIn` — the pass *still* reports
`changed = true`, violating `ChangedFlagValid` (`changed ↔ progOut ≠ progIn`).
`checkFilterChangedFlagValid` states that property honestly against the
all-targets scenario and therefore **fails**, surfacing the real bug exactly as
the repo's other honest-gap properties (`stmt #1`, function completeness) do.

### `ChangedFlagValid` for PrecondElim

`checkPrecondChangedFlagValid` states the same `changed ↔ progOut ≠ progIn`
contract for PrecondElim, and it too **fails** — but for a different, narrower
reason, and this one is a *false negative* (the pass rewrites the program while
reporting `changed = false`). The culprit is the `.funcDecl` branch of
`PrecondElim.transformStmt` (`PrecondElim.lean:318–338`): when a statement declares
an inline function, the branch emits a `{name}$$wf` block holding the asserts
collected from the function's **preconditions and body**, but returns
`(hasPreconds, …)` — a flag computed *only* from `!decl.preconditions.isEmpty`.
So a declared function with no preconditions of its own whose *body* calls a
partial function (e.g. `function f() : int { Int.SafeDiv(0, -2) }`) gets a `$$wf`
block inserted and is still reported unchanged. Empirically this hits ~0.5% of
generated programs, against ~6% on which the pass fires correctly.

Both `changed`-flag properties use full structural equality on `Program`, which
is available: `Program`, `Decl` and `Procedure.Header` all derive `DecidableEq`,
and `Strata.DL.Imperative.Stmt` supplies a hand-rolled `DecidableEq (Stmt P C)`
instance (`Stmt.lean:194`) that the derived `Decl` instance uses. This comparison
includes metadata, which is what we want and is not a source of spurious
failures: `transformStmt` re-emits every unchanged statement with its original
`md` untouched, and only the freshly generated asserts carry the
`propertySummary`-stripped metadata.

### `PrecondElimFactoryCorrect.factoryStripped`

`checkPrecondFactoryStripped` transcribes the field verbatim — *every* entry of
the output `Lambda.Factory` has `preconditions = []` — and **fails on every
input, including the empty program**, for two independent reasons:

1. The pass is seeded with `Core.Factory` (as `Core.Verifier` seeds it in
   production, and as it must be, since PrecondElim early-returns `(false, prog)`
   on a `none` factory). 58 of its 310 entries are the partial builtins
   (`Int.SafeDiv`, `Sequence.select`, …) *whose preconditions are the pass's
   entire reason for existing*. Nothing in the pass strips them, so the field
   cannot hold for any seeded run.
2. Independently, the pass pushes each declared function into the factory
   **before** stripping it: both `precondElim`'s `.func` branch
   (`PrecondElim.lean:412`, `F.push func.toLFunc` then `func' := {func with
   preconditions := []}`) and `transformStmt`'s `.funcDecl` branch
   (`PrecondElim.lean:326`) leave the *declaration* stripped in the program but
   the *factory copy* carrying its preconditions.

Cause (1) says the field as written is unsatisfiable for a realistically seeded
run — a specification bug, not a pass bug. Cause (2) is a real pass/spec
divergence and is pinned separately by `checkPrecondDeclaredFactoryStripped`,
which restricts the same claim to the functions the *program* declares and so
fails only when the program declares one. Both are stated rather than quietly
weakened; the deterministic `#guard`s at the end of the file pin each cause
independently.

## The FilterProcedures `noFilter` / call-graph divergence

`checkFilterAnalysisPreserving` (the `PreservesCachedAnalysesWF` field) passes on
generated input, but it is **not** vacuous and it does catch a real divergence
that generated input cannot reach: `FilterProcedures.run` retains a procedure
with `noFilter := true` in the declaration list while filtering it *out* of the
cached call graph (both maps are filtered by `isNeededProc`, which ignores
`noFilter` — FilterProcedures.lean:47–66). The retained procedure then has no
`callees` entry, breaking `CallGraphWF.complete` for the output pair. Generated
procedures all carry `noFilter := false` (`ProcedureHasTypeAGen/Core.lean:160`),
so the property cannot fail on generated input; the hand-built
`noFilterProgram` guard at the end of the file pins the divergence
deterministically instead.
-/

namespace StrataGenerators.Procedure.TestSupport

-- ── Program assembly + pipeline plumbing ─────────────────────────────────

/-- Assemble a `Program` from a procedure list, one `.proc` declaration each. -/
def mkProgram (ps : List Procedure) : Program :=
  { decls := ps.map (Decl.proc · .empty) }

/-- The structured statement list of a procedure body (`[]` for a CFG body —
    `genProcedure` only ever produces structured bodies, so this is total on
    generated input). -/
def bodyStmts : Procedure.Body → List Statement
  | .structured ss => ss
  | .cfg _ => []

mutual
/-- The inline function declarations in a statement, at any nesting depth. -/
def stmtFuncDecls (s : Statement) : List (Imperative.PureFunc Expression) :=
  match s with
  | .funcDecl d _ => [d]
  | .block _ b _ => stmtsFuncDecls b
  | .ite _ t e _ => stmtsFuncDecls t ++ stmtsFuncDecls e
  | .loop _ _ _ b _ => stmtsFuncDecls b
  | .cmd _ | .exit _ _ | .typeDecl _ _ => []

/-- The inline function declarations in a statement list, at any nesting depth. -/
def stmtsFuncDecls (ss : List Statement) : List (Imperative.PureFunc Expression) :=
  match ss with
  | [] => []
  | s :: rest => stmtFuncDecls s ++ stmtsFuncDecls rest
end

mutual
/-- Drop every inline `funcDecl` whose name is in `names`, at any nesting depth. -/
def stmtDropFuncDecls (names : List String) (s : Statement) : List Statement :=
  match s with
  | .funcDecl d md => if names.contains d.name.name then [] else [.funcDecl d md]
  | .block l b md => [.block l (stmtsDropFuncDecls names b) md]
  | .ite c t e md => [.ite c (stmtsDropFuncDecls names t) (stmtsDropFuncDecls names e) md]
  | .loop g m i b md => [.loop g m i (stmtsDropFuncDecls names b) md]
  | .cmd c => [.cmd c]
  | .exit l md => [.exit l md]
  | .typeDecl t md => [.typeDecl t md]

/-- Drop every inline `funcDecl` whose name is in `names` from a statement list. -/
def stmtsDropFuncDecls (names : List String) (ss : List Statement) : List Statement :=
  match ss with
  | [] => []
  | s :: rest => stmtDropFuncDecls names s ++ stmtsDropFuncDecls names rest
end

/-- The generated inline functions that can be lifted to top-level `.func`
    declarations, deduplicated by name (first occurrence wins). An inline
    declaration is liftable when `Function.ofPureFunc` accepts it — i.e. its
    formals and result are monotypes, which `genFunction` always produces.

    Deduplication matters: PrecondElim `throw`s "already in factory" if the same
    function name is pushed twice, and a thrown pass makes every property vacuous
    (`runPhase` returns `none`). Since *all* inline declarations bearing a lifted
    name are dropped from the bodies (see `mkMixedProgram`), no name is ever
    pushed twice, whether or not its other occurrences were themselves liftable. -/
def liftableFuncs (ps : List Procedure) : List Function :=
  let raw := ps.flatMap fun p => stmtsFuncDecls (bodyStmts p.body)
  (raw.filterMap fun d => (Function.ofPureFunc d).toOption).foldl
    (fun acc f => if acc.any (·.name.name == f.name.name) then acc else acc ++ [f]) []

/-- A fixed abstract type declaration, present in every `mkMixedProgram`. -/
def fixedTypeDecl : Decl := .type (.con { name := "TestSupportT", params := [] }) .empty

/-- A fixed (trivially true) axiom declaration, present in every `mkMixedProgram`. -/
def fixedAxiomDecl : Decl :=
  .ax { name := "testSupportAx", e := .const () (.boolConst true) } .empty

/-- A fixed `distinct` declaration, present in every `mkMixedProgram`. -/
def fixedDistinctDecl : Decl :=
  .distinct ⟨"testSupportDistinct", ()⟩
    [.const () (.intConst 0), .const () (.intConst 1)] .empty

/-- The three fixed non-procedure, non-function declarations. Their only job is
    to make `onlyProcsRemoved` / `nonProcDeclsPreserved` / `nonProcsUnchanged`
    non-vacuous: all three passes are supposed to carry them through untouched
    (`.type (.con …)`, `.ax` and `.distinct` all hit the catch-all branch of
    `precondElim`, the `other` branch of `anfEncodeProgram`, and the
    non-`.proc` branch of `FilterProcedures.run`'s filter). -/
def fixedNonProcDecls : List Decl := [fixedTypeDecl, fixedAxiomDecl, fixedDistinctDecl]

/-- Assemble a `Program` whose declaration list exercises *all* the declaration
    kinds the specifications quantify over: the three `fixedNonProcDecls`, then
    one top-level `.func` per liftable generated inline function, then one `.proc`
    per generated procedure with those inline declarations removed. See the module
    doc ("Two program shapes") for why this exists and which properties use it. -/
def mkMixedProgram (ps : List Procedure) : Program :=
  let fs := liftableFuncs ps
  let names := fs.map (·.name.name)
  let procs := ps.map fun p =>
    Decl.proc { p with body := .structured (stmtsDropFuncDecls names (bodyStmts p.body)) } .empty
  { decls := fixedNonProcDecls ++ fs.map (Decl.func · .empty) ++ procs }

/-- The transform state a pass is run in: the `Factory` is seeded with
    `Core.Factory` (PrecondElim early-returns `(false, prog)` if it is `none`, so
    an unseeded factory would make every PrecondElim property vacuous), and the
    cached call graph is seeded with the program's own `toProcedureCG` (which
    FilterProcedures consults, falling back to recomputing it only if absent). -/
def mkState (prog : Program) : Transform.CoreTransformState :=
  { Transform.CoreTransformState.emp with
    factory := some Core.Factory,
    cachedAnalyses := { callGraph := some prog.toProcedureCG } }

/-- Run a pipeline phase on a program from a freshly-seeded state, returning the
    `(changed, output)` pair together with the final transform state, or `none` if
    the pass raised a diagnostic. The final state is what the `analysisPreserving`
    and factory properties inspect. -/
def runPhaseSt (ph : Core.PipelinePhase) (prog : Program) :
    Option ((Bool × Program) × Transform.CoreTransformState) :=
  match Transform.runWith prog ph.transform (mkState prog) with
  | (.ok r, st) => some (r, st)
  | (.error _, _) => none

/-- Run a pipeline phase on a program from a freshly-seeded state, returning the
    `(changed, output)` pair, or `none` if the pass raised a diagnostic. -/
def runPhase (ph : Core.PipelinePhase) (prog : Program) : Option (Bool × Program) :=
  (runPhaseSt ph prog).map (·.1)

/-- The pretty-printed names of the procedure declarations in a program, in
    order. Mirrors `FilterProcedures.programProcNames` from the spec file. -/
def programProcNames (prog : Program) : List String :=
  prog.decls.filterMap fun
    | .proc p _ => some (CoreIdent.toPretty p.header.name)
    | _ => none

/-- Find the first procedure declaration with the given pretty-printed name. -/
def findProc (prog : Program) (name : String) : Option Procedure :=
  prog.decls.findSome? fun
    | .proc p _ => if CoreIdent.toPretty p.header.name == name then some p else none
    | _ => none

/-- Find the first top-level function declaration with the given name. -/
def findFunc (prog : Program) (name : String) : Option Function :=
  prog.decls.findSome? fun
    | .func f _ => if CoreIdent.toPretty f.name == name then some f else none
    | _ => none

-- ── Spec equality on the decidable-eq components ──────────────────────────
-- `Procedure.Header` derives `DecidableEq`; `Procedure.Spec` does not, but its
-- two `ListMap CoreLabel Procedure.Check` fields do (both `CoreLabel` and
-- `Procedure.Check` are `DecidableEq`), so spec equality is decided field-wise.

/-- Structural equality of two procedure specs (pre- and postconditions). -/
def specEq (s t : Procedure.Spec) : Bool :=
  decide (s.preconditions = t.preconditions) && decide (s.postconditions = t.postconditions)

/-- Structural equality of two procedure headers (derived `DecidableEq`). -/
def headerEq (h k : Procedure.Header) : Bool := decide (h = k)

-- ══ CallGraph well-formedness (`Core.CallGraphWF`) ════════════════════════
-- `PreservesCachedAnalysesWF` — a field of all three `*PhaseCorrect` structures —
-- is an implication between two `CallGraphWF` claims, so it needs `CallGraphWF`
-- as a *decision procedure*. The three definitions below transcribe the spec's
-- `CalleesCountEqual` and the four `CallGraphWF` fields field by field.

/-- **`Core.CalleesCountEqual`.** Every callee's recorded multiplicity equals its
    occurrence count in the procedure's body. The spec quantifies over *all*
    strings; ranging over `k`'s keys together with the actual call list is
    faithful, because outside that union both sides are `0` (`k[c]?.getD 0 = 0`
    and `calls.count c = 0`). -/
def calleesCountEqual (k : Std.HashMap String Nat) (p : Procedure) : Bool :=
  let calls := Core.extractCallsFromProcedure p
  ((k.keys ++ calls).dedup).all fun c => k[c]?.getD 0 == calls.count c

/-- **`Core.CallGraphWF`**, decided field by field:

    * `sound` — every `callees` key is a procedure of the program, with matching
      per-callee counts;
    * `complete` — every procedure of the program has a `callees` entry, with
      matching per-callee counts;
    * `noZeroCount` — no recorded multiplicity is `0`;
    * `callersTranspose` — `callers` is the transpose of `callees`. The spec's
      biconditional is decided by checking both inclusions over the entries that
      actually exist (each `(a, b, n)` edge of one map must appear in the other),
      which is exactly the two directions of the `↔`. -/
def callGraphWF (cg : CallGraph) (prog : Program) : Bool :=
  let sound := cg.callees.toList.all fun (caller, k) =>
    prog.decls.any fun
      | .proc p _ => CoreIdent.toPretty p.header.name == caller && calleesCountEqual k p
      | _ => false
  let complete := prog.decls.all fun
    | .proc p _ =>
      match cg.callees[CoreIdent.toPretty p.header.name]? with
      | some k => calleesCountEqual k p
      | none => false
    | _ => true
  let noZeroCount := cg.callees.toList.all fun (_, k) => k.toList.all fun (_, n) => n != 0
  let callersTranspose :=
    (cg.callees.toList.all fun (a, k) =>
      k.toList.all fun (b, n) => (cg.callers[b]?.bind (·[a]?)) == some n) &&
    (cg.callers.toList.all fun (b, k) =>
      k.toList.all fun (a, n) => (cg.callees[a]?.bind (·[b]?)) == some n)
  sound && complete && noZeroCount && callersTranspose

/-- **`Core.PreservesCachedAnalysesWF`** for one phase and one input program: if
    the seeded input call graph is well-formed for the input program, the phase's
    output call graph is well-formed for the output program. A pass that drops the
    cached graph (`callGraph := none`) discharges the obligation vacuously — the
    spec's conclusion is guarded by `st'.cachedAnalyses.callGraph = .some cgOut` —
    so `none` counts as a pass here too. -/
def checkAnalysisPreserving (ph : Core.PipelinePhase) (prog : Program) : Bool :=
  match runPhaseSt ph prog with
  | some ((_, out), st') =>
    !callGraphWF prog.toProcedureCG prog ||
      (match st'.cachedAnalyses.callGraph with
       | some cgOut => callGraphWF cgOut out
       | none => true)
  | none => true

/-- **`ChangedFlagValid`** for one phase and one input program: `changed = true ↔
    progOut ≠ progIn`, on full structural equality of `Program` (see the module
    doc on why that is both available and metadata-safe). -/
def checkChangedFlagValid (ph : Core.PipelinePhase) (prog : Program) : Bool :=
  match runPhase ph prog with
  | some (changed, out) => changed == decide (out ≠ prog)
  | none => true

-- ── Control-flow-skeleton equivalence (ported from the spec file) ─────────
-- `ANFEncoderCorrect.controlFlowPreserved` is stated via `stmtsCFEquiv`; we port
-- `cmdKindEquiv` / `stmtCFEquiv` / `stmtsCFEquiv` / `stripANFInits` verbatim from
-- `Strata/Transform/CustomSpecifications.lean` so the executable check matches the
-- declarative property exactly.

/-- Same command kind (init↔init, set↔set, assert↔assert, assume↔assume,
    cover↔cover, call↔call with same proc name). Expressions may differ. -/
def cmdKindEquiv (c1 c2 : Command) : Bool :=
  match c1, c2 with
  | .cmd (.init n1 _ _ _), .cmd (.init n2 _ _ _) => n1 == n2
  | .cmd (.set n1 _ _), .cmd (.set n2 _ _) => n1 == n2
  | .cmd (.assert l1 _ _), .cmd (.assert l2 _ _) => l1 == l2
  | .cmd (.assume l1 _ _), .cmd (.assume l2 _ _) => l1 == l2
  | .cmd (.cover l1 _ _), .cmd (.cover l2 _ _) => l1 == l2
  | .call p1 _ _, .call p2 _ _ => p1 == p2
  | _, _ => false

mutual
/-- Two statements have the same control-flow skeleton: same structure
    (block/ite/loop/exit shape), same labels, same command kinds, but
    expressions may differ. -/
def stmtCFEquiv (s1 s2 : Statement) : Bool :=
  match s1, s2 with
  | .cmd c1, .cmd c2 => cmdKindEquiv c1 c2
  | .block l1 b1 _, .block l2 b2 _ => l1 == l2 && stmtsCFEquiv b1 b2
  | .ite _ t1 e1 _, .ite _ t2 e2 _ => stmtsCFEquiv t1 t2 && stmtsCFEquiv e1 e2
  | .loop _ _ _ b1 _, .loop _ _ _ b2 _ => stmtsCFEquiv b1 b2
  | .exit l1 _, .exit l2 _ => l1 == l2
  | .funcDecl _ _, .funcDecl _ _ => true
  | .typeDecl _ _, .typeDecl _ _ => true
  | _, _ => false

/-- Two statement lists have the same control-flow skeleton pointwise. -/
def stmtsCFEquiv (ss1 ss2 : List Statement) : Bool :=
  match ss1, ss2 with
  | [], [] => true
  | s1 :: rest1, s2 :: rest2 => stmtCFEquiv s1 s2 && stmtsCFEquiv rest1 rest2
  | _, _ => false
end

/-- Strip ANF-prefixed `init` statements from a statement list. -/
def stripANFInits (ss : List Statement) : List Statement :=
  ss.filter fun
    | .cmd (.cmd (.init name _ _ _)) => !(CoreIdent.toPretty name).startsWith Core.ANFEncoder.anfVarPrefix
    | _ => true

-- ══ FilterProcedures check predicates ═════════════════════════════════════
-- All FilterProcedures properties below target the *last* procedure only
-- (`callerTargets`), a strict subset. Under the acyclic call DAG the harnesses now
-- generate (module doc, point 1), body `i` may call only siblings `0..i-1`, so the
-- last procedure `P{n-1}` is the one *source* of the DAG — the richest caller — and
-- targeting it is what makes the call-graph *closure* dimension non-vacuous
-- (`checkFilterCalleeClosureRetained`): its callee-closure is exactly the siblings
-- it transitively calls, all of which must then be retained. The removal dimension
-- still bites: any procedure the target does not transitively reach must be removed
-- (and procedure `P0`, a guaranteed leaf, is never reached from anyone, so it is
-- removed whenever it is not the target's own callee). The `ChangedFlagValid`
-- property is the exception: it targets *all* procedures, the scenario in which the
-- hardcoded `changed := true` is provably wrong.

/-- The target set used by the removal-oriented FilterProcedures properties: the
    *last* procedure name, if any.

    The last procedure is chosen deliberately: under the acyclic call DAG (body `i`
    calls only siblings `0..i-1`) it is the DAG's source — the procedure with the
    largest potential callee-closure — so targeting it exercises the closure
    dimension (`checkFilterCalleeClosureRetained`) rather than leaving it vacuous,
    which is what a leaf target (e.g. `P0`) would do.

    Taking a *strict subset* keeps the "removed" dimension non-vacuous too: every
    procedure the target does not transitively reach is obliged to disappear. All
    removal-oriented properties stay faithful — `checkFilterUnreachableRemoved`
    compares against the *closure* `targets ++ cg.getAllCalleesClosure targets`, not
    against `targets`, so a non-target reachable from the target is correctly *not*
    obliged to disappear. -/
private def callerTargets (ps : List Procedure) : List String :=
  (mkProgram ps |> programProcNames).reverse.take 1

/-- The FilterProcedures phase under test, at the target set and the
    `respectNoFilter := true` setting the properties below fix. -/
private def filterPhase (targets : List String) : Core.PipelinePhase :=
  Core.filterProceduresPipelinePhase targets true

/-- **`FilterCorrect.declsSublist`.** The output declarations are a sublist of the
    input declarations: same elements in the same relative order, with only some
    procedures removed. Decided with Lean's `Decidable (List.Sublist ..)` instance
    on `Decl` directly (`Decl` derives `DecidableEq`), so this is the spec's own
    statement rather than a name-sequence proxy — it therefore also subsumes
    "bodies are preserved" and "non-procedures are preserved". -/
def checkFilterDeclsSublist (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase (filterPhase (callerTargets ps)) prog with
  | some (_, out) => decide (out.decls.Sublist prog.decls)
  | none => true

/-- **`FilterCorrect.targetsRetained`.** Every target procedure that exists in the
    input appears in the output. -/
def checkFilterTargetsRetained (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  let targets := callerTargets ps
  match runPhase (filterPhase targets) prog with
  | some (_, out) =>
    let outNames := programProcNames out
    targets.all fun t => t ∉ programProcNames prog || t ∈ outNames
  | none => true

/-- **`FilterCorrect.calleeClosureRetained`.** The output is closed under the
    call graph: if a procedure is retained, every procedure in its transitive
    callee closure (per the *input* call graph, which is what the spec's `cgIn`
    denotes and what `mkState` seeds) is retained too.

    No longer vacuous on generated input: the harnesses generate an acyclic call
    DAG (module doc, point 1) and `callerTargets` targets the DAG's source (the last
    procedure), whose callee-closure is exactly the siblings it transitively calls,
    all of which the check requires be retained. The `callerCalleeProgram` guard is
    kept as a deterministic pin of a fixed multi-edge shape. -/
def checkFilterCalleeClosureRetained (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  let cgIn := prog.toProcedureCG
  match runPhase (filterPhase (callerTargets ps)) prog with
  | some (_, out) =>
    let outNames := programProcNames out
    outNames.all fun n => (cgIn.getCalleesClosure n).all fun callee => callee ∈ outNames
  | none => true

/-- **`FilterCorrect.onlyProcsRemoved`.** No non-procedure declaration is ever
    dropped. Run on `mkMixedProgram` so that non-procedure declarations are
    actually present (on the pure-procedure shape the field is vacuous). -/
def checkFilterOnlyProcsRemoved (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  let targets := (programProcNames prog).take 1
  match runPhase (filterPhase targets) prog with
  | some (_, out) =>
    prog.decls.all fun d => d.kind == .proc || decide (d ∈ out.decls)
  | none => true

/-- **`FilterCorrect.unreachableRemoved`.** A procedure unreachable from the
    target closure is removed, unless it is protected by `noFilter` (generated
    procedures all have `noFilter = false`). "Unreachable" is the spec's own
    condition — absence from `targets ++ cgIn.getAllCalleesClosure targets` — and
    removal is checked by name, which given the collision-free `P0…Pk` relabelling
    `TestScaffold` applies is equivalent to the spec's `∀ md', .proc proc md' ∉
    progOut.decls` (every declaration here carries `.empty` metadata). -/
def checkFilterUnreachableRemoved (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  let targets := callerTargets ps
  let cgIn := prog.toProcedureCG
  let reachable := targets ++ cgIn.getAllCalleesClosure targets
  match runPhase (filterPhase targets) prog with
  | some (_, out) =>
    let outNames := programProcNames out
    prog.decls.all fun
      | .proc p _ =>
        let n := CoreIdent.toPretty p.header.name
        n ∈ reachable || n ∉ outNames || p.header.noFilter
      | _ => true
  | none => true

/-- **`ChangedFlagValid` for FilterProcedures — HONEST FAILURE.** With the target
    set covering *every* procedure, nothing is removed, so `progOut = progIn` and
    the pass *should* report `changed = false`. It hardcodes `changed = true`
    instead (FilterProcedures.lean:82), so this property genuinely FAILS, pinning
    the real bug. -/
def checkFilterChangedFlagValid (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  checkChangedFlagValid (filterPhase (programProcNames prog)) prog

/-- **`PreservesCachedAnalysesWF` for FilterProcedures.** The pass rebuilds the
    cached call graph by filtering both directions of the seeded one; this checks
    that the result is well-formed for the output program whenever the seeded one
    was well-formed for the input program. Passes on generated input and is not
    vacuous there (`toProcedureCG` is well-formed for every generated program),
    but it does *not* pass in general: see "The FilterProcedures `noFilter` /
    call-graph divergence" in the module doc and the `noFilterProgram` guard. -/
def checkFilterAnalysisPreserving (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  checkAnalysisPreserving (filterPhase (callerTargets ps)) prog

-- ══ PrecondElim check predicates ══════════════════════════════════════════
-- Generated bodies *do* call partial functions (`corePartialOps`), so PrecondElim
-- genuinely fires here (see module doc). These properties test both that it does
-- not corrupt what it preserves (procedures, functions, order, other
-- declarations) and that what it inserts is what it should be (one assert per
-- obligation, no preconditions left standing, well-formed `$$wf` procedures).

-- ── Partial-call obligation counting ──────────────────────────────────────
-- The expected number of inserted asserts is computed *independently* of the
-- pass, by walking the input and asking the seeded `Core.Factory` how many WF
-- obligations each expression carries. `Lambda.collectWFObligations` is the same
-- function PrecondElim consults, so this is an oracle for "how many" and "where",
-- not a reimplementation of the pass's assert-construction logic.

/-- The number of partial-function precondition obligations in an expression,
    per the seeded `Core.Factory`. -/
def obligationCount (e : Expression.Expr) : Nat :=
  (Lambda.collectWFObligations Core.Factory e).length

/-- The obligations of a command's expressions, mirroring
    `PrecondElim.collectCmdPrecondAsserts` (a `nondet` init/set carries none). -/
def cmdObligations : Command → Nat
  | .cmd (.init _ _ (.det e) _) => obligationCount e
  | .cmd (.init _ _ .nondet _)  => 0
  | .cmd (.set _ (.det e) _)    => obligationCount e
  | .cmd (.set _ .nondet _)     => 0
  | .cmd (.assert _ e _)        => obligationCount e
  | .cmd (.assume _ e _)        => obligationCount e
  | .cmd (.cover _ e _)         => obligationCount e
  | .call pname args md         =>
    let _ := (pname, md)
    ((CallArg.getInputExprs args).map obligationCount).sum

mutual
/-- The number of asserts PrecondElim should insert for a statement, mirroring
    `transformStmt` branch for branch. A `loop`'s guard and measure are each
    asserted **twice** (once before the loop, once at the end of the body), and an
    inline `funcDecl` contributes the obligations of its own preconditions and
    body (which land in the emitted `{name}$$wf` block). -/
def stmtObligations (s : Statement) : Nat :=
  match s with
  | .cmd c => cmdObligations c
  | .block _ b _ => stmtsObligations b
  | .ite c t e _ =>
    (match c with | .det g => obligationCount g | .nondet => 0)
      + stmtsObligations t + stmtsObligations e
  | .loop guard measure invariant b _ =>
    2 * (match guard with | .det g => obligationCount g | .nondet => 0) +
    2 * (match measure with | some m => obligationCount m | none => 0) +
    (invariant.map (fun (_, inv) => obligationCount inv)).sum +
    stmtsObligations b
  | .exit _ _ => 0
  | .funcDecl d _ =>
    (match d.body with | some b => obligationCount b | none => 0) +
    (d.preconditions.map (fun p => obligationCount p.expr)).sum
  | .typeDecl _ _ => 0

/-- The obligations of a statement list, summed. -/
def stmtsObligations (ss : List Statement) : Nat :=
  match ss with
  | [] => 0
  | s :: rest => stmtObligations s + stmtsObligations rest
end

/-- Total obligations across every procedure body in a program. -/
def programObligations (prog : Program) : Nat :=
  prog.decls.foldl (init := 0) fun acc d =>
    acc + match d with
      | .proc p _ => stmtsObligations (bodyStmts p.body)
      | _ => 0

mutual
/-- Count `assert` commands anywhere in a statement, at any nesting depth. -/
def stmtAssertCount (s : Statement) : Nat :=
  match s with
  | .cmd (.cmd (.assert _ _ _)) => 1
  | .cmd _ => 0
  | .block _ b _ => stmtsAssertCount b
  | .ite _ t e _ => stmtsAssertCount t + stmtsAssertCount e
  | .loop _ _ _ b _ => stmtsAssertCount b
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => 0

/-- Count `assert` commands in a statement list. -/
def stmtsAssertCount (ss : List Statement) : Nat :=
  match ss with
  | [] => 0
  | s :: rest => stmtAssertCount s + stmtsAssertCount rest
end

/-- Total `assert`s across every procedure body in a program. -/
def programAssertCount (prog : Program) : Nat :=
  prog.decls.foldl (init := 0) fun acc d =>
    acc + match d with
      | .proc p _ => stmtsAssertCount (bodyStmts p.body)
      | _ => 0

mutual
/-- Does any inline function declaration in this statement still carry a
    precondition? (`PrecondElimCorrect.preconditionsStripped`, statement side.) -/
def stmtHasFuncPrecond (s : Statement) : Bool :=
  match s with
  | .cmd _ => false
  | .block _ b _ => stmtsHaveFuncPrecond b
  | .ite _ t e _ => stmtsHaveFuncPrecond t || stmtsHaveFuncPrecond e
  | .loop _ _ _ b _ => stmtsHaveFuncPrecond b
  | .exit _ _ => false
  | .funcDecl d _ => !d.preconditions.isEmpty
  | .typeDecl _ _ => false

/-- Does any inline function declaration in this statement list still carry a
    precondition? -/
def stmtsHaveFuncPrecond (ss : List Statement) : Bool :=
  match ss with
  | [] => false
  | s :: rest => stmtHasFuncPrecond s || stmtsHaveFuncPrecond rest
end

/-- Does any function reachable in the program — a top-level `.func` /
    `.recFuncBlock` declaration, or an inline `funcDecl` inside a procedure body —
    still carry a precondition? -/
def programHasFuncPrecond (prog : Program) : Bool :=
  prog.decls.any fun
    | .func f _ => !f.preconditions.isEmpty
    | .recFuncBlock fs _ => fs.any (!·.preconditions.isEmpty)
    | .proc p _ => stmtsHaveFuncPrecond (bodyStmts p.body)
    | _ => false

/-- **`PrecondElimCorrect.generatedWF`.** Every generated `$$wf` procedure in the
    output has `noFilter = true` and an empty spec (so FilterProcedures cannot
    drop the check, and the check itself carries no contract to discharge).

    Run on `mkMixedProgram`, which is what makes the field non-vacuous: a lifted
    top-level function whose precondition or body calls a partial function gets a
    `$$wf` *procedure* from `mkFuncWFProc`, whereas on the pure-procedure shape
    the obligations stay inside bodies and no `$$wf` declaration is produced
    (module doc, point 2). -/
def checkPrecondGeneratedWF (ps : List Procedure) : Bool :=
  match runPhase Core.precondElimPipelinePhase (mkMixedProgram ps) with
  | some (_, out) =>
    out.decls.all fun
      | .proc p _ =>
        !(CoreIdent.toPretty p.header.name).endsWith Core.PrecondElim.wfSuffix ||
          (p.header.noFilter && p.spec.preconditions.isEmpty && p.spec.postconditions.isEmpty)
      | _ => true
  | none => true

/-- **`PrecondElimCorrect.preconditionsStripped`.** "The returned program consists
    only of total functions (no preconditions)" (PrecondElim's module doc, point 4):
    no function reachable in the output — top-level or inline in a procedure body —
    still carries a precondition. (Stronger than the spec field, which quantifies
    over top-level `.func` / `.recFuncBlock` declarations only; the inline
    `funcDecl` case is where generated input puts its preconditions.)

    Non-vacuous: `genFunction` draws an optional `requires` clause over the
    function's own formals (see `FunctionHasTypeAGen.Core.genPrecondition`), so
    generated declarations really do carry preconditions for the pass to strip —
    184 of 1500 sampled programs did, up from 0 of 3000 before the generator
    gained the clause. -/
def checkPrecondPreconditionsStripped (ps : List Procedure) : Bool :=
  match runPhase Core.precondElimPipelinePhase (mkProgram ps) with
  | some (_, out) => !programHasFuncPrecond out
  | none => true

/-- **`PrecondElimCorrect.nonProcDeclsPreserved`.** Type, axiom and `distinct`
    declarations pass through untouched. Run on `mkMixedProgram`, which supplies
    exactly one declaration of each of those three kinds. -/
def checkPrecondNonProcDeclsPreserved (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) =>
    prog.decls.all fun d =>
      !(d.kind == .type || d.kind == .ax || d.kind == .distinct) || decide (d ∈ out.decls)
  | none => true

/-- **`PrecondElimCorrect.proceduresPreserved`.** Every input procedure survives
    with the same name and the same spec (its body may — and on partial-call input
    routinely does — *grow* with inserted asserts, which this tolerates). The
    header is compared too, which is stronger than the spec's name-only claim and
    still holds: the pass rewrites bodies, never signatures. -/
def checkPrecondProceduresPreserved (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) =>
    (programProcNames prog).all fun n =>
      match findProc prog n, findProc out n with
      | some p, some q => headerEq p.header q.header && specEq p.spec q.spec
      | _, _ => false
  | none => true

/-- **`PrecondElimCorrect.functionsPreserved`.** Every input function survives
    with the same name, body, inputs and output — and with its preconditions
    stripped. Run on `mkMixedProgram`, whose top-level `.func` declarations are
    the generated inline functions lifted out of the bodies. -/
def checkPrecondFunctionsPreserved (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) =>
    prog.decls.all fun
      | .func f _ =>
        match findFunc out (CoreIdent.toPretty f.name) with
        | some g =>
          g.preconditions.isEmpty && decide (g.body = f.body) &&
            decide (g.inputs = f.inputs) && decide (g.output = f.output)
        | none => false
      | _ => true
  | none => true

/-- **`PrecondElimCorrect.noDeclsRemoved`.** Every input declaration still has a
    same-named declaration in the output (the pass only ever *adds* `$$wf`
    declarations). Run on `mkMixedProgram` so all declaration kinds participate. -/
def checkPrecondNoDeclsRemoved (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) =>
    let outNames := out.decls.map Decl.name
    prog.decls.all fun d => decide (d.name ∈ outNames)
  | none => true

/-- **`PrecondElimCorrect.orderPreserved`.** The input declaration-name sequence
    is a sublist of the output's — the relative order of input declarations
    survives, with newly generated `$$wf` names interleaved. Decided with the
    spec's own `List.Sublist`, on `mkMixedProgram` so that the interleaving
    actually happens (`mkFuncWFProc` pushes each `$$wf` procedure immediately
    *before* the function it checks). -/
def checkPrecondOrderPreserved (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) =>
    decide ((prog.decls.map Decl.name).Sublist (out.decls.map Decl.name))
  | none => true

/-- **`ChangedFlagValid` for PrecondElim — HONEST FAILURE.** `changed ↔ progOut ≠
    progIn`. This **fails**: the `.funcDecl` branch of `transformStmt`
    (`PrecondElim.lean:318–338`) inserts a `{name}$$wf` block for obligations found
    in a declared function's *body* but derives `changed` solely from whether the
    declaration had preconditions of its own, so a precondition-free function whose
    body calls `Int.SafeDiv` is rewritten and reported unchanged. -/
def checkPrecondChangedFlagValid (ps : List Procedure) : Bool :=
  checkChangedFlagValid Core.precondElimPipelinePhase (mkProgram ps)

/-- **`PrecondElim` call-site asserts** — the operational content behind
    `generatedWF`'s asserts. Every partial-function call obligation in the input
    gets exactly one `assert` in the output, and no input assert is dropped: the
    output body-assert count is the input count plus the obligation count computed
    independently from `Core.Factory` via `Lambda.collectWFObligations` (see
    `programObligations`). Stated on `mkProgram`, where all obligations live in
    procedure bodies and the count is exact; on `mkMixedProgram` a lifted function
    would route its obligations into a separate `$$wf` *procedure*, which this
    body-local oracle deliberately does not model. -/
def checkPrecondCallSiteAsserts (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) =>
    programAssertCount out == programAssertCount prog + programObligations prog
  | none => true

-- ── Factory correctness (`PrecondElimFactoryCorrect`) ─────────────────────
-- The factory is threaded through `CoreTransformState`, so these three fields are
-- read off `runPhaseSt`'s final state rather than off the output program.

/-- The names in a `Lambda.Factory`. `toArray` is the public field of the
    structure (only `nameMap` is private) and `Factory.name_nodup` says its
    entries have distinct names, so enumerating it is exactly enumerating the
    factory's membership — and by `nameMapConsistent`, `f[name]` for `name ∈ f` is
    the array element of that name. -/
def factoryNames (f : @Lambda.Factory CoreLParams) : List String :=
  f.toArray.toList.map (·.name.name)

/-- **`PrecondElimFactoryCorrect.factoryGrows`.** The output factory contains
    every name the input factory had (entries are pushed, never dropped). -/
def checkPrecondFactoryGrows (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhaseSt Core.precondElimPipelinePhase prog with
  | some (_, st') =>
    match (mkState prog).factory, st'.factory with
    | some fIn, some fOut =>
      (factoryNames fIn).all fun n => decide (n ∈ fOut)
    | _, _ => true
  | none => true

/-- **`PrecondElimFactoryCorrect.factoryComplete`.** Every function the output
    program declares (top-level `.func` or a member of a `.recFuncBlock`) is
    present in the output factory. Run on `mkMixedProgram`, which is what puts
    top-level function declarations in front of the pass at all. -/
def checkPrecondFactoryComplete (ps : List Procedure) : Bool :=
  match runPhaseSt Core.precondElimPipelinePhase (mkMixedProgram ps) with
  | some ((_, out), st') =>
    match st'.factory with
    | some fOut =>
      out.decls.all fun
        | .func f _ => decide (f.name.name ∈ fOut)
        | .recFuncBlock fs _ => fs.all fun f => decide (f.name.name ∈ fOut)
        | _ => true
    | none => true
  | none => true

/-- **`PrecondElimFactoryCorrect.factoryStripped` — HONEST FAILURE (spec bug +
    pass bug).** Verbatim: every entry of the output factory has
    `preconditions = []`. This fails on *every* input, including the empty
    program, for two independent reasons — the seeded `Core.Factory` builtins keep
    the very preconditions the pass exists to discharge, and the pass pushes each
    declared function into the factory before stripping it. See "The three honest
    failures" in the module doc; `checkPrecondDeclaredFactoryStripped` isolates
    the second, pass-side cause. -/
def checkPrecondFactoryStripped (ps : List Procedure) : Bool :=
  match runPhaseSt Core.precondElimPipelinePhase (mkMixedProgram ps) with
  | some (_, st') =>
    match st'.factory with
    | some fOut => fOut.toArray.toList.all (·.preconditions.isEmpty)
    | none => true
  | none => true

/-- The factory entries that make `checkPrecondFactoryStripped` fail: every entry
    of the *output* factory that still carries a precondition, each paired with its
    formatted preconditions and with whether the input program declared it.

    This is the diagnostic counterpart to the check above. That property fails on
    every input — including the empty program — so a minimized *program* witness
    says nothing about the cause; the offenders are in the factory, not the program.
    Reporting them directly is what makes the failure legible: on the empty program
    this returns 58 entries, all seeded `Core.Factory` builtins
    (`Int.SafeDiv` requiring `!(y == 0)`, `Sequence.select`, the `Bv*.Safe*`
    family, …), and all with `declared = false`.

    The `declared` flag separates the two independent causes documented above:
    `false` entries are the spec-side bug (builtins whose preconditions the pass
    must *keep*, since they are the very WF obligations it reads to emit asserts),
    and `true` entries are the pass-side bug (a declared function pushed into the
    factory unstripped, `PrecondElim.lean:326`/`:412`) that
    `checkPrecondDeclaredFactoryStripped` isolates. -/
def precondFactoryStrippedOffenders (ps : List Procedure) :
    List (String × List String × Bool) :=
  let prog := mkMixedProgram ps
  match runPhaseSt Core.precondElimPipelinePhase prog with
  | some (_, st') =>
    match st'.factory with
    | some fOut =>
      let declared := prog.decls.filterMap fun
        | .func f _ => some f.name.name
        | _ => none
      fOut.toArray.toList.filterMap fun lf =>
        if lf.preconditions.isEmpty then none
        else some (lf.name.name,
                   lf.preconditions.map fun p => toString (Std.format p.expr),
                   declared.contains lf.name.name)
    | none => []
  | none => []

/-- **`PrecondElimFactoryCorrect.factoryStripped`, restricted to the functions the
    program declares — HONEST FAILURE (pass side only).** Drops the seeded
    builtins from the claim, so the only way to fail is the pass pushing a
    declared function's *unstripped* copy into the factory
    (`PrecondElim.lean:326` and `:412`). Fails exactly on the programs that
    declare a function with a precondition, which `genFunction` produces (module
    doc, point 3). -/
def checkPrecondDeclaredFactoryStripped (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhaseSt Core.precondElimPipelinePhase prog with
  | some (_, st') =>
    match st'.factory with
    | some fOut =>
      let declared := prog.decls.filterMap fun
        | .func f _ => some f.name.name
        | _ => none
      fOut.toArray.toList.all fun lf =>
        !declared.contains lf.name.name || lf.preconditions.isEmpty
    | none => true
  | none => true

/-- **`PreservesCachedAnalysesWF` for PrecondElim.** The pass registers each
    generated `$$wf` procedure as a leaf in the cached call graph
    (`addWFProcToCallGraph`); this checks that the graph it hands on is still
    well-formed for the program it hands on. Run on `mkMixedProgram` so the
    `$$wf`-procedure path — the only path that touches the cached graph — is
    actually taken. -/
def checkPrecondAnalysisPreserving (ps : List Procedure) : Bool :=
  checkAnalysisPreserving Core.precondElimPipelinePhase (mkMixedProgram ps)

-- ══ ANFEncoder check predicates ═══════════════════════════════════════════

/-- **`ANFEncoderCorrect.declsLength`.** No declarations are added or removed:
    the output is a pointwise modification of the input. -/
def checkAnfDeclsLength (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.anfEncoderPipelinePhase prog with
  | some (_, out) => out.decls.length == prog.decls.length
  | none => true

/-- **`ANFEncoderCorrect.nonProcsUnchanged`.** Non-procedure declarations are
    unchanged. Run on `mkMixedProgram` so that function, type, axiom and
    `distinct` declarations are present to be left alone. -/
def checkAnfNonProcsUnchanged (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhase Core.anfEncoderPipelinePhase prog with
  | some (_, out) =>
    prog.decls.all fun d => d.kind == .proc || decide (d ∈ out.decls)
  | none => true

/-- **`ANFEncoderCorrect.procHeadersPreserved`.** Procedure headers and specs are
    preserved (ANF touches only bodies). -/
def checkAnfHeadersPreserved (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.anfEncoderPipelinePhase prog with
  | some (_, out) =>
    (programProcNames prog).all fun n =>
      match findProc prog n, findProc out n with
      | some p, some q => headerEq p.header q.header && specEq p.spec q.spec
      | _, _ => false
  | none => true

mutual
/-- Every `init` statement in a statement, at any nesting depth, as a
    `(name, rhs)` pair. -/
def stmtInits (s : Statement) : List (Expression.Ident × ExprOrNondet Expression) :=
  match s with
  | .cmd (.cmd (.init name _ rhs _)) => [(name, rhs)]
  | .cmd _ => []
  | .block _ b _ => stmtsInits b
  | .ite _ t e _ => stmtsInits t ++ stmtsInits e
  | .loop _ _ _ b _ => stmtsInits b
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []

/-- Every `init` statement in a statement list, at any nesting depth. -/
def stmtsInits (ss : List Statement) : List (Expression.Ident × ExprOrNondet Expression) :=
  match ss with
  | [] => []
  | s :: rest => stmtInits s ++ stmtsInits rest
end

/-- **`ANFEncoderCorrect.freshVarsDet`.** Every ANF-prefixed `init` in an output
    body has a deterministic (non-havoc) initializer. Checked at *every* nesting
    depth (ANF hoists at the top of each block), which is stronger than looking at
    the top-level statements only. -/
def checkAnfFreshVarsDet (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.anfEncoderPipelinePhase prog with
  | some (_, out) =>
    out.decls.all fun
      | .proc q _ =>
        (stmtsInits (bodyStmts q.body)).all fun (name, rhs) =>
          !(CoreIdent.toPretty name).startsWith Core.ANFEncoder.anfVarPrefix ||
            (match rhs with | .det _ => true | .nondet => false)
      | _ => true
  | none => true

/-- **`ANFEncoderCorrect.orderPreserved`.** Declaration names match positionally:
    the output name list is *equal* to the input's (not merely a sublist — ANF
    neither adds nor removes declarations). Run on `mkMixedProgram` so all
    declaration kinds take part in the positional comparison. -/
def checkAnfOrderPreserved (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhase Core.anfEncoderPipelinePhase prog with
  | some (_, out) =>
    decide (out.decls.map Decl.name = prog.decls.map Decl.name)
  | none => true

/-- **`ANFEncoderCorrect.controlFlowPreserved`** — the spec's headline claim,
    "ANFEncoder does not change control flow". Stripping the fresh ANF `init`s
    from each output body yields a statement list with the same control-flow
    skeleton (`stmtsCFEquiv`) as the corresponding input body. -/
def checkAnfControlFlowPreserved (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.anfEncoderPipelinePhase prog with
  | some (_, out) =>
    (programProcNames prog).all fun n =>
      match findProc prog n, findProc out n with
      | some p, some q => stmtsCFEquiv (bodyStmts p.body) (stripANFInits (bodyStmts q.body))
      | _, _ => false
  | none => true

/-- **`ChangedFlagValid` for ANFEncoder.** `changed ↔ progOut ≠ progIn`. Unlike
    the other two passes, ANFEncoder derives its flag from the fresh-variable
    counter actually advancing (`idx' > idx`, ANFEncoder.lean:280), which is
    precisely when a body is rewritten — so this one holds. -/
def checkAnfChangedFlagValid (ps : List Procedure) : Bool :=
  checkChangedFlagValid Core.anfEncoderPipelinePhase (mkProgram ps)

/-- **`PreservesCachedAnalysesWF` for ANFEncoder.** ANF neither renames procedures
    nor adds or removes `call` statements, so the seeded call graph it passes
    through unchanged stays well-formed. -/
def checkAnfAnalysisPreserving (ps : List Procedure) : Bool :=
  checkAnalysisPreserving Core.anfEncoderPipelinePhase (mkProgram ps)

-- ── Sanity guards ─────────────────────────────────────────────────────────
-- Small hand-built programs pin the plumbing and, more importantly, pin the
-- dimensions that *generated* input cannot reach: call-graph closures (generated
-- procedures are leaves), `noFilter` protection (generated procedures set it
-- false), and each of the two independent causes behind the `factoryStripped`
-- failure.

section Guards

/-- A minimal procedure with the given name and body. -/
private def procOf (name : String) (ss : List Statement) : Procedure :=
  { header := { name := ⟨name, ()⟩, typeArgs := [], inputs := [], outputs := [],
                noFilter := false }
    spec := { preconditions := [], postconditions := [] }
    body := .structured ss }

private def intLit (i : Int) : Expression.Expr := .const () (.intConst i)

private def callOp (name : String) (a b : Expression.Expr) : Expression.Expr :=
  .app () (.app () (.op () ⟨name, ()⟩ none) a) b

/-- A `funcDecl` for `func f() : int` with the given body and preconditions. -/
private def funcDeclOf (name : String) (body : Option Expression.Expr)
    (preconds : List Expression.Expr) : Statement :=
  .funcDecl
    { name := ⟨name, ()⟩, typeArgs := [], inputs := [],
      output := (.forAll [] .int : LTy), body := body,
      preconditions := preconds.map (fun e => { expr := e, md := () }) } .empty

-- On the empty program (no declarations) every pass is the identity, so every
-- structural preservation check holds. `checkPrecondFactoryStripped` is the sole
-- exception, and deliberately so: the seeded `Core.Factory` builtins already
-- violate it before the pass runs (see the module doc), which is exactly what the
-- `== false` guard below records.
#guard checkFilterDeclsSublist [] == true
#guard checkFilterTargetsRetained [] == true
#guard checkFilterCalleeClosureRetained [] == true
#guard checkFilterOnlyProcsRemoved [] == true
#guard checkFilterUnreachableRemoved [] == true
#guard checkFilterAnalysisPreserving [] == true
#guard checkPrecondGeneratedWF [] == true
#guard checkPrecondPreconditionsStripped [] == true
#guard checkPrecondNonProcDeclsPreserved [] == true
#guard checkPrecondProceduresPreserved [] == true
#guard checkPrecondFunctionsPreserved [] == true
#guard checkPrecondNoDeclsRemoved [] == true
#guard checkPrecondOrderPreserved [] == true
#guard checkPrecondChangedFlagValid [] == true
#guard checkPrecondCallSiteAsserts [] == true
#guard checkPrecondFactoryGrows [] == true
#guard checkPrecondFactoryComplete [] == true
#guard checkPrecondDeclaredFactoryStripped [] == true
#guard checkPrecondAnalysisPreserving [] == true
#guard checkAnfDeclsLength [] == true
#guard checkAnfNonProcsUnchanged [] == true
#guard checkAnfHeadersPreserved [] == true
#guard checkAnfFreshVarsDet [] == true
#guard checkAnfOrderPreserved [] == true
#guard checkAnfControlFlowPreserved [] == true
#guard checkAnfChangedFlagValid [] == true
#guard checkAnfAnalysisPreserving [] == true

-- Cause (1) of the `factoryStripped` failure: the seeded factory violates the
-- field before the pass has done anything at all.
#guard (Core.Factory.toArray.toList.filter (!·.preconditions.isEmpty)).isEmpty == false
#guard checkPrecondFactoryStripped [] == false

-- `stmtsCFEquiv` is reflexive on the empty body and distinguishes shapes.
#guard stmtsCFEquiv [] [] == true
#guard stmtsCFEquiv [.exit "L" .empty] [.exit "L" .empty] == true
#guard stmtsCFEquiv [.exit "L" .empty] [.exit "M" .empty] == false

-- The obligation-counting oracle behind `checkPrecondCallSiteAsserts` must
-- actually see the `Int.Safe*` preconditions in `Core.Factory` — if it silently
-- counted zero everywhere the property would be vacuous. `Int.SafeDiv(1, 0)`
-- carries one (`y ≠ 0`); its total counterpart `Int.Div(1, 0)` carries none.
#guard obligationCount (callOp "Int.SafeDiv" (intLit 1) (intLit 0)) == 1
#guard obligationCount (callOp "Int.Div" (intLit 1) (intLit 0)) == 0
-- Nested partial calls contribute one obligation each.
#guard obligationCount
  (callOp "Int.SafeMod" (callOp "Int.SafeDiv" (intLit 1) (intLit 0)) (intLit 2)) == 2
-- A `loop` guard is asserted twice (before the loop and at the end of the body),
-- matching `transformStmt`'s `guardAsserts ++ … ++ guardAssertsEnd`.
#guard stmtObligations
  (.loop (.det (callOp "Int.SafeDiv" (intLit 1) (intLit 0))) none [] [] .empty) == 2
-- A `nondet` init carries no obligations (there is no expression to scan).
#guard stmtObligations (.init "x" (.forAll [] .int) .nondet .empty) == 0

-- ── The `mkMixedProgram` lifting ──────────────────────────────────────────
-- Pin the assembly itself: an inline `funcDecl` becomes a top-level `.func`, the
-- inline copy is gone, and the three fixed non-procedure declarations lead.

private def liftMeProc : Procedure :=
  procOf "P" [funcDeclOf "g" (some (intLit 3)) [], .exit "L" .empty]

#guard (mkMixedProgram [liftMeProc]).decls.map (fun d => CoreIdent.toPretty d.name) ==
  ["TestSupportT", "testSupportAx", "testSupportDistinct", "g", "P"]
-- The inline declaration really was removed from the body (only the `exit` left).
#guard (match findProc (mkMixedProgram [liftMeProc]) "P" with
        | some p => (stmtsFuncDecls (bodyStmts p.body)).isEmpty && (bodyStmts p.body).length == 1
        | none => false) == true
-- Duplicated inline names are lifted once, and every inline copy is dropped, so
-- PrecondElim's "already in factory" guard cannot fire (which would make every
-- property using this shape vacuous).
#guard (mkMixedProgram [liftMeProc, liftMeProc]).decls.map (fun d => CoreIdent.toPretty d.name) ==
  ["TestSupportT", "testSupportAx", "testSupportDistinct", "g", "P", "P"]
#guard (runPhase Core.precondElimPipelinePhase (mkMixedProgram [liftMeProc, liftMeProc])).isSome == true

-- ── Hand-built PrecondElim reproducers ───────────────────────────────────
-- Scenarios the *generator* cannot currently reach, pinned deterministically so
-- the behaviour is regression-tested even though no property covers it.

-- ① THE `changed`-FLAG BUG (`PrecondElim.lean:318–338`). `function f() : int {
-- Int.SafeDiv(1, 0) }` has no preconditions of its own, but its *body* calls a
-- partial function. The pass inserts an `f$$wf` block holding the obligation
-- assert — so the program provably changes — yet reports `changed = false`,
-- because that branch returns `hasPreconds`. `checkPrecondChangedFlagValid`
-- therefore fails on this input, which is exactly the honest failure the property
-- is there to pin.
private def bodyCallProc : Procedure :=
  procOf "P" [funcDeclOf "f" (some (callOp "Int.SafeDiv" (intLit 1) (intLit 0))) []]

#guard checkPrecondChangedFlagValid [bodyCallProc] == false
-- The obligation is real and the assert *is* emitted (so the flag is the only
-- thing wrong here — the pass does the right rewrite, it just misreports it).
#guard programObligations (mkProgram [bodyCallProc]) == 1
#guard checkPrecondCallSiteAsserts [bodyCallProc] == true
-- ...and the rewrite is genuinely visible in the output program.
#guard (match runPhase Core.precondElimPipelinePhase (mkProgram [bodyCallProc]) with
        | some (changed, out) => changed == false && out != mkProgram [bodyCallProc]
        | none => false) == true

-- ② `preconditionsStripped` with a declaration that *does* carry a precondition.
-- `genFunction` reaches this shape too, but pin it by hand as well so the property
-- has a deterministic witness independent of the generator's coin flips: the input
-- has a precondition, the output has none.
private def precondFuncProc : Procedure :=
  procOf "P" [funcDeclOf "g" none [callOp "Int.Ge" (intLit 1) (intLit 0)]]

#guard programHasFuncPrecond (mkProgram [precondFuncProc]) == true
#guard checkPrecondPreconditionsStripped [precondFuncProc] == true

-- ③ Cause (2) of the `factoryStripped` failure, isolated from the seeded
-- builtins: the *declaration* is stripped in the output program, but the copy the
-- pass pushed into the factory still carries the precondition.
#guard checkPrecondDeclaredFactoryStripped [precondFuncProc] == false
#guard checkPrecondPreconditionsStripped [precondFuncProc] == true
-- The `$$wf` procedure generated for that declared precondition is well-formed
-- (`noFilter`, empty spec) — `generatedWF` bites here.
#guard checkPrecondGeneratedWF [precondFuncProc] == true

-- ── Hand-built FilterProcedures reproducers ──────────────────────────────

/-- `A` calls `B`, `B` calls `C`, and `D` is unrelated. Gives the call-graph
    closure dimension of `calleeClosureRetained` / `unreachableRemoved` something
    to say. The caller `A` is listed **last** so that `callerTargets` (which picks
    the last procedure) targets it, driving the `checkFilter*` guards below through
    the non-empty closure `{B, C}`. -/
private def callerCalleeProgram : List Procedure :=
  [ procOf "D" [],
    procOf "C" [],
    procOf "B" [.call "C" [] .empty],
    procOf "A" [.call "B" [] .empty] ]

-- Targeting `A` keeps `A`, `B`, `C` (the closure) and drops the unrelated `D`.
#guard (match runPhase (Core.filterProceduresPipelinePhase ["A"] true)
                (mkProgram callerCalleeProgram) with
        | some (_, out) => programProcNames out == ["C", "B", "A"]
        | none => false) == true
#guard checkFilterCalleeClosureRetained callerCalleeProgram == true
#guard checkFilterUnreachableRemoved callerCalleeProgram == true
#guard checkFilterDeclsSublist callerCalleeProgram == true
#guard checkFilterTargetsRetained callerCalleeProgram == true
-- The seeded call graph really does record those edges, so `callGraphWF`'s
-- `CalleesCountEqual` / `callersTranspose` fields are exercised non-trivially.
#guard ((mkProgram callerCalleeProgram).toProcedureCG.getCalleesClosure "A").length == 2
#guard callGraphWF (mkProgram callerCalleeProgram).toProcedureCG
        (mkProgram callerCalleeProgram) == true
#guard checkFilterAnalysisPreserving callerCalleeProgram == true

/-- A `noFilter := true` procedure that no target reaches. FilterProcedures keeps
    the *declaration* (it respects `noFilter`) but filters the procedure out of
    the cached *call graph* (`isNeededProc` ignores `noFilter`), so the graph it
    caches is no longer complete for the program it returns — a real divergence
    from `PreservesCachedAnalysesWF` that generated input cannot reach, since
    `genProcedure` always sets `noFilter := false`.

    The `noFilter` procedure `P` is listed **first**, so `callerTargets` (which
    picks the *last* procedure — see its docstring) targets the plain procedure `Q`
    and `P` is left as the unreached, `noFilter`-protected non-target that triggers
    the divergence. -/
private def noFilterProgram : List Procedure :=
  [ { procOf "P" [] with header := { (procOf "P" []).header with noFilter := true } },
    procOf "Q" [] ]

-- `P` survives in the declarations (`callerTargets` picks the last proc, `["Q"]`,
-- and `P` is `noFilter`-protected)...
#guard (match runPhase (Core.filterProceduresPipelinePhase ["Q"] true)
                (mkProgram noFilterProgram) with
        | some (_, out) => programProcNames out == ["P", "Q"]
        | none => false) == true
-- ...but is missing from the cached call graph, so `analysisPreserving` fails.
#guard checkFilterAnalysisPreserving noFilterProgram == false
-- The antecedent is not the problem: the seeded input graph is well-formed.
#guard callGraphWF (mkProgram noFilterProgram).toProcedureCG (mkProgram noFilterProgram) == true
-- `unreachableRemoved` still holds — it exempts `noFilter` procedures by design.
#guard checkFilterUnreachableRemoved noFilterProgram == true

-- The hardcoded `changed := true` (FilterProcedures.lean:82) misreports the
-- all-targets scenario, in which nothing is removed.
#guard checkFilterChangedFlagValid noFilterProgram == false
#guard checkFilterChangedFlagValid callerCalleeProgram == false

end Guards

end StrataGenerators.Procedure.TestSupport
