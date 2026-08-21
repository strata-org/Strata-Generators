-- This file imports the *code* modules only, and no sibling with a proof that brings in Mathlib.
-- `ProcedureHasTypeAGen.Core` gives the generator and the syntax of Strata Core.
-- `HasTypeAGen.TestSupport` gives the operator contexts `coreMonoOps` and `corePartialOps`, and it needs
-- no Mathlib. The three `Strata.Transform.*` modules are the passes under test. An import of
-- `StmtHasTypeAGen.TestSupport` here would make this file impossible to import beside a transform pass,
-- because Strata and Batteries each define `List.Forall₂`.
import StrataGenerators.ProcedureHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.Transform.FilterProcedures
import Strata.Transform.PrecondElim
import Strata.Transform.CommonSubexprElim
import Strata.Languages.Core.Factory

open Lambda Core Imperative

/-!
# The shared support for the properties about `genProcedure` and the Core transform passes

This module holds the definitions that both harnesses use for the property-based tests of
`genProcedure`. That generator is in `ProcedureHasTypeAGen/Core.lean`, and it gives a well-typed Strata
Core procedure that satisfies the `ProcHasTypeA` typing relation. The generator has a proof of
**soundness** and a proof of **completeness** against that relation, in `ProcedureHasTypeAGen.lean`.
Therefore each generated procedure is a certified well-typed input, and it is a good input for the three
Core *transform* passes that this module tests:

- **FilterProcedures** removes each procedure that no target of the entry set reaches.
- **PrecondElim** removes the precondition of a partial function, and it emits a check of
  well-formedness, which is a `$$wf` block.
- **ANFEncoder** lifts a subexpression into a fresh `init` statement, in A-normal form.

## The relation to the declarative specification

Each check predicate below is the executable form of **one named field** of the three `*PhaseCorrect`
structures in the specification file of Strata. The coverage is *complete*: each field of these three
structures has a `check*` counterpart here, and the docstring of that counterpart names the field.

- `Core.FilterProcedures.FilterProcedurePhaseCorrect`, which holds five `FilterCorrect` fields,
  `changedFlagValid` and `analysisPreserving`.
- `Core.PrecondElim.PrecondElimPhaseCorrect`, which holds seven `PrecondElimCorrect` fields, three
  `PrecondElimFactoryCorrect` fields, `changedFlagValid` and `analysisPreserving`.
- `Core.ANFEncoder.ANFEncoderPhaseCorrect`, which holds six `ANFEncoderCorrect` fields,
  `changedFlagValid` and `analysisPreserving`.

Three obligations occur in each of the three passes, so one predicate decides each of them for all three:

- `ChangedFlagValid pass` says that `changed` is `true` if and only if the output program differs from
  the input program. The derived `DecidableEq Program` instance decides it. Read the note about
  structural equality below.
- `PreservesCachedAnalysesWF pass` says that a well-formed input call graph gives a well-formed output
  call graph. `callGraphWF` below decides it, and that definition transcribes each field of the
  `CallGraphWF` structure of the specification.
- The properties about an order have the shape of a `Sublist`. The `Decidable (List.Sublist ..)`
  instance of Lean decides each of them, on a `Decl` directly or on the list of the declaration names.
  That is the form of the specification itself, and not a substitute.

## The two shapes of a program

Each field of the specification quantifies over *each* kind of declaration, and `genProcedure` gives a
procedure only. Therefore a program that holds generated procedures only leaves each field about a
function and about a declaration that is not a procedure with no content. Those fields are
`onlyProcsRemoved`, `nonProcDeclsPreserved`, `functionsPreserved`, `noDeclsRemoved`, `factoryComplete`
and `nonProcsUnchanged`. This module therefore gives two assemblies:

- `mkProgram ps` gives one `.proc` declaration for each generated procedure. Each property whose field
  is about a procedure, about an order or about the `changed` flag uses this shape.
- `mkMixedProgram ps` gives the same procedures, and it **lifts** each inline `funcDecl` statement of a
  body to a top-level `.func` declaration. It drops the inline declaration, and it keeps one
  declaration for each name, so that the guard of PrecondElim for a name that is already in the factory
  cannot fire. It also puts one fixed `.type` declaration, one `.ax` declaration and one `.distinct`
  declaration in front. Exactly the six fields above use this shape, so each of them has real content.
  This assembly invents nothing: each lifted function is a function that `genFunction` drew, and the
  assembly only moves it from a statement position to a declaration position.

## What the generator can reach, and what it cannot reach

`genProcedure` builds *one* procedure with a structured body from `genStmtChain`, at the operator
context that `TestScaffold` gives it. That context is `corePartialOps`, which is `coreMonoOps` together
with the four `Int.Safe*` operators that carry a precondition. Three facts about the shape of that body
limit what these properties can test:

1. **A procedure call, in an acyclic graph of calls.** `genCallStmt`, in `StmtHasTypeAGen/Core.lean`
   with a proof of soundness in `GenCallStmtSound.lean`, emits a `call` statement against a
   `procs : ProcSigCtx` that is not empty. `genProcedure` threads such a context into `genStmtChain`.
   Both harnesses use that context, and they generate the procedures from left to right. The generator
   makes the body of the procedure `i` against the signatures of the monomorphic procedures before it,
   which the renaming step names `P0` up to `P{i-1}`. Therefore no cycle and no self-recursion occurs.
   Only a monomorphic procedure becomes a target of a call, because `genCallStmt` and
   `ProcSigCorresponds` each need a monomorphic callee.

   The call graph of a generated program therefore holds real edges. A `call P{j}` for `j` below `i`
   occurs in the body `i`, and the procedure 0 is a leaf. Therefore the fields about the closure of the
   callees and about the call graph have real content on generated input. The `callerCalleeProgram`
   guard stays as a deterministic pin of one fixed shape with several edges.

   A body can reach a procedure that is not a target, through the call graph. Therefore `callerTargets`
   below, which is a *strict subset* of the procedures, does not make each procedure outside it
   unreachable. `checkFilterUnreachableRemoved` handles that fact: it compares against the transitive
   *closure* of the targets, so a procedure that a target reaches is correctly *not* obliged to
   disappear. Read `callerTargets`.

2. **A call to a partial function, in a body only.** `corePartialOps` holds each `Int.Safe*` operator,
   and each of them has the precondition `y ≠ 0` in `Core.Factory`. Therefore a generated expression
   *does* call a partial function, and PrecondElim acts and is not a no-op. On the `mkProgram` shape,
   each obligation lands **inside a procedure body**. The generator draws the contract clauses of a
   procedure from the same context, and `mkContractWFProc` emits a `$$wf` *procedure* only when a
   contract clause calls a partial function, which happens rarely. On the `mkMixedProgram` shape, a
   lifted function whose body or whose precondition calls a partial function *does* give a top-level
   `$$wf` procedure, through `mkFuncWFProc`. That is what gives `checkPrecondGeneratedWF` real content.

3. **A declared precondition, over the formal parameters only.** `genFunction` emits an optional
   `requires` clause over the formal parameters of the function itself. That limit is necessary,
   because `FuncWF.precond_freevars` needs the free variables of a precondition to be among the names
   of the inputs. The generator has a bias of 3 to 1 toward a clause that names a formal parameter.
   Therefore an inline `funcDecl` can be *declared* partial, and not only call a partial operator. That
   is what makes the path of PrecondElim that *removes* a precondition, the properties about the
   factory, and `functionsPreserved` reachable from generated input.

## Structural equality for the properties about the `changed` flag

Both properties about the `changed` flag use full structural equality on a `Program`. That equality is
available, because `Program`, `Decl` and `Procedure.Header` each derive `DecidableEq`, and
`Strata.DL.Imperative.Stmt` gives a `DecidableEq (Stmt P C)` instance that the derived `Decl` instance
uses.

The comparison includes the metadata, which is the correct behaviour and is not a source of a false
difference. `transformStmt` emits each unchanged statement again with its original metadata, and only a
fresh assert carries the metadata without the summary of the property.

Each property states its field of the specification exactly, and no property is weakened. The `#guard`s
at the end of the file pin each cause separately.

## The disagreement between `noFilter` and the call graph in FilterProcedures

`checkFilterAnalysisPreserving`, which is the field `PreservesCachedAnalysesWF`, has real content on
generated input, and it catches a real disagreement that generated input cannot reach.
`FilterProcedures.run` keeps a procedure that has `noFilter := true` in the list of the declarations,
and it filters that procedure *out* of the cached call graph. `isNeededProc` filters both maps, and it
reads no `noFilter` field. The procedure that stays then has no entry among the callees, which breaks
the field `complete` of `CallGraphWF` for the pair of the output. Each generated procedure has
`noFilter := false`, so generated input cannot reach the disagreement. The `noFilterProgram` guard at
the end of the file pins it deterministically instead.
-/

namespace StrataGenerators.Procedure.TestSupport

-- ── Program assembly + pipeline plumbing ─────────────────────────────────

/-- Assemble a `Program` from a procedure list, one `.proc` declaration each. -/
def mkProgram (ps : List Procedure) : Program :=
  { decls := ps.map (Decl.proc · .empty) }

/-- The structured statement list of the body of a procedure. The result is the empty list for a body that
    is a control-flow graph. `genProcedure` gives a structured body only, so this function is total on
    generated input. -/
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
    A declaration is liftable when `Function.ofPureFunc` accepts it, which asks that its formal parameters
    and its result each have a monotype. `genFunction` always gives such a function.

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
    `Core.Factory` (an unseeded factory has no builtin to read WF obligations off,
    so it would make every PrecondElim property vacuous), and the cached call graph
    is seeded with the program's own `toProcedureCG` (which FilterProcedures
    consults, falling back to recomputing it only if absent).

    The field `CoreTransformState.factory` is a plain `Factory`, so this function and each read of that
    field below need no unwrapping. -/
def mkState (prog : Program) : Transform.CoreTransformState :=
  { Transform.CoreTransformState.emp with
    factory := Core.Factory,
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
-- `PreservesCachedAnalysesWF` is a field of each of the three `*PhaseCorrect` structures, and it is an
-- implication between two claims about `CallGraphWF`. Therefore it needs `CallGraphWF` as a *decision
-- procedure*. The three definitions below transcribe `CalleesCountEqual` and each of the four
-- `CallGraphWF` fields of the specification.

/-- **`Core.CalleesCountEqual`.** Every callee's recorded multiplicity equals its
    occurrence count in the procedure's body. The spec quantifies over *all*
    strings; ranging over `k`'s keys together with the actual call list is
    faithful, because outside that union both sides are `0` (`k[c]?.getD 0 = 0`
    and `calls.count c = 0`). -/
def calleesCountEqual (k : Std.HashMap String Nat) (p : Procedure) : Bool :=
  let calls := Core.extractCallsFromProcedure p
  ((k.keys ++ calls).dedup).all fun c => k[c]?.getD 0 == calls.count c

/-- **`Core.CallGraphWF`**, decided field by field:

    * `sound`: each key of `callees` is a procedure of the program, and the count for each callee agrees.
    * `complete`: each procedure of the program has an entry in `callees`, and the count for each callee
      agrees.
    * `noZeroCount`: no recorded count is 0.
    * `callersTranspose`: `callers` is the transpose of `callees`. The specification states a
      biconditional. This definition checks both inclusions over the entries that exist, so each edge of
      one map must occur in the other map. Those two checks are the two directions of the
      biconditional. -/
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
    cached graph, by `callGraph := none`, satisfies the obligation with no content, because the conclusion
    of the specification holds only for a cached graph of the form `.some cgOut`. Therefore a `none` also
    satisfies this predicate. -/
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
-- The field `ANFEncoderCorrect.controlFlowPreserved` uses `stmtsCFEquiv`. This section copies
-- `cmdKindEquiv`, `stmtCFEquiv`, `stmtsCFEquiv` and `stripANFInits` from the specification file of
-- Strata, without a change, so that the executable check agrees with the declarative property exactly.

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
    | .cmd (.cmd (.init name _ _ _)) => !(CoreIdent.toPretty name).startsWith Core.CSE.cseVarPrefix
    | _ => true

-- ══ FilterProcedures check predicates ═════════════════════════════════════
-- Each property about FilterProcedures below targets the *last* procedure only, through
-- `callerTargets`, which is a strict subset. In the acyclic graph of calls that both harnesses
-- generate, the body `i` can call only a procedure before it. Therefore the last procedure is the source
-- of that graph, and it is the caller with the most edges. A target of that kind gives the dimension of
-- the *closure* of the call graph real content, which `checkFilterCalleeClosureRetained` needs. The
-- closure of its callees is exactly the set of the procedures that it calls, and the pass must keep each
-- of them.
--
-- The dimension of the removal also has real content: the pass must remove each procedure that the
-- target does not reach. The procedure `P0` is a leaf, and no other procedure reaches it, so the pass
-- removes it whenever it is not a callee of the target.
--
-- The property about `ChangedFlagValid` is the exception. It targets *each* procedure, and that is the
-- case where a `changed := true` as a literal is provably wrong.

/-- The set of the targets that each property about a removal in FilterProcedures uses. That set holds the
    name of the *last* procedure, if the list holds one.

    The choice of the last procedure is deliberate. In the acyclic graph of calls, the body `i` calls only
    a procedure before it. Therefore the last procedure is the source of that graph, and it has the largest
    possible closure of its callees. Such a target gives the dimension of the closure real content, which
    `checkFilterCalleeClosureRetained` needs. A leaf target, such as `P0`, would leave that dimension with
    no content.

    A *strict subset* also gives the dimension of the removal real content, because the pass must remove
    each procedure that the target does not reach. Each property about a removal stays faithful, because
    `checkFilterUnreachableRemoved` compares against the *closure*
    `targets ++ cg.getAllCalleesClosure targets`, and not against the targets alone. Therefore a procedure
    outside the target set that the target reaches is correctly *not* obliged to disappear. -/
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
    statement, and not a substitute over a sequence of names. Therefore it also gives the two claims that
    each body stays and that each declaration which is not a procedure stays. -/
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
    procedure has `noFilter = false`. The word "unreachable" is the condition of the specification itself,
    which is the absence from `targets ++ cgIn.getAllCalleesClosure targets`.

    The predicate checks the removal by name. `TestScaffold` renames each procedure to `P0` up to `Pk`, so
    no two names collide, and each declaration here carries empty metadata. Therefore the check by name is
    equal to the claim of the specification, which quantifies over the metadata. -/
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

/-- **`ChangedFlagValid` for FilterProcedures.** With the target set covering
    *every* procedure, nothing is removed, so `progOut = progIn` and the pass should
    report `changed = false`. It hardcodes `changed = true` instead
    (FilterProcedures.lean). -/
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

/-- Whether any function of the program still holds a precondition. Such a function is a top-level `.func`
    declaration, a member of a `.recFuncBlock` declaration, or an inline `funcDecl` inside the body of a
    procedure. -/
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
    no function of the output, whether top-level or inline in the body of a procedure,
    still carries a precondition. (Stronger than the spec field, which quantifies
    over top-level `.func` / `.recFuncBlock` declarations only; the inline
    `funcDecl` case is where generated input puts its preconditions.)

    Non-vacuous: `genFunction` draws an optional `requires` clause over the
    function's own formals (see `FunctionHasTypeAGen.Core.genPrecondition`), so
    a generated declaration does carry a precondition for the pass to remove. -/
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
    with the same name and the same spec. Its body can *grow* with an inserted assert, which this
    predicate permits, and on input with a call to a partial function it usually does grow. The
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
    with the same name, the same body, the same inputs and the same output, and with its preconditions
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
    is a sublist of the sequence of the output. The relative order of the input declarations
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

/-- **`ChangedFlagValid` for PrecondElim:** `changed ↔ progOut ≠ progIn`. -/
def checkPrecondChangedFlagValid (ps : List Procedure) : Bool :=
  checkChangedFlagValid Core.precondElimPipelinePhase (mkProgram ps)

/-- **The asserts of `PrecondElim` at a call site.** This is the operational content behind
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
    membership in the factory. By `nameMapConsistent`, the lookup of a name in the factory gives
    the array element of that name. -/
def factoryNames (f : @Lambda.Factory CoreLParams) : List String :=
  f.toArray.toList.map (·.name.name)

/-- **`PrecondElimFactoryCorrect.factoryGrows`.** The output factory contains
    every name the input factory had (entries are pushed, never dropped). -/
def checkPrecondFactoryGrows (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhaseSt Core.precondElimPipelinePhase prog with
  | some (_, st') =>
    let fIn := (mkState prog).factory
    let fOut := st'.factory
    (factoryNames fIn).all fun n => decide (n ∈ fOut)
  | none => true

/-- **`PrecondElimFactoryCorrect.factoryComplete`.** Every function the output
    program declares (top-level `.func` or a member of a `.recFuncBlock`) is
    present in the output factory. Run on `mkMixedProgram`, which is what puts
    top-level function declarations in front of the pass at all. -/
def checkPrecondFactoryComplete (ps : List Procedure) : Bool :=
  match runPhaseSt Core.precondElimPipelinePhase (mkMixedProgram ps) with
  | some ((_, out), st') =>
    let fOut := st'.factory
    out.decls.all fun
      | .func f _ => decide (f.name.name ∈ fOut)
      | .recFuncBlock fs _ => fs.all fun f => decide (f.name.name ∈ fOut)
      | _ => true
  | none => true

/-- **`PrecondElimFactoryCorrect.factoryStripped`.** Verbatim: every entry of the
    output factory has `preconditions = []`. Two independent causes concern this field. The
    seeded `Core.Factory` builtins keep the very preconditions the pass exists to
    discharge, and the pass pushes each declared function into the factory before
    stripping it. `checkPrecondDeclaredFactoryStripped` isolates the second,
    pass-side cause. -/
def checkPrecondFactoryStripped (ps : List Procedure) : Bool :=
  match runPhaseSt Core.precondElimPipelinePhase (mkMixedProgram ps) with
  | some (_, st') =>
    st'.factory.toArray.toList.all (·.preconditions.isEmpty)
  | none => true

/-- The factory entries that make `checkPrecondFactoryStripped` fail: every entry
    of the *output* factory that still carries a precondition, each paired with its
    formatted preconditions and with whether the input program declared it.

    This is the diagnostic counterpart to the check above. That property fails on
    each input, and also on the empty program. Therefore a minimized *program* witness
    says nothing about the cause; the offenders are in the factory, not the program.
    Reporting them directly is what makes the failure legible: on the empty program
    this returns 58 entries, all seeded `Core.Factory` builtins
    (`Int.SafeDiv` requiring `!(y == 0)`, `Sequence.select`, the `Bv*.Safe*`
    family, …), and all with `declared = false`.

    The `declared` flag separates the two independent causes documented above:
    `false` entries are the spec-side bug (builtins whose preconditions the pass
    must *keep*, since they are the very WF obligations it reads to emit asserts),
    and `true` entries are the pass-side bug (a declared function pushed into the
    factory unstripped, in `PrecondElim.lean`) that
    `checkPrecondDeclaredFactoryStripped` isolates. -/
def precondFactoryStrippedOffenders (ps : List Procedure) :
    List (String × List String × Bool) :=
  let prog := mkMixedProgram ps
  match runPhaseSt Core.precondElimPipelinePhase prog with
  | some (_, st') =>
    let declared := prog.decls.filterMap fun
      | .func f _ => some f.name.name
      | _ => none
    st'.factory.toArray.toList.filterMap fun lf =>
      if lf.preconditions.isEmpty then none
      else some (lf.name.name,
                 lf.preconditions.map fun p => toString (Std.format p.expr),
                 declared.contains lf.name.name)
  | none => []

/-- **`PrecondElimFactoryCorrect.factoryStripped`, restricted to the functions the
    program declares (pass side only).** Drops the seeded builtins from the claim,
    so the only cause it can report is the pass pushing a declared function's
    *unstripped* copy into the factory (`PrecondElim.lean`). Live exactly on the
    programs that declare a function with a precondition, which `genFunction`
    produces (module doc, point 3). -/
def checkPrecondDeclaredFactoryStripped (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhaseSt Core.precondElimPipelinePhase prog with
  | some (_, st') =>
    let declared := prog.decls.filterMap fun
      | .func f _ => some f.name.name
      | _ => none
    st'.factory.toArray.toList.all fun lf =>
      !declared.contains lf.name.name || lf.preconditions.isEmpty
  | none => true

/-- **`PreservesCachedAnalysesWF` for PrecondElim.** The pass registers each
    generated `$$wf` procedure as a leaf in the cached call graph
    (`addWFProcToCallGraph`); this checks that the graph it hands on is still
    well-formed for the program it hands on. Run on `mkMixedProgram` so the
    path for a `$$wf` procedure, which is the only path that changes the cached graph, is
    actually taken. -/
def checkPrecondAnalysisPreserving (ps : List Procedure) : Bool :=
  checkAnalysisPreserving Core.precondElimPipelinePhase (mkMixedProgram ps)

-- ══ ANFEncoder check predicates ═══════════════════════════════════════════

/-- **`ANFEncoderCorrect.declsLength`.** No declarations are added or removed:
    the output is a pointwise modification of the input. -/
def checkAnfDeclsLength (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.commonSubexprElimPhase prog with
  | some (_, out) => out.decls.length == prog.decls.length
  | none => true

/-- **`ANFEncoderCorrect.nonProcsUnchanged`.** Non-procedure declarations are
    unchanged. Run on `mkMixedProgram` so that function, type, axiom and
    `distinct` declarations are present to be left alone. -/
def checkAnfNonProcsUnchanged (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhase Core.commonSubexprElimPhase prog with
  | some (_, out) =>
    prog.decls.all fun d => d.kind == .proc || decide (d ∈ out.decls)
  | none => true

/-- **`ANFEncoderCorrect.procHeadersPreserved`.** Procedure headers and specs are
    preserved (ANF touches only bodies). -/
def checkAnfHeadersPreserved (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.commonSubexprElimPhase prog with
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
  match runPhase Core.commonSubexprElimPhase prog with
  | some (_, out) =>
    out.decls.all fun
      | .proc q _ =>
        (stmtsInits (bodyStmts q.body)).all fun (name, rhs) =>
          !(CoreIdent.toPretty name).startsWith Core.CSE.cseVarPrefix ||
            (match rhs with | .det _ => true | .nondet => false)
      | _ => true
  | none => true

/-- **`ANFEncoderCorrect.orderPreserved`.** Declaration names match positionally:
    the list of the output names is *equal* to the list of the input names, and not only a sublist,
    because ANF adds and removes no declaration. The property runs on `mkMixedProgram`, so each
    declaration kinds take part in the positional comparison. -/
def checkAnfOrderPreserved (ps : List Procedure) : Bool :=
  let prog := mkMixedProgram ps
  match runPhase Core.commonSubexprElimPhase prog with
  | some (_, out) =>
    decide (out.decls.map Decl.name = prog.decls.map Decl.name)
  | none => true

/-- **`ANFEncoderCorrect.controlFlowPreserved`.** This is the main claim of the specification,
    "ANFEncoder does not change control flow". Stripping the fresh ANF `init`s
    from each output body yields a statement list with the same control-flow
    skeleton (`stmtsCFEquiv`) as the corresponding input body. -/
def checkAnfControlFlowPreserved (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.commonSubexprElimPhase prog with
  | some (_, out) =>
    (programProcNames prog).all fun n =>
      match findProc prog n, findProc out n with
      | some p, some q => stmtsCFEquiv (bodyStmts p.body) (stripANFInits (bodyStmts q.body))
      | _, _ => false
  | none => true

/-- **`ChangedFlagValid` for ANFEncoder.** `changed ↔ progOut ≠ progIn`. Unlike
    the other two passes, ANFEncoder derives its flag from the fresh-variable
    counter actually advancing (`idx' > idx`, ANFEncoder.lean), which is
    which happens exactly when the pass rewrites a body. -/
def checkAnfChangedFlagValid (ps : List Procedure) : Bool :=
  checkChangedFlagValid Core.commonSubexprElimPhase (mkProgram ps)

/-- **`PreservesCachedAnalysesWF` for ANFEncoder.** ANF neither renames procedures
    nor adds or removes `call` statements, so the seeded call graph it passes
    through unchanged stays well-formed. -/
def checkAnfAnalysisPreserving (ps : List Procedure) : Bool :=
  checkAnalysisPreserving Core.commonSubexprElimPhase (mkProgram ps)

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
-- see each `Int.Safe*` precondition in `Core.Factory`. If it
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

-- ── The reproducers for PrecondElim that a person wrote ──────────────────
--
-- Each program below is a case that the *generator* cannot reach. The guards pin the behaviour, although
-- no property covers it.

-- ① **The `changed` flag for a function whose body calls a partial function.** The function
-- `function f() : int { Int.SafeDiv(1, 0) }` has no precondition of its own, and its *body* calls a
-- partial function. The pass inserts an `f$$wf` block that holds the assert for the obligation, so the
-- program provably changes, and the flag must be `true`.
private def bodyCallProc : Procedure :=
  procOf "P" [funcDeclOf "f" (some (callOp "Int.SafeDiv" (intLit 1) (intLit 0))) []]

#guard checkPrecondChangedFlagValid [bodyCallProc] == true
-- The obligation is real and the assert *is* emitted.
#guard programObligations (mkProgram [bodyCallProc]) == 1
#guard checkPrecondCallSiteAsserts [bodyCallProc] == true
-- The output program shows the rewrite, and the flag agrees with it.
#guard (match runPhase Core.precondElimPipelinePhase (mkProgram [bodyCallProc]) with
        | some (changed, out) => changed == true && out != mkProgram [bodyCallProc]
        | none => false) == true

-- ② **`preconditionsStripped` with a declaration that *does* carry a precondition.** `genFunction` also
-- reaches this shape, and the guard below pins it, so the property has a deterministic witness that does
-- not depend on a draw. The input holds a precondition, and the output holds none.
private def precondFuncProc : Procedure :=
  procOf "P" [funcDeclOf "g" none [callOp "Int.Ge" (intLit 1) (intLit 0)]]

#guard programHasFuncPrecond (mkProgram [precondFuncProc]) == true
#guard checkPrecondPreconditionsStripped [precondFuncProc] == true

-- ③ **The second cause of the failure of `factoryStripped`, apart from the builtin entries.** The pass
-- pushes a copy of each declared function into the factory, and it must remove the precondition from that
-- copy too. The entry of a declared function therefore holds no precondition, so only the first cause
-- remains in `checkPrecondFactoryStripped`. That cause is the builtin entries, whose preconditions the
-- pass must keep.
#guard checkPrecondDeclaredFactoryStripped [precondFuncProc] == true
#guard checkPrecondPreconditionsStripped [precondFuncProc] == true
-- The `$$wf` procedure for that declared precondition is well-formed, which is `noFilter := true` and an
-- empty spec. `generatedWF` has real content here.
#guard checkPrecondGeneratedWF [precondFuncProc] == true

-- ── Hand-built FilterProcedures reproducers ──────────────────────────────

/-- A program where `A` calls `B`, `B` calls `C`, and `D` calls nothing. It gives real content to the
    dimension of the closure of the call graph, which `calleeClosureRetained` and `unreachableRemoved` use.
    The caller `A` is **last** in the list, so `callerTargets`, which takes the last procedure, targets it.
    Therefore each `checkFilter*` guard below runs against the closure `{B, C}`, which is not empty. -/
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

/-- A program with a procedure that has `noFilter := true` and that no target reaches. FilterProcedures
    keeps the *declaration*, because it reads `noFilter`, and it filters that procedure out of the cached
    *call graph*, because `isNeededProc` reads no `noFilter` field. Therefore the graph that the pass
    caches is not complete for the program that it gives, which is a real disagreement with
    `PreservesCachedAnalysesWF`. Generated input cannot reach that disagreement, because `genProcedure`
    always sets `noFilter := false`.

    The procedure `P`, which has `noFilter := true`, is **first** in the list. Therefore `callerTargets`,
    which takes the *last* procedure, targets the plain procedure `Q`. `P` stays as the procedure that no
    target reaches and that `noFilter` protects, and it causes the disagreement. -/
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
-- `unreachableRemoved` still holds, because it permits a procedure with `noFilter := true` by design.
#guard checkFilterUnreachableRemoved noFilterProgram == true

-- The `changed` flag of FilterProcedures tracks whether the pass removed a procedure. A `changed := true`
-- as a literal would report the wrong value for a target set that covers each procedure, where the pass
-- removes nothing.
#guard checkFilterChangedFlagValid noFilterProgram == true
#guard checkFilterChangedFlagValid callerCalleeProgram == true

end Guards

end StrataGenerators.Procedure.TestSupport
