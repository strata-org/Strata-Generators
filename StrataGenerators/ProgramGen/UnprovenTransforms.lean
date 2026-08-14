-- The whole-program shrinker (and, through it, the program-level typechecker
-- oracle `progTypeChecks` plus the statement / procedure / function shrinkers) is
-- the base every property here builds on. The `Strata.Transform.*` imports are the
-- eight passes under test. `ASTtoCST` supplies `Core.formatProgram`, whose error
-- banner is the printer oracle for a `.cfg` body.
import StrataGenerators.ProgramGen.Shrink
import Strata.Transform.IrrelevantAxioms
import Strata.Transform.StructuredToUnstructured
import Strata.Transform.InsertLoopInvariantAsserts
import Strata.Transform.LoopElim
import Strata.Transform.FunctionInlining
import Strata.Transform.ProcedureInlining
import Strata.Transform.NondetElim
import Strata.Transform.LoopInitHoist
import Strata.Languages.Core.DDMTransform.ASTtoCST
-- `toCoreProofObligationProgram`, the executable symbolic evaluator, which is the
-- differential oracle for the two inlining eval-agreement properties below.
import Strata.Languages.Core.Verifier

open Lambda Core Imperative
-- `Core.formatProgram` lives in the `Strata` namespace (`ASTtoCST.lean`), so both
-- of these are needed to name it unqualified.
open Strata Strata.CoreDDM
-- `progTypeChecks` (the whole-program typechecker oracle), `sizeProgram`, and the
-- program shrinker come from the program test support.
open StrataGenerators.Program.TestSupport
-- `runPhase` / `runPhaseSt` (pipeline-phase plumbing on a seeded state), `mkState`,
-- `programProcNames`, `findProc` and `bodyStmts` come from the procedure test
-- support, and are reused verbatim rather than re-implemented here.
open StrataGenerators.Procedure.TestSupport
-- `toCmdStmts` (the `CmdExt` unwrapper the `Cmd P`-shaped passes need) and the
-- statement counters come from the statement test support.
open StrataGenerators.Stmt.TestSupport

/-!
# Properties for the eight Core transform passes that have no correctness proof

This module holds the check predicates for strata-generators issue #69: property
tests for the parts of `Strata/Transform/` that carry no machine-checked
correctness argument. Each predicate takes a **whole generated program**
(`Core.Program` from `ProgramGen.genProgram`, which is proven sound against
`ProgramHasTypeA`) and returns a `Bool`. Both harnesses evaluate the same
predicate, and the whole-program shrinker minimizes a counterexample.

## The eight passes and why they are here

`Strata/Transform/` holds 23 files. Only four passes have a correctness
companion. These eight passes have no correctness file, and no theorem in the
file itself:

`StructuredToUnstructured`, `LoopElim`, `InsertLoopInvariantAsserts`,
`CommonSubexprElim`, `FunctionInlining`, `ProcedureInlining`, `TerminationCheck`
and `IrrelevantAxioms`. Two more passes (`NondetElim` and `LoopInitHoist`) prove
syntactic preservation lemmas, but neither one proves its own headline
postcondition, so both are here too.

`TerminationCheck` is **not** covered. Its properties need a recursive function
to be non-vacuous, and the generator cannot make one yet (issues #15 and #29), so
each property would pass on empty input and give a false signal of coverage.

## Why the input is a whole program, and not a statement list

Three of the eight passes are program-to-program `PipelinePhase`s that read
declarations other than procedures: `IrrelevantAxioms` reads the axioms and the
function call graph, `ProcedureInlining` reads the callee's declaration at each
call site, and `FunctionInlining` reads a function body out of the factory. A
statement list cannot express any of those, so the input here is the whole
program that `ProgramGen.genProgram` draws, which holds every declaration kind.
The two purely structural passes (`StructuredToUnstructured` and `NondetElim`)
take a statement list, so each property applies the pass to each procedure body
of the program.

## The typechecker guard

`Program.typeCheck` rejects about 60 percent of generated programs, for three
documented reasons (see the module doc of `ProgramGen/Shrink`). A pass can be
blamed only for what it does to input that is already well typed. Therefore each
predicate that could be affected starts with `!progTypeChecks p ||`, which makes
it vacuous on a rejected draw and a real claim on the rest. The property
`program: typechecker rejections are only the known gaps` pins the three known
causes, so a new cause appears as a failure of that property, and not as silent
filtering here.

## Seeding the factory

`FunctionInlining` reads function bodies from a `Lambda.Factory`, and
`Core.Factory` holds **no** function body: 0 of its 310 entries have one. So a
property that runs the pass against `Core.Factory` alone can never inline, and
would pass vacuously. `programFactory` therefore pushes each function that the
*program* declares into `Core.Factory`, which is what `Core.Verifier` does in
production. A generated function has a body about half of the time, so the
inlining properties bite.

## Findings

The properties found **eight** defects. Each one is stated as the true claim, and
not weakened, so the property reports the defect instead of hiding it.

Five fail on **generated** input, at the rate given:

* `checkLoopBlockLabelsNodup` (4 of 40 draws) — `LoopElim` mints the block label
  `loopElim_havoc_{loop_num}` **two times** for one loop. `LoopElim.lean:126`
  builds one `havocd` statement, and `:139` puts it in the output two times: once
  inside the `arbitrary_iter_facts` block, and once after it, to model the exit
  state. So the output holds two blocks under one label, for each loop the pass
  erases. The pass carries a collision *detector* (`hasLabelConflict`) for a label
  the loop *body* already holds, which shows that a duplicate is a defect and not a
  design choice, but the detector cannot see the collision the pass makes itself.

* `checkS2uAllReachable` (10 of 40 draws) — every source `.block l` becomes an
  unreachable block in the emitted CFG. The `.block` case emits `(l, goto bl)` as
  a landing site for an `.exit l` and returns a *different* label as its own entry,
  so nothing jumps to `l` unless the body holds an `exit` to it. The minimal
  witness is a procedure whose body is one empty labelled block.

* `checkS2uCfgPrintable` (31 of 40 draws) — a procedure with a `.cfg` body does
  not print. `procToCST` writes the error "CFG bodies not yet supported in CST
  conversion" and emits an empty body (`FormatCore.lean:1112`).
  `StructuredToUnstructured` is the only pass in the tree that makes a `.cfg`
  body, so no other property can reach this hole. The same program with a
  structured body prints with no error.

* `checkInlineProcLabelsNodup` (2 of 400 draws) — `ProcedureInlining` gives two
  call sites of one procedure the same labels, in two independent ways. The wrapper
  block label `procName ++ "$inlined"` is a string concatenation that reaches no
  counter (`ProcedureInlining.lean:288`). And `renameAllLocalNames` folds the
  *label* renaming inside the fold over `var_map` (`:110`), so a callee that
  declares no variable has an empty `var_map`, the fold body never runs, and the
  callee's labels are copied verbatim at every call site. A callee that does
  declare a variable gets its labels freshened correctly, which shows the renaming
  works and the fold nesting is the defect.

* `checkInlineProcTypechecks` (1 of 400 draws) — `ProcedureInlining` copies an
  `old x` expression verbatim. Inside a procedure body, `old x` is a free variable
  whose name is literally `"old x"`, admitted because the enclosing procedure
  declares `x` as an inout parameter. The pass substitutes with
  `Statement.substFvar` over `var_map`, whose keys are the plain parameter names,
  so `"old x"` is not a key: `x` is renamed and `old x` is not. The caller then
  holds a free variable no parameter of the caller backs, and `Program.typeCheck`
  accepts the input while rejecting the output.

Two more are in `CommonSubexprElim`, which fires on **0 of 200** generated
programs, because no generated body holds a duplicated subexpression. So both need
a hand-built body, and a deterministic `#guard` at the end of this file pins each:

* `checkCseOutputTypechecks` — CSE emits a **polymorphic** annotation for an
  extracted subexpression whose operator carries no type annotation. It reads the
  type with `LExpr.typeOf`, which reads an annotation rather than inferring one, so
  the read gives `none` for a term as ordinary as `Int.Add(3, 4)` with a bare `.op`
  node, and the pass falls back to `LTy.forAll ["α"] (.ftvar "α")`
  (`CommonSubexprElim.lean:335`). The typechecker rejects that outright: "Variable
  annotation must be monomorphic, but got polymorphic type ∀[α]. α". The same body
  with the operator annotated gets `var $__cse.0 : int` and typechecks, which
  isolates the fallback as the cause. The fix is to infer the type rather than to
  invent a type variable.

* `checkCseFreshNamesFresh` — CSE declares `$__cse.0` a second time on a body that
  already declares it. The counter that mints the index never reads a program name
  (`CommonSubexprElim.lean:331`). The output then holds two declarations under that
  name, and the references the pass inserted resolve to the wrong one, so the
  rewrite changes what the program means. `Program.typeCheck` accepts the input and
  rejects the output.

The eighth is **not** in any of the eight passes — it is in the symbolic
**evaluator**, and it is unsound. It was found by the §2.9 properties, which are
the only ones here that ask what obligations actually reach SMT:

* **`Core.Statement.evalOneStmt` silently drops every proof obligation after a
  second `if *`.** The variable standing for a nondeterministic guard is named
  `$__nondet_cond_{pathConditions.scopes.length}` (`StatementEval.lean:586`) — from
  the current path-condition *depth*, not from a counter. Entering a `.block`
  pushes only a variable scope, and `Env.performMerge` pops the branch scope again,
  so two `if *` at the same depth are handed the same name; the second one's
  synthesized `init` re-declares a name already in scope, the path takes an error,
  and `evalAuxGo` stops without reporting anything. `if * { assert a }; if * {
  assert b }` yields the obligations `[a]`. `toCoreProofObligationProgram` returns
  `.ok`, so the verifier reports success on assertions it never checked. Pinned by
  the §2.9 `#guard`s, including a source program that declares the minted name
  itself and thereby loses **all** of its obligations. Tracked as repo issue #113
  and documented in `docs/strata-symbolic-eval-nondet-collision.md`.

  This is also why `checkNondetElimSymbolicNoLoss` is containment and not equality:
  `NondetElim` removes every `if *`, so the dropped obligations come back and the
  set legitimately grows.

Each other property passes on generated input. Three caveats, each recorded where
it belongs so a green tick is not read as more than it is:

* `checkKleeneMeasureAccepted` is a characterization and not a bug oracle, for the
  reason its docstring gives.
* the four `CommonSubexprElim` properties are vacuous on generated input (the pass
  fires on 0 of 200 draws), for the reason the §2.5 note gives.
* the four `FunctionInlining` properties now fire on **231 of 400** draws, after the
  generator work the §2.6 note describes, and all four pass — a real negative result
  for that pass rather than an absence of testing.

`#guard`s cover the four `CommonSubexprElim` properties on hand-built input, and
also back the `FunctionInlining` four (including a two-function chain on which the
fuel-1 and fuel-4 results genuinely differ).

The rates that make the other families non-vacuous, over 200 draws: 12 programs
declare an axiom and all 12 have one pruned; 33 carry a loop invariant or a
measure; 28 hold a nondeterministic guard; 7 hold an `init` in a loop body.

## What each property family checks

The families follow the sections of issue #69:

* **IrrelevantAxioms** (§2.1) — the *relevance* oracle, and not the `changed`
  flag (issue #91 covers the flag). Five properties: only an `.ax` declaration
  is ever removed, declaration order holds, each retained axiom is relevant, each
  removed axiom is irrelevant, and the pruned program still typechecks.
* **StructuredToUnstructured** (§2.2) — seven structural properties over the
  emitted CFG: no dangling target, distinct labels, the entry label exists,
  exactly one `.finish` block, each block is reachable from the entry, the
  command count holds modulo the commands the pass synthesizes, and the `.cfg`
  body prints.
* **LoopElim and InsertLoopInvariantAsserts** (§2.4) — the accounting of the
  verification conditions: the exact count of each inserted `assert` and
  `assume` as a function of the invariant count, a bare loop after the pass,
  idempotence, the statistics counter, and the survival of each verification
  condition through `LoopElim`.
* **CommonSubexprElim** (§2.5) — a fresh name that does not collide, the
  `assert` labels, the order of the fresh declarations, and a typecheckable
  output.
* **FunctionInlining** (§2.6) — identity at fuel 0, monotonicity in the fuel,
  type preservation, and freedom from capture.
* **ProcedureInlining** (§2.7) — distinct labels after two call sites, the
  count of the `assert` labels, the statistics counters, and a well-formed call
  graph.
* **NondetElim and LoopInitHoist** (§2.8) — the headline postcondition of each
  pass, which neither file proves: no `.nondet` guard is left, and each loop body
  holds no `init`.
* **The three loop passes under the symbolic evaluator** (§2.9) — whether
  `InsertLoopInvariantAsserts`, `NondetElim` and `LoopInitHoist` change the proof
  obligations that reach SMT. §2.4 and §2.8 state their claims syntactically; these
  three go through Strata's executable evaluator instead, which is the only oracle
  that can see an obligation surviving as *syntax* but never being emitted. Since
  the evaluator refuses a loop, each side runs `LoopElim` first. All three are
  stated as "no obligation is lost", and the §2.9 note gives the reason equality
  would be wrong for each. **These found the eighth defect, and it is in the
  evaluator rather than in any of the three passes** — see the findings note above.
-/

namespace StrataGenerators.Program.UnprovenTransforms

/-! ## Shared plumbing

Small accessors that more than one family needs. Each one reuses an existing
Strata or repository function; nothing below re-implements a traversal that
`Strata/Transform/` or the sibling test-support modules already supply. -/

/-- Each procedure declaration of a program, with its pretty-printed name. -/
def programProcs (p : Program) : List (String × Procedure) :=
  p.decls.filterMap fun
    | .proc q _ => some (CoreIdent.toPretty q.header.name, q)
    | _ => none

/-- The structured statement list of each procedure of a program, in declaration
    order. Reuses `bodyStmts`, so a `.cfg` body contributes nothing. -/
def programBodies (p : Program) : List (List Statement) :=
  (programProcs p).map fun (_, q) => bodyStmts q.body

/-- Each function that the program declares, from a `.func` declaration or from a
    `.recFuncBlock`. -/
def programFuncs (p : Program) : List Function :=
  p.decls.flatMap fun
    | .func f _ => [f]
    | .recFuncBlock fs _ => fs
    | _ => []

/-- Each axiom name that the program declares, in declaration order. -/
def programAxiomNames (p : Program) : List String :=
  p.decls.filterMap fun
    | .ax a _ => some a.name
    | _ => none

/-- The name of each declaration of a program, in order. Used by the properties
    about order, which compare this list before and after a pass. -/
def declNames (p : Program) : List String :=
  p.decls.map fun d => CoreIdent.toPretty d.name

/-- Whether a list holds no duplicate. -/
def nodup [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

/-- `Core.Factory` with each function that the program declares pushed in.

    `Core.Factory` holds no function body, so a pass that reads a body out of the
    factory (`FunctionInlining`, through `Factory.callOfLFunc`) can do nothing
    with `Core.Factory` alone. `Core.Verifier` seeds the factory from the program
    for the same reason. `pushIfNew` keeps the first entry under a name, so a
    program name that shadows a builtin cannot displace the builtin. -/
def programFactory (p : Program) : Lambda.Factory CoreLParams :=
  (programFuncs p).foldl (fun F f => F.pushIfNew f.toLFunc) Core.Factory

/-- The `(changed, output)` pair of a phase run on a program whose transform
    state also carries the program's own functions in the factory.

    `runPhaseSt` seeds the factory with `Core.Factory` only. A pass that needs a
    *body* needs `programFactory`, so this variant exists for those. `none` means
    that the pass raised a diagnostic. -/
def runPhaseWithFuncs (ph : Core.PipelinePhase) (prog : Program) :
    Option ((Bool × Program) × Transform.CoreTransformState) :=
  let st := { mkState prog with factory := programFactory prog }
  match Transform.runWith prog ph.transform st with
  | (.ok r, st') => some (r, st')
  | (.error _, _) => none

/-! ## The symbolic evaluator as a differential oracle

Two families below compare a pass's *proof obligations* before and after it runs:
`IrrelevantAxioms` (§2.1), where the obligation set must be **unchanged**, and
`ProcedureInlining` (§2.7), where it must not **shrink**. Both use Strata's own
executable symbolic evaluator, which is the `symbolicEval` phase of
`corePipelinePhases`.

**It panics on a loop.** `Core.Statement.evalOneStmt` aborts with "Cannot evaluate
`loop` statement. Please transform your program to eliminate loops before calling
`Core.Statement.evalAux`" — which is why `loopElimPipelinePhase` sits immediately
before `symbolicEval` in `transformPipelinePhases`. A `PANIC` is not catchable, so a
property using this oracle must screen the input with `programHasLoop` *first*, not
rely on the `none` branch. -/

/-- The obligation program that Strata's symbolic evaluator produces, or `none` when
    it raises a diagnostic. This is the `symbolicEval` phase of
    `corePipelinePhases`, called directly.

    Run at `VerifyOptions.quiet`, not `.default`: the evaluator `dbg_trace`s the whole
    obligation list at `.normal` verbosity or above (`Verifier.lean:832`), which would
    dump a VC listing into the build output on every `#guard` and every property
    sample. `.quiet` differs from `.default` only in that field.

    **Never call this on a program holding a loop** — see the section note. -/
def symbolicObligations (p : Program) : Option Program :=
  match Core.toCoreProofObligationProgram Core.VerifyOptions.quiet p with
  | .ok (out, _) => some out
  | .error _ => none

/-! ## Statement-level measurement

Counters over a statement list that more than one family needs. Each one walks
the tree at every depth, since every pass here can act at any depth. -/

mutual
/-- Each `assert` label of a statement, at any depth. -/
def stmtAssertLabels (s : Statement) : List String :=
  match s with
  | .cmd (.cmd (.assert l _ _)) => [l]
  | .cmd _ => []
  | .block _ b _ => stmtsAssertLabels b
  | .ite _ t e _ => stmtsAssertLabels t ++ stmtsAssertLabels e
  | .loop _ _ _ b _ => stmtsAssertLabels b
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []

/-- Each `assert` label of a statement list, at any depth. -/
def stmtsAssertLabels (ss : List Statement) : List String :=
  match ss with
  | [] => []
  | s :: rest => stmtAssertLabels s ++ stmtsAssertLabels rest
end

mutual
/-- Each `assume` label of a statement, at any depth. -/
def stmtAssumeLabels (s : Statement) : List String :=
  match s with
  | .cmd (.cmd (.assume l _ _)) => [l]
  | .cmd _ => []
  | .block _ b _ => stmtsAssumeLabels b
  | .ite _ t e _ => stmtsAssumeLabels t ++ stmtsAssumeLabels e
  | .loop _ _ _ b _ => stmtsAssumeLabels b
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []

/-- Each `assume` label of a statement list, at any depth. -/
def stmtsAssumeLabels (ss : List Statement) : List String :=
  match ss with
  | [] => []
  | s :: rest => stmtAssumeLabels s ++ stmtsAssumeLabels rest
end

mutual
/-- Each `loop` of a statement, at any depth, as its
    `(guard, measure, invariants)` triple. The body is dropped, because each
    property below reads only the loop's own annotation. -/
def stmtLoopShapes (s : Statement) :
    List (ExprOrNondet Expression × Option Expression.Expr × List (String × Expression.Expr)) :=
  match s with
  | .loop g m inv b _ => (g, m, inv) :: stmtsLoopShapes b
  | .block _ b _ => stmtsLoopShapes b
  | .ite _ t e _ => stmtsLoopShapes t ++ stmtsLoopShapes e
  | .cmd _ | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []

/-- Each `loop` of a statement list, at any depth. -/
def stmtsLoopShapes (ss : List Statement) :
    List (ExprOrNondet Expression × Option Expression.Expr × List (String × Expression.Expr)) :=
  match ss with
  | [] => []
  | s :: rest => stmtLoopShapes s ++ stmtsLoopShapes rest
end

/-- Whether any procedure body of the program holds a `loop`, at any depth.

    The screen every property using `symbolicObligations` must apply *before* calling
    it: the symbolic evaluator **panics** on a loop rather than returning an error, so
    the `none` branch cannot absorb it (see the oracle note above). -/
def programHasLoop (p : Program) : Bool :=
  (programBodies p).any fun ss => !(stmtsLoopShapes ss).isEmpty

/-- Each block label of a statement list, at any depth, together with each
    `assert`, `assume` and `cover` label. Reuses the pass's own collector
    (`ProcedureInlining.Block.labelsOfBlocksAndAssertAssumes`), which is the list
    the pass itself renames, so a property about it tests the pass on its own
    terms. -/
def allLabels (ss : List Statement) : List String :=
  ss.flatMap Core.ProcedureInlining.Statement.labelsOfBlocksAndAssertAssumes

/-- Each block label of a statement list, at any depth. Reuses Strata's own
    `Block.labels`, which collects the label of a `.block` and the target of an
    `.exit`. -/
def blockAndExitLabels (ss : List Statement) : List String := Imperative.Block.labels ss

mutual
/-- Only the `.block` labels of a statement, at any depth. Unlike
    `Imperative.Block.labels`, an `.exit` target is not included, so the result is
    the list of labels the program *declares* rather than the list it mentions. -/
def stmtBlockLabels (s : Statement) : List String :=
  match s with
  | .block l b _ => l :: stmtsBlockLabels b
  | .ite _ t e _ => stmtsBlockLabels t ++ stmtsBlockLabels e
  | .loop _ _ _ b _ => stmtsBlockLabels b
  | .cmd _ | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []

/-- Only the `.block` labels of a statement list, at any depth. -/
def stmtsBlockLabels (ss : List Statement) : List String :=
  match ss with
  | [] => []
  | s :: rest => stmtBlockLabels s ++ stmtsBlockLabels rest
end

/-! ## §2.1 `IrrelevantAxioms` — the relevance oracle

`irrelevantAxiomsPipelinePhase` prunes each axiom that its fixed-point relevance
computation finds irrelevant to a seed set of function names. Issue #91 pins the
`changed` flag, which the pass hardcodes to `true`. What no property covers yet is
whether the pass prunes the **right** axioms, which is what this family checks.

The seed set is each function the program declares (`axiomSeedFunctions`). That is
the production shape: `Verifier` seeds the pass with the functions of the goal
under proof. A seed set of every declared function is the most demanding case for
the "each removed axiom is irrelevant" direction, because it makes the relevant
set as large as it can be, so a wrongly pruned axiom is a real loss. -/

/-- The seed function names for the relevance query: each function that the
    program declares. -/
def axiomSeedFunctions (p : Program) : List String :=
  (programFuncs p).map fun f => CoreIdent.toPretty f.name

/-- The phase under test, seeded with the program's own function names. -/
def irrelevantAxiomsPhase (p : Program) : Core.PipelinePhase :=
  Core.irrelevantAxiomsPipelinePhase (axiomSeedFunctions p)

/-- The set of axiom names that the pass itself calls irrelevant. This is the
    pass's own oracle (`IrrelevantAxioms.getIrrelevantAxioms` over
    `IrrelevantAxioms.Cache.build`), so a property that compares the pruned
    program against it tests the *pass*, and a property that recomputes the
    relevance closure independently tests the *oracle*. -/
def irrelevantByPass (p : Program) : List String :=
  Core.IrrelevantAxioms.getIrrelevantAxioms p (Core.IrrelevantAxioms.Cache.build p)
    (axiomSeedFunctions p)

/-- **Only an axiom is ever removed.** The pass filters on the `.ax` constructor,
    so each declaration of any other kind must survive with its metadata
    untouched. A failure means that the filter reached a declaration kind the pass
    has no business touching. -/
def checkAxiomsOnlyAxRemoved (p : Program) : Bool :=
  match runPhase (irrelevantAxiomsPhase p) p with
  | some (_, out) =>
    p.decls.all fun d =>
      match d with
      | .ax _ _ => true
      | _ => decide (d ∈ out.decls)
  | none => true

/-- **Declaration order holds.** The output declaration names are a sublist of the
    input's: the pass may drop an axiom, but it may not reorder, rename or
    duplicate a declaration. Stated with Lean's decidable `List.Sublist`, which is
    the same formulation the `FilterProcedures` order properties use. -/
def checkAxiomsOrderPreserved (p : Program) : Bool :=
  match runPhase (irrelevantAxiomsPhase p) p with
  | some (_, out) => decide ((declNames out).Sublist (declNames p))
  | none => true

/-- **Each retained axiom is relevant.** An axiom that survives the pass must not
    be in the set the relevance oracle calls irrelevant. This is the direction
    that catches a pass that prunes too little, and it holds by construction if
    the pass filters on exactly the oracle's answer, so it is a regression gate on
    the filter and on the `Std.HashSet` round trip inside it. -/
def checkAxiomsRetainedRelevant (p : Program) : Bool :=
  match runPhase (irrelevantAxiomsPhase p) p with
  | some (_, out) =>
    let irrelevant := irrelevantByPass p
    (programAxiomNames out).all fun a => !irrelevant.contains a
  | none => true

/-- **Each removed axiom is irrelevant.** This is the soundness direction, and the
    one that matters: the pass is declared model-preserving, so dropping an axiom
    that a goal needs turns `unsat` into a false `sat`. An axiom that the output
    does not hold must appear in the oracle's irrelevant set.

    The oracle itself is checked independently by
    `checkAxiomsRemovedNotSeedReachable`: this property alone would hold even if
    the oracle were wrong, since both sides read the same oracle. -/
def checkAxiomsRemovedIrrelevant (p : Program) : Bool :=
  match runPhase (irrelevantAxiomsPhase p) p with
  | some (_, out) =>
    let kept := programAxiomNames out
    let irrelevant := irrelevantByPass p
    (programAxiomNames p).all fun a => kept.contains a || irrelevant.contains a
  | none => true

/-- **A removed axiom mentions no reachable function.** The independent check on
    the relevance oracle: an axiom that the pass drops must mention no function in
    the call-graph closure of the seed set. `getCalleesClosure` and
    `getCallersClosure` over the program's own function call graph give the
    closure, which is what `getIrrelevantAxioms` starts from
    (`IrrelevantAxioms.lean:52`), and `LExpr.getOps` gives the functions of the
    axiom body, which is what `functionImmediateAxiomMap` reads.

    A builtin is excluded, in the same way the axiom map excludes one: a builtin
    appears in nearly every axiom body, so counting one would make each axiom
    relevant and collapse the property to a tautology. -/
def checkAxiomsRemovedNotSeedReachable (p : Program) : Bool :=
  match runPhase (irrelevantAxiomsPhase p) p with
  | some (_, out) =>
    let kept := programAxiomNames out
    let cg := p.toFunctionCG
    let closure := ((axiomSeedFunctions p).flatMap fun f =>
      f :: cg.getCalleesClosure f ++ cg.getCallersClosure f).dedup
    p.decls.all fun d =>
      match d with
      | .ax a _ =>
        kept.contains a.name ||
          (Lambda.LExpr.getOps a.e).all fun op =>
            let fname := CoreIdent.toPretty op
            Core.builtinFunctions.contains fname || !closure.contains fname
      | _ => true
  | none => true

/-- **The pruned program still typechecks.** Dropping an axiom cannot break the
    types of the declarations that stay, since an axiom binds no name that another
    declaration resolves against. Conditional on the input typechecking. -/
def checkAxiomsPrunedTypechecks (p : Program) : Bool :=
  !progTypeChecks p ||
    (match runPhase (irrelevantAxiomsPhase p) p with
     | some (_, out) => progTypeChecks out
     | none => true)

/-- **Pruning axioms leaves the proof obligations unchanged.** The semantic
    counterpart to the five syntactic properties above, and the sharpest claim this
    pass admits without a solver.

    An axiom is an *assumption*, never an obligation, so deleting one cannot add,
    remove or rename a single obligation. The obligation sets before and after must
    therefore be **equal** — not merely contained, as for `ProcedureInlining`, whose
    obligations legitimately duplicate per call site. Equality is the right claim here
    precisely because this pass is supposed to change nothing that reaches the solver.

    The oracle is Strata's own `symbolicEval` phase, so what the property compares is
    the obligations a verification run would actually receive.

    ### What it does and does not catch

    It catches the pass perturbing the obligation *structure*: adding, dropping or
    relabelling one. It does **not** catch the failure mode that matters most —
    pruning an axiom some obligation needed, which leaves the obligation present but
    no longer provable. That is invisible without a solver, since the obligation
    expression is unchanged and only its *provability* differs. Confirming that needs
    the `--smt` oracle, and is the natural follow-up.

    So this is a necessary-but-not-sufficient condition for the pass's
    `modelPreserving` annotation. Stating it as such rather than overselling it: a
    green result here means the pass did not disturb the obligations, not that it
    preserved their provability.

    ### Coverage

    Conditional on the input typechecking **and being loop-free**, because the
    symbolic evaluator panics on a loop (see the oracle note). Measured non-vacuous:
    152 of 300 generated draws satisfy both guards, and all 152 give exactly equal
    obligation sets. -/
def checkAxiomsObligationsUnchanged (p : Program) : Bool :=
  !progTypeChecks p || programHasLoop p ||
    (match runPhase (irrelevantAxiomsPhase p) p with
     | none => true
     | some (_, out) =>
       (match symbolicObligations p, symbolicObligations out with
        | some before, some after =>
          let la := (programBodies before).flatMap stmtsAssertLabels
          let lb := (programBodies after).flatMap stmtsAssertLabels
          -- Equality as multisets: same length, and each label of one occurs in the
          -- other. Comparing lengths rules out a silent duplication that plain
          -- mutual containment would miss.
          la.length == lb.length && la.all lb.contains && lb.all la.contains
        | none, none => true   -- the oracle read neither side; no claim to make
        | _, _ => false))      -- it read one side only: the pass changed its verdict

/-! ## §2.2 `StructuredToUnstructured` — the structural properties

`stmtsToBlocks` (`StructuredToUnstructured.lean:58`) threads a continuation label
`k` and an `exitConts` association list by hand across eight statement cases, and
mints labels from a `StringGenState`. It has no theorem at all. The seven
properties below are the structural claims that need no CFG interpreter: Strata
has no executable one (`CFGSemantics.lean` gives only the relation `StepCFG`), so a
differential test against `Statement.eval` is out of scope here.

Each property applies `stmtsToCFG` to each procedure body of the program. The
`CmdExt` wrapper is kept, since `stmtsToCFG` is generic in the command type and
Core's `Command` has each instance it needs, so no unwrapping is needed and a
`call` statement is carried through as a command. -/

/-- The CFG of one procedure body. -/
def bodyCfg (ss : List Statement) : Core.DetCFG :=
  Imperative.stmtsToCFG (P := Expression) (CmdT := Command) ss

/-- The label of each block of a CFG, in order. -/
def cfgLabels (c : Core.DetCFG) : List String := c.blocks.map (·.1)

/-- The target of each transfer command of a CFG. A `.finish` block has no
    target, and a `.condGoto` has two (which coincide for a `goto`, since Strata
    models an unconditional jump as a diagonal `condGoto`). -/
def cfgTargets (c : Core.DetCFG) : List String :=
  c.blocks.flatMap fun (_, b) =>
    match b.transfer with
    | .condGoto _ lt lf _ => [lt, lf]
    | .finish _ => []

/-- The labels reachable from `entry` in at most `fuel` rounds of a
    breadth-first sweep. `fuel = c.blocks.length` is enough, because each round
    that adds nothing stops the sweep and each round that adds something adds at
    least one of the finitely many labels. -/
def cfgReachable (c : Core.DetCFG) : List String :=
  go c.blocks.length [c.entry]
where
  go (fuel : Nat) (seen : List String) : List String :=
    match fuel with
    | 0 => seen
    | fuel + 1 =>
      let next := (seen.flatMap fun l =>
        match c.blocks.lookup l with
        | some b =>
          (match b.transfer with
           | .condGoto _ lt lf _ => [lt, lf]
           | .finish _ => [])
        | none => []).filter fun t => !seen.contains t
      if next.isEmpty then seen else go fuel (seen ++ next.dedup)

/-- The number of `.finish` blocks of a CFG. -/
def cfgFinishCount (c : Core.DetCFG) : Nat :=
  (c.blocks.filter fun (_, b) => match b.transfer with | .finish _ => true | _ => false).length

/-- The command count of a CFG: the total over each block. -/
def cfgCmdCount (c : Core.DetCFG) : Nat := (c.blocks.map fun (_, b) => b.cmds.length).sum

mutual
/-- The count of the commands of a statement that the pass can reach.

    Two constructors count as nothing, and each for a reason the pass states:
    a `funcDecl` and a `typeDecl`, because `stmtsToBlocks` drops both ("Not yet
    supported, so just continue with `rest`"). -/
def stmtCmdCount (s : Statement) : Nat :=
  match s with
  | .cmd _ => 1
  | .block _ b _ => stmtsCmdCount b
  | .ite _ t e _ => stmtsCmdCount t + stmtsCmdCount e
  | .loop _ _ _ b _ => stmtsCmdCount b
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => 0

/-- The count of the commands of a statement list that the pass can reach.

    The list **stops at the first `.exit`**, because an `.exit` is unconditional:
    each statement after it in the same list is unreachable, and the pass drops
    them ("Any statements after the `.exit` are skipped",
    `StructuredToUnstructured.lean:167`). A nested list under a `.block`, an `.ite`
    branch or a loop body is counted on its own, which matches the pass: each one
    is a separate `stmtsToBlocks` call with its own continuation. -/
def stmtsCmdCount (ss : List Statement) : Nat :=
  match ss with
  | [] => 0
  | .exit _ _ :: _ => 0
  | s :: rest => stmtCmdCount s + stmtsCmdCount rest
end

/-- **No dangling label.** Each `.goto` or `.condGoto` target of the emitted CFG
    occurs as a block label. Given the manual threading of `k` and `exitConts`
    across eight cases, and the `.exit` fallback that silently continues on an
    invalid exit (`| .none => k`, line 163, with the comment "We assume a prior
    check to avoid this"), this is where a defect is most likely. -/
def checkS2uNoDanglingLabel (p : Program) : Bool :=
  (programBodies p).all fun ss =>
    let c := bodyCfg ss
    let labels := cfgLabels c
    (cfgTargets c).all labels.contains

/-- **Distinct block labels.** Two blocks under one label make the CFG
    ill-defined: `blocks.lookup` would find the first one and drop the second.

    Conditional on the source body already having distinct `.block` labels, and it
    must be: `genFreshLabel` (`StmtHasTypeAGen/Core.lean:114`) draws a label fresh
    against the *enclosing* labels only, which is what the `block` premise of the
    typing spec requires, so two **sibling** blocks may share a label. A body such as
    `j: { } j: { }` is therefore generatable, and it makes the emitted CFG hold two
    blocks named `j` — through no fault of this pass, which copies the source label.
    Blaming the pass for that would report a generator artefact as a Strata defect,
    the same way the `procInline` label property has to guard against `String.arbitrary`
    drawing `""` twice.

    Under the guard the property is a real claim: the pass mints labels of its own
    (`l$`, `blk$`, `ite$`, `loop_entry$`, and so on) from a `StringGenState` counter,
    and none of them may collide with each other or with a source label. -/
def checkS2uLabelsNodup (p : Program) : Bool :=
  (programBodies p).all fun ss =>
    !nodup (stmtsBlockLabels ss) || nodup (cfgLabels (bodyCfg ss))

/-- **The entry label exists.** `stmtsToCFG` returns the label that
    `stmtsToBlocks` gives back as the entry. When the body is empty and the
    accumulator flushes nothing, `flushCmds` returns the continuation `k` rather
    than a fresh label, so the entry is then the `end$` block, which the graph does
    hold. -/
def checkS2uEntryExists (p : Program) : Bool :=
  (programBodies p).all fun ss =>
    let c := bodyCfg ss
    (cfgLabels c).contains c.entry

/-- **Exactly one `.finish` block.** `stmtsToCFGM` makes one `end$` block whose
    transfer is `.finish`, and nothing else in the pass makes one. So a count
    other than one means either a lost exit point or a duplicated one. -/
def checkS2uOneFinish (p : Program) : Bool :=
  (programBodies p).all fun ss => cfgFinishCount (bodyCfg ss) == 1

/-- **Each block is reachable from the entry.** FAILS honestly. An orphan block is
    dead code that the pass emitted and no path can enter, which points at a
    continuation the threading dropped.

    Every source `.block l` becomes an orphan. The `.block` case
    (`StructuredToUnstructured.lean:78`) emits a block `(l, goto bl)` whose only job
    is to give the source label a landing site for an `.exit l`, and separately
    flushes the accumulated commands into `accumEntry`, which is what the case
    returns as its own entry. So the caller jumps to `accumEntry` and never to `l`,
    and the `l` block is entered only by an `.exit l` inside the body. A block with
    no `exit` to it therefore has no predecessor at all.

    The minimal witness is a procedure whose body is one empty labelled block: the
    emitted graph is `f -> goto end$_0` plus `end$_0 -> finish`, with entry
    `end$_0`, so `f` is unreachable. Whether this is harmful depends on the
    consumer: dead code is sound, but a CFG consumer that assumes each block is
    reachable (a dominator computation, or a check that each block was visited)
    reads a block that no path enters. The pass emits the block unconditionally,
    even when the body holds no `exit`, so the label could be dropped in that case.

    Measured at 10 of 40 draws, which is the rate at which a generated procedure
    body holds a labelled block. -/
def checkS2uAllReachable (p : Program) : Bool :=
  (programBodies p).all fun ss =>
    let c := bodyCfg ss
    let reachable := cfgReachable c
    (cfgLabels c).all reachable.contains

/-- **The command count does not shrink.** The pass synthesizes commands (a
    `$__nondet_*` init for a nondet guard, an invariant `assert`, and the three
    measure commands), so the count can grow. It must never shrink: a smaller
    count means the pass dropped a command of the source program.

    The source count excludes exactly what the pass openly does not carry, so the
    claim never blames it for a documented omission: a `funcDecl` and a `typeDecl`
    statement count as zero, and a statement after an `.exit` in the same list
    counts as zero, because an `.exit` is unconditional and the pass skips the
    remainder. Anything else the pass drops is a real loss and the property reports
    it. -/
def checkS2uCmdCountGrows (p : Program) : Bool :=
  (programBodies p).all fun ss => stmtsCmdCount ss ≤ cfgCmdCount (bodyCfg ss)

/-- **A `.cfg` body prints.** FAILS honestly. `procToCST` writes the error "CFG
    bodies not yet supported in CST conversion" and emits an empty body
    (`FormatCore.lean:1112`), so a procedure that this pass rewrote cannot be
    printed at all.

    `StructuredToUnstructured` is the only pass in the tree that makes a `.cfg`
    body, so issue #91's printer oracle cannot reach this hole: nothing else
    produces the constructor. The oracle here is the formatter's own error banner,
    which `Core.formatProgram` appends when the conversion collected an error, so
    the property needs no access to the private error array.

    The gap is wider than the printer. `Program.typeCheck` also rejects a
    `.cfg`-bodied procedure ("CFG procedures not supported yet") while accepting the
    structured original, and `corePipelinePhases` appends a typecheck phase *after*
    the transform phases — so a program that went through this pass can be neither
    printed nor re-checked. The `#guard`s at the end of this file pin both halves.

    The property is vacuous on a program with no procedure, which is honest: there
    is then no `.cfg` body to print. -/
def checkS2uCfgPrintable (p : Program) : Bool :=
  let cfgProg : Program :=
    { decls := p.decls.map fun d =>
        match d with
        | .proc q md =>
          match q.body with
          | .structured ss => .proc { q with body := .cfg (bodyCfg ss) } md
          | .cfg _ => .proc q md
        | other => other }
  (toString (Core.formatProgram cfgProg)).splitOn "Errors encountered" |>.length == 1

/-! ## §2.4 `LoopElim` and `InsertLoopInvariantAsserts` — accounting of the
verification conditions

The repository already checks that `LoopElim` preserves typeability and removes
each loop. What no property covers is whether the verification conditions
**survive**, which is the whole point of the pair.
`InsertLoopInvariantAsserts.lean` states its output shape exactly (its docstring
enumerates VC1 to VC4), so the oracle is unusually sharp: per invariant the pass
must emit 1 entry `assert`, 1 entry `assume`, 1 mid `assume`, 1 maintain
`assert` and 1 exit `assume`, and a measure adds exactly 3 more. -/

/-- The phase that materializes the verification conditions of a loop. -/
def loopInvPhase : Core.PipelinePhase := Core.insertLoopInvariantAssertsPipelinePhase

/-- The total invariant count over each loop of a program, at any depth. -/
def programInvariantCount (p : Program) : Nat :=
  ((programBodies p).map fun ss =>
    ((stmtsLoopShapes ss).map fun (_, _, inv) => inv.length).sum).sum

/-- The count of loops that carry a measure, over the whole program. -/
def programMeasureLoopCount (p : Program) : Nat :=
  ((programBodies p).map fun ss =>
    ((stmtsLoopShapes ss).filter fun (_, m, _) => m.isSome).length).sum

/-- Whether the program holds a nondeterministic loop that carries a measure.
    `insertInvariantAsserts` rejects such a loop with a diagnostic
    (`InsertLoopInvariantAsserts.lean:113`), so a property about the pass's output
    is vacuous on such a program and `checkLoopNondetMeasureThrows` states the
    rejection itself. -/
def hasNondetMeasureLoop (p : Program) : Bool :=
  (programBodies p).any fun ss =>
    (stmtsLoopShapes ss).any fun (g, m, _) =>
      m.isSome && (match g with | .nondet => true | .det _ => false)

/-- The number of labels of `ls` that start with `pfx`. -/
def countPrefixed (pfx : String) (ls : List String) : Nat :=
  (ls.filter fun l => l.startsWith pfx).length

/-- **The exact count of inserted asserts and assumes.** The pass's docstring
    fixes the shape, so the count follows from the invariant count `n` and the
    count `m` of loops that carry a measure:

    * an `assert` with the `insertLoopInvAssert_` prefix: `n` at entry, `n` to
      maintain, and `2 * m` for the measure (the lower bound and the decrease), so
      `2 * n + 2 * m`;
    * an `assume` with the `insertLoopInvAssume_` prefix: `n` at entry, `n` at
      mid, `n` at exit, `m` for the measure, and one negated guard per
      deterministic loop that carries an invariant or a measure.

    The negated guard makes the `assume` count depend on the guard kind, which the
    count of invariants alone does not fix, so the property states the `assert`
    count exactly and bounds the `assume` count below by `3 * n + m`. The `assert`
    side is the one that carries each verification condition, so an exact claim
    there is what the property needs to be sharp.

    Vacuous when a nondeterministic loop carries a measure, since the pass then
    throws. -/
def checkLoopVcAssertCount (p : Program) : Bool :=
  hasNondetMeasureLoop p ||
    (match runPhase loopInvPhase p with
     | some (_, out) =>
       let n := programInvariantCount p
       let m := programMeasureLoopCount p
       let asserts := ((programBodies out).map fun ss =>
         countPrefixed Core.insertLoopInvAssertPrefix (stmtsAssertLabels ss)).sum
       let assumes := ((programBodies out).map fun ss =>
         countPrefixed Core.insertLoopInvAssumePrefix (stmtsAssumeLabels ss)).sum
       asserts == 2 * n + 2 * m && 3 * n + m ≤ assumes
     | none => true)

/-- **Each loop is bare after the pass.** The pass moves the invariants and the
    measure of a loop into explicit `assert` and `assume` statements and clears
    both fields, so no loop of the output may still carry either. `LoopElim` then
    *throws* on a loop that still does, so a failure here is not cosmetic: it
    blocks the rest of the pipeline. -/
def checkLoopBareAfterPass (p : Program) : Bool :=
  hasNondetMeasureLoop p ||
    (match runPhase loopInvPhase p with
     | some (_, out) =>
       (programBodies out).all fun ss =>
         (stmtsLoopShapes ss).all fun (_, m, inv) => inv.isEmpty && m.isNone
     | none => true)

/-- **The pass is idempotent.** The pipeline runs it to a fixed point through
    `runProgramUntil`, so a second run must change nothing. Since the first run
    leaves each loop bare, the second run's `insertInvariantAsserts` returns `none`
    for each statement, and the output must equal its input.

    The comparison is full structural equality on `Program`, which the derived
    `DecidableEq` supplies. -/
def checkLoopVcIdempotent (p : Program) : Bool :=
  hasNondetMeasureLoop p ||
    (match runPhase loopInvPhase p with
     | some (_, out) =>
       (match runPhase loopInvPhase out with
        | some (_, out2) => decide (out2 = out)
        | none => false)
     | none => true)

/-- **The statistics counter is faithful.** The pass increments
    `InsertLoopInvariantAsserts.insertedAssertAssumes` by its own count of the
    statements it inserted. That counter is a hand-maintained side channel of the
    same kind as the `changed` flag, whose family gave four findings, so it
    deserves an independent check: the counter must equal the number of prefixed
    `assert` and `assume` statements the output actually holds.

    The `assume` side includes the negated guard, which the pass counts in
    `numAssertAssumes` through `exit_assumes.length`, so both sides here count the
    same set and the claim is an equality. -/
def checkLoopVcStatFaithful (p : Program) : Bool :=
  hasNondetMeasureLoop p ||
    (match runPhaseSt loopInvPhase p with
     | some ((_, out), st) =>
       let inserted := ((programBodies out).map fun ss =>
         countPrefixed Core.insertLoopInvAssertPrefix (stmtsAssertLabels ss) +
         countPrefixed Core.insertLoopInvAssumePrefix (stmtsAssumeLabels ss)).sum
       st.statistics.get "InsertLoopInvariantAsserts.insertedAssertAssumes" == (inserted : Int)
     | none => true)

/-- **No verification condition is lost through `LoopElim`.** The two passes are a
    pair: the first materializes the conditions, the second removes the loop that
    carried them. Each `assert` label the first pass minted must still appear in
    the program the second pass emits, or a proof obligation vanished silently and
    the verifier reports a false pass.

    `LoopElim` runs on the *output* of the first pass, which is the production
    order (`transformPipelinePhases` puts `insertLoopInvariantAssertsPipelinePhase`
    immediately before `loopElimPipelinePhase`). -/
def checkLoopVcSurvivesElim (p : Program) : Bool :=
  hasNondetMeasureLoop p ||
    (match runPhase loopInvPhase p with
     | some (_, mid) =>
       (match runPhase Core.loopElimPipelinePhase mid with
        | some (_, out) =>
          let outLabels := ((programBodies out).map stmtsAssertLabels).flatten
          ((programBodies mid).map stmtsAssertLabels).flatten.all fun l =>
            !l.startsWith Core.insertLoopInvAssertPrefix || outLabels.contains l
        | none => true)
     | none => true)

/-- **A nondeterministic loop that carries a measure is rejected.** A `while *`
    loop iterates an arbitrary number of times, so no measure can show that it
    terminates, and the pass throws rather than dropping the measure silently
    (`InsertLoopInvariantAsserts.lean:113`). The generator can draw exactly this
    shape: `genCondOrNondet` gives `.nondet` about 20 percent of the time and
    `genOptMeasure` gives a measure about 75 percent of the time.

    Stated as a biconditional, so it catches both a missed rejection and a
    spurious one. -/
def checkLoopNondetMeasureThrows (p : Program) : Bool :=
  (runPhase loopInvPhase p).isNone == hasNondetMeasureLoop p

/-- **`LoopElim` mints distinct block labels.** FAILS honestly.
    `removeLoop` builds one `havocd` block statement labeled
    `loopElim_havoc_{loop_num}` (`LoopElim.lean:126`) and puts it into the output
    **two times** (`:139`): once inside the `arbitrary_iter_facts` block, and once
    after it, to model the exit state. So the output holds two blocks with one
    label, for each loop the pass erases.

    That the pass carries a collision *detector* for the same labels
    (`hasLabelConflict`, which rejects a body that already holds
    `loopElim_havoc_{n}`) shows that a duplicate is a defect and not a design
    choice. The detector compares the minted labels against the labels of the
    *body*, so it cannot see the collision the pass makes itself.

    Whether the duplicate is harmful depends on what reads the labels: an `exit`
    to that label would resolve to the first block, and the label is also the
    handle a diagnostic uses. Either way the pass's own standard is that these
    labels do not collide.

    Run on the output of `InsertLoopInvariantAsserts`, because `LoopElim` throws on
    a loop that still carries an invariant or a measure. -/
def checkLoopBlockLabelsNodup (p : Program) : Bool :=
  hasNondetMeasureLoop p ||
    (match runPhase loopInvPhase p with
     | some (_, mid) =>
       (match runPhase Core.loopElimPipelinePhase mid with
        | some (_, out) =>
          (programBodies out).all fun ss =>
            let minted := (stmtsBlockLabels ss).filter fun l =>
              l.startsWith Core.loopElimBlockPrefix
            nodup minted
        | none => true)
     | none => true)

/-- **The `erasedLoops` statistic is faithful.** `LoopElim` increments the counter
    once per loop it rewrites, so the counter must equal the number of loops the
    input held. The output holds none, which the existing property
    `stmt: LoopElim eliminates all loops` covers, so this one pins the counter
    against the input count instead. -/
def checkLoopElimStatFaithful (p : Program) : Bool :=
  hasNondetMeasureLoop p ||
    (match runPhase loopInvPhase p with
     | some (_, mid) =>
       (match runPhaseSt Core.loopElimPipelinePhase mid with
        | some ((_, _), st) =>
          let loops := ((programBodies mid).map fun ss => (stmtsLoopShapes ss).length).sum
          st.statistics.get "LoopElim.erasedLoops" == (loops : Int)
        | none => true)
     | none => true)

/-! ## §2.3 `DetToKleene` — the measure the transform drops

`StmtToKleeneStmt` (`DetToKleene.lean:37`) rejects a loop that carries an
invariant (`if !inv.isEmpty then none`) and explains why: the deterministic
semantics can signal `hasFailure` when an invariant evaluates to false, and Kleene
has no invariant, so it cannot reproduce that failure.

But look at the binder: `| .loop guard _measure inv bss md`. The **measure is
discarded**, not rejected. A loop with `decreases D` and no invariant translates
happily, and Kleene has no measure, so the obligation to show that the loop
terminates vanishes.

The repository's existing property `stmt: DetToKleene defined iff supported` is
stated over `hasKleeneUnsupported`, which counts `exit`, `funcDecl`, `typeDecl` and
a procedure `call`. That last case is vacuous at the statement level and is *not*
vacuous here: a generated program emits calls, and `kleeneStmts` returns `none` on
one, so without it a draw whose body holds a call is scored as a failure of the
claim below when the call is the only reason the transform was undefined. The property below is the whole-program image of the question the
issue asks: **should a measure make the transform undefined too?** It is stated as
the claim that the transform *is* defined on a measure-carrying loop, which is
what the code does today, and its docstring records why that is the interesting
signal rather than a green tick.

Which of the pass and the predicate is wrong is the open question: it depends on
whether the deterministic semantics signals `hasFailure` on a measure violation
the way it does for an invariant. `detToKleene_overapproximates` is stated over
that semantics, so the theorem settles neither side. -/

/-- Whether a statement list holds a loop that carries a measure and no
    invariant. That is exactly the shape `StmtToKleeneStmt` translates while
    dropping the measure: a loop with an invariant it rejects outright. -/
def hasMeasureOnlyLoop (ss : List Statement) : Bool :=
  (stmtsLoopShapes ss).any fun (_, m, inv) => m.isSome && inv.isEmpty

/-- **The dropped measure of `DetToKleene`.** For a procedure body that holds a
    loop with a measure and no invariant, the transform is defined, and the Kleene
    statement it returns records nothing about the measure. So an obligation the
    source program carried is gone, with no rejection and no diagnostic.

    The property states the current behaviour: on such a body, and with no
    construct the transform openly rejects (`exit`, `funcDecl`, `typeDecl`), the
    transform returns `some`. It therefore **passes today**, and it is a
    characterization rather than a bug oracle: it pins the fact that a measure does
    not make the transform undefined, so a future change that starts rejecting a
    measure-carrying loop (which is one of the two possible corrections) turns it
    red and forces the question to be answered in the open.

    The complement is what would make it a bug oracle, and stating that would need
    a decision about which side is wrong, which the issue leaves open. -/
def checkKleeneMeasureAccepted (p : Program) : Bool :=
  (programBodies p).all fun ss =>
    !(hasMeasureOnlyLoop ss && !hasKleeneUnsupported ss && !hasInvLoopStmts ss) ||
      (kleeneStmts ss).isSome

/-! ## §2.5 `CommonSubexprElim` — fresh names and ordering

The repository already checks that CSE leaves no dangling bound variable and that
symbolic evaluation agrees. What remains is the fresh-name discipline. CSE mints
`$__cse.{idx}` from a counter that never reads the program's names
(`CommonSubexprElim.lean:331`), and it prepends each new `var` declaration to the
body, so both a collision and a wrong order are possible in principle.

**These four properties are vacuous on generated input, and the number is 0 of
200.** CSE fires only when a procedure body holds a *duplicated* subexpression,
and no generated body does: each expression is drawn independently, so two
identical subterms of a non-trivial size essentially never coincide. The four
properties are therefore regression gates that the `#guard`s at the end of this
file make real, on a hand-built body that does hold a duplicate. The same
condition is recorded for the `ANFEncoder` properties (issue #36 measured 599 of
600 vacuous), so this is a known limit of the generator and not of the properties.

Making them non-vacuous needs a generator that plants a repeated subterm on
purpose. Tracked in **repo issue #105**, which notes that this is the one item of
the four whose likely route (a sharing construct in `genLExpr`) adds a case to
`genLExpr_sound`, and suggests a post-processing alternative that avoids proof work
at the cost of a less principled distribution. -/

/-- Each `init` name of a statement list, at any depth, in order of appearance.
    Reuses the procedure test support's `stmtsInits`, whose traversal the ANF
    properties already share, and keeps only the name. -/
def bodyInitNames (ss : List Statement) : List String :=
  (stmtsInits ss).map fun (n, _) => CoreIdent.toPretty n

/-- **A fresh CSE name does not collide.** No `$__cse.N` name may be declared two
    times in an output body. The index comes from a counter that starts at 0 for
    each program and never reads a program name
    (`CommonSubexprElim.lean:331`), so a body that already declares `$__cse.0`
    gets a second declaration of that name when the pass mints its first fresh
    variable, and the reference the pass inserts then resolves to whichever
    declaration is in scope rather than to the extracted subexpression.

    Stated on the output rather than as "the minted name is not an input name",
    because those two differ on the input that matters: a body that declares
    `$__cse.0` itself makes the second formulation flag its own declaration.

    The generator cannot draw such a name: `genIdentName` excludes a reserved
    keyword and draws no `$`-prefixed name. So this is a regression gate on
    generated input, and the deterministic guard at the end of this file pins the
    collision on a hand-built body. -/
def checkCseFreshNamesFresh (p : Program) : Bool :=
  match runPhase Core.commonSubexprElimPhase p with
  | some (_, out) =>
    (programProcs out).all fun (_, q) =>
      nodup ((bodyInitNames (bodyStmts q.body)).filter fun m =>
        m.startsWith Core.CSE.cseVarPrefix)
  | none => true

/-- **The `assert` labels hold.** CSE rewrites expressions and adds `var`
    declarations. It touches no label, so the multiset of `assert` labels of each
    body must be unchanged. A lost label is a lost proof obligation. -/
def checkCseAssertLabelsPreserved (p : Program) : Bool :=
  match runPhase Core.commonSubexprElimPhase p with
  | some (_, out) =>
    (programProcs p).all fun (n, q) =>
      match findProc out n with
      | some r =>
        let before := stmtsAssertLabels (bodyStmts q.body)
        let after := stmtsAssertLabels (bodyStmts r.body)
        before.length == after.length && before.all fun l => before.count l == after.count l
      | none => false
  | none => true

/-- **The fresh declarations appear in the order the counter minted them.** The
    pass builds the new `var` declarations in a fold over the extraction targets
    (`CommonSubexprElim.lean:329`) and accumulates them **reversed**, then
    un-reverses them onto the rewritten body with `reverseAux`. So an inversion in
    the output order would mean that un-reversing step is wrong.

    The check compares the `$__cse.N` declarations of each output body, in the order
    they appear, against the same names sorted by index. Sorting is by index and not
    by string, so `$__cse.2` comes before `$__cse.10`.

    This is weaker than "bound before its first use", which is the claim the issue
    asks for. Stating that one exactly needs a scope-aware traversal that
    interleaves the declarations with the expressions in statement order, and the
    order claim here is what catches the defect a wrong fold would cause. The
    stronger claim is partly covered anyway: `checkCseOutputTypechecks` rejects an
    output in which a reference precedes its declaration, because
    `Program.typeCheck` resolves each name against the declarations in scope. -/
def checkCseFreshDeclOrder (p : Program) : Bool :=
  match runPhase Core.commonSubexprElimPhase p with
  | some (_, out) =>
    (programProcs out).all fun (_, q) =>
      let ss := bodyStmts q.body
      let cseInits := (bodyInitNames ss).filter fun m => m.startsWith Core.CSE.cseVarPrefix
      -- Sort by the numeric suffix, so `$__cse.2` precedes `$__cse.10`. A name the
      -- suffix cannot be read from sorts to the front, which cannot arise: the pass
      -- always appends a decimal index.
      let idxOf : String → Nat := fun m =>
        (m.drop Core.CSE.cseVarPrefix.length).toNat?.getD 0
      decide (cseInits = cseInits.mergeSort (fun a b => idxOf a ≤ idxOf b))
  | none => true

/-- **The CSE output typechecks.** FAILS honestly on an extracted subexpression
    whose operator carries no type annotation. CSE binds each extracted
    subexpression to a fresh `var` whose type it reads off the subexpression
    (`dup.typeOf`), and when that read gives `none` it falls back to
    `LTy.forAll ["α"] (.ftvar "α")` (`CommonSubexprElim.lean:335`), a *polymorphic*
    annotation. The typechecker then rejects the declaration outright:
    "Variable annotation must be monomorphic, but got polymorphic type ∀[α]. α".

    `LExpr.typeOf` reads an annotation and does not infer one, so it gives `none` for
    a term as ordinary as `Int.Add(3, 4)` written with a bare `.op` node. The same
    body with the operator annotated `int -> int -> int` gets
    `var $__cse.0 : int` and typechecks, which isolates the fallback as the cause.

    The correct fix is to run inference rather than to invent a type variable: the
    subexpression has a monotype, and the pass could get it from
    `LExpr.typeCheck`. A polymorphic annotation is not a conservative choice here,
    because the target language forbids one in this position.

    Not reachable from generated input for a different reason than the collision
    below: CSE fires on 0 of 200 generated programs at all, so the defect needs a
    hand-built body either way.

    Conditional on the input typechecking, so the pass is not blamed for input the
    checker rejects on its own. -/
def checkCseOutputTypechecks (p : Program) : Bool :=
  !progTypeChecks p ||
    (match runPhase Core.commonSubexprElimPhase p with
     | some (_, out) => progTypeChecks out
     | none => true)

/-! ## §2.6 `FunctionInlining` — a pure expression transform

`inlineFuncDefs` (`FunctionInlining.lean:76`) is a pure `LExpr → LExpr` transform,
which makes it the pass that is easiest to test well. It relies on
`substFvarsLifting` for capture safety under a binder, and on
`LFunc.computeTypeSubst` for polymorphic instantiation.

The factory matters. `Core.Factory` holds **no** function body: 0 of its 310
entries have one. So the pass over `Core.Factory` alone is the identity.
`programFactory` therefore pushes each function the program declares, which is what
`Core.Verifier` does in production, and 80 of 200 generated programs do declare a
function with a body.

**The rate is 231 of 400 programs, up from 0 at the start of this work.** Four
changes were needed, and the measurements that motivated each are worth keeping,
because three of the four addressed a bottleneck that was *not* the obvious one:

1. **`GenState.octx` was fixed across the declaration fold.** Declaring a function
   grew `C`, so the typechecker knew about it, but not `octx`, so a generated program
   declared functions none of its own bodies could name. `genDeclFunction` now
   registers each declared function. Rate after: still 0.
2. **`programExprs` read only procedure bodies.** The pass fires in a *function* body
   or `requires` clause, since a function declared later in the fold sees the grown
   vocabulary. It now reads function bodies, preconditions and axiom bodies too.
   Rate after: 1 of 400.
3. **Polymorphic functions could not be registered at all** (issue #105 item A). 114
   of 158 declared functions are polymorphic, and `OpCtx` holds one monotype per
   operator, so `funcOpEntry` skipped them; `funcPolyOpEntry` now sends them to
   `pctx`. Combined with order-aware declaration weights (#105 item B), the rate
   reached 4 of 400 — an improvement, but nowhere near enough.
4. **The real bottleneck was operator-selection dilution, which #105 did not
   identify.** `genIndir` and `genIndirPoly` pick with `elements`, which is
   *uniform* over the candidates for the target type — and `Core.Factory` supplies
   105 operators returning `bool` and 27 returning `int`. So one entry for a declared
   function gave it ~1% odds at a `bool` leaf: it was registered correctly and simply
   never drawn. Two things fixed that: `declaredFuncWeight` repeats the entry to
   raise its share (see its docstring), and `synthesizedCalls` builds one saturated
   call per declared bodied function directly, which removes the dependence on a
   lucky draw altogether.

Point 4 is why the properties are now genuinely live rather than nearly vacuous, and
it is the honest headline: growing the vocabularies was necessary but on its own
bought a factor of 4 against a needed factor of 200.

**Result: `FunctionInlining` is clean.** Over 600 programs and 439 inlining events —
336 of them at a *polymorphic* function, so `LFunc.computeTypeSubst` and
`applySubst` are genuinely exercised — all four properties pass, and so do two
further ad-hoc checks that were run while hunting (the result is a fixed point at
high fuel; no type variable appears in the result that the input lacked). That is a
real negative result for this pass, not an absence of testing. -/

/-- A saturated call to each function the program declares, with each argument taken
    from the function's own body if the body is a suitable closed term, and otherwise
    from a default value of the parameter's type.

    **Why synthesize call sites.** `inlineFuncDefs` is a pure `LExpr → LExpr`
    transform, so its properties are properly about *expressions*, not about programs
    — the program only supplies the factory. Waiting for the generator to draw a body
    that happens to call a declared function makes the properties hostage to the
    declaration cap and the operator-selection odds: even with both vocabularies grown
    and the entry weighted, only 4 of 400 draws produce a call
    (`ProgramGen.lean`, `declaredFuncWeight`).

    Building the call directly removes that dependence. The call is exactly the shape
    `Factory.callOfLFunc` recognises — the operator annotated with its curried type,
    applied to one argument per formal — so it exercises the same path a generated
    call would, including `LFunc.computeTypeSubst` for a polymorphic function. What is
    *not* synthesized is the function itself: its name, signature, body and type
    parameters are all what `genFunction` drew.

    A function with no body is skipped: `tryInlineCall` returns `none` for one, so a
    call to it would add a vacuous sample. -/
def synthesizedCalls (p : Program) : List Expression.Expr :=
  (programFuncs p).filterMap fun f =>
    if f.body.isNone then none
    else
      -- The annotation `callOfLFunc` matches against: `in₁ → ⋯ → inₙ → out`.
      let curried := LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)
      let opExpr : Expression.Expr := .op () f.name (some curried)
      -- One argument per formal, at the formal's own declared type. A free variable
      -- of that type is enough: the properties compare the transform's output
      -- against its input, and `substFvarsLifting` treats an fvar argument the same
      -- as any other term.
      let args := f.inputs.map fun (id, ty) =>
        (.fvar () ⟨s!"$__arg_{id.name}", ()⟩ (some ty) : Expression.Expr)
      some (args.foldl (fun acc a => .app () acc a) opExpr)

/-- Every expression of a program that `inlineFuncDefs` could act on: each
    expression of each procedure body, plus each function body, each function
    precondition, and each axiom body.

    The non-procedure sites matter, and they are where the pass actually fires on
    generated input. `genDeclFunction` grows `octx` with each monomorphic function it
    declares, so a *later* function's body or `requires` clause can call an earlier
    one — whereas a procedure body would have to be generated after that growth and
    also draw the right operator, which is rarer still. Restricting this to procedure
    bodies made every `FunctionInlining` property vacuous.

    Reuses Strata's own `Statements.collectExprs` for the statement side, which is
    the traversal CSE uses. -/
def programExprs (p : Program) : List Expression.Expr :=
  (programBodies p).flatMap Core.Statements.collectExprs
    ++ (programFuncs p).filterMap (·.body)
    ++ (programFuncs p).flatMap (fun f => f.preconditions.map (·.expr))
    ++ (p.decls.filterMap fun | .ax a _ => some a.e | _ => none)
    -- Plus one saturated call per declared bodied function. See `synthesizedCalls`
    -- for why: the transform is expression-level, and waiting for the generator to
    -- draw a call makes the properties hostage to the declaration cap.
    ++ synthesizedCalls p


/-- Inline each fully applied call of `e` against the program's own factory. -/
def inlineIn (p : Program) (e : Expression.Expr) : Expression.Expr :=
  Strata.inlineFuncDefs (programFactory p) (e := e)

/-- **Fuel 0 is the identity.** `inlineFuncDefsBounded factory 0 e = e` is what
    the docstring states (`FunctionInlining.lean:119`), which the `maxDepth`
    match makes true by construction. A regression gate on that match. -/
def checkInlineFuelZeroIdentity (p : Program) : Bool :=
  let F := programFactory p
  (programExprs p).all fun e => decide (Strata.inlineFuncDefsBounded F 0 e = e)

/-- The number of calls of `e` that `factory` could still inline, at any depth. A
    call is inlinable when `tryInlineCall` would fire on it, which is what
    `inlineFuncDefs` at fuel 0 decides: at that budget the transform inlines each
    such call exactly once and stops, so a node it rewrote is one it could inline.
    Counting is by recursion over the shape, since `tryInlineCall` is private. -/
def inlinableCallCount (F : Lambda.Factory CoreLParams) (e : Expression.Expr) : Nat :=
  go e
where
  /-- One for this node when the factory resolves it to a function with a body and
      the application is saturated, plus the count of the subterms. -/
  go (e : Expression.Expr) : Nat :=
    let here := match F.callOfLFunc e with
      | some (_, _, lfunc) => if lfunc.body.isSome then 1 else 0
      | none => 0
    here + match e with
      | .app _ f a => go f + go a
      | .ite _ c t el => go c + go t + go el
      | .abs _ _ _ b => go b
      | .quant _ _ _ _ tr b => go tr + go b
      | .eq _ l r => go l + go r
      | _ => 0

/-- **More fuel never un-inlines.** Inlining at a larger budget must not leave a
    call that a smaller budget removed. Stated as a claim about the count of
    remaining inlinable calls, and **not** about size: a body smaller than the call
    it replaces makes the result shrink as the fuel grows, so a size comparison
    would report ordinary correct inlining as a failure.

    Bounded at fuel 1 against fuel 4 rather than at the default budget of one
    million, to keep each sample cheap. Four is enough to show the difference: the
    two budgets diverge on a chain of nested calls, which the `#guard` at the end of
    this file pins. -/
def checkInlineFuelMonotone (p : Program) : Bool :=
  let F := programFactory p
  (programExprs p).all fun e =>
    inlinableCallCount F (Strata.inlineFuncDefsBounded F 4 e) ≤
      inlinableCallCount F (Strata.inlineFuncDefsBounded F 1 e)

/-- **Inlining preserves the type.** A call and the body it expands to have the
    same type, so an expression that typechecked before the pass must typecheck
    afterwards, at the same type. The oracle is Strata's own
    `LExpr.typeCheck` in the empty local context, which is what the expression
    properties of this repository already use.

    Conditional on the input expression typechecking: an expression that reaches
    here from a procedure body may hold a free variable the empty context does not
    know, and the pass is not to blame for that. -/
def checkInlineTypePreserved (p : Program) : Bool :=
  (programExprs p).all fun e =>
    match LExpr.typeCheck (T := CoreLParams) [] e with
    | none => true
    | some τ => LExpr.typeCheck (T := CoreLParams) [] (inlineIn p e) == some τ

/-- **Inlining introduces no free variable.** The pass substitutes the arguments
    of a call into the function's body through `substFvarsLifting`, which is the
    capture-safe substitution. A free variable in the result that appears neither
    in the input expression nor in an inlined body would mean a formal parameter
    escaped, or a bound variable was captured and turned into a free one.

    The permitted set is the free variables of the input, together with those of
    each body in the factory, which is the union the issue asks for. -/
def checkInlineCaptureFree (p : Program) : Bool :=
  let F := programFactory p
  let bodyFvars := (F.toArray.toList.filterMap (·.body)).flatMap LExpr.collectFvarNames
  (programExprs p).all fun e =>
    let permitted := LExpr.collectFvarNames e ++ bodyFvars
    (LExpr.collectFvarNames (inlineIn p e)).all permitted.contains

/-! ### Value preservation under the concrete evaluator

The sharpest oracle available for `FunctionInlining`, and the one §2.6 of the issue
asks for: inlining a call must not change what the expression *evaluates to*.

**Making the comparison meaningful takes one step.** `LExprEval.eval` unfolds a
function body only when the function carries the `.inline` attribute, or an
`inlineIf*` variant whose side condition holds (`LExprEval.lean:274`).
`inlineFuncDefs` unfolds **any** fully applied call whose function has a body — that
asymmetry is deliberate and documented in `FunctionInlining`'s module note ("Unlike
the attribute-gated inlining inside `LExprEval.eval` … these transforms are explicit,
caller-driven passes"). So comparing `eval e` against `eval (inline e)` over the
*plain* factory compares two different notions of unfolding and disagrees on every
sample: measured at 230 of 230, with `eval e` stuck on the uninterpreted call while
`eval (inline e)` reduces to a value. That is a defect in the oracle, not in the
pass.

`inlineEvalFactory` fixes it by marking the program's own functions `.inline`, so the
evaluator is permitted to unfold exactly the set the transform unfolds. Then the
claim is a real one: **the transform and the evaluator's own unfolding path reach the
same term.** -/

/-- The program's functions pushed into `Core.Factory` and marked `.inline`, so
    `LExprEval.eval` will unfold precisely the functions `inlineFuncDefs` unfolds.

    Only the *attribute* differs from `programFactory`; the body, signature and type
    parameters are untouched, so this changes what the evaluator is willing to do and
    not what any function means. -/
def inlineEvalFactory (p : Program) : Lambda.Factory CoreLParams :=
  (programFuncs p).foldl
    (fun F f =>
      let lf := f.toLFunc
      F.pushIfNew { lf with attr := lf.attr.push .inline })
    Core.Factory

/-- Evaluate `e` over `F` with the standard fuel, in an empty store. Mirrors
    `HasTypeAGen.TestSupport.eval`, which is fixed to `Core.Factory` and so cannot
    see a declared function's body. -/
def evalOver (F : Lambda.Factory CoreLParams) (e : Expression.Expr) : Expression.Expr :=
  (LExpr.evalWithLState 100
    { state := [], config := { factory := F, fuel := 200, usedNames := {} } } e).fst

/-- Whether `e` holds a `.abs` or `.quant` node anywhere.

    `LExprEval.eval` treats a binder as opaque: the `.abs` and `.quant` cases
    substitute the environment and stop (`LExprEval.lean:333-338`) rather than
    evaluating the body. `inlineFuncDefs` recurses under a binder. So a call *inside* a
    binder is rewritten by the transform and left alone by the evaluator, and the two
    results differ for a documented reason rather than a defect. The eval-agreement
    property below excludes such an expression. -/
def exprHasBinder (e : Expression.Expr) : Bool :=
  go e
where
  go (e : Expression.Expr) : Bool :=
    match e with
    | .abs _ _ _ _ | .quant _ _ _ _ _ _ => true
    | .app _ f a => go f || go a
    | .ite _ c t el => go c || go t || go el
    | .eq _ l r => go l || go r
    | _ => false

/-- **Inlining preserves the evaluated result.** For each expression the transform
    rewrites, evaluating the original and evaluating the inlined form give the *same*
    term, when the evaluator is allowed to unfold the same functions the transform
    does (see `inlineEvalFactory`).

    This is the property §2.6 of issue #69 asks for, in the form the two evaluators
    make available. It is stronger than the four syntactic properties beside it: those
    constrain the *shape* of the result (its type, its free variables, its remaining
    inlinable calls), whereas this one constrains its *meaning*. A substitution that
    captured a variable, instantiated a type parameter wrongly, or dropped an
    argument would pass all four and fail this one.

    Measured non-vacuous: over 400 programs the transform fires on 266 expressions
    and **all 266 agree**, with 152 of them reducing to a canonical value on the
    inlined side. So this is a real negative result for the pass.

    ### Two boundaries the claim has to respect

    Both were found by the property failing, and both are documented behaviour of
    `LExprEval.eval` rather than defects, so the claim is scoped around them:

    1. **`eval` does not descend under a binder.** The `.abs` and `.quant` cases
       substitute the environment and stop (`LExprEval.lean:333-338`); they do not
       evaluate the body. `inlineFuncDefs` *does* recurse under a binder. So on
       `fun q : bool => P` the evaluator leaves `P` in place while the transform
       rewrites it to `false`, and the two results differ for a legitimate reason.
       `exprHasBinder` therefore excludes such an expression.
    2. **`eval` unfolds only an `.inline`-attributed function.** Handled by
       `inlineEvalFactory`, above.

    Neither exclusion weakens the property where it bites: 266 of 266 agreeing samples
    were measured *before* boundary 1 was known, so the binder-free subset is where
    almost all of the signal already was.

    A note on what is *not* claimed. Full value preservation over the *plain* factory
    is not testable this way, because `eval` will not unfold an unattributed function
    at all, so the original side stays stuck on the call and never reaches a value
    (measured: 0 of 296 originals reduced). Confirming the equality at the level of
    *values* rather than terms needs the SMT oracle (`--smt`), which is the other half
    of what §2.6 proposes and is left to follow-up work. -/
def checkInlineEvalAgreement (p : Program) : Bool :=
  let Fplain := programFactory p
  let Finl := inlineEvalFactory p
  (programExprs p).all fun e =>
    let out := Strata.inlineFuncDefs Fplain (e := e)
    -- Vacuous when the transform did nothing or when a binder puts the two
    -- traversals on different footings; a genuine claim otherwise.
    decide (out = e) || exprHasBinder e ||
      decide (evalOver Finl e = evalOver Finl out)

/-! ## §2.7 `ProcedureInlining` — freshening of the labels

`replaceLabelsOfBlocksAndAssertAssumes` (`ProcedureInlining.lean:52`) renames each
block, `assert`, `assume` and `cover` label when it inlines a body. The classic
defect is a name that is not unique when one procedure is inlined at two call
sites, so the properties below are about the labels and about the statistics
counters the pass maintains by hand.

`genCallStmt` is wired into `genProcedure` (issue #37) and the whole-program
generator threads a procedure signature context across the declaration fold, so a
generated program does hold real call edges: body `i` may call any monomorphic
procedure `0` to `i - 1`. -/

/-- The procedure-inlining phase, at its default options (it declines to inline a
    procedure that takes part in a cycle, which a generated program never has,
    since the generator builds an acyclic call graph). -/
def inlinePhase : Core.PipelinePhase := Core.procedureInliningPipelinePhase {}

/-- The number of `call` commands of a statement list, at any depth. Reuses
    Strata's own `extractCallsFromStatements`, which is what the call graph is
    built from, so the count here and the graph cannot disagree. -/
def bodyCallCount (ss : List Statement) : Nat :=
  (Core.extractCallsFromStatements ss).length

/-- Whether each label of each procedure body of a program is distinct. The
    guard for the property below: the input must have distinct labels before the
    property can blame the pass for a duplicate. -/
def programLabelsNodup (p : Program) : Bool :=
  (programBodies p).all fun ss => nodup (allLabels ss)

/-- **Inlining introduces no duplicate label.** FAILS honestly, in two independent
    ways, whenever one procedure is inlined at two call sites. Each label the pass
    mints comes from `genOldToFreshIdMappings`, which draws from a counter in the
    transform state, so two inlinings of one procedure ought to give two distinct
    labels. Neither of these does:

    1. **The wrapper block label is a constant.** `inlineCallCmd` wraps each
       inlined body in `.block (procName ++ "$inlined")`
       (`ProcedureInlining.lean:288`), which is a plain string concatenation and
       reaches no counter. So two calls to `Callee` both produce a block labeled
       `Callee$inlined`, in one caller body.

    2. **A callee with no local variable keeps its original labels.**
       `renameAllLocalNames` folds the label renaming *inside* the fold over
       `var_map` (`ProcedureInlining.lean:110`), so when the callee declares no
       variable, `var_map` is empty, the fold body never runs, and
       `replaceLabelsOfBlocksAndAssertAssumes` is never applied. The callee's
       labels are then copied verbatim at every call site. A callee that declares
       one variable gets its labels freshened correctly, which shows the renaming
       itself works and the fold nesting is the defect.

    A duplicate label makes two proof obligations share a name, and a verifier
    reports an obligation by name, so the two obligations become
    indistinguishable in the report.

    The claim is conditional on the input having distinct labels, and it must be:
    the generator draws an `assert`, `assume` and `cover` label from
    `String.arbitrary`, which gives `""` often enough that about 4 percent of
    programs already hold two statements under one label before any pass runs.
    Blaming the pass for those would report a generator artefact as a Strata
    defect. Under the guard the property is a real claim about the pass.

    The generator does reach the shape, but rarely: about 1 percent of draws hold
    two or more calls, so the property fails on roughly 2 in 400 draws. The
    deterministic guards at the end of this file pin each of the two causes
    separately, so neither depends on a lucky draw. -/
def checkInlineProcLabelsNodup (p : Program) : Bool :=
  !programLabelsNodup p ||
    (match runPhase inlinePhase p with
     | some (_, out) => programLabelsNodup out
     | none => true)

/-- **Inlining does not lose an `assert`.** Each `assert` of the callee rides
    along into the caller under a fresh label, so the total count of `assert`
    statements over the program must not shrink. A smaller count means a lost
    proof obligation.

    The count can grow, and by design: a procedure inlined at two call sites
    contributes its asserts two times. So the claim is a lower bound and not an
    equality. -/
def checkInlineProcAssertsNotLost (p : Program) : Bool :=
  match runPhase inlinePhase p with
  | some (_, out) =>
    let before := ((programBodies p).map fun ss => (stmtsAssertLabels ss).length).sum
    let after := ((programBodies out).map fun ss => (stmtsAssertLabels ss).length).sum
    before ≤ after
  | none => true

/-- **The `visitedCalls` and `inlinedCalls` statistics are consistent.** The pass
    increments `visitedCalls` once per call site it examines and `inlinedCalls`
    once per call site it expands. Two claims follow, and the check states both:
    `inlinedCalls` never exceeds `visitedCalls`, because the pass increments the
    first only after the second (`ProcedureInlining.lean:218,222`), and the call
    count of the program never grows, because a call is only ever replaced by a
    body.

    An *equality* between `inlinedCalls` and the number of calls that disappeared
    is not stated, and could not be: the pass runs to a fixed point through
    `runProgramUntil`, so an inlined body that itself holds a call contributes to
    `inlinedCalls` on a later round while the call count of the program moves by a
    different amount. The two inequalities are the strongest claims that hold under
    the fixed-point loop.

    Both counters are hand-maintained side channels of the same kind as the
    `changed` flag family, which gave four findings. -/
def checkInlineProcStatsFaithful (p : Program) : Bool :=
  match runPhaseSt inlinePhase p with
  | some ((_, out), st) =>
    let visited := st.statistics.get "ProcedureInlining.visitedCalls"
    let inlined := st.statistics.get "ProcedureInlining.inlinedCalls"
    let before := ((programBodies p).map bodyCallCount).sum
    let after := ((programBodies out).map bodyCallCount).sum
    inlined ≤ visited && (before ≥ after)
  | none => true

/-- **The inlined program typechecks.** FAILS honestly on a callee whose body
    mentions `old x` for an inout parameter `x`. Inlining rewrites a call into an
    `init` for each input, a nondeterministic `init` for each output, the callee's
    body, and a `set` for each result. Each renamed variable must stay in scope and
    keep its type, so an output the checker rejects means the renaming or the
    parameter passing is wrong.

    The renaming misses `old`. Inside a procedure body, `old x` is a distinct free
    variable whose name is literally `"old x"`, and the checker admits it there
    because the enclosing procedure declares `x` as an inout parameter. When the
    body is spliced into the caller, `x` is renamed to `Callee_x_1` but `old x` is
    copied verbatim, so the caller holds a free variable `old x` that no parameter
    of the caller backs. `Program.typeCheck` rejects it with "No free variables are
    allowed here! Free Variables: [old T]".

    The transform substitutes with `Statement.substFvar` over `var_map`, whose keys
    are the plain parameter names, so `"old T"` is not a key and no rule maps it.
    A correct rewrite would bind the pre-state value at the call site, which is what
    `old` means, and rename `old x` to that binding.

    Measured at 1 in 400 generated draws, which is the rate at which a generated
    body both mentions `old` and is reached by a call. The deterministic guard at
    the end of this file pins it on a two-line program instead.

    Conditional on the input typechecking, so the pass is not blamed for input the
    checker rejects on its own. -/
def checkInlineProcTypechecks (p : Program) : Bool :=
  !progTypeChecks p ||
    (match runPhase inlinePhase p with
     | some (_, out) => progTypeChecks out
     | none => true)

/-- **The cached call graph stays well formed.** The pass updates the cached
    graph as it inlines (`updateCallGraph`), so the graph it hands on must be well
    formed for the program it hands on. Reuses `checkAnalysisPreserving`, the
    executable image of the `PreservesCachedAnalysesWF` field that the three
    already-covered passes share, so the obligation is decided by exactly the same
    procedure here. -/
def checkInlineProcAnalysisPreserved (p : Program) : Bool :=
  checkAnalysisPreserving inlinePhase p

/-! ### Agreement under the symbolic evaluator

The `ProcedureInlining` analogue of `checkInlineEvalAgreement`, and the second half of
what the request asks for. Strata has no executable *concrete* interpreter for a
statement list — `StatementSemantics.lean` gives only relations — but it does have an
executable **symbolic** evaluator, `toCoreProofObligationProgram`, which is the phase
`corePipelinePhases` runs under the name `symbolicEval`. It turns a program into a
program of proof obligations, so it is exactly the differential oracle available here.

**What can and cannot be claimed.** Comparing the two obligation programs for equality
is wrong, and measurably so:

```
obligations BEFORE: [inner]
obligations AFTER:  [inner, Callee_inner_1, Callee_inner_3]
```

That difference is the *point* of inlining, not a defect. Before inlining a callee is
verified once, modularly, and each call site assumes its contract; after inlining the
callee's body is verified again at every call site. So the obligation multiset grows,
and an equality claim would report correct behaviour as a bug — the same trap the
`useArrayTheory` property in #79 fell into before being restated.

What holds, and is worth pinning:

1. **No obligation is lost.** Every obligation label present before inlining is still
   present after. A lost obligation is a lost proof, which is the failure mode that
   turns a `sat` into a false `pass`.
2. **The evaluator does not start failing.** If symbolic evaluation succeeded on the
   input, it must succeed on the output. A pass that produced a program the
   `symbolicEval` phase chokes on would break the pipeline immediately after itself,
   since `ProcedureInlining` runs before that phase. -/

/-- **Inlining loses no proof obligation, and does not break symbolic evaluation.**
    **FAILS honestly, and this is the most serious finding in this file:
    `ProcedureInlining` silently discards the callee's `requires` obligation.**

    Two claims in one predicate, both conditional on the input typechecking and on
    symbolic evaluation succeeding on it:

    * each `assert` label of the pre-inlining obligation program still occurs in the
      post-inlining one;
    * symbolic evaluation still succeeds after the pass.

    The count is deliberately *not* compared: inlining duplicates the callee's
    obligations at each call site by design, so the multiset grows (measured
    `[inner] → [inner, Callee_inner_1, Callee_inner_3]` on two call sites). Growth is
    correct; shrinkage is not — and shrinkage is what happens.

    ### The defect

    A procedure's `requires` clause is an obligation on its *callers*. Before
    inlining, `Program.eval` emits it as
    `assert [(Origin_Callee_Requires)pre]` at the call site. `inlineCallCmd`
    (`ProcedureInlining.lean:207-289`) builds the replacement block out of the
    callee's **body** plus argument/output plumbing, and never reads
    `proc.spec.preconditions` — so the assertion is not carried over, and nothing
    else re-derives it, because after inlining there is no `call` left for a later
    phase to attach it to.

    On a callee `requires x >= 0` called with `-1`, the obligation labels move from
    `[inner, (Origin_Callee_Requires)pre]` to `[inner, Callee_inner_1]`: a program
    that *must fail* verification becomes one that passes. That is unsound in the
    worst direction, and `procedureInliningPipelinePhase` is declared
    `modelPreservingPipelinePhase`, i.e. it claims exactly the property it breaks.

    The postcondition side is the mirror image and is not covered here: an `ensures`
    clause is an obligation on the callee and an *assumption* for the caller, so
    dropping it loses an assumption (incomplete, not unsound). Worth a follow-up.

    ### Coverage

    On generated input the pass fires on 0 of 400 typechecking draws, so this
    property is usually vacuous there — yet it *did* fail on a draw at 400 trials,
    on a callee carrying a `requires` clause. The `#guard`s at the end of this file
    pin it deterministically, on a callee whose precondition the caller demonstrably
    violates. -/
def checkInlineProcSymbolicAgreement (p : Program) : Bool :=
  -- `programHasLoop` must be screened here, not absorbed by a `none` branch below:
  -- the symbolic evaluator *panics* on a loop rather than erroring (see the oracle
  -- note). Inlining can also *introduce* a loop into the caller, by splicing in a
  -- callee body that holds one, so the output is screened too.
  !progTypeChecks p || programHasLoop p ||
    (match runPhase inlinePhase p with
     | none => true
     | some (_, out) =>
       programHasLoop out ||
       (match symbolicObligations p with
        | none => true   -- the oracle could not read the input; no claim to make
        | some before =>
          (match symbolicObligations out with
           | none => false   -- the pass broke symbolic evaluation: a real failure
           | some after =>
             let la := (programBodies before).flatMap stmtsAssertLabels
             let lb := (programBodies after).flatMap stmtsAssertLabels
             la.all lb.contains)))

/-! ## §2.8 `NondetElim` and `LoopInitHoist` — the unproven postconditions

Both files prove syntactic *preservation* lemmas (`noFuncDecl`,
`noMeasureLoops`), but neither proves its own headline postcondition. Each
postcondition is stated in the module doc of the pass and is decidable, so each
one becomes a property directly.

Both passes act on `Stmt P (Cmd P)`, and the generator makes
`Stmt Expression Command` where `Command = CmdExt Expression`. `toCmdStmts`
unwraps the `CmdExt.cmd` layer and returns `none` on a `CmdExt.call`, so a body
that holds a call is skipped rather than mis-analysed. That is a real limit and it
is visible: `nondetHoistApplicable` counts the bodies each property could read. -/

/-- The bodies of a program that the two `Cmd P`-shaped passes can read: each one
    that holds no procedure call. -/
def cmdShapedBodies (p : Program) : List (List (Stmt Expression (Cmd Expression))) :=
  (programBodies p).filterMap toCmdStmts

/-- Whether a guard is nondeterministic. -/
def guardIsNondet : ExprOrNondet Expression → Bool
  | .nondet => true
  | .det _ => false

mutual
/-- Whether a statement holds an `.ite` or a `.loop` with a nondeterministic
    guard, at any depth. This is the negation of the postcondition of
    `NondetElim`. -/
def stmtHasNondetGuard (s : Stmt Expression (Cmd Expression)) : Bool :=
  match s with
  | .ite g t e _ => guardIsNondet g || stmtsHaveNondetGuard t || stmtsHaveNondetGuard e
  | .loop g _ _ b _ => guardIsNondet g || stmtsHaveNondetGuard b
  | .block _ b _ => stmtsHaveNondetGuard b
  | .cmd _ | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => false

/-- Whether a statement list holds a nondeterministic guard, at any depth. -/
def stmtsHaveNondetGuard (ss : List (Stmt Expression (Cmd Expression))) : Bool :=
  match ss with
  | [] => false
  | s :: rest => stmtHasNondetGuard s || stmtsHaveNondetGuard rest
end

mutual
/-- Each `init` name of a `Cmd`-shaped statement, at any depth. Distinct from
    `bodyInitNames`, which reads the `CmdExt`-shaped statements the generator
    makes. -/
def cmdStmtInitNames (s : Stmt Expression (Cmd Expression)) : List String :=
  match s with
  | .cmd (.init n _ _ _) => [CoreIdent.toPretty n]
  | .cmd _ => []
  | .block _ b _ => cmdStmtsInitNames b
  | .ite _ t e _ => cmdStmtsInitNames t ++ cmdStmtsInitNames e
  | .loop _ _ _ b _ => cmdStmtsInitNames b
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []

/-- Each `init` name of a `Cmd`-shaped statement list, at any depth. -/
def cmdStmtsInitNames (ss : List (Stmt Expression (Cmd Expression))) : List String :=
  match ss with
  | [] => []
  | s :: rest => cmdStmtInitNames s ++ cmdStmtsInitNames rest
end

/-- **`NondetElim` leaves no nondeterministic guard.** "After the pass, no `.ite`
    or `.loop` carries a `.nondet` guard" is the module doc of `NondetElim`, and
    the file proves no such theorem: its 19 theorems are all preservation lemmas
    about other predicates (`noFuncDecl`, `noMeasureLoops`, and the projections of
    the pass's own step function). The postcondition is decidable, so it becomes
    this property. -/
def checkNondetElimNoNondetGuard (p : Program) : Bool :=
  (cmdShapedBodies p).all fun ss => !stmtsHaveNondetGuard (Imperative.Block.nondetElim ss)

/-- **The fresh guard names of `NondetElim` are distinct and do not collide.** The
    pass mints `$__ndelim_ite$` and `$__ndelim_loop$` names from a
    `StringGenState` counter that never reads the program's names. Two such names
    must differ, and neither may equal a name the input body already declared.

    A collision would make the havoc'd guard variable alias a program variable,
    which changes what the guard reads. -/
def checkNondetElimFreshNames (p : Program) : Bool :=
  (cmdShapedBodies p).all fun ss =>
    let inputNames := cmdStmtsInitNames ss
    let minted := (cmdStmtsInitNames (Imperative.Block.nondetElim ss)).filter fun n =>
      n.startsWith Imperative.ndelimItePrefix || n.startsWith Imperative.ndelimLoopPrefix
    nodup minted && minted.all fun n => !inputNames.contains n

/-- **`LoopInitHoist` leaves no `init` in a loop body.** "The output satisfies
    `Block.loopBodyNoInits = true`" is the module doc of `LoopInitHoist`, and the
    file proves no such theorem: its eight lemmas distribute the structural
    walkers over `++` and are consumed by downstream proof files.
    `Block.loopBodyNoInits` is Strata's own decidable predicate, so the
    postcondition becomes this property directly. -/
def checkHoistNoLoopBodyInits (p : Program) : Bool :=
  (cmdShapedBodies p).all fun ss =>
    Imperative.Block.loopBodyNoInits (Imperative.Block.hoistLoopPrefixInits ss)

/-- `Block.uniqueInits` as a `Bool`. The Strata definition is a `Prop`
    (`(Block.initVars ss).Nodup`) with no `Decidable` instance, so this decides it
    by unfolding one step: `Block.initVars` is the list the `Prop` quantifies over,
    and `nodup` is its `Nodup` under the `BEq` of the identifiers. -/
def uniqueInitsB (ss : List (Stmt Expression (Cmd Expression))) : Bool :=
  nodup (Imperative.Block.initVars ss)

/-- **The same-name lift of `LoopInitHoist` needs `uniqueInits`, and says so.**
    The pass lifts a body `init` to a prelude havoc under the **same** name. Its
    module doc records that this is sound only under `Block.uniqueInits`, the
    global `Nodup` of the init names, "which rules out two hoisted preludes
    colliding".

    So the interesting claim is conditional: when the input satisfies
    `uniqueInits`, the output must too. A generated body can violate `uniqueInits`
    (two sibling blocks may each declare `x`), and the property is then vacuous,
    which is honest: the pass makes no promise there. What the property catches is
    a pass that *breaks* uniqueness on input that had it, which is exactly the
    collision the doc warns about. -/
def checkHoistPreservesUniqueInits (p : Program) : Bool :=
  (cmdShapedBodies p).all fun ss =>
    !uniqueInitsB ss || uniqueInitsB (Imperative.Block.hoistLoopPrefixInits ss)

/-! ## §2.9 The three loop passes under the symbolic evaluator

§2.4 and §2.8 state each loop pass's claim **syntactically**: a count of inserted
statements, a `Bool` postcondition, a survival check on assert *labels*. None of
them asks the question the pipeline actually cares about — whether the pass
changes the **proof obligations that reach SMT**. That is what this section adds,
for `InsertLoopInvariantAsserts`, `NondetElim` and `LoopInitHoist`.

### Running the evaluator on a program that holds a loop

The evaluator does not accept a loop: `Core.Statement.evalOneStmt` *panics* on one
(see the oracle note above `symbolicObligations`), which is why
`loopElimPipelinePhase` sits immediately before `symbolicEval` in
`transformPipelinePhases`. All three passes here act on loops and leave loops
behind, so neither side of the comparison can go straight to the evaluator:
`LoopElim` has to run first, on the pass's output *and* on the baseline. That is
what `elimObligationLabels` does, and it screens the `LoopElim` output for
loop-freedom before calling the evaluator rather than trusting it, because the
failure mode is an uncatchable `PANIC` and not a `false`.

`LoopElim` in turn *throws* on a loop that still carries an invariant or a
measure, so a baseline has to be made loop-eliminable first. The two structural
passes get `InsertLoopInvariantAsserts` in front of them, which is the production
order. `InsertLoopInvariantAsserts` cannot use itself as its own baseline, so
there the invariants and the measures are stripped with `bareLoopsProgram`, which
is sound as a baseline precisely because an invariant is an *annotation*: `while
(c) invariant I { B }` and `while (c) { B }` run the same, so they owe the same
obligations, and the pass's whole job is to add the ones `I` licenses.

### Containment, not equality

For all three the claim is that **no obligation is lost**, plus that the
evaluator does not start failing. Equality is wrong in all three cases, for two
different reasons:

* `InsertLoopInvariantAsserts` *adds* obligations by design — that is the pass.
  So the obligation set must grow, and an equality claim would report the pass
  working as a bug (the trap §2.7 records).

* `NondetElim` also makes the obligation set grow, but for a reason that is *not*
  by design: it **repairs a soundness defect in the evaluator**. See the note
  below, and the `#guard`s at the end of this file.

`LoopInitHoist` is the one pass here whose obligation set is expected to be
exactly preserved, and measurement agrees — but it is still stated as
containment, so that the property keeps reporting the direction that matters (a
*lost* obligation is a lost proof) rather than turning red on a benign addition.

### The evaluator defect that `NondetElim` hides

`StatementEval.lean:586` mints the variable standing for a nondeterministic guard
as

    $__nondet_cond_{Ewn.env.pathConditions.scopes.length}

— a name derived from the current path-condition **depth**, not from a monotone
counter. Entering a `.block` pushes a *variable* scope and no path-condition
scope (`Env.pushEmptyScope` touches `exprEnv.state` only), and
`Env.performMerge` pops the branch scope again after an `.ite`, so two `if *`
statements sitting at the same path-condition depth are handed the **same** name.
The second one's synthesized `init` then re-declares a name already in scope, the
path takes an error, and `evalAuxGo` — whose first act is
`if good.isEmpty then return` — stops. Every obligation from that point to the
end of the procedure is dropped, and `toCoreProofObligationProgram` still returns
`.ok`, so nothing reports it.

Measured, on a one-procedure program:

| body | obligations |
| --- | --- |
| `if * { assert a }; assert after` | `[a, after]` |
| `if * { assert a }; if * { assert b }` | `[a]` |
| `if * { assert a }; if * { assert b }; assert after` | `[a]` |
| `if (true) { assert a }; if (true) { assert b }` | `[a, b]` |

and the mechanism is confirmed against a source program that declares the name
itself: prefixing `init $__nondet_cond_2 : bool := true` to
`if * { assert a }; assert after` drops the obligation list to `[]` — a program
whose every assertion silently goes unchecked.

`NondetElim` replaces each `if *` with a havoc of its own freshly generated
`$__ndelim_ite$` variable, drawn from a `StringGenState` counter that *is*
monotone, so after the pass no `$__nondet_cond_` is ever minted and the dropped
obligations come back. That is why `checkNondetElimSymbolicNoLoss` is stated as
containment: the growth it sees is the evaluator being repaired, and an equality
claim would blame the pass for fixing a bug. -/

/-- A program's procedure bodies rewritten by `f`, every other declaration left
    alone. A `.cfg` body is left alone too: `bodyStmts` reads nothing out of one,
    so there is nothing for a structured pass to rewrite. -/
def mapProgramBodies (f : List Statement → List Statement) (p : Program) : Program :=
  { p with decls := p.decls.map fun
      | .proc q md =>
        .proc { q with body := match q.body with
                  | .structured ss => .structured (f ss)
                  | cfg => cfg } md
      | other => other }

/-- Lift a pass on `Stmt Expression (Cmd Expression)` to one on `Statement`s.
    A body holding a procedure call does not convert (`toCmdStmts` gives `none`),
    and is then returned unchanged rather than dropped — the pass simply does not
    apply there, which is what `cmdShapedBodies` measures. -/
def onCmdShaped
    (f : List (Stmt Expression (Cmd Expression)) → List (Stmt Expression (Cmd Expression)))
    (ss : List Statement) : List Statement :=
  match toCmdStmts ss with
  | some cs => ofCmdStmts (f cs)
  | none => ss

/-- `NondetElim` as a whole-program transform. The pass itself is
    `Imperative.Block.nondetElim`, which has no `PipelinePhase`. -/
def nondetElimProgram (p : Program) : Program :=
  mapProgramBodies (onCmdShaped Imperative.Block.nondetElim) p

/-- `LoopInitHoist` as a whole-program transform. The pass itself is
    `Imperative.Block.hoistLoopPrefixInits`, which has no `PipelinePhase`. -/
def loopInitHoistProgram (p : Program) : Program :=
  mapProgramBodies (onCmdShaped Imperative.Block.hoistLoopPrefixInits) p

mutual
/-- Clear the invariants and the measure of every loop of a statement, at any
    depth. -/
def bareLoopsStmt (s : Statement) : Statement :=
  match s with
  | .loop g _ _ b md => .loop g none [] (bareLoopsStmts b) md
  | .block l b md => .block l (bareLoopsStmts b) md
  | .ite g t e md => .ite g (bareLoopsStmts t) (bareLoopsStmts e) md
  | .cmd c => .cmd c
  | .exit l md => .exit l md
  | .funcDecl d md => .funcDecl d md
  | .typeDecl t md => .typeDecl t md
/-- List analogue of `bareLoopsStmt`. -/
def bareLoopsStmts (ss : List Statement) : List Statement :=
  match ss with
  | [] => []
  | s :: rest => bareLoopsStmt s :: bareLoopsStmts rest
end

/-- The program with every loop annotation dropped. `LoopElim` throws on a loop
    that still carries an invariant or a measure, so this is what makes a
    *pre*-`InsertLoopInvariantAsserts` baseline loop-eliminable at all. Dropping
    an annotation does not change what the program does, so the baseline owes
    exactly the obligations the source program owes minus the ones the invariants
    license. -/
def bareLoopsProgram (p : Program) : Program := mapProgramBodies bareLoopsStmts p

/-- The `assert` labels of the proof obligations of `p` after loop elimination, or
    `none` when the chain never reaches a program the evaluator can read: either
    `LoopElim` threw, or it left a loop behind, or the evaluator raised a
    diagnostic.

    The loop-freedom of the `LoopElim` output is *checked*, not assumed. The
    evaluator answers a loop with an uncatchable `PANIC`, so a `LoopElim` that
    ever failed to remove one would abort the whole test run instead of reporting
    a counterexample. -/
def elimObligationLabels (p : Program) : Option (List String) :=
  match runPhase Core.loopElimPipelinePhase p with
  | none => none
  | some (_, out) =>
    if programHasLoop out then none
    else
      match symbolicObligations out with
      | none => none
      | some ob => some ((programBodies ob).flatMap stmtsAssertLabels)

/-- The obligation labels of `p` after `InsertLoopInvariantAsserts` and then
    `LoopElim` — the production order, and the chain the two structural passes of
    this section are measured through on both sides. -/
def vcElimObligationLabels (p : Program) : Option (List String) :=
  match runPhase loopInvPhase p with
  | none => none
  | some (_, mid) => elimObligationLabels mid

/-- Whether `after` holds every label of `before`, **with at least its
    multiplicity**. Containment and not equality: each of the three passes may
    legitimately *add* an obligation (see the section note), while a lost one is
    always a lost proof.

    Counted rather than set-based, which `checkInlineProcSymbolicAgreement` is not:
    two obligations can share a label (an `assert` inside a loop body reaches the
    evaluator once per encoding branch), and plain `List.contains` would call a
    drop from two copies to one "retained". Comparing counts is the same claim on
    labels that occur once, and strictly sharper on the rest. -/
def labelsRetained (before after : List String) : Bool :=
  before.all fun l => before.count l ≤ after.count l

/-- **`InsertLoopInvariantAsserts` loses no proof obligation under the symbolic
    evaluator.** The syntactic version of this claim is
    `checkLoopVcSurvivesElim`, which follows the pass's own minted labels through
    `LoopElim`. This one is sharper in the direction that matters: it asks what
    the *evaluator* still emits, so an obligation that survives as syntax but is
    dropped during evaluation is caught here and nowhere else.

    The baseline is `bareLoopsProgram p`, the same program with the loop
    annotations cleared, which is what makes it loop-eliminable without running
    the pass under test. Both sides then go through `LoopElim` and the evaluator.

    Vacuous when the input does not typecheck, when a nondeterministic loop
    carries a measure (the pass throws, which `checkLoopNondetMeasureThrows`
    states), or when the baseline itself never reaches the evaluator — there is
    then nothing to compare against. A pass output that *stops* reaching the
    evaluator is a failure, not a skip.

    Coverage, measured over 400 draws
    (`docs/measurements/loop-pass-symeval-coverage.lean`): the claim is live on
    390, and the pass has an invariant or a measure to insert on 10 of those. So
    the guards are cheap but the interesting subset is small, which is what the
    `#guard`s at the end of this file are for. Passes on every draw. -/
def checkLoopVcSymbolicNoLoss (p : Program) : Bool :=
  !progTypeChecks p || hasNondetMeasureLoop p ||
    (match elimObligationLabels (bareLoopsProgram p) with
     | none => true   -- no baseline: no claim to make
     | some before =>
       match vcElimObligationLabels p with
       | none => false   -- the pass broke the chain to the evaluator
       | some after => labelsRetained before after)

/-- **`NondetElim` loses no proof obligation under the symbolic evaluator.**
    Both sides run the production chain `InsertLoopInvariantAsserts` then
    `LoopElim` and then the evaluator; the two differ only in whether
    `Imperative.Block.nondetElim` ran on the procedure bodies first.

    Stated as containment because the pass makes the obligation set **grow**, and
    the growth is the evaluator's `$__nondet_cond_` collision being repaired
    rather than anything the pass does wrong — see the section note and the
    `#guard`s. Equality would report the repair as a defect.

    Vacuous when the input does not typecheck or holds a nondeterministic loop
    carrying a measure. That second guard is doing real work here and is not
    symmetric: `insertInvariantAsserts` throws on such a loop, and `NondetElim`
    makes every guard deterministic, so the pass would *remove* the rejection —
    the after-side would run where the before-side threw, and there would be no
    baseline to compare with.

    Coverage over 400 draws: live on 390, and the pass has a nondeterministic
    guard to rewrite on 8 of those. Passes on every draw — the growth the
    evaluator defect causes is real but always in the safe direction, so only the
    `#guard`s pin the defect itself. -/
def checkNondetElimSymbolicNoLoss (p : Program) : Bool :=
  !progTypeChecks p || hasNondetMeasureLoop p ||
    (match vcElimObligationLabels p with
     | none => true   -- no baseline: no claim to make
     | some before =>
       match vcElimObligationLabels (nondetElimProgram p) with
       | none => false   -- the pass broke the chain to the evaluator
       | some after => labelsRetained before after)

/-- **`LoopInitHoist` loses no proof obligation under the symbolic evaluator.**
    The same chain as `checkNondetElimSymbolicNoLoss`, with
    `Imperative.Block.hoistLoopPrefixInits` as the pass.

    Conditional on `uniqueInitsB`, exactly as `checkHoistPreservesUniqueInits`
    is: the pass lifts a loop-body `init` to a prelude havoc under the **same**
    name, and its module doc records that this is sound only under
    `Block.uniqueInits`, "which rules out two hoisted preludes colliding". On a
    body that violates it the pass makes no promise, so neither does this
    property.

    Of the three passes in this section this is the one whose obligation set is
    expected to be preserved *exactly*, and measurement agrees. It is still
    stated as containment, so a benign addition cannot turn it red while a lost
    obligation — a lost proof — still does.

    Coverage over 400 draws: live on 390, and a loop body holds an `init` for the
    pass to hoist on only 2 of those — the thinnest of the three, since it needs a
    loop *and* a declaration inside it. `uniqueInitsB` rejected none of the 390,
    so that guard costs no coverage here. Passes on every draw. -/
def checkHoistSymbolicNoLoss (p : Program) : Bool :=
  !progTypeChecks p || hasNondetMeasureLoop p ||
    !((cmdShapedBodies p).all uniqueInitsB) ||
    (match vcElimObligationLabels p with
     | none => true   -- no baseline: no claim to make
     | some before =>
       match vcElimObligationLabels (loopInitHoistProgram p) with
       | none => false   -- the pass broke the chain to the evaluator
       | some after => labelsRetained before after)

/-! ## Deterministic guards

Small hand-built programs that pin each dimension generated input cannot reach,
and each of the three honest failures, so a regression shows up as a broken build
rather than as a property that turns green for the wrong reason.

Generated input cannot reach three things: a name that collides with a pass's own
generated prefix (`genIdentName` draws no `$`-prefixed name), a procedure inlined
at two call sites (a generated program holds two or more procedures in about
3 percent of draws, and a call in under 2 percent), and a `.cfg` body in the input
(no generator makes one). -/

section Guards

/-- A procedure with the given name and structured body, and no parameter. -/
private def guardProc (name : String) (ss : List Statement) : Procedure :=
  { header := { name := ⟨name, ()⟩, typeArgs := [], inputs := [], outputs := [],
                noFilter := false }
    spec := { preconditions := [], postconditions := [] }
    body := .structured ss }

/-- A one-procedure program holding `ss`. -/
private def guardProg (ss : List Statement) : Program :=
  { decls := [.proc (guardProc "P" ss) .empty] }

private def trueLit : Expression.Expr := .const () (.boolConst true)
private def intLit (i : Int) : Expression.Expr := .const () (.intConst i)

/-- A trivial `assert` leaf. -/
private def guardAssert (l : String) : Statement := Statement.assert l trueLit .empty

-- ── The three honest failures ─────────────────────────────────────────────

-- `LoopElim` mints `loopElim_havoc_{n}` two times for one loop, so the output
-- holds two blocks under one label. Pinned on a bare loop, which is the shape
-- `LoopElim` accepts.
#guard !checkLoopBlockLabelsNodup (guardProg [.loop .nondet none [] [guardAssert "a"] .empty])

-- A procedure with a `.cfg` body does not print: `procToCST` writes
-- "CFG bodies not yet supported" and emits an empty body.
#guard !checkS2uCfgPrintable (guardProg [guardAssert "a"])

-- The same `.cfg` body does not *typecheck* either, which is the sharper half of
-- the same gap: `Program.typeCheck` rejects it with "CFG procedures not supported
-- yet" while accepting the structured original. Since `corePipelinePhases` appends
-- a typecheck phase after the transform phases, a program that went through
-- `StructuredToUnstructured` can be neither printed nor re-checked.
#guard progTypeChecks (guardProg [guardAssert "a"])
#guard !progTypeChecks
  { decls := [.proc { guardProc "P" [] with
                      body := .cfg (bodyCfg [guardAssert "a"]) } .empty] }

-- Every source `.block l` becomes an orphan in the emitted CFG: the pass gives the
-- label a landing site for an `.exit l` and returns a different entry, so nothing
-- jumps to `l`.
#guard !checkS2uAllReachable (guardProg [.block "f" [] .empty])

-- The label-distinctness property is guarded on the source, because two sibling
-- blocks may legitimately share a label (`genFreshLabel` draws fresh against the
-- *enclosing* labels only, which is all the typing spec's `block` premise asks).
-- Such a body makes the emitted CFG hold two blocks of that name, and the pass is
-- not at fault: it copied the source label.
#guard !nodup (stmtsBlockLabels [(.block "j" [] .empty : Statement), .block "j" [] .empty])
#guard checkS2uLabelsNodup (guardProg [.block "j" [] .empty, .block "j" [] .empty])

-- With distinct source labels the claim is live, and it holds: the labels the pass
-- mints from its own counter collide neither with each other nor with a source
-- label, at every shape the generator can reach.
#guard nodup (stmtsBlockLabels [(.block "j" [] .empty : Statement), .block "k" [] .empty])
#guard checkS2uLabelsNodup (guardProg [.block "j" [] .empty, .block "k" [] .empty])
#guard checkS2uLabelsNodup
  (guardProg [.block "b" [.ite (.det trueLit) [guardAssert "t"] [.exit "b" .empty] .empty] .empty,
              .loop .nondet none [] [guardAssert "l"] .empty])

-- ── The command count, and what it may exclude ────────────────────────────

-- A statement after an `.exit` in the same list is unreachable, and the pass drops
-- it. The source count therefore stops at the `.exit`, so the property does not
-- report a documented omission as a loss.
#guard checkS2uCmdCountGrows
  (guardProg [.block "f" [.exit "f" .empty, guardAssert "dead"] .empty])

-- With the same body and no `.exit`, the command is carried through and counted on
-- both sides, so the property is not weakened into a tautology.
#guard checkS2uCmdCountGrows (guardProg [.block "f" [guardAssert "live"] .empty])
#guard stmtsCmdCount [.block "f" [guardAssert "live"] .empty] == 1
#guard stmtsCmdCount [.block "f" [.exit "f" .empty, guardAssert "dead"] .empty] == 0

-- ── Dimensions generated input cannot reach ───────────────────────────────

/-- The type of a binary integer operator, `int -> int -> int`. -/
private def intBinOpTy : LMonoTy := .tcons "arrow" [.int, .tcons "arrow" [.int, .int]]

/-- `Int.Add(3, 4)` with the operator annotated, so `LExpr.typeOf` gives `int` and
    CSE records a monomorphic annotation for the extracted variable. -/
private def cseDup : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Add", ()⟩ (some intBinOpTy)) (intLit 3)) (intLit 4)

/-- The same subexpression with the operator **unannotated**. `LExpr.typeOf` reads
    an annotation rather than inferring one, so it gives `none` here, and CSE falls
    back to a polymorphic annotation the typechecker forbids. -/
private def cseDupBare : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Add", ()⟩ none) (intLit 3)) (intLit 4)

/-- A body whose two `init`s share the subexpression `Int.Add(3, 4)`, so CSE
    fires and mints `$__cse.0`. -/
private def cseFiringBody : List Statement :=
  [ Statement.init ⟨"a", ()⟩ (.forAll [] .int) (.det cseDup) .empty,
    Statement.init ⟨"b", ()⟩ (.forAll [] .int) (.det cseDup) .empty ]

/-- The same body, with `$__cse.0` already declared. The counter that mints the
    index never reads a program name (`CommonSubexprElim.lean:331`), so this is
    where the collision lands. `genIdentName` draws no `$`-prefixed name, so only
    a hand-built program reaches it. -/
private def cseCollisionBody : List Statement :=
  Statement.init ⟨s!"{Core.CSE.cseVarPrefix}0", ()⟩ (.forAll [] .int) (.det (intLit 9)) .empty
    :: cseFiringBody

-- CSE really fires on `cseFiringBody`, and the fresh name it mints is unique
-- there, so each property is non-vacuous and green on a well-behaved input. This
-- matters more than usual: CSE fires on 0 of 200 generated programs, so without
-- these guards all four CSE properties would be vacuously green forever.
#guard (runPhase Core.commonSubexprElimPhase (guardProg cseFiringBody)).any (·.1)
#guard checkCseFreshNamesFresh (guardProg cseFiringBody)
#guard checkCseAssertLabelsPreserved (guardProg cseFiringBody)
#guard checkCseFreshDeclOrder (guardProg cseFiringBody)
#guard checkCseOutputTypechecks (guardProg cseFiringBody)

/-- The same firing body, with the duplicated subexpression left unannotated. -/
private def cseBareBody : List Statement :=
  [ Statement.init ⟨"a", ()⟩ (.forAll [] .int) (.det cseDupBare) .empty,
    Statement.init ⟨"b", ()⟩ (.forAll [] .int) (.det cseDupBare) .empty ]

-- **A polymorphic annotation the typechecker used to forbid — FIXED UPSTREAM.** With the
-- operator unannotated, `dup.typeOf` gives `none` and CSE emits `var $__cse.0 : α := 3 + 4;`.
-- That output used to be rejected ("Variable annotation must be monomorphic, but got
-- polymorphic type ∀[α]. α"), isolating the `none` fallback as the cause; on
-- `strata-org/Strata` `main` both the input and the CSE output typecheck.
#guard progTypeChecks (guardProg cseBareBody)
#guard checkCseOutputTypechecks (guardProg cseBareBody)

/-- `Int.Add(7, 8)`, a second subexpression to duplicate, so CSE mints two names
    and the order claim has something to order. -/
private def cseDup2 : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Add", ()⟩ none) (intLit 7)) (intLit 8)

/-- A body with two distinct duplicated subexpressions, so CSE mints `$__cse.0`
    and `$__cse.1`. With one minted name the order claim is trivially true, so this
    is what makes `checkCseFreshDeclOrder` a real claim. -/
private def cseTwoExtractionsBody : List Statement :=
  [ Statement.init ⟨"a", ()⟩ (.forAll [] .int) (.det cseDup) .empty,
    Statement.init ⟨"b", ()⟩ (.forAll [] .int) (.det cseDup) .empty,
    Statement.init ⟨"c", ()⟩ (.forAll [] .int) (.det cseDup2) .empty,
    Statement.init ⟨"d", ()⟩ (.forAll [] .int) (.det cseDup2) .empty ]

-- Two names really are minted, in index order.
#guard (match runPhase Core.commonSubexprElimPhase (guardProg cseTwoExtractionsBody) with
        | some (_, out) =>
          ((programBodies out).map bodyInitNames).flatten.filter
            (·.startsWith Core.CSE.cseVarPrefix) ==
              [s!"{Core.CSE.cseVarPrefix}0", s!"{Core.CSE.cseVarPrefix}1"]
        | none => false)
#guard checkCseFreshDeclOrder (guardProg cseTwoExtractionsBody)
#guard checkCseFreshNamesFresh (guardProg cseTwoExtractionsBody)

-- **A real collision.** On a body that already declares `$__cse.0`, the pass
-- declares it a second time: the output holds `var $__cse.0 : α := 3 + 4;`
-- immediately followed by the body's own `var $__cse.0 : int := 9;`. The two
-- references the pass inserted then resolve to the second declaration, which holds
-- `9` rather than the extracted `3 + 4`, so the rewrite changes the meaning of the
-- program. `Program.typeCheck` accepts the input and rejects the output, which is
-- the sharpest available statement of the defect.
#guard !checkCseFreshNamesFresh (guardProg cseCollisionBody)
#guard progTypeChecks (guardProg cseCollisionBody)
#guard !checkCseOutputTypechecks (guardProg cseCollisionBody)

/-- Two procedures, the second calling the first two times, with the callee
    holding a local variable. This is the shape the `ProcedureInlining` label
    properties exist for: one callee inlined at two call sites, which is where a
    non-unique label appears. A generated program reaches two procedures rarely,
    and two calls to one procedure not at all, so this pins the dimension
    deterministically.

    The local variable matters: it makes `var_map` non-empty, which is what lets
    `renameAllLocalNames` reach its label-renaming step at all (see cause 2 in
    `checkInlineProcLabelsNodup`). So this program isolates cause 1. -/
private def twoCallSitesProgram : Program :=
  { decls :=
      [ .proc (guardProc "Callee"
          [ Statement.init ⟨"v", ()⟩ (.forAll [] .int) (.det (intLit 1)) .empty,
            guardAssert "inner" ]) .empty,
        .proc (guardProc "Caller"
          [ .cmd (.call "Callee" [] .empty),
            .cmd (.call "Callee" [] .empty) ]) .empty ] }

/-- The same two call sites, but with a callee that declares no variable. This
    isolates cause 2: `var_map` is empty, so the fold that carries the label
    renaming never runs, and the callee's `assert` label is copied verbatim at
    both call sites. -/
private def twoCallSitesNoVarProgram : Program :=
  { decls :=
      [ .proc (guardProc "Callee" [guardAssert "inner"]) .empty,
        .proc (guardProc "Caller"
          [ .cmd (.call "Callee" [] .empty),
            .cmd (.call "Callee" [] .empty) ]) .empty ] }

-- Both inputs have distinct labels, so the property's guard does not fire and each
-- failure below is about the pass.
#guard programLabelsNodup twoCallSitesProgram
#guard programLabelsNodup twoCallSitesNoVarProgram

-- **Cause 1: the constant wrapper label.** With the callee's own labels correctly
-- freshened to `Callee_inner_1` and `Callee_inner_3`, the two wrapper blocks are
-- both labeled `Callee$inlined`, because that label is a string concatenation and
-- not a counter draw.
#guard !checkInlineProcLabelsNodup twoCallSitesProgram

-- **Cause 2: the unreached renaming.** With an empty `var_map`, neither the
-- wrapper label nor the callee's `assert` label is freshened, so the caller body
-- holds `Callee$inlined` two times *and* `inner` two times.
#guard !checkInlineProcLabelsNodup twoCallSitesNoVarProgram

-- The callee's one `assert` rides along into the caller two times, so the total
-- count grows rather than shrinking. This holds under both causes: a duplicated
-- label is still a present obligation.
#guard checkInlineProcAssertsNotLost twoCallSitesProgram
#guard checkInlineProcAssertsNotLost twoCallSitesNoVarProgram

-- The statistics counters stay consistent across the two inlinings.
#guard checkInlineProcStatsFaithful twoCallSitesProgram

-- ── Symbolic-eval agreement for `ProcedureInlining` ───────────────────────
-- The pass fires on 0 of 400 typechecking generated draws, so these guards are what
-- test the property at all.

-- On a callee with NO precondition, nothing is lost and the property holds.
#guard checkInlineProcSymbolicAgreement twoCallSitesProgram
#guard checkInlineProcSymbolicAgreement twoCallSitesNoVarProgram

/-- `x >= 0`, as an obligation on the caller of `Callee`. -/
private def geZeroX : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Ge", ()⟩ none) (.fvar () ⟨"x", ()⟩ (some .int))) (intLit 0)

/-- A caller that binds `y := arg` and calls `Callee(y)`. Shared by the two witnesses
    below, which differ only in the callee's body. -/
private def callerPassing (arg : Expression.Expr) : Decl :=
  .proc { header := { name := ⟨"Caller", ()⟩, typeArgs := [], inputs := [],
                      outputs := [], noFilter := false }
          spec := { preconditions := [], postconditions := [] }
          body := .structured
            [ Statement.init ⟨"y", ()⟩ (.forAll [] .int) (.det arg) .empty,
              .cmd (.call "Callee" [.inArg (.fvar () ⟨"y", ()⟩ (some .int))] .empty) ]
        } .empty

/-- **The minimal witness for the dropped-`requires` defect.** A callee with
    `requires x >= 0` and an **empty body**, called with `-1`.

    The empty body is what makes this the sharpest possible statement of the defect:
    the precondition check is the program's *only* proof obligation, so the obligation
    list goes from exactly one entry to **zero**. There is no surviving obligation for
    a reader to compare against, and — more to the point — no candidate the lost
    obligation could have been silently *renamed* into, which forecloses the objection
    that it was absorbed rather than dropped.

    Before inlining, symbolic evaluation of this program is one line:

        assert [|(Origin_Callee_Requires)pre|]: false;

    `false` because `-1 >= 0` folds to it, so the obligation is unsatisfiable —
    correctly reporting that the call is illegal. After inlining the whole inlined
    block is a single variable binding and the obligation list is `[]`. -/
private def preconditionEmptyBodyProgram : Program :=
  { decls :=
      [ .proc { header := { name := ⟨"Callee", ()⟩, typeArgs := [],
                            inputs := [(⟨"x", ()⟩, .int)], outputs := [],
                            noFilter := false }
                spec := { preconditions := [("pre", { expr := geZeroX })],
                          postconditions := [] }
                body := .structured [] } .empty,
        callerPassing (intLit (-1)) ] }

/-- The same, with a **non-empty** callee body. Kept alongside the minimal witness
    because it shows the defect is not an artifact of the body being empty: here the
    body's own obligation survives (renamed to `Callee_inner_1`) while the precondition
    obligation still disappears, so the list *shrinks* rather than emptying. -/
private def preconditionCallProgram : Program :=
  { decls :=
      [ .proc { header := { name := ⟨"Callee", ()⟩, typeArgs := [],
                            inputs := [(⟨"x", ()⟩, .int)], outputs := [],
                            noFilter := false }
                spec := { preconditions := [("pre", { expr := geZeroX })],
                          postconditions := [] }
                body := .structured [guardAssert "inner"] } .empty,
        callerPassing (intLit (-1)) ] }

/-- The minimal witness's callee, called with a value that **satisfies** the
    precondition. The contrast case: the obligation is a real check on the argument
    rather than a constant, so it folds to `true` here and discharges trivially. -/
private def preconditionSatisfiedProgram : Program :=
  { decls :=
      [ .proc { header := { name := ⟨"Callee", ()⟩, typeArgs := [],
                            inputs := [(⟨"x", ()⟩, .int)], outputs := [],
                            noFilter := false }
                spec := { preconditions := [("pre", { expr := geZeroX })],
                          postconditions := [] }
                body := .structured [] } .empty,
        callerPassing (intLit 5) ] }

-- **The precondition obligation is dropped, on the minimal witness.** The input
-- typechecks, symbolic evaluation succeeds on both sides, and the pass fires — so the
-- failure is neither an ill-typed input, nor an oracle error, nor a no-op. It is a
-- lost proof obligation.
#guard progTypeChecks preconditionEmptyBodyProgram
#guard (symbolicObligations preconditionEmptyBodyProgram).isSome
#guard (runPhase inlinePhase preconditionEmptyBodyProgram).any (·.1)
#guard !checkInlineProcSymbolicAgreement preconditionEmptyBodyProgram

-- Exactly one obligation before, and none after. The total form of the defect.
#guard (match symbolicObligations preconditionEmptyBodyProgram with
        | some sa => ((programBodies sa).flatMap stmtsAssertLabels).length == 1
        | none => false)
#guard (match runPhase inlinePhase preconditionEmptyBodyProgram with
        | some (_, out) =>
          (match symbolicObligations out with
           | some sb => ((programBodies sb).flatMap stmtsAssertLabels).isEmpty
           | none => false)
        | none => false)

-- The contrast case. With an argument that satisfies the precondition, the obligation
-- folds to `true` rather than `false` — so the pre-inlining obligation really is a
-- check on the caller's argument. The defect is still present (the check is still
-- dropped), which is the point: the pass does not inspect the argument either.
#guard progTypeChecks preconditionSatisfiedProgram
#guard !checkInlineProcSymbolicAgreement preconditionSatisfiedProgram

-- And on the non-empty-body variant the list shrinks rather than emptying, so the
-- defect is not an artifact of the empty body.
#guard progTypeChecks preconditionCallProgram
#guard (symbolicObligations preconditionCallProgram).isSome
#guard !checkInlineProcSymbolicAgreement preconditionCallProgram

/-- The shrunk counterexample the property reported on a generated draw at 400 trials,
    transcribed so the finding does not depend on a lucky reseed.

    Two things make it a *better* witness than `preconditionCallProgram` above, and it
    is kept alongside rather than instead of it:

    * the callee has an **empty body**, so the obligation program before inlining holds
      *only* the precondition check. After inlining the obligation list is `[]` — the
      program's sole proof obligation is gone, rather than one of several;
    * nothing about it is contrived. The generator drew a beta redex for the
      precondition (`(fun __q0 : bv64 => true)(bv{64}(5065526758814335903))`), five
      parameters of assorted types, two type parameters, and a procedure named `$`.
      A hand-written witness invites the reply "no real program looks like that"; this
      one is what the generator actually produced. -/
private def generatedRequiresWitness : Program :=
  let preExpr : Expression.Expr :=
    .app ()
      (.abs () "__q0" (some (.bitvec 64)) (.const () (.boolConst true)))
      (.const () (.bitvecConst 64 5065526758814335903))
  { decls :=
      [ .proc { header := { name := ⟨"Mj", ()⟩, typeArgs := ["P", "jvB"],
                            inputs := [(⟨"xB", ()⟩, .string), (⟨"sRw", ()⟩, .real),
                                       (⟨"w", ()⟩, .real)],
                            outputs := [(⟨"xB", ()⟩, .string), (⟨"sRw", ()⟩, .real),
                                        (⟨"w", ()⟩, .real), (⟨"u", ()⟩, .int),
                                        (⟨"h", ()⟩, .real)],
                            noFilter := false }
                spec := { preconditions := [("y_", { expr := preExpr })],
                          postconditions := [] }
                body := .structured [] } .empty,
        .proc { header := { name := ⟨"HcX", ()⟩, typeArgs := ["E", "n", "$"],
                            inputs := [(⟨"o", ()⟩, .tcons "Sequence" [.real]),
                                       (⟨"p", ()⟩, .regex), (⟨"DN", ()⟩, .bool)],
                            outputs := [(⟨"o", ()⟩, .tcons "Sequence" [.real]),
                                        (⟨"E", ()⟩, .int)],
                            noFilter := false }
                spec := { preconditions := [], postconditions := [] }
                body := .structured
                  [ Statement.init ⟨"xB", ()⟩ (.forAll [] .string) .nondet .empty,
                    Statement.init ⟨"sRw", ()⟩ (.forAll [] .real) .nondet .empty,
                    Statement.init ⟨"w", ()⟩ (.forAll [] .real) .nondet .empty,
                    Statement.init ⟨"xxxxxx", ()⟩ (.forAll [] .int) .nondet .empty,
                    Statement.init ⟨"xxxxxxx", ()⟩ (.forAll [] .real) .nondet .empty,
                    .cmd (.call "Mj"
                      [ .inoutArg ⟨"xB", ()⟩, .inoutArg ⟨"sRw", ()⟩, .inoutArg ⟨"w", ()⟩,
                        .outArg ⟨"xxxxxx", ()⟩, .outArg ⟨"xxxxxxx", ()⟩ ] .empty) ]
              } .empty ] }

-- The generated witness typechecks, the pass fires on it, and the property fails.
#guard progTypeChecks generatedRequiresWitness
#guard (runPhase inlinePhase generatedRequiresWitness).any (·.1)
#guard !checkInlineProcSymbolicAgreement generatedRequiresWitness

-- The sharpest statement of the defect: **one** obligation before, **none** after.
#guard (match symbolicObligations generatedRequiresWitness with
        | some sa => ((programBodies sa).flatMap stmtsAssertLabels).length == 1
        | none => false)
#guard (match runPhase inlinePhase generatedRequiresWitness with
        | some (_, out) =>
          (match symbolicObligations out with
           | some sb => ((programBodies sb).flatMap stmtsAssertLabels).isEmpty
           | none => false)
        | none => false)

-- Precisely which label is lost: `(Origin_Callee_Requires)pre` is present before and
-- absent after, while the body's own `inner` survives (renamed). Pinning the label
-- keeps the finding legible if the property is ever restated.
#guard (match symbolicObligations preconditionCallProgram with
        | some sa => ((programBodies sa).flatMap stmtsAssertLabels).any
            (·.endsWith "pre")
        | none => false)
#guard (match runPhase inlinePhase preconditionCallProgram with
        | some (_, out) =>
          (match symbolicObligations out with
           | some sb => !(((programBodies sb).flatMap stmtsAssertLabels).any
               (·.endsWith "pre"))
           | none => false)
        | none => false)

-- Non-vacuity: the pass really fires, symbolic evaluation really succeeds on both
-- sides, and the obligation count really *grows* — which is why the property claims
-- containment rather than equality. Pinning the growth keeps a future reader from
-- "tightening" the property into something false.
#guard (runPhase inlinePhase twoCallSitesProgram).any (·.1)
#guard (symbolicObligations twoCallSitesProgram).isSome
#guard (match runPhase inlinePhase twoCallSitesProgram with
        | some (_, out) =>
          (match symbolicObligations twoCallSitesProgram, symbolicObligations out with
           | some before, some after =>
             ((programBodies after).flatMap stmtsAssertLabels).length >
               ((programBodies before).flatMap stmtsAssertLabels).length
           | _, _ => false)
        | none => false)

/-- `old T`, the pre-state value of an inout parameter `T`. Inside a procedure body
    this is a free variable whose name is literally `"old T"`, which the checker
    admits because the enclosing procedure declares `T` as an inout parameter. -/
private def oldT : Expression.Expr := .fvar () ⟨"old T", ()⟩ (some .bool)

/-- A callee with one inout parameter `T` whose body asserts `old T`, called once
    by a caller that declares `T`. This is the shape that shows `old` escaping the
    renaming: `T` is renamed and `old T` is not. -/
private def oldExprProgram : Program :=
  { decls :=
      [ .proc { header := { name := ⟨"Callee", ()⟩, typeArgs := [],
                            inputs := [(⟨"T", ()⟩, .bool)],
                            outputs := [(⟨"T", ()⟩, .bool)], noFilter := false }
                spec := { preconditions := [], postconditions := [] }
                body := .structured [Statement.assert "inner" oldT .empty] } .empty,
        .proc { header := { name := ⟨"Caller", ()⟩, typeArgs := [], inputs := [],
                            outputs := [], noFilter := false }
                spec := { preconditions := [], postconditions := [] }
                body := .structured
                  [ Statement.init ⟨"T", ()⟩ (.forAll [] .bool) (.det trueLit) .empty,
                    .cmd (.call "Callee" [.inoutArg ⟨"T", ()⟩] .empty) ] } .empty ] }

-- **`old` escapes the renaming.** The input typechecks and the output does not:
-- the spliced body renames `T` to `Callee_T_1` but copies `old T` verbatim, so the
-- caller holds a free variable that no parameter of the caller backs. The checker's
-- own message is "No free variables are allowed here! Free Variables: [old T]".
#guard progTypeChecks oldExprProgram
#guard !checkInlineProcTypechecks oldExprProgram

/-- A program whose one function has a body, so `FunctionInlining` can fire.
    `Core.Factory` holds no function body at all (0 of 310 entries), so without a
    declared function every inlining property would pass vacuously. -/
private def inlinableProgram : Program :=
  let f : Function :=
    { name := ⟨"guardF", ()⟩, typeArgs := [], inputs := [(⟨"x", ()⟩, .int)],
      output := .int, body := some (.fvar () ⟨"x", ()⟩ (some .int)) }
  { decls :=
      [ .func f .empty,
        .proc (guardProc "P"
          [ Statement.init ⟨"y", ()⟩ (.forAll [] .int)
              (.det (.app () (.op () ⟨"guardF", ()⟩
                (some (.tcons "arrow" [.int, .int]))) (intLit 7))) .empty ]) .empty ] }

-- The factory seeded from the program does hold the body, so the pass really
-- inlines: the transformed expression differs from the input.
#guard (programExprs inlinableProgram).any fun e =>
  decide (inlineIn inlinableProgram e = e) == false

-- And each inlining property holds on that non-vacuous input.
#guard checkInlineFuelZeroIdentity inlinableProgram
#guard checkInlineFuelMonotone inlinableProgram
#guard checkInlineTypePreserved inlinableProgram
#guard checkInlineCaptureFree inlinableProgram

/-- A program with a **chain** of two functions, the second calling the first, and a
    body that calls the second. Nesting is what makes fuel monotonicity a real
    claim: with one function the two budgets the property compares (1 and 4) reach
    the same fixed point, so the comparison is trivially an equality. -/
private def nestedInlinableProgram : Program :=
  let inner : Function :=
    { name := ⟨"guardInner", ()⟩, typeArgs := [], inputs := [(⟨"x", ()⟩, .int)],
      output := .int, body := some (.fvar () ⟨"x", ()⟩ (some .int)) }
  let outer : Function :=
    { name := ⟨"guardOuter", ()⟩, typeArgs := [], inputs := [(⟨"y", ()⟩, .int)],
      output := .int,
      body := some (.app () (.op () ⟨"guardInner", ()⟩
        (some (.tcons "arrow" [.int, .int]))) (.fvar () ⟨"y", ()⟩ (some .int))) }
  { decls :=
      [ .func inner .empty, .func outer .empty,
        .proc (guardProc "P"
          [ Statement.init ⟨"z", ()⟩ (.forAll [] .int)
              (.det (.app () (.op () ⟨"guardOuter", ()⟩
                (some (.tcons "arrow" [.int, .int]))) (intLit 7))) .empty ]) .empty ] }

-- The chain really inlines through both levels: the fully inlined result is the
-- argument itself, so nothing of either call is left.
#guard (programExprs nestedInlinableProgram).any fun e =>
  decide (inlineIn nestedInlinableProgram e = intLit 7)

-- The two budgets that `checkInlineFuelMonotone` compares really do differ on this
-- program: at fuel 1 one inlinable call is left, and at fuel 4 none is. So the
-- property is a strict inequality here and not a trivial equality, which it *is* on
-- the single-function `inlinableProgram` above (both budgets reach the same fixed
-- point there). Without this the monotonicity claim would be untested.
#guard (programExprs nestedInlinableProgram).any fun e =>
  let F := programFactory nestedInlinableProgram
  inlinableCallCount F (Strata.inlineFuncDefsBounded F 4 e) <
    inlinableCallCount F (Strata.inlineFuncDefsBounded F 1 e)

#guard checkInlineFuelZeroIdentity nestedInlinableProgram
#guard checkInlineFuelMonotone nestedInlinableProgram
#guard checkInlineTypePreserved nestedInlinableProgram
#guard checkInlineCaptureFree nestedInlinableProgram

-- ── Value preservation under the evaluator ────────────────────────────────

-- Inlining preserves the evaluated result on both inlinable shapes.
#guard checkInlineEvalAgreement inlinableProgram
#guard checkInlineEvalAgreement nestedInlinableProgram

-- Non-vacuity, and it matters here more than usual: the property is an implication
-- whose premise is "the transform changed the expression", and the whole comparison
-- rests on the evaluator being *willing* to unfold. So pin that the inlined side
-- really reduces to a canonical value under `inlineEvalFactory` — the chain
-- `guardOuter(7) → guardInner(7) → 7` collapses to the literal.
#guard (programExprs nestedInlinableProgram).any fun e =>
  let out := Strata.inlineFuncDefs (programFactory nestedInlinableProgram) (e := e)
  decide (out = e) == false &&
    decide (evalOver (inlineEvalFactory nestedInlinableProgram) out = intLit 7)

-- And pin the asymmetry that makes `inlineEvalFactory` necessary: over the *plain*
-- factory the evaluator will not unfold an unattributed function, so the original
-- side stays stuck on the call. Without the `.inline` marking the comparison would be
-- between two different notions of unfolding, and would fail on every sample.
#guard (programExprs nestedInlinableProgram).any fun e =>
  let F := programFactory nestedInlinableProgram
  let out := Strata.inlineFuncDefs F (e := e)
  decide (out = e) == false && decide (evalOver F e = e)

/-- A nullary bodied function, so a "call" to it is a bare `.op` node — the smallest
    shape that exercises the binder boundary below. -/
private def nullaryFuncProgram (body : Expression.Expr) : Program :=
  { decls :=
      [ .func { name := ⟨"NF", ()⟩, typeArgs := [], inputs := [], output := .bool,
                body := some (.const () (.boolConst false)) } .empty,
        .proc (guardProc "P" [Statement.assert "a" body .empty]) .empty ] }

/-- The call `NF`, at `bool`. -/
private def nfCall : Expression.Expr := .op () ⟨"NF", ()⟩ (some .bool)

-- **The binder boundary, pinned in both directions.** Outside a binder the evaluator
-- and the transform agree, so the property is a live claim there.
#guard !exprHasBinder nfCall
#guard checkInlineEvalAgreement (nullaryFuncProgram nfCall)
#guard checkInlineEvalAgreement
  (nullaryFuncProgram (.ite () nfCall trueLit (.const () (.boolConst false))))

-- Under a binder they legitimately diverge: `eval` substitutes and stops
-- (`LExprEval.lean:333`) while `inlineFuncDefs` recurses, so `fun q => NF` evaluates
-- to itself on the left and to `fun q => false` on the right. `exprHasBinder`
-- excludes it, which is why the property still passes on such a program — the guard
-- records that this exclusion is doing real work and is not dead weight.
#guard exprHasBinder (.abs () "q" (some .bool) nfCall)
#guard checkInlineEvalAgreement (nullaryFuncProgram (.abs () "q" (some .bool) nfCall))
#guard (let p := nullaryFuncProgram (.abs () "q" (some .bool) nfCall)
        let e : Expression.Expr := .abs () "q" (some .bool) nfCall
        let out := Strata.inlineFuncDefs (programFactory p) (e := e)
        -- Without the exclusion this pair would be reported as a disagreement.
        decide (out = e) == false &&
          decide (evalOver (inlineEvalFactory p) e = evalOver (inlineEvalFactory p) out) == false)

-- ── The measure that `DetToKleene` drops ──────────────────────────────────

-- A loop with a measure and no invariant: the transform is defined, and the
-- measure is gone from the result. This is the §2.3 characterization, pinned on
-- the exact shape rather than left to the generator's 8 percent hit rate.
#guard checkKleeneMeasureAccepted (guardProg [.loop .nondet (some (intLit 3)) [] [] .empty])

-- The contrast: a loop with an invariant makes the transform undefined, which is
-- the rejection the pass does make. So the two annotations are treated
-- differently, which is the asymmetry the property records.
#guard (kleeneStmts [.loop .nondet none [("i", trueLit)] [] .empty]).isNone
#guard (kleeneStmts [.loop .nondet (some (intLit 3)) [] [] .empty]).isSome

-- ── The verification-condition counts ─────────────────────────────────────

-- One deterministic loop with two invariants and a measure: 2 entry asserts,
-- 2 maintain asserts and 2 measure asserts, so 6 prefixed asserts in all.
private def twoInvariantLoop : Statement :=
  .loop (.det trueLit) (some (intLit 3)) [("i", trueLit), ("j", trueLit)] [guardAssert "a"] .empty

#guard checkLoopVcAssertCount (guardProg [twoInvariantLoop])
#guard checkLoopBareAfterPass (guardProg [twoInvariantLoop])
#guard checkLoopVcIdempotent (guardProg [twoInvariantLoop])
#guard checkLoopVcStatFaithful (guardProg [twoInvariantLoop])
#guard checkLoopVcSurvivesElim (guardProg [twoInvariantLoop])
#guard checkLoopElimStatFaithful (guardProg [twoInvariantLoop])

-- A nondeterministic loop that carries a measure is rejected with a diagnostic,
-- and not silently stripped.
#guard checkLoopNondetMeasureThrows
  (guardProg [.loop .nondet (some (intLit 3)) [] [] .empty])
#guard (runPhase loopInvPhase (guardProg [.loop .nondet (some (intLit 3)) [] [] .empty])).isNone

-- ── The axiom relevance oracle ────────────────────────────────────────────

/-- A program with a function, an axiom that mentions it, and an axiom that
    mentions nothing. The pass must keep the first and prune the second, which is
    the discrimination the relevance oracle exists to make. A generated program
    holds an axiom in about 3 percent of draws, so this pins the dimension. -/
private def axiomRelevanceProgram : Program :=
  let f : Function :=
    { name := ⟨"relF", ()⟩, typeArgs := [], inputs := [(⟨"x", ()⟩, .int)],
      output := .int, body := some (.fvar () ⟨"x", ()⟩ (some .int)) }
  { decls :=
      [ .func f .empty,
        -- Mentions `relF`, so it is relevant to the seed set `["relF"]`.
        .ax { name := "relevantAx",
              e := .eq () (.app () (.op () ⟨"relF", ()⟩
                (some (.tcons "arrow" [.int, .int]))) (intLit 1)) (intLit 1) } .empty,
        -- Mentions no declared function, so it is irrelevant.
        .ax { name := "irrelevantAx", e := trueLit } .empty ] }

#guard checkAxiomsOnlyAxRemoved axiomRelevanceProgram
#guard checkAxiomsOrderPreserved axiomRelevanceProgram
#guard checkAxiomsRetainedRelevant axiomRelevanceProgram
#guard checkAxiomsRemovedIrrelevant axiomRelevanceProgram
#guard checkAxiomsRemovedNotSeedReachable axiomRelevanceProgram

-- The pass really discriminates on this input: it keeps the relevant axiom and
-- prunes the other, so the five properties above are not vacuous here.
#guard (irrelevantByPass axiomRelevanceProgram) == ["irrelevantAx"]

-- The obligation-equality property holds on the same program, and non-vacuously: the
-- input is loop-free and typechecks, so neither guard short-circuits it, and the pass
-- really prunes an axiom (pinned just above). Deleting an assumption leaves the
-- obligations alone, which is the claim.
#guard !programHasLoop axiomRelevanceProgram
#guard (symbolicObligations axiomRelevanceProgram).isSome
#guard checkAxiomsObligationsUnchanged axiomRelevanceProgram

-- A program with a loop is skipped rather than crashing the evaluator. Worth pinning
-- because the failure mode is a `PANIC`, not a `false` — an unscreened property would
-- abort the whole test run rather than report a counterexample.
#guard programHasLoop (guardProg [.loop .nondet none [] [guardAssert "a"] .empty])
#guard checkAxiomsObligationsUnchanged
  (guardProg [.loop .nondet none [] [guardAssert "a"] .empty])

-- ── The two unproven postconditions ───────────────────────────────────────

-- `NondetElim` leaves no nondeterministic guard, on a body that holds both a
-- nondet `ite` and a nondet `loop`.
private def nondetBody : List Statement :=
  [ .ite .nondet [guardAssert "t"] [guardAssert "e"] .empty,
    .loop .nondet none [] [guardAssert "b"] .empty ]

#guard checkNondetElimNoNondetGuard (guardProg nondetBody)
#guard checkNondetElimFreshNames (guardProg nondetBody)
-- Non-vacuous: the input does carry a nondet guard.
#guard (cmdShapedBodies (guardProg nondetBody)).any stmtsHaveNondetGuard

-- `LoopInitHoist` leaves no `init` in a loop body, on a body whose loop declares
-- one.
private def hoistBody : List Statement :=
  [ .loop .nondet none []
      [ Statement.init ⟨"y", ()⟩ (.forAll [] .int) (.det (intLit 1)) .empty ] .empty ]

#guard checkHoistNoLoopBodyInits (guardProg hoistBody)
#guard checkHoistPreservesUniqueInits (guardProg hoistBody)
-- Non-vacuous: the input violates the postcondition the pass establishes.
#guard (cmdShapedBodies (guardProg hoistBody)).all fun ss =>
  !Imperative.Block.loopBodyNoInits ss

-- ── §2.9 Obligation preservation under the symbolic evaluator ─────────────

/-- A nondeterministic `if *` whose then-branch asserts `l`. -/
private def ndIte (l : String) : Statement :=
  .ite .nondet [guardAssert l] [] .empty

/-- The deterministic counterpart, for the contrast below. -/
private def detIte (l : String) : Statement :=
  .ite (.det trueLit) [guardAssert l] [] .empty

/-- The obligation labels the evaluator emits for a body, with no pass in
    between. The bodies below are loop-free, so `LoopElim` is a no-op on them and
    `elimObligationLabels` is just "evaluate this". -/
private def obligationsOf (ss : List Statement) : Option (List String) :=
  elimObligationLabels (guardProg ss)

-- **The evaluator drops proof obligations after a second `if *`.** Pinned here
-- because it is the reason `checkNondetElimSymbolicNoLoss` is containment and not
-- equality, and because nothing else in the tree records it. One `if *` is fine:
#guard obligationsOf [ndIte "a", guardAssert "after"] == some ["a", "after"]
-- Two are not — `b` is gone, and so is the `assert` that follows both:
#guard obligationsOf [ndIte "a", ndIte "b"] == some ["a"]
#guard obligationsOf [ndIte "a", ndIte "b", guardAssert "after"] == some ["a"]
-- The obligation *before* the second `if *` survives, which locates the stop
-- exactly at the second nondeterministic guard:
#guard obligationsOf [ndIte "a", guardAssert "mid", ndIte "b"] == some ["a", "mid"]
-- Deterministic guards at the same depth are unaffected, so the defect is about
-- the nondet path and not about `.ite` in general:
#guard obligationsOf [detIte "a", detIte "b"] == some ["a", "b"]
-- And it is not depth as such: nesting one `if *` inside another gives the two of
-- them different path-condition depths, so both obligations survive.
#guard obligationsOf [.ite .nondet [guardAssert "a", ndIte "b"] [] .empty] == some ["a", "b"]

-- The mechanism, pinned directly: the name the evaluator mints for the guard is
-- `$__nondet_cond_{path-condition depth}` (`StatementEval.lean:586`), so a source
-- program that declares that very name collides with the *first* `if *` — and the
-- whole procedure's obligation list goes empty, with no diagnostic anywhere.
private def collidingNondetName : Statement :=
  Statement.init ⟨"$__nondet_cond_2", ()⟩ (.forAll [] .bool) (.det trueLit) .empty

/-- The same declaration under a name the evaluator will never mint — the control
    for the guard below, so the effect is attributed to the collision and not to
    the extra `init`. -/
private def innocentNondetName : Statement :=
  Statement.init ⟨"$__nondet_cond_99", ()⟩ (.forAll [] .bool) (.det trueLit) .empty

#guard progTypeChecks (guardProg [collidingNondetName, ndIte "a", guardAssert "after"])
#guard obligationsOf [collidingNondetName, ndIte "a", guardAssert "after"] == some []
#guard obligationsOf [innocentNondetName, ndIte "a", guardAssert "after"]
        == some ["a", "after"]

-- `NondetElim` repairs it: after the pass there is no `if *` left for the
-- evaluator to mint a name for, so both obligations come back. This is the growth
-- that makes an equality claim wrong.
#guard (nondetElimProgram (guardProg [ndIte "a", ndIte "b"]) |> fun p =>
  (cmdShapedBodies p).all fun ss => !stmtsHaveNondetGuard ss)
#guard vcElimObligationLabels (guardProg [ndIte "a", ndIte "b"]) == some ["a"]
#guard (vcElimObligationLabels (nondetElimProgram (guardProg [ndIte "a", ndIte "b"]))).any
  fun ls => ls.contains "a" && ls.contains "b"
-- So the property holds, and holds because nothing was lost — not because the two
-- sides agree.
#guard checkNondetElimSymbolicNoLoss (guardProg [ndIte "a", ndIte "b"])

-- `InsertLoopInvariantAsserts`: the baseline owes `a`, and the pass's output owes
-- `a` plus the six verification conditions the two invariants and the measure
-- license. Growth in the right direction, and nothing dropped.
#guard checkLoopVcSymbolicNoLoss (guardProg [twoInvariantLoop])
#guard elimObligationLabels (bareLoopsProgram (guardProg [twoInvariantLoop])) == some ["a"]
#guard (vcElimObligationLabels (guardProg [twoInvariantLoop])).any fun ls =>
  ls.contains "a" &&
    (countPrefixed Core.insertLoopInvAssertPrefix ls) == 6
-- The baseline really is loop-eliminable only because the annotations were
-- stripped: `LoopElim` throws on the annotated program.
#guard (runPhase Core.loopElimPipelinePhase (guardProg [twoInvariantLoop])).isNone
#guard (runPhase Core.loopElimPipelinePhase (bareLoopsProgram (guardProg [twoInvariantLoop]))).isSome

-- `LoopInitHoist`: the obligation set is preserved exactly here, on a loop that
-- declares an `init` the pass has to hoist and an `assert` after the loop.
private def hoistObligationBody : List Statement :=
  [ .loop (.det trueLit) none []
      [ Statement.init ⟨"y", ()⟩ (.forAll [] .int) (.det (intLit 1)) .empty,
        guardAssert "b" ] .empty,
    guardAssert "after" ]

#guard checkHoistSymbolicNoLoss (guardProg hoistObligationBody)
-- Non-vacuous, and exact: both sides emit the same two obligations, and the pass
-- really did move the `init` out of the loop body.
#guard vcElimObligationLabels (guardProg hoistObligationBody) == some ["b", "after"]
#guard vcElimObligationLabels (loopInitHoistProgram (guardProg hoistObligationBody))
        == some ["b", "after"]
#guard (cmdShapedBodies (guardProg hoistObligationBody)).all fun ss =>
  !Imperative.Block.loopBodyNoInits ss
#guard (cmdShapedBodies (loopInitHoistProgram (guardProg hoistObligationBody))).all
  Imperative.Block.loopBodyNoInits

-- The sharpest form of the evaluator defect, and the one the random generator
-- actually produced (a draw of size 129, shrunk to 16 and then tidied): a
-- procedure whose postcondition is `false` — unverifiable by construction —
-- together with two *empty* `if *`. The blocks assert nothing and assign nothing;
-- they only consume the minted name. The obligation list comes back **empty**, so
-- a verifier has nothing to prove and reports success. See
-- `docs/measurements/nondet-cond-collision-witnesses.lean` for the search that
-- found it and repo issue #113 for the report.

/-- `procedure P (out r : int) ensures [post]: false { ss }`. The postcondition
    makes the procedure unverifiable, so its obligation must reach the evaluator. -/
private def ensuresFalseProg (ss : List Statement) : Program :=
  { decls := [.proc
      { header := { name := ⟨"P", ()⟩, typeArgs := [], inputs := [],
                    outputs := [(⟨"r", ()⟩, .int)], noFilter := false }
        spec := { preconditions := [],
                  postconditions := [("post", { expr := .const () (.boolConst false) })] }
        body := .structured ss } .empty] }

/-- An empty nondeterministic `if *`, which contributes nothing but the name. -/
private def emptyNdIte : Statement := .ite .nondet [] [] .empty

-- Varying only the number of empty `if *` isolates the defect: zero and one are
-- correct, two loses the postcondition entirely, and a deterministic guard never
-- loses it.
#guard vcElimObligationLabels (ensuresFalseProg []) == some ["post"]
#guard vcElimObligationLabels (ensuresFalseProg [emptyNdIte]) == some ["post"]
#guard vcElimObligationLabels (ensuresFalseProg [emptyNdIte, emptyNdIte]) == some []
#guard vcElimObligationLabels
  (ensuresFalseProg [.ite (.det trueLit) [] [] .empty, .ite (.det trueLit) [] [] .empty])
    == some ["post"]
-- `NondetElim` brings it back, which is the growth that makes an equality claim
-- wrong for `checkNondetElimSymbolicNoLoss`.
#guard vcElimObligationLabels (nondetElimProgram (ensuresFalseProg [emptyNdIte, emptyNdIte]))
    == some ["post"]
#guard checkNondetElimSymbolicNoLoss (ensuresFalseProg [emptyNdIte, emptyNdIte])

-- All three are vacuous on a program with a nondeterministic measure-carrying
-- loop, since `InsertLoopInvariantAsserts` throws on it and neither side reaches
-- the evaluator. Pinned so the guard is not silently doing nothing.
private def nondetMeasureProg : Program :=
  guardProg [.loop .nondet (some (intLit 3)) [] [guardAssert "a"] .empty]

#guard hasNondetMeasureLoop nondetMeasureProg
#guard checkLoopVcSymbolicNoLoss nondetMeasureProg
#guard checkNondetElimSymbolicNoLoss nondetMeasureProg
#guard checkHoistSymbolicNoLoss nondetMeasureProg

end Guards

end StrataGenerators.Program.UnprovenTransforms
