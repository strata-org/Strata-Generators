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
# The properties for the Core transform passes that have no correctness proof

This module holds the check predicates for the passes of `Strata/Transform/` that carry no
machine-checked correctness argument. Each predicate takes a **whole generated program**, which is a
`Core.Program` from `ProgramGen.genProgram` with a proof of soundness against `ProgramHasTypeA`, and it
gives a `Bool`. Both harnesses evaluate the same predicate, and the whole-program shrinker minimizes a
counterexample.

## The passes that this module covers

Only four passes of `Strata/Transform/` have a companion file with a correctness proof. These eight
passes have no such file, and no theorem in the file of the pass itself:

`StructuredToUnstructured`, `LoopElim`, `InsertLoopInvariantAsserts`, `CommonSubexprElim`,
`FunctionInlining`, `ProcedureInlining`, `TerminationCheck` and `IrrelevantAxioms`.

Two more passes, which are `NondetElim` and `LoopInitHoist`, prove lemmas about syntactic preservation.
Neither of them proves its own main postcondition, so this module also covers both of them.

This module does **not** cover `TerminationCheck`. A property about that pass needs a recursive
function, and the generator cannot make one. Each such property would therefore say nothing about the
pass, and it would give a false signal of coverage.

## Why the input is a whole program, and not a statement list

Three of the passes are `PipelinePhase` values from a program to a program, and each of them reads a
declaration that is not a procedure. `IrrelevantAxioms` reads the axioms and the call graph of the
functions. `ProcedureInlining` reads the declaration of the callee at each call site.
`FunctionInlining` reads the body of a function out of the factory. A statement list holds none of
those. Therefore the input here is the whole program that `ProgramGen.genProgram` draws, which holds
each kind of declaration. The two purely structural passes, which are `StructuredToUnstructured` and
`NondetElim`, take a statement list, so each property applies such a pass to each procedure body of the
program.

## The guard for the typechecker

`Program.typeCheck` rejects a large part of the generated programs, for three reasons that the module
docstring of `ProgramGen/Shrink` gives. A pass is responsible only for what it does to input that is
already well typed. Therefore each predicate that the guard concerns starts with `!progTypeChecks p ||`.
That guard makes the predicate empty on a rejected draw, and a real claim on each other draw. A separate
property pins the three known causes of a rejection, so a new cause becomes visible there, and this
module filters nothing in silence.

## The functions of the program in the factory

`FunctionInlining` reads the body of a function from a `Lambda.Factory`, and `Core.Factory` holds **no**
function body. Therefore a property that runs the pass against `Core.Factory` alone can inline nothing,
and it says nothing about the pass. `programFactory` therefore pushes each function that the *program*
declares into `Core.Factory`. `Core.Verifier` does the same in production. A generated function has a
body about half of the time, so each property about inlining has real input.

## Coverage

Each property states the true claim, and it is not weakened, so it reports a defect and does not hide
one. Two limits of the coverage are recorded where they belong:

* `checkKleeneMeasureAccepted` describes the behaviour of the pass, and it is not an oracle for a
  defect. Its own docstring gives the reason.
* The four properties about `CommonSubexprElim` are usually silent on generated input, because the pass
  acts only on a duplicate subexpression, and a generated body rarely holds one. A `#guard` exercises
  each of them at each build. Read the note about `CommonSubexprElim`.

A `#guard` covers each of the four properties about `CommonSubexprElim` on input that a person wrote. A
`#guard` also covers each of the four properties about `FunctionInlining`. One of those guards uses a
chain of two functions, where the results at the fuel 1 and at the fuel 4 differ.

## What each family of properties checks

* **IrrelevantAxioms.** The oracle for *relevance*, and not the `changed` flag, which a separate
  property covers. There are five properties: the pass removes an `.ax` declaration only, the order of
  the declarations holds, each axiom that stays is relevant, each axiom that the pass removes is
  irrelevant, and the pruned program still type checks.
* **StructuredToUnstructured.** Seven structural properties about the control-flow graph that the pass
  emits: no target dangles, the labels are different in pairs, the entry label exists, there is exactly
  one `.finish` block, each block is reachable from the entry, the count of the commands holds after the
  commands that the pass builds, and the `.cfg` body prints.
* **LoopElim and InsertLoopInvariantAsserts.** The accounting of the verification conditions: the exact
  count of each `assert` and each `assume` that the pass inserts, as a function of the number of the
  invariants, a bare loop after the pass, idempotence, the counter for the statistics, and the survival
  of each verification condition through `LoopElim`.
* **CommonSubexprElim.** A fresh name that collides with no other name, the `assert` labels, the order
  of the fresh declarations, and an output that type checks.
* **FunctionInlining.** The identity at the fuel 0, growth with the fuel, preservation of a type, and
  freedom from capture.
* **ProcedureInlining.** Labels that are different in pairs after two call sites, the count of the
  `assert` labels, the counters for the statistics, and a well-formed call graph.
* **NondetElim and LoopInitHoist.** The main postcondition of each pass, which neither file proves. No
  `.nondet` guard stays, and each loop body holds no `init`.
* **The three loop passes under the symbolic evaluator.** Whether `InsertLoopInvariantAsserts`,
  `NondetElim` and `LoopInitHoist` change the proof obligations that reach SMT. The two families above
  state their claims about the syntax. These three properties go through the executable evaluator of
  Strata instead. That evaluator is the only oracle that can see an obligation that survives as *syntax*
  and that the pipeline never emits. The evaluator refuses a loop, so each side runs `LoopElim` first.
  Each of the three properties states that no obligation is lost, and the note of that section gives the
  reason why an equality would be the wrong claim.
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

Two families of properties below compare the *proof obligations* of a pass before and after the pass
runs. For `IrrelevantAxioms`, the set of the obligations must be **the same**. For
`ProcedureInlining`, it must not become **smaller**. Both families use the executable symbolic
evaluator of Strata, which is the `symbolicEval` phase of `corePipelinePhases`, together with the
`nondetElim` phase that comes before it there.

**The evaluator panics on a loop.** `Core.Statement.evalOneStmt` stops with a message that asks the
caller to eliminate each loop first. That message is why `loopElimPipelinePhase` comes immediately
before `symbolicEval` in `transformPipelinePhases`. A panic is not catchable. Therefore a property
that uses this oracle must first screen the input with `programHasLoop`, and it must not rely on the
`none` branch.

**The evaluator rejects a nondeterministic guard.** Therefore this oracle runs
`nondetElimPipelinePhase` in front of it, as `corePipelinePhases` does. A call to `symbolicEval`
alone would refuse each draw that holds an `if *` or a `while *`. Each property here reads the
resulting `none` as "there is no claim to make", so a whole class of shapes would go unscored in
silence. -/

/-- The program of the obligations that the symbolic evaluator of Strata gives, or `none` when it
    raises a diagnostic. The function calls the `nondetElim` phase and the `symbolicEval` phase of
    `corePipelinePhases` directly, in that order. The evaluator rejects a nondeterministic guard
    that stays, so the two phases are one step here. Read the note of this section.

    The call uses `VerifyOptions.quiet`, and not `.default`. At the verbosity `.normal` or above, the
    evaluator traces the whole list of the obligations, which would write that list into the output
    of each build and of each draw. `.quiet` differs from `.default` in that field only.

    **Never call this function on a program that holds a loop.** Read the note of this section. -/
def symbolicObligations (p : Program) : Option Program :=
  match runPhase Core.nondetElimPipelinePhase p with
  | none => none
  | some (_, q) =>
    match Core.toCoreProofObligationProgram Core.VerifyOptions.quiet q with
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

/-! ## `IrrelevantAxioms`: the oracle for relevance

`irrelevantAxiomsPipelinePhase` removes each axiom that its computation of a fixed point finds
irrelevant to a seed set of function names. A separate property pins the `changed` flag, which the pass
sets to `true` always. This family checks whether the pass removes the **correct** axioms.

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
    (`IrrelevantAxioms.lean`), and `LExpr.getOps` gives the functions of the
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

/-- **The removal of an axiom leaves the proof obligations unchanged.** This property is the semantic
    companion of the five syntactic properties above, and it is the sharpest claim about this pass that
    needs no solver.

    An axiom is an *assumption*, and it is never an obligation. Therefore the removal of an axiom cannot
    add, remove or rename an obligation. The set of the obligations before the pass and the set after it
    must therefore be **equal**. For `ProcedureInlining`, containment is the correct claim, because the
    obligations of that pass duplicate at each call site. Equality is the correct claim here, because this
    pass must change nothing that reaches the solver.

    The oracle is the `symbolicEval` phase of Strata. Therefore this property compares the obligations
    that a verification run receives.

    ### What the property catches, and what it does not catch

    It catches a change to the *structure* of an obligation, which is an addition, a removal or a new
    label. It does **not** catch the most important failure: the pass removes an axiom that an obligation
    needs, and the obligation then stays but is not provable. That failure is invisible with no solver,
    because the expression of the obligation does not change, and only its *provability* differs. A check
    of that kind needs the oracle behind the `--smt` gate.

    This property is therefore a necessary condition for the `modelPreserving` annotation of the pass, and
    it is not a sufficient one. It says that the pass did not change the obligations. It does not say that
    the pass kept them provable.

    ### Coverage

    The claim holds under two guards: the input type checks, and it holds **no loop**. The symbolic
    evaluator panics on a loop. Read the note about the oracle. -/
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

/-! ## `StructuredToUnstructured`: the structural properties

`stmtsToBlocks` (`StructuredToUnstructured.lean`) threads a continuation label
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
    `StructuredToUnstructured.lean`). A nested list under a `.block`, an `.ite`
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
    invalid exit (`| .none => k`, with the comment "We assume a prior
    check to avoid this"), this is where a defect is most likely. -/
def checkS2uNoDanglingLabel (p : Program) : Bool :=
  (programBodies p).all fun ss =>
    let c := bodyCfg ss
    let labels := cfgLabels c
    (cfgTargets c).all labels.contains

/-- **Distinct block labels.** Two blocks under one label make the CFG
    ill-defined: `blocks.lookup` would find the first one and drop the second.

    Conditional on the source body already having distinct `.block` labels, and it
    must be: `genFreshLabel` (`StmtHasTypeAGen/Core.lean`) draws a label fresh
    against the *enclosing* labels only, which is what the `block` premise of the
    typing spec requires, so two **sibling** blocks may share a label. A body such as
    `j: { } j: { }` is therefore generatable, and it makes the emitted CFG hold two
    blocks named `j`. That result is not a fault of this pass, which copies the label of the source.
    Blaming the pass for that would report a generator artefact as a Strata defect,
    the same way the `procInline` label property has to guard against `genIdentName`
    drawing one name twice.

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

/-- **Each block is reachable from the entry.** An orphan block is dead code that
    the pass emitted and no path can enter, which points at a continuation the
    threading dropped. -/
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

/-- **A `.cfg` body prints.** The oracle is the formatter's own error banner,
    which `Core.formatProgram` appends when the conversion collected an error, so
    the property needs no access to the private error array.

    `StructuredToUnstructured` is the only pass in the tree that makes a `.cfg`
    body, so nothing else produces the constructor and no other property can reach
    this hole. The `#guard`s at the end of this file pin it.

    The property is vacuous on a program with no procedure: there is then no `.cfg`
    body to print. -/
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

/-! ## `LoopElim` and `InsertLoopInvariantAsserts`: the accounting of the
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
    (`InsertLoopInvariantAsserts.lean`), so a property about the pass's output
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
    (`InsertLoopInvariantAsserts.lean`). The generator can draw exactly this
    shape: `genCondOrNondet` gives `.nondet` about 20 percent of the time and
    `genOptMeasure` gives a measure about 75 percent of the time.

    Stated as a biconditional, so it catches both a missed rejection and a
    spurious one. -/
def checkLoopNondetMeasureThrows (p : Program) : Bool :=
  (runPhase loopInvPhase p).isNone == hasNondetMeasureLoop p

/-- **`LoopElim` mints distinct block labels.**

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

/-! ## `DetToKleene`: the measure that the transform drops

`StmtToKleeneStmt` (`DetToKleene.lean`) rejects a loop that carries an
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
signal.

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
    transform returns `some`. It is a characterization rather than a bug oracle: it
    pins the fact that a measure does not make the transform undefined, so a future
    change that starts rejecting a measure-carrying loop (which is one of the two
    possible corrections) breaks it and forces the question to be answered in the
    open.

    The complement is what would make it a bug oracle, and stating that would need
    a decision about which side is wrong, which the issue leaves open. -/
def checkKleeneMeasureAccepted (p : Program) : Bool :=
  (programBodies p).all fun ss =>
    !(hasMeasureOnlyLoop ss && !hasKleeneUnsupported ss && !hasInvLoopStmts ss) ||
      (kleeneStmts ss).isSome

/-! ## `CommonSubexprElim`: the fresh names and the order

The repository already checks that CSE leaves no dangling bound variable and that
symbolic evaluation agrees. What remains is the fresh-name discipline. CSE mints
`$__cse.{idx}` from a counter that never reads the program's names
(`CommonSubexprElim.lean`), and it prepends each new `var` declaration to the
body, so both a collision and a wrong order are possible in principle.

**The pass acts on very few generated programs.** It acts only when a procedure body holds a
*duplicate* subexpression, and a generated body rarely holds one. The generator draws each expression
on its own, so two identical subterms of a real size rarely occur together. Therefore these four
properties are usually silent on generated input, and the `#guard`s at the end of this file are what
exercise them at each build.

They are not silent *always*. `cseCapturingBody` pins one defect that a draw can reach: the pass lifts
an extracted subexpression above the declaration of a variable that the subexpression names. Read a
green result for these four properties as "the pass rarely ran", and not as a claim about the pass. The
`decl_kinds` axis and the `program_size` axis of the Tyche panel say whether a run reached the pass.

To reach the pass *often*, a generator must put a repeated subterm into a body on purpose. Of these
four items, this is the one whose likely route, which is a construct for sharing in `genLExpr`, adds a
case to the soundness proof of `genLExpr`. A step after generation avoids that proof, at the price of a
less principled distribution. -/

/-- Each `init` name of a statement list, at any depth, in order of appearance.
    Reuses the procedure test support's `stmtsInits`, whose traversal the ANF
    properties already share, and keeps only the name. -/
def bodyInitNames (ss : List Statement) : List String :=
  (stmtsInits ss).map fun (n, _) => CoreIdent.toPretty n

/-- **A fresh CSE name does not collide.** No `$__cse.N` name may be declared two
    times in an output body. The index comes from a counter that starts at 0 for
    each program and never reads a program name
    (`CommonSubexprElim.lean`), so a body that already declares `$__cse.0`
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
    (`CommonSubexprElim.lean`) and accumulates them **reversed**, then
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

/-- **The CSE output typechecks. FAILS.**

    The pass prepends every extracted `var $__cse.{idx}` to the *front* of the
    procedure body, without regard for where the variables of the extracted
    subexpression are declared. So a duplicated subexpression mentioning a local is
    hoisted above that local's declaration, and the output is rejected with
    `No free variables are allowed here!`. Pinned deterministically by
    `cseCapturingBody` below, and reached on a generated draw only when the body
    happens to hold a duplicate, which is rare.

    Conditional on the input typechecking, so the pass is not blamed for input the
    checker rejects on its own. -/
def checkCseOutputTypechecks (p : Program) : Bool :=
  !progTypeChecks p ||
    (match runPhase Core.commonSubexprElimPhase p with
     | some (_, out) => progTypeChecks out
     | none => true)

/-! ## `FunctionInlining`: a transform of an expression only

`inlineFuncDefs` (`FunctionInlining.lean`) is a pure `LExpr → LExpr` transform,
which makes it the pass that is easiest to test well. It relies on
`substFvarsLifting` for capture safety under a binder, and on
`LFunc.computeTypeSubst` for polymorphic instantiation.

The factory matters. `Core.Factory` holds **no** function body, so the pass over `Core.Factory` alone is
the identity. `programFactory` therefore pushes each function that the program declares, and
`Core.Verifier` does the same in production.

Four parts of the generator must work together, or a property about this pass reaches the pass on almost
no draw:

1. **`GenState.octx` must grow across the fold over the declarations.** A declaration of a function
   grows `C`, so the typechecker knows the function. A body can name the function only when `octx` also
   holds it, so `genDeclFunction` registers each declared function there.
2. **`programExprs` must read more than a procedure body.** The pass acts inside a *function* body or a
   `requires` clause, because a function that the fold declares later sees the larger vocabulary.
   Therefore `programExprs` also reads each function body, each precondition and each axiom body.
3. **A polymorphic function needs its own context.** Most declared functions are polymorphic, and an
   `OpCtx` holds one monotype for each operator. Therefore `funcOpEntry` cannot take such a function, and
   `funcPolyOpEntry` sends it to `pctx`.
4. **The selection of an operator dilutes a single entry.** `genIndir` and `genIndirPoly` draw with
   `elements`, which is *uniform* over the candidates for the target type, and `Core.Factory` gives more
   than a hundred operators that give a `bool`. Therefore one entry for a declared function has a very
   small share at a `bool` leaf, and a draw almost never selects it. Two definitions handle this.
   `declaredFuncWeight` repeats the entry to raise its share, and its docstring gives the details.
   `synthesizedCalls` builds one full call for each declared function that has a body, so a property
   does not depend on a lucky draw at all.

Item 4 is the largest of the four. A larger vocabulary is necessary, and it alone is far from enough. -/

/-- A saturated call to each function the program declares, with each argument taken
    from the function's own body if the body is a suitable closed term, and otherwise
    from a default value of the parameter's type.

    **Why this function builds a call site.** `inlineFuncDefs` is a transform from an `LExpr` to an
    `LExpr`, so a property about it is a property about an *expression*, and not about a program. The
    program gives the factory only. A property that waits for the generator to draw a body that calls a
    declared function depends on the limit for the declarations and on the odds of the selection of an
    operator. Under those odds, very few draws hold such a call.

    A call that this function builds removes that dependence. The call has exactly the shape that
    `Factory.callOfLFunc` accepts, which is the operator with an annotation of its curried type, applied
    to one argument for each formal parameter. Therefore it reaches the same path as a generated call,
    including `LFunc.computeTypeSubst` for a polymorphic function. This function does *not* build the
    function itself. `genFunction` draws its name, its signature, its body and its type parameters.

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

    The sites that are not a procedure body are the important ones, because the pass acts there on
    generated input. `genDeclFunction` adds each monomorphic function that it declares to `octx`.
    Therefore the body or the `requires` clause of a *later* function can call an earlier one. A
    procedure body must be generated after that growth, and it must also draw the correct operator,
    which happens less often. A list of the procedure bodies alone therefore leaves each property about
    `FunctionInlining` with no input.

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
    the docstring states (`FunctionInlining.lean`), which the `maxDepth`
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

/-! ### Preservation of a value under the concrete evaluator

This is the sharpest oracle for `FunctionInlining`. The inlining of a call must not change the value
that the expression *evaluates to*.

**The comparison needs one step to be meaningful.** `LExprEval.eval` unfolds the body of a function only
when the function holds the `.inline` attribute, or an `inlineIf*` variant whose side condition holds.
`inlineFuncDefs` unfolds **each** full call whose function has a body. That difference is deliberate,
and the module docstring of `FunctionInlining` records it. Therefore a comparison of `eval e` against
`eval (inline e)` over the *plain* factory compares two different notions of an unfolding, and the two
sides disagree on each sample. `eval e` stops at the call, which it cannot interpret, and
`eval (inline e)` reduces to a value. That is a defect in the oracle, and not in the pass.

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
    substitute the environment and stop (`LExprEval.lean`) rather than
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

    This is the property the test plan asks for, in the form the two evaluators
    make available. It is stronger than the four syntactic properties beside it: those
    constrain the *shape* of the result (its type, its free variables, its remaining
    inlinable calls), whereas this one constrains its *meaning*. A substitution that
    captured a variable, instantiated a type parameter wrongly, or dropped an
    argument would pass all four and fail this one.

    The property has real content, because the transform acts on many expressions of a generated program, and
    the inlined side of many of them reduces to a canonical value.

    ### Two boundaries the claim has to respect

    Both were found by the property failing, and both are documented behaviour of
    `LExprEval.eval` rather than defects, so the claim is scoped around them:

    1. **`eval` does not descend under a binder.** The `.abs` and `.quant` cases
       substitute the environment and stop (`LExprEval.lean`); they do not
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
    of what the test plan proposes and is left to follow-up work. -/
def checkInlineEvalAgreement (p : Program) : Bool :=
  let Fplain := programFactory p
  let Finl := inlineEvalFactory p
  (programExprs p).all fun e =>
    let out := Strata.inlineFuncDefs Fplain (e := e)
    -- Vacuous when the transform did nothing or when a binder puts the two
    -- traversals on different footings; a genuine claim otherwise.
    decide (out = e) || exprHasBinder e ||
      decide (evalOver Finl e = evalOver Finl out)

/-! ## `ProcedureInlining`: the renaming of the labels

`replaceLabelsOfBlocksAndAssertAssumes` (`ProcedureInlining.lean`) renames each
block, `assert`, `assume` and `cover` label when it inlines a body. The classic
defect is a name that is not unique when one procedure is inlined at two call
sites, so the properties below are about the labels and about the statistics
counters the pass maintains by hand.

`genCallStmt` is wired into `genProcedure` and the whole-program
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

/-- **Inlining introduces no duplicate label.** Each label the pass

    A duplicate label makes two proof obligations share a name, and a verifier
    reports an obligation by name, so the two obligations become
    indistinguishable in the report.

    The claim is conditional on the input having distinct labels, and it must be:
    the generator draws an `assert`, `assume` and `cover` label from `genIdentName`,
    and two draws can coincide, so a program can hold two statements under one label
    before any pass runs. Blaming the pass for those would report a generator
    artefact as a defect of Strata. Under the guard, the property is a real claim about the pass.

    The generator rarely reaches the shape, because few draws hold two calls or more. The `#guard`s at
    the end of this file pin each of the two causes separately, so neither one depends on a lucky
    draw. -/
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
    first only after the second (`ProcedureInlining.lean`), and the call
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

/-- **The inlined program typechecks.** Inlining rewrites a call into an
    `init` for each input, a nondeterministic `init` for each output, the callee's
    body, and a `set` for each result. Each renamed variable must stay in scope and
    keep its type, so an output the checker rejects means the renaming or the
    parameter passing is wrong.

    The deterministic guard at the end of this file pins the known shape on a
    two-line program.

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
statement list, because `StatementSemantics.lean` gives a relation only. It does have an
executable **symbolic** evaluator, `toCoreProofObligationProgram`, which is the phase
`corePipelinePhases` runs under the name `symbolicEval`. It turns a program into a
program of proof obligations, so it is exactly the differential oracle available here.

**What the property can claim, and what it cannot claim.** A comparison of the two programs of
obligations for equality is the wrong claim:

```
obligations BEFORE: [inner]
obligations AFTER:  [inner, Callee_inner_1, Callee_inner_3]
```

That difference is the *purpose* of the inlining, and not a defect. Before the pass, one proof covers a
callee, and each call site assumes its contract. After the pass, a proof covers the body of the callee
again at each call site. Therefore the multiset of the obligations grows, and a claim of equality would
report correct behaviour as a defect.

What holds, and is worth pinning:

1. **No obligation is lost.** Every obligation label present before inlining is still
   present after. A lost obligation is a lost proof, which is the failure mode that
   turns a `sat` into a false `pass`.
2. **The evaluator does not start failing.** If symbolic evaluation succeeded on the
   input, it must succeed on the output. A pass that produced a program the
   `symbolicEval` phase chokes on would break the pipeline immediately after itself,
   since `ProcedureInlining` runs before that phase. -/

/-- **Inlining loses no proof obligation, and does not break symbolic evaluation.**

    Two claims in one predicate, both conditional on the input typechecking and on
    symbolic evaluation succeeding on it:

    * each `assert` label of the pre-inlining obligation program still occurs in the
      post-inlining one;
    * symbolic evaluation still succeeds after the pass.

    The count is deliberately *not* compared: inlining duplicates the callee's
    obligations at each call site by design, so the multiset grows (measured
    `[inner] → [inner, Callee_inner_1, Callee_inner_3]` on two call sites). Growth is
    correct; shrinkage is not.

    The postcondition side is the mirror image and is not covered here: an `ensures`
    clause is an obligation on the callee and an *assumption* for the caller, so
    dropping it loses an assumption (incomplete, not unsound). Worth a follow-up.

    ### Coverage

    On generated input the pass fires on 0 of 400 typechecking draws, so this
    property is usually vacuous there. The `#guard`s at the end of this file pin it
    deterministically, on a callee whose precondition the caller demonstrably
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

/-! ## `NondetElim` and `LoopInitHoist`: the postconditions with no proof

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
    (two sibling blocks may each declare `x`), and the property is then vacuous:
    the pass makes no promise there. What the property catches is
    a pass that *breaks* uniqueness on input that had it, which is exactly the
    collision the doc warns about. -/
def checkHoistPreservesUniqueInits (p : Program) : Bool :=
  (cmdShapedBodies p).all fun ss =>
    !uniqueInitsB ss || uniqueInitsB (Imperative.Block.hoistLoopPrefixInits ss)

/-! ## The three loop passes under the symbolic evaluator

The two sections above state the claim of each loop pass **about its syntax**. Those claims are a count
of the inserted statements, a postcondition as a `Bool`, and a check on the survival of an `assert`
*label*. None of them asks whether the pass changes the **proof obligations that reach SMT**, which is
the question that the pipeline cares about. This section asks it, for `InsertLoopInvariantAsserts`,
`NondetElim` and `LoopInitHoist`.

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
evaluator does not start failing. Equality is wrong for the first, and stated as
containment for the other two so that they report the direction that matters:

* `InsertLoopInvariantAsserts` *adds* an obligation by design, because that is the purpose of the pass.
  Therefore the set of the obligations must grow, and a claim of equality would report correct
  behaviour as a defect.

* `NondetElim` and `LoopInitHoist` must keep each obligation. Each of the two properties states
  containment, so that it reports a *lost* obligation, which is a lost proof, and it does not report a
  harmless addition.

### `NondetElim` is early-against-late, not with-against-without

The evaluator refuses a program that still holds an `if *` / `while *`, and
`symbolicObligations` therefore runs `nondetElimPipelinePhase` in front of it, the
way `corePipelinePhases` does. There is consequently no "without the pass"
baseline left for `checkNondetElimSymbolicNoLoss` to use: a program that reaches
the evaluator at all has had `nondetElim` applied to it.

What the property compares instead is *where* the elimination happens.
`nondetElimProgram` rewrites each procedure body at the source, before
`InsertLoopInvariantAsserts` and before `LoopElim`. The phase of the oracle rewrites the output of those
two passes. Both sides then evaluate. The claim is that an earlier elimination loses no obligation. That
earlier position is before a pass that reads a loop guard, and before a pass that rewrites a `while *`
into an `if *`. A caller who wants to normalize each nondeterministic guard first must ask that
question.

### Why the oracle runs `nondetElim` itself

`Core.Statement.eval` and `toCoreProofObligationProgram` **reject** a nondeterministic guard that
survives, and `nondetElimPipelinePhase` sits immediately before `symbolicEval`, so that no such guard
reaches the evaluator. `nondetElim` replaces each `if *` with a havoc of a fresh variable of the form
`$__ndelim_ite$`, drawn from a monotone counter in a `StringGenState`.

The oracle here runs that phase itself, and it does not let the rejection happen. A rejection would turn
each draw that holds an `if *` into a silent skip, because every property here reads the resulting
`none` as "there is no claim to make". The `#guard`s at the end of this file hold the obligation lists
for a set of small bodies with an `if *`, so a change to this behaviour becomes visible there. -/

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
    A body that holds a procedure call does not convert, because `toCmdStmts` gives `none` for it. The
    function then gives that body back unchanged, and it does not drop the body. The pass does not apply
    there, and `cmdShapedBodies` measures how often that happens. -/
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
    `LoopElim` threw, or it left a loop behind, or `symbolicObligations` raised a
    diagnostic.

    `LoopElim` runs *before* the `nondetElim` that `symbolicObligations` performs, and that is the
    production order. `loopElimPipelinePhase` is a part of `transformPipelinePhases`, and
    `nondetElimPipelinePhase` comes immediately before `symbolicEval`. The order matters in at least one
    direction, because `LoopElim` rewrites a `while *` into an `if *`. A `nondetElim` before `LoopElim`
    would therefore have to run again after it.

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

/-- The labels of the obligations of `p`, after `InsertLoopInvariantAsserts` and then `LoopElim`. That
    is the production order, and it is the chain that both sides of a comparison use for the two
    structural passes of this section. -/
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
    states), or when the baseline itself does not reach the evaluator, because there is then nothing to
    compare against. An output of the pass that *stops* reaching the evaluator is a failure, and not a
    skip.

    The two guards cost little coverage, and few generated programs hold an invariant or a measure for
    the pass to insert. That small subset is
    what the `#guard`s at the end of this file are for. Passes on every draw. -/
def checkLoopVcSymbolicNoLoss (p : Program) : Bool :=
  !progTypeChecks p || hasNondetMeasureLoop p ||
    (match elimObligationLabels (bareLoopsProgram p) with
     | none => true   -- no baseline: no claim to make
     | some before =>
       match vcElimObligationLabels p with
       | none => false   -- the pass broke the chain to the evaluator
       | some after => labelsRetained before after)

/-- **Eliminating nondeterminism early loses no proof obligation under the
    symbolic evaluator.** Both sides run the production chain
    `InsertLoopInvariantAsserts` then `LoopElim` and then the evaluator, and the
    evaluator's own chain begins with `nondetElimPipelinePhase`, so *both* sides
    have their nondeterminism eliminated. The two differ only in **when**: the
    after-side has `Imperative.Block.nondetElim` applied to the procedure bodies at
    the source, ahead of the two structural passes, while the before-side leaves it
    to the phase inside `symbolicObligations`.

    There is no baseline without an elimination. The evaluator rejects a nondeterministic guard that
    survives, so a program reaches the evaluator only after an elimination. Read the note of this
    section.

    The property states containment, for uniformity with the other two properties of this section.

    The property says nothing when the input does not type check, and when it holds a nondeterministic
    loop that carries a measure. That second guard does real work here, and it is not symmetric.
    `insertInvariantAsserts` throws on such a loop, and `NondetElim` makes each guard deterministic.
    Therefore the early rewrite would *remove* the rejection. The side after the pass would then run
    where the side before it threw, and there would be no baseline for the comparison. -/
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

    The property states containment, so a harmless addition does not break it, and a lost obligation,
    which is a lost proof, does break it.

    Generated input reaches this pass least often of the three, because the pass needs a loop *and* a
    declaration inside that loop. A run can therefore score this property with no real input throughout.
    The `#guard`s below are where the preservation of the obligations of this pass is pinned. -/
def checkHoistSymbolicNoLoss (p : Program) : Bool :=
  !progTypeChecks p || hasNondetMeasureLoop p ||
    !((cmdShapedBodies p).all uniqueInitsB) ||
    (match vcElimObligationLabels p with
     | none => true   -- no baseline: no claim to make
     | some before =>
       match vcElimObligationLabels (loopInitHoistProgram p) with
       | none => false   -- the pass broke the chain to the evaluator
       | some after => labelsRetained before after)

/-! ## The deterministic guards

Each guard below is a small program that a person wrote. Together they pin each dimension that generated
input cannot reach, and each of the three known defects. Therefore a change to any of them breaks the
build.

Generated input cannot reach three things. The first is a name that collides with the prefix that a pass
generates, because `genIdentName` draws no name that starts with `$`. The second is a procedure that the
pass inlines at two call sites, because few generated programs hold two procedures and a call. The third
is a `.cfg` body in the input, because no generator makes one. -/

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

-- ── The three known defects ───────────────────────────────────────────────

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
    index never reads a program name (`CommonSubexprElim.lean`), so this is
    where the collision lands. `genIdentName` draws no `$`-prefixed name, so only
    a hand-built program reaches it. -/
private def cseCollisionBody : List Statement :=
  Statement.init ⟨s!"{Core.CSE.cseVarPrefix}0", ()⟩ (.forAll [] .int) (.det (intLit 9)) .empty
    :: cseFiringBody

-- CSE really fires on `cseFiringBody`, and the fresh name it mints is unique there,
-- so each property is live on a well-behaved input. This matters more than usual,
-- since the pass fires on few generated programs: these guards are what exercise the
-- four properties on every build.
#guard (runPhase Core.commonSubexprElimPhase (guardProg cseFiringBody)).any (·.1)
#guard checkCseFreshNamesFresh (guardProg cseFiringBody)
#guard checkCseAssertLabelsPreserved (guardProg cseFiringBody)
#guard checkCseFreshDeclOrder (guardProg cseFiringBody)
#guard checkCseOutputTypechecks (guardProg cseFiringBody)

/-- `Int.Add(G, 4)`: the same shape as `cseDup`, except that it mentions a variable
    the body **declares**, rather than being closed. -/
private def cseDupLocal : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Add", ()⟩ (some intBinOpTy))
    (.fvar () ⟨"G", ()⟩ (some .int))) (intLit 4)

/-- A body whose duplicated subexpression mentions the local `G`. CSE hoists the
    extracted `var $__cse.0 := int.add(G, 4)` to the front of the body, *above*
    `var G : int := 0`, so `G` is out of scope where the hoisted declaration reads it.

    `cseFiringBody` cannot show this, because its duplicate `Int.Add(3, 4)` is closed
    and hoisting a closed expression to the front is always sound. -/
private def cseCapturingBody : List Statement :=
  [ Statement.init ⟨"G", ()⟩ (.forAll [] .int) (.det (intLit 0)) .empty,
    Statement.init ⟨"a", ()⟩ (.forAll [] .int) (.det cseDupLocal) .empty,
    Statement.init ⟨"b", ()⟩ (.forAll [] .int) (.det cseDupLocal) .empty ]

-- The input typechecks and the pass fires, so the claim is live …
#guard progTypeChecks (guardProg cseCapturingBody)
#guard (runPhase Core.commonSubexprElimPhase (guardProg cseCapturingBody)).any (·.1)
-- … and the output does **not** typecheck:
--   `[init ($__cse.0 : int) := ((~Int.Add …) (G : int) #4)]`
--   `No free variables are allowed here! Free Variables: [G]`
-- Reported upstream. This guard is stated negatively, so it turns red when the pass
-- is fixed, which is when it should be deleted.
#guard !checkCseOutputTypechecks (guardProg cseCapturingBody)

/-- The same firing body, with the duplicated subexpression left unannotated. -/
private def cseBareBody : List Statement :=
  [ Statement.init ⟨"a", ()⟩ (.forAll [] .int) (.det cseDupBare) .empty,
    Statement.init ⟨"b", ()⟩ (.forAll [] .int) (.det cseDupBare) .empty ]

-- **A polymorphic annotation on the output of the pass.** With no annotation on the operator,
-- `dup.typeOf` gives `none`, and the pass emits `var $__cse.0 : α := 3 + 4;`. The typechecker accepts
-- both the input and that output.
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
    the check of the precondition is the *only* proof obligation of the program. Therefore the list of
    the obligations goes from one entry to **zero**. No obligation survives for a reader to compare
    against, and no obligation remains that could hold a new name for the lost one. Therefore nobody can
    reply that the pass absorbed the obligation and did not drop it.

    Before inlining, symbolic evaluation of this program is one line:

        assert [|(Origin_Callee_Requires)pre|]: false;

    The obligation is `false`, because `-1 >= 0` folds to `false`. That obligation is therefore not
    provable, and it correctly reports that the call is illegal. After the pass, the whole inlined block
    is one binding of a variable, and the list of the obligations is empty. -/
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

-- **The pass drops the obligation of the precondition, on the smallest witness.** The input type
-- checks, the symbolic evaluation succeeds on both sides, and the pass acts. Therefore the failure is
-- not an ill-typed input, and not an error of the oracle, and not a no-op. It is a lost proof
-- obligation.
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

-- The contrast case. With an argument that satisfies the precondition, the obligation folds to `true`
-- and not to `false`. Therefore the obligation before the pass is a check on the argument of the caller.
-- The pass still drops that check, which is the point: the pass reads the argument no more than before.
#guard progTypeChecks preconditionSatisfiedProgram
#guard !checkInlineProcSymbolicAgreement preconditionSatisfiedProgram

-- And on the non-empty-body variant the list shrinks rather than emptying, so the
-- defect is not an artifact of the empty body.
#guard progTypeChecks preconditionCallProgram
#guard (symbolicObligations preconditionCallProgram).isSome
#guard !checkInlineProcSymbolicAgreement preconditionCallProgram

/-- A counterexample that the generator produced, in its shrunk form, written out here so that it does
    not depend on a seed.

    Two properties make it a *better* witness than `preconditionCallProgram` above, and this file keeps
    both witnesses:

    * The callee has an **empty body**, so the program of the obligations before the pass holds the check
      of the precondition only. After the pass, the list of the obligations is empty, so the one proof
      obligation of the program is gone, and not one of several.
    * Nothing in it is contrived. The generator drew a beta redex for the precondition, five parameters
      of assorted types, two type parameters, and a procedure whose name is `$`. A reader can reply to a
      witness that a person wrote that no real program has that shape. This witness is what the generator
      gave. -/
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

-- The generated witness typechecks and the pass fires on it.
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

-- The input is real: the pass acts, the symbolic evaluation succeeds on both sides, and the count of the
-- obligations *grows*. That growth is why the property claims containment and not equality. These guards
-- record the growth, so that a later reader does not make the property stronger and false.
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
-- depends on the evaluator being *able* to unfold. Therefore this guard pins that the inlined side
-- reduces to a canonical value under `inlineEvalFactory`. The chain `guardOuter(7) → guardInner(7) → 7`
-- collapses to the literal.
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

/-- A function with no parameter and with a body, so a call to it is a bare `.op` node. That is the
    smallest shape that reaches the boundary of a binder below. -/
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
-- (`LExprEval.lean`) while `inlineFuncDefs` recurses, so `fun q => NF` evaluates
-- to itself on the left and to `fun q => false` on the right. `exprHasBinder`
-- excludes such an expression, and the property therefore holds on such a program. This guard records
-- that the exclusion does real work.
#guard exprHasBinder (.abs () "q" (some .bool) nfCall)
#guard checkInlineEvalAgreement (nullaryFuncProgram (.abs () "q" (some .bool) nfCall))
#guard (let p := nullaryFuncProgram (.abs () "q" (some .bool) nfCall)
        let e : Expression.Expr := .abs () "q" (some .bool) nfCall
        let out := Strata.inlineFuncDefs (programFactory p) (e := e)
        -- Without the exclusion this pair would be reported as a disagreement.
        decide (out = e) == false &&
          decide (evalOver (inlineEvalFactory p) e = evalOver (inlineEvalFactory p) out) == false)

-- ── The measure that `DetToKleene` drops ──────────────────────────────────

-- A loop with a measure and no invariant. The transform is defined there, and the measure is absent
-- from the result. This guard pins the behaviour of `DetToKleene` on the exact shape, and it does not
-- wait for the generator to draw one.
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

-- The property skips a program that holds a loop, and it does not send that program to the evaluator.
-- This guard matters, because the failure is a panic and not a `false`. A property with no screen would
-- stop the whole run instead of reporting a counterexample.
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

-- ── Obligation preservation under the symbolic evaluator ──────────────────

/-- A nondeterministic `if *` whose then-branch asserts `l`. -/
private def ndIte (l : String) : Statement :=
  .ite .nondet [guardAssert l] [] .empty

/-- The deterministic counterpart, for the contrast below. -/
private def detIte (l : String) : Statement :=
  .ite (.det trueLit) [guardAssert l] [] .empty

/-- The labels of the obligations that the evaluator emits for a body, with no *structural* pass between
    them. Each body below holds no loop, so `LoopElim` changes nothing there. `elimObligationLabels` is
    then `nondetElim` followed by the evaluation, which are the two phases that `symbolicObligations`
    runs, in the production order. -/
private def obligationsOf (ss : List Statement) : Option (List String) :=
  elimObligationLabels (guardProg ss)

-- **Each obligation arrives, in source order, after any number of `if *` statements.** This is the
-- property that a reader should check first, because a defect in the evaluator can drop an obligation
-- after a second `if *` in silence. `Core.Statement.eval` and `toCoreProofObligationProgram` *reject* a
-- nondeterministic guard that survives, and `nondetElimPipelinePhase` runs immediately before
-- `symbolicEval` in `corePipelinePhases`, so no such guard reaches them. `symbolicObligations` runs the
-- same pair of phases.
#guard obligationsOf [ndIte "a", guardAssert "after"] == some ["a", "after"]
#guard obligationsOf [ndIte "a", ndIte "b"] == some ["a", "b"]
#guard obligationsOf [ndIte "a", ndIte "b", guardAssert "after"] == some ["a", "b", "after"]
#guard obligationsOf [ndIte "a", guardAssert "mid", ndIte "b"] == some ["a", "mid", "b"]
-- Two controls. The first is a pair of deterministic guards. The second nests one `if *` inside another.
-- Both agree with the pair of sibling nondeterministic guards above, so the answer depends neither on the
-- kind of the guard nor on the nesting.
#guard obligationsOf [detIte "a", detIte "b"] == some ["a", "b"]
#guard obligationsOf [.ite .nondet [guardAssert "a", ndIte "b"] [] .empty] == some ["a", "b"]

-- **A name in the source cannot collide with the name of a generated guard.** `nondetElim` builds each
-- name from a monotone `StringGenState`, under a prefix of its own. Therefore a program cannot predict
-- that name, and the two declarations below give the same obligations. A name that an evaluator derives
-- from the depth of the path condition is predictable, and a program that declares that name empties the
-- whole list of the obligations with no diagnostic.
private def collidingNondetName : Statement :=
  Statement.init ⟨"$__nondet_cond_2", ()⟩ (.forAll [] .bool) (.det trueLit) .empty

/-- The same declaration under a name that no phase generates. This is the control, so that an effect
    belongs to the collision and not to the extra `init`. -/
private def innocentNondetName : Statement :=
  Statement.init ⟨"$__nondet_cond_99", ()⟩ (.forAll [] .bool) (.det trueLit) .empty

#guard progTypeChecks (guardProg [collidingNondetName, ndIte "a", guardAssert "after"])
#guard obligationsOf [collidingNondetName, ndIte "a", guardAssert "after"]
        == some ["a", "after"]
#guard obligationsOf [innocentNondetName, ndIte "a", guardAssert "after"]
        == some ["a", "after"]

-- The oracle runs `nondetElim` on both sides, so `checkNondetElimSymbolicNoLoss` compares an **early**
-- elimination against a **late** one, and not the pass against its absence. `nondetElimProgram` rewrites
-- the source before `InsertLoopInvariantAsserts` and before `LoopElim`, and the phase inside the oracle
-- rewrites after both. The claim is that the earlier position loses nothing.
#guard (nondetElimProgram (guardProg [ndIte "a", ndIte "b"]) |> fun p =>
  (cmdShapedBodies p).all fun ss => !stmtsHaveNondetGuard ss)
#guard vcElimObligationLabels (guardProg [ndIte "a", ndIte "b"]) == some ["a", "b"]
#guard vcElimObligationLabels (nondetElimProgram (guardProg [ndIte "a", ndIte "b"]))
        == some ["a", "b"]
-- Non-vacuous here, and exact: both orders emit the same two obligations on a body
-- the pass really rewrites.
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

-- The sharpest shape for this class of defect, and one that the random generator produced. The procedure
-- has the postcondition `false`, so it is unverifiable by construction, and its body holds two *empty*
-- `if *` statements. Those blocks assert nothing and assign nothing, and they only consume a generated
-- name. A predictable name empties the list of the obligations, so a verifier then has nothing to prove
-- and it reports success. This witness therefore shows such a defect fastest.

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

-- The four cases below differ only in the number of the empty `if *` statements, and in the kind of the
-- guard. All four give `["post"]`, so the number of the `if *` statements does not change what the
-- procedure owes.
#guard vcElimObligationLabels (ensuresFalseProg []) == some ["post"]
#guard vcElimObligationLabels (ensuresFalseProg [emptyNdIte]) == some ["post"]
#guard vcElimObligationLabels (ensuresFalseProg [emptyNdIte, emptyNdIte]) == some ["post"]
#guard vcElimObligationLabels
  (ensuresFalseProg [.ite (.det trueLit) [] [] .empty, .ite (.det trueLit) [] [] .empty])
    == some ["post"]
-- Rewriting the guards early, before `InsertLoopInvariantAsserts` and `LoopElim`,
-- gives the same answer as leaving them to the oracle's own `nondetElim` phase.
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
