import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import Strata.Languages.Core.StatementType
import Strata.Languages.Core.Factory
import Strata.Transform.LoopElim
import Strata.Transform.DetToKleene
import Strata.Transform.CommonSubexprElim

open Lambda RandomChoice Core Imperative
open StrataGenerators.Stmt

/-!
# Shared test support for the `StmtHasTypeAGen` generator

Utilities shared between the LSpec property suite and the Tyche panels (both in
the merged `TestMain` driver) for property-based testing of `genStmt` / `genStmtChain`
(defined in `StmtHasTypeAGen/Core.lean`), which
generate random well-typed Strata Core statements
(`Statement = Imperative.Stmt Core.Expression Core.Command`) satisfying the
`StatementHasTypeA` / `StatementsHasTypeA` typing relations. The generator is proven both
**soundness** and a proof of **completeness** against those relations, in `StmtHasTypeAGen.lean`. Therefore
each generated statement is a certified well-typed input, and it is a good input for the typechecker of a
statement and for each transform of Strata Core at the level of a statement.

This module holds everything both harnesses need so the harness files only add
thin glue:

- **The total functions that measure a statement list**, which are `countLoops`, `countExit`,
  `countFuncDecl`, `countTypeDecl`, `sizeStmts` and `stmtKind`. A `#guard` below checks each of them.
- **The wrapper `genProgramStmtsIO` around the generator**, together with the contexts.
- **Six check predicates that give a `Bool`**, one for each property under test, and each of them applies to a
  generated statement list.

## The statement typechecker context

`Statement.typeCheck` takes an ambient `LContext CoreLParams` (`= Expression.TyContext`)
and a `TEnv Unit`. The generator threads its own `LContext CoreLParams` starting
from `LContext.default`, and the annotated typing spec `instHasTypeA` ignores `C`
when it types an *expression*. Therefore a generated statement is well typed under *each* context whose
factory and whose known types resolve each operator and each type alias that the statement uses. This module
therefore runs the algorithm against the standard context of Strata Core,
(`Core.Factory` + `Core.KnownTypes`), exactly the context real Core programs are
checks a real Core program in. A generated statement holds no procedure call, because a `CmdExt.call` is
provably unreachable from the generator, which `StmtHasTypeAGen.lean` proves. Therefore the empty program with
no procedure is enough, because the `.call` branch is the one place where the typechecker reads the program or
a procedure.
-/

namespace StrataGenerators.Stmt.TestSupport

-- ── Ambient context for the statement typechecker ────────────────────────

/-- The standard Core ambient typing context: the full built-in `Core.Factory`
    (integer/real/bool/string/regex/sequence/map operators) and `Core.KnownTypes`
    (base types + `arrow`/`Map`/`Sequence` aliases). This is the context real Core
    programs are typechecked in, so a generated statement that fails to typecheck
    here is a genuine counterexample to typechecker completeness,
    not a missing-declaration artifact. -/
def stmtCheckContext : LContext CoreLParams :=
  { LContext.default with
    functions := Core.Factory,
    knownTypes := Core.KnownTypes }

-- ── Total measurement functions ──────────────────────────────────────────
-- All `partial`-free and structurally recursive on `Stmt.sizeOf`, so they are
-- usable in `#guard`s and (in principle) in proofs.

mutual

/-- Count the statement nodes (anywhere in `s`, including nested bodies) that
    satisfy `pred`. The generic traversal underlying every structural count/has
    query below. It goes into the body of a `block`, of an `ite` and of a `loop`, and it adds one for each node
    where `pred` holds, whether that node is a leaf or a compound statement. -/
def countStmtsBy (pred : Statement → Bool) : Statement → Nat
  | s@(.block _ body _) => (if pred s then 1 else 0) + countStmtsByList pred body
  | s@(.ite _ thenb elseb _) =>
      (if pred s then 1 else 0) + countStmtsByList pred thenb + countStmtsByList pred elseb
  | s@(.loop _ _ _ body _) => (if pred s then 1 else 0) + countStmtsByList pred body
  | s => if pred s then 1 else 0

/-- List analogue of `countStmtsBy`: total matching nodes across the list. -/
def countStmtsByList (pred : Statement → Bool) : List Statement → Nat
  | [] => 0
  | s :: ss => countStmtsBy pred s + countStmtsByList pred ss

end

/-- Number of `loop` nodes anywhere in a statement list. -/
def countLoopsStmts (ss : List Statement) : Nat :=
  countStmtsByList (fun | .loop _ _ _ _ _ => true | _ => false) ss

/-- Number of `exit` nodes anywhere in a statement list. -/
def countExitStmts (ss : List Statement) : Nat :=
  countStmtsByList (fun | .exit _ _ => true | _ => false) ss

/-- Number of `funcDecl` nodes anywhere in a statement list. -/
def countFuncDeclStmts (ss : List Statement) : Nat :=
  countStmtsByList (fun | .funcDecl _ _ => true | _ => false) ss

/-- Number of `typeDecl` nodes anywhere in a statement list. -/
def countTypeDeclStmts (ss : List Statement) : Nat :=
  countStmtsByList (fun | .typeDecl _ _ => true | _ => false) ss

/-- AST size of a statement list (delegates to `Block.sizeOf`). -/
def sizeStmts (ss : List Statement) : Nat := Block.sizeOf ss

/-- Classify the top-level constructor of a statement (for Tyche breakdowns). -/
def stmtKind : Statement → String
  | .cmd _ => "cmd"
  | .block _ _ _ => "block"
  | .ite (.det _) _ _ _ => "ite_det"
  | .ite .nondet _ _ _ => "ite_nondet"
  | .loop _ _ _ _ _ => "loop"
  | .exit _ _ => "exit"
  | .funcDecl _ _ => "funcDecl"
  | .typeDecl _ _ => "typeDecl"

/-- Whether a statement list holds an `exit`, a `funcDecl`, a `typeDecl` or a procedure `call`. Those are
    exactly the constructors that make `kleeneStmts` give `none`, apart from a loop that carries an invariant,
    which `hasInvLoopStmts` finds. The property about the definedness of the transform uses this function.

    The `call` case is unreachable from the *statement* generator, which is why
    `toCmdStmt`'s note calls it vacuous. It is **not** vacuous for a whole generated
    *program*: `ProgramGen` emits `call` commands, so a property that screens on this
    predicate over program bodies (`checkKleeneMeasureAccepted`) needs the case, or a
    draw containing a call is scored as a Kleene failure that has nothing to do with
    the construct under test. -/
def hasKleeneUnsupported (ss : List Statement) : Bool :=
  countStmtsByList
    (fun | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ | .cmd (.call _ _ _) => true
         | _ => false) ss != 0

/-- Whether a statement list contains any `loop` node carrying a non-empty
    invariant list. `StmtToKleeneStmt` returns `none` for such loops (Kleene has
    no invariant. That is one more cause of a rejection, beyond an `exit`, a `funcDecl` and a `typeDecl`, and
    the property about definedness accounts for it. -/
def hasInvLoopStmts (ss : List Statement) : Bool :=
  countStmtsByList (fun | .loop _ _ inv _ _ => !inv.isEmpty | _ => false) ss != 0

/-- The structural equality of two statement lists, through the `DecidableEq (Stmt …)` instance of Strata. This
    definition compares the two abstract syntax trees directly, and not the printed form of each of them. A
    comparison of two printed forms is not exact, because two different trees can print to one text, and the body
    of a `funcDecl` in particular does not survive a round trip. -/
def stmtsEq (ss ss' : List Statement) : Bool :=
  decide (ss = ss')

mutual
/-- Collect a `[body=…, measure=…]` tag for every `funcDecl` node anywhere in a
    statement, and it reads each nested body. The formatter of Strata cannot write a `funcDecl` statement with
    no body, and it puts a dummy body there instead. A `funcDecl` with a measure and no body is exactly the
    counterexample to the completeness of the typechecker, so this function records the true shape. -/
def funcDeclShapes : Statement → List String
  | .funcDecl d _ => [s!"funcDecl[body={d.body.isSome}, measure={d.measure.isSome}]"]
  | .block _ body _ => funcDeclShapesList body
  | .ite _ thenb elseb _ => funcDeclShapesList thenb ++ funcDeclShapesList elseb
  | .loop _ _ _ body _ => funcDeclShapesList body
  | .cmd _ | .exit _ _ | .typeDecl _ _ => []
/-- List analogue of `funcDeclShapes`. -/
def funcDeclShapesList : List Statement → List String
  | [] => []
  | s :: ss => funcDeclShapes s ++ funcDeclShapesList ss
end

-- ── `#guard` sanity checks on the measurement functions ──────────────────

section Guards
open Imperative

/-- A trivial `assert true` command statement (a leaf, no loops/exits/etc.). -/
private def leafStmt : Statement :=
  Statement.assert "l" (.const () (.boolConst true)) .empty

/-- A loop whose body is a single leaf, wrapped in a block: 1 loop, 0 exits. -/
private def loopInBlock : Statement :=
  .block "b" [.loop .nondet none [] [leafStmt] .empty] .empty

/-- An `ite` each of whose branches has a loop, plus an `exit`: 2 loops, 1 exit. -/
private def iteTwoLoops : Statement :=
  .ite .nondet
    [.loop .nondet none [] [] .empty]
    [.loop .nondet none [] [.exit "b" .empty] .empty]
    .empty

/-- A `typeDecl` leaf statement. -/
private def typeDeclStmt : Statement :=
  .typeDecl { name := "T", params := [] } .empty

/-- A loop carrying one invariant (so `StmtToKleeneStmt` rejects it). -/
private def invLoop : Statement :=
  .loop .nondet none [("i", .const () (.boolConst true))] [] .empty

#guard countLoopsStmts [leafStmt] == 0
#guard countLoopsStmts [loopInBlock] == 1
#guard countLoopsStmts [iteTwoLoops] == 2
#guard countExitStmts [iteTwoLoops] == 1
#guard countExitStmts [loopInBlock] == 0
#guard countTypeDeclStmts [typeDeclStmt] == 1
#guard countLoopsStmts [leafStmt, loopInBlock, iteTwoLoops] == 3
#guard hasKleeneUnsupported [iteTwoLoops] == true
#guard hasKleeneUnsupported [loopInBlock] == false
#guard hasInvLoopStmts [invLoop] == true
#guard hasInvLoopStmts [loopInBlock] == false
-- `countStmtsBy` counts compound nodes too: block + inner loop + the loop's leaf.
#guard countStmtsByList (fun _ => true) [loopInBlock] == 3
#guard stmtKind leafStmt == "cmd"
#guard stmtKind loopInBlock == "block"

end Guards

-- ── Transform applications ───────────────────────────────────────────────
-- The Core `Expression`/`Command` typeclass instances (`HasBool`, `HasBoolOps`,
-- `HasInit`, …) all exist, so these transforms resolve directly on
-- `List Statement` with no procedure/program wrapper.

/-- Apply loop elimination to a statement list, run from a fresh
    `CoreTransformState`. The function works on a statement list directly, and it needs no procedure and no
    program.

    Strata gives the pass as `Core.removeLoop`, which acts on one statement, and `Transform.runStmtsRec` in
    `CoreTransformM` drives it over a statement list. This function drives it in the same way, and it gives
    the input back unchanged when the pass throws. The pass throws on a loop that still carries an invariant
    or a measure, and on a label
    conflicts), since these properties are all of the shape
    "if the input type-checks, so does the output". -/
def loopElimStmts (ss : List Statement) : List Statement :=
  match (StateT.run (ExceptT.run
      (Transform.runStmtsRec Core.removeLoop ss))
      Transform.CoreTransformState.emp).fst with
  | .ok (_, ss') => ss'
  | .error _ => ss

/-- Apply the eliminator of a common subexpression to a statement list. The function starts the index of the
    fresh variables at 0, and it discards the next index that the pass gives. -/
def anfStmts (ss : List Statement) : List Statement :=
  (Core.CSE.stmtRunCSE ss 0).fst

-- `StmtToKleeneStmt` operates on `Stmt Expression (Cmd Expression)`, whereas the
-- generator produces `Statement = Stmt Expression Command` with
-- `Command = CmdExt Expression`. The two differ only by the `CmdExt` wrapper: a
-- each atomic command of a generated statement is a `CmdExt.cmd`, and never a `CmdExt.call`, because a
-- procedure call is provably unreachable from the generator. Therefore the function below first removes the
-- `CmdExt.cmd` wrapper, and it gives `none` when a `.call` occurs.

mutual
/-- Unwrap `CmdExt.cmd` throughout a statement, yielding a
    `Stmt Expression (Cmd Expression)`. Returns `none` on any `CmdExt.call`
    (unreachable for generated statements). -/
def toCmdStmt : Statement → Option (Stmt Expression (Cmd Expression))
  | .cmd (.cmd c) => some (.cmd c)
  | .cmd (.call _ _ _) => none
  | .block label body md => (fun b => .block label b md) <$> toCmdStmts body
  | .ite cond thenb elseb md => do
      let t ← toCmdStmts thenb
      let e ← toCmdStmts elseb
      pure (.ite cond t e md)
  | .loop guard measure inv body md => (fun b => .loop guard measure inv b md) <$> toCmdStmts body
  | .exit label md => some (.exit label md)
  | .funcDecl decl md => some (.funcDecl decl md)
  | .typeDecl tc md => some (.typeDecl tc md)
/-- List analogue of `toCmdStmt`. -/
def toCmdStmts : List Statement → Option (List (Stmt Expression (Cmd Expression)))
  | [] => some []
  | s :: ss => do
      let s' ← toCmdStmt s
      let ss' ← toCmdStmts ss
      pure (s' :: ss')
end

-- The other direction. `toCmdStmt` is partial because `CmdExt.call` has no `Cmd`
-- counterpart; re-wrapping is total, since every `Cmd` is a `CmdExt.cmd`. A pass
-- that acts on `Stmt Expression (Cmd Expression)` (`nondetElim`,
-- `hoistLoopPrefixInits`) needs both directions to be liftable to a whole
-- `Program`, whose procedure bodies are `Statement`s.

mutual
/-- Re-wrap every atomic command as `CmdExt.cmd`, yielding a `Statement`. Left
    inverse of `toCmdStmt` on its domain: `toCmdStmt s = some s'` implies
    `ofCmdStmt s' = s`. -/
def ofCmdStmt : Stmt Expression (Cmd Expression) → Statement
  | .cmd c => .cmd (.cmd c)
  | .block label body md => .block label (ofCmdStmts body) md
  | .ite cond thenb elseb md => .ite cond (ofCmdStmts thenb) (ofCmdStmts elseb) md
  | .loop guard measure inv body md => .loop guard measure inv (ofCmdStmts body) md
  | .exit label md => .exit label md
  | .funcDecl decl md => .funcDecl decl md
  | .typeDecl tc md => .typeDecl tc md
/-- List analogue of `ofCmdStmt`. -/
def ofCmdStmts : List (Stmt Expression (Cmd Expression)) → List Statement
  | [] => []
  | s :: ss => ofCmdStmt s :: ofCmdStmts ss
end

-- The round trip really is the identity on the shapes the generator makes, which
-- is what lets a `Cmd P`-shaped pass be lifted to a `Program` without changing
-- anything the pass did not touch.
#guard (toCmdStmts [Statement.assert "a" (.const () (.boolConst true)) .empty]).map
  ofCmdStmts == some [Statement.assert "a" (.const () (.boolConst true)) .empty]

/-- The transform from a deterministic statement list to a Kleene statement. The result is `none` if and only
    if the list holds a construct that has no counterpart in the Kleene form. Such a construct is an `exit`, a
    `funcDecl`, a `typeDecl`, a loop that carries an invariant, or a procedure call. Generated input holds no
    procedure call. -/
def kleeneStmts (ss : List Statement) : Option (KleeneStmt Expression (Cmd Expression)) := do
  let ss' ← toCmdStmts ss
  BlockToKleeneStmt (P := Expression) ss'

-- ── The six `Bool` check predicates ──────────────────────────────────────

/-- A dummy enclosing procedure. The typechecker consults its `op : Option
    Procedure` argument *only* in the `exit` case, where `exit` is rejected
    outright when `op = none` ("occurs outside a procedure"). Generated statement
    list is the *body* of a procedure, and it can hold an `exit` that targets a block around it. Therefore this
    module type checks such a list inside a procedure, and it gives `some dummyProc`. The typechecker reads no
    other field of that procedure. -/
def dummyProc : Procedure := Inhabited.default

/-- Whether `Statement.typeCheck` accepts a statement list in the standard Core
    ambient context, checked as a procedure body (`op := some dummyProc`, so
    `exit`s to enclosing blocks are permitted). -/
def checkTypeChecks (ss : List Statement) : Bool :=
  match Statement.typeCheck stmtCheckContext TEnv.default Program.init (some dummyProc) ss with
  | .ok _ => true
  | .error _ => false

/-- Whether a statement list contains any `funcDecl` node. -/
def stmtsHaveFuncDecl (ss : List Statement) : Bool := countFuncDeclStmts ss != 0

/-- **The completeness of the typechecker.** The generator has a proof of *soundness*: each statement list that
    it gives satisfies `StatementsHasTypeA`. Therefore the algorithmic typechecker must accept each of them.
    That algorithm has a proof of *soundness*, and it has no proof of *completeness*. A rejection is therefore a
    true gap in the completeness of the algorithm against the declarative specification. This predicate states
    that claim and does not weaken it, and it does not hide the known difference at a `funcDecl`. Read
    `rejectionImpliesFuncDecl`. -/
abbrev checkTypeCheckerComplete (ss : List Statement) : Bool := checkTypeChecks ss

/-- **The description of the gap in completeness.** The result is `true` when the typechecker accepts the list,
    *or* the list holds a `funcDecl`. That is to say that a `funcDecl` causes each rejection of a generated
    statement. This predicate pins the one known source of a gap in completeness. A counterexample means that
    the generator gave a statement that the specification accepts and that the algorithm rejects for some
    *other* reason, which is a gap in completeness of a new kind.

    The difference at a `funcDecl` is this. The declarative rule `StatementHasType'.funcDecl` asks only that the
    *witness* function that it adds to the context is well typed, and that the syntactic declaration node is
    not recursive. The two are **independent**, because no premise ties the declaration to the function. The
    generator therefore draws them independently. The *algorithm* instead derives the witness *from* the
    declaration node, through `PureFunc.typeCheck`. Therefore it rejects a `funcDecl` whose declaration node
    does not type check itself. The specification is therefore strictly more permissive at a `funcDecl`, and its
    rule is arguably too loose, because it should relate the declaration to the function. Either way, that is a
    true disagreement between the specification and the algorithm. -/
def rejectionImpliesFuncDecl (ss : List Statement) : Bool :=
  checkTypeChecks ss || stmtsHaveFuncDecl ss

/-- **LoopElim preserves typeability.** A preservation property is
    inherently conditional: a transform can only be blamed for *breaking* an
    already-well-typed input, not for input the algorithm rejects on its own. So
    this asserts the implication "input typechecks ⇒ output typechecks". It is
    vacuously satisfied when the input is rejected (e.g. the `funcDecl` gap), and
    genuinely FAILS if LoopElim turns an accepted statement list into a rejected
    one. -/
def checkLoopElimPreservesTyping (ss : List Statement) : Bool :=
  !checkTypeChecks ss || checkTypeChecks (loopElimStmts ss)

/-- **LoopElim eliminates every loop**: the result has zero `loop`
    nodes. -/
def checkLoopElimZeroLoops (ss : List Statement) : Bool :=
  countLoopsStmts (loopElimStmts ss) == 0

/-- **ANF is idempotent**: `anf (anf x) = anf x` (structural
    equality on the resulting statement lists). -/
def checkAnfIdempotent (ss : List Statement) : Bool :=
  let once := anfStmts ss
  stmtsEq (anfStmts once) once

/-- **ANF preserves typeability.** As with LoopElim preservation: the implication "input
    typechecks ⇒ ANF output typechecks". Vacuous when the input is rejected;
    genuinely FAILS if ANF turns an accepted statement list into a rejected one. -/
def checkAnfPreservesTyping (ss : List Statement) : Bool :=
  !checkTypeChecks ss || checkTypeChecks (anfStmts ss)

/-- **Kleene definedness**: `StmtToKleeneStmt` is defined *exactly* when the block has no
    an `exit`, a `funcDecl` or a `typeDecl`. There is one further condition: the transform *also* rejects a loop
    that carries an invariant, through its guard on the list of the invariants. Therefore the plain
    biconditional holds only when the list holds no such loop. This predicate accepts a sample when the
    biconditional holds, or when the list holds a loop with an invariant, which is the one further cause of a
    `none`. That form keeps the property a faithful test of the
    doc-comment's stated contract without spurious failures. -/
def checkKleeneDefinedIff (ss : List Statement) : Bool :=
  let defined := (kleeneStmts ss).isSome
  let unsupported := hasKleeneUnsupported ss
  if hasInvLoopStmts ss then
    -- A loop-with-invariant forces `none` regardless of the other constructors,
    -- so the only sound claim is that the transform is *not* defined.
    !defined
  else
    -- The doc-comment contract: defined ⟺ ¬(exit/funcDecl/typeDecl present).
    defined == !unsupported

/-- **The identity of `mapExprs`.** The statement `Statements.mapExprs id = id` says that a map of the identity
    function over each expression of a statement list gives that list again. -/
def checkMapExprsId (ss : List Statement) : Bool :=
  stmtsEq (Statements.mapExprs id ss) ss

-- ── The completeness of the typechecker for a function ───────────────
--
-- `genFunction` has a proof of soundness: each function that it gives satisfies the declarative specification
-- `FuncHasType'`. Therefore `Function.typeCheck` must accept each of them. Another property tests the
-- *soundness* of that algorithm, and no proof gives its *completeness*. The algorithm does not accept each
-- generated function. `FuncHasType'` has no field that asks for a body, because the field about the body and
-- the field about the measure are each conditional on
-- the component being present), so a function with a **measure but no body**
-- satisfies the spec; but `Function.typeCheck` rejects it ("a decreases clause was
-- supplied but the function has no body", FunctionType.lean). This is the
-- form at the level of a function of the gap at a `funcDecl` at the level of a statement. Against the full
-- `Core.Factory` and `Core.KnownTypes` below, a measure with no body is the *one* cause. With a smaller
-- factory, a generated operator on a regular expression or on a real number would fail to resolve for a false
-- reason, and that failure would hide the real gap.

/-- Whether `Function.typeCheck` accepts `func` in the full Core ambient context
    (`Core.Factory` + `Core.KnownTypes`, so every operator/type the generator can
    emit resolves). -/
def checkFunctionTypeChecks (func : Function) : Bool :=
  match Function.typeCheck stmtCheckContext TEnv.default func with
  | .ok _ => true
  | .error _ => false

/-- Whether `func` has a measure and no body. The specification permits that shape, the algorithm rejects it,
    and it is therefore the witness for the gap in the completeness of the typechecker for a function. -/
def funcMeasureWithoutBody (func : Function) : Bool :=
  func.measure.isSome && func.body.isNone

/-- **The completeness of the typechecker for a function.** `genFunction` is sound, because its output
    satisfies `FuncHasType'`. Therefore the algorithm must accept each generated function. This predicate states
    that claim and does not weaken it, so it reports the gap about a measure with no body, which is a true
    disagreement between the specification and the algorithm, with a smallest witness. -/
abbrev checkFunctionTypeCheckerComplete (func : Function) : Bool := checkFunctionTypeChecks func

/-- **Characterization of the function-completeness gap.** "Every rejection is a
    measure-without-body function." Accepts, OR is measure-without-body. This PINS
    a measure with no body as the one known cause. A counterexample means that `genFunction` gave a function
    that the specification accepts and that the algorithm rejects for some *other* reason, which is a gap in
    completeness of a new kind. -/
def funcRejectionImpliesMeasureNoBody (func : Function) : Bool :=
  checkFunctionTypeChecks func || funcMeasureWithoutBody func

-- ── Structural statement shrinker ─────────────────────────────────────────
--
-- The statement-level analogue of the expression shrinker (`shrinkLExpr`): it
-- proposes structurally smaller statement lists, and the caller
-- (`shrinkStmts`) rejection-samples on the well-typedness oracle
-- `checkTypeChecks` (the algorithmic `Statement.typeCheck` in the standard Core
-- ambient context). This is the direct analogue of how the expression shrinker
-- filters on `LExpr.typeCheck`. Consequently *every* statement list the shrinker
-- gives is well typed by the algorithm. It need not have the same shape or the same scope as the original,
-- which the requirement permits. A shrink can drop the `init` of a variable and each statement that names that
-- variable, and it can change the type of a guard. The shrinker checks the whole list again, and it tracks no
-- type for one node.
--
-- Interaction with the completeness-gap properties: typechecker completeness
-- (`checkTypeCheckerComplete`) and the function-completeness properties hunt for
-- statement lists the *algorithm rejects* (e.g. a `funcDecl` with a measure but
-- with no body. The oracle here is the algorithm, so the shrinker minimizes no such counterexample, because
-- the filter removes each candidate that still fails. The harness therefore reports such a counterexample at
-- its full size, and it never reports a *wrong* result. For each
-- transform properties, whose inputs must be genuinely well-typed,
-- the algorithmic filter is exactly the right invariant.

/-- The structurally smaller replacements for a guard, which is deterministic or nondeterministic. The function
    shrinks the expression of the guard with `shrinkLExpr`, and it also replaces a deterministic guard by a
    nondeterministic one, which is a strictly simpler choice. The type check of the whole list in `shrinkStmts`
    removes each candidate whose type is wrong at the position of a guard. -/
def shrinkGuard (g : ExprOrNondet Expression) : List (ExprOrNondet Expression) :=
  match g with
  | .det e => (ExprOrNondet.det <$> shrinkLExpr e) ++ [ExprOrNondet.nondet]
  | .nondet => []

/-- Structurally smaller `funcDecl` bodies: drop the body, or drop the measure.
    Dropping the body while keeping the measure deliberately *preserves* the
    measure-without-body shape (the known completeness counterexample); dropping
    the measure moves toward a shape the algorithm accepts. -/
def shrinkPureFunc (d : PureFunc Expression) : List (PureFunc Expression) :=
  (if d.body.isSome then [{ d with body := none }] else [])
  ++ (if d.measure.isSome then [{ d with measure := none }] else [])

mutual
/-- The structurally smaller replacements for one statement. Each of them is strictly smaller by `Stmt.sizeOf`.
    The function goes into each body and each branch, it shrinks the atomic command with `shrinkCmd`, it shrinks
    each guard, and for a loop it drops the measure or the invariants. `shrinkStmtsList` also *flattens* a
    `block`, an `ite` and a `loop` at the level of the list, and it puts the body in place of the statement.
    Therefore this function needs no
    unwrap them. -/
partial def shrinkStmt : Statement → List Statement
  | .cmd (.cmd c) => (fun c' => .cmd (.cmd c')) <$> shrinkCmd c
  -- Procedure calls are unreachable from the generator; nothing to shrink.
  | .cmd (.call _ _ _) => []
  | .block label body md =>
    (.block label · md) <$> shrinkStmtsList body
  | .ite cond thenb elseb md =>
    (.ite cond · elseb md) <$> shrinkStmtsList thenb
    ++ (.ite cond thenb · md) <$> shrinkStmtsList elseb
    ++ (.ite · thenb elseb md) <$> shrinkGuard cond
  | .loop guard measure inv body md =>
    (if measure.isSome then [Stmt.loop guard none inv body md] else [])
    ++ (if !inv.isEmpty then [Stmt.loop guard measure [] body md] else [])
    ++ (.loop · measure inv body md) <$> shrinkGuard guard
    ++ (.loop guard measure inv · md) <$> shrinkStmtsList body
  | .exit _ _ => []
  | .funcDecl decl md => (.funcDecl · md) <$> shrinkPureFunc decl
  | .typeDecl _ _ => []

/-- Structurally smaller statement lists. Three families of reduction: drop one
    statement (`dropEach`); replace one statement by a smaller one (`shrinkStmt`);
    or *flatten* a `block`/`ite`/`loop` at position `i` by splicing its body (or a
    branch) in place of the compound node, dropping the wrapper. -/
partial def shrinkStmtsList (ss : List Statement) : List (List Statement) :=
  dropEach ss
  ++ ss.zipIdx.flatMap (fun (s, i) => (ss.set i ·) <$> shrinkStmt s)
  ++ (List.range ss.length).flatMap (fun i =>
      match ss.splitAt i with
      | (pre, s :: post) =>
        let splice (mid : List Statement) := pre ++ mid ++ post
        match s with
        | .block _ body _ => [splice body]
        | .ite _ thenb elseb _ => [splice thenb, splice elseb]
        | .loop _ _ _ body _ => [splice body]
        | _ => []
      | (_, []) => [])
end

/-- Well-typed structural shrinks of a statement list: every structurally smaller
    candidate (`shrinkStmtsList`) that still typechecks under the standard Core
    ambient context (`checkTypeChecks`). Guaranteed to remain well-typed; the type
    of individual sub-terms may differ from the original. -/
def shrinkStmts (ss : List Statement) : List (List Statement) :=
  (shrinkStmtsList ss).filter checkTypeChecks

-- ── Generator wrapper (IO) ───────────────────────────────────────────────

/-- Generate a well-typed statement list in `IO` via `genProgramStmts`, from an
    empty ambient context and empty variable scope. `size` bounds each
    statement's nesting/expression size; `len` bounds the top-level sequence
    length. The function gives the statement list only, and it discards each output context that the generator
    threads, because each property needs the statements only. -/
def genProgramStmtsIO (size len : Nat) (octx : OpCtx := coreMonoOps)
    (tvars : List TyIdentifier := []) : IO (List Statement) := do
  let (ss, _, _) ← genProgramStmts (G := IO) octx tvars size len
  pure ss

end StrataGenerators.Stmt.TestSupport
