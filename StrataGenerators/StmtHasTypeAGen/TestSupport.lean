import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import Strata.Languages.Core.StatementType
import Strata.Languages.Core.Factory
import Strata.Transform.LoopElim
import Strata.Transform.DetToKleene
import Strata.Transform.ANFEncoder

open Lambda RandomChoice Core Imperative
open StrataGenerators.Stmt

/-!
# Shared test support for the `StmtHasTypeAGen` generator

Utilities shared between `PlausibleTestMain` and `TycheMain` for property-based
testing of `genStmt` / `genStmts` (defined in `StmtHasTypeAGen/Core.lean`), which
generate random well-typed Strata Core statements
(`Statement = Imperative.Stmt Core.Expression Core.Command`) satisfying the
`StmtHasTypeA` / `StmtsHasTypeA` typing relations. The generator is proven both
**sound** and **complete** w.r.t. those relations (see `StmtHasTypeAGen.lean`), so
every generated statement is a certified well-typed input — an ideal oracle input
for the statement typechecker and the Core statement-level transformations.

This module holds everything both harnesses need so the harness files only add
thin glue:

- **Total measurement functions** (`countLoops`, `countExit`, `countFuncDecl`,
  `countTypeDecl`, `sizeStmts`, `stmtKind`) — each `#guard`-checked below.
- **Generator wrappers** (`genProgramStmtsIO`) plus the ambient contexts.
- **Six `Bool` check predicates**, one per property under test (#1, #3, #4, #5,
  #6, #9), each applied to a generated statement list.

## The statement typechecker context

`Statement.typeCheck` takes an ambient `LContext CoreLParams` (`= Expression.TyContext`)
and a `TEnv Unit`. The generator threads its own `LContext CoreLParams` starting
from `LContext.default`, and the annotated typing spec `instHasTypeA` ignores `C`
when typing *expressions* — so a generated statement is well-typed under *any* `C`
whose factory/known-types resolve the operators and type aliases it uses. We
therefore run the algorithm against the standard Core ambient context
(`Core.Factory` + `Core.KnownTypes`), exactly the context real Core programs are
checked in. Generated statements never contain procedure calls (`CmdExt.call` is
provably unreachable from the generator — see `StmtHasTypeAGen.lean`), so the
empty program `Program.init` with `op := none` is sufficient: the only place the
typechecker consults the `Program`/`Procedure` is the `.call` branch.
-/

namespace StrataGenerators.Stmt.TestSupport

-- ── Ambient context for the statement typechecker ────────────────────────

/-- The standard Core ambient typing context: the full built-in `Core.Factory`
    (integer/real/bool/string/regex/sequence/map operators) and `Core.KnownTypes`
    (base types + `arrow`/`Map`/`Sequence` aliases). This is the context real Core
    programs are typechecked in, so a generated statement that fails to typecheck
    here is a genuine counterexample to typechecker completeness (property #1),
    not a missing-declaration artifact. -/
def stmtCheckContext : LContext CoreLParams :=
  { LContext.default with
    functions := Core.Factory,
    knownTypes := Core.KnownTypes }

-- ── Total measurement functions ──────────────────────────────────────────
-- All `partial`-free and structurally recursive on `Stmt.sizeOf`, so they are
-- usable in `#guard`s and (in principle) in proofs.

mutual

/-- Number of `loop` nodes anywhere in a statement (including nested bodies). -/
def countLoopsStmt : Statement → Nat
  | .loop _ _ _ body _ => 1 + countLoopsStmts body
  | .block _ body _ => countLoopsStmts body
  | .ite _ thenb elseb _ => countLoopsStmts thenb + countLoopsStmts elseb
  | .cmd _ | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => 0

/-- Number of `loop` nodes anywhere in a statement list. -/
def countLoopsStmts : List Statement → Nat
  | [] => 0
  | s :: ss => countLoopsStmt s + countLoopsStmts ss

end

mutual

/-- Number of `exit` nodes anywhere in a statement. -/
def countExitStmt : Statement → Nat
  | .exit _ _ => 1
  | .loop _ _ _ body _ => countExitStmts body
  | .block _ body _ => countExitStmts body
  | .ite _ thenb elseb _ => countExitStmts thenb + countExitStmts elseb
  | .cmd _ | .funcDecl _ _ | .typeDecl _ _ => 0

/-- Number of `exit` nodes anywhere in a statement list. -/
def countExitStmts : List Statement → Nat
  | [] => 0
  | s :: ss => countExitStmt s + countExitStmts ss

end

mutual

/-- Number of `funcDecl` nodes anywhere in a statement. -/
def countFuncDeclStmt : Statement → Nat
  | .funcDecl _ _ => 1
  | .loop _ _ _ body _ => countFuncDeclStmts body
  | .block _ body _ => countFuncDeclStmts body
  | .ite _ thenb elseb _ => countFuncDeclStmts thenb + countFuncDeclStmts elseb
  | .cmd _ | .exit _ _ | .typeDecl _ _ => 0

/-- Number of `funcDecl` nodes anywhere in a statement list. -/
def countFuncDeclStmts : List Statement → Nat
  | [] => 0
  | s :: ss => countFuncDeclStmt s + countFuncDeclStmts ss

end

mutual

/-- Number of `typeDecl` nodes anywhere in a statement. -/
def countTypeDeclStmt : Statement → Nat
  | .typeDecl _ _ => 1
  | .loop _ _ _ body _ => countTypeDeclStmts body
  | .block _ body _ => countTypeDeclStmts body
  | .ite _ thenb elseb _ => countTypeDeclStmts thenb + countTypeDeclStmts elseb
  | .cmd _ | .exit _ _ | .funcDecl _ _ => 0

/-- Number of `typeDecl` nodes anywhere in a statement list. -/
def countTypeDeclStmts : List Statement → Nat
  | [] => 0
  | s :: ss => countTypeDeclStmt s + countTypeDeclStmts ss

end

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

/-- Whether a statement list contains any `exit`/`funcDecl`/`typeDecl` node —
    exactly the constructors `StmtToKleeneStmt` has no Kleene counterpart for.
    Used to state the "defined ⟺ supported" property (#6). -/
def hasKleeneUnsupported (ss : List Statement) : Bool :=
  countExitStmts ss + countFuncDeclStmts ss + countTypeDeclStmts ss != 0

mutual
/-- Whether a statement contains any `loop` node carrying a non-empty invariant
    list. `StmtToKleeneStmt` returns `none` for such loops (Kleene has no
    invariants), an extra rejection beyond `exit`/`funcDecl`/`typeDecl` —
    accounted for in property #6. -/
def hasInvLoopStmt : Statement → Bool
  | .loop _ _ inv body _ => !inv.isEmpty || hasInvLoopStmts body
  | .block _ body _ => hasInvLoopStmts body
  | .ite _ thenb elseb _ => hasInvLoopStmts thenb || hasInvLoopStmts elseb
  | .cmd _ | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => false
/-- List analogue of `hasInvLoopStmt`. -/
def hasInvLoopStmts : List Statement → Bool
  | [] => false
  | s :: ss => hasInvLoopStmt s || hasInvLoopStmts ss
end

/-- Structural equality on statement lists via their canonical pretty-print.
    `Statement` has no `BEq`/`DecidableEq` instance, so — following the codebase's
    own `StrataTest/Transform/DetToKleene.lean` convention — we compare through
    `Std.format`. -/
def stmtsEq (ss ss' : List Statement) : Bool :=
  (Std.format ss).pretty == (Std.format ss').pretty

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

#guard countLoopsStmt leafStmt == 0
#guard countLoopsStmt loopInBlock == 1
#guard countLoopsStmt iteTwoLoops == 2
#guard countExitStmt iteTwoLoops == 1
#guard countExitStmt loopInBlock == 0
#guard countTypeDeclStmt typeDeclStmt == 1
#guard countLoopsStmts [leafStmt, loopInBlock, iteTwoLoops] == 3
#guard hasKleeneUnsupported [iteTwoLoops] == true
#guard hasKleeneUnsupported [loopInBlock] == false
#guard hasInvLoopStmt invLoop == true
#guard hasInvLoopStmt loopInBlock == false
#guard stmtKind leafStmt == "cmd"
#guard stmtKind loopInBlock == "block"

end Guards

-- ── Transform applications ───────────────────────────────────────────────
-- The Core `Expression`/`Command` typeclass instances (`HasBool`, `HasBoolOps`,
-- `HasInit`, …) all exist, so these transforms resolve directly on
-- `List Statement` with no procedure/program wrapper.

/-- Apply loop elimination to a statement list (LoopElim `Block.removeLoopsM`,
    run from a fresh `LoopElimState`). Operates directly on statements — no
    `Procedure`/`Program` needed. -/
def loopElimStmts (ss : List Statement) : List Statement :=
  (StateT.run (Block.removeLoopsM ss) {}).fst

/-- Apply the ANF encoder to a statement list (starting fresh-var index 0),
    discarding the returned next-index. -/
def anfStmts (ss : List Statement) : List Statement :=
  (Core.ANFEncoder.anfEncodeBody ss 0).fst

-- `StmtToKleeneStmt` operates on `Stmt Expression (Cmd Expression)`, whereas the
-- generator produces `Statement = Stmt Expression Command` with
-- `Command = CmdExt Expression`. The two differ only by the `CmdExt` wrapper: a
-- generated statement's atomic commands are always `CmdExt.cmd` (never
-- `CmdExt.call` — procedure calls are provably unreachable from the generator).
-- So we first unwrap `CmdExt.cmd`, returning `none` if a `.call` ever appears.

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

/-- The deterministic-to-Kleene transform on a statement list. `none` iff the
    block contains a construct with no Kleene counterpart (`exit`/`funcDecl`/
    `typeDecl`, or a loop carrying an invariant), or — vacuously for generated
    input — a procedure call. -/
def kleeneStmts (ss : List Statement) : Option (KleeneStmt Expression (Cmd Expression)) := do
  let ss' ← toCmdStmts ss
  BlockToKleeneStmt (P := Expression) ss'

-- ── The six `Bool` check predicates ──────────────────────────────────────

/-- A dummy enclosing procedure. The typechecker consults its `op : Option
    Procedure` argument *only* in the `exit` case, where `exit` is rejected
    outright when `op = none` ("occurs outside a procedure"). Generated statement
    lists are procedure *bodies* — they legitimately contain `exit`s targeting
    enclosing blocks — so we typecheck them as if inside a procedure by passing
    `some dummyProc`. No field of the procedure is otherwise inspected. -/
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

/-- **Property #1 (typechecker completeness).** The generator is proven *sound*:
    every statement list it produces satisfies `StmtsHasTypeA`. So the algorithmic
    typechecker — whose *soundness* (`typeCheck_annotated_sound`) is proven but
    whose *completeness* is not — should accept every one of them. A rejection is a
    genuine incompleteness of the algorithm relative to the declarative spec. This
    predicate makes that honest claim (no masking), so it will FAIL on the known
    `funcDecl` discrepancy — see `rejectionImpliesFuncDecl`. -/
abbrev checkTypeCheckerComplete (ss : List Statement) : Bool := checkTypeChecks ss

/-- **Characterization of the completeness gap.** `true` when the typechecker
    accepts `ss`, *or* `ss` contains a `funcDecl`. Equivalently: "every rejection of
    a generated statement is attributable to a `funcDecl`." This SHOULD hold — it
    pins the sole known source of incompleteness. If it ever *fails*, the generator
    has produced a spec-well-typed statement the algorithm rejects for some reason
    *other* than `funcDecl` — a new, unclassified completeness bug.

    The `funcDecl` discrepancy itself: the declarative `StmtHasType'.funcDecl` rule
    requires only that the *witness* `func` added to `C` is well-typed and the
    syntactic `decl` node is non-recursive — the two are **independent** (no premise
    ties `decl` to `func`). The generator faithfully samples them independently. The
    *algorithm*, by contrast, derives the witness *from* the decl node
    (`PureFunc.typeCheck C Env decl`, FunctionType.lean:273), so it rejects a
    `funcDecl` whose decl node does not itself typecheck. The spec is thus strictly
    more permissive on `funcDecl` — arguably the spec rule is too loose (it should
    relate `decl` to `func`). Either way it is a real spec/algorithm divergence. -/
def rejectionImpliesFuncDecl (ss : List Statement) : Bool :=
  checkTypeChecks ss || stmtsHaveFuncDecl ss

/-- **Property #3 (LoopElim preserves typeability).** A preservation property is
    inherently conditional: a transform can only be blamed for *breaking* an
    already-well-typed input, not for input the algorithm rejects on its own. So
    this asserts the implication "input typechecks ⇒ output typechecks". It is
    vacuously satisfied when the input is rejected (e.g. the `funcDecl` gap), and
    genuinely FAILS if LoopElim turns an accepted statement list into a rejected
    one. -/
def checkLoopElimPreservesTyping (ss : List Statement) : Bool :=
  !checkTypeChecks ss || checkTypeChecks (loopElimStmts ss)

/-- **Property #4**: LoopElim eliminates every loop — the result has zero `loop`
    nodes. -/
def checkLoopElimZeroLoops (ss : List Statement) : Bool :=
  countLoopsStmts (loopElimStmts ss) == 0

/-- **Property #5a**: ANF is idempotent — `anf (anf x) = anf x` (structural
    equality on the resulting statement lists). -/
def checkAnfIdempotent (ss : List Statement) : Bool :=
  let once := anfStmts ss
  stmtsEq (anfStmts once) once

/-- **Property #5b (ANF preserves typeability).** As #3: the implication "input
    typechecks ⇒ ANF output typechecks". Vacuous when the input is rejected;
    genuinely FAILS if ANF turns an accepted statement list into a rejected one. -/
def checkAnfPreservesTyping (ss : List Statement) : Bool :=
  !checkTypeChecks ss || checkTypeChecks (anfStmts ss)

/-- **Property #6**: `StmtToKleeneStmt` is defined *exactly* when the block has no
    `exit`/`funcDecl`/`typeDecl`. One caveat: the transform *also* rejects loops
    carrying invariants (`inv.isEmpty` guard). So the clean bi-implication only
    holds when no such loop is present; we score the sample as a pass when either
    the bi-implication holds, or the block contains an invariant-bearing loop
    (the one documented extra `none` case). This keeps #6 a faithful test of the
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

/-- **Property #9**: `Statements.mapExprs id = id` — mapping the identity over all
    expressions in a statement list is the identity. -/
def checkMapExprsId (ss : List Statement) : Bool :=
  stmtsEq (Statements.mapExprs id ss) ss

-- ── Generator wrapper (IO) ───────────────────────────────────────────────

/-- Generate a well-typed statement list in `IO` via `genProgramStmts`, from an
    empty ambient context and empty variable scope. `size` bounds each
    statement's nesting/expression size; `len` bounds the top-level sequence
    length. Returns just the statement list (the threaded output contexts are
    discarded — the tests only need the statements). -/
def genProgramStmtsIO (size len : Nat) (fctx : FVarCtx := []) (octx : OpCtx := coreOpCtx)
    (tvars : List TyIdentifier := []) : IO (List Statement) := do
  let (ss, _, _) ← genProgramStmts (G := IO) fctx octx tvars size len
  pure ss

end StrataGenerators.Stmt.TestSupport
