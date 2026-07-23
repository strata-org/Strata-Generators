import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.SubexprMutate
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import Strata.Languages.Core.StatementType
import Strata.Languages.Core.Factory
import Strata.Transform.LoopElim
import Strata.Transform.DetToKleene
import Strata.Transform.CommonSubexprElim
import Strata.Languages.Core.StatementEval

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

/-- Count the statement nodes (anywhere in `s`, including nested bodies) that
    satisfy `pred`. The generic traversal underlying every structural count/has
    query below: recurse into `block`/`ite`/`loop` bodies, adding one for each
    node — leaf or compound — for which `pred` holds. -/
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

/-- Whether a statement list contains any `exit`/`funcDecl`/`typeDecl` node —
    exactly the constructors `StmtToKleeneStmt` has no Kleene counterpart for.
    Used to state the "defined ⟺ supported" property (#6). -/
def hasKleeneUnsupported (ss : List Statement) : Bool :=
  countStmtsByList (fun | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => true | _ => false) ss != 0

/-- Whether a statement list contains any `loop` node carrying a non-empty
    invariant list. `StmtToKleeneStmt` returns `none` for such loops (Kleene has
    no invariants), an extra rejection beyond `exit`/`funcDecl`/`typeDecl` —
    accounted for in property #6. -/
def hasInvLoopStmts (ss : List Statement) : Bool :=
  countStmtsByList (fun | .loop _ _ inv _ _ => !inv.isEmpty | _ => false) ss != 0

/-- Equality on statement lists via their canonical pretty-print. `Statement` has
    no `BEq`/`DecidableEq` instance (its `funcDecl` payload carries a
    function-typed field), so — following the codebase's own
    `StrataTest/Transform/DetToKleene.lean` convention — we compare through
    `Std.format`.

    CAVEAT: this is brittle. The CST formatter cannot faithfully render every
    statement (e.g. a bodiless `funcDecl` gets a substituted dummy body), so two
    *distinct* lists can format identically. Only use it where a false "equal" is
    harmless — e.g. `checkMapExprsId` below, where both sides are literally the
    same list. Do NOT use it to decide CSE-output equality; `checkCseIdempotent`
    instead compares CSE-introduced var *counts* (`countCseVars`), which is total
    and formatter-independent. -/
def stmtsEq (ss ss' : List Statement) : Bool :=
  (Std.format ss).pretty == (Std.format ss').pretty

mutual
/-- Collect a `[body=…, measure=…]` tag for every `funcDecl` node anywhere in a
    statement (nested bodies included). Strata's CST formatter cannot represent a
    bodiless `funcDecl` statement — it substitutes a dummy body — and a bodiless
    funcDecl *with a measure* is exactly the typechecker-completeness
    counterexample, so this records the true shape the rendered form can't show. -/
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

/-- Apply loop elimination to a statement list (LoopElim `Block.removeLoopsM`,
    run from a fresh `LoopElimState`). Operates directly on statements — no
    `Procedure`/`Program` needed. -/
def loopElimStmts (ss : List Statement) : List Statement :=
  (StateT.run (Block.removeLoopsM ss) {}).fst

/-- Apply common-subexpression elimination to a statement list (starting
    fresh-var index 0), discarding the returned next-index. -/
def cseStmts (ss : List Statement) : List Statement :=
  (Core.CSE.stmtRunCSE ss 0).fst

-- ── Subexpression-duplication mutation (CSE input shaping) ────────────────
-- `genStmt`'s expressions are drawn independently, so they almost never contain
-- two structurally-equal non-trivial subterms — CSE then runs near-vacuously.
-- Rather than change the *proven* generator (which would force re-discharging
-- `genStmt_sound`; see docs/cse-ptrcache-pbt-plan.md), we mutate the generated
-- output here, at the proof-free harness layer, via a pure per-expression map.
-- `SubexprMutate.duplicateOneSubterm` is type-preserving by construction (it
-- returns a `duplicationMutants` entry), so the mutated list stays well-typed —
-- the CSE properties' own `typeCheck` oracle re-confirms this.
--
-- Every user-facing statement expression is typed under the empty bound-variable
-- context (statement-scope variables are `fvar`s; only `abs`/`quant` *inside* an
-- expression introduce de Bruijn binders, which `SubexprMutate.occurrences`
-- threads correctly). So the same-context splice runs soundly at `bctx = []`.

/-- Duplicate one non-trivial subterm inside every user-facing expression of a
    statement list, forcing common subexpressions for CSE to act on. Each
    expression is mapped through `SubexprMutate.duplicateOneSubterm []`, a
    type-preserving no-op when the expression has no duplication opportunity. -/
def dupSubtermsStmts (ss : List Statement) : List Statement :=
  Statements.mapExprs (SubexprMutate.duplicateOneSubterm []) ss

/-- Total count of subterm-duplication opportunities across all user-facing
    expressions of a statement list — a Tyche feature (`dup_sites`) confirming the
    mutation actually fires on a sample rather than passing vacuously. -/
def dupSitesStmts (ss : List Statement) : Nat :=
  (Statements.collectExprs ss).foldl
    (fun acc e => acc + SubexprMutate.duplicationSiteCount [] e) 0

/-- **Regression guard on the mutation code itself.** Every duplication mutant of
    every user-facing expression typechecks at the expression's own type under the
    empty context. Should be impossible to falsify unless `SubexprMutate`'s
    path/context bookkeeping is wrong (analogous to MUTAGEN's
    `prop_mutantsWellTyped`) — a failure indicts this harness code, not CSE. -/
def checkDupMutantsWellTyped (ss : List Statement) : Bool :=
  (Statements.collectExprs ss).all (SubexprMutate.checkAllMutantsWellTyped [])

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

mutual
/-- Collect the RHS `Expr` of every CSE-introduced `init` declaration (name
    prefixed by `Core.CSE.cseVarPrefix`) anywhere in a statement, nested bodies
    included. These are exactly the subexpressions CSE hoisted into fresh `var`
    declarations. Operates on a *given* statement list — it does not run CSE. -/
def cseInitRHSs : Statement → List Expression.Expr
  | .cmd (.cmd (.init n _ (.det e) _)) =>
      if n.name.startsWith Core.CSE.cseVarPrefix then [e] else []
  | .cmd _ => []
  | .block _ body _ => cseInitRHSsList body
  | .ite _ thenb elseb _ => cseInitRHSsList thenb ++ cseInitRHSsList elseb
  | .loop _ _ _ body _ => cseInitRHSsList body
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []
/-- List analogue of `cseInitRHSs`. -/
def cseInitRHSsList : List Statement → List Expression.Expr
  | [] => []
  | s :: ss => cseInitRHSs s ++ cseInitRHSsList ss
end

/-- Number of CSE-introduced `var` declarations *already present* in a statement
    list (name prefixed by `Core.CSE.cseVarPrefix`). Does not run CSE. -/
def countCseVars (ss : List Statement) : Nat :=
  (cseInitRHSsList ss).length

/-- **Property #5a (CSE reaches a fixpoint / idempotence proxy).** Rather than
    assert exact structural equality of `cse (cse x)` and `cse x` — which would
    force a brittle comparison of statement lists (`Statement` has no
    `DecidableEq`; its `funcDecl` payload even carries a function-typed field) —
    we compare the *number of CSE-introduced `var` declarations* before and after
    a second pass. This directly exercises the fixpoint-fuel convergence of
    `stmtRunCSE` (the CR replaced the provable `|S(body)|` bound with the constant
    `fuel := 1024`): if the fixpoint has not converged, the second pass extracts
    further duplicates and introduces *additional* `$__cse.*` vars, so the count
    strictly increases and this fails.

    This is a proxy, deliberately weaker than structural equality (a second pass
    that rewrites without changing the var count would not be caught) — but it is
    total, deterministic, and free of pretty-printer artifacts, and it captures
    exactly the non-convergence failure mode we care about. -/
def checkCseIdempotent (ss : List Statement) : Bool :=
  let once := cseStmts ss
  countCseVars once == countCseVars (cseStmts once)

/-- **Property #5b (CSE preserves typeability).** As #3: the implication "input
    typechecks ⇒ CSE output typechecks". Vacuous when the input is rejected;
    genuinely FAILS if CSE turns an accepted statement list into a rejected one.
    Because a subterm hoisted out of its binder becomes ill-scoped, this is also
    a partial capture detector: a capture that yields an unbound/ill-typed
    reference surfaces here as a typing regression. -/
def checkCsePreservesTyping (ss : List Statement) : Bool :=
  !checkTypeChecks ss || checkTypeChecks (cseStmts ss)

-- ── CSE capture-safety and DAG-size properties (see docs/cse-ptrcache-pbt-plan.md) ──
-- These target the parts of CR-289836082 that are *not* covered by a Lean proof:
-- the `PtrCache` itself is proved a transparent optimization (`run'_output_eq`),
-- but the CSE traversal built on top of it — in particular the bvar-freeness flag
-- in `collectSubexprs.abs` (flagged "may spuriously return true") — is not.
-- (`cseInitRHSs` / `cseInitRHSsList` / `countCseVars` are defined above, next to
-- `checkCseIdempotent`.)

/-- **Property P-CSE-3 (capture safety — no dangling de Bruijn index in any
    extracted init).** CSE only ever introduces `var $__cse.k := e` declarations,
    prepended to the body they were lifted from — i.e. at top level, under *zero*
    binders. In Strata's locally-nameless `LExpr`, a `.bvar i` node is a de Bruijn
    index pointing `i` binders outward; it is well-formed only under enough
    enclosing `abs`/`quant`s. A subterm hoisted out of an enclosing binder carries
    its `.bvar` node along, and at top level that index now points past every
    binder — it is *dangling* (an escaped bound variable). Since the init sits
    under no binders, `LExpr.hasBVar e` (true iff `e` contains any `.bvar` node at
    all) detects exactly this: we assert every CSE-introduced init RHS satisfies
    `!e.hasBVar`. A failure is a variable-capture bug and thus a violation of the
    pass's "model-preserving" contract — the cheapest, most direct detector for
    the `collectSubexprs.abs` bvar-freeness approximation. -/
def checkCseNoFreeBVarInInits (ss : List Statement) : Bool :=
  (cseInitRHSsList (cseStmts ss)).all (fun e => !LExpr.hasBVar e)

/-- Number of distinct subterms of `e` up to structural (metadata-ignoring)
    equality — the DAG-node count. Uses a `HashMap` keyed by `LExpr.hashExpr`
    with a structural `==` disambiguator inside each bucket, so it is robust to
    hash collisions (counting distinct `UInt64` hashes would undercount). The
    early-return on an already-seen key is what makes this the DAG measure rather
    than the exponential tree measure. -/
partial def structuralDagSize (e : Expression.Expr) : Nat :=
  go [e] (Std.HashMap.emptyWithCapacity) |>.size
where
  /-- `seen` maps a structural hash to the list of distinct subterms carrying it. -/
  go (work : List Expression.Expr)
     (seen : Std.HashMap UInt64 (List Expression.Expr)) :
     Std.HashMap UInt64 (List Expression.Expr) :=
    match work with
    | [] => seen
    | e :: rest =>
      let h := LExpr.hashExpr e
      let bucket := seen.getD h []
      if bucket.any (fun e' => e' == e) then go rest seen
      else
        let seen := seen.insert h (e :: bucket)
        go (children e ++ rest) seen
  /-- Immediate structural children of a node. -/
  children : Expression.Expr → List Expression.Expr
    | .app _ fn arg => [fn, arg]
    | .ite _ c t f => [c, t, f]
    | .eq _ a b => [a, b]
    | .abs _ _ _ body => [body]
    | .quant _ _ _ _ tr body => [tr, body]
    | _ => []

/-- Number of CSE-introduced `var` declarations in the output of running CSE. -/
def cseVarCount (ss : List Statement) : Nat :=
  countCseVars (cseStmts ss)

/-- Number of **common (shared) compound subterms** in a statement list: the count
    of *distinct* non-leaf subterms — up to structural (metadata-ignoring)
    equality — that occur two or more times across every expression in `ss`.

    This is exactly the pool of subexpressions CSE can eliminate: only compound
    nodes (`app`/`ite`/`eq`/`abs`/`quant`) are worth abbreviating (a bare
    `fvar`/`bvar`/`const`/`op` is already atomic), and a subterm is only a *common*
    subexpression once it appears at least twice. A program with a count of `0` has
    nothing for CSE to do; a positive count means the sample genuinely exercises
    the transform. Robust to hash collisions the same way `structuralDagSize` is:
    a `HashMap` keyed by `LExpr.hashExpr` whose buckets carry a structural `==`
    disambiguator, each paired with its running occurrence tally. -/
partial def commonSubtermCount (ss : List Statement) : Nat :=
  let seen := (Statements.collectExprs ss).foldl (fun acc e => tally [e] acc)
                (Std.HashMap.emptyWithCapacity)
  -- Count distinct compound subterms whose occurrence tally reached ≥ 2.
  seen.fold (fun n _ bucket =>
    n + (bucket.filter (fun (e, c) => c ≥ 2 && isCompound e)).length) 0
where
  /-- Whether `e` is a compound node worth abbreviating (not an atomic leaf). -/
  isCompound : Expression.Expr → Bool
    | .app _ _ _ | .ite _ _ _ _ | .eq _ _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _ => true
    | _ => false
  /-- Immediate structural children of a node (same set as `structuralDagSize`). -/
  children : Expression.Expr → List Expression.Expr
    | .app _ fn arg => [fn, arg]
    | .ite _ c t f => [c, t, f]
    | .eq _ a b => [a, b]
    | .abs _ _ _ body => [body]
    | .quant _ _ _ _ tr body => [tr, body]
    | _ => []
  /-- Walk every subterm, incrementing each distinct subterm's occurrence tally.
      `seen` maps a structural hash to a bucket of `(subterm, occurrences)`. -/
  tally (work : List Expression.Expr)
     (seen : Std.HashMap UInt64 (List (Expression.Expr × Nat))) :
     Std.HashMap UInt64 (List (Expression.Expr × Nat)) :=
    match work with
    | [] => seen
    | e :: rest =>
      let h := LExpr.hashExpr e
      let bucket := seen.getD h []
      -- Every visited node is descended into (unlike the DAG measure, which prunes
      -- repeats): we need the true multiplicity of each subterm across the program.
      let seen := seen.insert h
        (if bucket.any (fun (e', _) => e' == e)
         then bucket.map (fun (e', c) => if e' == e then (e', c + 1) else (e', c))
         else (e, 1) :: bucket)
      tally (children e ++ rest) seen

/-- **Property P-CSE-6 (output-size bound on the DAG measure).** Your reviewer's
    "output doesn't grow more than it should", pinned to the *distinct-DAG-node*
    measure rather than tree size (CSE *adds* `var` decls, so a tree-size bound
    would report false failures). The number of fresh `var` declarations CSE
    introduces cannot exceed the number of distinct non-leaf subterms available
    to abbreviate, which is bounded by the input's structural DAG size. -/
def checkCseVarCountBounded (ss : List Statement) : Bool :=
  cseVarCount ss ≤ ((Statements.collectExprs ss).foldl
    (fun acc e => acc + structuralDagSize e) 0)

-- ── P-CSE-4: semantic preservation under evaluation ──────────────────────
-- This is the "model-preserving" claim of CR-289836082 itself: CSE must not
-- change what a program *means*. P-CSE-3 (no dangling bvar) and P-CSE-2 (typing
-- preservation) are cheap *necessary* conditions — they catch a capture that
-- produces an ill-scoped or ill-typed program. P-CSE-4 is the *sufficient* one:
-- it catches a capture that produces a program that is still well-typed but
-- computes a *different* result. It is the only property here that would fail on
-- a "well-typed but wrong" miscompile.
--
-- The observable. Strata ships a public statement-level symbolic simulator,
-- `Core.Statement.eval : Env → SubstMap → Statements → List Env × Statistics`,
-- which is exactly the evaluation oracle the plan doc flagged as missing. Its
-- expression evaluator *inlines store bindings* (`EC.eval` resolves every
-- in-scope `.fvar`), so a CSE-introduced `var $__cse.k := e; … assert P[$__cse.k]`
-- evaluates the assertion back to `P[e]` — the fresh abbreviation is substituted
-- away. Consequently the **proof obligations** the simulator emits (the
-- verifier-facing semantic output: the assert/cover/overflow conditions together
-- with their path-condition assumptions) are invariant under a *correct* CSE
-- pass, and differ under a capturing one. Because `ExpressionMetadata := Unit`,
-- `Expression.Expr`'s `BEq` is clean structural equality — no pretty-printing,
-- no brittle store diffing.
--
-- Two facts make this sound rather than lucky:
--  * `.init`/`var` commands only *update the store*; they never push a
--    path-condition entry (`Imperative.Cmd.eval`, CmdEval.lean). So the fresh
--    `$__cse.*` declarations never leak into obligation assumptions either.
--  * ite-branch path-condition *labels* embed the RAW, un-inlined branch
--    condition (`processIteBranches`: `<label_ite_cond_true: {cond.eraseTypes}>`),
--    which CSE *does* rewrite. So we compare obligation and assumption
--    *expressions* (which are inlined), never labels.
--
-- The simulator `panic!`s on `loop` statements — so we loop-eliminate first
-- (matching Strata's real LoopElim→CSE pipeline order; P-CSE properties #3/#4
-- certify that LoopElim preserves typing and removes every loop) and keep a
-- zero-loop backstop so a stray loop yields a vacuous pass rather than a panic.

/-- The semantic *observable* of a statement list: run the Core statement-level
    symbolic simulator (`Statement.eval`) from the initial Core environment and,
    for every resulting path and every proof obligation accumulated on it,
    collect a label-free signature — the obligation's `PropertyType`, its
    (evaluated) obligation expression, and the (evaluated) expressions of its
    path-condition assumptions. Labels are dropped because ite-branch labels
    embed the raw un-inlined condition (see the section note); everything
    retained is post-evaluation and hence free of `$__cse.*` abbreviations. -/
def obligationSignature (ss : List Statement) :
    List (Imperative.PropertyType × Expression.Expr × List Expression.Expr) :=
  let (envs, _) := Statement.eval Env.init [] ss
  envs.flatMap (fun E =>
    E.deferred.toList.map (fun ob =>
      (ob.property,
       ob.obligation,
       ob.assumptions.flatMap (fun pc =>
         pc.filterMap (fun
           | .assumption _ e => some e
           | _ => none)))))

/-- The *store* observable of a statement list, complementing `obligationSignature`.
    For every resulting path, collect the final value of every **user** variable:
    the single-map view of the evaluation store (`exprEnv.state.toSingleMap`), with
    the CSE-introduced `$__cse.*` temporaries dropped and each remaining value run
    through `E.exprEval` so any residual reference to a `$__cse.*` binding is
    inlined back to its definition. This makes the signature CSE-invariant for the
    same reason the obligation one is (the evaluator resolves store bindings), while
    covering the large class of programs that emit **no proof obligation at all** —
    e.g. straight-line `var`/`set` code, where a capture bug would corrupt a
    computed value with nothing in `deferred` to witness it. Because
    `ExpressionMetadata := Unit`, the resulting `Expr`s compare by clean structural
    equality; identifiers and the outer `List` lift that. -/
def storeSignature (ss : List Statement) :
    List (List (Expression.Ident × Expression.Expr)) :=
  let (envs, _) := Statement.eval Env.init [] ss
  envs.map (fun E =>
    E.exprEnv.state.toSingleMap.filterMap (fun (i, _, e) =>
      if i.name.startsWith Core.CSE.cseVarPrefix then none
      else some (i, E.exprEval e)))

/-- **Property P-CSE-4 (semantic preservation under evaluation).** The heart of
    the transform's "model-preserving" contract: CSE must not change program
    meaning. We compare **two** complementary observables produced by the symbolic
    simulator before and after CSE, and require *both* to match:

    * `obligationSignature` — the verification conditions (property kind +
      evaluated obligation expression + assumption expressions). Catches a capture
      that corrupts an `assert`/`cover`/overflow condition or a branch assumption.
    * `storeSignature` — the final value of every user variable on every path.
      Catches a capture that corrupts a *computed value* in straight-line code
      that emits no proof obligation at all — the majority of generated programs
      (~two-thirds have no obligation), which the obligation observable alone
      leaves as a vacuous `[] == []`.

    Both are CSE-invariant for the same reason: the simulator inlines the
    CSE-introduced `$__cse.*` bindings back to their definitions, so a correct pass
    leaves each observable identical, while a variable-capture bug that yields a
    well-typed-but-different program perturbs at least one of them. This is the
    failure mode P-CSE-2/3 (typing / no-dangling-index) cannot see. Empirically,
    over thousands of generated programs, neither observable is ever perturbed by
    CSE (no false positives) and together they give a non-vacuous check on ~50% of
    type-checking inputs vs. ~32% for obligations alone.

    Conditional and total: we loop-eliminate first (the simulator cannot evaluate
    `loop`s; this mirrors the real LoopElim→CSE pipeline), pass vacuously if any
    loop somehow survives (backstop against the simulator's `panic!`), and pass
    vacuously on input the typechecker rejects (only well-typed programs have
    semantics to preserve — cf. `checkCsePreservesTyping`). -/
def checkCseSemanticPreservation (ss : List Statement) : Bool :=
  let base := loopElimStmts ss
  if countLoopsStmts base != 0 then true
  else if !checkTypeChecks base then true
  else
    let cse := cseStmts base
    obligationSignature base == obligationSignature cse
      && storeSignature base == storeSignature cse

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

-- ── Function typechecker completeness ─────────────────────────────────────
-- `genFunction` is proven sound: every function it produces satisfies the
-- declarative spec `FuncHasType'`. So `Function.typeCheck` — whose *soundness* is
-- tested elsewhere but whose *completeness* is not — should accept every one. The
-- probe (see git history) shows it does NOT: the spec's `FuncHasType'` has no
-- field requiring a body (both `bodyTyped` and `measureTyped` are conditional on
-- the component being present), so a function with a **measure but no body**
-- satisfies the spec; but `Function.typeCheck` rejects it ("a decreases clause was
-- supplied but the function has no body", FunctionType.lean). This is the
-- function-level analogue of the statement-level `funcDecl` gap. Running against
-- the full `Core.Factory`/`Core.KnownTypes` (below), measure-without-body is the
-- *sole* cause — with a smaller factory, generated regex/real ops would spuriously
-- fail to resolve, masking the real gap.

/-- Whether `Function.typeCheck` accepts `func` in the full Core ambient context
    (`Core.Factory` + `Core.KnownTypes`, so every operator/type the generator can
    emit resolves). -/
def checkFunctionTypeChecks (func : Function) : Bool :=
  match Function.typeCheck stmtCheckContext TEnv.default func with
  | .ok _ => true
  | .error _ => false

/-- Whether `func` has a measure but no body — the spec-permitted, algorithm-
    rejected shape that witnesses the function typechecker's incompleteness. -/
def funcMeasureWithoutBody (func : Function) : Bool :=
  func.measure.isSome && func.body.isNone

/-- **Function typechecker completeness.** `genFunction` is sound (output satisfies
    `FuncHasType'`), so the algorithm should accept every generated function. This
    asserts that HONESTLY and so FAILS on the measure-without-body gap — a genuine
    spec/algorithm divergence, reported as a real failure with a minimal witness. -/
abbrev checkFunctionTypeCheckerComplete (func : Function) : Bool := checkFunctionTypeChecks func

/-- **Characterization of the function-completeness gap.** "Every rejection is a
    measure-without-body function." Accepts, OR is measure-without-body. This PINS
    measure-without-body as the sole known cause: it should pass, and a failure
    means `genFunction` produced a spec-well-typed function the algorithm rejects
    for some *other* reason — a new, unclassified completeness bug. -/
def funcRejectionImpliesMeasureNoBody (func : Function) : Bool :=
  checkFunctionTypeChecks func || funcMeasureWithoutBody func

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
