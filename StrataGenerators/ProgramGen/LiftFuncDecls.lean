-- The whole-program generator supplies the ambient program; `UnprovenTransforms`
-- supplies the shared plumbing (`runPhase` on a seeded transform state,
-- `progTypeChecks`, `nodup`, `programFuncs`) that the other transform families
-- already use, so nothing here re-implements it. The pass itself is imported
-- directly rather than reached through `Verifier`, so a rename upstream breaks the
-- build instead of silently skipping every property.
import StrataGenerators.ProgramGen.UnprovenTransforms
import Strata.Transform.LiftInternalFuncDecls

open Lambda Core Imperative
open StrataGenerators.Program.TestSupport
open StrataGenerators.Procedure.TestSupport
open StrataGenerators.Program.UnprovenTransforms

/-!
# Properties for `LiftInternalFuncDecls` — lambda lifting with declaration-site capture

This module holds the check predicates described in
`LIFT_INTERNAL_FUNCDECLS_PBT_PLAN.md`: property tests for
`Strata/Transform/LiftInternalFuncDecls.lean`, which hoists every internal
`Stmt.funcDecl` out of a procedure body into a closed top-level `Decl.func`.

It is a companion to `ProgramGen/UnprovenTransforms` and follows the
same shape: each predicate takes a whole generated `Core.Program` and returns a
`Bool`, both harnesses score the identical predicate, and the whole-program
shrinker minimizes a counterexample.

## What the pass does, and the one non-textbook part

It is **lambda lifting**, not closure conversion: free variables of the internal
function become extra *leading* parameters, the function is hoisted to the top
level, and every call site is given the extra arguments. There is no closure
datatype and no change to how functions are represented.

The one part with no textbook oracle is the **snapshot variable**. Strata is
imperative, and its evaluator gives `funcDecl` *declaration-time* capture
semantics (`Core.captureFreevars`), so the pass cannot pass the captured variable
at the call site — that would read a later value. Instead it emits
`var $__liftfncl_i := c` *in place of* the `funcDecl` statement, freezing `c`
there, and passes that snapshot at every call site. Textbook lifting would be
observably wrong whenever `c` is reassigned between the declaration and the call.

That design is what §"Findings" below turns out to hinge on: the *function* is
hoisted to the top level, but the *snapshot* stays at the original program point.

## What is already proved upstream, and what is not

`Strata/Transform/LiftInternalFuncDeclsCorrect.lean` proves `run_noFuncDecl`:
after the pass, no procedure body holds a `funcDecl`. That is the plan's **P2**,
so `checkLiftNoResidualFuncDecl` below is a regression gate on a proved theorem
rather than a probe. Everything else the pass claims is unproved — closedness
(the property the pass *exists* for, and which licenses the `LFuncClosed` remark
in `FactoryWF.lean`), the arity/type shape, name freshness, scope correctness of
the snapshots, the Johnsson fixpoint, and the rejection conditions.

## Why the input is a generated program plus a constructed injection

`genFuncDeclStmt` draws its `funcDecl` bodies with `genFunction []` — an **empty**
free-variable context — so every generated internal function is *closed*. The pass
would then have nothing to capture, every property below would hold vacuously, and
a green run would mean nothing.

So each predicate **injects** a capturing `funcDecl` into the generated program and
scores the pass on the result. `Scenario` names the shapes worth injecting and
`allScenarios` enumerates them; every predicate sweeps the whole list, so one draw
exercises every shape. The generated program supplies what a hand-built witness
cannot: arbitrary surrounding statements for the traversal to walk, and arbitrary
declarations for the name and factory logic to meet.

Names the injection introduces are freshened against the host procedure
(`mkNames`), so an injected program never collides with a generated identifier by
accident — the one property that is *about* collisions
(`checkLiftFreshSnapshotNames`) creates its collision deliberately.

## The typechecker guard, and why most properties do not use it

`Program.typeCheck` rejects about 60% of generated programs for three documented
reasons (see `ProgramGen/Shrink`'s module doc). Only the two properties whose
*claim* is about well-typedness — `checkLiftOutputTypechecks` and
`checkLiftRejectsOnlyKnownTriggers` — guard on `progTypeChecks`. The pass is
otherwise a syntactic program-to-program transform, so the structural properties
are stated unconditionally and stay non-vacuous on every draw.

## Findings

Measured over 20 draws at `numDecls := 6`, `size := 8`. Ten of the thirteen
properties hold on **20/20**; three fail on **0/20**, i.e. deterministically, and on
6 of the 15 injected shapes each time. `checkLiftInjectionFires` confirms the pass
really ran and really hoisted a function on 20/20, so none of the greens is vacuous.

**Two defects, both machine-checked, both reachable from a well-typed program.**

* `checkLiftOutputTypechecks` — **the snapshot init is left behind in a nested
  scope while the function is hoisted out of it.** When a `funcDecl` sits inside a
  `block` / `ite` / `loop` and is called anywhere outside that construct, the pass
  emits `var $__liftfncl_0 : int := c` *inside* the construct and rewrites the outer
  call site to `$__liftfncl_addC_1($__liftfncl_0, …)`. The snapshot is out of scope
  there, so `Program.typeCheck` **accepts the input and rejects the output**:

  ```
  No free variables are allowed here! Free Variables: [$__liftfncl_0]
  ```

  All four nesting shapes fail (`Placement.block`, `.ite`, `.elseArm`, `.loop`);
  the two same-scope shapes (`.top`, `.blockIn`) pass, which isolates the escape
  from the declaring scope as the cause. Core's own typechecker puts a `funcDecl`'s
  name in scope for the whole enclosing procedure — that is *why* the input is
  well-typed — so a call outside the declaring block is legal input, not a
  malformed program.

  Severity: `liftInternalFuncDeclsPipelinePhase` is the **first** phase of
  `transformPipelinePhases` and the pipeline's own `typeCheck` phase runs after all
  of them (`Verifier.lean`), so this surfaces to a user as
  `❌ Type checking error` on a program that was well typed as written.

* `checkLiftFreshSnapshotNames` — **the minted names are not checked against the
  program's own identifiers.** A procedure that already declares
  `$__liftfncl_0` gets a *second* declaration of it, and the typechecker rejects the
  output with `Variable $__liftfncl_0 of type int already in context.`
  `CoreGenState.gen` (`CoreGen.lean`) delegates to `StringGenState.gen`
  (`StringGen.lean`), which is a bare counter: it guarantees uniqueness only
  among the names *it* minted, never against the program.

  The pass's module doc states the assumption honestly ("it is assumed that the
  input Core program doesn't have any identifier starting with this prefix … a way
  of enforcing absence of these is necessary in the future"), so this is a
  documented gap rather than a surprise. Two things are still worth reporting: the
  `hoistProcedure` comment claiming the generator is "collision-proof against user
  names" overstates what `StringGenState.gen` provides, and this is the *same*
  defect class as the already-filed `checkCseFreshNamesFresh` (`CommonSubexprElim`
  mints `$__cse.0` without reading a program name) — two passes, one missing
  mechanism.

**Everything else passes, including three things the plan expected to be weak:**

* Capture through `axioms`, `preconditions` and `measure` — the plan's §6.2 calls a
  body-only generator "the most likely coverage gap". The pass handles all four
  fields correctly: each is rewritten to the snapshot parameter and survives into
  the emitted function. `CaptureVia` covers all four.
* `substOps` under a binder (plan P11) — a sibling call inside `forall z :: …` is
  rewritten correctly. The replacement is an operator applied to *free* snapshot
  variables, so the documented bvar-lifting side condition holds.
* The Johnsson fixpoint (plan P8) — `checkLiftFixpointMatchesReference` scores the
  pass against an independent least-fixpoint implementation of Levy–Reeves Def 4.6
  (`extCapturedRef`) and they agree, including on the chain and star shapes.

**One rejection trigger is unreachable from well-typed input.** Of the four
conditions `processDecl` rejects, `isRecursive` cannot be reached: Core's
`funcDecl` typing rule requires a non-recursive declaration, so a program carrying
one fails `Program.typeCheck` before the pass sees it. The
`Scenario.recursiveDecl` case is therefore scored only by a `#guard`, and
`checkLiftRejectsOnlyKnownTriggers` treats it as a skip.

**A methodological finding worth keeping.** The first run of this suite read 6/20
on all three failing properties, and the first draw's diagnostic said everything
passed — signal that turned out to be noise. `run` folds `processDecl` over the
declarations with `foldlM`, so a rejection in *any* procedure aborts the whole
program, and 5 of 20 draws carried their own trigger (a generated internal function
name clashing with a top-level one, or sitting beside a local `typeDecl`). Those
draws took the injected scenario down with them and every property scored
vacuously green. `normalizeAmbient` fixes the cause and `checkLiftInjectionFires`
scores the symptom, so the same masking cannot come back unnoticed.

**Not covered here.** The plan's semantic tier — P13 (bidirectional operational
correctness), P14 (verification-outcome preservation) and P16 (the
snapshot-vs-call-site differential that would pin the declaration-time capture
semantics) — needs the symbolic evaluator and a decision about comparing
`List Env`. The structural layer had to be trusted first, and it is not: it found
the two defects above.
-/

namespace StrataGenerators.Program.LiftFuncDecls

/-! ## The prefix the pass mints under

`Core.LiftInternalFuncDecls.liftPrefix` is `private`, so it cannot be read. This
mirrors it. `liftPrefixAgrees` below pins the mirror against the pass's actual
output, so a change upstream fails a `#guard` here instead of silently making
every "is this a lifted function" test vacuous. -/

/-- Mirror of the pass's private `liftPrefix`. -/
def liftPrefix : String := "$__liftfncl"

/-! ## Reading a program

Small accessors. `programFuncs`, `nodup` and `runPhase` come from the sibling
modules and are reused rather than restated. -/

/-- The pass, as a `PipelinePhase`. Named once so every property runs the same
    thing. -/
def liftPhase : Core.PipelinePhase := Core.liftInternalFuncDeclsPipelinePhase

/-- Run the pass on a program: `none` if it raised a diagnostic. -/
def runLift (p : Program) : Option (Bool × Program) := runPhase liftPhase p

/-- The name of every function the program declares. -/
def funcNames (p : Program) : List String := (programFuncs p).map (·.name.name)

/-- The functions present in `out` but not in `inp`, by name — i.e. the ones the
    pass hoisted. Computed as a set difference rather than by matching the
    `$__liftfncl` prefix, so it stays correct if the prefix changes. -/
def liftedFuncs (inp out : Program) : List Function :=
  let before := funcNames inp
  (programFuncs out).filter (fun f => !before.contains f.name.name)

/-- The internal `funcDecl` declarations of a statement list, at any depth. -/
partial def bodyFuncDecls (ss : List Statement) : List (Imperative.PureFunc Expression) :=
  ss.flatMap fun s =>
    match s with
    | .funcDecl d _ => [d]
    | .block _ b _ => bodyFuncDecls b
    | .ite _ t e _ => bodyFuncDecls t ++ bodyFuncDecls e
    | .loop _ _ _ b _ => bodyFuncDecls b
    | _ => []

/-- Every internal `funcDecl` of every procedure of the program. -/
def programFuncDecls (p : Program) : List (Imperative.PureFunc Expression) :=
  (programBodies p).flatMap bodyFuncDecls

/-- Whether any procedure body still holds a `funcDecl`, at any depth. Reuses
    Strata's own `Block.noFuncDecl`, which is what `run_noFuncDecl` is stated
    with, rather than a private re-walk. -/
def anyResidualFuncDecl (p : Program) : Bool :=
  (programBodies p).any (fun ss => !decide (Imperative.Block.noFuncDecl ss))

/-! ## Closedness — the property the pass exists for

Two notions, because Strata's own one is weaker than what the pass computes.

`Lambda.LFuncClosed` constrains only `body` and `preconditions`
(`FuncClosed`, `Func.lean`). But `capturedVars` unions the free variables of
`body`, `axioms`, `preconditions` **and** `measure`, and `rewritePureFunc`
rewrites all four. So a function with an open `axioms` field would satisfy
`LFuncClosed` while still mentioning a variable that no longer exists. Both are
checked: Strata's notion, so a green tick means the real predicate the pass is
supposed to establish, and the stronger all-four-fields notion, so the gap in
`LFuncClosed` cannot hide a defect. -/

/-- Every free variable of every one of `f`'s four expression-carrying fields that
    is not one of `f`'s own inputs. Empty is the strong closedness the pass's
    `capturedVars`/`rewritePureFunc` pair should establish. -/
def openVars (f : Function) : List String :=
  let formals := f.inputs.map (fun iv => iv.1.name)
  let fvs := (f.body.map Lambda.LExpr.freeVars).getD []
    ++ f.axioms.flatMap Lambda.LExpr.freeVars
    ++ f.preconditions.flatMap (fun q => Lambda.LExpr.freeVars q.expr)
    ++ (f.measure.map Lambda.LExpr.freeVars).getD []
  ((fvs.map (fun v => v.1.name)).filter (fun n => !formals.contains n)).dedup

/-- `Lambda.LFuncClosed` is a structure with no `Decidable` instance, though each
    of its two inherited `FuncClosed` fields has one
    (`FuncClosed.body_freevars_decidable`, `FuncClosed.precond_freevars_decidable`).
    This assembles them, so `strataClosed` below decides *Strata's* predicate
    rather than a local restatement of it. -/
instance instDecidableLFuncClosed {T : Lambda.LExprParams} (f : Lambda.LFunc T) :
    Decidable (Lambda.LFuncClosed f) :=
  let getName := fun (id : T.Identifier) => id.name
  let getVarNames := fun (e : Lambda.LExpr T.mono) =>
    (Lambda.LExpr.freeVars e).map (fun v => v.1.name)
  match Strata.DL.Util.FuncClosed.body_freevars_decidable getName getVarNames f.toFunc,
        Strata.DL.Util.FuncClosed.precond_freevars_decidable getName getVarNames f.toFunc with
  | isTrue h1, isTrue h2 => isTrue ⟨h1, h2⟩
  | isFalse h1, _ => isFalse (fun h => h1 h.body_freevars)
  | _, isFalse h2 => isFalse (fun h => h2 h.precond_freevars)

/-- Strata's own closedness predicate, decided. This is the one the pass is
    supposed to establish for every function in the program. -/
def strataClosed (f : Function) : Bool := decide (Lambda.LFuncClosed f.toLFunc)

/-! ## Levy–Reeves Def 4.6 — an independent least fixpoint

The algorithmically interesting part of the pass is Phase 2 of `hoistProcedure`:

    extCaptured(f) = own(f) ∪ ⋃ { extCaptured(g) | g a sibling called by f }

as a least fixpoint over the sibling call graph. This is Levy–Reeves Def 4.6
specialised to Strata's flat scope structure (a `funcDecl` carries a `PureFunc`
whose body is an expression, so internal functions cannot nest, hence all of a
procedure's internal functions are siblings and Def 4.6's "not the declaring
function" guard can never fire).

`extCapturedRef` computes it independently, over *original* variable names rather
than the pass's minted snapshot names, so the two implementations share no code.
Iterating `decls.length + 1` times is enough: each round either adds a name to
some set or the fixpoint is reached, and a chain of `n` siblings propagates a name
`n` steps. -/

/-- The free variables of `d` that are not `d`'s own formals — Def 4.6 clause (1),
    "a referenced non-local of `f`". Reads the same four fields the pass does. -/
def ownCaptures (d : Imperative.PureFunc Expression) : List String :=
  let formals := d.inputs.map (fun iv => iv.1.name)
  let fvs := (d.body.map Lambda.LExpr.freeVars).getD []
    ++ d.axioms.flatMap Lambda.LExpr.freeVars
    ++ d.preconditions.flatMap (fun q => Lambda.LExpr.freeVars q.expr)
    ++ (d.measure.map Lambda.LExpr.freeVars).getD []
  ((fvs.map (fun v => v.1.name)).filter (fun n => !formals.contains n)).dedup

/-- The siblings `d` calls: operator references in any of its four fields whose
    name is another internal function of the same procedure. -/
def calledSiblingsRef (siblings : List String) (d : Imperative.PureFunc Expression) :
    List String :=
  let ops := (d.body.map Lambda.LExpr.getOps).getD []
    ++ d.axioms.flatMap Lambda.LExpr.getOps
    ++ d.preconditions.flatMap (fun q => Lambda.LExpr.getOps q.expr)
    ++ (d.measure.map Lambda.LExpr.getOps).getD []
  ((ops.map (fun o => o.name)).filter siblings.contains).dedup

/-- One propagation round of Def 4.6 clause (2). -/
def extStep (decls : List (Imperative.PureFunc Expression)) (siblings : List String)
    (cur : List (String × List String)) : List (String × List String) :=
  decls.map fun d =>
    let nm := d.name.name
    let mine := (cur.find? (fun e => e.1 == nm)).map (·.2) |>.getD []
    let inherited := (calledSiblingsRef siblings d).flatMap fun g =>
      (cur.find? (fun e => e.1 == g)).map (·.2) |>.getD []
    (nm, (mine ++ inherited).dedup)

/-- The least fixpoint of Def 4.6 for one procedure's internal functions, as
    `(functionName, capturedVariableNames)` pairs. Independent of the pass. -/
def extCapturedRef (decls : List (Imperative.PureFunc Expression)) :
    List (String × List String) :=
  let siblings := decls.map (fun d => d.name.name)
  let init := decls.map (fun d => (d.name.name, ownCaptures d))
  -- `decls.length + 1` rounds suffice; see the section note.
  (List.range (decls.length + 1)).foldl (fun acc _ => extStep decls siblings acc) init

/-! ## Scope tracking — is a snapshot visible where it is used?

The direct, non-typechecker statement of the plan's P7: walk the output body
carrying the set of variables in scope, and check that every `$__liftfncl`
free variable a statement mentions has already been declared in an enclosing or
current scope. A `block` / `ite` arm / `loop` body extends the scope for its own
statements only, which is exactly the scoping the defect violates.

`checkLiftOutputTypechecks` is the authoritative oracle (it is Strata's own
checker); this one localises the failure to "a snapshot is used out of scope"
rather than reporting a generic type error. -/

/-- Every free variable named in an expression. -/
def exprFvarNames (e : Expression.Expr) : List String :=
  (Lambda.LExpr.freeVars e).map (fun v => v.1.name)

/-- The free variables a single command mentions, and the variable it declares. -/
def cmdVars : Command → List String × Option String
  | .cmd (.init n _ (.det e) _) => (exprFvarNames e, some n.name)
  | .cmd (.init n _ .nondet _) => ([], some n.name)
  | .cmd (.set _ (.det e) _) => (exprFvarNames e, none)
  | .cmd (.set _ .nondet _) => ([], none)
  | .cmd (.assert _ e _) | .cmd (.assume _ e _) | .cmd (.cover _ e _) =>
    (exprFvarNames e, none)
  | .call _ args _ =>
    (args.flatMap fun
      | .inArg e => exprFvarNames e
      | .inoutArg _ | .outArg _ => [], none)

/-- Whether every `liftPrefix` variable used in `ss` is in scope, given the
    variables `scope` already in scope. Returns `false` on the first use of a
    snapshot variable that has not been declared at that point. -/
partial def snapshotsInScope (scope : List String) (ss : List Statement) : Bool :=
  match ss with
  | [] => true
  | s :: rest =>
    let ok : Bool × List String :=
      match s with
      | .cmd c =>
        let (used, declared) := cmdVars c
        let bad := used.any (fun n => n.startsWith liftPrefix && !scope.contains n)
        (!bad, match declared with | some d => d :: scope | none => scope)
      | .block _ b _ => (snapshotsInScope scope b, scope)
      | .ite c t e _ =>
        let guardUsed := match c with | .det g => exprFvarNames g | .nondet => []
        let bad := guardUsed.any (fun n => n.startsWith liftPrefix && !scope.contains n)
        (!bad && snapshotsInScope scope t && snapshotsInScope scope e, scope)
      | .loop g m invs b _ =>
        let used := (match g with | .det x => exprFvarNames x | .nondet => [])
          ++ (m.map exprFvarNames).getD [] ++ invs.flatMap (fun iv => exprFvarNames iv.2)
        let bad := used.any (fun n => n.startsWith liftPrefix && !scope.contains n)
        (!bad && snapshotsInScope scope b, scope)
      | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => (true, scope)
    ok.1 && snapshotsInScope ok.2 rest

/-- Every snapshot variable a procedure uses is in scope where it is used, taking
    the procedure's own parameters as the initial scope. -/
def procSnapshotsInScope (q : Procedure) : Bool :=
  let params := (q.header.inputs.map (fun iv => iv.1.name))
    ++ (q.header.outputs.map (fun ov => ov.1.name))
  snapshotsInScope params (bodyStmts q.body)

/-! ## The injected shapes

`genFuncDeclStmt` cannot produce a capturing `funcDecl` (see the module doc), so
each property injects one. A `Scenario` is the dimensions worth varying, and
`allScenarios` is the curated cross-product every property sweeps.

The four dimensions come straight from the plan's §6 generator requirements:

* `Placement` — where the `funcDecl` sits relative to its call sites. The plan's
  P7 names the three escaping shapes (declared in a branch and used after the
  `if`; used in the sibling arm; declared in a loop body) and this adds the
  labelled-`block` case. `.top` and `.blockIn` are the controls where the call is
  in the declaring scope.
* `CaptureVia` — which of the four fields `capturedVars` unions carries the
  captured variable. §6.2 calls a body-only generator "the most likely coverage
  gap".
* `CallShape` — the sibling call graph the Johnsson fixpoint runs over. `.chain`
  is a capturing function called by a non-capturing one (the case where the
  fixpoint must propagate); `.star` has one caller and two callees capturing
  *different* variables, so the union is non-trivial.
* `underBinder` — wraps the sibling call in a `forall`, so `substOps` has to go
  under a binder (plan P11). -/

/-- Where the injected `funcDecl` sits relative to the calls that reach it. -/
inductive Placement where
  /-- Declaration and calls both at the top level of the body. -/
  | top
  /-- Declaration and calls both inside one labelled block. -/
  | blockIn
  /-- Declaration inside a labelled block, calls after the block. -/
  | block
  /-- Declaration in a then-branch, calls after the `ite`. -/
  | ite
  /-- Declaration in a then-branch, calls in the `else` arm. -/
  | elseArm
  /-- Declaration in a loop body, calls after the loop. -/
  | loop
  deriving DecidableEq, Repr

/-- Which field of the `PureFunc` carries the captured variable. -/
inductive CaptureVia where
  | body | axioms | preconditions | measure
  deriving DecidableEq, Repr

/-- The sibling call graph among the injected functions. -/
inductive CallShape where
  /-- One capturing function, no sibling calls. -/
  | solo
  /-- A non-capturing caller of a capturing callee — the fixpoint must propagate. -/
  | chain
  /-- One caller, two callees capturing *different* variables. -/
  | star
  deriving DecidableEq, Repr

/-- One injected shape. -/
structure Scenario where
  /-- Display name, used by the diagnostics to say which shape failed. -/
  label : String
  placement : Placement
  captureVia : CaptureVia
  callShape : CallShape
  /-- Reassign the captured variable between the declaration and the calls. This
      is the case where declaration-site capture and call-site capture disagree,
      so it is the one textbook lambda lifting would get wrong. -/
  reassign : Bool
  /-- Put the sibling call under a quantifier, so `substOps` goes under a binder. -/
  underBinder : Bool
  deriving DecidableEq, Repr

/-- The shapes every property sweeps. Ordered controls-first, so a diagnostic that
    lists failures reads as "the same-scope shapes pass, the escaping ones do
    not". -/
def allScenarios : List Scenario :=
  [ ⟨"top/body", .top, .body, .solo, false, false⟩,
    ⟨"top/body/reassign", .top, .body, .solo, true, false⟩,
    ⟨"top/axioms", .top, .axioms, .solo, false, false⟩,
    ⟨"top/preconditions", .top, .preconditions, .solo, false, false⟩,
    ⟨"top/measure", .top, .measure, .solo, false, false⟩,
    ⟨"top/body/chain", .top, .body, .chain, false, false⟩,
    ⟨"top/body/star", .top, .body, .star, false, false⟩,
    ⟨"top/body/chain/binder", .top, .body, .chain, false, true⟩,
    ⟨"blockIn/body", .blockIn, .body, .solo, false, false⟩,
    ⟨"block/body", .block, .body, .solo, false, false⟩,
    ⟨"ite/body", .ite, .body, .solo, false, false⟩,
    ⟨"elseArm/body", .elseArm, .body, .solo, false, false⟩,
    ⟨"loop/body", .loop, .body, .solo, false, false⟩,
    ⟨"block/body/chain", .block, .body, .chain, false, false⟩,
    ⟨"ite/measure", .ite, .measure, .solo, false, false⟩ ]

/-! ## Building the injection

Every name the injection introduces is freshened against the names the host
program already uses, so a collision is never an accident of the draw. -/

/-- The names declared by a statement list, at any depth: `init` targets,
    `funcDecl` names, and block labels. Together with the procedure headers and
    the declaration names, this is what an injected name could collide with. -/
partial def bodyDeclaredNames (ss : List Statement) : List String :=
  ss.flatMap fun s =>
    match s with
    | .cmd (.cmd (.init n _ _ _)) => [n.name]
    | .cmd _ => []
    | .funcDecl d _ => [d.name.name]
    | .typeDecl tc _ => [tc.name]
    | .block l b _ => l :: bodyDeclaredNames b
    | .ite _ t e _ => bodyDeclaredNames t ++ bodyDeclaredNames e
    | .loop _ _ _ b _ => bodyDeclaredNames b
    | .exit _ _ => []

/-- Every name in the program an injected name must avoid. -/
def usedNames (p : Program) : List String :=
  declNames p
  ++ (programProcs p).flatMap (fun nq =>
       (nq.2.header.inputs.map (fun iv => iv.1.name))
       ++ (nq.2.header.outputs.map (fun ov => ov.1.name))
       ++ bodyDeclaredNames (bodyStmts nq.2.body))
  ++ funcNames p

/-- The names one injection uses. -/
structure InjNames where
  /-- The captured local. -/
  cap1 : String
  /-- A second captured local, for `CallShape.star`. -/
  cap2 : String
  /-- The injected functions' shared formal parameter name. -/
  formal : String
  /-- The caller (the function the injected call site names). -/
  fn1 : String
  /-- A callee, for `.chain` and `.star`. -/
  fn2 : String
  /-- A second callee, for `.star`. -/
  fn3 : String
  /-- The local that receives the call result. -/
  res : String
  /-- The label of the injected block, for the `block` placements. -/
  blockLbl : String

/-- Append the first index that makes `base` unused. Always appends, so the
    injected names are recognisable in a counterexample. -/
def freshen (used : List String) (base : String) : String :=
  match (List.range 64).find? (fun i => !used.contains s!"{base}{i}") with
  | some i => s!"{base}{i}"
  | none => s!"{base}$"

/-- Freshen every injected name against `p`. The `$lift$` infix is deliberate: it
    cannot be confused with the pass's own `$__liftfncl` prefix, which
    `checkLiftFreshSnapshotNames` needs to be the *only* source of that prefix. -/
def mkNames (p : Program) : InjNames :=
  let u := usedNames p
  { cap1 := freshen u "$lift$c", cap2 := freshen u "$lift$d",
    formal := freshen u "$lift$x",
    fn1 := freshen u "$lift$f", fn2 := freshen u "$lift$g",
    fn3 := freshen u "$lift$h",
    res := freshen u "$lift$r", blockLbl := freshen u "$lift$B" }

/-! ### Expression and statement builders -/

/-- `int -> int -> int`, the type of a binary integer operator. -/
def intBinOpTy : LMonoTy := .tcons "arrow" [.int, .tcons "arrow" [.int, .int]]
/-- `int -> int`, the type of the injected functions. -/
def intFnTy : LMonoTy := .tcons "arrow" [.int, .int]
/-- `int -> bool`, the type of an injected function whose body is a quantifier. -/
def intPredTy : LMonoTy := .tcons "arrow" [.int, .bool]

def intLit (i : Int) : Expression.Expr := .const () (.intConst i)
/-- An `int`-annotated free variable. The annotation is what `capturedVars` reads
    the captured variable's type off, so it must be present. -/
def fvInt (n : String) : Expression.Expr := .fvar () ⟨n, ()⟩ (some .int)
/-- `Int.Add(a, b)`, with the operator annotated. -/
def addI (a b : Expression.Expr) : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Add", ()⟩ (some intBinOpTy)) a) b
/-- A call `f(arg)` of an injected `int -> int` function. -/
def callInt (f : String) (arg : Expression.Expr) : Expression.Expr :=
  .app () (.op () ⟨f, ()⟩ (some intFnTy)) arg

/-- `var n : int := i`. -/
def declInt (n : String) (i : Int) : Statement :=
  Statement.init ⟨n, ()⟩ (.forAll [] .int) (.det (intLit i)) .empty

/-- The injected `funcDecl`'s declaration: formal `x : int`, output `int`, with the
    captured variable placed in the field `via` names and an optional sibling call
    in the body. -/
def mkDecl (nm : InjNames) (via : CaptureVia) (fname : String)
    (captured : Option String) (callee : Option String) :
    Imperative.PureFunc Expression :=
  let cap := (captured.map fvInt).getD (intLit 0)
  let base := match callee with
    | some g => addI (fvInt nm.formal) (callInt g (fvInt nm.formal))
    | none => fvInt nm.formal
  let bodyExpr := match via with
    | .body => if captured.isSome then addI base cap else base
    | _ => base
  { name := ⟨fname, ()⟩,
    inputs := [(⟨nm.formal, ()⟩, (.forAll [] .int : LTy))],
    output := (.forAll [] .int : LTy),
    body := some bodyExpr,
    axioms := match via with
      | .axioms => if captured.isSome then [.eq () cap cap] else []
      | _ => [],
    preconditions := match via with
      | .preconditions => if captured.isSome then [{ expr := .eq () cap cap, md := () }] else []
      | _ => [],
    measure := match via with
      | .measure => if captured.isSome then some cap else none
      | _ => none }

/-- A caller whose body is `forall z : int :: g(z) == z`, so the sibling call sits
    under a binder and `substOps` must go through it. Output type is `bool`. -/
def mkBinderDecl (nm : InjNames) (fname callee : String) :
    Imperative.PureFunc Expression :=
  { name := ⟨fname, ()⟩,
    inputs := [(⟨nm.formal, ()⟩, (.forAll [] .int : LTy))],
    output := (.forAll [] .bool : LTy),
    body := some (.quant () .all "z" (some .int) (.const () (.boolConst true))
                    (.eq () (callInt callee (.bvar () 0)) (.bvar () 0))) }

/-- The `funcDecl` statements the scenario declares, innermost callee first so a
    caller's reference is to an already-declared sibling (which is what Core's own
    typechecker requires of the input). -/
def scenarioDecls (sc : Scenario) (nm : InjNames) : List Statement :=
  match sc.callShape with
  | .solo =>
    [Stmt.funcDecl (mkDecl nm sc.captureVia nm.fn1 (some nm.cap1) none) .empty]
  | .chain =>
    [ Stmt.funcDecl (mkDecl nm sc.captureVia nm.fn2 (some nm.cap1) none) .empty,
      Stmt.funcDecl
        (if sc.underBinder then mkBinderDecl nm nm.fn1 nm.fn2
         else mkDecl nm sc.captureVia nm.fn1 none (some nm.fn2)) .empty ]
  | .star =>
    [ Stmt.funcDecl (mkDecl nm sc.captureVia nm.fn2 (some nm.cap1) none) .empty,
      Stmt.funcDecl (mkDecl nm sc.captureVia nm.fn3 (some nm.cap2) none) .empty,
      Stmt.funcDecl
        { mkDecl nm sc.captureVia nm.fn1 none (some nm.fn2) with
          body := some (addI (callInt nm.fn2 (fvInt nm.formal))
                             (callInt nm.fn3 (fvInt nm.formal))) } .empty ]

/-- The statements that call the injected caller. A `bool`-output caller (the
    binder shape) is used by an `assume` rather than by an `init`. -/
def scenarioCalls (sc : Scenario) (nm : InjNames) : List Statement :=
  let call : Statement :=
    if sc.underBinder && sc.callShape == .chain then
      Statement.assume nm.res
        (.app () (.op () ⟨nm.fn1, ()⟩ (some intPredTy)) (intLit 0)) .empty
    else
      Statement.init ⟨nm.res, ()⟩ (.forAll [] .int)
        (.det (callInt nm.fn1 (intLit 0))) .empty
  if sc.reassign then [Statement.set ⟨nm.cap1, ()⟩ (intLit 999) .empty, call] else [call]

/-- Place the declarations and the calls per the scenario's `Placement`. -/
def placeGroup (pl : Placement) (lbl : String) (decls calls : List Statement) :
    List Statement :=
  let tt : ExprOrNondet Expression := .det (.const () (.boolConst true))
  let ff : ExprOrNondet Expression := .det (.const () (.boolConst false))
  match pl with
  | .top => decls ++ calls
  | .blockIn => [.block lbl (decls ++ calls) .empty]
  | .block => .block lbl decls .empty :: calls
  | .ite => .ite tt decls [] .empty :: calls
  | .elseArm => [.ite tt decls calls .empty]
  | .loop => .loop ff none [] decls .empty :: calls

/-- The statements the scenario injects: the captured locals, then the declaration
    group and the calls placed per `Placement`. The locals are declared at the top
    level of the body so they are in scope in every placement — the captured
    variable's own scope is never the thing under test. -/
def scenarioStmts (sc : Scenario) (nm : InjNames) : List Statement :=
  declInt nm.cap1 10 :: declInt nm.cap2 20
    :: placeGroup sc.placement nm.blockLbl (scenarioDecls sc nm) (scenarioCalls sc nm)

/-! ### Splicing into the program -/

/-- A minimal procedure holding `ss`, used when the draw has no procedure with a
    structured body to inject into. -/
def fallbackProc (n : String) (ss : List Statement) : Procedure :=
  { header := { name := ⟨n, ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured ss }

/-- Prepend `extra` to the body of the program's first structured-body procedure.
    If the draw has none, a fresh procedure holding `extra` is appended instead, so
    the injection — and every property that reads it — is never vacuous. -/
def injectStmts (extra : List Statement) (p : Program) : Program :=
  let (ds, done) := p.decls.foldl
    (fun (acc : List Decl × Bool) d =>
      if acc.2 then (acc.1 ++ [d], true)
      else match d with
        | .proc q md =>
          match q.body with
          | .structured ss => (acc.1 ++ [.proc { q with body := .structured (extra ++ ss) } md], true)
          | .cfg _ => (acc.1 ++ [d], false)
        | _ => (acc.1 ++ [d], false))
    ([], false)
  if done then { decls := ds }
  else { decls := ds ++ [.proc (fallbackProc (freshen (usedNames p) "$lift$P") extra) .empty] }

/-! ### Normalizing the ambient draw

`run` folds `processDecl` over the declarations with `foldlM`, so a `throw` in
*any* procedure aborts the whole program. A draw whose own internal functions
happen to trip one of the four rejection conditions therefore takes the injected
scenario down with it: the pass returns a diagnostic, and every property below is
vacuously green without saying so. Measured on 20 draws, 5 were lost this way.

`stripInternalDecls` removes the draw's own `funcDecl` and local `typeDecl`
statements before injecting, which is what the three reachable triggers need
(duplicate internal names, a clash with a top-level function, a local type
declaration beside a function declaration). Nothing of interest is lost:
`genFuncDeclStmt` draws its bodies with `genFunction []`, so every generated
internal function is *closed* and contributes no capture — they are exactly the
declarations these properties have nothing to say about. The draw's blocks, `ite`
arms, loops and commands are all still there for the traversal to walk.

`checkLiftRejectsOnlyKnownTriggers` deliberately does **not** normalize: its whole
claim is about which inputs get rejected, so it needs the raw draw's triggers to
stay reachable. -/

/-- Remove every `funcDecl` and local `typeDecl` statement, at any depth. -/
partial def stripInternalDecls (ss : List Statement) : List Statement :=
  ss.filterMap fun s =>
    match s with
    | .funcDecl _ _ | .typeDecl _ _ => none
    | .block l b md => some (.block l (stripInternalDecls b) md)
    | .ite c t e md => some (.ite c (stripInternalDecls t) (stripInternalDecls e) md)
    | .loop g m invs b md => some (.loop g m invs (stripInternalDecls b) md)
    | .cmd _ | .exit _ _ => some s

/-- The program with every procedure body's own internal declarations stripped. -/
def normalizeAmbient (p : Program) : Program :=
  { decls := p.decls.map fun
      | .proc q md =>
        match q.body with
        | .structured ss => .proc { q with body := .structured (stripInternalDecls ss) } md
        | .cfg _ => .proc q md
      | d => d }

/-- The generated program, normalized, with `sc` injected into it. -/
def applyScenario (sc : Scenario) (p : Program) : Program :=
  let base := normalizeAmbient p
  injectStmts (scenarioStmts sc (mkNames p)) base

/-! ## The properties

Each sweeps `allScenarios`, so one draw scores every injected shape. `scenarioFails`
is the shared kernel: it takes a per-scenario verdict and returns the labels of the
shapes that failed, which both the properties and the diagnostics read — a panel
can therefore never display a verdict other than the one that was scored. -/

/-- The labels of the scenarios on which `verdict` fails, given the injected
    program and, when the pass ran, its `(changed, output)` pair. -/
def scenarioFails (p : Program)
    (verdict : Scenario → Program → Option (Bool × Program) → Bool) : List String :=
  allScenarios.filterMap fun sc =>
    let q := applyScenario sc p
    if verdict sc q (runLift q) then none else some sc.label

/-- A verdict that only looks at a successful run, skipping a diagnostic. Several
    properties are about what the output *is*, and a rejection is scored by
    `checkLiftRejectsOnlyKnownTriggers` instead. -/
def onOutput (f : Program → Program → Bool) :
    Scenario → Program → Option (Bool × Program) → Bool :=
  fun _ q r => match r with
    | none => true
    | some (_, out) => f q out

/-- **Coverage, not a claim about the pass.** On every injected shape the pass
    really ran, really reported `changed`, and really hoisted at least one
    function.

    This exists because every other property here is stated to *skip* a run that
    returned a diagnostic — which is right (a rejection is scored by
    `checkLiftRejectsOnlyKnownTriggers`, not by the closedness properties) but
    means a draw the pass refuses makes them all vacuously green in silence. That
    is not hypothetical: before `normalizeAmbient` existed, 5 of 20 draws were lost
    that way, and three properties read 6/20 for reasons that had nothing to do
    with the pass. Scoring coverage as its own property turns that failure mode
    from invisible into red. -/
def checkLiftInjectionFires (p : Program) : Bool :=
  (scenarioFails p (fun _ q r =>
    match r with
    | none => false
    | some (changed, out) => changed && !(liftedFuncs q out).isEmpty)).isEmpty

/-- **P1 — closedness, the property the pass exists for.** Every function the pass
    hoists is closed: no free variable outside its own inputs, in any of the four
    expression-carrying fields. This is what licenses the `LFuncClosed` remark in
    `FactoryWF.lean`, so it gets the widest scenario sweep.

    Stated over `openVars` (all four fields) rather than `strataClosed`
    (`Lambda.LFuncClosed`, which constrains only `body` and `preconditions`) — see
    the closedness section note. `checkLiftStrataClosed` covers Strata's own
    weaker predicate separately. -/
def checkLiftAllFuncsClosed (p : Program) : Bool :=
  (scenarioFails p (onOutput fun q out =>
    (liftedFuncs q out).all (fun f => (openVars f).isEmpty))).isEmpty

/-- **P1, in Strata's own words.** Every function in the output — hoisted or
    pre-existing — satisfies `Lambda.LFuncClosed`. Weaker than
    `checkLiftAllFuncsClosed` (it ignores `axioms` and `measure`) but it is the
    predicate the rest of Strata consumes. -/
def checkLiftStrataClosed (p : Program) : Bool :=
  (scenarioFails p (onOutput fun _ out => (programFuncs out).all strataClosed)).isEmpty

/-- **P2 — no residual `funcDecl`.** Proved upstream as `run_noFuncDecl`, so this
    is a regression gate rather than a probe. Kept because every call-site property
    depends on it: `Stmt.mapExpr` does not recurse into `funcDecl`
    (`Stmt.lean`), so a `funcDecl` that survived stripping would have its inner
    call sites silently left un-rewritten. -/
def checkLiftNoResidualFuncDecl (p : Program) : Bool :=
  (scenarioFails p (onOutput fun _ out => !anyResidualFuncDecl out)).isEmpty

/-- **P3 — idempotence.** A second run changes nothing and returns the same
    program. Follows from P2, so a violation means the traversal missed a nesting
    position. -/
def checkLiftIdempotent (p : Program) : Bool :=
  (scenarioFails p (onOutput fun _ out =>
    match runLift out with
    | none => false
    | some (changed, out2) => !changed && decide (out2 = out))).isEmpty

/-- **P4 — identity on a program with no `funcDecl`.** The un-injected draw is
    left alone: `changed = false` and the output is syntactically the input. Since
    `liftInternalFuncDecls` infers `changed` from `decls.length != decls.length`,
    this also pins that proxy on the one input where it is unambiguous.

    Note this is the *only* property that scores the raw draw rather than an
    injection — a generated program's own `funcDecl`s are all closed, but they are
    still lifted, so `p` must be filtered to the draws that have none. -/
def checkLiftIdentityWithoutFuncDecl (p : Program) : Bool :=
  if !(programFuncDecls p).isEmpty then true
  else match runLift p with
    | none => false
    | some (changed, out) => !changed && decide (out = p)

/-- **P5 — the arity and type shape.** For every hoisted function: the original
    inputs are a *suffix* of the emitted inputs (the captured parameters **lead**,
    which is what makes the call-site rewrite a purely local edit at the `.op`
    node), the output type is unchanged, and the original `typeArgs` are retained.

    Matched by name: the pass emits `{liftPrefix}_{original}_{n}`, so the original
    declaration is the one whose name the emitted name embeds. Only the injected
    functions are scored — their names are freshened, so the match is unambiguous,
    whereas a generated `funcDecl` name could be a substring of another. -/
def checkLiftParamsLead (p : Program) : Bool :=
  (scenarioFails p (fun _ q r =>
    match r with
    | none => true
    | some (_, out) =>
      let nm := mkNames p
      let injected := [nm.fn1, nm.fn2, nm.fn3]
      let decls := (programFuncDecls q).filter (fun d => injected.contains d.name.name)
      decls.all fun d =>
        match (liftedFuncs q out).find? (fun f =>
                f.name.name.startsWith s!"{liftPrefix}_{d.name.name}_") with
        | none => false
        | some f =>
          let origIns := d.inputs.map (fun iv => iv.1.name)
          let emitIns := f.inputs.map (fun iv => iv.1.name)
          emitIns.length ≥ origIns.length
            && (emitIns.drop (emitIns.length - origIns.length)) == origIns
            && decide (f.output = Lambda.LTy.toMonoTypeUnsafe d.output)
            && d.typeArgs.all f.typeArgs.contains)).isEmpty

/-- **P6 — the minted names are fresh.** Every `{liftPrefix}`-prefixed name in the
    output was introduced by the pass, and the minted names are pairwise distinct.
    A name the *input* already used under that prefix is therefore a collision.

    The sweep above cannot see this: `mkNames` freshens the injected names away
    from the prefix on purpose. So this property injects the collision deliberately.

    It seeds a *range* of prefixed names rather than just `{liftPrefix}_0`. The
    counter is shared across the whole program, so how many values are already
    consumed by the time the injected function is lifted depends on how many
    `funcDecl`s the draw itself carries — with a single seeded name the property
    was red on only 14 of 20 draws, which would make its green runs meaningless.
    Seeding `_0` … `_5` makes it deterministic on any draw.

    **This FAILS.** See the module doc: `StringGenState.gen` is a bare counter that
    never reads a program name, so the output declares a seeded name twice. -/
def checkLiftFreshSnapshotNames (p : Program) : Bool :=
  let nm := mkNames p
  let collide := (List.range 6).map (fun i => declInt s!"{liftPrefix}_{i}" 7)
  let q := injectStmts
    (collide ++ scenarioStmts ⟨"collide", .top, .body, .solo, false, false⟩ nm)
    (normalizeAmbient p)
  match runLift q with
  | none => true
  | some (_, out) =>
    -- Every declared name in the output, at any depth: a minted snapshot must not
    -- coincide with a name that was already there.
    let declared := (programBodies out).flatMap bodyDeclaredNames
    let snapshots := declared.filter (fun n => n.startsWith liftPrefix)
    nodup snapshots

/-- **P7 — the output typechecks.** The sharp property, and the authoritative
    oracle for scope correctness: Strata's own `Program.typeCheck` accepted the
    input, so it must accept the output of a pass that claims to be
    model-preserving.

    **This FAILS on all four escaping placements** (`.block`, `.ite`, `.elseArm`,
    `.loop`). The pass hoists the function out of the nested scope but leaves the
    snapshot `init` inside it, so a call site outside the construct names a
    variable that is not in scope. See the module doc for the diagnostic and the
    severity. -/
def checkLiftOutputTypechecks (p : Program) : Bool :=
  (scenarioFails p (fun _ q r =>
    !progTypeChecks q || match r with
      | none => true
      | some (_, out) => progTypeChecks out)).isEmpty

/-- **P7, structurally.** The same claim without the typechecker: every
    `{liftPrefix}` variable a procedure mentions is in scope at that point. This
    localises the failure to "a snapshot escaped its scope" rather than reporting a
    generic type error, and it holds independently of whether the draw typechecks.

    **This FAILS on the same four placements**, which is what confirms the two
    properties are seeing one defect and not two. -/
def checkLiftSnapshotsInScope (p : Program) : Bool :=
  (scenarioFails p (onOutput fun _ out =>
    (programProcs out).all (fun nq => procSnapshotsInScope nq.2))).isEmpty

/-- **P8 — the Johnsson fixpoint agrees with an independent implementation.**
    `extCapturedRef` computes Levy–Reeves Def 4.6 as a least fixpoint over the
    original variable names, sharing no code with the pass. For each injected
    function, the number of parameters the pass prepended must equal the size of
    the reference fixpoint's captured set for that function.

    This is the algorithmically interesting part of the pass — `.chain` needs one
    propagation step and `.star` needs a union of two different captured sets — and
    it is where the loop bound `for _ in [0 : lfs.length]` would show up if it were
    too small. -/
def checkLiftFixpointMatchesReference (p : Program) : Bool :=
  (scenarioFails p (fun _ q r =>
    match r with
    | none => true
    | some (_, out) =>
      let nm := mkNames p
      let injected := [nm.fn1, nm.fn2, nm.fn3]
      -- The reference fixpoint is per procedure, so it is computed over the body
      -- that actually holds the injected declarations.
      (programBodies q).all fun ss =>
        let decls := bodyFuncDecls ss
        let ref := extCapturedRef decls
        (decls.filter (fun d => injected.contains d.name.name)).all fun d =>
          match (liftedFuncs q out).find? (fun f =>
                  f.name.name.startsWith s!"{liftPrefix}_{d.name.name}_") with
          | none => false
          | some f =>
            let expected := (ref.find? (fun e => e.1 == d.name.name)).map (·.2) |>.getD []
            f.inputs.length == expected.length + d.inputs.length)).isEmpty

/-- **P10 — no free type variables.** Every type variable occurring in a hoisted
    function's inputs or output is declared in its `typeArgs`. `extraTypeArgs` is
    computed per function from the extended capture set, so an inherited capture
    has to bring its own type variables along. -/
def checkLiftTypeArgsClosed (p : Program) : Bool :=
  (scenarioFails p (onOutput fun q out =>
    (liftedFuncs q out).all fun f =>
      let tvs := (f.inputs.flatMap (fun iv => Lambda.LMonoTy.freeVars iv.2))
        ++ Lambda.LMonoTy.freeVars f.output
      tvs.all f.typeArgs.contains)).isEmpty

/-! ### Rejection completeness (P12)

`processDecl` rejects a procedure on four conditions. The property is the
biconditional: on a well-typed input the pass errors *only* if one of them holds.
It is stated as "no unintended rejection" because that is the direction that finds
bugs — the four triggers themselves are pinned by `#guard`s below.

`isRecursive` is unreachable from well-typed input: Core's `funcDecl` typing rule
requires a non-recursive declaration, so such a program fails `Program.typeCheck`
before the pass runs. -/

/-- Whether a procedure body holds two internal functions with the same name. -/
def hasDuplicateInternalNames (ss : List Statement) : Bool :=
  let ns := (bodyFuncDecls ss).map (fun d => d.name.name)
  !nodup ns

/-- Whether a procedure body holds a `funcDecl` *and* a local `typeDecl`. -/
def hasLocalTypeAndFunc (ss : List Statement) : Bool :=
  !(bodyFuncDecls ss).isEmpty && Imperative.Block.hasLocalTypeDecl ss

/-- Whether an internal function name clashes with a top-level function name. -/
def hasTopLevelClash (p : Program) (ss : List Statement) : Bool :=
  let top := funcNames p
  ((bodyFuncDecls ss).map (fun d => d.name.name)).any top.contains

/-- Whether a procedure body declares a recursive internal function. -/
def hasRecursiveInternal (ss : List Statement) : Bool :=
  (bodyFuncDecls ss).any (·.isRecursive)

/-- One of the four conditions `processDecl` rejects on holds somewhere in `p`. -/
def hasKnownRejectionTrigger (p : Program) : Bool :=
  (programBodies p).any fun ss =>
    hasDuplicateInternalNames ss || hasLocalTypeAndFunc ss
      || hasTopLevelClash p ss || hasRecursiveInternal ss

/-- **P12 — the pass rejects only what it documents.** On a well-typed input, a
    diagnostic implies one of the four conditions. This converts an open-ended
    "does it crash" into a biconditional, and it is the property that would find an
    *unintended* rejection. -/
def checkLiftRejectsOnlyKnownTriggers (p : Program) : Bool :=
  -- Deliberately un-normalized (see the normalization note): the raw draw's own
  -- triggers are exactly what this property is about, and `applyScenario` would
  -- strip them. The injection is still added, so a capturing declaration is
  -- present either way.
  allScenarios.all fun sc =>
    let q := injectStmts (scenarioStmts sc (mkNames p)) p
    !progTypeChecks q || match runLift q with
      | none => hasKnownRejectionTrigger q
      | some _ => true

/-! ## Diagnostics

A failing sweep says only *that* some shape broke. These name which one, for the
Tyche panels and for anyone reading a counterexample. -/

/-- The scenario labels on which the output fails to typecheck, with the
    typechecker's own message for the first one. -/
def liftTypecheckDiagnostic (p : Program) : String :=
  let bad := scenarioFails p (fun _ q r =>
    !progTypeChecks q || match r with
      | none => true
      | some (_, out) => progTypeChecks out)
  if bad.isEmpty then
    s!"-- lift: the output typechecks on all {allScenarios.length} injected shapes"
  else
    let firstErr := (allScenarios.find? (fun sc => bad.contains sc.label)).bind fun sc =>
      (runLift (applyScenario sc p)).bind fun r => progTypeCheckError r.2
    s!"-- lift: output rejected on {bad.length} of {allScenarios.length} shapes: \
       {String.intercalate ", " bad}"
      ++ (match firstErr with | some e => s!"\n   first: {e}" | none => "")

/-- The scenario labels on which a snapshot variable escapes its scope. -/
def liftScopeDiagnostic (p : Program) : String :=
  let bad := scenarioFails p (onOutput fun _ out =>
    (programProcs out).all (fun nq => procSnapshotsInScope nq.2))
  if bad.isEmpty then
    s!"-- lift: every snapshot is in scope on all {allScenarios.length} injected shapes"
  else
    s!"-- lift: snapshot out of scope on {bad.length} of {allScenarios.length} shapes: \
       {String.intercalate ", " bad}"

/-! ## Constructed witnesses

Three things the generated sweep cannot pin on its own:

1. that the `liftPrefix` mirror still matches what the pass actually mints — if it
   drifted, `liftedFuncs` would still work (it is a set difference) but every
   prefix-keyed property would quietly stop looking at anything;
2. the four rejection triggers of `processDecl`, in the *positive* direction —
   `checkLiftRejectsOnlyKnownTriggers` only says the pass rejects nothing else;
3. the defects, minimally, so they are pinned independently of any draw. -/

/-- The empty program. `injectStmts` appends a fallback procedure to it, so an
    injected scenario over this is a self-contained one-procedure program with no
    generated content — the minimal witness for each guard below. -/
private def emptyProg : Program := { decls := [] }

/-- `sc` injected into the empty program. -/
private def soleScenario (sc : Scenario) : Program := applyScenario sc emptyProg

private def topBody : Scenario := ⟨"top/body", .top, .body, .solo, false, false⟩
private def blockBody : Scenario := ⟨"block/body", .block, .body, .solo, false, false⟩
private def chainBody : Scenario := ⟨"top/body/chain", .top, .body, .chain, false, false⟩
private def starBody : Scenario := ⟨"top/body/star", .top, .body, .star, false, false⟩
private def binderChain : Scenario := ⟨"top/chain/binder", .top, .body, .chain, false, true⟩

-- The injection really is well typed on its own, so a failing property below is
-- about the pass and not about a malformed witness.
#guard progTypeChecks (soleScenario topBody)
#guard progTypeChecks (soleScenario blockBody)
#guard progTypeChecks (soleScenario chainBody)
#guard progTypeChecks (soleScenario starBody)
#guard progTypeChecks (soleScenario binderChain)

-- The pass really fires on the injection (`changed = true` and a function is
-- hoisted), so none of the properties above is vacuously green.
#guard (runLift (soleScenario topBody)).any (·.1)
#guard match runLift (soleScenario topBody) with
       | some (_, out) => (liftedFuncs (soleScenario topBody) out).length == 1
       | none => false

-- The `liftPrefix` mirror agrees with what the pass mints. If this fails, fix
-- `liftPrefix` — every prefix-keyed property depends on it.
#guard match runLift (soleScenario topBody) with
       | some (_, out) =>
         (liftedFuncs (soleScenario topBody) out).all
           (fun f => f.name.name.startsWith liftPrefix)
       | none => false

-- The captured parameter **leads**: the emitted arity is one more than the
-- original, and the original formal is last.
#guard match runLift (soleScenario topBody) with
       | some (_, out) =>
         match (liftedFuncs (soleScenario topBody) out).head? with
         | some f => f.inputs.length == 2
         | none => false
       | none => false

-- A chain reuses the callee's snapshot rather than minting a second one, so the
-- caller also takes exactly one captured parameter (Def 4.6 clause (2)).
#guard match runLift (soleScenario chainBody) with
       | some (_, out) => (liftedFuncs (soleScenario chainBody) out).all
           (fun f => f.inputs.length == 2)
       | none => false

-- A star unions two *different* captured variables into the caller, so the caller
-- takes two captured parameters while each callee takes one.
#guard match runLift (soleScenario starBody) with
       | some (_, out) =>
         ((liftedFuncs (soleScenario starBody) out).map (fun f => f.inputs.length)).foldl
           (· + ·) 0 == 2 + 2 + 3
       | none => false

/-! ### The two defects, minimally -/

-- **HONEST FAILURE — the snapshot escapes its declaring scope.** A `funcDecl`
-- inside a labelled block, called after the block: the input typechecks, the
-- output does not.
#guard progTypeChecks (soleScenario blockBody)
#guard match runLift (soleScenario blockBody) with
       | some (_, out) => !progTypeChecks out
       | none => false
#guard !checkLiftOutputTypechecks emptyProg
#guard !checkLiftSnapshotsInScope emptyProg

-- The same shape with the call *inside* the block is fine, which isolates the
-- escape from the declaring scope as the cause rather than the block itself.
#guard match runLift (soleScenario ⟨"blockIn", .blockIn, .body, .solo, false, false⟩) with
       | some (_, out) => progTypeChecks out
       | none => false

-- **HONEST FAILURE — a minted snapshot name collides with a program name.**
#guard !checkLiftFreshSnapshotNames emptyProg

/-! ### The four rejection triggers, in the positive direction

`checkLiftRejectsOnlyKnownTriggers` says the pass rejects *nothing else*; these say
each documented trigger really does reject. Built directly rather than through
`Scenario`, since a rejection is not a shape any property sweeps. -/

/-- A capturing declaration named `f`, for the rejection witnesses. -/
private def rejDecl (f : String) : Imperative.PureFunc Expression :=
  { name := ⟨f, ()⟩,
    inputs := [(⟨"x", ()⟩, (.forAll [] .int : LTy))],
    output := (.forAll [] .int : LTy),
    body := some (addI (fvInt "x") (fvInt "c")) }

private def rejProg (ss : List Statement) (extra : List Decl := []) : Program :=
  { decls := extra ++ [.proc (fallbackProc "P" (declInt "c" 10 :: ss)) .empty] }

-- (a) two internal functions with the same name
#guard (runLift (rejProg [Stmt.funcDecl (rejDecl "d") .empty,
                          Stmt.funcDecl (rejDecl "d") .empty])).isNone
-- (b) a local `typeDecl` alongside a `funcDecl`
#guard (runLift (rejProg [Statement.typeDecl { name := "T", params := [], bound := .Infinite } .empty,
                          Stmt.funcDecl (rejDecl "t") .empty])).isNone
-- (c) an internal name clashing with a top-level `Decl.func`
#guard (runLift (rejProg [Stmt.funcDecl (rejDecl "clash") .empty]
                  [.func { name := ⟨"clash", ()⟩, inputs := [(⟨"x", ()⟩, .int)],
                           output := .int, body := some (fvInt "x") } .empty])).isNone
-- (d) a recursive internal function
#guard (runLift (rejProg [Stmt.funcDecl { rejDecl "r" with isRecursive := true } .empty])).isNone

-- Trigger (d) is **unreachable from well-typed input**: Core's `funcDecl` typing
-- rule requires a non-recursive declaration, so a program carrying one is rejected
-- by `Program.typeCheck` before the pass ever runs. The other three are reachable.
#guard !progTypeChecks (rejProg [Stmt.funcDecl { rejDecl "r" with isRecursive := true } .empty])
#guard progTypeChecks (rejProg [Stmt.funcDecl (rejDecl "d") .empty,
                                Stmt.funcDecl (rejDecl "d") .empty])

/-! ### Capture through each of the four fields

The plan's §6.2 calls a body-only generator "the most likely coverage gap". It is
not one: each field is rewritten to the snapshot parameter and survives into the
emitted function. Pinned per field, since the printed program shows neither
`axioms` nor `measure` and a regression there would otherwise be invisible. -/

private def viaScenario (via : CaptureVia) : Program :=
  soleScenario ⟨"via", .top, via, .solo, false, false⟩

/-- The captured variable is gone from every field, and the field that carried it
    is still populated — so the capture was *rewritten*, not dropped. -/
private def capturedRewritten (via : CaptureVia) : Bool :=
  match runLift (viaScenario via) with
  | none => false
  | some (_, out) =>
    match (liftedFuncs (viaScenario via) out).head? with
    | none => false
    | some f =>
      (openVars f).isEmpty && f.inputs.length == 2 &&
        (match via with
         | .body => f.body.isSome
         | .axioms => !f.axioms.isEmpty
         | .preconditions => !f.preconditions.isEmpty
         | .measure => f.measure.isSome)

#guard capturedRewritten .body
#guard capturedRewritten .axioms
#guard capturedRewritten .preconditions
#guard capturedRewritten .measure

end StrataGenerators.Program.LiftFuncDecls
