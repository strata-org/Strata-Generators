-- The whole-program generator gives the program. `UnprovenTransforms` gives the shared definitions that
-- each other family of transform properties uses, which are `runPhase` over a seeded transform state,
-- `progTypeChecks`, `nodup` and `programFuncs`. Nothing here writes any of them again. This file imports
-- the pass itself directly, and it does not reach the pass through `Verifier`. Therefore a rename of the
-- pass breaks the build, and it does not make each property skip in silence.
import StrataGenerators.ProgramGen.UnprovenTransforms
import Strata.Transform.LiftInternalFuncDecls

open Lambda Core Imperative
open StrataGenerators.Program.TestSupport
open StrataGenerators.Procedure.TestSupport
open StrataGenerators.Program.UnprovenTransforms

/-!
# The properties for `LiftInternalFuncDecls`, which lifts a lambda and captures at the declaration

This module holds the check predicates for `Strata/Transform/LiftInternalFuncDecls.lean`. That pass lifts
each internal `Stmt.funcDecl` out of a procedure body, into a closed top-level `Decl.func`.

This module is a companion of `ProgramGen/UnprovenTransforms`, and it has the same shape. Each predicate
takes a whole generated `Core.Program` and gives a `Bool`, both harnesses score the same predicate, and the
whole-program shrinker minimizes a counterexample.

## What the pass does, and the one part that no textbook covers

The pass performs **lambda lifting**, and not a conversion to a closure. Each free variable of the internal
function becomes an extra parameter at the front, the pass lifts the function to the top level, and it gives
the extra arguments at each call site. There is no datatype for a closure, and the representation of a
function does not change.

The one part with no oracle in a textbook is the **snapshot variable**. Strata is imperative, and its
evaluator gives a `funcDecl` the semantics of a capture at the time of the declaration, through
`Core.captureFreevars`. Therefore the pass cannot pass a captured variable at the call site, because a call
site would read a later value. The pass instead emits `var $__liftfncl_i := c` *in place of* the `funcDecl`
statement, which freezes the value of `c` there, and it passes that snapshot at each call site. Plain
lifting would give an observably wrong result whenever a program assigns to `c` between the declaration and
the call.

That design is what each finding below depends on: the pass lifts the *function* to the top level, and the
*snapshot* stays at the original point of the program.

## What Strata proves, and what it does not prove

`Strata/Transform/LiftInternalFuncDeclsCorrect.lean` proves that no procedure body holds a `funcDecl` after
the pass. Therefore `checkLiftNoResidualFuncDecl` below is a guard on a theorem with a proof, and not a
probe. Each other claim of the pass has no proof. Those claims are closedness, which is the property that
the pass *exists* for and which licenses a remark in `FactoryWF.lean`, the shape of the arity and of the
type, the freshness of a name, the correctness of the scope of a snapshot, the fixed point of the
computation of the captured variables, and the conditions for a rejection.

## Why the input is a generated program together with an injection

`genFuncDeclStmt` draws the body of a `funcDecl` with `genFunction []`, at an **empty** context of free
variables. Therefore each generated internal function is *closed*. The pass would then capture nothing, and
each property below would hold with no content, so a sweep over unchanged draws would establish nothing.

Each predicate therefore **injects** a `funcDecl` that captures a variable into the generated program, and
it scores the pass on the result. `Scenario` names each shape that is worth an injection, and
`allScenarios` lists them. Each predicate sweeps the whole list, so one draw reaches each shape. The
generated program gives what a witness that a person writes cannot: arbitrary statements around the
injection for the traversal to walk, and arbitrary declarations for the logic about a name and about the
factory to meet.

`mkNames` makes each name of the injection fresh against the host procedure, so an injected program never
collides with a generated identifier by accident. The one property that is *about* a collision, which is
`checkLiftFreshSnapshotNames`, builds its collision on purpose.

## The guard for the typechecker

Each property here starts with `!progTypeChecks p`, so it skips a draw that the whole-program typechecker
rejects, and it scores nothing there. The pass is a phase of `transformPipelinePhases`, and it runs on a
program that Core accepted only. Therefore a claim about its behaviour on an ill-typed input is a claim
about a state that the pipeline never reaches, and a counterexample from such an input would give a reader
nothing to act on.

The guard is a screen, so it can cost coverage only. How much it costs is a property of the generator, and
not of anything here. `checkLiftInjectionFires` carries the same guard, and it keeps that cost visible. The
`#guard`s at the end of the file are free of the guard either way, because each of them uses the empty
program, which type checks.

Two properties apply a second guard, for each scenario and not for each draw.
`checkLiftOutputTypechecks` and `checkLiftRejectsOnlyKnownTriggers` ask `!progTypeChecks q` of the
*injected* program, because the claim of each of them holds only when the shape that it scores is well
typed, and not only when the host draw is well typed.

## The two defects that these properties pin

* `checkLiftSnapshotsInScope` finds that **the pass leaves the init of the snapshot inside a nested scope
  while it lifts the function out of that scope.** When a `funcDecl` sits inside a `block`, an `ite` or a
  `loop`, and a call to it sits outside that construct, the pass emits `var $__liftfncl_0 : int := c`
  *inside* the construct, and it rewrites the outer call site to a call that names `$__liftfncl_0`. That
  snapshot is out of scope there, so `Program.typeCheck` rejects the output with a message about a free
  variable.

  The six shapes that escape the declaring scope reach that defect, and the nine shapes that stay in the
  declaring scope do not reach it. That split isolates the escape as the cause.

  The typechecker of Core scopes a block-local `funcDecl` to its block, exactly as it scopes a block-local
  variable. Therefore each of the six shapes that escape is not well-typed input, and the guard of a
  property decides whether that property can see the defect. `checkLiftOutputTypechecks` and
  `liftTypecheckDiagnostic` skip a scenario whose injection is ill typed, and `checkLiftSnapshotsInScope`
  does not skip it. Read the property about the scope for a placement that escapes, and read a clean result
  from `liftTypecheckDiagnostic` as no evidence about the escape. The `#guard`s under "The two defects, at
  their smallest" pin that split.

  `liftInternalFuncDeclsPipelinePhase` is the **first** phase of `transformPipelinePhases`, and the
  `typeCheck` phase of the pipeline runs after each of them. Therefore this defect reaches a user as a type
  error on a program that is well typed as written.

* `checkLiftFreshSnapshotNames` finds that **the pass does not check a name that it builds against the
  identifiers of the program.** A procedure that already declares `$__liftfncl_0` gets a *second*
  declaration of that name, and the typechecker rejects the output with a message about a variable that is
  already in the context. `CoreGenState.gen` calls `StringGenState.gen`, which is a plain counter. It gives
  a name that differs from each name that *it* built, and never a name that differs from a name of the
  program.

  The module docstring of the pass records that assumption, so this is a documented gap. Two facts are
  still worth a report. The comment on `hoistProcedure` says that the generator cannot collide with a name
  of the user, and `StringGenState.gen` gives less than that. This is also the same class of defect as the
  one that `checkCseFreshNamesFresh` pins, where `CommonSubexprElim` builds the name `$__cse.0` and reads no
  name of the program. Two passes need one mechanism.

## Three parts of the pass that these properties confirm

* **A capture through the `axioms`, the `preconditions` or the `measure` field.** The pass handles each of
  the four fields that can hold an expression. It rewrites each of them to name the parameter for the
  snapshot, and each of them survives into the emitted function. `CaptureVia` covers each of the four.
* **A substitution under a binder.** A call to a sibling function inside a `forall` is rewritten correctly.
  The replacement is an operator applied to *free* variables for the snapshots, so the side condition about
  a bound variable holds.
* **The fixed point of the computation of the captured variables.**
  `checkLiftFixpointMatchesReference` scores the pass against an independent implementation of the least
  fixed point, which is `extCapturedRef`, and the two agree, on a chain shape and on a star shape too.

## One condition for a rejection that well-typed input cannot reach

`processDecl` rejects a declaration under four conditions, and a recursive declaration is not reachable.
The typing rule of Core for a `funcDecl` needs a declaration that is not recursive, so a program that holds
one fails `Program.typeCheck` before the pass sees it. Therefore only a `#guard` scores the scenario for a
recursive declaration, and `checkLiftRejectsOnlyKnownTriggers` treats that scenario as a skip.

## Why the ambient program needs normalization

`run` folds `processDecl` over the declarations with `foldlM`, so a rejection in *any* procedure stops the
whole program. A generated draw can carry its own trigger for a rejection, such as the name of an internal
function that clashes with a top-level name, or a local `typeDecl` beside it. Such a draw takes the injected
scenario with it, and each property then scores nothing. `normalizeAmbient` removes that cause, and
`checkLiftInjectionFires` reports the symptom, so the same masking cannot return without notice.

## What this module does not cover

The semantic tier needs the symbolic evaluator, and it also needs a decision about how to compare a
`List Env`. That tier holds three claims: operational correctness in both directions, the preservation of
the outcome of a verification, and a comparison between the snapshot and the call site that would pin the
semantics of a capture at the time of the declaration.
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

/-- The functions of `out` that `inp` does not hold, by name. Those are the functions that the pass lifted.
    The definition takes a difference of two sets, and it matches no prefix. Therefore it stays correct after
    a change to the prefix. -/
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

/-! ## Closedness, which is the property that the pass exists for

Two notions, because Strata's own one is weaker than what the pass computes.

`Lambda.LFuncClosed` constrains only `body` and `preconditions`
(`FuncClosed`, `Func.lean`). But `capturedVars` unions the free variables of
`body`, `axioms`, `preconditions` **and** `measure`, and `rewritePureFunc`
rewrites all four. So a function with an open `axioms` field would satisfy
`LFuncClosed` and still name a variable that the output does not declare. This module checks both notions:
the notion of Strata, which is the predicate that the pass must establish, and the stronger notion over
each of the four fields, so that the gap in `LFuncClosed` cannot hide a defect. -/

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

/-! ## An independent least fixed point for the captured variables

The algorithmically interesting part of the pass is Phase 2 of `hoistProcedure`:

    extCaptured(f) = own(f) ∪ ⋃ { extCaptured(g) | g a sibling called by f }

That equation is a least fixed point over the graph of the calls between the sibling functions. It is the
definition of Levy and Reeves, at the flat structure of the scopes of Strata. A `funcDecl` carries a
`PureFunc` whose body is an expression, so one internal function cannot hold another one. Therefore each
internal function of a procedure is a sibling of each other one, and the guard of that definition for the
declaring function can never apply.

`extCapturedRef` computes it independently, over *original* variable names rather
than the pass's minted snapshot names, so the two implementations share no code.
Iterating `decls.length + 1` times is enough: each round either adds a name to
some set or the fixpoint is reached, and a chain of `n` siblings propagates a name
`n` steps. -/

/-- The free variables of `d` that are not formal parameters of `d`. Those are the variables of the first
    clause of the definition, which names a non-local variable that the function references. The definition
    reads the same four fields as the pass. -/
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

/-- One round of the propagation of the second clause of the definition. -/
def extStep (decls : List (Imperative.PureFunc Expression)) (siblings : List String)
    (cur : List (String × List String)) : List (String × List String) :=
  decls.map fun d =>
    let nm := d.name.name
    let mine := (cur.find? (fun e => e.1 == nm)).map (·.2) |>.getD []
    let inherited := (calledSiblingsRef siblings d).flatMap fun g =>
      (cur.find? (fun e => e.1 == g)).map (·.2) |>.getD []
    (nm, (mine ++ inherited).dedup)

/-- The least fixed point of the definition, for the internal functions of one procedure, as a pair of a
    function name and the names of the captured variables. This definition shares no code with the pass. -/
def extCapturedRef (decls : List (Imperative.PureFunc Expression)) :
    List (String × List String) :=
  let siblings := decls.map (fun d => d.name.name)
  let init := decls.map (fun d => (d.name.name, ownCaptures d))
  -- `decls.length + 1` rounds suffice; see the section note.
  (List.range (decls.length + 1)).foldl (fun acc _ => extStep decls siblings acc) init

/-! ## The scope: is a snapshot visible where the output uses it?

This section states the claim directly, and it uses no typechecker. It walks the body of the output with the
set of the variables in scope, and it checks that a declaration in an enclosing scope or in the current
scope already gives each `$__liftfncl` free variable that a statement names. The body of a `block`, an arm
of an `ite` and the body of a `loop` each extend the scope for their own statements only, and that is
exactly the scoping that the defect breaks.

`checkLiftOutputTypechecks` is the sharper oracle in principle, because it is the checker of Strata itself.
It carries a guard on the type check of the input, and each shape that escapes the declaring scope is not
well-typed input. Therefore this predicate is the one that reports the escape, and it names the cause, which
is a snapshot out of scope, instead of a general type error. -/

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

`genFuncDeclStmt` cannot give a `funcDecl` that captures a variable, as the module docstring says. Therefore
each property injects one. A `Scenario` holds the dimensions that are worth a change, and `allScenarios` is
the list of the combinations that each property sweeps.

The four dimensions are:

* `Placement` says where the `funcDecl` sits, against its call sites. Four shapes escape the declaring
  scope: a declaration in a branch with a use after the `if`, a use in the other arm, a declaration in the
  body of a loop, and a declaration in a labelled `block`. The values `.top` and `.blockIn` are the
  controls, where the call is inside the declaring scope.
* `CaptureVia` says which of the four fields that `capturedVars` reads holds the captured variable. A
  generator that uses the body only is the most likely gap in the coverage.
* `CallShape` is the graph of the calls between the siblings, over which the fixed point runs. The value
  `.chain` gives a function that captures a variable and a caller that captures none, which is the case
  where the fixed point must propagate the variable. The value `.star` gives one caller and two callees that
  capture *different* variables, so the union of the two sets has real content.
* `underBinder` puts the call to the sibling inside a `forall`, so the substitution of the operators must go
  under a binder. -/

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
  /-- A caller that captures nothing, of a callee that captures a variable. The fixed point must propagate
      that variable. -/
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

/-- The shapes that each property sweeps. The controls come first, so a diagnostic that lists the failures
    shows the shapes inside the declaring scope before the shapes that escape it. -/
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
    level of the body, so that they are in scope at each placement. The scope of the captured variable
    itself is never the subject of a property. -/
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
    the injection, and each property that reads it, always has content. -/
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
*any* procedure stops the whole program. A draw whose own internal functions meet one of the four
conditions for a rejection therefore takes the injected scenario with it. The pass gives a diagnostic, and
each property below then scores nothing and says nothing about that.

`stripInternalDecls` removes the draw's own `funcDecl` and local `typeDecl`
statements before injecting, which is what the three reachable triggers need
(duplicate internal names, a clash with a top-level function, a local type
declaration beside a function declaration). Nothing of interest is lost:
`genFuncDeclStmt` draws its bodies with `genFunction []`, so every generated
internal function is *closed* and captures nothing. Those declarations are exactly the
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
shapes that failed. Both the properties and the diagnostics read that kernel, so a panel can never show a
verdict other than the one that the property scored. -/

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
    gave a diagnostic. That is the correct behaviour, because `checkLiftRejectsOnlyKnownTriggers` scores a
    rejection, and a property about closedness does not. It also means that a draw that the pass refuses
    makes each of those properties score nothing, in silence. This property scores the coverage itself, so
    that failure becomes visible. -/
def checkLiftInjectionFires (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (fun _ q r =>
    match r with
    | none => false
    | some (changed, out) => changed && !(liftedFuncs q out).isEmpty)).isEmpty

/-- **Closedness, which is the property that the pass exists for.** Each function that the pass lifts is
    closed: it holds no free variable outside its own inputs, in any of the four fields that can hold an
    expression. That property is what licenses the remark about `LFuncClosed` in `FactoryWF.lean`, so it gets
    the widest sweep over the scenarios.

    The predicate uses `openVars`, which reads each of the four fields, and it does not use `strataClosed`.
    `Lambda.LFuncClosed` constrains the body and the preconditions only. Read the note of the section about
    closedness. `checkLiftStrataClosed` covers the weaker predicate of Strata separately. -/
def checkLiftAllFuncsClosed (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (onOutput fun q out =>
    (liftedFuncs q out).all (fun f => (openVars f).isEmpty))).isEmpty

/-- **Closedness, in the form of Strata.** Each function of the output satisfies `Lambda.LFuncClosed`,
    whether the pass lifted it or the input already held it. That predicate is weaker than the one of
    `checkLiftAllFuncsClosed`, because it reads no `axioms` field and no `measure` field. It is the predicate
    that each other part of Strata uses. -/
def checkLiftStrataClosed (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (onOutput fun _ out => (programFuncs out).all strataClosed)).isEmpty

/-- **No `funcDecl` stays in a body.** Strata proves this claim, so this predicate is a guard against a
    change and not a probe. It stays because each property about a call site depends on it. `Stmt.mapExpr`
    does not go into a `funcDecl`, so a `funcDecl` that stays would keep each of its inner call sites without
    a rewrite, and nothing would report that. -/
def checkLiftNoResidualFuncDecl (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (onOutput fun _ out => !anyResidualFuncDecl out)).isEmpty

/-- **Idempotence.** A second run changes nothing, and it gives the same program. This claim follows from
    the claim that no `funcDecl` stays, so a counterexample means that the traversal missed a position of the
    nesting. -/
def checkLiftIdempotent (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (onOutput fun _ out =>
    match runLift out with
    | none => false
    | some (changed, out2) => !changed && decide (out2 = out))).isEmpty

/-- **The pass is the identity on a program that holds no `funcDecl`.** The pass leaves the draw with no
    injection unchanged: the flag `changed` is `false`, and the output is syntactically the input.
    `liftInternalFuncDecls` derives `changed` from a comparison of two lengths, so this property also pins
    that comparison at the one input where it is unambiguous.

    This is the *only* property that scores the raw draw, and not an injection. Each `funcDecl` of a
    generated program is closed, and the pass still lifts it. Therefore the predicate keeps only a draw that
    holds none. -/
def checkLiftIdentityWithoutFuncDecl (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  if !(programFuncDecls p).isEmpty then true
  else match runLift p with
    | none => false
    | some (changed, out) => !changed && decide (out = p)

/-- **The shape of the arity and of the type.** For each function that the pass lifts, three claims hold. The
    original inputs are a *suffix* of the inputs of the emitted function, so each parameter for a captured
    variable comes **first**, and the rewrite at a call site is therefore a local change at the `.op` node.
    The output type does not change. The emitted function keeps the original type arguments.

    The predicate matches by name, because the pass emits a name that holds the original name inside it. It
    scores the injected functions only. Their names are fresh, so the match is unambiguous, and the name of a
    generated `funcDecl` could be a part of another name. -/
def checkLiftParamsLead (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
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

/-- **Each name that the pass builds is fresh.** The pass introduced each name of the output that starts with
    the prefix, and those names are different in pairs. A name that the *input* already uses under that
    prefix is therefore a collision.

    The sweep above cannot find such a collision, because `mkNames` moves each injected name away from that
    prefix on purpose. This property therefore builds the collision itself.

    It puts a *range* of names with that prefix into the program, and not one name. The counter is shared
    across the whole program, so the number of the values that the pass has already used when it lifts the
    injected function depends on the number of the `funcDecl` statements of the draw. One name would
    therefore make the result depend on the draw, and a range does not.

    `StringGenState.gen` is a plain counter, and it reads no name of the program. Read the module
    docstring. -/
def checkLiftFreshSnapshotNames (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  let nm := mkNames p
  let collide := (List.range 6).map (fun i => declInt s!"{liftPrefix}_{i}" 7)
  let q := injectStmts
    (collide ++ scenarioStmts ⟨"collide", .top, .body, .solo, false, false⟩ nm)
    (normalizeAmbient p)
  match runLift q with
  | none => true
  | some (_, out) =>
    -- Each declared name of the output, at any depth. A snapshot that the pass builds must differ from each
    -- name that the input already declares.
    let declared := (programBodies out).flatMap bodyDeclaredNames
    let snapshots := declared.filter (fun n => n.startsWith liftPrefix)
    nodup snapshots

/-- **The output type checks.** `Program.typeCheck` of Strata accepted the input, so it must accept the
    output of a pass that claims to preserve the model.

    The property carries a guard for each scenario as well as for each draw. The condition `!progTypeChecks q`
    skips an *injected* shape that is not well typed itself, and that guard is what makes the claim statable
    at all, because an ill-typed input puts no obligation on the output. The typechecker of Core scopes a
    block-local `funcDecl` to its block, so a call after the declaring block is not well typed. Therefore
    that guard, and not the typechecker, decides each shape that escapes the declaring scope.

    `checkLiftSnapshotsInScope` states the same claim structurally, and it does not depend on the type check
    of the scenario. Therefore it is the property to read for a shape that escapes. Read the module
    docstring. -/
def checkLiftOutputTypechecks (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (fun _ q r =>
    !progTypeChecks q || match r with
      | none => true
      | some (_, out) => progTypeChecks out)).isEmpty

/-- **The same claim about the scope, without the typechecker.** Each variable with the prefix that a
    procedure names is in scope at that point. This predicate names the cause, which is a snapshot that
    escaped its scope, and it does not report a general type error. It also holds whether or not the draw
    type checks.

    The predicate carries a guard on the draw only, and no guard for each scenario. It reads nothing about
    the type check of the *injected* shape, unlike `checkLiftOutputTypechecks`. Therefore it still speaks
    about a shape that the block scoping of Core makes ill typed, and it is the sharper of the two properties
    at a placement that escapes. -/
def checkLiftSnapshotsInScope (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (onOutput fun _ out =>
    (programProcs out).all (fun nq => procSnapshotsInScope nq.2))).isEmpty

/-- **The fixed point of the pass agrees with an independent implementation.** `extCapturedRef` computes the
    definition of Levy and Reeves as a least fixed point over the original names of the variables, and it
    shares no code with the pass. For each injected function, the number of the parameters that the pass put
    at the front must equal the size of the captured set that the reference gives for that function.

    This is the part of the pass with real content in its algorithm. The shape `.chain` needs one step of the
    propagation, and the shape `.star` needs a union of two different captured sets. A bound on the loop of
    the pass that is too small would also show up here. -/
def checkLiftFixpointMatchesReference (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (fun _ q r =>
    match r with
    | none => true
    | some (_, out) =>
      let nm := mkNames p
      let injected := [nm.fn1, nm.fn2, nm.fn3]
      -- The reference fixed point is for one procedure, so the code computes it over the body that holds the
      -- injected declarations.
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

/-- **No free type variable.** The `typeArgs` field of a lifted function declares each type variable that
    occurs in its inputs or in its output. The pass computes `extraTypeArgs` for each function, from the
    extended set of the captured variables, so a variable that a function inherits must bring its own type
    variables. -/
def checkLiftTypeArgsClosed (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  (scenarioFails p (onOutput fun q out =>
    (liftedFuncs q out).all fun f =>
      let tvs := (f.inputs.flatMap (fun iv => Lambda.LMonoTy.freeVars iv.2))
        ++ Lambda.LMonoTy.freeVars f.output
      tvs.all f.typeArgs.contains)).isEmpty

/-! ### The conditions for a rejection

`processDecl` rejects a procedure under four conditions. The property below is the direction that finds a
defect: on a well-typed input, the pass gives an error *only* when one of the four conditions holds. The
`#guard`s below pin the other direction, which is that each of the four conditions does cause a rejection.

A recursive declaration is not reachable from well-typed input. The typing rule of Core for a `funcDecl`
needs a declaration that is not recursive, so such a program fails `Program.typeCheck` before the pass
runs. -/

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

/-- **The pass rejects only the input that its docstring names.** On a well-typed input, a diagnostic means
    that one of the four conditions holds. This property is the one that would find a rejection that the pass
    does not intend. -/
def checkLiftRejectsOnlyKnownTriggers (p : Program) : Bool :=
  -- Every property here is about what the pass does to a *legal* program.
  !progTypeChecks p ||
  -- This property uses the raw draw, with no normalization. Read the note about normalization. The
  -- conditions of the draw itself are what this property is about, and `applyScenario` would remove them.
  -- The code still adds the injection, so a declaration that captures a variable is present.
  allScenarios.all fun sc =>
    let q := injectStmts (scenarioStmts sc (mkNames p)) p
    !progTypeChecks q || match runLift q with
      | none => hasKnownRejectionTrigger q
      | some _ => true

/-! ## The diagnostics

A sweep that fails says only *that* one shape failed. Each diagnostic below names the shape, for the Tyche
panels and for a reader of a counterexample. -/

/-- The scenario labels on which the output fails to typecheck, with the
    typechecker's own message for the first one.

    This diagnostic follows `checkLiftOutputTypechecks`, and it carries the same `!progTypeChecks q` guard.
    Therefore a shape whose *injection* is ill typed is absent from this list. `liftScopeDiagnostic` carries
    no such guard. -/
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

/-! ## The witnesses that a person wrote

A generated sweep cannot pin three things on its own:

1. That the copy of the prefix here still matches the prefix that the pass builds. After a change to the
   prefix, `liftedFuncs` would still work, because it takes a difference of two sets, and each property that
   reads the prefix would silently look at nothing.
2. The four conditions of `processDecl` in the *positive* direction.
   `checkLiftRejectsOnlyKnownTriggers` says only that the pass rejects nothing else.
3. The two defects, at their smallest, so that a guard pins each of them and no draw is necessary. -/

/-- The empty program. `injectStmts` appends a fallback procedure to it, so an injected scenario over this
    program is a program of one procedure with no generated content. That is the smallest witness for each
    guard below. -/
private def emptyProg : Program := { decls := [] }

/-- `sc` injected into the empty program. -/
private def soleScenario (sc : Scenario) : Program := applyScenario sc emptyProg

private def topBody : Scenario := ⟨"top/body", .top, .body, .solo, false, false⟩
private def blockBody : Scenario := ⟨"block/body", .block, .body, .solo, false, false⟩
private def chainBody : Scenario := ⟨"top/body/chain", .top, .body, .chain, false, false⟩
private def starBody : Scenario := ⟨"top/body/star", .top, .body, .star, false, false⟩
private def binderChain : Scenario := ⟨"top/chain/binder", .top, .body, .chain, false, true⟩

-- Each injection is well typed by itself, so a property that fails below reports the pass and not a
-- malformed witness. The placement in a labelled block is the exception, and the section about the defects
-- below pins it. The typechecker of Core scopes a block-local `funcDecl` to its block, so a call after the
-- block is not legal *input*.
#guard progTypeChecks (soleScenario topBody)
#guard progTypeChecks (soleScenario chainBody)
#guard progTypeChecks (soleScenario starBody)
#guard progTypeChecks (soleScenario binderChain)

-- The pass acts on the injection: the flag `changed` is `true`, and the pass lifts a function. Therefore
-- each property above has content.
#guard (runLift (soleScenario topBody)).any (·.1)
#guard match runLift (soleScenario topBody) with
       | some (_, out) => (liftedFuncs (soleScenario topBody) out).length == 1
       | none => false

-- The copy of the prefix here agrees with the prefix that the pass builds. After a failure of this guard,
-- correct the copy, because each property that reads the prefix depends on it.
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

-- A chain uses the snapshot of the callee again, and the pass builds no second snapshot. Therefore the
-- caller also takes exactly one parameter for a captured variable, by the second clause of the definition.
#guard match runLift (soleScenario chainBody) with
       | some (_, out) => (liftedFuncs (soleScenario chainBody) out).all
           (fun f => f.inputs.length == 2)
       | none => false

-- A star gives the caller the union of two *different* captured variables. Therefore the caller takes two
-- parameters for a captured variable, and each callee takes one.
#guard match runLift (soleScenario starBody) with
       | some (_, out) =>
         ((liftedFuncs (soleScenario starBody) out).map (fun f => f.inputs.length)).foldl
           (· + ·) 0 == 2 + 2 + 3
       | none => false

/-! ### The two defects, at their smallest -/

-- **The snapshot escapes its declaring scope.** The witness holds a `funcDecl` inside a labelled block,
-- with a call after the block. The pass lifts the function out of the block, and it leaves the `init` of the
-- snapshot inside. Therefore the rewritten call site names a variable that is not in scope there.
--
-- The typechecker of Core scopes a block-local `funcDecl` to its block, exactly as it scopes a block-local
-- variable. The input shape is therefore not well typed, and `checkLiftOutputTypechecks` skips it on its
-- `!progTypeChecks q` guard.
#guard !progTypeChecks (soleScenario blockBody)
#guard checkLiftOutputTypechecks emptyProg

-- The pass gives the same output for that shape: a program that the typechecker rejects, with the snapshot
-- out of scope. The structural property carries no guard about a type check, so it finds that output.
#guard match runLift (soleScenario blockBody) with
       | some (_, out) => !progTypeChecks out
       | none => false
#guard !checkLiftSnapshotsInScope emptyProg

-- The same shape with the call *inside* the block gives a correct output. That contrast isolates the escape
-- from the declaring scope as the cause, and not the block itself.
#guard match runLift (soleScenario ⟨"blockIn", .blockIn, .body, .solo, false, false⟩) with
       | some (_, out) => progTypeChecks out
       | none => false

-- **A name that the pass builds for a snapshot collides with a name of the program.**
#guard !checkLiftFreshSnapshotNames emptyProg

/-! ### The four conditions for a rejection, in the positive direction

`checkLiftRejectsOnlyKnownTriggers` says that the pass rejects *nothing else*. Each guard below says that one
condition of the docstring does cause a rejection. Each witness is built directly, and not through a
`Scenario`, because a rejection is not a shape that a property sweeps. -/

/-- A declaration named `f` that captures a variable, for each witness of a rejection. -/
private def rejDecl (f : String) : Imperative.PureFunc Expression :=
  { name := ⟨f, ()⟩,
    inputs := [(⟨"x", ()⟩, (.forAll [] .int : LTy))],
    output := (.forAll [] .int : LTy),
    body := some (addI (fvInt "x") (fvInt "c")) }

private def rejProg (ss : List Statement) (extra : List Decl := []) : Program :=
  { decls := extra ++ [.proc (fallbackProc "P" (declInt "c" 10 :: ss)) .empty] }

-- The first condition: two internal functions with the same name.
#guard (runLift (rejProg [Stmt.funcDecl (rejDecl "d") .empty,
                          Stmt.funcDecl (rejDecl "d") .empty])).isNone
-- The second condition: a local `typeDecl` beside a `funcDecl`.
#guard (runLift (rejProg [Statement.typeDecl { name := "T", params := [], bound := .Infinite } .empty,
                          Stmt.funcDecl (rejDecl "t") .empty])).isNone
-- The third condition: an internal name that clashes with a top-level `Decl.func`.
#guard (runLift (rejProg [Stmt.funcDecl (rejDecl "clash") .empty]
                  [.func { name := ⟨"clash", ()⟩, inputs := [(⟨"x", ()⟩, .int)],
                           output := .int, body := some (fvInt "x") } .empty])).isNone
-- The fourth condition: a recursive internal function.
#guard (runLift (rejProg [Stmt.funcDecl { rejDecl "r" with isRecursive := true } .empty])).isNone

-- The fourth condition is **not reachable from well-typed input**. The typing rule of Core for a `funcDecl`
-- needs a declaration that is not recursive, so `Program.typeCheck` rejects a program that holds one before
-- the pass runs. The other three conditions are reachable.
#guard !progTypeChecks (rejProg [Stmt.funcDecl { rejDecl "r" with isRecursive := true } .empty])
#guard progTypeChecks (rejProg [Stmt.funcDecl (rejDecl "d") .empty,
                                Stmt.funcDecl (rejDecl "d") .empty])

/-! ### A capture through each of the four fields

The pass rewrites each of the four fields to name the parameter for the snapshot, and each field survives
into the emitted function. There is one guard for each field, because the printed program shows neither the
`axioms` field nor the `measure` field, and a change to either of them would otherwise be invisible. -/

private def viaScenario (via : CaptureVia) : Program :=
  soleScenario ⟨"via", .top, via, .solo, false, false⟩

/-- The captured variable is absent from each field, and the field that held it still holds a value.
    Therefore the pass *rewrote* the capture, and it did not drop the field. -/
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
