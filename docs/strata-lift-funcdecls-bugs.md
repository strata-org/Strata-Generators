# Bug report for Strata: two defects in `LiftInternalFuncDecls`

**Target repo:** `strata-org/Strata` (observed at the pinned revision
`a7b525555bac5b912c52f0ca3853106d864a1342`, `lake-manifest.json`). None of the
affected code is fork-only.

**How they were found:** property-based testing of
`Strata/Transform/LiftInternalFuncDecls.lean` (strata-generators issue #33, plan in
`LIFT_INTERNAL_FUNCDECLS_PBT_PLAN.md`). Every property runs against a whole
well-typed `Core.Program` drawn by `ProgramGen.genProgram` — proven sound against
`ProgramHasTypeA` — with a *capturing* internal function injected into it. The
injection is necessary: `genFuncDeclStmt` draws its `funcDecl` bodies with
`genFunction []`, an empty free-variable context, so every generated internal
function is closed and the pass would have nothing to capture.

The properties live in `StrataGenerators/ProgramGen/LiftFuncDecls.lean`. Each defect
is pinned there by a `#guard`, so a fix turns the guard red and the finding cannot
silently rot.

---

## Summary

| # | Defect | Severity |
|---|---|---|
| 1 | A `funcDecl` nested in a `block`/`ite`/`loop` and called outside it has its snapshot `init` left behind in the nested scope, so the pass turns a well-typed program into an ill-typed one | **high** |
| 2 | Minted `$__liftfncl` names are never checked against the program's own identifiers, so a program already using that prefix gets a duplicate declaration | low (documented assumption) |

Plus one documentation inaccuracy, §3.

### Which property found which

| # | Property | Predicate | Found on |
|---|---|---|---|
| 1 | `lift: the output typechecks` | `checkLiftOutputTypechecks` | every draw (0/20), 6 of 15 injected shapes |
| 1 | `lift: every snapshot is used in scope` | `checkLiftSnapshotsInScope` | every draw (0/20), the same 6 shapes |
| 2 | `lift: the minted snapshot names are fresh` | `checkLiftFreshSnapshotNames` | every draw (0/20) |

Ten further properties — closedness (both Strata's `LFuncClosed` and the stronger
all-four-fields notion), no residual `funcDecl`, idempotence, identity on
`funcDecl`-free input, leading captured parameters, no free type variables, the
Johnsson fixpoint against an independent Def 4.6 implementation, and rejection
completeness — hold on 20/20 draws. §4 records what that rules out.

Defect 1 was found by the *cheapest* property shape in the set — "if the input
typechecks, so must the output" — the same shape that found the highest-severity
defect in the previous transform-pass sweep
(`docs/strata-unproven-transform-bugs.md`, defect 3).

---

## Shared setup for the reproducers

Both reproducers import **only Strata** — nothing from this repository.

```lean
import Strata.Languages.Core.Verifier
import Strata.Transform.LiftInternalFuncDecls

open Lambda Core Imperative

def intBinOpTy : LMonoTy := .tcons "arrow" [.int, .tcons "arrow" [.int, .int]]
def intFnTy : LMonoTy := .tcons "arrow" [.int, .int]

def intLit (i : Int) : Expression.Expr := .const () (.intConst i)
def fvInt (n : String) : Expression.Expr := .fvar () ⟨n, ()⟩ (some .int)
def addI (a b : Expression.Expr) : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Add", ()⟩ (some intBinOpTy)) a) b

/-- `addC (x : int) : int := x + c` — captures the enclosing local `c`. -/
def addC : Imperative.PureFunc Expression :=
  { name := ⟨"addC", ()⟩,
    inputs := [(⟨"x", ()⟩, (.forAll [] .int : LTy))],
    output := (.forAll [] .int : LTy),
    body := some (addI (fvInt "x") (fvInt "c")) }

def proc (name : String) (ss : List Statement) : Procedure :=
  { header := { name := ⟨name, ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured ss }

def prog (ss : List Statement) : Program := { decls := [.proc (proc "P" ss) .empty] }

def declC : Statement := Statement.init ⟨"c", ()⟩ (.forAll [] .int) (.det (intLit 10)) .empty

/-- `var r : int := addC(0)` -/
def callAddC (r : String) : Statement :=
  Statement.init ⟨r, ()⟩ (.forAll [] .int)
    (.det (.app () (.op () ⟨"addC", ()⟩ (some intFnTy)) (intLit 0))) .empty

/-- The typechecking context Strata's own verifier uses. -/
def checkContext : LContext CoreLParams :=
  { LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }

def typeChecks (p : Program) : Bool :=
  (Program.typeCheck checkContext TEnv.default p).isOk

def typeCheckError (p : Program) : String :=
  match Program.typeCheck checkContext TEnv.default p with
  | .ok _ => "(accepted)"
  | .error e => (toString e.message).replace "\n" " "

def runLift (p : Program) : Option Program :=
  match Transform.runWith p Core.liftInternalFuncDeclsPipelinePhase.transform
    { Transform.CoreTransformState.emp with
      factory := Core.Factory,
      cachedAnalyses := { callGraph := some p.toProcedureCG } } with
  | (.ok (_, out), _) => some out
  | (.error _, _) => none
```

---

## Defect 1 — the snapshot `init` is left behind in a nested scope

**Severity: high.** The pass turns a program `Program.typeCheck` **accepts** into one
it **rejects**.

### What happens

The pass performs lambda lifting with declaration-site value capture. For an
internal function `f` capturing `c`, it does two separate things:

1. hoists `f` to a **top-level** `Decl.func`, with `c` renamed to a fresh snapshot
   parameter, and
2. replaces the `funcDecl` **statement, in place**, with `var $__liftfncl_i := c`,
   freezing `c` at that program point.

Step 2's "in place" is deliberate and correct — it is what models the evaluator's
`captureFreevars` declaration-time capture semantics, and it is why the pass cannot
simply pass `c` at the call site. But when the `funcDecl` sits inside a `block`,
an `ite` arm, or a `loop` body, "in place" means *inside that construct*. Every call
site is then rewritten to pass the snapshot — including call sites **outside** the
construct, where the snapshot is not in scope.

Core's own typechecker puts a `funcDecl`'s name in scope for the whole enclosing
procedure. That is why the input below is well typed: a call after the block is legal
input, not a malformed program.

### Reproducer

```lean
/-- `addC` declared inside a labelled block, called after it. -/
def defect1 : Program :=
  prog [ declC,
         .block "B" [Stmt.funcDecl addC .empty] .empty,
         callAddC "r" ]

/-- The control: the same block, with the call *inside* it. -/
def control1 : Program :=
  prog [ declC,
         .block "B" [Stmt.funcDecl addC .empty, callAddC "r"] .empty ]

#guard typeChecks defect1                                  -- input accepted
#guard (runLift defect1).all (fun out => !typeChecks out)   -- output rejected
#guard (runLift control1).all typeChecks                    -- the control is fine
```

### Observed output

Input accepted; output rejected with

```
[init (r : int) := ((~$__liftfncl_addC_1 : (arrow int (arrow int int)))  ($__liftfncl_0 : int)  #0)]
No free variables are allowed here! Free Variables: [$__liftfncl_0]
```

and the emitted program shows the split plainly — the function is at the top level,
the snapshot is inside `B`, and the call after `B` names it anyway:

```
program Core;

function $__liftfncl_addC_1 ($__liftfncl_0 : int, x : int) : int {
  int.add(x, $__liftfncl_0)
}
procedure P ()
{
  var c : int := 10;
  B: {
    var $__liftfncl_0 : int := c;
  }
  var r : int := $__liftfncl_addC_1($__liftfncl_0, 0);
};
```

The control — same block, call inside it — produces a well-typed program, which
isolates the escape from the declaring scope as the cause rather than the block
itself.

### Which nesting shapes fail

All four, and only the shapes where a call escapes the declaring scope:

| Shape | `Placement` | Output typechecks |
|---|---|---|
| declaration and call both at the top level | `.top` | yes |
| both inside one block | `.blockIn` | yes |
| declared in a block, called after it | `.block` | **no** |
| declared in a then-branch, called after the `ite` | `.ite` | **no** |
| declared in a then-branch, called in the `else` arm | `.elseArm` | **no** |
| declared in a loop body, called after the loop | `.loop` | **no** |

The `.elseArm` case is worth singling out: the snapshot is initialised only on a path
that is never taken when the call executes, so even a scoping fix has a semantic
question to answer there — what value should the call see when the declaring branch
did not run?

### Severity

`liftInternalFuncDeclsPipelinePhase` is the **first** phase of
`transformPipelinePhases`, and the pipeline's own `typeCheck` phase runs after all
the transform phases (`Verifier.lean:1502–1536`):

```
filterProcedures → LiftInternalFuncDecls → callElim → termCheck → precondElim
  → … → typeCheck → symbolicEval → …
```

So a user who writes a `funcDecl` in a branch or a loop and calls it outside gets
`❌ Type checking error` from the verifier, on a program that was well typed as
written, with a diagnostic naming a variable they never wrote.

The pass is also declared `modelPreservingPipelinePhase`, which claims the program's
meaning is unchanged. An output that does not typecheck has no meaning to preserve.

### Note on the correctness file

`Strata/Transform/LiftInternalFuncDeclsCorrect.lean` proves `run_noFuncDecl` — after
the pass no procedure body holds a `funcDecl` — and that theorem is unaffected: this
defect is about *where the snapshot lands*, not about whether the `funcDecl` is
removed. The property `lift: no procedure body holds a funcDecl` passes on 20/20
draws, as the theorem says it must.

---

## Defect 2 — minted names are not checked against the program's identifiers

**Severity: low**, because the pass documents the assumption. Reported for two
reasons: one comment overstates what the name generator guarantees (§3), and this is
the *same defect class* as an already-filed one in `CommonSubexprElim`.

### What happens

`genLiftVar` and `genLiftFuncName` mint names through `CoreGenState.gen`
(`Strata/Languages/Core/CoreGen.lean:45`), which delegates to `StringGenState.gen`
(`Strata/DL/Util/StringGen.lean:46`):

```lean
def StringGenState.gen (pf : String) (σ : StringGenState) : String × StringGenState :=
  let (counter, cs) := Counter.genCounter σ.cs
  let newString : String := (pf ++ "_" ++ toString counter)
  ...
```

It is a bare counter. Its well-formedness condition (`StringGenState.WF`) says the
names it produced are pairwise distinct — it says nothing about the program, which it
never reads. So a program that already declares `$__liftfncl_0` gets a second
declaration of it.

### Reproducer

```lean
def defect2 : Program :=
  prog [ Statement.init ⟨"$__liftfncl_0", ()⟩ (.forAll [] .int) (.det (intLit 7)) .empty,
         declC,
         Stmt.funcDecl addC .empty,
         callAddC "r" ]

#guard typeChecks defect2
#guard (runLift defect2).all (fun out => !typeChecks out)
```

Output rejected with `Variable $__liftfncl_0 of type int already in context.`, on this
program:

```
procedure P ()
{
  var $__liftfncl_0 : int := 7;
  var c : int := 10;
  var $__liftfncl_0 : int := c;
  var r : int := $__liftfncl_addC_1($__liftfncl_0, 0);
};
```

### Why it is still worth filing

The module doc is explicit and honest:

> As other passes in Strata like InsertLoopInvariantAsserts do, it is assumed that
> the input Core program doesn't have any identifier starting with this prefix. This
> isn't being enforced by Core verifier yet, so in theory the user can write a
> program that has these prefixes, and a way of enforcing absence of these is
> necessary in the future.

So this is a known gap, not a surprise. But `CommonSubexprElim` has the identical gap
— it mints `$__cse.0` from a counter that never reads a program name, filed as
`cse: the fresh names are fresh` in `docs/strata-unproven-transform-bugs.md`. Two
passes with one missing mechanism suggests the fix belongs in the shared generator
(seed the counter from the program's identifiers, or have the verifier reject the
reserved prefixes on input) rather than in each pass.

---

## 3. Documentation inaccuracies

Neither affects behaviour.

**`hoistProcedure` overstates the generator's guarantee.** Phase 1's comment reads:

> mint a fresh `$__liftfncl`-prefixed top-level name per function
> (collision-proof against user names) through the shared generator.

`StringGenState.gen` provides no such property (§2). Collision-freedom rests entirely
on the module-level *assumption* about the input, which the module doc states
correctly. Suggest deleting the parenthesis or pointing it at the assumption.

**Three docstrings still say "closure conversion"** for what the file's own section
heading correctly calls "lambda lifting with declaration-site value capture":

- `rewritePureFunc`: "Apply the closure-conversion substitutions"
- `Strata/DL/Lambda/LExprWF.lean`, `substOps`: "the closure-conversion use in
  `LiftInternalFuncDecls`"

The pass builds no closure datatype, no environment tuple, and no `apply`; function
references stay direct `.op` applications and `funcDecl` is not first-class. Worth
fixing so nobody later reads this as introducing closures.

---

## 4. What the passing properties rule out

Recorded because negative results are the point of a property suite, and three of
these were predicted to be weak spots by the test plan.

* **Capture through `axioms`, `preconditions` and `measure` is handled correctly.**
  The plan's §6.2 called a body-only generator "the most likely coverage gap". It is
  not one: `capturedVars` unions all four fields, `rewritePureFunc` rewrites all
  four, and each is present and correctly renamed in the emitted function. Pinned per
  field, since the program printer displays neither `axioms` nor `measure` and a
  regression would otherwise be invisible.

* **`substOps` under a binder is correct** (plan P11). Its docstring notes it does not
  lift de Bruijn indices, so it is sound only for bvar-free replacements. A sibling
  call inside `forall z :: g(z) == x` is rewritten correctly — the replacement is an
  operator applied to *free* snapshot variables, so the side condition holds.

* **The Johnsson fixpoint agrees with an independent implementation** (plan P8).
  `extCapturedRef` computes Levy–Reeves Def 4.6 as a least fixpoint over original
  variable names, sharing no code with the pass. They agree on a two-function chain
  (the callee's snapshot is reused, not re-minted) and on a star where one caller
  unions two *different* captured variables from two callees. The loop bound
  `for _ in [0 : lfs.length]`, asserted sufficient in a comment, was sufficient on
  every shape tried.

* **The captured parameters lead**, the output type is unchanged, the original
  `typeArgs` are retained, and no emitted function has a free type variable
  (plan P5, P10).

* **Rejection completeness** (plan P12). `processDecl` rejects four conditions; on
  well-typed input the pass rejected nothing else on 20/20 draws. One of the four —
  `isRecursive` — is **unreachable from well-typed input**, since Core's `funcDecl`
  typing rule requires a non-recursive declaration, so a program carrying one is
  rejected by `Program.typeCheck` before the pass runs. Worth knowing before anyone
  invests in that error path.

### Not covered

The plan's semantic tier: P13 (bidirectional operational correctness through
`Core.eval`), P14 (verification-outcome preservation), and P16 (the
snapshot-vs-call-site differential, which would pin the declaration-time capture
semantics that motivate the whole snapshot design). These need the symbolic evaluator
and a decision about comparing `List Env`. The structural layer had to be trusted
first, and it turned out not to be trustworthy — it found defect 1.

A last observation about defect 1 and P16: the two interact. P16 would compare the
pass against *call-site* lifting and require them to disagree when the captured
variable is reassigned. For the `.elseArm` shape neither answer is obviously right,
so a fix for defect 1 should settle the semantics before P16 is written.
