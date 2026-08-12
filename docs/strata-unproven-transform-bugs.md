# Bug report for Strata: four defects in the unproven Core transform passes

**Target repo:** `strata-org/Strata` (observed at the pinned revision
`865885871f87269e075ce20ac16e502bc688d763`, `lakefile.toml`). None of the affected
code is fork-only.

**Tracked separately:** defect 4, the unsound one, is repo issue #107, which carries a
self-contained runnable reproducer (imports only Strata, needs nothing from this
repository).

**How they were found:** property-based testing of the eight passes in
`Strata/Transform/` that carry no machine-checked correctness argument
(strata-generators issue #69). Every property runs against a whole well-typed
`Core.Program` drawn by `ProgramGen.genProgram`, which is proven sound against
`ProgramHasTypeA`. The properties and the reproducers below live in
`StrataGenerators/ProgramGen/UnprovenTransforms.lean`; each defect is pinned there
by a `#guard`, so a fix turns the guard red and the finding cannot silently rot.

---

## Summary

| # | Pass | Defect | Severity |
|---|---|---|---|
| 1 | `LoopElim` | Mints the same block label twice for one loop | low |
| 2 | `ProcedureInlining` | Two call sites of one procedure get identical labels (two causes) | medium |
| 3 | `ProcedureInlining` | `old x` is copied verbatim while `x` is renamed, producing an ill-typed program | **high** |
| 4 | `ProcedureInlining` | **Drops the callee's `requires` obligation — unsound** | **critical** |

### Which property found which defect

Each defect below carries a "The property that found it" section giving the predicate
verbatim and what about its formulation mattered. In summary:

| # | Property | Predicate | Found by |
|---|---|---|---|
| 1 | `loop: LoopElim mints distinct block labels` | `checkLoopBlockLabelsNodup` | generated draw (4/40) |
| 2 | `procInline: inlining introduces no duplicate label` | `checkInlineProcLabelsNodup` | generated draw (2/400) |
| 3 | `procInline: the output typechecks` | `checkInlineProcTypechecks` | generated draw (1/400) |
| 4 | `procInline: symbolic evaluation loses no obligation` | `checkInlineProcSymbolicAgreement` | generated draw (1/400) |

Every defect here was found on a randomly generated draw, not on a hand-built input.
Worth noting that defect 3 came from the *cheapest* property shape in the set — "if
the input typechecks, so must the output" — and the four sharper structural properties
beside it all missed it.

Defect 3 turns a program the typechecker **accepts** into one it **rejects**: the pass
breaks its input rather than merely producing something untidy.

**Defect 4 is worse than all of them and is rated separately.** It does not break the
program — it makes a program that *must fail* verification silently pass, by dropping
a proof obligation. And `procedureInliningPipelinePhase` is declared
`modelPreservingPipelinePhase`, so the pass asserts precisely the property it
violates.

Shared setup for every reproducer below:

```lean
import StrataGenerators.ProgramGen.UnprovenTransforms

open Lambda Core Imperative
open Strata Strata.CoreDDM                    -- `Core.formatProgram` lives here
open StrataGenerators.Procedure.TestSupport   -- runPhase, runPhaseSt, mkState
open StrataGenerators.Program.TestSupport     -- progTypeChecks, progTypeCheckError

def proc (name : String) (ss : List Statement) : Procedure :=
  { header := { name := ⟨name, ()⟩, typeArgs := [], inputs := [], outputs := [],
                noFilter := false }
    spec := { preconditions := [], postconditions := [] }
    body := .structured ss }

def prog (ss : List Statement) : Program := { decls := [.proc (proc "P" ss) .empty] }

def intLit (i : Int) : Expression.Expr := .const () (.intConst i)
def trueLit : Expression.Expr := .const () (.boolConst true)
```

`runPhase` runs a `PipelinePhase` from a state seeded the way `Core.Verifier` seeds
it (`factory := some Core.Factory`, `callGraph := some prog.toProcedureCG`).

---

## 1. `LoopElim` mints the same block label twice for one loop

**Site:** `Strata/Transform/LoopElim.lean:126` and `:139`.

`removeLoop` builds **one** block statement labelled
`loopElim_havoc_{loop_num}`:

```lean
let havocd : Statement :=
  .block s!"{loopElimBlockPrefix}havoc_{loop_num}"
    (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}
```

and then places that same statement into the output **twice** (`:139`): once inside
the `arbitrary_iter_facts` block to pick the mid-loop state, and once after it to
pick the exit state.

```lean
let arbitrary_iter_facts :=
  .block s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
    ([havocd] ++ assume_guard ++ bss) {}
let loop_passive :=
  .ite guard (arbitrary_iter_facts :: ([havocd] ++ exit_guard)) [] {}
```

So the output holds two blocks under one label, per erased loop.

### Reproduction

```lean
#eval do
  let body := [.loop .nondet none [] [Statement.assert "a" trueLit .empty] .empty]
  match runPhase Core.loopElimPipelinePhase (prog body) with
  | some (_, out) => IO.println (toString (Core.formatProgram out))
  | none => IO.println "threw"
```

**Source** (typechecks):

```
program Core;

procedure P ()
{
  while *
  {
    assert [a]: true;
  }
};
```

**After `LoopElim`** (typechecks) — note `loopElim_havoc_loop_0` appearing twice:

```
program Core;

procedure P ()
{
  if * {
    loopElim_arbitrary_iter_facts_loop_0: {
      loopElim_havoc_loop_0: {
        
      }
      assert [a]: true;
    }
    loopElim_havoc_loop_0: {
      
    }
  }
};
```

### The same defect on a generated program

The property found this independently. Shrunk witness, with the source drawn by
`genProgram` rather than written by hand:

```
program Core;

procedure e6<qwW, A$, |h'J|> (inout Zf$ : string, M : Map regex string)
{
  while (bv{8}(1) smod bv{8}(0) sgt bv{8}(255))
  decreases Bv16.ToInt(bv{16}(32767) div bv{16}(32766))
  {
    
  }
};
```

After `InsertLoopInvariantAsserts` then `LoopElim` (the production order):

```
program Core;

procedure e6<qwW, A$, |h'J|> (inout Zf$ : string, M : Map regex string)
{
  if (bv{8}(1) smod bv{8}(0) sgt bv{8}(255)) {
    loopElim_arbitrary_iter_facts_loop_0: {
      loopElim_havoc_loop_0: {
        
      }
      assume [loopElimAssume_guard_loop_0]: bv{8}(1) smod bv{8}(0) sgt bv{8}(255);
      var $__loop_measure_loop_0 : int;
      assume [insertLoopInvAssume_measure_loop_0]:
        $__loop_measure_loop_0 == Bv16.ToInt(bv{16}(32767) div bv{16}(32766));
      assert [insertLoopInvAssert_measure_lb_loop_0]: !($__loop_measure_loop_0 < 0);
      assert [insertLoopInvAssert_measure_decrease_loop_0]:
        Bv16.ToInt(bv{16}(32767) div bv{16}(32766)) < $__loop_measure_loop_0;
    }
    loopElim_havoc_loop_0: {
      
    }
    assume [loopElimAssume_not_guard_loop_0]: !(bv{8}(1) smod bv{8}(0) sgt bv{8}(255));
  }
  assume [insertLoopInvAssume_exit_not_guard_loop_0]:
    !(bv{8}(1) smod bv{8}(0) sgt bv{8}(255));
};
```

Minted block labels of the result:
`[loopElim_arbitrary_iter_facts_loop_0, loopElim_havoc_loop_0, loopElim_havoc_loop_0]`.

### Why this is a defect and not a design choice

The pass carries a collision **detector** for exactly these labels:

```lean
def hasLabelConflict (loop_num : String) (bss : List (Stmt P C)) : Bool :=
  let bodyLabels := Block.labels bss
  (loopElimGeneratedBlockLabels loop_num).any bodyLabels.contains
```

and throws `"Generated loop block label conflicts with exit target in loop body"`
when it fires. So the pass's own standard is that these labels do not collide. The
detector only compares the minted labels against the labels of the *body*, so it
cannot see the collision the pass makes itself.

**Impact:** an `exit` to that label resolves to the first block, and the label is
also the handle a diagnostic uses to name a block. Two distinct program points
become indistinguishable.

**Suggested fix:** draw a second `loop_num`-suffixed label for the exit havoc (for
example `loopElim_exit_havoc_{n}`), and extend `loopElimGeneratedBlockLabels` to
list it so the detector covers it too.

### The property that found it

`loop: LoopElim mints distinct block labels`
(`checkLoopBlockLabelsNodup`). It runs `InsertLoopInvariantAsserts` and then
`LoopElim` — the production order, and necessary because `LoopElim` *throws* on a
loop that still carries invariants — then collects every `.block` label of every
output body at any depth, keeps the ones with the pass's own
`loopElim_` prefix, and asserts that list has no duplicate:

```lean
def checkLoopBlockLabelsNodup (p : Program) : Bool :=
  hasNondetMeasureLoop p ||
    (match runPhase loopInvPhase p with
     | some (_, mid) =>
       (match runPhase Core.loopElimPipelinePhase mid with
        | some (_, out) =>
          (programBodies out).all fun ss =>
            nodup ((stmtsBlockLabels ss).filter (·.startsWith Core.loopElimBlockPrefix))
        | none => true)
     | none => true)
```

Filtering to the pass's own prefix is what makes the claim attributable: a
duplicate among *source* labels would be a generator artefact — `genFreshLabel` draws
fresh against *enclosing* labels only, which is all the typing spec's `block` premise
requires, so a generated body may hold `j: { } j: { }` — whereas a duplicate among
`loopElim_`-prefixed labels can only have been minted by this pass. The `hasNondetMeasureLoop` guard skips the input shape on
which the first pass legitimately throws.

Fails on **4 of 40** generated draws, which is the rate at which a generated
program holds a loop at all.

---

## 2. `ProcedureInlining` gives two call sites identical labels

Two independent causes, both in `Strata/Transform/ProcedureInlining.lean`.

### Cause A: the wrapper block label reaches no counter (`:288`)

```lean
return .some [.block (procName ++ "$inlined") stmts md]
```

A plain string concatenation. Two calls to `Callee` both produce a block labelled
`Callee$inlined` in one caller body.

### Cause B: the label renaming sits inside the fold over `var_map` (`:110`)

```lean
pure <| .structured (List.map (fun (s0:Statement) =>
  var_map.foldl (fun (s:Statement) (old_id,new_id) =>
      let s := Statement.substFvar s old_id (.fvar () new_id .none)
      let s := Statement.renameLhs s old_id new_id
      Statement.replaceLabelsOfBlocksAndAssertAssumes s label_map)   -- ← inside
    s0) bodyStmts)
```

`label_map` is built correctly just above, but it is only *applied* inside the fold
body. When the callee declares no local variable and has no parameters, `var_map` is
empty, the fold body never runs, and the callee's labels are copied verbatim at
every call site.

### Reproduction

```lean
def twoCalls (callee : Procedure) : Program :=
  { decls := [ .proc callee .empty,
               .proc (proc "Caller" [ .cmd (.call "Callee" [] .empty),
                                      .cmd (.call "Callee" [] .empty) ]) .empty ] }

-- Cause A: callee HAS a local, so `var_map` is non-empty and labels do freshen
#eval match runPhase (Core.procedureInliningPipelinePhase {})
        (twoCalls (proc "Callee"
          [ Statement.init ⟨"v", ()⟩ (.forAll [] .int) (.det (intLit 1)) .empty,
            Statement.assert "inner" trueLit .empty ])) with
      | some (_, out) => IO.println (toString (Core.formatProgram out))
      | none => IO.println "threw"

-- Cause B: callee has NO local, so `var_map` is empty and nothing freshens
#eval match runPhase (Core.procedureInliningPipelinePhase {})
        (twoCalls (proc "Callee" [Statement.assert "inner" trueLit .empty])) with
      | some (_, out) => IO.println (toString (Core.formatProgram out))
      | none => IO.println "threw"
```

**Cause A — source** (typechecks; the callee declares a local, so `var_map` is
non-empty):

```
program Core;

procedure Callee ()
{
  var v : int := 1;
  assert [inner]: true;
};
procedure Caller ()
{
  call Callee();
  call Callee();
};
```

**Cause A — after `ProcedureInlining`** (still typechecks). The callee's own labels
freshen correctly to `Callee_inner_1` and `Callee_inner_3`, but both wrapper labels
are `Callee$inlined`:

```
program Core;

procedure Callee ()
{
  var v : int := 1;
  assert [inner]: true;
};
procedure Caller ()
{
  Callee$inlined: {
    var Callee_v_0 : int := 1;
    assert [Callee_inner_1]: true;
  }
  Callee$inlined: {
    var Callee_v_2 : int := 1;
    assert [Callee_inner_3]: true;
  }
};
```

**Cause B — source** (typechecks; the callee declares nothing, so `var_map` is
empty):

```
program Core;

procedure Callee ()
{
  assert [inner]: true;
};
procedure Caller ()
{
  call Callee();
  call Callee();
};
```

**Cause B — after `ProcedureInlining`** (still typechecks). Nothing freshens at all:
`inner` now appears twice as well as the two `Callee$inlined` wrappers:

```
program Core;

procedure Callee ()
{
  assert [inner]: true;
};
procedure Caller ()
{
  Callee$inlined: {
    assert [inner]: true;
  }
  Callee$inlined: {
    assert [inner]: true;
  }
};
```

That cause A freshens the callee's labels correctly shows the renaming logic itself
works, and that the fold nesting is the defect. Note that both outputs *typecheck* —
the checker does not require labels to be distinct — so the defect is invisible to
every oracle except a direct check on the labels.

**Impact:** a duplicate label makes two proof obligations share a name, and a
verifier reports obligations by name, so the two become indistinguishable in the
report. Cause B is the worse of the two, since it leaves the *callee's own* labels
unfreshened rather than only the synthesized wrapper.

**Suggested fix:** for cause A, draw the wrapper label from the same
`genIdent` counter the variable renaming uses. For cause B, lift
`replaceLabelsOfBlocksAndAssertAssumes s label_map` out of the `var_map.foldl` so it
runs once per statement unconditionally.

### The property that found it

`procInline: inlining introduces no duplicate label` (`checkInlineProcLabelsNodup`).
It runs the inlining phase and asserts the label list of each output body has no
duplicate, **conditional on the input's already being duplicate-free**:

```lean
def programLabelsNodup (p : Program) : Bool :=
  (programBodies p).all fun ss => nodup (allLabels ss)

def checkInlineProcLabelsNodup (p : Program) : Bool :=
  !programLabelsNodup p ||
    (match runPhase inlinePhase p with
     | some (_, out) => programLabelsNodup out
     | none => true)
```

Two design points carried the finding:

- **The label collector is the pass's own.** `allLabels` delegates to
  `ProcedureInlining.Statement.labelsOfBlocksAndAssertAssumes`, the very function the
  pass calls to build its rename map. So the property quantifies over exactly the
  labels the pass claims to freshen — block, `assert`, `assume` and `cover` — rather
  than over a hand-rolled list that could omit a kind the pass handles.
- **The input guard is load-bearing.** Without it the property fails on ~4% of draws
  for a reason that is not the pass's fault: the command generator draws `assert` /
  `assume` / `cover` labels from `String.arbitrary`, which yields `""` often enough
  that two statements already share a label before any pass runs. That would have
  reported a generator artefact as a Strata defect.

Note that **both** buggy outputs typecheck: `Program.typeCheck` does not require
labels to be distinct. So no type-based oracle can see this defect, and neither can
the `changed`-flag or statistics families — a direct check on the labels is the only
thing that catches it. That is the case for this property existing.

Fails on **2 of 400** generated draws, the rate at which a generated program holds
two or more calls. Both causes are additionally pinned by `#guard`, on a callee with
a local (cause A) and one without (cause B).

---

## 3. `ProcedureInlining` copies `old x` verbatim while renaming `x`

**Site:** `Strata/Transform/ProcedureInlining.lean:110` (the `substFvar` fold).

Inside a procedure body, `old x` is a **free variable whose name is literally
`"old x"`**, which the typechecker admits because the enclosing procedure declares
`x` as an `inout` parameter. The pass substitutes with `Statement.substFvar` over
`var_map`, whose keys are the plain parameter names, so `"old x"` is not a key and
no rule maps it: `x` is renamed and `old x` is not.

### Reproduction

```lean
def oldExprProgram : Program :=
  { decls :=
      [ .proc { header := { name := ⟨"Callee", ()⟩, typeArgs := [],
                            inputs := [(⟨"T", ()⟩, .bool)],
                            outputs := [(⟨"T", ()⟩, .bool)], noFilter := false }
                spec := { preconditions := [], postconditions := [] }
                body := .structured
                  [Statement.assert "inner" (.fvar () ⟨"old T", ()⟩ (some .bool)) .empty]
              } .empty,
        .proc (proc "Caller"
          [ Statement.init ⟨"T", ()⟩ (.forAll [] .bool) (.det trueLit) .empty,
            .cmd (.call "Callee" [.inoutArg ⟨"T", ()⟩] .empty) ]) .empty ] }

#eval do
  IO.println s!"input typechecks  = {progTypeChecks oldExprProgram}"
  match runPhase (Core.procedureInliningPipelinePhase {}) oldExprProgram with
  | some (_, out) =>
    IO.println (toString (Core.formatProgram out))
    IO.println s!"output typechecks = {progTypeChecks out}"
    IO.println s!"error = {progTypeCheckError out}"
  | none => IO.println "threw"
```

**Source** (typechecks):

```
program Core;

procedure Callee (inout T : bool)
{
  assert [inner]: old T;
};
procedure Caller ()
{
  var T : bool := true;
  call Callee(inout T);
};
```

**After `ProcedureInlining`** (does **not** typecheck) — `T` is renamed to
`Callee_T_1`, but the `old T` inside the assert is copied verbatim:

```
program Core;

procedure Callee (inout T : bool)
{
  assert [inner]: old T;
};
procedure Caller ()
{
  var T : bool := true;
  Callee$inlined: {
    var Callee_T_1 : bool := T;
    assert [Callee_inner_2]: old T;
    T := Callee_T_1;
  }
};
```

```
[source typechecks: true]
[output typechecks: false]
[checker error: [assert [Callee_inner_2] (old T : bool)]
                No free variables are allowed here! Free Variables: [old T]]
```

**Impact:** high. The pass takes a program the typechecker accepts and produces one
it rejects, so the pipeline breaks on any callee that mentions `old` — which is
routine in a postcondition-bearing procedure. The failure is loud (the checker
rejects it) rather than silent, which is the one mercy here.

**Suggested fix:** bind the pre-state value at the call site, which is what `old`
means, and add `("old " ++ x, "old " ++ x')` to the substitution for each renamed
inout parameter `x`. Treating `old` as an opaque name prefix is what the current
representation invites; a structured `old` node would remove the class of bug
entirely.

### The property that found it

`procInline: the output typechecks` (`checkInlineProcTypechecks`) — the plainest
oracle in the whole set:

```lean
def checkInlineProcTypechecks (p : Program) : Bool :=
  !progTypeChecks p ||
    (match runPhase inlinePhase p with
     | some (_, out) => progTypeChecks out
     | none => true)
```

"If the input typechecks, so must the output." The implication is what makes it
usable at all: `Program.typeCheck` rejects ~60% of generated programs for three
documented reasons unrelated to any pass, so an unconditional claim would fail
constantly and say nothing. Guarded this way it is vacuous on a rejected draw and a
real claim on the rest.

The finding is a good argument for keeping a **cheap, broad** property alongside the
sharp structural ones. Nothing about this property mentions `old`, or renaming, or
parameters — and it still caught a substitution bug the other four `ProcedureInlining`
properties all missed, because a lost `old` is neither a label problem nor a
statistics problem nor a call-graph problem. Strata's own typechecker did the work;
the property just had to ask it the right question.

The counterexample was reported by the whole-program shrinker as an unminimized draw
(a two-procedure program with an `assert [||]: old T` in the callee). Reducing it by
hand to the two-line reproducer above is what identified `substFvar`'s key set as the
mechanism.

Fails on **1 of 400** generated draws — the rate at which a generated body both
mentions `old` and is reached by a call — and is pinned by a `#guard` on the
two-procedure program above.

---

## 4. `ProcedureInlining` drops the callee's `requires` obligation

**Site:** `Strata/Transform/ProcedureInlining.lean:207-289` (`inlineCallCmd`).

**This is the most serious defect in this report.** The others produce a program that
is untidy or ill-typed — loudly wrong. This one produces a program that verifies
*successfully* when it should fail.

A procedure's `requires` clause is an obligation on its **callers**. Before inlining,
`Program.eval` emits it at the call site as
`assert [(Origin_Callee_Requires)pre]`. `inlineCallCmd` builds its replacement block
from the callee's **body** plus argument and output plumbing:

```lean
let stmts : List (Imperative.Stmt Core.Expression Core.Command)
  := inputInits ++ outputInits
     ++ Block.setCallSiteMetadata procBodyStmts md
     ++ outputSetStmts
```

`proc.spec.preconditions` is never read. And nothing downstream re-derives the
obligation, because after inlining there is no `call` command left for a later phase
to attach one to.

### Reproduction

The minimal witness: a callee with `requires x >= 0` and an **empty body**, called
with `-1`. A fully self-contained runnable version — importing only
Strata, so it needs nothing from this repository — is in repo issue #107.

```lean
def geZeroX : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Ge", ()⟩ none) (.fvar () ⟨"x", ()⟩ (some .int))) (intLit 0)

def preconditionEmptyBodyProgram : Program :=
  { decls :=
      [ .proc { header := { name := ⟨"Callee", ()⟩, typeArgs := [],
                            inputs := [(⟨"x", ()⟩, .int)], outputs := [],
                            noFilter := false }
                spec := { preconditions := [("pre", { expr := geZeroX })],
                          postconditions := [] }
                body := .structured [] } .empty,
        callerPassing (intLit (-1)) ] }
```

**Source** (typechecks):

```
program Core;

procedure Callee (x : int)
spec {
  requires [pre]: x >= 0;
  } {
  
};
procedure Caller ()
{
  var y : int := -1;
  call Callee(y);
};
```

**Symbolic evaluation BEFORE inlining** is a single line. The obligation is `false`
because `-1 >= 0` folds to it, so it cannot be discharged — correctly reporting that
the call is illegal:

```
procedure Callee ()
{
  assert [|(Origin_Callee_Requires)pre|]: false;
};
```

obligation labels: `[(Origin_Callee_Requires)pre]`

**After `ProcedureInlining`** the entire inlined block is one variable binding:

```
program Core;

procedure Callee (x : int)
spec {
  requires [pre]: x >= 0;
  } {
  
};
procedure Caller ()
{
  var y : int := -1;
  Callee$inlined: {
    var Callee_x_0 : int := y;
  }
};
```

**Symbolic evaluation AFTER inlining** yields an empty procedure:

```
procedure Callee ()
{
  
};
```

obligation labels: `[]`

### Why the empty body is the right witness

The precondition check is this program's **only** proof obligation, so the list does
not merely shrink — it *empties*. Verifying the inlined program checks nothing at
all, while verifying it before inlining checks exactly one thing that must fail.

That also forecloses the natural objection to a weaker witness: with a non-empty
callee body the labels go
`[inner, (Origin_Callee_Requires)pre] → [inner, Callee_inner_1]`, and a reader could
ask whether the obligation was *renamed* into `Callee_inner_1` rather than dropped.
With an empty body there is no candidate for it to have become.
`preconditionCallProgram` keeps that non-empty variant, so the report shows the defect
is not an artifact of the body being empty.

### The argument is not inspected either

Passing a value that *satisfies* the precondition shows the pre-inlining obligation is
a real check on the caller's argument rather than a constant:

| caller passes | obligation before inlining | after inlining |
| --- | --- | --- |
| `-1` | `assert …: false` (must fail) | *dropped* |
| `5` | `assert …: true` (discharges) | *dropped* |

The pass drops it either way — it never looks at the argument. Only the `-1` row is
unsound; the `5` row merely loses a check that happened to succeed.
`preconditionSatisfiedProgram` pins the contrast.

### The generated counterexample

The hand-built program above is the minimal reproducer, but it is not what found the
defect. The property failed on a **randomly generated** draw at 400 trials, and the
whole-program shrinker minimized it to this — reproduced verbatim as
`Core.formatProgram` renders it:

```
program Core;

procedure Mj<P, jvB> (inout xB : string, inout sRw : real, inout w : real, out u : int, out h : real)
spec {
  requires [y_]: (fun __q0 : bv64 => true)(bv{64}(5065526758814335903));
  } {
  
};
procedure HcX<E, n, $> (inout o : Sequence real, p : regex, DN : bool, out E : int)
{
  var xB : string;
  var sRw : real;
  var w : real;
  var xxxxxx : int;
  var xxxxxxx : real;
  call Mj(inout xB, inout sRw, inout w, out xxxxxx, out xxxxxxx);
};
```

It typechecks. Nothing about it is contrived: the generator drew a beta redex for the
precondition, five parameters of assorted types, two type parameters on each procedure,
and a procedure whose type parameter is named `$`.

**After `ProcedureInlining`:**

```
program Core;

procedure Mj<P, jvB> (inout xB : string, inout sRw : real, inout w : real, out u : int, out h : real)
spec {
  requires [y_]: (fun __q0 : bv64 => true)(bv{64}(5065526758814335903));
  } {
  
};
procedure HcX<E, n, $> (inout o : Sequence real, p : regex, DN : bool, out E : int)
{
  var xB : string;
  var sRw : real;
  var w : real;
  var xxxxxx : int;
  var xxxxxxx : real;
  Mj$inlined: {
    var Mj_xB_3 : string := xB;
    var Mj_sRw_4 : real := sRw;
    var Mj_w_5 : real := w;
    var Mj_u_6 : int;
    var Mj_h_7 : real;
    xB := Mj_xB_3;
    sRw := Mj_sRw_4;
    w := Mj_w_5;
    xxxxxx := Mj_u_6;
    xxxxxxx := Mj_h_7;
  }
};
```

The argument and output plumbing is all there — `Mj_xB_3` through `Mj_h_7`, then the
write-backs. The `requires` clause is not.

```
obligation labels BEFORE: [(Origin_Mj_Requires)y_]
obligation labels AFTER:  []
```

This is the shape the minimal witness above distills: an empty callee body, so the
obligation list empties rather than shrinking. All four witnesses are pinned by
`#guard` in `ProgramGen/UnprovenTransforms.lean`
(`preconditionEmptyBodyProgram`, `preconditionCallProgram`,
`preconditionSatisfiedProgram`, `generatedRequiresWitness`), so none of them depends
on a lucky reseed.

### Impact

Critical, and in the worst direction. `procedureInliningPipelinePhase` is built with
`modelPreservingPipelinePhase`, whose contract is that the phase "cannot introduce
spurious models" — the exact property this breaks. Any pipeline that enables procedure
inlining silently stops checking preconditions at inlined call sites.

Mitigating: `procedureInliningPipelinePhase` is not in `corePipelinePhases`, so the
default verification pipeline is unaffected. It is reached through
`EntryPoint.lean:72`, so a consumer that opts into inlining is exposed.

### The mirror case, not covered here

An `ensures` clause is the dual: an obligation on the callee and an *assumption* for
the caller. Dropping it loses an assumption, which is incomplete rather than unsound —
verification gets harder, not wrong. This report does not test it; worth a follow-up.

**Suggested fix:** emit `assert` for each of the callee's preconditions (with the
arguments substituted for the formals) at the head of the inlined block, and `assume`
for each postcondition at its tail. The substitution machinery is already there —
`inputInits` maps each formal to its argument.

### The property that found it

`procInline: symbolic evaluation loses no obligation`
(`checkInlineProcSymbolicAgreement`). It runs Strata's own executable symbolic
evaluator — `toCoreProofObligationProgram`, the `symbolicEval` phase of
`corePipelinePhases` — on both sides of the pass, and asserts every obligation label
present before is still present after:

```lean
def checkInlineProcSymbolicAgreement (p : Program) : Bool :=
  !progTypeChecks p ||
    (match runPhase inlinePhase p with
     | none => true
     | some (_, out) =>
       (match symbolicObligations p with
        | none => true
        | some before =>
          (match symbolicObligations out with
           | none => false
           | some after =>
             let la := (programBodies before).flatMap stmtsAssertLabels
             let lb := (programBodies after).flatMap stmtsAssertLabels
             la.all lb.contains)))
```

**Getting the claim right was the whole difficulty.** The obvious formulation — the
two obligation programs are equal — is false by design, and measurably so: inlining
verifies the callee's body once per call site, so the multiset *grows*
(`[inner] → [inner, Callee_inner_1, Callee_inner_3]` on two call sites). An equality
claim would have reported correct behaviour as a bug, the same trap #79's
`useArrayTheory` property fell into before being restated. Weakening it to *containment*
is what makes it both true and sharp enough to catch a dropped obligation.

Found on a generated draw at 400 trials. The shrunk witness is shown above under
"The generated counterexample"; both it and the minimal hand-built reproducer are
pinned by `#guard`, so the finding does not depend on a reseed.

**Re-measured after #106, #84 and #102 landed:** this property now passes 1000 of
1000 draws, so the draw that found it no longer reproduces at that budget — the
generator's declaration mix moved under those three PRs (#106 alone adds a run of
constant declarations per `distinct` group). Nothing about the defect changed: the
four `#guard` witnesses still fail, which is exactly why they were written. Every
other rate quoted in this report was measured before those merges and should be
read as a lower bound until re-measured.

---

## Coverage caveats worth recording

Two property families barely fire on generated input, which the module doc of
`UnprovenTransforms` records at the definition site so a green tick is not read as
coverage:

- **`CommonSubexprElim`**: the pass fires on **0 of 200** generated programs. It
  needs a *duplicated* subexpression in a procedure body, and each generated
  expression is drawn independently, so two identical non-trivial subterms
  essentially never coincide. All four CSE properties are therefore pinned by `#guard`
  rather than by a draw, and no defect in this report is attributed to them. This is
  the same limitation strata-generators issue #36 measured for the
  `ANFEncoder` properties (599 of 600 vacuous).

- **`FunctionInlining`**: **231 of 400** programs are now rewritten, up from 0 at the
  start of this work, and all four properties pass. Getting there took four changes,
  and the order matters because three of them addressed a bottleneck that was not the
  obvious one:

  1. `GenState.octx` was fixed across the declaration fold, so a program declared
     functions its own bodies could not name. Growing it took the rate to **0**.
  2. The property read only *procedure* bodies, whereas the pass fires in a
     *function* body or `requires` clause. Widening it: **1 of 400**.
  3. Polymorphic functions could not be registered at all (114 of 158 declared
     functions are polymorphic, and `OpCtx` holds one monotype per operator), so
     `funcPolyOpEntry` now sends them to `pctx`; plus order-aware declaration
     weights. Together: **4 of 400**.
  4. The actual bottleneck was **operator-selection dilution**. `genIndir` and
     `genIndirPoly` pick with `elements`, which is *uniform* over the candidates for
     the target type, and `Core.Factory` supplies 105 operators returning `bool` and
     27 returning `int` — so a single entry gave a declared function ~1% odds at a
     `bool` leaf. It was registered correctly and never drawn. Repeating the entry
     (`declaredFuncWeight`) plus synthesizing one saturated call per declared bodied
     function (`synthesizedCalls`) took it to **231 of 400**.

  Worth stating plainly: growing the vocabularies was necessary but on its own bought
  a factor of 4 against a needed factor of 200.

  **The result is a clean bill for this pass.** Over 600 programs and 439 inlining
  events — 336 at a *polymorphic* function, so `LFunc.computeTypeSubst` and
  `applySubst` are genuinely exercised — all four properties hold, as do two further
  ad-hoc checks run while hunting: the output is a fixed point at high fuel, and no
  type variable appears in the result that the input lacked. That is a real negative
  result rather than an absence of testing.

Items A and B.1 of **strata-generators issue #105** (registering polymorphic declared
functions in `pctx`, and order-aware declaration weights) are **done here**, along
with two changes the issue did not anticipate — the entry repetition and the
synthesized call sites, which turned out to matter far more. All of it needed **no
proof change**, exactly as the issue predicted: `lake build` re-checks
`genProgram_sound` and every lemma under `ProgramGen/` unchanged, because
`genLExpr_sound` quantifies over both vocabularies and the fold invariant `Inv`
mentions neither.

What remains open in #105 is the CSE duplication gap (item D), which is the one item
whose likely route adds a case to `genLExpr_sound`, and the `numDecls` cap (item C),
which no longer blocks `FunctionInlining` now that call sites are synthesized.

The rates that make the other families non-vacuous, over 200 draws: 12 programs
declare an axiom and all 12 have one pruned by `IrrelevantAxioms`; 33 carry a loop
invariant or a measure; 28 hold a nondeterministic guard; 7 hold an `init` in a loop
body.
