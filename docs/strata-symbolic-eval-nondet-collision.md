# Bug report for Strata: the symbolic evaluator silently drops proof obligations after a second `if *`

**Tracked as:** repo issue #113. Found by the properties added in repo PR #110.

**Severity: critical (unsound).** A program whose assertions are never checked is
reported as verified. No diagnostic, no warning, no statistic.

**Target repo:** `strata-org/Strata`, `main` (observed at `a7b52555`, the revision
`lake-manifest.json` pins on the `upstream-strata-main` branch of this repository —
strata-generators PR #109). Not fork-only.

**Affected code:** `Strata/Languages/Core/StatementEval.lean:586`, the `.nondet`
arm of `Core.Statement.evalOneStmt`.

**How it was found:** property-based testing of whether the three loop passes
`InsertLoopInvariantAsserts`, `NondetElim` and `LoopInitHoist` preserve the result
of symbolic evaluation (strata-generators §2.9 of
`StrataGenerators/ProgramGen/UnprovenTransforms.lean`). The defect is in none of
those three passes — it surfaced because `NondetElim` **removes** every `if *`, so
running it made obligations *reappear* that the evaluator had been dropping. A
property comparing obligations before and after the pass therefore saw the
obligation set grow, which is what led back to the evaluator.

---

## The defect

The evaluator has no `.nondet` case for `.ite`. It desugars one into a havoc plus a
deterministic `.ite` over a synthesized boolean variable
(`StatementEval.lean:583-590`):

```lean
| .ite cond then_ss else_ss _ =>
  match cond with
  | .nondet =>
    let freshName : CoreIdent := ⟨s!"$__nondet_cond_{Ewn.env.pathConditions.scopes.length}", ()⟩
    let freshVar : Expression.Expr := .fvar () freshName none
    let initStmt := Statement.init freshName (.forAll [] (.tcons "bool" [])) .nondet ...
    let iteStmt := Imperative.Stmt.ite (.det freshVar) then_ss else_ss ...
    evalSub Ewn [initStmt, iteStmt] nextSplitId
```

The name is built from `Ewn.env.pathConditions.scopes.length` — the current
path-condition **depth**. A depth is not a supply of fresh names:

* it does not increase from one statement to the next, so two `if *` that are
  siblings in the same block are handed the *same* name;
* entering a `.block` does not increase it either — `Env.pushEmptyScope` touches
  `exprEnv.state` only (`Env.lean:231`), not `pathConditions`;
* an enclosing `.ite` does increase it, but `Env.performMerge` pops that scope back
  off when the branches merge (`Env.lean:376-378`), so the increase does not
  survive the construct.

So the second `if *` emits `init $__nondet_cond_N` for an `N` whose name is already
declared and still in scope. That path takes an error, and the first thing
`evalAuxGo` does with an errored path set is stop (`StatementEval.lean:636-637`):

```lean
let (errors, good) := Ewns.partition (fun ewn => ewn.env.error.isSome)
if good.isEmpty then (Ewns, noStats, nextSplitId)
```

The remaining statements are never evaluated, so their obligations are never
deferred. `toCoreProofObligationProgram` reads `postEvalEnv.deferred` and returns
`.ok` regardless, so the error never reaches a diagnostic, and no statistic
records it either (`simulatingStmtHitOutOfFuel` is not it — this is not fuel
exhaustion; `Evaluator.simulatedStmts` simply stops rising).

## Reproducer

Self-contained apart from the two helpers, and needs nothing from this repository
beyond them.

```lean
import Strata.Languages.Core.Verifier

open Lambda Core Imperative

def trueLit : Expression.Expr := .const () (.boolConst true)

def gProg (ss : List Statement) : Program :=
  { decls := [.proc
      { header := { name := ⟨"P", ()⟩, typeArgs := [], inputs := [], outputs := [],
                    noFilter := false }
        spec := { preconditions := [], postconditions := [] }
        body := .structured ss } .empty] }

/-- `assert [l]: true` -/
def gAssert (l : String) : Statement := Statement.assert l trueLit .empty

/-- `if * { assert [l]: true }` -/
def ndIte (l : String) : Statement := .ite .nondet [gAssert l] [] .empty

/-- `if (true) { assert [l]: true }` -/
def detIte (l : String) : Statement := .ite (.det trueLit) [gAssert l] [] .empty

/-- Every `assert` label of a statement list, at any depth. The evaluator nests
    its obligations inside blocks, so a shallow scan under-reports them. -/
partial def assertLabels (ss : List Statement) : List String :=
  ss.flatMap fun
    | .cmd (.cmd (.assert l _ _)) => [l]
    | .block _ b _ => assertLabels b
    | .ite _ t e _ => assertLabels t ++ assertLabels e
    | .loop _ _ _ b _ => assertLabels b
    | _ => []

/-- The labels of the obligations the evaluator emits. -/
def obligations (ss : List Statement) : Option (List String) :=
  match Core.toCoreProofObligationProgram Core.VerifyOptions.quiet (gProg ss) with
  | .error _ => none
  | .ok (out, _) =>
    some (out.decls.flatMap fun
      | .proc q _ => (match q.body with
          | .structured b => assertLabels b
          | .cfg _ => [])
      | _ => [])

-- One `if *`: correct.
#guard obligations [ndIte "a", gAssert "after"]              == some ["a", "after"]
-- Two: `b` is dropped, and so is everything after it.
#guard obligations [ndIte "a", ndIte "b"]                    == some ["a"]
#guard obligations [ndIte "a", ndIte "b", gAssert "after"]   == some ["a"]
-- The obligation *between* them survives, which locates the stop at the second
-- nondeterministic guard exactly.
#guard obligations [ndIte "a", gAssert "mid", ndIte "b"]     == some ["a", "mid"]
-- Deterministic guards at the same depth are unaffected: this is about `.nondet`,
-- not about `.ite`.
#guard obligations [detIte "a", detIte "b"]                  == some ["a", "b"]
-- Nor is it depth as such — nesting gives the two guards different path-condition
-- depths, hence different names, and both obligations survive.
#guard obligations [.ite .nondet [gAssert "a", ndIte "b"] [] .empty] == some ["a", "b"]
```

### The mechanism, pinned directly

The name is predictable, so a *source* program can collide with it. Declaring
`$__nondet_cond_2` and then using a single `if *` loses **every** obligation in the
procedure:

```lean
def collidingName : Statement :=
  Statement.init ⟨"$__nondet_cond_2", ()⟩ (.forAll [] .bool) (.det trueLit) .empty

def innocentName : Statement :=
  Statement.init ⟨"$__nondet_cond_99", ()⟩ (.forAll [] .bool) (.det trueLit) .empty

-- Typechecks, evaluation returns `.ok`, and the obligation list is empty.
#guard obligations [collidingName, ndIte "a", gAssert "after"] == some []
-- The control, under a name the evaluator will not mint.
#guard obligations [innocentName,  ndIte "a", gAssert "after"] == some ["a", "after"]
```

## Why it matters

`assert` obligations are what the verifier proves. Dropping one turns a program
that *must fail* verification into one that passes, and this drops all of them
from the second `if *` to the end of the procedure. Two sibling `while *` loops,
or two sibling `if *`s, is not an exotic shape — and after `LoopElim` every
`while *` **becomes** an `if *` (`LoopElim.lean:139` emits `.ite guard ...`), so any
procedure with two nondeterministic loops at the same nesting level reaches this on
the standard pipeline.

The failure is silent in every channel: no `Message`, no warning on the `Env`, no
statistic, and the obligation program is still well formed. Nothing downstream can
tell the difference between "these assertions were proved" and "these assertions
were never looked at".

## Suggested fix

Mint the name from a monotone counter rather than from a scope depth. The
evaluator already threads `nextSplitId` through every one of these functions for
exactly this purpose, and `NondetElim` — which performs the same desugaring as a
source-to-source pass — already does it correctly, with a `StringGenState` counter
behind `Imperative.ndelimItePrefix`.

Two further hardenings worth considering independently of the naming fix, since
each turns this class of defect from silent into visible:

1. **Do not let a re-declaration be silent.** `evalAuxGo` abandoning the remaining
   statements when every path has errored is reasonable, but the error should reach
   `toCoreProofObligationProgram`, which currently reads `deferred` off the final
   `Env` without consulting `Env.error`. Surfacing it as a `Message` would have
   made this a loud failure rather than a quiet `pass`.

2. **Reserve the synthesized prefixes.** `$__nondet_cond_` is mintable by the
   evaluator but writable by a source program, which is what the second reproducer
   above exploits. The same is true of `$__cse.` (strata-generators already reports
   a collision there) and of `$__ndelim_ite$` / `$__ndelim_loop$`.

## Related findings from the same property family

* `docs/strata-unproven-transform-bugs.md` — four defects in the unproven Core
  transform passes, including `ProcedureInlining` dropping the callee's `requires`
  obligation (repo issue #107), which is the other unsound, obligation-losing
  defect in the set.
