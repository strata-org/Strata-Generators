import StrataGenerators.ProcedureHasTypeAGen.TestSupport
import StrataGenerators.StmtHasTypeAGen.TestSupport
import Strata.Languages.Core.ProcedureType

open Lambda Core Imperative
-- The statement-level shrinker (`shrinkStmtsList`, recursing into `shrinkCmd` and
-- `shrinkLExpr`), the size measure `sizeStmts`, and the ambient typing context
-- `stmtCheckContext` all come from the statement test support.
open StrataGenerators.Stmt.TestSupport

/-!
# Well-typed shrinker for generated procedures

The procedure-level analogue of the expression (`shrinkLExpr`), command
(`shrinkCmd`), statement (`shrinkStmts`) and function (`shrinkFuncWellFormed`)
shrinkers: it proposes structurally smaller procedures and rejection-samples them
on a well-typedness oracle. Nothing here re-implements a reduction that already
exists — body reductions are delegated wholesale to `shrinkStmtsList` (which
recurses through `shrinkStmt` into `shrinkCmd` and `shrinkLExpr`), and contract
clauses are reduced with `shrinkLExpr` directly.

## The oracle

Candidates are filtered by `procTypeChecks`, i.e. Strata's own whole-procedure
typechecker `Core.Procedure.typeCheck`, run in the same standard ambient context
(`stmtCheckContext`: the full `Core.Factory` and `Core.KnownTypes`) the statement
properties use. So every procedure this shrinker yields is well-typed by the
algorithm.

Checking the *whole* procedure rather than tracking per-node types is what makes
the delegation above sound, and it is what decides several obligations for free:

- **Contract clauses stay Boolean.** `Procedure.typeCheck`'s `typeCheckConditions`
  rejects any pre/postcondition whose type is not `bool` (ProcedureType.lean:93),
  so a clause reduced to a non-Boolean subterm is filtered out rather than
  emitted. Clauses may therefore be shrunk freely.
- **Modification rights stay valid.** Dropping a body statement can leave a `set x`
  whose defining `init x` is gone, which `checkModificationRights` rejects
  (ProcedureType.lean:55) — again caught by the filter, not by local reasoning.
- **`old v` stays in scope.** Postconditions may mention `old v` for in-out
  parameters; since the header is held fixed (below), those bindings survive every
  reduction.

## What is preserved, and what is not

Following the convention of the function shrinker
(`FunctionHasTypeAGen.Shrink.shrinkFuncCandidates`, which is body-only), the
**entire header is held fixed**: name, `typeArgs`, `inputs`, `outputs` and
`noFilter`. A shrunk procedure therefore has exactly the original's type
signature, and stays a drop-in replacement for it in any program the properties
assemble — in particular the modifies-clause obligation is unchanged, and the
`P0…Pk` names the procedure properties key off stay put.

The contract and the body are *not* preserved: clauses may be dropped or reduced
and the body may be reduced to `[]` (an abstract procedure). This is intended and
is what the requirement permits — the shrunk procedure need not have the same
*behaviour* or contract, only the same signature and the well-typedness
invariant.

CFG bodies are left alone entirely: `Procedure.typeCheck` rejects them outright
("CFG procedures not supported yet"), so no CFG-bodied candidate could pass the
filter. `genProcedure` only ever produces structured bodies, so this costs
nothing on generated input.
-/

namespace StrataGenerators.Procedure.TestSupport

-- ── Well-typedness oracle ─────────────────────────────────────────────────

/-- Whether Strata's whole-procedure typechecker accepts `p` as a declaration of
    `prog`, in the standard Core ambient context. The `prog` argument is consulted
    only by the `call` branch of the statement typechecker; generated procedures
    now *do* emit calls against their siblings (see the module doc of
    `StrataGenerators.ProcedureHasTypeAGen.TestSupport`, point 1), so the
    procedure-*list* shrinker must pass the assembled program (`mkProgram ps`) for
    the check to stay faithful — a candidate that still calls `P{j}` only
    typechecks against a program in which `P{j}` is declared. The default empty
    program is retained only for the call-free standalone sanity `#guard`s below. -/
def procTypeChecks (p : Procedure) (prog : Program := Program.init) : Bool :=
  match Procedure.typeCheck stmtCheckContext TEnv.default prog p .empty with
  | .ok _ => true
  | .error _ => false

/-- Whether every procedure in a list typechecks, each against the program the
    list assembles to. This is the invariant the list-level shrinker maintains:
    *every* candidate family is filtered through it, including the drop family.

    Filtering drops as well may look redundant — removing a procedure cannot break
    the ones that remain — and on well-typed input it never rejects anything. It
    matters for *ill-typed* input, which does occur: `Procedure.typeCheck` rejects
    a body declaring a function with a `decreases` clause but no body, the known
    completeness gap (measured at 7 of 400 generated procedures). Without this
    filter, shrinking such a list would emit smaller *ill-typed* lists and quietly
    break the shrinker's contract. With it, the guarantee is unconditional: every
    list this shrinker returns is well-typed regardless of what it was handed.

    The cost is that a counterexample resting on the completeness gap cannot be
    minimized — no smaller candidate passes, so the input is reported unshrunk.
    That is deliberate and matches `shrinkStmts`, which makes the same trade for
    the same reason (see its comment in `StmtHasTypeAGen.TestSupport`): an unshrunk
    counterexample is a worse report, never a wrong one. -/
def procsTypeCheck (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  ps.all fun p => procTypeChecks p prog

-- ── Size measure ──────────────────────────────────────────────────────────

/-- Size of one contract clause: its expression's AST size, plus one for the
    clause itself (so *dropping* a clause is strictly smaller than shrinking its
    expression to a leaf). -/
def sizeCheck (c : Procedure.Check) : Nat := 1 + c.expr.sizeOf

/-- Size of the parts of a procedure this shrinker can reduce: the body's
    statement AST plus both contract clause lists. The header is excluded because
    it is held fixed, so it contributes a constant that would only dilute the
    strict-decrease test. -/
def sizeProc (p : Procedure) : Nat :=
  sizeStmts (bodyStmts p.body)
    + (p.spec.preconditions.values.map sizeCheck).sum
    + (p.spec.postconditions.values.map sizeCheck).sum

-- ── Candidate families ────────────────────────────────────────────────────

/-- Replace the clause at index `i` of a clause list, keeping its label. -/
private def setClause (cs : ListMap CoreLabel Procedure.Check) (i : Nat)
    (e : Expression.Expr) : ListMap CoreLabel Procedure.Check :=
  match cs.toList[i]? with
  | some (l, c) => ListMap.ofList (cs.toList.set i (l, { c with expr := e }))
  | none => cs

/-- Structurally smaller candidate procedures, **largest reduction first** (which
    is what makes the greedy `minimizeProcWhile` converge quickly):

    1. drop the body entirely, leaving an abstract procedure;
    2. drop one precondition; 3. drop one postcondition;
    4. reduce the body via `shrinkStmtsList` (drop a statement, replace one by a
       smaller one, or splice a compound's body in place of the compound —
       recursing into `shrinkCmd` and `shrinkLExpr`);
    5. reduce one precondition expression via `shrinkLExpr`;
    6. reduce one postcondition expression via `shrinkLExpr`.

    Candidates are raw: ill-typed ones are removed by `shrinkProcWellTyped`. The
    header is untouched in every family. -/
def shrinkProcCandidates (p : Procedure) : List Procedure :=
  let body := bodyStmts p.body
  let pres := p.spec.preconditions.toList
  let posts := p.spec.postconditions.toList
  let withPre (cs : ListMap CoreLabel Procedure.Check) : Procedure :=
    { p with spec := { p.spec with preconditions := cs } }
  let withPost (cs : ListMap CoreLabel Procedure.Check) : Procedure :=
    { p with spec := { p.spec with postconditions := cs } }
  -- Only structured bodies are reduced; a CFG body could not typecheck anyway.
  let structured := p.body.isStructured
  let dropBody := if structured && !body.isEmpty then [{ p with body := .structured [] }] else []
  let dropPre := (fun cs => withPre (ListMap.ofList cs)) <$> dropEach pres
  let dropPost := (fun cs => withPost (ListMap.ofList cs)) <$> dropEach posts
  let shrinkBody :=
    if structured then
      (fun ss => { p with body := Procedure.Body.structured ss }) <$> shrinkStmtsList body
    else []
  let shrinkPre := pres.zipIdx.flatMap fun ((_, c), i) =>
    (fun e => withPre (setClause p.spec.preconditions i e)) <$> shrinkLExpr c.expr
  let shrinkPost := posts.zipIdx.flatMap fun ((_, c), i) =>
    (fun e => withPost (setClause p.spec.postconditions i e)) <$> shrinkLExpr c.expr
  dropBody ++ dropPre ++ dropPost ++ shrinkBody ++ shrinkPre ++ shrinkPost

/-- Well-typed structural shrinks of a procedure: every candidate that is strictly
    smaller by `sizeProc` and still accepted by `Procedure.typeCheck`. This is the
    one-step candidate list the `Shrinkable` typeclass expects; the greedy
    whole-list minimizer used by the Tyche panels is `minimizeProcsWhile`. -/
def shrinkProcWellTyped (p : Procedure) (prog : Program := Program.init) : List Procedure :=
  (shrinkProcCandidates p).filter fun c => sizeProc c < sizeProc p && procTypeChecks c prog

-- ── Procedure lists ───────────────────────────────────────────────────────

/-- Rewrite each procedure's name to `P{i}` so a procedure list has distinct,
    collision-free names. The name-based FilterProcedures / ordering properties
    need this: `genProcedure` draws each name independently, so two procedures
    could otherwise share one and confound the checks. Applied after every
    list-level reduction so the surviving procedures stay `P0…Pk`. -/
def relabelProcs (ps : List Procedure) : List Procedure :=
  ps.zipIdx.map fun (p, i) =>
    { p with header := { p.header with name := ⟨s!"P{i}", ()⟩ } }

/-- Structurally smaller, **well-typed** candidate procedure *lists*: drop one
    procedure, or replace one procedure by a smaller one. Dropping comes first (the
    larger reduction). Every candidate is relabelled `P0…Pk`, and every candidate —
    drops included — is filtered through `procsTypeCheck`, so the well-typedness
    guarantee holds even on ill-typed input (see `procsTypeCheck`).

    Per-procedure candidates are proposed against the program assembled from the
    *original* list, which is the program shape the procedure properties run the
    passes on, and then re-checked as a list after relabelling. -/
def shrinkProcsList (ps : List Procedure) : List (List Procedure) :=
  let prog := mkProgram ps
  let candidates :=
    (relabelProcs <$> dropEach ps)
      ++ ps.zipIdx.flatMap fun (p, i) =>
          (fun p' => relabelProcs (ps.set i p')) <$> shrinkProcWellTyped p prog
  candidates.filter procsTypeCheck

/-- Total reducible size of a procedure list (`sizeProc` summed), the measure the
    greedy minimizer decreases. -/
def sizeProcs (ps : List Procedure) : Nat := (ps.map sizeProc).sum

/-- Greedily minimize `ps` while the predicate `fails` still holds, mirroring the
    round-trip minimizer `FunctionHasTypeAGen.Roundtrip.shrinkWhile`: repeatedly
    take the first strictly-smaller candidate that still satisfies `fails`, until
    no candidate does or the fuel runs out.

    Used by the Tyche panels to report the *minimal* counterexample to a procedure
    property rather than the raw generated one. Because a candidate is kept only
    when it still fails, the returned list is always a genuine counterexample —
    and because every candidate passed `procTypeChecks`, it is always a well-typed
    one. If the property's failure hinges on something no smaller well-typed list
    reproduces, this returns `ps` unchanged: never a wrong answer, just an
    unshrunk one. -/
partial def minimizeProcsWhile (fails : List Procedure → Bool) (fuel : Nat)
    (ps : List Procedure) : List Procedure :=
  match fuel with
  | 0 => ps
  | fuel + 1 =>
    let cands := (shrinkProcsList ps).filter fun c => sizeProcs c < sizeProcs ps && fails c
    match cands with
    | [] => ps
    | c :: _ => minimizeProcsWhile fails fuel c

/-- Minimize a counterexample to a `Bool` procedure-list property: the smallest
    well-typed list this shrinker can reach on which `check` still returns `false`.
    Returns `ps` untouched when `check` already holds (nothing to minimize). -/
def minimizeProcsCounterexample (check : List Procedure → Bool) (fuel : Nat := 200)
    (ps : List Procedure) : List Procedure :=
  if check ps then ps else minimizeProcsWhile (fun c => !check c) fuel ps

-- ── Sanity guards ─────────────────────────────────────────────────────────

section Guards

/-- A minimal well-typed procedure: no formals, no contract, empty body. -/
private def emptyProc : Procedure :=
  { header := { name := ⟨"P0", ()⟩, typeArgs := [], inputs := [], outputs := [],
                noFilter := false }
    spec := { preconditions := [], postconditions := [] }
    body := .structured [] }

private def trueExpr : Expression.Expr := .const () (.boolConst true)

/-- `emptyProc` with one trivial precondition and one trivial postcondition. -/
private def specProc : Procedure :=
  { emptyProc with
    spec := { preconditions := [("pre", { expr := trueExpr })],
              postconditions := [("post", { expr := trueExpr })] } }

-- The oracle accepts these by-hand procedures, so it is not vacuously rejecting.
#guard procTypeChecks emptyProc == true
#guard procTypeChecks specProc == true

-- Fully minimal already: nothing smaller to propose. (`sizeProc` bottoms out at 1,
-- not 0 — `Block.sizeOf []` is 1 — which is immaterial: only *differences* matter.)
#guard (shrinkProcWellTyped emptyProc).isEmpty == true
#guard sizeProc emptyProc == 1

-- The contract clauses are reducible, and every reduction stays well-typed.
#guard (shrinkProcWellTyped specProc).isEmpty == false
#guard (shrinkProcWellTyped specProc).all procTypeChecks == true
-- Dropping either clause is offered, and dropping is strictly smaller.
#guard (shrinkProcWellTyped specProc).any (fun p => p.spec.preconditions.isEmpty) == true
#guard (shrinkProcWellTyped specProc).any (fun p => p.spec.postconditions.isEmpty) == true
#guard (shrinkProcWellTyped specProc).all (fun p => sizeProc p < sizeProc specProc) == true

-- The header is preserved by *every* candidate — the signature-fixing convention.
#guard (shrinkProcCandidates specProc).all (fun p => p.header == specProc.header) == true

-- A non-Boolean clause is not well-typed, so the oracle refuses it. This is what
-- licenses shrinking clause expressions freely: `Procedure.typeCheck` is the thing
-- keeping pre/postconditions Boolean, not the candidate generator.
#guard procTypeChecks
  { emptyProc with
    spec := { preconditions := [("pre", { expr := .const () (.intConst 0) })],
              postconditions := [] } } == false

-- List level: dropping is offered, relabelling keeps names contiguous, and the
-- minimizer reaches the empty list for a property that fails on every list.
#guard (shrinkProcsList [emptyProc, specProc]).length > 0
#guard (relabelProcs [specProc, specProc]).map (fun p => p.header.name.name) == ["P0", "P1"]
#guard minimizeProcsWhile (fun _ => true) 100 [emptyProc, specProc] == []
-- A property that holds everywhere leaves the input untouched.
#guard minimizeProcsCounterexample (fun _ => true) 100 [emptyProc, specProc] ==
  [emptyProc, specProc]

-- THE HEADLINE INVARIANT: every candidate list is well-typed.
#guard (shrinkProcsList [emptyProc, specProc]).all procsTypeCheck == true

/-- A procedure whose body declares a function with a `decreases` clause but no
    body — the measure-without-body shape the *algorithmic* typechecker rejects
    while the declarative spec permits it (the documented completeness gap, which
    `genProcedure` reaches on roughly 2% of draws). -/
private def illTypedProc : Procedure :=
  { emptyProc with
    body := .structured [
      .funcDecl { name := ⟨"g", ()⟩, typeArgs := [], inputs := [],
                  output := (.forAll [] .int : LTy), body := none,
                  measure := some (.const () (.intConst 0)),
                  preconditions := [] } .empty ] }

-- The oracle really does reject it (so the case below is not vacuous)...
#guard procTypeChecks illTypedProc == false
#guard procsTypeCheck [illTypedProc] == false
-- ...and, crucially, shrinking an ill-typed list never *emits* an ill-typed one.
-- Before `procsTypeCheck` filtered the drop family too, the drop of `specProc`
-- here would have been emitted unchecked, still carrying `illTypedProc`.
#guard (shrinkProcsList [illTypedProc, specProc]).all procsTypeCheck == true
-- Concretely: the only way past the filter is to drop the offending procedure, so
-- no candidate retains it. (Reducing it in place cannot help either — the gap is in
-- the `funcDecl` the algorithm rejects, and every reduct still contains it or is
-- the drop.)
#guard (shrinkProcsList [illTypedProc, specProc]).all
  (fun c => !c.any (fun p => p.body == illTypedProc.body)) == true
-- Dropping is a legitimate reduction, so a singleton ill-typed list minimizes to
-- the empty list rather than getting stuck. What the filter rules out is reporting
-- a *smaller, still ill-typed* list: the shrinker's output is well-typed either way.
#guard minimizeProcsWhile (fun _ => true) 100 [illTypedProc] == []

end Guards

end StrataGenerators.Procedure.TestSupport
