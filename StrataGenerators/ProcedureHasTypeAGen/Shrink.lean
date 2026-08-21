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
against an oracle for well-typedness. Nothing here writes a reduction again that already exists.
`shrinkStmtsList` performs each reduction of a body, and it recurses through `shrinkStmt` into `shrinkCmd` and
`shrinkLExpr`. `shrinkLExpr` reduces a contract clause directly.

## The oracle

Candidates are filtered by `procTypeChecks`, i.e. Strata's own whole-procedure
typechecker `Core.Procedure.typeCheck`, run in the same standard ambient context
(`stmtCheckContext`: the full `Core.Factory` and `Core.KnownTypes`) the statement
properties use. So every procedure this shrinker yields is well-typed by the
algorithm.

Checking the *whole* procedure rather than tracking per-node types is what makes
the delegation above sound, and it is what decides several obligations for free:

- **Contract clauses stay Boolean.** `Procedure.typeCheck`'s `typeCheckConditions`
  rejects any pre/postcondition whose type is not `bool` (ProcedureType.lean),
  so a clause reduced to a non-Boolean subterm is filtered out rather than
  emitted. Clauses may therefore be shrunk freely.
- **Modification rights stay valid.** Dropping a body statement can leave a `set x`
  whose declaration is gone, and `checkModificationRights` rejects that shape. The filter catches such a
  candidate, and no local argument is necessary.
- **`old v` stays in scope.** Postconditions may mention `old v` for in-out
  parameters; since the header is held fixed (below), those bindings survive every
  reduction.

## What is preserved, and what is not

Following the convention of the function shrinker
(`FunctionHasTypeAGen.Shrink.shrinkFuncCandidates`, which is body-only), the
**entire header is held fixed**: name, `typeArgs`, `inputs`, `outputs` and
`noFilter`. A shrunk procedure therefore has exactly the original's type
signature, and it therefore replaces the original one in each program that a property assembles. The obligation
about the modified variables does not change either, and each name from `P0` up to `Pk` that a property reads
stays the same.

The contract and the body do *not* stay the same. The shrinker can drop a clause or reduce it, and it can reduce
the body to the empty list, which gives an abstract procedure. That behaviour is deliberate, and the requirement
permits it. A shrunk procedure needs the same signature and the invariant about well-typedness, and it needs
neither the same *behaviour* nor the same contract.

CFG bodies are left alone entirely: `Procedure.typeCheck` rejects them outright
("CFG procedures not supported yet"), so no CFG-bodied candidate could pass the
filter. `genProcedure` only ever produces structured bodies, so this costs
nothing on generated input.
-/

namespace StrataGenerators.Procedure.TestSupport

-- ── Well-typedness oracle ─────────────────────────────────────────────────

/-- Whether Strata's whole-procedure typechecker accepts `p` as a declaration of
    `prog`, in the standard Core ambient context. The `prog` argument is consulted
    by the `call` branch of the typechecker for a statement. A generated procedure *does* emit a call to a
    procedure beside it, which the module docstring of `StrataGenerators.ProcedureHasTypeAGen.TestSupport`
    records. Therefore the shrinker for a *list* of procedures must give the assembled program, so that the check
    stays faithful. A candidate that still calls a procedure type checks only against a program that declares
    that procedure. The default empty program is there for the `#guard`s below, which hold no call. -/
def procTypeChecks (p : Procedure) (prog : Program := Program.init) : Bool :=
  match Procedure.typeCheck stmtCheckContext TEnv.default prog p .empty with
  | .ok _ => true
  | .error _ => false

/-- Whether every procedure in a list typechecks, each against the program the
    list assembles to. This is the invariant the list-level shrinker maintains:
    *every* candidate family is filtered through it, including the drop family.

    The filter also applies to the family that drops a procedure. That choice can look unnecessary, because a
    removal of a procedure cannot break the procedures that stay, and on well-typed input the filter rejects
    nothing. It matters for input that is *not* well typed, which does occur. `Procedure.typeCheck` rejects
    a body declaring a function with a `decreases` clause but no body, the known
    completeness gap (measured at 7 of 400 generated procedures). Without this
    filter, shrinking such a list would emit smaller *ill-typed* lists and quietly
    break the shrinker's contract. With it, the guarantee is unconditional: every
    list this shrinker returns is well-typed regardless of what it was handed.

    The cost is that a counterexample which depends on a gap in completeness cannot shrink. No smaller candidate
    passes the filter, so the harness reports the input at its full size. That behaviour is deliberate, and
    `shrinkStmts` makes the same trade for the same reason. Read its comment in
    `StmtHasTypeAGen.TestSupport`. An input at its full size
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
    4. Reduce the body with `shrinkStmtsList`, which drops a statement, replaces one statement by a smaller one,
       or puts the body of a compound statement in place of that statement, and which recurses into `shrinkCmd`
       and `shrinkLExpr`.
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
    procedure, or replace one procedure by a smaller one. The family that drops a procedure comes first, because
    it gives the larger reduction. The function renames each candidate to the names from `P0` up to `Pk`, and
    `procsTypeCheck` filters each candidate, and also each candidate of the family that drops a procedure.
    Therefore the guarantee about well-typedness holds on input that is not well typed too. Read
    `procsTypeCheck`.

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
    when it still fails, the result is always a genuine counterexample. Each candidate also passed
    `procTypeChecks`, so the result is always well typed. When the failure of the property depends on something
    that no smaller well-typed list
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

-- This procedure is already smallest, so the shrinker proposes nothing. `sizeProc` bottoms out at 1, and not at
-- 0, because `Block.sizeOf []` is 1. That value does not matter, because only a *difference* of two sizes
-- matters.
#guard (shrinkProcWellTyped emptyProc).isEmpty == true
#guard sizeProc emptyProc == 1

-- The contract clauses are reducible, and every reduction stays well-typed.
#guard (shrinkProcWellTyped specProc).isEmpty == false
#guard (shrinkProcWellTyped specProc).all procTypeChecks == true
-- Dropping either clause is offered, and dropping is strictly smaller.
#guard (shrinkProcWellTyped specProc).any (fun p => p.spec.preconditions.isEmpty) == true
#guard (shrinkProcWellTyped specProc).any (fun p => p.spec.postconditions.isEmpty) == true
#guard (shrinkProcWellTyped specProc).all (fun p => sizeProc p < sizeProc specProc) == true

-- *Each* candidate keeps the header, by the convention that fixes the signature.
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

/-- A procedure whose body declares a function with a `decreases` clause but no body.

    The typechecker accepts that shape, so this procedure is well typed. This definition stays as a pin for the
    shape and for the invariant of the shrinker about well-typedness. -/
private def measureNoBodyProc : Procedure :=
  { emptyProc with
    body := .structured [
      .funcDecl { name := ⟨"g", ()⟩, typeArgs := [], inputs := [],
                  output := (.forAll [] .int : LTy), body := none,
                  measure := some (.const () (.intConst 0)),
                  preconditions := [] } .empty ] }

-- The oracle *accepts* that shape, so this input is well typed, and each candidate of the shrinker is then well
-- typed for a trivial reason.
#guard procTypeChecks measureNoBodyProc == true
#guard procsTypeCheck [measureNoBodyProc] == true
-- The headline invariant still holds on this input, which is what the pin is for: the
-- `procsTypeCheck` filter covers the drop family as well as the reduce family, so no
-- candidate list can be ill-typed regardless of which shape the checker accepts.
#guard (shrinkProcsList [measureNoBodyProc, specProc]).all procsTypeCheck == true
-- The procedure is well typed, so a candidate can *keep* it.
#guard (shrinkProcsList [measureNoBodyProc, specProc]).any
  (fun c => c.any (fun p => p.body == measureNoBodyProc.body)) == true
-- Dropping is still a legitimate reduction, so a singleton minimizes to the empty list
-- for a property that fails everywhere.
#guard minimizeProcsWhile (fun _ => true) 100 [measureNoBodyProc] == []

end Guards

end StrataGenerators.Procedure.TestSupport
