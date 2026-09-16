/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import Basalt.PBT.Property
import StrataGenerators.HasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.StmtHasTypeAGen.TestSupport
import StrataGenerators.ProgramGen
import StrataGenerators.ProgramGen.LiftFuncDecls
-- `ASTtoCST` gives `Program` a `ToString` (via `Core.formatProgram`); the DDM printer is Mathlib-free.
import Strata.Languages.Core.DDMTransform.ASTtoCST

/-!
# FuzzGen properties for the Strata generators

The suite's expression, statement, and whole-program properties, expressed as Basalt `PropM`
properties so the *same* term runs under `--backend=fuzz|io|plausible` (see `StrataFuzzMain.lean`).

This module is a **strictly additive, self-contained** layer over the mainline suite: it reuses the
suite's own polymorphic generators (`genLExpr`/`genProgramStmts`/`genProgram`) and its own check
functions (`checkPreservation`/`checkAnfPreservesTyping`/…) — one source of truth for each — and it
depends on the baseline one-way (the baseline never depends on this). Dropping fuzzing is therefore
deleting this layer; nothing in the mainline suite changes.

Two things are fuzz-specific and intentionally local here: a *fixed* size per property (`FuzzGen` has
no size parameter, and a fixed size keeps the backends on one input regime), and no `retryGen` — the
retry a `Plausible.Gen` draw needs is applied by the runner (`StrataFuzzMain`), not the property.
The generator wiring restated below mirrors each type's `Generable` instance; it lives here rather
than importing `TestScaffold` because that module pulls the Plausible/SMT/proof closure Mathlib into
the fuzz executable's otherwise Mathlib-free link set.
-/

namespace StrataFuzz

open Basalt.PBT

/-- The shape of every fuzz property: draw a value from the polymorphic generator `g`, score it with
the `Bool` check `ok`, and name it in the counterexample via `render` — built lazily (a `Thunk`), so
the potentially-expensive rendering runs only on a failing draw. The generator, the check, and the
size are a property's only per-case data. -/
def checkGen [Gen G] (g : G α) (ok : α → Bool) (render : α → String) : PropM G Unit := do
  let x ← generate g
  check (ok x) (Thunk.mk fun () => render x)

/-! ## Expressions -/
namespace Expr
open Lambda Core

/-- Fixed depth (matches the suite's `--quick` size of 2). -/
abbrev depth : Nat := 2
/-- A deeper depth, the deepest expression regime for the coverage study (`fuzz-experiment/`). -/
abbrev depthDeep : Nat := 4

/-- Draw a closed, well-typed expression paired with its type, at a fixed depth. Mirrors the
`Generable ClosedTypedExpr` instance. -/
def genClosedTypedExpr [Gen G] (d : Nat) : G (LExpr' × LMonoTy) := do
  let ty ← genLMonoTy (G := G) [] d
  let e  ← genLExpr (G := G) [] coreMonoOps corePolyOps [] [] d ty
  return (e, ty)

/-- Preservation: `eval` preserves the type of a closed well-typed term. Must never fail. -/
def prop_exprPreservation [Gen G] : PropM G Unit :=
  checkGen (genClosedTypedExpr (G := G) depth)
    (fun (e, ty) => checkPreservation e ty) (fun (e, ty) => s!"{reprStr e} : {reprStr ty}")

/-- Preservation at the deeper depth — the deepest reachable input regime for the coverage study. -/
def prop_exprPreservationDeep [Gen G] : PropM G Unit :=
  checkGen (genClosedTypedExpr (G := G) depthDeep)
    (fun (e, ty) => checkPreservation e ty) (fun (e, ty) => s!"{reprStr e} : {reprStr ty}")

/-- Progress: a closed well-typed term is a value or steps. Expected to FAIL (a quantifier in test
position, or a stuck operator application, is neither) — a counterexample every backend can find. -/
def prop_exprProgress [Gen G] : PropM G Unit :=
  checkGen (genClosedTypedExpr (G := G) depth)
    (fun (e, _) => checkProgress e) (fun (e, ty) => s!"{reprStr e} : {reprStr ty}")

end Expr

/-! ## Statements -/
namespace Stmt
open Lambda Core
open StrataGenerators.Stmt
open StrataGenerators.Stmt.TestSupport

/-- Fixed nesting depth and list length (the suite's `--quick` size of 2). -/
abbrev nesting : Nat := 2
abbrev len : Nat := 2

/-- Draw a well-typed statement list at a fixed size. Mirrors the `Generable GenStmts` instance. -/
def genStmts [Gen G] : G (List Statement) := do
  let (ss, _, _) ← genProgramStmts (G := G) coreMonoOps [] nesting len
  return ss

/-- ANF preserves typing: encoding a well-typed statement list to A-normal form keeps it well typed.
Must never fail. Exercises the ANF encoder. -/
def prop_stmtAnfPreservesTyping [Gen G] : PropM G Unit :=
  checkGen (genStmts (G := G)) checkAnfPreservesTyping (fun ss => (Std.format ss).pretty)

/-- Typechecker completeness: the algorithmic checker accepts every generated (well-typed) statement
list. Expected to FAIL — a `funcDecl` with a measure and no body is well typed by the declarative
spec but rejected by the algorithm. -/
def prop_stmtTypeCheckComplete [Gen G] : PropM G Unit :=
  checkGen (genStmts (G := G)) checkTypeCheckerComplete (fun ss => (Std.format ss).pretty)

end Stmt

/-! ## Whole programs -/
namespace Program
open Lambda Core
open StrataGenerators.Program.LiftFuncDecls

/-- Fixed number of top-level declarations (≥ 2, so a pass reading one and rewriting another has work
to do; small so a draw is not dominated by generation dead-ends). -/
abbrev numDecls : Nat := 3

/-- Draw a whole program. Mirrors the `Generable GenProgram` instance. -/
def genProg [Gen G] : G Core.Program := ProgramGen.genProgram (G := G) numDecls {}

/-- `LiftInternalFuncDecls` output typechecks: lifting a well-typed program's internal `funcDecl`s to
top level yields a program the checker still accepts. Must never fail. Exercises the Lift pass and the
whole-program typechecker. -/
def prop_liftOutputTypechecks [Gen G] : PropM G Unit :=
  checkGen (genProg (G := G)) checkLiftOutputTypechecks (fun p => toString p)

end Program
end StrataFuzz
