import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Statement-generator properties

`genProgramStmts` generates a well-typed Core statement list (`StatementsHasTypeA`),
proven sound *and* complete against the declarative typing spec, so it is a
certified-well-typed oracle input for the statement typechecker and the
statement-level transformations. Every claim here is currently unproven upstream.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Stmt.TestSupport

/-- The six statement transform / typechecker properties. -/
@[strata_properties]
def stmtTransforms : List TestDecl :=
  family "stmt" Gens.stmts
    [ ("stmt: typechecker accepts generated statements",
       fun gs => checkTypeCheckerComplete gs.stmts),
      ("stmt: LoopElim preserves typeability",
       fun gs => checkLoopElimPreservesTyping gs.stmts),
      ("stmt: LoopElim eliminates all loops",
       fun gs => checkLoopElimZeroLoops gs.stmts),
      ("stmt: ANF is idempotent",
       fun gs => checkAnfIdempotent gs.stmts),
      ("stmt: ANF preserves typeability",
       fun gs => checkAnfPreservesTyping gs.stmts),
      ("stmt: mapExprs id = id",
       fun gs => checkMapExprsId gs.stmts) ]

/-- `StmtToKleeneStmt` is defined exactly when the block has no
    `exit`/`funcDecl`/`typeDecl` — and, for the invariant-loop caveat, not defined
    when an invariant-bearing loop is present. Its panel records the definedness
    verdict *and* why, so it keeps a bespoke one. -/
@[strata_property]
def stmtKleeneDefinedIff : TestDecl :=
  (TestDecl.property "stmt: DetToKleene defined iff supported" "stmt" Gens.stmts
    (fun gs => checkKleeneDefinedIff gs.stmts)).withPanel genKleeneDefined
