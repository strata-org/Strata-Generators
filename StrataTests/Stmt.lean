import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Properties of the statement generator

`genProgramStmts` makes a well-typed list of Core statements, which the relation
`StatementsHasTypeA` describes. The generator is sound *and* complete against the declarative
typing specification. Its output is therefore an input with a certificate of good typing,
both for the statement type checker and for the transformations on statements. Upstream
proves none of the claims here.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Stmt.TestSupport

/-- The six properties for the statement transformations and for the statement type
    checker. -/
@[strata_properties]
def stmtTransforms : List TestDecl :=
  family GenStmts
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

/-- `StmtToKleeneStmt` is defined exactly when the block holds no `exit`, no `funcDecl` and
    no `typeDecl`. It is also not defined when the block holds a loop that has an invariant.
    The panel gives the verdict on definedness *and* the reason for it, so this property keeps
    a panel of its own. -/
@[strata_property]
def stmtKleeneDefinedIff : TestDecl :=
  (TestDecl.property "stmt: DetToKleene defined iff supported"
    (fun (gs : GenStmts) => checkKleeneDefinedIff gs.stmts)).withPanel genKleeneDefined
