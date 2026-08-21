import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Properties of the statement generator

`genProgramStmts` makes a well-typed list of Core statements, which the relation
`StatementsHasTypeA` describes. The generator is sound *and* complete against the declarative
typing specification. Its output is therefore an input with a certificate of good typing,
both for the statement type checker and for the transformations on statements. Upstream
proves none of the claims here.

Two of the properties below name their *distribution* as well as their check. Soundness and
completeness say that every sample is well-typed and that every well-typed program is
reachable. Neither says how *often* a shape appears. `LoopElim`'s two properties are the
identity on a loop-free program, where they degenerate into `stmt: typechecker accepts
generated statements`, which the suite already tests.

`dist-report` measures a loop in 23–26% of statement lists at the source weights, and in
80–82% under `stmtLoopHeavy`. A loop inside a loop goes from 0–2% to 27–28%, and that is
where a loop-elimination pass is most likely to be wrong. So those two properties are
registered under both weightings, through `@[strata_property (tunings := …)]`. Each row has
its own verdict and its own Tyche panel. The `[default]` row is exactly the property as
written, because `genWith defaults` is the type's `Arbitrary` instance.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.TuningProfiles

/-- The four properties for the statement transformations and for the statement type checker whose
    default distribution is adequate. The two `LoopElim` claims are registered separately, under two
    weightings. -/
@[strata_properties]
def stmtTransforms : List TestDecl :=
  family GenStmts
    [ ("stmt: typechecker accepts generated statements",
       fun gs => checkTypeCheckerComplete gs.stmts),
      ("stmt: ANF is idempotent",
       fun gs => checkAnfIdempotent gs.stmts),
      ("stmt: ANF preserves typeability",
       fun gs => checkAnfPreservesTyping gs.stmts),
      ("stmt: mapExprs id = id",
       fun gs => checkMapExprsId gs.stmts) ]

/-- `LoopElim` preserves typeability. It is checked at the source weights *and* at weights
    that make a loop the modal statement, because the claim has no content without a loop. -/
@[strata_property (tunings := [("default", stmtDefault), ("loop-heavy", stmtLoopHeavy)])]
def loopElimPreservesTyping : TestDecl :=
  .property "stmt: LoopElim preserves typeability"
    fun (gs : GenStmts) => checkLoopElimPreservesTyping gs.stmts

/-- `LoopElim` eliminates every loop. The claim is vacuously true on a loop-free program, so the
    loop-heavy row is the row that carries it.

    **Both rows fail, and the weights are not the mechanism.** `Core.removeLoop` throws on a loop that
    still carries an invariant or a measure. `loopElimStmts` returns the input unchanged when the pass
    throws, so such a loop survives and the count is not zero.
    This is machine-checked with no generator involved:
    `checkLoopElimZeroLoops [.loop .nondet none [("i", .const () (.boolConst true))] [] .empty]`
    is `false`, and the same loop without the invariant gives `true`.

    An invariant-bearing loop appears in 16% of samples at the source weights and in 56–58%
    under `stmtLoopHeavy`. That is why the loop-heavy row fails faster rather than differently.
    The claim as stated really reads "unless the pass throws". The fix belongs upstream, or in
    the property, and this property pins the defect either way. -/
@[strata_property (tunings := [("default", stmtDefault), ("loop-heavy", stmtLoopHeavy)])]
def loopElimZeroLoops : TestDecl :=
  .property "stmt: LoopElim eliminates all loops"
    fun (gs : GenStmts) => checkLoopElimZeroLoops gs.stmts

/-- `StmtToKleeneStmt` is defined exactly when the block holds no `exit`, no `funcDecl` and
    no `typeDecl`. It is also not defined when the block holds a loop that has an invariant.
    The panel gives the verdict on definedness *and* the reason for it, so this property keeps
    a panel of its own. -/
@[strata_property]
def stmtKleeneDefinedIff : TestDecl :=
  (TestDecl.property "stmt: DetToKleene defined iff supported"
    (fun (gs : GenStmts) => checkKleeneDefinedIff gs.stmts)).withPanel genKleeneDefined
