import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Statement-generator properties

`genProgramStmts` generates a well-typed Core statement list (`StatementsHasTypeA`),
proven sound *and* complete against the declarative typing spec, so it is a
certified-well-typed oracle input for the statement typechecker and the
statement-level transformations. Every claim here is currently unproven upstream.

Two of the properties below name their *distribution* as well as their check. Soundness
and completeness say every sample is well-typed and every well-typed program is
reachable; neither says how *often* a shape appears, and `LoopElim`'s two properties are
the identity on a loop-free program — where they degenerate into
`stmt: typechecker accepts generated statements`, which is already tested. `dist-report`
measures a loop in 28% of statement lists at the source weights and 76% under
`stmtLoopHeavy`, with a loop inside a loop — where a loop-elimination pass is likeliest
to be wrong — going 3% to 24%. So those two are registered under both weightings, by naming them
in the registration attribute: `@[strata_property (tunings := …)]`. Each row is its own
verdict and its own Tyche panel, and the `[default]` row is exactly the property as
written, since `genWith defaults` is the type's `Arbitrary` instance (pinned by `rfl` in
`StrataGenerators.Test.Generators`).
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.TuningProfiles

/-- The four statement transform / typechecker properties whose default distribution is
    adequate. The two `LoopElim` claims are registered separately, under two weightings. -/
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

/-- `LoopElim` preserves typeability — checked at the source weights *and* at weights
    that make a loop the modal statement, since the claim has no content without one. -/
@[strata_property (tunings := [("default", stmtDefault), ("loop-heavy", stmtLoopHeavy)])]
def loopElimPreservesTyping : TestDecl :=
  .property "stmt: LoopElim preserves typeability"
    fun (gs : GenStmts) => checkLoopElimPreservesTyping gs.stmts

/-- `LoopElim` eliminates every loop. Vacuously true on a loop-free program, so the
    loop-heavy row is the one that carries the claim.

    **Both rows currently FAIL, and the mechanism is not the weights.** `Core.removeLoop`
    throws on a loop that still carries an invariant or a measure, and `loopElimStmts`
    returns the input unchanged when the pass throws (see its docstring), so such a loop
    survives and the count is not zero. Machine-checked, with no generator involved:
    `checkLoopElimZeroLoops [.loop .nondet none [("i", .const () (.boolConst true))] [] .empty]`
    is `false`, while the same loop without the invariant gives `true`. An
    invariant-bearing loop appears in 19% of samples at the source weights and 59% under
    `stmtLoopHeavy`, which is why the loop-heavy row fails faster rather than differently.
    The claim as stated is really "…unless the pass throws"; the fix is upstream (or in the
    property), and this pins it either way. -/
@[strata_property (tunings := [("default", stmtDefault), ("loop-heavy", stmtLoopHeavy)])]
def loopElimZeroLoops : TestDecl :=
  .property "stmt: LoopElim eliminates all loops"
    fun (gs : GenStmts) => checkLoopElimZeroLoops gs.stmts

/-- `StmtToKleeneStmt` is defined exactly when the block has no
    `exit`/`funcDecl`/`typeDecl` — and, for the invariant-loop caveat, not defined
    when an invariant-bearing loop is present. Its panel records the definedness
    verdict *and* why, so it keeps a bespoke one. -/
@[strata_property]
def stmtKleeneDefinedIff : TestDecl :=
  (TestDecl.property "stmt: DetToKleene defined iff supported"
    (fun (gs : GenStmts) => checkKleeneDefinedIff gs.stmts)).withPanel genKleeneDefined
