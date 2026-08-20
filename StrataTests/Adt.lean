import StrataGenerators.Test
import StrataGenerators.AdtLawsSmt

/-!
# The two laws of an algebraic datatype: injectivity and disjointness

Every generated `mutual … end` block denotes an initial algebra, so its constructors
must be injective and pairwise disjoint — the `injection` and `discriminate` facts of
Software Foundations' `Tactics` chapter. The claims are **not** about the generator:
they are about *Strata's SMT encoding of a datatype*, and the oracle is a real solver
run through the whole Core pipeline. Uniformness is deliberately not covered
(`addMutualBlock` already checks it).

Blocks are drawn at `maxSize := 0`. At a larger size `genArgTy` emits arrows and
`validateDatatypesForSMT` refuses a function-typed field for the whole block, so the
arrow-free fraction falls from 40/40 to about 5/40 — three quarters of the budget
would go to blocks no solver ever sees. The larger sizes are exercised where they are
the point, in `adt: every emitted law query reaches a solver verdict`, which *wants*
the refusals.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.AdtLaws
open StrataGenerators.AdtLawsSmt (runLawTallies tallyToNode adtSolverAcceptsQueryAction)

/-- The two pure companions to the solver-backed law properties, plus the
    eliminator-scoping property.

    They need no solver, so they run in the default suite, and they are what keeps the
    `--smt` properties honest: the first says the law program is well-typed, and the
    third says the constructor-form disjointness assertion is resolved by the partial
    evaluator *while the tester form is not* — i.e. that the solver is genuinely asked
    about disjointness rather than handed a `true`. -/
@[strata_properties]
def adtBlockChecks : List TestDecl :=
  family GenAdtBlock
    [ -- The screen that keeps the solver properties from being fed an ill-typed
      -- program, and a claim in its own right: a derived constructor is usable in an
      -- equality at its ground instance. Holds on every block Strata accepts.
      ("adt: the law program typechecks",
       fun gb => checkLawProgramTypeChecks gb.block),
      -- FAILS honestly, but only on a rare draw. A datatype with a field `f` *and* a
      -- field `f!` derives the name `d..f!` twice — once as `f!`'s safe destructor,
      -- once as `f`'s unsafe one — and the whole declaration is then rejected. Both
      -- field names are legal Core identifiers. The collision needs two field names
      -- differing by exactly a trailing `!`, which a random draw almost never produces
      -- (0 in a sweep of 400 blocks; it fired once across several `--quick` runs), so
      -- the deterministic pin is the `#guard`ed `AdtLaws.bangFieldWitness` and this
      -- property is the regression net around it. Reported upstream.
      -- Marked `rareFailure` and not `knownFailure` precisely because of the frequency
      -- above: it holds on nearly every run, so `knownFailure` would fail the suite
      -- almost always. This gates in neither direction.
      ("adt: no datatype derives the same function name twice",
       fun gb => checkNoDerivedNameCollisions gb.block,
       .rareFailure "reported upstream: a field `f` alongside a field `f!` derives \
`d..f!` twice; needs two field names differing by exactly a trailing `!`, so a draw \
almost never produces it"),
      -- The partial evaluator decides constructor-form disjointness by itself:
      -- `!(C x⃗ == D y⃗)` folds to the literal `true` during `symbolicEval`, while the
      -- tester form `!(isC u && isD u)` survives to the solver. Both halves are
      -- asserted — the second is the non-vacuity guard for `adt: constructor
      -- disjointness is provable by SMT`.
      ("adt: constructor-form disjointness folds during symbolic evaluation",
       fun gb => checkDisjFoldsDuringSymEval gb.block),
      -- FAILS honestly (28 of 60 ordinary generated blocks). Lives here rather than in
      -- the `mutual:` suite because the defect is not specific to an independent
      -- block: `visibleRefs` lets a datatype refer to one whose parameters are a
      -- subset of its own, and the block's parameter lists then differ.
      ("mutual: derived functions bind every type variable they mention",
       fun gb => StrataGenerators.MutualBlockShape.checkDerivedFuncsWellScoped gb.block,
       .knownFailure "reported upstream: `elimFuncs` builds `d$Elim`'s case-function \
arguments from every datatype in the block but binds only `d`'s own type parameters, so \
a sibling's parameters occur free") ]

/-- One run of the pipeline per block yields the obligations of *every* law family at
    once, so the three solver-backed properties share a single computation. Computing
    them per property would run every solver query twice for identical coverage.

    The cache is what makes the sharing possible now that each property is a separate
    registered declaration rather than three nodes assembled in one place. -/
private initialize lawTallyCache :
    IO.Ref (Option (StrataGenerators.AdtLawsSmt.Tally × StrataGenerators.AdtLawsSmt.Tally × StrataGenerators.AdtLawsSmt.Tally × List String)) ←
      IO.mkRef none

private def lawTallies (cfg : RunConfig) :
    IO (StrataGenerators.AdtLawsSmt.Tally × StrataGenerators.AdtLawsSmt.Tally × StrataGenerators.AdtLawsSmt.Tally × List String) := do
  match ← lawTallyCache.get with
  | some t => pure t
  | none =>
    let t ← runLawTallies cfg.numTrials StrataGenerators.SmtEval.solverName
    lawTallyCache.set (some t)
    pure t

/-- Injectivity of every constructor of a generated block, at the block's `int`
    instance. PASSES (74/74 obligations at cvc5, 75/75 at z3, on the `blockIsSmtSafe`
    screen). Gated on `--smt`. -/
@[strata_property]
def adtInjSmt : TestDecl :=
  TestDecl.action "adt: constructor injectivity is provable by SMT"
    (fun cfg => do
      let (inj, _, _, notes) ← lawTallies cfg
      pure (ActionResult.ofTuple (tallyToNode "injectivity" inj notes)))
    (gate := some "smt")

/-- Disjointness in the **tester** form, which is the form that reaches the solver.
    PASSES (45/45 at cvc5, 53/53 at z3). Gated on `--smt`. -/
@[strata_property]
def adtDisjSmt : TestDecl :=
  TestDecl.action "adt: constructor disjointness is provable by SMT"
    (fun cfg => do
      let (_, disjT, _, notes) ← lawTallies cfg
      pure (ActionResult.ofTuple
        (tallyToNode "disjointness (tester form)" disjT notes)))
    (gate := some "smt")

/-- **FAILS honestly.** The unscreened counterpart of the two above: every emitted law
    query must reach a solver *verdict*. Two independent defects make it red, both from
    legal Core datatypes:

    1. a `bitvec 0` field is emitted as `(_ BitVec 0)`, whose index SMT-LIB 2.6
       requires to be positive (cvc5 `Illegal bitvector size: 0`, z3 `bit-vector size
       must be greater than zero`);
    2. a name that is not a bare SMT-LIB symbol — one containing `'`, or one that is an
       SMT-LIB reserved word such as `_` — is interpolated verbatim into
       `declare-datatype`, while the *same* name is pipe-quoted where it occurs in a
       field type (`(par (vx' NK) (… (U |vx'| NK) …))`).

    Both are reported upstream, and pinned by hand-built witnesses as well as by
    generated blocks. Gated on `--smt`. -/
@[strata_property]
def adtSolverAcceptsQuery : TestDecl :=
  knownFailure "reported upstream: (1) a `bitvec 0` field is emitted as `(_ BitVec 0)`, \
whose index SMT-LIB 2.6 requires to be positive; (2) a name that is not a bare SMT-LIB \
symbol is interpolated verbatim into `declare-datatype`" <|
    TestDecl.action "adt: every emitted law query reaches a solver verdict"
      (fun cfg => ActionResult.ofTuple <$>
        adtSolverAcceptsQueryAction cfg.numTrials StrataGenerators.SmtEval.solverName)
      (gate := some "smt")
