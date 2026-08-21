import StrataGenerators.Test
import StrataGenerators.AdtLawsSmt

/-!
# The two laws of an algebraic datatype: injectivity and disjointness

Each generated `mutual … end` block denotes an initial algebra. Therefore its constructors
must be injective and pairwise disjoint. These are the `injection` and `discriminate`
facts of the `Tactics` chapter of Software Foundations. The claims are **not** about the
generator. They are about *the SMT encoding of a datatype in Strata*, and the oracle is a
real solver that runs through the whole Core pipeline. Uniformness has no property here,
because `addMutualBlock` checks it.

These properties draw blocks at `maxSize := 0`. At a larger size, `genArgTy` emits arrow
types, and `validateDatatypesForSMT` then refuses the whole block because a field has a
function type. Most of the budget would go to blocks that no solver sees. The property
`adt: every emitted law query reaches a solver verdict` uses the larger sizes, because it
wants those refusals.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.AdtLaws
open StrataGenerators.AdtLawsSmt (runLawTallies tallyToNode adtSolverAcceptsQueryAction)

/-- The two pure companions to the law properties that a solver discharges, and the
    property about the scope of an eliminator.

    These properties need no solver, so they run in the default suite. They also keep the
    `--smt` properties honest. The first property says that the law program is well-typed.
    The third property says that the partial evaluator resolves the disjointness assertion
    in constructor form, but not the assertion in tester form. Therefore the solver really
    gets a question about disjointness, and not the literal `true`. -/
@[strata_properties]
def adtBlockChecks : List TestDecl :=
  family GenAdtBlock
    [ -- This screen keeps an ill-typed program away from the solver properties. It is
      -- also a claim on its own: an equality can use a derived constructor at its ground
      -- instance.
      ("adt: the law program typechecks",
       fun gb => checkLawProgramTypeChecks gb.block),
      -- A datatype that has a field `f` and a field `f!` derives the name `d..f!` two
      -- times: once as the safe destructor of `f!`, and once as the unsafe destructor of
      -- `f`. Core then rejects the whole declaration. Both field names are legal Core
      -- identifiers. The collision needs two field names that differ only by a trailing
      -- `!`, and a random draw almost never gives such a pair. Therefore the deterministic
      -- pin is `AdtLaws.bangFieldWitness`, which a `#guard` holds, and this property is
      -- the net around that witness. The property carries no `.knownFailure` mark,
      -- because the mark describes a defect that a draw finds often.
      ("adt: no datatype derives the same function name twice",
       fun gb => checkNoDerivedNameCollisions gb.block),
      -- The partial evaluator decides disjointness in constructor form without a solver.
      -- `symbolicEval` folds `!(C x⃗ == D y⃗)` to the literal `true`. The tester form
      -- `!(isC u && isD u)` reaches the solver. This property asserts both halves, and the
      -- second half guards `adt: constructor disjointness is provable by SMT` against
      -- vacuity.
      ("adt: constructor-form disjointness folds during symbolic evaluation",
       fun gb => checkDisjFoldsDuringSymEval gb.block),
      -- This property is here and not in the `mutual:` suite, because the defect is not
      -- specific to an independent block. `visibleRefs` lets a datatype refer to a
      -- datatype whose parameters are a subset of its own, and the parameter lists in the
      -- block then differ.
      ("mutual: derived functions bind every type variable they mention",
       fun gb => StrataGenerators.MutualBlockShape.checkDerivedFuncsWellScoped gb.block,
       .knownFailure "reported upstream: `elimFuncs` builds `d$Elim`'s case-function \
arguments from every datatype in the block but binds only `d`'s own type parameters, so \
a sibling's parameters occur free") ]

/-- One run of the pipeline for one block gives the obligations of *every* law family.
    Therefore the three properties that need a solver share one computation. A separate
    computation for each property would repeat every solver query and give the same
    coverage.

    Each property is a separate declaration in the registry, so this cache is what lets
    the three properties share one result. -/
private initialize lawTallyCache :
    IO.Ref (Option (StrataGenerators.AdtLawsSmt.Tally × StrataGenerators.AdtLawsSmt.Tally × StrataGenerators.AdtLawsSmt.Tally × List String)) ←
      IO.mkRef none

/-- The law tallies for the current configuration. The first call runs the pipeline and
    fills `lawTallyCache`. Each later call returns the cached result. -/
private def lawTallies (cfg : RunConfig) :
    IO (StrataGenerators.AdtLawsSmt.Tally × StrataGenerators.AdtLawsSmt.Tally × StrataGenerators.AdtLawsSmt.Tally × List String) := do
  match ← lawTallyCache.get with
  | some t => pure t
  | none =>
    let t ← runLawTallies cfg.numTrials StrataGenerators.SmtEval.solverName
    lawTallyCache.set (some t)
    pure t

/-- Each constructor of a generated block is injective at the `int` instance of the block.
    The `blockIsSmtSafe` screen selects the blocks. The `--smt` gate controls the
    property. -/
@[strata_property]
def adtInjSmt : TestDecl :=
  TestDecl.action "adt: constructor injectivity is provable by SMT"
    (fun cfg => do
      let (inj, _, _, notes) ← lawTallies cfg
      pure (ActionResult.ofTuple (tallyToNode "injectivity" inj notes)))
    (gate := some "smt")

/-- The constructors of a generated block are pairwise disjoint in the **tester** form,
    which is the form that reaches the solver. The `--smt` gate controls the property. -/
@[strata_property]
def adtDisjSmt : TestDecl :=
  TestDecl.action "adt: constructor disjointness is provable by SMT"
    (fun cfg => do
      let (_, disjT, _, notes) ← lawTallies cfg
      pure (ActionResult.ofTuple
        (tallyToNode "disjointness (tester form)" disjT notes)))
    (gate := some "smt")

/-- Each law query that Strata emits reaches a *verdict* from the solver. No screen
    removes a block first, and this is the difference from the properties for injectivity
    and disjointness.

    Two separate defects break this property, and a legal Core datatype causes each one:

    1. A `bitvec 0` field becomes `(_ BitVec 0)`. SMT-LIB 2.6 needs a positive index, so
       cvc5 reports `Illegal bitvector size: 0` and z3 reports `bit-vector size must be
       greater than zero`.
    2. A name that is not a bare SMT-LIB symbol goes into `declare-datatype` without a
       change. Such a name holds a `'` character, or it is an SMT-LIB reserved word such as
       `_`. Where the *same* name occurs in a field type, pipes quote it, as in
       `(par (vx' NK) (… (U |vx'| NK) …))`.

    Hand-built witnesses and generated blocks both pin the two defects. The `--smt` gate
    controls the property. -/
@[strata_property]
def adtSolverAcceptsQuery : TestDecl :=
  knownFailure "reported upstream: (1) a `bitvec 0` field is emitted as `(_ BitVec 0)`, \
whose index SMT-LIB 2.6 requires to be positive; (2) a name that is not a bare SMT-LIB \
symbol is interpolated verbatim into `declare-datatype`" <|
    TestDecl.action "adt: every emitted law query reaches a solver verdict"
      (fun cfg => ActionResult.ofTuple <$>
        adtSolverAcceptsQueryAction cfg.numTrials StrataGenerators.SmtEval.solverName)
      (gate := some "smt")
