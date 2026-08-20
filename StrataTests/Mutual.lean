import StrataGenerators.Test

/-!
# `mutual … end` blocks that are not mutually recursive

A block of datatypes that do not refer to one another at all is accepted, is usable,
and means the same as declaring each datatype separately. All four properties pass —
which is the answer to the question the suite was written to ask.

Each check re-verifies the shape it needs (`isIndependentBlock`) and is vacuously true
otherwise, so feeding it an ordinary block cannot silently turn it into a claim about
connected blocks.

The defect this shape exposes — `d$Elim` leaving another datatype's type parameters
free — is *not* specific to the independent shape, so it is registered with the `adt:`
suite over ordinary blocks instead.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.MutualBlockShape

/-- The four claims about a block whose datatypes are pairwise independent, scored on
    blocks drawn by `genIndependentBlock`: datatypes drawn independently over a
    threaded reserved-name set, so no constructor field can mention a sibling. -/
@[strata_properties]
def mutualIndepChecks : List TestDecl :=
  family GenIndepBlock
    [ ("mutual: a block of non-mutually-recursive datatypes is accepted",
       fun gb => checkIndependentBlockAccepted gb.block),
      ("mutual: such a block's constructors are usable in a program",
       fun gb => checkIndependentBlockUsable gb.block),
      -- Interchangeability with the split form, up to the eliminators — which differ
      -- by design, since `d$Elim` takes a case function per constructor of the *whole*
      -- block.
      ("mutual: splitting such a block preserves the derived vocabulary",
       fun gb => checkSplitBlockAgrees gb.block),
      ("mutual: such a block prints without a conversion error",
       fun gb => checkIndependentBlockPrints gb.block) ]
