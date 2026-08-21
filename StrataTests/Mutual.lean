import StrataGenerators.Test

/-!
# A `mutual … end` block that is not mutually recursive

Strata accepts a block of datatypes that do not refer to one another. Such a block is
usable, and it means the same as a separate declaration for each datatype. These four
properties state that claim.

Each check tests the shape that it needs with `isIndependentBlock`, and it is vacuously true
for another shape. Therefore an ordinary block cannot turn a check into a claim about a
connected block.

The defect that this shape shows is *not* specific to the independent shape: `d$Elim` leaves
the type parameters of another datatype free. Therefore the `adt:` suite holds that
property, over ordinary blocks.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.MutualBlockShape

/-- The four claims about a block whose datatypes are pairwise independent.
    `genIndependentBlock` draws the blocks. It draws each datatype on its own, and it
    threads one set of reserved names through the draws, so no constructor field can mention
    a sibling datatype. -/
@[strata_properties]
def mutualIndepChecks : List TestDecl :=
  family GenIndepBlock
    [ ("mutual: a block of non-mutually-recursive datatypes is accepted",
       fun gb => checkIndependentBlockAccepted gb.block),
      ("mutual: such a block's constructors are usable in a program",
       fun gb => checkIndependentBlockUsable gb.block),
      -- The block and the split form are interchangeable, except for the eliminators. The
      -- eliminators differ by design, because `d$Elim` takes one case function for each
      -- constructor of the *whole* block.
      ("mutual: splitting such a block preserves the derived vocabulary",
       fun gb => checkSplitBlockAgrees gb.block),
      ("mutual: such a block prints without a conversion error",
       fun gb => checkIndependentBlockPrints gb.block) ]
