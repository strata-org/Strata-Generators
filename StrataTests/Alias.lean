import StrataGenerators.Test

/-!
# Eager and incremental resolution of a type alias

Strata resolves a type alias *during* type checking, one declaration at a time. These two
properties say that this order gives the same result as the expansion of every alias before
type checking. An alias is therefore the transparent abbreviation that the documents
describe.

The properties need help to stay away from vacuity. `ProgramGen` emits alias declarations
that nothing *uses*, because `Inv.aliasVocabDisjoint` keeps the type vocabulary disjoint
from the alias names. Resolution on such a draw is the identity function. Therefore
`introduceAlias` *adds* a use: it makes an alias for a ground type that the program
mentions, and it rewrites each occurrence of that type.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.AliasResolution

/-- The two properties for alias resolution. They use the same input shape as the
    `program:` suite, so the whole-program shrinker reduces a counterexample. -/
@[strata_properties]
def aliasChecks : List TestDecl :=
  family GenProgram
    [ ("alias: eager and incremental resolution agree on acceptance",
       fun gp => checkAliasAcceptanceAgrees gp.prog),
      -- The second half: the two orders of resolution give the same proof obligations
      -- under the symbolic evaluator of Strata.
      ("alias: eager and incremental resolution give the same obligations",
       fun gp => checkAliasObligationsAgree gp.prog) ]
