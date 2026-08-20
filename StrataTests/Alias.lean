import StrataGenerators.Test

/-!
# Eager versus incremental type-alias resolution

Strata resolves a type alias *during* type checking, one declaration at a time. These
two properties say that this is equivalent to expanding every alias up front — that an
alias is the transparent abbreviation it is documented to be. Both pass.

Non-vacuity needed work: `ProgramGen` emits alias declarations that nothing ever
*uses* (`Inv.aliasVocabDisjoint` keeps the type vocabulary disjoint from the alias
names), so resolution on a raw draw is the identity. `introduceAlias` therefore *adds*
a use — it aliases a ground type the program mentions and rewrites every occurrence —
measured introducible on 29/30 draws.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.AliasResolution

/-- The two alias-resolution properties. Same input shape as the `program:` suite, so
    counterexamples go through the whole-program shrinker. -/
@[strata_properties]
def aliasChecks : List TestDecl :=
  family "alias"
    [ ("alias: eager and incremental resolution agree on acceptance",
       fun (gp : GenProgram) => checkAliasAcceptanceAgrees gp.prog),
      -- The "evaluates the same" half: the two resolution orders give the same proof
      -- obligations under Strata's own symbolic evaluator.
      ("alias: eager and incremental resolution give the same obligations",
       fun gp => checkAliasObligationsAgree gp.prog) ]
