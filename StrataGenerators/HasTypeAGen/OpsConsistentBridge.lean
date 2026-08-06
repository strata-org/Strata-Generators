module
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import Std.Data.HashMap.Lemmas

/-!
# `Factory`-internal bridge lemma for the `OpsConsistent(R)` generator proofs

Both of Strata's op-consistency predicates are nameable directly from downstream
(non-`module`) proof files: `Lambda.OpsConsistent` is `@[expose] public`,
`Lambda.OpsConsistentR` is `public`, and the soundness bridge
`Lambda.OpsConsistent_OpsConsistentR` is `public`. So the generator proofs need
**no local copy** of either predicate, and — since the traversal is proven
directly against the declarative `OpsConsistentR` via its constructors — no
operational-unfolding or self-unification helpers either.

This module survives only for `mem_get?_eq`, which reaches the *private*
`Factory.nameMap` internals and therefore must live in a `module` file that does
`import all Factory`. The non-`module` op-consistency proof file cannot `import all`
itself (it transitively depends on the non-`module` Basalt library), so it reuses
this one lemma from here.
-/

namespace Lambda
open Lambda

set_option linter.unusedSectionVars false

variable {T : LExprParams} [DecidableEq T.IDMeta]

-- ── Factory lookup bridge ────────────────────────────────────────────

/-- Membership plus a total lookup determines the partial lookup: if `s ∈ F`
    and `F[s] = fn`, then `F[s]? = some fn`. -/
public theorem mem_get?_eq {F : @Factory T} {s : String} {fn : LFunc T}
    (hs : s ∈ F) (hget : F[s]'hs = fn) : F[s]? = some fn := by
  cases h : F[s]? with
  | none =>
    exfalso
    have hmem : s ∈ F.nameMap := hs
    change Factory.get? F s = none at h
    unfold Factory.get? at h
    split at h
    · rename_i heq
      rw [Std.HashMap.mem_iff_contains] at hmem
      simp [Std.HashMap.contains_eq_isSome_getElem?, heq] at hmem
    · exact absurd h (by simp)
  | some fn' =>
    have h1 := Factory.getElem?_some_getElem h
    rw [← hget]; congr 1; grind

end Lambda
