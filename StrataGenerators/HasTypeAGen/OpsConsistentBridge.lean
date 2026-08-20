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

This module survives for two lemmas that reach into `Factory`'s module-private surface and
therefore must live in a `module` file that does `import all Factory`. The non-`module`
op-consistency proof file cannot `import all` itself (it transitively depends on the
non-`module` Basalt library), so it reuses both from here:

* `mem_get?_eq`, which reaches the *private* `Factory.nameMap` internals;
* `Factory.memNameGetElem`, a re-export of Strata's `Factory.mem_name_eq_getElem`. That
  theorem lives in `Strata.DL.Lambda.FactoryProps`, whose declarations are not `public`
  under Strata's module system, so it cannot be named from a plain import.
-/

namespace Lambda
open Lambda

set_option linter.unusedSectionVars false

variable {T : LExprParams} [DecidableEq T.IDMeta]

-- ── Factory lookup bridge ────────────────────────────────────────────

/-- Public re-export of `Factory.mem_name_eq_getElem`: if `fn ∈ F.toArray` and
    `fn.name.name = s`, then `s ∈ F` and `F[s] = fn`. -/
public theorem Factory.memNameGetElem {F : @Factory T} {fn : LFunc T} {s : String}
    (hmem : fn ∈ F.toArray) (hname : fn.name.name = s) :
    ∃ (hs : s ∈ F), F[s]'hs = fn :=
  Factory.mem_name_eq_getElem hmem hname

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
