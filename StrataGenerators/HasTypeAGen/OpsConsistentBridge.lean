module
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import Std.Data.HashMap.Lemmas

/-!
# The two lemmas about the inside of a `Factory`, for the op-consistency proofs

A proof file that is not a module can name both op-consistency predicates of Strata directly.
`Lambda.OpsConsistent` is `@[expose] public`, `Lambda.OpsConsistentR` is `public`, and the
bridge for soundness, `Lambda.OpsConsistent_OpsConsistentR`, is also `public`. The proofs for
the generator therefore need **no copy** of either predicate. The proof about the traversal
also goes through the constructors of the declarative `OpsConsistentR`, so it needs no lemma
that unfolds the operational form and no lemma that unifies a type with itself.

This module holds two lemmas that reach the parts of `Factory` that its own module keeps
private. Such a lemma must be in a `module` file that does `import all Factory`. The proof
file for op-consistency is not a module and cannot use `import all`, because it depends on
the Basalt library, which is also not a module. That file therefore uses both lemmas from
here:

* `mem_get?_eq`, which reaches the *private* internals of `Factory.nameMap`;
* `Factory.memNameGetElem`, which exports `Factory.mem_name_eq_getElem` of Strata again. That
  theorem is in a module whose declarations are not `public` under the module system of
  Strata, so a plain import cannot name it.
-/

namespace Lambda
open Lambda

set_option linter.unusedSectionVars false

variable {T : LExprParams} [DecidableEq T.IDMeta]

-- ── The lemmas for a lookup in a `Factory` ──────────────────────────

/-- A public export of `Factory.mem_name_eq_getElem`. If `F.toArray` holds `fn` and the name of `fn`
    is `s`, then `F` holds `s` and `F[s]` is `fn`. -/
public theorem Factory.memNameGetElem {F : @Factory T} {fn : LFunc T} {s : String}
    (hmem : fn ∈ F.toArray) (hname : fn.name.name = s) :
    ∃ (hs : s ∈ F), F[s]'hs = fn :=
  Factory.mem_name_eq_getElem hmem hname

/-- Membership and a total lookup give the partial lookup. If `F` holds `s` and `F[s]` is `fn`, then
    `F[s]?` is `some fn`. -/
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
