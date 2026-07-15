module
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Denote.Assumptions
import Std.Data.HashMap.Lemmas

/-!
# `Factory`-internal bridge lemmas for the `OpsConsistent(R)` generator proofs

Both of Strata's op-consistency predicates are now nameable directly from
downstream (non-`module`) proof files: `Lambda.OpsConsistent` is `@[expose] public`
(so it can also be *unfolded*), and the declarative `Lambda.OpsConsistentR` is
`public`, as is the soundness bridge `Lambda.OpsConsistent_OpsConsistentR`. So the
generator proofs need **no local copy** of either predicate.

This module survives only because a few helper lemmas genuinely require a `module`
file that does `import all` on `Factory`/`Assumptions`:

* `mem_get?_eq` — reaches the *private* `Factory.nameMap` internals.
* `opGeneric_opsConsistent` — op-annotation consistency for a generic factory type.
* `unify_self` / `unifyOne_self` — self-unification facts.

These are re-used by the non-`module` op-consistency proofs, which cannot
themselves `import all` (they transitively depend on the non-`module` Basalt
library). (The former `destructArrow`/`mkArrow` reconciliation lemmas are gone:
`factoryOps` now builds each op type with `mkArrow'` directly, so its entries are
*definitionally* the operator's generic type — no arrow-spine bridging needed.)
-/

namespace Lambda
open Lambda

set_option linter.unusedSectionVars false

variable {T : LExprParams} [DecidableEq T.IDMeta]

-- Both `Lambda.OpsConsistent` (operational, `@[expose] public`) and
-- `Lambda.OpsConsistentR` (declarative, `public`) are now nameable — and the former
-- unfoldable — directly from downstream non-`module` proof files, so no local copy
-- of either predicate is needed. The soundness bridge
-- `Lambda.OpsConsistent_OpsConsistentR` is likewise `public`. This file therefore
-- only carries the `Factory`-internal bridge lemmas below (which genuinely require
-- `import all Factory` to reach the private `nameMap`) and the `factoryOps`
-- type-shape lemmas.

-- ── Factory lookup bridge ────────────────────────────────────────────
-- These bridge lemmas need access to the *private* internals of `Factory`
-- (`nameMap`), so they must live in a `module` file that does `import all`
-- on `Factory`. They are re-used by the non-`module` op-consistency proofs.

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

-- ── Self-unification ─────────────────────────────────────────────────

/-- Unifying a constraint of a type with itself leaves the substitution
    unchanged (the `t == t` fast-path in `Constraint.unifyOne`). -/
public theorem unifyOne_self (t : LMonoTy) (S : SubstInfo) :
    ∃ h, Constraint.unifyOne (t, t) S = .ok ⟨S, h⟩ := by
  unfold Constraint.unifyOne
  simp only [beq_self_eq_true, reduceDIte]
  exact ⟨by simp [Subst.freeVars_subset_prop], trivial⟩

/-- Unifying `[(t, t)]` against a substitution `S` returns `S` unchanged. -/
public theorem unify_self (t : LMonoTy) (S : SubstInfo) :
    Constraints.unify [(t, t)] S = .ok S := by
  unfold Constraints.unify Constraints.unifyCore
  simp only [bind, Except.bind, Except.mapError]
  obtain ⟨h, hone⟩ := unifyOne_self t S
  rw [hone]; simp only [Constraints.unifyCore]

-- ── Op-annotation consistency for generic factory types ──────────────

/-- An `.op` node whose annotation is exactly the *generic* factory type of
    `fn` (as produced by `factoryOps`) satisfies `OpsConsistent`. This holds
    for both monomorphic and polymorphic `fn`: in both cases `opTypeSubst`
    unifies the annotation against itself, yielding the empty substitution,
    which fixes the (generic) type. -/
public theorem opGeneric_opsConsistent (F : @Factory T)
    (fn : LFunc T) (m : T.Metadata) (name : T.Identifier)
    (hname : F[name.name]? = some fn) :
    Lambda.OpsConsistent F
      (.op m name (some (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)))) := by
  unfold Lambda.OpsConsistent
  simp only [hname]
  unfold LFunc.opTypeSubst
  by_cases hta : fn.typeArgs.isEmpty
  · simp only [hta, if_true]
    rw [LMonoTy.subst_emptyS (by simp)]
  · simp only [hta, Bool.false_eq_true, if_false]
    rw [← ListMap.values_eq_map_snd, unify_self]
    show fn.output.mkArrow' fn.inputs.values = LMonoTy.subst SubstInfo.empty.subst _
    rw [LMonoTy.subst_emptyS (by simp [SubstInfo.empty])]

-- Note: the operational `opGroundInstance_opsConsistent` (ground-instance op
-- consistency for the *operational* `OpsConsistent`, which needed the
-- ground-matching unification-completeness result `unify_ground_instance`) is no
-- longer required. The generator's polymorphic op annotations are now discharged
-- against the *declarative* `OpsConsistentR`, whose `.op_in` constructor asks only
-- for the existence of an instantiating substitution — the generator builds one by
-- construction, so no `opTypeSubst` round-trip / ground matching is needed.

end Lambda
