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
* the `factoryOps` type-shape lemmas (`ArrowSpineOK`, `destructArrow`/`mkArrow`
  reconstruction).

These are re-used by the non-`module` op-consistency proofs, which cannot
themselves `import all` (they transitively depend on the non-`module` Basalt
library).
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

-- ── `factoryOps` type-shape bridge ───────────────────────────────────
-- `factoryOps` assigns each op the curried type
--   `mkArrow ity (irest ++ destructArrow output)`
-- whereas `OpsConsistent` expects the generic type `mkArrow' output values`.
-- These coincide exactly when the output type's arrow spine is well-formed
-- (each `arrow` node has arity 2), captured by `ArrowSpineOK`. Real factory
-- outputs (produced by the parser/type-checker) always satisfy this.

/-- The arrow *spine* of a monotype is well-formed: every `arrow` tycon along
    the right spine has exactly two arguments. This is all that
    `destructArrow`/`mkArrow` reconstruction requires. -/
public def ArrowSpineOK : LMonoTy → Prop
  | .tcons "arrow" [_, b] => ArrowSpineOK b
  | .tcons "arrow" _ => False
  | _ => True

/-- `LMonoTys.destructArrow` of a singleton is `LMonoTy.destructArrow`. -/
public theorem LMonoTys_destructArrow_single (t : LMonoTy) :
    LMonoTys.destructArrow [t] = LMonoTy.destructArrow t := by
  rw [LMonoTys.destructArrow]; simp [LMonoTys.destructArrow]

/-- `destructArrow` of a non-arrow tycon is the singleton list. -/
public theorem destructArrow_non_arrow (nm : String) (args : List LMonoTy)
    (h : nm ≠ "arrow") : LMonoTy.destructArrow (.tcons nm args) = [.tcons nm args] := by
  rw [LMonoTy.destructArrow]
  intro t1 trest heq
  simp only [LMonoTy.tcons.injEq] at heq
  exact absurd heq.1 h

/-- `destructArrow` of a binary arrow peels the domain and recurses. -/
public theorem destructArrow_arrow2 (a b : LMonoTy) :
    LMonoTy.destructArrow (.tcons "arrow" [a, b]) = a :: LMonoTy.destructArrow b := by
  rw [LMonoTy.destructArrow]
  show a :: LMonoTys.destructArrow [b] = _
  rw [LMonoTys_destructArrow_single]

/-- Reconstruction: for a monotype with a well-formed arrow spine,
    `mkArrow x (destructArrow o) = arrow x o`. -/
public theorem mkArrow_destructArrow : (o : LMonoTy) → ArrowSpineOK o → (x : LMonoTy) →
    LMonoTy.mkArrow x (LMonoTy.destructArrow o) = LMonoTy.arrow x o
  | .tcons "arrow" [a, b] => fun hwf x => by
      have hb : ArrowSpineOK b := hwf
      rw [destructArrow_arrow2]
      show LMonoTy.arrow x (LMonoTy.mkArrow a (LMonoTy.destructArrow b)) = _
      rw [mkArrow_destructArrow b hb a]; rfl
  | .ftvar nm => fun _ x => by simp [LMonoTy.destructArrow, LMonoTy.mkArrow]
  | .bitvec n => fun _ x => by simp [LMonoTy.destructArrow, LMonoTy.mkArrow]
  | .tcons "arrow" [] => fun hwf x => absurd hwf (by simp [ArrowSpineOK])
  | .tcons "arrow" [_] => fun hwf x => absurd hwf (by simp [ArrowSpineOK])
  | .tcons "arrow" (_::_::_::_) => fun hwf x => absurd hwf (by simp [ArrowSpineOK])
  | .tcons "bool" args => fun _ x => by rw [destructArrow_non_arrow _ _ (by decide)]; simp [LMonoTy.mkArrow]
  | .tcons "int" args => fun _ x => by rw [destructArrow_non_arrow _ _ (by decide)]; simp [LMonoTy.mkArrow]
  | .tcons "string" args => fun _ x => by rw [destructArrow_non_arrow _ _ (by decide)]; simp [LMonoTy.mkArrow]
  | .tcons "real" args => fun _ x => by rw [destructArrow_non_arrow _ _ (by decide)]; simp [LMonoTy.mkArrow]
  | .tcons "regex" args => fun _ x => by rw [destructArrow_non_arrow _ _ (by decide)]; simp [LMonoTy.mkArrow]
  | .tcons "Map" args => fun _ x => by rw [destructArrow_non_arrow _ _ (by decide)]; simp [LMonoTy.mkArrow]
  | .tcons "Sequence" args => fun _ x => by rw [destructArrow_non_arrow _ _ (by decide)]; simp [LMonoTy.mkArrow]
  | .tcons nm args => fun hwf x => by
      by_cases hnm : nm = "arrow"
      · subst hnm
        match args, hwf with
        | [], hwf => exact absurd hwf (by simp [ArrowSpineOK])
        | [_], hwf => exact absurd hwf (by simp [ArrowSpineOK])
        | [a, b], hwf =>
            have hb : ArrowSpineOK b := hwf
            rw [destructArrow_arrow2]
            show LMonoTy.arrow x (LMonoTy.mkArrow a (LMonoTy.destructArrow b)) = _
            rw [mkArrow_destructArrow b hb a]; rfl
        | (_::_::_::_), hwf => exact absurd hwf (by simp [ArrowSpineOK])
      · rw [destructArrow_non_arrow nm args hnm]; simp [LMonoTy.mkArrow]
  termination_by o => sizeOf o
  decreasing_by all_goals (simp_wf; omega)

end Lambda
