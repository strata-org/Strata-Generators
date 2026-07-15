module
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Denote.Assumptions
import Std.Data.HashMap.Lemmas

/-!
# A public, reasoning-friendly copy of Strata's `OpsConsistent`

Strata defines `Lambda.OpsConsistent` inside a *private* (non-`public`) section of
`Strata/DL/Lambda/Denote/Assumptions.lean`. Because of Lean's module system, that
symbol is only nameable from a `module` file that does `import all` on
`Assumptions` — and such a file cannot, in turn, import the (non-`module`)
generator definitions in `HasTypeAGen/Core.lean` (they transitively depend on the
non-`module` Basalt library).

To let the generator soundness proofs reason about `OpsConsistent`, we mirror its
definition here as `GenOpsConsistent`, marked `@[expose] public` so it is usable
from the non-`module` proof files. The `faithful` theorem below is machine-checked
at build time and certifies that `GenOpsConsistent` is *definitionally identical*
to Strata's `Lambda.OpsConsistent`.
-/

namespace Lambda
open Lambda

set_option linter.unusedSectionVars false

variable {T : LExprParams} [DecidableEq T.IDMeta]

/-- A faithful, `@[expose] public` copy of `Lambda.OpsConsistent` (see module
    docstring). Certified equal to the original by `GenOpsConsistent.faithful`. -/
@[expose] public def GenOpsConsistent (F : @Factory T) : LExpr T.mono → Prop := fun e =>
  match e with
  | .op _ name ty =>
      match F[name.name]? with
      | some fn =>
          match LFunc.opTypeSubst fn e with
          | some tySubst =>
              match ty with
              | some ty_op => ty_op = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst tySubst
              | none => False
          | none => False
      | none => True
  | .app _ fn arg => GenOpsConsistent F fn ∧ GenOpsConsistent F arg
  | .abs _ _ _ body => GenOpsConsistent F body
  | .ite _ c t f => GenOpsConsistent F c ∧ GenOpsConsistent F t ∧ GenOpsConsistent F f
  | .eq _ e1 e2 => GenOpsConsistent F e1 ∧ GenOpsConsistent F e2
  | .quant _ _ _ _ tr body => GenOpsConsistent F tr ∧ GenOpsConsistent F body
  | _ => True

set_option linter.unusedSectionVars false in
/-- **Faithfulness**: `GenOpsConsistent` is definitionally identical to Strata's
    `Lambda.OpsConsistent`. Checked at build time. (Cannot be `public` because it
    mentions the private `Lambda.OpsConsistent`, but this build-time check is what
    licenses reading `GenOpsConsistent`-based results as results about the real
    predicate.) -/
theorem GenOpsConsistent.faithful (F : @Factory T) (e : LExpr T.mono) :
    GenOpsConsistent F e = Lambda.OpsConsistent F e := by
  induction e with
  | op m o ty => rfl
  | app m fn arg ihf iha => unfold GenOpsConsistent Lambda.OpsConsistent; rw [ihf, iha]
  | abs m n aty body ih => unfold GenOpsConsistent Lambda.OpsConsistent; rw [ih]
  | ite m c t f ihc iht ihf => unfold GenOpsConsistent Lambda.OpsConsistent; rw [ihc, iht, ihf]
  | eq m e1 e2 ih1 ih2 => unfold GenOpsConsistent Lambda.OpsConsistent; rw [ih1, ih2]
  | quant m k n qty tr body ihtr ihbody => unfold GenOpsConsistent Lambda.OpsConsistent; rw [ihtr, ihbody]
  | const => rfl
  | bvar => rfl
  | fvar => rfl

-- ── Declarative `OpsConsistentR` copy ────────────────────────────────
-- Strata's `Lambda.OpsConsistentR` (the *inductive*, declarative specification of
-- `OpsConsistent`) also lives in the non-`public` section of `Assumptions.lean`,
-- so it is not nameable from the non-`module` proof files either. We mirror it
-- here as `GenOpsConsistentR`, marked `@[expose] public`, and certify it
-- equivalent to the original by `GenOpsConsistentR.faithful` below.
--
-- Unlike the operational `GenOpsConsistent`, the `.op_in` case demands only the
-- *existence* of a type substitution turning the function's generic type into the
-- node's annotation — it never mentions `opTypeSubst`/unification. That is exactly
-- what makes the generator's polymorphic op annotations consistent by
-- construction (they are built as such an instance), with no need for the
-- ground-matching unification-completeness machinery.

/-- A faithful, `@[expose] public` copy of `Lambda.OpsConsistentR` (see comment
    above). Certified equivalent to the original by `GenOpsConsistentR.faithful`. -/
public inductive GenOpsConsistentR (F : @Factory T) : LExpr T.mono → Prop where
  | const {m c} : GenOpsConsistentR F (.const m c)
  | bvar {m i} : GenOpsConsistentR F (.bvar m i)
  | fvar {m name ty} : GenOpsConsistentR F (.fvar m name ty)
  /-- An operator whose name is not in the factory is unconstrained. -/
  | op_notin {m name ty} (h : F[name.name]? = none) : GenOpsConsistentR F (.op m name ty)
  /-- An operator in the factory must be annotated with some instantiation of the
  function's generic type. -/
  | op_in {m name ty_op fn tySubst}
      (hfn : F[name.name]? = some fn)
      (hty : ty_op = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst tySubst) :
      GenOpsConsistentR F (.op m name (some ty_op))
  | app {m fn arg} :
      GenOpsConsistentR F fn → GenOpsConsistentR F arg → GenOpsConsistentR F (.app m fn arg)
  | abs {m name ty body} : GenOpsConsistentR F body → GenOpsConsistentR F (.abs m name ty body)
  | ite {m c t f} :
      GenOpsConsistentR F c → GenOpsConsistentR F t → GenOpsConsistentR F f →
      GenOpsConsistentR F (.ite m c t f)
  | eq {m e1 e2} :
      GenOpsConsistentR F e1 → GenOpsConsistentR F e2 → GenOpsConsistentR F (.eq m e1 e2)
  | quant {m k name ty tr body} :
      GenOpsConsistentR F tr → GenOpsConsistentR F body →
      GenOpsConsistentR F (.quant m k name ty tr body)

set_option linter.unusedSectionVars false in
/-- **Faithfulness**: `GenOpsConsistentR` is equivalent to Strata's
    `Lambda.OpsConsistentR`. Checked at build time. (Cannot be `public` because it
    mentions the private `Lambda.OpsConsistentR`, but this build-time check is what
    licenses reading `GenOpsConsistentR`-based results as results about the real
    predicate.) -/
theorem GenOpsConsistentR.faithful (F : @Factory T) (e : LExpr T.mono) :
    GenOpsConsistentR F e ↔ Lambda.OpsConsistentR F e := by
  constructor
  · intro h
    induction h with
    | const => exact .const
    | bvar => exact .bvar
    | fvar => exact .fvar
    | op_notin hn => exact .op_notin hn
    | op_in hfn hty => exact .op_in hfn hty
    | app _ _ ihf iha => exact .app ihf iha
    | abs _ ih => exact .abs ih
    | ite _ _ _ ihc iht ihf => exact .ite ihc iht ihf
    | eq _ _ ih1 ih2 => exact .eq ih1 ih2
    | quant _ _ ihtr ihbody => exact .quant ihtr ihbody
  · intro h
    induction h with
    | const => exact .const
    | bvar => exact .bvar
    | fvar => exact .fvar
    | op_notin hn => exact .op_notin hn
    | op_in hfn hty => exact .op_in hfn hty
    | app _ _ ihf iha => exact .app ihf iha
    | abs _ ih => exact .abs ih
    | ite _ _ _ ihc iht ihf => exact .ite ihc iht ihf
    | eq _ _ ih1 ih2 => exact .eq ih1 ih2
    | quant _ _ ihtr ihbody => exact .quant ihtr ihbody

/-- **Soundness bridge (operational ⇒ declarative), on the public copies.**
    `GenOpsConsistent F e → GenOpsConsistentR F e`. This lets the existing
    operational-consistency lemmas (leaf ops, monomorphic Indir) be reused
    verbatim and then bridged into the declarative relation. Proven by routing
    through Strata's own `OpsConsistent_OpsConsistentR` via the two `faithful`
    theorems. -/
public theorem GenOpsConsistent.toR (F : @Factory T) (e : LExpr T.mono)
    (h : GenOpsConsistent F e) : GenOpsConsistentR F e := by
  rw [GenOpsConsistentR.faithful]
  rw [GenOpsConsistent.faithful] at h
  exact Lambda.OpsConsistent_OpsConsistentR h

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
    `fn` (as produced by `factoryOps`) satisfies `GenOpsConsistent`. This holds
    for both monomorphic and polymorphic `fn`: in both cases `opTypeSubst`
    unifies the annotation against itself, yielding the empty substitution,
    which fixes the (generic) type. -/
public theorem opGeneric_opsConsistent (F : @Factory T)
    (fn : LFunc T) (m : T.Metadata) (name : T.Identifier)
    (hname : F[name.name]? = some fn) :
    GenOpsConsistent F
      (.op m name (some (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)))) := by
  unfold GenOpsConsistent
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
