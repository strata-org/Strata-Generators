/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.SetGen
import Basalt.Tuning.Attr

open RandomChoice
open scoped SetGen.Set

/-!
# `@[tunable]` on `Set`-based generators

This file is the counterpart of Basalt's `BasaltTest/Tuning.lean`, run against the `SetGen.Set`
interpretation rather than against `SPMF`. The `@[tunable]` attribute and the `Tuning` data are generic
over `[Gen G]`, and `SetGen.Set` is a `Gen`, so the attribute applies unchanged. Seven sections check
that:

1. `genTree.tuned genTree.defaults` and `genTree` are interchangeable. `tuned_defaults` is `Eq.refl`
   and the kernel checks it, so a generator's existing `SetGen` support proofs compile unchanged.
2. `sites` reports each site's name, offset and arity, and the recursive calls of each branch.
3. `defaults` holds the literal weights from the source.
4. Elaboration rejects a literal `0` weight, and `Tuning.weight` clamps a `0` in a *runtime* `θ` to 1.
5. **Every `θ` denotes the same set.** At `SetGen.Set`, `genFoo.tuned θ = genFoo` for every `θ`. These
   are equal generators and not merely generators with equal supports, because `SetGen.support` is the
   identity. Any soundness or completeness property of the untuned generator therefore holds of every
   tuning of it, with no work per property.
6. Structural, well-founded and `partial_fixpoint` recursion are all tunable, because `@[tunable]`
   rewrites the elaborated body and so does not constrain how the generator recurses.
7. A site reads its depth from a binder named `depth`, or from the binder that
   `@[tunable (depth := …)]` names.

The `SPMF` version also compares distributions, with `#genstats`, `p50` and head-constructor splits.
Those sections have no counterpart here, because `SetGen.Set` tracks *reachability* alone rather than
probabilities, and is noncomputable. Section 5 is what tuning buys on the `Set` side: a reweighting
never changes the support, so a generator's soundness and completeness survive any `θ`.
-/

namespace SetGenTunableExamples

/-- A tiny binary tree, standing in for `BasaltExamples.BST.Tree`. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree
deriving Repr, DecidableEq

/-! ## A depth-indexed tunable generator

This mirrors `genTree` in `BasaltTest/Tuning.lean`. It has an explicit `depth` binder, so each site
reads its weights at that depth. -/

@[tunable]
def genTree [Gen G] (depth : Nat) : G Tree :=
  frequency [
    (1, fun _ => pure .leaf),
    (2, fun _ => do
      let l ← genTree (depth + 1)
      let r ← genTree (depth + 1)
      return .node l r)
  ] (by simp)
partial_fixpoint

/-! ## 1. The defaults are the generator as written

The attribute emits `tuned_defaults`, and it holds definitionally at `SetGen.Set` as it does at
`SPMF`. -/

example (depth : Nat) :
    (genTree.tuned genTree.defaults depth : SetGen.Set Tree) = genTree depth :=
  genTree.tuned_defaults depth

/-- A support fact about the untuned generator transfers to the default-tuned form by one rewrite, so
    tuning does not change an existing `SetGen` proof. -/
example (depth : Nat) (t : Tree) :
    t ∈ SetGen.support (genTree.tuned genTree.defaults depth : SetGen.Set Tree) ↔
      t ∈ SetGen.support (genTree depth : SetGen.Set Tree) := by
  rw [genTree.tuned_defaults]

/-! ## 2. The site table

The attribute names a site by its position, as `<defName>.site<i>`, outside-in in traversal order. -/

example : genTree.sites = #[⟨`SetGenTunableExamples.genTree.site0, 0, 2, #[0, 2]⟩] := rfl

/-! ## 3. The defaults are the literal weights from the source. -/

example : genTree.defaults = ⟨#[(1, 0), (2, 0)]⟩ := rfl

/-! ## 4. A zero weight is rejected at elaboration -/

/--
error: tunable: a literal weight of 0 is rejected: a zero weight removes its branch from the generator's support (see `SPMF.support_frequency`), breaking support-completeness (`IsSoundAndComplete`). To prune a branch, remove it from the source instead.
-/
#guard_msgs in
@[tunable]
def genZero [Gen G] : G Nat := do
  frequency [
    (0, fun _ => pure 0),
    (1, fun _ => pure 1)
  ] (by simp)

/-! A zero entry in a *runtime* `θ` cannot break the support either. `Tuning.weight` clamps it, so it
reads as the weight 1 and the generator stays total in `θ`, as on the `SPMF` side. -/

example (i d : Nat) :
    Tuning.weight ⟨#[(0, 0), (0, 0)]⟩ i d = Tuning.weight ⟨#[(1, 0), (1, 0)]⟩ i d := by
  simp only [Tuning.weight]
  rcases i with _ | _ | i <;> simp

/-! ## 5. Every `θ` denotes the same generator

This section has no `SPMF` counterpart, and it is the reason to interpret a tuned generator at `Set`
at all. `Set` ignores weights, so `genFoo.tuned θ` and `genFoo` are *the same set-valued generator* for
every `θ`. They are literally equal, and not merely equal in support up to a lemma. Every existing
result about the untuned generator therefore applies to the tuned one by `rw`.

For a `partial_fixpoint` generator, both sides are `Lean.Order.fix` over functionals that differ only
in their `frequency` weights. `@[tunable]` binds `θ` outside the fix and re-proves monotonicity.
`SetGen.fix_congr` reduces the goal to equality of those functionals, and
`SetGen.frequency_congr_weights` closes it.

The `unseal` is needed because `partial_fixpoint` definitions are irreducible, and `@[tunable]`
deliberately copies that status onto `.tuned` so that `simp`/`rw` behave the same on both. -/

unseal genTree genTree.tuned

theorem genTree_tuned_eq (θ : Tuning) :
    (genTree.tuned θ : Nat → SetGen.Set Tree) = genTree := by
  apply SetGen.fix_congr
  funext f depth
  apply SetGen.frequency_congr_weights
  · rfl
  all_goals simp [Tuning.weight_pos]

/-- The consequence for the support, at any `θ` and any depth: the tuned generator loses no reachable
    tree and gains none. -/
example (θ : Tuning) (depth : Nat) :
    SetGen.support (genTree.tuned θ depth : SetGen.Set Tree) =
      SetGen.support (genTree depth : SetGen.Set Tree) := by
  rw [genTree_tuned_eq]

/-- The consequence at the level of a property: every tuning of `genTree` is sound and complete for
    *whatever* predicate `genTree` is sound and complete for. The proof does not need to know what `P`
    is, and that is the whole point of the equality of generators. -/
example (θ : Tuning) (depth : Nat) (P : Tree → Prop)
    (h : SetGen.IsSoundAndComplete (genTree depth : SetGen.Set Tree) P) :
    SetGen.IsSoundAndComplete (genTree.tuned θ depth : SetGen.Set Tree) P :=
  SetGen.IsSoundAndComplete.of_support_eq (by rw [genTree_tuned_eq]) h

/-! ## 6. A *tunable* option split via `weightedOptionGen`

Basalt's `optionGen` and `biasedOptionGen` decide the `some` or `none` split with a rational `coin`. A
coin is not a `frequency` site, so `@[tunable]` cannot address it. `SetGen.weightedOptionGen` splits on
a `frequency` over two `Nat` weights instead. A generator that inlines that split under `@[tunable]`
therefore records a site, and a `Tuning` can bias the `some` weight at run time.

This is how to raise the chance of a generated precondition, which is what `PrecondElim` wants, without
a change to the language. The split stays total in its support, so soundness and completeness do not
change.

`genOptNat` below optionally wraps a `Nat` drawn from 0 to 3. It writes the split inline, so the
attribute sees it. -/

@[tunable]
def genOptNat [Gen G] : G (Option Nat) :=
  frequency [
    (1, fun _ => do let x ← (ULift.down · |>.val) <$> RandomChoice.choose 0 3 (by omega); pure (some x)),
    (1, fun _ => pure none)
  ] (by simp)

/-- One tunable site of arity 2, for `some` and `none`, with no recursive call. -/
example : genOptNat.sites = #[⟨`SetGenTunableExamples.genOptNat.site0, 0, 2, #[0, 0]⟩] := rfl

/-- The defaults are the inline 1 to 1 split. -/
example : genOptNat.defaults = ⟨#[(1, 0), (1, 0)]⟩ := rfl

/-- `tuned_defaults` is definitional here too. -/
example : (genOptNat.tuned genOptNat.defaults : SetGen.Set (Option Nat)) = genOptNat :=
  genOptNat.tuned_defaults

/-- A bias on the split leaves the generator fixed at `Set`. For *any* `θ`, both `none` and every
    reachable `some x` stay reachable, because `Tuning.weight` keeps both branch weights at 1 or more.
    The distribution shifts and the language does not.

    This proof needs no `unseal`. A non-recursive generator whose body *is* the `frequency` needs only
    an `unfold`. -/
theorem genOptNat_tuned_eq (θ : Tuning) :
    (genOptNat.tuned θ : SetGen.Set (Option Nat)) = genOptNat := by
  unfold genOptNat genOptNat.tuned
  apply SetGen.frequency_congr_weights
  · rfl
  all_goals simp [Tuning.weight_pos]

example (θ : Tuning) :
    SetGen.support (genOptNat.tuned θ : SetGen.Set (Option Nat)) =
      SetGen.support (genOptNat : SetGen.Set (Option Nat)) := by
  rw [genOptNat_tuned_eq]

/-! ## 7. Every recursion form, not just `partial_fixpoint`

The attribute rewrites the elaborated body, so the equation compiler never runs a second time. The
tuned generator therefore scrutinises through the *same* matcher constants as the original, and
`tuned_defaults` is `Eq.refl` under structural recursion and under well-founded recursion as well. -/

@[tunable]
def genStruct [Gen G] (size : Nat) : G Tree :=
  match size with
  | 0 => pure .leaf
  | n + 1 =>
    frequency [
      (1, fun _ => pure .leaf),
      (5, fun _ => do
        let l ← genStruct n
        let r ← genStruct n
        return .node l r)
    ] (by simp)

/-- Structural recursion hands the recursive results to the branch as a `below` bundle, and the two
    projections of that bundle are the two holes. -/
example : genStruct.sites = #[⟨`SetGenTunableExamples.genStruct.site0, 0, 2, #[0, 2]⟩] := rfl

example (size : Nat) :
    (genStruct.tuned genStruct.defaults size : SetGen.Set Tree) = genStruct size :=
  genStruct.tuned_defaults size

@[tunable]
def genWF [Gen G] (fuel : Nat) : G Tree :=
  if h : fuel = 0 then pure .leaf
  else
    frequency [
      (1, fun _ => pure .leaf),
      (5, fun _ => do
        let l ← genWF (fuel - 1)
        let r ← genWF (fuel - 1)
        return .node l r)
    ] (by simp)
termination_by fuel
decreasing_by all_goals omega

/-- Well-founded recursion passes an `ih` that lands in the generator's own monad, and the two
    applications of it are the two holes. -/
example : genWF.sites = #[⟨`SetGenTunableExamples.genWF.site0, 0, 2, #[0, 2]⟩] := rfl

example (fuel : Nat) :
    (genWF.tuned genWF.defaults fuel : SetGen.Set Tree) = genWF fuel :=
  genWF.tuned_defaults fuel

/-! ## 8. Naming the depth binder

`depth` is the default name, and `(depth := …)` names any other `Nat` binder. -/

@[tunable (depth := lvl)]
def genLvl [Gen G] (lvl : Nat) : G Tree :=
  frequency [
    (1, fun _ => pure .leaf),
    (2, fun _ => do
      let l ← genLvl (lvl + 1)
      let r ← genLvl (lvl + 1)
      return .node l r)
  ] (by simp)
partial_fixpoint

example (lvl : Nat) :
    (genLvl.tuned genLvl.defaults lvl : SetGen.Set Tree) = genLvl lvl :=
  genLvl.tuned_defaults lvl

/-! The attribute must find a depth binder that you name. A site that cannot see it is an error, and
not a silent fall back to depth 0. -/

/--
error: tunable: `SetGenTunableExamples.genNoLvl` has no `Nat` binder named `lvl` in scope at one of its `frequency` sites — `(depth := lvl)` names the binder whose value each site reads its weight schedules at
-/
#guard_msgs in
@[tunable (depth := lvl)]
def genNoLvl [Gen G] : G Nat :=
  frequency [
    (1, fun _ => pure 0),
    (1, fun _ => pure 1)
  ] (by simp)

end SetGenTunableExamples

section ReweightObligation

variable {α : Type}

-- Reweight a uniform choice: `oneOf` becomes `frequency`.
example (gs : List (Unit → SetGen.Set α)) (gs' : List (Nat × (Unit → SetGen.Set α)))
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1)
    (hne : gs ≠ []) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    SetGen.support (frequency gs' h') = SetGen.support (oneOf gs hne) :=
  SetGen.support_frequency_reweight hsnd hpos hne h'

-- Change the weights in place: `frequency` becomes `frequency`, which is the shape `@[tunable]`
-- rewrites.
example (gs gs' : List (Nat × (Unit → SetGen.Set α)))
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    SetGen.support (frequency gs' h') = SetGen.support (frequency gs h) :=
  SetGen.support_frequency_congr_weights hsnd hpos hpos' h h'

-- The strengthening that only `Set` admits. These are the same two facts as equalities of
-- *generators*, because `support` is the identity. They are what rewrites a `frequency` inside a `do`
-- block.
example (gs : List (Nat × (Unit → SetGen.Set α)))
    (hpos : ∀ p ∈ gs, 0 < p.1) (h : 0 < List.sum (List.map Prod.fst gs))
    (hne : gs.map Prod.snd ≠ []) :
    frequency gs h = oneOf (gs.map Prod.snd) hne :=
  SetGen.frequency_eq_oneOf hpos h hne

-- `Tuning.weight` satisfies the positivity hypothesis for every `θ` and every depth, so no tuning a
-- user supplies can fail it. The `SPMF` side shares this fact.
example (θ : Tuning) (i d : Nat) : 0 < θ.weight i d := Tuning.weight_pos θ i d

-- `frequency`'s own side condition holds for every `θ` before any `θ` exists. That is what lets
-- `@[tunable]` rewrite the weights during elaboration.
example (θ : Tuning) (i d : Nat) (g : Unit → SetGen.Set α) (tl : List (Nat × (Unit → SetGen.Set α))) :
    0 < List.sum (List.map Prod.fst ((θ.weight i d, g) :: tl)) :=
  Tuning.sum_map_fst_pos θ i d g tl

-- Given an equality of supports, soundness and completeness transfer in one application.
example {g g' : SetGen.Set α} {P : α → Prop}
    (tuned_support : SetGen.support g' = SetGen.support g)
    (sound_complete : SetGen.IsSoundAndComplete g P) :
    SetGen.IsSoundAndComplete g' P :=
  SetGen.IsSoundAndComplete.of_support_eq tuned_support sound_complete

end ReweightObligation
