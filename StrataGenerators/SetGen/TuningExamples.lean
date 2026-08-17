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

The counterpart of Basalt's `BasaltTest/Tuning.lean`, exercised against the `SetGen.Set`
interpretation instead of `SPMF`. The `@[tunable]` attribute and the `Tuning` data are generic over
`[Gen G]`, and `SetGen.Set` is a `Gen`, so the attribute applies with no changes:

1. `genTree.tuned genTree.defaults` and `genTree` are interchangeable — `tuned_defaults` is
   `Eq.refl` checked by the kernel, so a generator's existing `SetGen` support proofs compile
   unchanged.
2. `sites` reports each site's name, offset, arity, and per-branch recursive calls.
3. `defaults` are the literal weights from the source.
4. A literal `0` weight is rejected at elaboration; a `0` in a *runtime* `θ` is clamped to `1`.
5. **Every `θ` denotes the same set.** `genFoo.tuned θ = genFoo` at `SetGen.Set`, for every `θ` —
   not merely equal supports but equal generators, because `SetGen.support` is the identity. So any
   soundness/completeness property of the untuned generator holds of every tuning of it, with no
   per-property work.
6. Structural, well-founded and `partial_fixpoint` recursion are all tunable — `@[tunable]` rewrites
   the elaborated body, so it does not constrain how the generator recurses.
7. The site's depth is read from a binder named `depth`, or from whichever binder
   `@[tunable (depth := …)]` names.

The distribution-comparison sections of the `SPMF` version (`#genstats`, `p50`, head-constructor
splits) have no counterpart here: `SetGen.Set` tracks only *reachability*, not probabilities, and is
noncomputable. What tuning buys on the `Set` side is precisely §5 — reweighting never changes the
support, so a generator's soundness-and-completeness survives any `θ`.
-/

namespace SetGenTunableExamples

/-- A tiny binary tree, standing in for `BasaltExamples.BST.Tree`. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree
deriving Repr, DecidableEq

/-! ## A depth-indexed tunable generator

Mirrors `BasaltTest/Tuning.lean`'s `genTree`: an explicit `depth` binder, so each site reads its
weights at that depth. -/

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

`tuned_defaults` is emitted by the attribute — definitionally — at `SetGen.Set` just as at `SPMF`. -/

example (depth : Nat) :
    (genTree.tuned genTree.defaults depth : SetGen.Set Tree) = genTree depth :=
  genTree.tuned_defaults depth

/-- Support facts about the untuned generator transfer to the default-tuned form by rewriting —
    adopting tuning does not change existing `SetGen` proofs. -/
example (depth : Nat) (t : Tree) :
    t ∈ SetGen.support (genTree.tuned genTree.defaults depth : SetGen.Set Tree) ↔
      t ∈ SetGen.support (genTree depth : SetGen.Set Tree) := by
  rw [genTree.tuned_defaults]

/-! ## 2. The site table

Sites are named positionally, `<defName>.site<i>`, outside-in in traversal order. -/

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

/-! Zero entries in a *runtime* `θ` cannot break support either: they read as weight `1`
(`Tuning.weight` clamps), so the generator is total in `θ`, exactly as on the `SPMF` side. -/

example (i d : Nat) :
    Tuning.weight ⟨#[(0, 0), (0, 0)]⟩ i d = Tuning.weight ⟨#[(1, 0), (1, 0)]⟩ i d := by
  simp only [Tuning.weight]
  rcases i with _ | _ | i <;> simp

/-! ## 5. Every `θ` denotes the same generator

This is the section with no `SPMF` counterpart, and the reason to interpret a tuned generator at
`Set` at all: `Set` is weight-blind, so `genFoo.tuned θ` and `genFoo` are *the same set-valued
generator* for every `θ`. Not "the same support up to a lemma" — literally equal, so every existing
result about the untuned generator applies to the tuned one by `rw`.

For a `partial_fixpoint` generator, both sides are `Lean.Order.fix` applied to functionals that
differ only in their `frequency` weights (`@[tunable]` binds `θ` outside the fix and re-proves
monotonicity). `SetGen.fix_congr` reduces the goal to equality of those functionals, and
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

/-- The support consequence, for any `θ` and any depth: no reachable tree is lost or gained. -/
example (θ : Tuning) (depth : Nat) :
    SetGen.support (genTree.tuned θ depth : SetGen.Set Tree) =
      SetGen.support (genTree depth : SetGen.Set Tree) := by
  rw [genTree_tuned_eq]

/-- And the property-level consequence: *whatever* predicate `genTree` is sound and complete for,
    every tuning of it is sound and complete for the same predicate. The proof does not need to know
    what `P` is — which is the whole point of establishing the generator equality. -/
example (θ : Tuning) (depth : Nat) (P : Tree → Prop)
    (h : SetGen.IsSoundAndComplete (genTree depth : SetGen.Set Tree) P) :
    SetGen.IsSoundAndComplete (genTree.tuned θ depth : SetGen.Set Tree) P :=
  SetGen.IsSoundAndComplete.of_support_eq (by rw [genTree_tuned_eq]) h

/-! ## 6. A *tunable* option split via `weightedOptionGen`

`Basalt`'s `optionGen`/`biasedOptionGen` decide `some`/`none` with a rational `coin`, which is not a
`frequency` site — so `@[tunable]` cannot address it. `SetGen.weightedOptionGen` splits with a
`frequency` over two `Nat` weights instead, so inlining that split under `@[tunable]` records a
tunable site whose `some`-weight a `Tuning` can bias at runtime. This is the mechanism for
"boost the probability of generating a precondition" (`PrecondElim`) without touching the language:
the split stays support-total, so soundness/completeness is unchanged.

Here `genOptNat` optionally wraps a `Nat` drawn from `0..3`; the split is written inline so the
attribute sees it. -/

@[tunable]
def genOptNat [Gen G] : G (Option Nat) :=
  frequency [
    (1, fun _ => do let x ← (ULift.down · |>.val) <$> RandomChoice.choose 0 3 (by omega); pure (some x)),
    (1, fun _ => pure none)
  ] (by simp)

/-- One tunable site, arity 2 (`some`/`none`), no recursive calls. -/
example : genOptNat.sites = #[⟨`SetGenTunableExamples.genOptNat.site0, 0, 2, #[0, 0]⟩] := rfl

/-- The defaults are the inline `1 : 1` split. -/
example : genOptNat.defaults = ⟨#[(1, 0), (1, 0)]⟩ := rfl

/-- `tuned_defaults` is definitional here too. -/
example : (genOptNat.tuned genOptNat.defaults : SetGen.Set (Option Nat)) = genOptNat :=
  genOptNat.tuned_defaults

/-- Biasing the split (e.g. `PrecondElim` wanting `some` more often) leaves the generator fixed at
    `Set`: both `none` and every reachable `some x` stay reachable for *any* `θ`, because
    `Tuning.weight` keeps both branch weights ≥ 1. The distribution shifts; the language does not.

    No `unseal` here — a non-recursive generator whose body *is* the `frequency` needs only
    `unfold`. -/
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

The attribute rewrites the elaborated body, so the equation compiler never runs a second time and
the tuned generator scrutinises through the *same* matcher constants as the original.
`tuned_defaults` is therefore `Eq.refl` under structural and well-founded recursion too. This is
what the older `tunable def` macro could not do. -/

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

/-- Structural recursion hands its recursive results to the branch as a `below` bundle; the two
    projections of it are the two holes. -/
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

/-- Well-founded recursion passes an `ih` landing in the generator's own monad; the two applications
    of it are the two holes. -/
example : genWF.sites = #[⟨`SetGenTunableExamples.genWF.site0, 0, 2, #[0, 2]⟩] := rfl

example (fuel : Nat) :
    (genWF.tuned genWF.defaults fuel : SetGen.Set Tree) = genWF fuel :=
  genWF.tuned_defaults fuel

/-! ## 8. Naming the depth binder

`depth` is the default; `(depth := …)` names any other `Nat` binder. -/

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

/-! A depth binder named explicitly must be found: a site that cannot see it is an error, not a
silent fall back to depth `0`. -/

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

-- Reweighting a uniform choice: `oneOf` to `frequency`.
example (gs : List (Unit → SetGen.Set α)) (gs' : List (Nat × (Unit → SetGen.Set α)))
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1)
    (hne : gs ≠ []) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    SetGen.support (frequency gs' h') = SetGen.support (oneOf gs hne) :=
  SetGen.support_frequency_reweight hsnd hpos hne h'

-- Changing weights in place: `frequency` to `frequency`, the shape `@[tunable]` rewrites.
example (gs gs' : List (Nat × (Unit → SetGen.Set α)))
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    SetGen.support (frequency gs' h') = SetGen.support (frequency gs h) :=
  SetGen.support_frequency_congr_weights hsnd hpos hpos' h h'

-- The `Set`-only strengthening: the same two facts as *generator* equalities, since `support` is the
-- identity. These are what rewrite a `frequency` sitting inside a `do` block.
example (gs : List (Nat × (Unit → SetGen.Set α)))
    (hpos : ∀ p ∈ gs, 0 < p.1) (h : 0 < List.sum (List.map Prod.fst gs))
    (hne : gs.map Prod.snd ≠ []) :
    frequency gs h = oneOf (gs.map Prod.snd) hne :=
  SetGen.frequency_eq_oneOf hpos h hne

-- `Tuning.weight` satisfies the positivity hypothesis unconditionally, for every `θ` and depth —
-- there is no tuning a user can supply that fails it. (Shared with the `SPMF` side.)
example (θ : Tuning) (i d : Nat) : 0 < θ.weight i d := Tuning.weight_pos θ i d

-- And `frequency`'s own side condition holds for every `θ` before any `θ` exists, which is what lets
-- `@[tunable]` rewrite the weights at elaboration time.
example (θ : Tuning) (i d : Nat) (g : Unit → SetGen.Set α) (tl : List (Nat × (Unit → SetGen.Set α))) :
    0 < List.sum (List.map Prod.fst ((θ.weight i d, g) :: tl)) :=
  Tuning.sum_map_fst_pos θ i d g tl

-- Given a `tuned_support`, soundness-and-completeness transfers in one application. This is the
-- `SetGen` analogue of `genFoo.tuned_sound_complete`.
example {g g' : SetGen.Set α} {P : α → Prop}
    (tuned_support : SetGen.support g' = SetGen.support g)
    (sound_complete : SetGen.IsSoundAndComplete g P) :
    SetGen.IsSoundAndComplete g' P :=
  SetGen.IsSoundAndComplete.of_support_eq tuned_support sound_complete

end ReweightObligation
