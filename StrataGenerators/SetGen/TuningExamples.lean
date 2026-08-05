/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.SetGen
import StrataGenerators.SetGen.Tuning
import Basalt.Tuning.Macro

open RandomChoice
open scoped SetGen.Set

/-!
# `tunable def` on `Set`-based generators

The counterpart of Basalt's `BasaltTest/Tuning.lean`, exercised against the `SetGen.Set`
interpretation instead of `SPMF`. The `tunable def` macro and the `Tuning` data are generic over
`[Gen G]`, and `SetGen.Set` is a `Gen`, so the macro applies with no changes:

1. `genTree.tuned genTree.defaults` and `genTree` are interchangeable — `tuned_defaults` is
   definitional, so a generator's existing `SetGen` support proofs compile unchanged.
2. `sites` reports each site's offset, arity, and per-branch recursive calls.
3. `defaults` are the literal weights from the source.
4. A literal `0` weight is rejected at elaboration.
5. The reweight obligations (`SetGen.support_frequency_reweight` /
   `SetGen.support_frequency_congr_weights`) and the soundness/completeness transfer
   (`SetGen.IsSoundAndComplete.of_support_eq`) hold at `SetGen.Set`, and `Tuning.weight_pos`
   discharges their positivity side conditions for every runtime `θ`.

The distribution-comparison sections of the `SPMF` version (`#genstats`, `p50`, head-constructor
splits) have no counterpart here: `SetGen.Set` tracks only *reachability* (support), not
probabilities, and is noncomputable. What tuning buys on the `Set` side is precisely that
reweighting never changes the support — so a generator's soundness-and-completeness survives any
`θ`, which is what the section-5 examples establish.
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

tunable def genTree [Gen G] (depth : Nat) : G Tree :=
  frequency (site := `genTree.spine) [
    (1, fun _ => pure .leaf),
    (2, fun _ => do
      let l ← genTree (depth + 1)
      let r ← genTree (depth + 1)
      return .node l r)
  ] (by simp)
partial_fixpoint

/-! ## 1. The defaults are the generator as written

`tuned_defaults` is proved by the macro — definitionally — at `SetGen.Set` just as at `SPMF`. -/

example (depth : Nat) :
    (genTree.tuned genTree.defaults depth : SetGen.Set Tree) = genTree depth :=
  genTree.tuned_defaults depth

/-- Support facts about the untuned generator transfer to the default-tuned form by rewriting —
    adopting tuning does not change existing `SetGen` proofs. -/
example (depth : Nat) (t : Tree) :
    t ∈ SetGen.support (genTree.tuned genTree.defaults depth : SetGen.Set Tree) ↔
      t ∈ SetGen.support (genTree depth : SetGen.Set Tree) := by
  rw [genTree.tuned_defaults]

/-! ## 2. The site table -/

/-- The site override names the site; one site, holes `#[0, 2]`. -/
example : genTree.sites = #[⟨`genTree.spine, 0, 2, #[0, 2]⟩] := rfl

/-! ## 3. The defaults are the literal weights from the source. -/

example : genTree.defaults = ⟨#[(1, 0), (2, 0)]⟩ := rfl

/-! ## 4. A zero weight is rejected at elaboration -/

/--
error: tunable def: a literal weight of 0 is rejected: a zero weight removes its branch from the generator's support (see `SPMF.support_frequency`), breaking support-completeness (`IsSoundAndComplete`). To prune a branch, remove it from the source instead.
-/
#guard_msgs in
tunable def genZero [Gen G] : G Nat := do
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

end SetGenTunableExamples

section ReweightObligation

variable {α : Type}

-- Reweighting a uniform choice: `oneOf` to `frequency`, the shape `derive_tuning` rewrites.
example (gs : List (Unit → SetGen.Set α)) (gs' : List (Nat × (Unit → SetGen.Set α)))
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1)
    (hne : gs ≠ []) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    SetGen.support (frequency gs' h') = SetGen.support (oneOf gs hne) :=
  SetGen.support_frequency_reweight hsnd hpos hne h'

-- Changing weights in place: `frequency` to `frequency`, the shape `tunable def` rewrites.
example (gs gs' : List (Nat × (Unit → SetGen.Set α)))
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    SetGen.support (frequency gs' h') = SetGen.support (frequency gs h) :=
  SetGen.support_frequency_congr_weights hsnd hpos hpos' h h'

-- `Tuning.weight` satisfies the positivity hypothesis unconditionally, for every `θ` and depth —
-- there is no tuning a user can supply that fails it. (Shared with the `SPMF` side.)
example (θ : Tuning) (i d : Nat) : 0 < θ.weight i d := Tuning.weight_pos θ i d

-- And given a `tuned_support`, soundness-and-completeness transfers in one application. This is the
-- `SetGen` analogue of `genFoo.tuned_sound_complete`.
example {g g' : SetGen.Set α} {P : α → Prop}
    (tuned_support : SetGen.support g' = SetGen.support g)
    (sound_complete : SetGen.IsSoundAndComplete g P) :
    SetGen.IsSoundAndComplete g' P :=
  SetGen.IsSoundAndComplete.of_support_eq tuned_support sound_complete

end ReweightObligation
