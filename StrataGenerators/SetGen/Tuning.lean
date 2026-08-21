/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.SetGen.Support
import StrataGenerators.SetGen.Classes

open RandomChoice
open scoped SetGen.Set

/-!
# Tuning support for `Set`-based generators

Basalt's tuning infrastructure has two halves.

The first half is the data and the `@[tunable]` attribute, in `Basalt.Tuning` and
`Basalt.Tuning.Attr`. It holds `Tuning`, `Site`, `Tuning.weight`, `Tuning.weight_pos` and
`Tuning.sum_map_fst_pos`, and the attribute that threads a `Tuning` through a generator's
`frequency` sites. All of it is generic over `[Gen G]` and needs no `SPMF`, so it applies unchanged
to any `Gen`. `SetGen.Set` is one. If you tag `@[tunable] def genFoo … : G α := …`, the attribute
emits `genFoo.tuned`, `genFoo.defaults`, `genFoo.sites` and `genFoo.tuned_defaults`. All four
specialize to `G := SetGen.Set`.

The attribute rewrites the *elaborated* body rather than the surface syntax. Two consequences matter
here. It does not constrain the recursion form, so a structural, a well-founded and a
`partial_fixpoint` generator are all tunable. And a second module can apply it with
`attribute [tunable] genFoo`, to a generator whose source you do not want to touch.
`StrataGenerators.TuningProfiles` does that to `genPrecondition`, to `genLMonoTy` and to
`genStmt._mutual`. The last one is the auxiliary that the members of a `mutual` block share, and a
tag on it threads one `θ` through the whole recursion.

The second half is the reweight lemmas. In Basalt they live in `Basalt.SPMF.Support` and
`Basalt.Laws`, and they are stated for `SPMF`. This file ports them to `SetGen.Set` and then
strengthens them, because at `Set` the support *is* the generator:

- `SetGen.support_frequency_reweight` and `SetGen.support_frequency_congr_weights` are the direct
  ports. Given positive weights, a reweighted `frequency` has the support that the original had. The
  original is a uniform `oneOf` in the first lemma, and a `frequency` in the second.
- `SetGen.frequency_eq_oneOf` and `SetGen.frequency_congr_weights` state the same two facts as
  equalities of *generators* rather than of supports. `SetGen.support` is the identity function, so
  the support-level statements already prove them. The restatement earns its place: an equality of
  generators rewrites a `frequency` wherever it occurs, and a support equation does not apply under
  the `Bind.bind`s and the `dite`s of a `do` block.
- `SetGen.fix_congr` says that `Lean.Order.fix` depends on its functional alone, because the
  monotonicity proof is a `Prop`. This lemma lifts a per-site fact to a whole `partial_fixpoint`
  generator.
- `SetGen.IsSoundAndComplete.of_support_eq` transfers soundness and completeness along a support
  equation. A tuned generator's support fact therefore lifts the untuned law in one step.

`Tuning.weight_pos` discharges the positivity hypotheses for *every* runtime `θ`, so no weighting
that a user supplies can fail them. In practice `simp [Tuning.weight_pos]` closes them: the
obligation `∀ p ∈ [(θ.weight i d, g), …], 0 < p.1` reduces to a conjunction of `0 < θ.weight _ _`.

## Where to look

* `StrataGenerators.SetGen.TuningWalkthrough` is the end-user walkthrough. It tags a generator, finds
  the flat index of a branch, writes a `Tuning`, draws from it, and checks that nothing broke. Start
  here if you want to *use* tuning.
* `StrataGenerators.SetGen.TuningExamples` shows what the attribute emits: the site tables, both
  error cases, and every recursion form.
* `StrataGenerators.SetGen.TuningPrototypes` applies the same steps to *every* generator that this
  repo's test suite draws from, and proves θ-invariance for each.
* `StrataGenerators.TuningProfiles` says which weights to use for which family of properties, and
  gives the `dist-report` measurements behind them.

## How to prove a tuned generator θ-invariant

The `Set` interpretation ignores weights, so for every `θ` the tuned generator denotes the *same
set* as the untuned one. There is one recipe per recursion form:

* **The body is the `frequency`, with no recursion.** `unfold` both sides, then
  `apply SetGen.frequency_congr_weights`.
* **`partial_fixpoint`.** `apply SetGen.fix_congr`, then `funext`, then reweight the functional's
  site. First `unseal genFoo genFoo.tuned`, because a `partial_fixpoint` definition is irreducible
  and the attribute copies that status onto `.tuned`.
* **`termination_by`, and a `mutual` block.** The same, with `SetGen.wellFounded_fix_congr`, after
  you `delta`-unfold the definition. The members of a `mutual` block share one `WellFounded.fix`, so
  unfold the `genFoo._mutual` auxiliary and `cases` the `PSum`. The member with no site closes by
  `rfl`. This is the recipe `genStmt` needs.
* **Structural recursion on a `Nat`.** The same, with `SetGen.brecOn_congr`. Here `delta` leaves the
  arguments that the compiler moved into the motive applied *outside* the `Nat.brecOn`. So reach the
  functional with `refine congrFun (congrFun (SetGen.brecOn_congr ?_ n) x) y` rather than with
  `apply`. Then `split` takes a wide per-constructor match one arm at a time. `genLExprBase` has ten
  arms.
* **A `frequency` inside a `do` block.** `rw [SetGen.frequency_eq_oneOf, …]` once per site. That
  sends every positively-weighted `frequency` to the uniform `oneOf` over its branches, and both
  sides then close by `rfl`.

What transfers is the equality of generators, not merely an equality of supports. So every existing
lemma about the untuned generator applies to the tuned one by `rw`.
-/

namespace SetGen

section reweight

variable {α : Type}

/-- A `frequency` over the branches of a uniform `oneOf` reaches the same values, if every weight is
positive. A weight therefore decides how often a branch is taken, and never whether it is
reachable. -/
theorem support_frequency_reweight
    {gs : List (Unit → Set α)} {gs' : List (Nat × (Unit → Set α))}
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1)
    (hne : gs ≠ []) (h_pos : 0 < List.sum (List.map Prod.fst gs')) :
    support (frequency gs' h_pos) = support (oneOf gs hne) := by
  subst hsnd
  rw [support_frequency, support_oneOf]
  ext a
  simp only [Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    exact ⟨g, ⟨(w, g), hmem, rfl⟩, ha⟩
  · rintro ⟨g, ⟨⟨w, g'⟩, hmem, hg⟩, ha⟩
    cases hg
    exact ⟨w, g', hmem, hpos _ hmem, ha⟩

/-- Two `frequency`s over the same branches reach the same values, if every weight on both sides is
positive. This is the shape a tuning rewrite has: `@[tunable]` replaces each literal weight by a
`Tuning.weight θ i d` read in place, so both sides are a `frequency` and only the weights differ. -/
theorem support_frequency_congr_weights
    {gs gs' : List (Nat × (Unit → Set α))}
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    support (frequency gs' h') = support (frequency gs h) := by
  rw [support_frequency, support_frequency]
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    have : g ∈ gs.map Prod.snd := hsnd ▸ List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
    obtain ⟨⟨w', g'⟩, hmem', hg⟩ := List.mem_map.mp this
    cases hg
    exact ⟨w', g', hmem', hpos' _ hmem', ha⟩
  · rintro ⟨w, g, hmem, _, ha⟩
    have : g ∈ gs'.map Prod.snd := hsnd ▸ List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
    obtain ⟨⟨w', g'⟩, hmem', hg⟩ := List.mem_map.mp this
    cases hg
    exact ⟨w', g', hmem', hpos _ hmem', ha⟩

/-! ### The same facts as generator equalities

`SetGen.support` is the identity function on `Set α`, so each of the two lemmas above already *is* an
equality of generators. The restatement needs no further argument, and it earns its place: `rw` and
`simp only` can use an equation between generators to rewrite a `frequency` inside a `do` block or a
`dite`. That is where the sites of a realistic generator sit. -/

/-- **Canonical form of a `frequency` at `Set`.** A `frequency` with positive weights equals the
uniform `oneOf` over its branches, because the `Set` interpretation cannot see a weight.

This is the main tool for θ-invariance of a generator whose sites sit inside a `do` block. One
rewrite per site sends the tuned and the untuned generator to the same weight-free form, for
every `θ`. -/
theorem frequency_eq_oneOf {gs : List (Nat × (Unit → Set α))}
    (hpos : ∀ p ∈ gs, 0 < p.1) (h : 0 < List.sum (List.map Prod.fst gs))
    (hne : gs.map Prod.snd ≠ []) :
    frequency gs h = oneOf (gs.map Prod.snd) hne :=
  support_frequency_reweight rfl hpos hne h

/-- At `Set`, a change to the weights of a `frequency` changes nothing at all. This is the rewrite
`@[tunable]` performs, stated as an equality of generators. -/
theorem frequency_congr_weights {gs gs' : List (Nat × (Unit → Set α))}
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    frequency gs' h' = frequency gs h :=
  support_frequency_congr_weights hsnd hpos hpos' h h'

end reweight

/-- Two `Lean.Order.fix` terms over equal functionals are equal. The monotonicity proof is a `Prop`,
so proof irrelevance makes it immaterial.

This lemma turns a per-site reweighting fact into a fact about a whole `partial_fixpoint` generator.
`@[tunable]` binds `θ` *outside* the fix and re-proves monotonicity for the rewritten functional. So
`genFoo.tuned θ` and `genFoo` are one fix over two functionals that differ only in their `frequency`
weights, and at `Set` those functionals are equal.

The statement is not specific to `Set`. It belongs upstream in Basalt, next to the reweight
lemmas. -/
theorem fix_congr {α : Sort u} [Lean.Order.CCPO α] {f g : α → α}
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) (h : f = g) :
    Lean.Order.fix f hf = Lean.Order.fix g hg := by
  subst h; rfl

/-- Two `WellFounded.fix` terms over equal functionals are equal. The accessibility argument is a
`Prop`, so only the functional matters.

The equation compiler uses `WellFounded.fix` for a generator with `termination_by`, and the members
of a `mutual` block share one such fix over a `PSum` of their argument tuples. This lemma is
therefore what lifts a per-site reweighting to a whole block. -/
theorem wellFounded_fix_congr {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
    (hwf : WellFounded r) {F F' : ∀ x, (∀ y, r y x → C y) → C x} (h : F = F') :
    WellFounded.fix hwf F = WellFounded.fix hwf F' := by
  subst h; rfl

/-- Two `Nat.brecOn` terms over equal step functions are equal. The recursive results arrive in a
`Nat.below` bundle, which is one bound variable on both sides, so equality of the step functions is
enough.

The equation compiler uses `Nat.brecOn` for a generator that recurses structurally on a `Nat`, as
`genLMonoTy` and `genLExprBase` do. -/
theorem brecOn_congr {motive : Nat → Sort u}
    {F F' : (n : Nat) → @Nat.below motive n → motive n} (h : F = F') (n : Nat) :
    @Nat.brecOn motive n F = @Nat.brecOn motive n F' := by
  subst h; rfl

/-- Soundness and completeness transfer along an equality of supports. If a generator is sound and
complete for `P`, then so is every generator that reaches the same values.

This is the last step of a tuning proof. The generator equalities above give the equality of
supports, and this lemma carries the law across it. -/
theorem IsSoundAndComplete.of_support_eq {g g' : Set α} {P : α → Prop}
    (h : support g' = support g) (hg : IsSoundAndComplete g P) :
    IsSoundAndComplete g' P where
  support_iff a := by rw [h]; exact hg.support_iff a

end SetGen
