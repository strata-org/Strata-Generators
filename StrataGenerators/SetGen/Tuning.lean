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

Basalt's tuning infrastructure has two halves:

* the data and the `@[tunable]` attribute (`Basalt.Tuning` / `Basalt.Tuning.Attr`) — `Tuning`,
  `Site`, `Tuning.weight`, `Tuning.weight_pos`, `Tuning.sum_map_fst_pos`, and the attribute that
  threads a `Tuning` through a generator's `frequency` sites. All of it is generic over `[Gen G]`,
  with no `SPMF` dependency, so it applies to any `Gen` — including `SetGen.Set` (see
  `StrataGenerators.SetGen.Core`) — with no changes. Tagging `@[tunable] def genFoo … : G α := …`
  emits `genFoo.tuned/.defaults/.sites/.tuned_defaults`, and those all specialize to
  `G := SetGen.Set`.

  (`@[tunable]` replaced the older `tunable def` macro in
  [basalt@5d23328](https://github.com/hgoldstein95/basalt/commit/5d233281209442f6edc2d776993fe04bc39cb06c).
  Because it rewrites the *elaborated* body rather than the surface syntax, it no longer constrains
  the recursion form — structural, well-founded and `partial_fixpoint` generators are all tunable —
  and it can be applied from another module, with `attribute [tunable] genFoo`, to a generator whose
  source you do not want to touch. `StrataGenerators.TuningProfiles` does exactly that to the
  shipping `genPrecondition` and `genLMonoTy`, and to `genStmt._mutual` — the auxiliary a `mutual`
  block's members share, tagging which is what threads one `θ` through the whole recursion.)

* the proof-side reweight lemmas, which in Basalt live in `Basalt.SPMF.Support` and `Basalt.Laws`
  and are stated for `SPMF`. This file ports those to `SetGen.Set` and then strengthens them, since
  `Set`'s support *is* the generator:

  - `SetGen.support_frequency_reweight` / `SetGen.support_frequency_congr_weights` — the direct
    ports: reweighting a `frequency` (from a uniform `oneOf`, or in place) leaves the support
    unchanged, given positive weights.
  - `SetGen.frequency_eq_oneOf` / `SetGen.frequency_congr_weights` — the same two facts as
    *generator* equalities rather than support equalities. `SetGen.support` is the identity
    (`SetGen.support s = s` by definition), so the support-level statements already prove these;
    they are worth stating separately because an equality of generators rewrites anywhere a
    `frequency` occurs, including under the `Bind.bind`s and `dite`s of a `do` block, where a
    support-level equation does not apply.
  - `SetGen.fix_congr` — `Lean.Order.fix` respects equality of its functional (the monotonicity
    proof is a `Prop`, hence irrelevant). This is what lifts the per-site facts above to a whole
    `partial_fixpoint` generator.
  - `SetGen.IsSoundAndComplete.of_support_eq` — soundness-and-completeness transfers along a
    support equation, so a tuned generator's support fact lifts an untuned `IsSoundAndComplete` in
    one step.

`Tuning.weight_pos` (from `Basalt.Tuning`) discharges the positivity hypotheses for *every* runtime
`θ`, exactly as it does on the `SPMF` side, so there is no weighting a user can supply that fails
them. In practice `simp [Tuning.weight_pos]` closes them: the obligation
`∀ p ∈ [(θ.weight i d, g), …], 0 < p.1` reduces to a conjunction of `0 < θ.weight _ _`.

## Where to look

* `StrataGenerators.SetGen.TuningWalkthrough` — the end-user walkthrough: tag a generator, find the
  flat index of the branch you want, write a `Tuning`, draw from it, and check nothing broke. Start
  here if you want to *use* tuning.
* `StrataGenerators.SetGen.TuningExamples` — what the attribute emits, exhaustively: site tables,
  both error cases, and every recursion form.
* `StrataGenerators.SetGen.TuningPrototypes` — the same steps applied to *every* generator this
  repo's test suite draws from, with the θ-invariance theorem for each.
* `StrataGenerators.TuningProfiles` — which weights to use for which family of properties, and the
  measurements (`lake exe dist-report`) behind them.

## Proving a tuned generator θ-invariant

The `Set` interpretation is weight-blind, so for every `θ` the tuned generator denotes the *same
set* as the untuned one. Three recipes, all exercised in
`StrataGenerators.SetGen.TuningExamples`/`TuningPrototypes`:

* **Non-recursive, body is the `frequency`** — `unfold` both sides and
  `apply SetGen.frequency_congr_weights`.
* **`partial_fixpoint`** — `apply SetGen.fix_congr` (after `unseal genFoo genFoo.tuned`, since
  `partial_fixpoint` definitions are irreducible and `@[tunable]` copies that status onto `.tuned`),
  then `funext` and reweight the functional's site.
* **`termination_by`, including a `mutual` block** — the same, with `SetGen.wellFounded_fix_congr`
  after `delta`-unfolding the definition (a `mutual` block's members share one `WellFounded.fix`, so
  unfold the `genFoo._mutual` auxiliary and `cases` the `PSum`; the member with no site closes by
  `rfl`). This is what `genStmt` needs.
* **Structural recursion on a `Nat`** — the same, with `SetGen.brecOn_congr`. `delta` leaves the
  arguments the compiler moved into the motive applied *outside* the `Nat.brecOn`, so reach the
  functional with `refine congrFun (congrFun (SetGen.brecOn_congr ?_ n) x) y` rather than `apply`;
  then `split` handles a wide per-constructor match one arm at a time (`genLExprBase` has ten).
* **A `frequency` buried in a `do` block** — `rw [SetGen.frequency_eq_oneOf, …]` once per site,
  which canonicalizes every positively-weighted `frequency` to the uniform `oneOf` over its
  branches; both sides then close by `rfl`.

The payoff is that the generator equality, not merely a support equality, is what transfers: every
existing lemma about the untuned generator applies to the tuned one by `rw`.
-/

namespace SetGen

section reweight

variable {α : Type}

/-- Reweighting a uniform choice preserves its support. Replacing `oneOf gs` by a `frequency` over
the same branches leaves the set of reachable values unchanged, provided every weight is positive.

Ported from `SPMF.support_frequency_reweight` to `SetGen.Set`. -/
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

/-- The same, between two `frequency`s. This is the shape a tuning rewrite has: `@[tunable]`
replaces literal weights by `Tuning.weight θ i d` in place, so both sides are already `frequency`s
and only the weights differ.

Ported from `SPMF.support_frequency_congr_weights` to `SetGen.Set`. -/
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

`SetGen.support` is the identity function on `Set α`, so each of the two lemmas above *is* an
equality of generators — no additional argument is needed, only a restatement. The restatement
matters in practice: `rw` and `simp only` can use an equation between generators to rewrite a
`frequency` sitting inside a `do` block or a `dite`, which is where the sites of a realistic
generator live. -/

/-- **Canonical form of a `frequency` at `Set`.** Every positively-weighted `frequency` is *equal*
to the uniform `oneOf` over its branches: the weights are invisible to the `Set` interpretation.

This is the workhorse for θ-invariance of a generator whose sites are buried inside a `do` block:
rewriting with it once per site sends both the tuned and the untuned generator to the same
weight-free normal form, whatever `θ` is. -/
theorem frequency_eq_oneOf {gs : List (Nat × (Unit → Set α))}
    (hpos : ∀ p ∈ gs, 0 < p.1) (h : 0 < List.sum (List.map Prod.fst gs))
    (hne : gs.map Prod.snd ≠ []) :
    frequency gs h = oneOf (gs.map Prod.snd) hne :=
  support_frequency_reweight rfl hpos hne h

/-- `support_frequency_congr_weights` as an equality of generators: at `Set`, changing the weights
of a `frequency` in place — the rewrite `@[tunable]` performs — changes nothing at all. -/
theorem frequency_congr_weights {gs gs' : List (Nat × (Unit → Set α))}
    (hsnd : gs'.map Prod.snd = gs.map Prod.snd)
    (hpos : ∀ p ∈ gs', 0 < p.1) (hpos' : ∀ p ∈ gs, 0 < p.1)
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    frequency gs' h' = frequency gs h :=
  support_frequency_congr_weights hsnd hpos hpos' h h'

end reweight

/-- `Lean.Order.fix` depends on its functional only, not on the monotonicity proof (which is a
`Prop`, so proof irrelevance applies). This is what turns a per-site reweighting fact into a fact
about a whole `partial_fixpoint` generator: `@[tunable]` binds `θ` *outside* the fix and re-proves
monotonicity for the rewritten functional, so `genFoo.tuned θ` and `genFoo` are `Lean.Order.fix`
applied to two functionals that differ only in their `frequency` weights — and at `Set` those
functionals are equal (`SetGen.frequency_congr_weights`).

Not `Set`-specific; stated here because the tuning port is its only consumer so far, and it belongs
upstream in Basalt alongside the reweight lemmas. -/
theorem fix_congr {α : Sort u} [Lean.Order.CCPO α] {f g : α → α}
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) (h : f = g) :
    Lean.Order.fix f hf = Lean.Order.fix g hg := by
  subst h; rfl

/-- The same fact for `WellFounded.fix`, which is what the equation compiler uses for a generator
with `termination_by` — including a `mutual` block, whose members share one `WellFounded.fix` over a
`PSum` of their argument tuples. As with `fix_congr`, the accessibility/monotonicity argument is a
`Prop`, so only the functional matters.

This is the lemma that lifts a per-site reweighting to `StrataGenerators.Stmt.genStmt`: after
`delta`-unfolding the block's shared auxiliary, both sides are `WellFounded.fix` applied to
functionals that differ only in their `frequency` weights, and the *same* `ih` is bound in both — so
`funext`, a `cases` on the `PSum`, and `frequency_congr_weights` per site finish it. See
`StrataGenerators.SetGen.TuningPrototypes`. -/
theorem wellFounded_fix_congr {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
    (hwf : WellFounded r) {F F' : ∀ x, (∀ y, r y x → C y) → C x} (h : F = F') :
    WellFounded.fix hwf F = WellFounded.fix hwf F' := by
  subst h; rfl

/-- And for `Nat.brecOn`, which the equation compiler uses for a generator that recurses
structurally on a `Nat` — `genLMonoTy` and `genLExprBase` both do. Same shape as the two `fix`
congruences: the recursive results arrive in a `Nat.below` bundle that is one bound variable on both
sides, so equality of the step functions is all that is needed. -/
theorem brecOn_congr {motive : Nat → Sort u}
    {F F' : (n : Nat) → @Nat.below motive n → motive n} (h : F = F') (n : Nat) :
    @Nat.brecOn motive n F = @Nat.brecOn motive n F' := by
  subst h; rfl

/-- Soundness-and-completeness transfers along a support equation. Given a proof that the tuned
generator has the same support as the untuned one (`SetGen.frequency_congr_weights` and
`SetGen.fix_congr` supply the stronger *generator* equality, whose `congrArg support` is exactly
this), an `IsSoundAndComplete` for the untuned generator lifts to the tuned one.

Ported from `IsSoundAndComplete.of_support_eq` (`Basalt.Laws`) to `SetGen.Set`; here
`IsSoundAndComplete` is a class, so this is a derived instance-producing lemma. -/
theorem IsSoundAndComplete.of_support_eq {g g' : Set α} {P : α → Prop}
    (h : support g' = support g) (hg : IsSoundAndComplete g P) :
    IsSoundAndComplete g' P where
  support_iff a := by rw [h]; exact hg.support_iff a

end SetGen
