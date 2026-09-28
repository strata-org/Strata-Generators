/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import Basalt.Combinators

open Lean.Order RandomChoice

/-!
# The option combinators Basalt's library no longer holds

`biasedOptionGen` and `optionGen` left the Basalt library for `BasaltTest/OptionGen.lean`, where they
are fixtures that pin the walk's behaviour on a combinator with no law. The generators in this package
draw from them, so the definitions live here.

This module imports `Basalt.Combinators` only, and therefore no `Basalt.SPMF` and no Mathlib. That is
deliberate: `StrataGenerators.HasTypeAGen.Core` and the other generator-definition modules import it
and stay Mathlib-free. `StrataGenerators.BasaltCompat` holds the support lemmas, which do need
`Basalt.SPMF.Support`.
-/

/-- Lift a generator of `α`s to a generator of `Option α`s that gives `some x` with probability `r`.

    The `some` branch is an explicit `bind` rather than `<$>`, because `Lean.Order` has no
    monotonicity lemma for `<$>`. Carried over from Basalt, which now keeps this combinator in
    `BasaltTest/OptionGen.lean`. -/
def biasedOptionGen [Gen G] (r : Rat) (g : G α) : G (Option α) := do
  if ← RandomChoice.coin r then do
    let x ← g
    pure (some x)
  else
    pure none

/-- Lift a generator of `α`s to a generator of `Option α`s that gives `none` half of the time. -/
def optionGen [Gen G] (g : G α) : G (Option α) :=
  biasedOptionGen (1 / 2) g

/-- What a `partial_fixpoint` generator needs in order to call `biasedOptionGen`. -/
@[partial_fixpoint_monotone]
theorem monotone_biasedOptionGen [Gen G] [Lean.Order.PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => biasedOptionGen r (g x)) := by
  unfold biasedOptionGen
  apply monotone_bind
  · apply Lean.Order.monotone_const
  · apply monotone_of_monotone_apply
    intro b
    cases b <;> simp
    · apply Lean.Order.monotone_const
    · apply monotone_bind
      · assumption
      · apply Lean.Order.monotone_const

/-- What a `partial_fixpoint` generator needs in order to call `optionGen`. -/
@[partial_fixpoint_monotone]
theorem monotone_optionGen [Gen G] [Lean.Order.PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => optionGen (g x)) := by
  unfold optionGen
  apply monotone_biasedOptionGen
  assumption

