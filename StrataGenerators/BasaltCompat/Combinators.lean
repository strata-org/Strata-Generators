/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import Basalt.Combinators

open Lean.Order RandomChoice

/-!
# The option generators that Basalt no longer ships

Basalt's `lean-4.29` reorganization moved `biasedOptionGen` and `optionGen` out of the library and
into `BasaltTest/OptionGen.lean`, on the grounds that they are fixtures with no law of their own.
The generators in this package call both, so this file keeps them, verbatim from Basalt.

They are defined at the root namespace, where Basalt had them, because the call sites name them
unqualified. `StrataGenerators.BasaltCompat.Support` has their support lemmas; this file has no
`SPMF` import, so that a generator definition need not pull the proof API in.

See `StrataGenerators.weightedOptionGen` for the variant whose `some`/`none` split is a `frequency`,
which is what `@[tunable]` can address.
-/

/-- Lifts a generator of `α`s into a generator of `Option α`s which returns `some <$> g` with
probability `r`. Formerly `Basalt.Combinators.biasedOptionGen`.

The `some` branch uses an explicit `bind` rather than `<$>` because `Lean.Order` has no
monotonicity lemma for `<$>`. -/
def biasedOptionGen [Gen G] (r : Rat) (g : G α) : G (Option α) := do
  if ← RandomChoice.coin r then do
    let x ← g
    pure (some x)
  else
    pure none

/-- Lets `biasedOptionGen` appear in a `partial_fixpoint`. -/
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

/-- Lifts a generator of `α`s into a generator of `Option α`s which returns `none` with probability
one half. Formerly `Basalt.Combinators.optionGen`. -/
def optionGen [Gen G] (g : G α) : G (Option α) :=
  biasedOptionGen (1 / 2) g

/-- Lets `optionGen` appear in a `partial_fixpoint`. -/
@[partial_fixpoint_monotone]
theorem monotone_optionGen [Gen G] [Lean.Order.PartialOrder γ]
    (g : γ → G α) (hg : monotone g) :
    monotone (fun x => optionGen (g x)) := by
  unfold optionGen
  exact monotone_biasedOptionGen g hg

