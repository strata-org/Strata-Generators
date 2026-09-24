/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import Basalt.SPMF.Expect.Obs
import Basalt.SPMF.Mass

open Lean.Order RandomChoice NNReal ENNReal

/-!
# Expectation and mass lemmas that Basalt no longer ships

The companion of `StrataGenerators.BasaltCompat.Support` at the other two interpretations. Basalt's
`lean-4.29` reorganization replaced the `le_mass_*` family by the `mass_bound` walk and restated the
expectation laws on `chooseNat` rather than on the raw `choose`, which dropped the two lemmas below.
Both are re-derived from what Basalt kept: `expect_choose` from `Mix.range_average`, and
`mass_elements` from `expect_elements`.
-/

namespace SPMF

/-- Expectation over a uniform `choose` is the average over the range. The summand is taken in `Nat`
form `m` (with `hm` bridging) so callers avoid `choose`'s `ULift` subtype; `Basalt`'s surviving
`expect_chooseNat` is this lemma with the bridge already applied. -/
theorem expect_choose {lo hi : Nat} (h : lo ≤ hi)
    (f : ULift.{u} {x : Nat // lo ≤ x ∧ x ≤ hi} → ℝ≥0∞) (m : Nat → ℝ≥0∞)
    (hm : ∀ a, f a = m a.down.val) :
    expect (choose lo hi h : SPMF _) f
      = (∑ x ∈ Finset.Icc lo hi, m x) / ((hi - lo + 1 : ℕ) : ℝ≥0∞) := by
  rw [funext hm]
  exact (congrFun (expectObs.map_choose lo hi h) _).trans (Mix.range_average lo hi m)

/-- `elements` always terminates: it draws one index and returns one element. Basalt used to state
this as the `@[gen_rule]` `le_mass_elements`, with the note that `elements` destructures its draw
with a `match` that no rule walks into; `expect_elements` is now the way past that `match`. -/
theorem mass_elements {xs : List α} {hne : xs ≠ []} :
    (elements xs hne : SPMF α).mass = 1 := by
  have hlen : (xs.length : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (List.length_pos_iff.mpr hne))
  rw [← expect_one, expect_elements hne, List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
  exact ENNReal.div_self hlen (ENNReal.natCast_ne_top _)

/-- `le_mass_elements` under Basalt's old name, so that a `mass` bound reads the same at `elements`
as it does at the combinators Basalt still covers. -/
theorem le_mass_elements {xs : List α} {hne : xs ≠ []} :
    (1 : ℝ≥0∞) ≤ (elements xs hne : SPMF α).mass :=
  mass_elements.ge

end SPMF
