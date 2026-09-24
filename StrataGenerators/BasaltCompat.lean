/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import StrataGenerators.BasaltCompat.Combinators
import StrataGenerators.BasaltCompat.Measure
import StrataGenerators.BasaltCompat.Support

/-!
# What Basalt's `lean-4.29` reorganization dropped

Import root for the two files that keep the pieces of Basalt's API this package still uses:
`Combinators` has `biasedOptionGen` and `optionGen`, which Basalt moved to `BasaltTest`; `Support`
has the support lemmas Basalt stopped stating; and `Measure` has the two it stopped stating about
expectation and mass. All are verbatim restatements; see each file for the detail.
-/
