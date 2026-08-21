/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein

Vendored from https://github.com/hgoldstein95/basalt, from the `SetGen` branch.
-/
import StrataGenerators.SetGen.Support

/-!
# The correctness classes of `SetGen`

This file defines the property of correctness for a generator on `Set`.

## The main definitions

- `SetGen.IsSoundAndComplete`: a generator is sound and complete against a predicate `P` when
  membership in the support of the generator is equivalent to `P`.
-/

namespace SetGen

/-- A generator `g` on `Set` is sound and complete against a predicate `P` when the support of `g`
    is exactly the set of the values that satisfy `P`. -/
class IsSoundAndComplete (g : Set α) (P : α → Prop) where
  support_iff : ∀ a, a ∈ SetGen.support g ↔ P a

end SetGen
