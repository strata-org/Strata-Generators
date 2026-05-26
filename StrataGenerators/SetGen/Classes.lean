/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein

Vendored from https://github.com/hgoldstein95/basalt (SetGen branch, not yet on `main`).
-/
import StrataGenerators.SetGen.Support

/-!
# SetGen Correctness Classes

This file defines the correctness property for `Set`-based generators.

## Main Definitions

- `SetGen.IsSoundAndComplete` — A generator is sound and complete with respect to a predicate `P`
  if membership in the generator's support is equivalent to satisfying `P`.
-/

namespace SetGen

/-- A `Set`-based generator `g` is sound and complete with respect to a predicate `P` if
    the support of `g` is exactly the set of values satisfying `P`. -/
class IsSoundAndComplete (g : Set α) (P : α → Prop) where
  support_iff : ∀ a, a ∈ SetGen.support g ↔ P a

end SetGen
