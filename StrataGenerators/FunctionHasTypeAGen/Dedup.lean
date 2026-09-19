import Strata.Util.ListUtils

/-!
# A local fact about a fixed point of `List.uniq`

`genFunction` uses the `List.uniq` of Strata to make `typeArgs` and the input identifiers
hold no duplicate. The lemmas for that function are in another module of Strata, which this
package reaches through its other imports. `List.nodup_uniq` and `List.mem_of_dedup`
therefore appear at their call sites, and this file does not prove them again. Note that the
`mem_of_dedup` of upstream reads `a ∈ l ↔ a ∈ l.uniq`.

Upstream gives no law about a fixed point, and the proof of completeness needs one: the
generators that use `uniq` must be able to reach the `typeArgs` and the inputs of a
well-typed function, and those lists hold no duplicate. The theorem below is a short
induction on the definition of `List.uniq`, which is
`| a :: as => let as := as.uniq; if a ∈ as then as else a :: as`.

Mathlib also defines `List.uniq`, with a lemma about a fixed point. This file cannot use
that lemma. Once the module of Strata that defines `List.uniq` is in the environment, an
import of a Mathlib module that also defines `List.uniq` fails with the error that the
environment already holds `List.uniq`. `List.nodup_cons` comes from the core library and
from Batteries, and it therefore has no such collision. This file compiles in the
environment that `HasTypeAGen` imports.
-/

namespace StrataGenerators.Dedup

/-- A list that holds no duplicate is a fixed point of `List.uniq`. The proof of completeness needs
    this theorem: the generators that use `uniq` must be able to reach the `typeArgs` and the inputs
    of a well-typed function. -/
theorem dedup_eq_self {α} [DecidableEq α] (l : List α) (h : l.Nodup) :
    l.uniq = l := by
  induction l with
  | nil => simp [List.uniq]
  | cons a as ih =>
    obtain ⟨hnotin, hnd⟩ := List.nodup_cons.mp h
    simp only [List.uniq]; rw [ih hnd]
    simp [hnotin]

end StrataGenerators.Dedup
