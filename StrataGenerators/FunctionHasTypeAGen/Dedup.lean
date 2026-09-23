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

Mathlib defines a separate `List.dedup`, with a lemma about a fixed point. That lemma is
about a different constant, so this file cannot use it, whatever the imports are.
`List.nodup_cons` comes from the core library and from Batteries. This file compiles in the
environment that `HasTypeAGen` imports.
-/

namespace StrataGenerators.Dedup

/-- A list that holds no duplicate is a fixed point of `List.uniq`. The proof of completeness needs
    this theorem: the generators that use `uniq` must be able to reach the `typeArgs` and the inputs
    of a well-typed function. -/
theorem uniq_eq_self {α} [DecidableEq α] (l : List α) (h : l.Nodup) :
    l.uniq = l := by
  induction l with
  | nil => simp [List.uniq]
  | cons a as ih =>
    obtain ⟨hnotin, hnd⟩ := List.nodup_cons.mp h
    simp only [List.uniq]; rw [ih hnd]
    simp [hnotin]

end StrataGenerators.Dedup
