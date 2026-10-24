import Strata.Util.ListUtils

/-!
# A fixed point of `List.uniq`

`genFunction` uses `List.uniq` of Strata, a duplicate-removing function, to make `typeArgs` and
the input identifiers hold no duplicate. Strata proves that the result holds no duplicate
(`List.nodup_uniq`) and that it has the same members (`List.mem_of_dedup`), but gives no law about
a fixed point. The proof of completeness needs one: the generators must be able to reach the
`typeArgs` and the inputs of a well-typed function, and those lists hold no duplicate.
-/

namespace StrataGenerators.Dedup

/-- A list that holds no duplicate is a fixed point of `List.uniq`. Proved by induction on the
    list. -/
theorem dedup_eq_self {α} [DecidableEq α] (l : List α) (h : l.Nodup) :
    l.uniq = l := by
  induction l with
  | nil => simp [List.uniq]
  | cons a as ih =>
    obtain ⟨hnotin, hnd⟩ := List.nodup_cons.mp h
    simp only [List.uniq]; rw [ih hnd]
    simp [hnotin]

end StrataGenerators.Dedup
