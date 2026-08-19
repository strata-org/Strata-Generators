import Strata.Util.ListUtils

/-!
# Local facts about `List.dedup`

Strata's `List.dedup` (in `Strata.Util.ListUtils`) is used by `genFunction` to make
`typeArgs` and the input identifiers `Nodup`. Mathlib also defines `List.dedup`
with a rich lemma set, but once `Strata.Util.ListUtils` is in the environment,
importing a Mathlib module that defines `List.dedup` fails with an "environment
already contains `List.dedup`" error.

The `FunctionHasTypeAGen` proofs (which transitively import both
`Strata.Util.ListUtils` and Mathlib via `HasTypeAGen`) are therefore stuck with
Strata's `dedup` definition rather than Mathlib's. We only need three basic
facts, all provable by a short induction on `List.dedup`'s definition
(`| a :: as => let as := as.dedup; if a ∈ as then as else a :: as`), so we prove
them locally here. `List.nodup_cons` and `List.mem_cons` come from core/Batteries
(no collision), so these compile in the `HasTypeAGen`-importing environment.

Note: as of Strata `b3ae917`, upstream's own dedup lemmas (`nodup_dedup`,
`mem_of_dedup`, …) moved to `Strata.Util.ListUtilsProps` and are now `public`, so
`nodup_dedup` and `mem_dedup` below could be replaced by imports. `dedup_eq_self`
has no upstream counterpart. Left as-is to keep this fix minimal.
-/

namespace StrataGenerators.Dedup

/-- `List.dedup` always produces a `Nodup` list. -/
theorem nodup_dedup {α} [DecidableEq α] (l : List α) : l.dedup.Nodup := by
  induction l with
  | nil => simp [List.dedup]
  | cons a as ih =>
    simp only [List.dedup]; split
    · exact ih
    · rename_i h; exact List.nodup_cons.mpr ⟨h, ih⟩

/-- Membership is preserved by `List.dedup` in both directions. -/
theorem mem_dedup {α} [DecidableEq α] (l : List α) (a : α) :
    a ∈ l.dedup ↔ a ∈ l := by
  induction l with
  | nil => simp [List.dedup]
  | cons b bs ih =>
    simp only [List.dedup]; split
    · rename_i h
      rw [ih, List.mem_cons]
      refine ⟨fun hh => Or.inr hh, fun hh => ?_⟩
      rcases hh with heq | hmem
      · subst heq; exact ih.mp h
      · exact hmem
    · rename_i h; rw [List.mem_cons, List.mem_cons, ih]

/-- A `Nodup` list is a fixed point of `List.dedup`. Needed for completeness:
    a well-typed function's `Nodup` `typeArgs`/inputs are reachable by the
    dedup-based generators. -/
theorem dedup_eq_self {α} [DecidableEq α] (l : List α) (h : l.Nodup) :
    l.dedup = l := by
  induction l with
  | nil => simp [List.dedup]
  | cons a as ih =>
    obtain ⟨hnotin, hnd⟩ := List.nodup_cons.mp h
    simp only [List.dedup]; rw [ih hnd]
    simp [hnotin]

end StrataGenerators.Dedup
