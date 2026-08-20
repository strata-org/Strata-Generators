import Strata.Util.ListUtils

/-!
# A local fixed-point fact about `List.dedup`

Strata's `List.dedup` (in `Strata.Util.ListUtils`) is used by `genFunction` to make
`typeArgs` and the input identifiers `Nodup`. Its lemmas live in
`Strata.Util.ListUtilsProps`, which this package reaches transitively via
`Strata.DL.Lambda.LTyUnify`, so `List.nodup_dedup` and `List.mem_of_dedup` are used
directly at their call sites rather than re-proved here. Note that upstream's
`mem_of_dedup` is oriented `a ∈ l ↔ a ∈ l.dedup`.

The one fact upstream does not provide is the fixed-point law below, which
completeness needs: a well-typed function's `Nodup` `typeArgs`/inputs have to be
reachable by the dedup-based generators. It is a short induction on `List.dedup`'s
definition (`| a :: as => let as := as.dedup; if a ∈ as then as else a :: as`).

Mathlib also defines `List.dedup`, with a fixed-point lemma among others, but it is
unavailable here: once `Strata.Util.ListUtils` is in the environment, importing a
Mathlib module that defines `List.dedup` fails with an "environment already
contains `List.dedup`" error. `List.nodup_cons` comes from core/Batteries (no
clash), so this file compiles in the `HasTypeAGen`-importing environment.
-/

namespace StrataGenerators.Dedup

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
