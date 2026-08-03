import Plausible

/-!
# Retry-on-failure wrapper for fallible `Plausible.Gen`s

A single definition, in its own module so that both test-facing consumers —
`StrataGenerators.TestScaffold` (shared by the LSpec and Plausible-only drivers)
and `StrataGenerators.TycheViz` (which deliberately does *not* import the
scaffold) — can use the same wrapper instead of keeping copies in sync. This
module depends only on `Plausible`, so importing it adds nothing to either
module's dependency footprint.
-/

/-- Retry a fallible `Plausible.Gen` up to `fuel` times, advancing the RNG on
    each failure so the retry sees fresh randomness.

    This replaces the `Gen.backtrack (List.replicate n (1, g))` idiom that the
    `Arbitrary` instances and Tyche panels used to wrap their generators.
    `backtrack` makes progress only by *shrinking* the weighted list it walks — so
    it must materialize an `n`-element list and its per-draw cost is `O(n)` even
    when the first attempt succeeds. `retryGen` instead threads `Rand.next`
    through the failure handler exactly as `Gen.runUntil` does (Plausible's `Gen`
    rolls the RNG state back on a caught exception, so without an explicit
    `Rand.next` the retry would replay the same failing draw). It is `O(1)` in
    memory and `O(attempts-until-success)` in time, and — since every `replicate`
    entry was the *same* generator `g` — it is distribution-identical to the list
    it replaces. -/
def retryGen (fuel : Nat) (g : Plausible.Gen α) : Plausible.Gen α :=
  match fuel with
  | 0 => g
  | fuel + 1 => tryCatch g (fun _ => do let _ ← Plausible.Rand.next; retryGen fuel g)
