import Plausible

/-!
# Retry-on-failure wrappers for fallible `Plausible.Gen`s

Two definitions, in their own module so that both test-facing consumers —
`StrataGenerators.TestScaffold` (shared by the LSpec and Plausible-only drivers)
and `StrataGenerators.TycheViz` (which deliberately does *not* import the
scaffold) — can use the same wrappers instead of keeping copies in sync. This
module depends only on `Plausible`, so importing it adds nothing to either
module's dependency footprint.

`retryGen` retries a whole generator; `retryGenArg` retries a *parameterized* one
and is the shape `genLExpr`'s `retryCont` parameter expects.
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

/-- `retryGen` lifted over a generator that takes a parameter: the **retry
    continuation** to hand to `genLExpr`'s `retryCont`, which retries a failed
    *subterm* instead of discarding the whole term.

    `genLExpr` invokes this on whichever generator it would have used in
    Indir/IndirPoly argument position, and threads it into its own recursive call,
    so retrying applies at **every** nesting level. That matters because generation
    failure compounds multiplicatively with depth: without it, one unfillable leaf
    deep inside a term forces the caller's outer `retryGen` to redraw the entire
    term from scratch.

    Note this covers rather more than a single argument. At depth `n + 1` the
    argument generator *is* the whole level-`n` generator, so a retry here also
    resamples `genIndirPoly`'s type-variable instantiation (`sampledTys`) — which is
    what rescues targets whose chosen instantiation was unfillable no matter how
    often a fixed argument type is retried.

    Definitionally this is just `retryGen` applied pointwise
    (`retryGenArg fuel g σ = retryGen fuel (g σ)`); it exists as a named definition
    because that is the type `retryCont` requires. Callers should keep their outer
    `retryGen` as well — `retryCont` reaches every nested level but not the root
    draw itself. -/
def retryGenArg (fuel : Nat) (g : α → Plausible.Gen β) : α → Plausible.Gen β :=
  fun a => retryGen fuel (g a)
