import Plausible

/-!
# The wrappers that retry a `Plausible.Gen` after a failure

This module holds two definitions. It is a separate module, so that both consumers
in the test code can use the same wrappers and no one must keep two copies in
agreement. `StrataGenerators.TestScaffold` is the first consumer, and both drivers
share it. `StrataGenerators.TycheViz` is the second, and it does *not* import the
scaffold. This module depends only on `Plausible`, so an import of it adds no
dependency to either consumer.

`retryGen` retries a whole generator. `retryGenArg` retries a generator that takes
a parameter, and it has the shape that the `retryCont` parameter of `genLExpr`
needs.
-/

/-- Retries a `Plausible.Gen` that can fail, up to `fuel` times. After each failure
    the wrapper advances the random number generator, so the next attempt sees
    fresh randomness.

    The failure handler threads `Rand.next` through, in the same way as
    `Gen.runUntil`. This step is necessary: the `Gen` monad of Plausible rolls the
    state of the random number generator back when it catches an exception, so
    without `Rand.next` the next attempt makes the same draw again.

    The wrapper uses `O(1)` memory, and its time is proportional to the number of
    attempts before the first success. -/
def retryGen (fuel : Nat) (g : Plausible.Gen α) : Plausible.Gen α :=
  match fuel with
  | 0 => g
  | fuel + 1 => tryCatch g (fun _ => do let _ ← Plausible.Rand.next; retryGen fuel g)

/-- `retryGen` over a generator that takes a parameter. This is the **retry
    continuation** for the `retryCont` parameter of `genLExpr`. It retries a
    *subterm* that failed, and it does not discard the whole term.

    `genLExpr` calls it on the generator for an argument of `Indir` or of
    `IndirPoly`, and it threads the result into its own recursive call. A retry
    therefore happens at **each** level of the nesting. This matters, because the
    chance of a failure grows with the depth of a term. Without it, one leaf that
    the generator cannot fill, deep inside a term, makes the outer `retryGen` of
    the caller draw the whole term again.

    The continuation covers more than one argument. At depth `n + 1` the generator
    for an argument *is* the whole generator for level `n`. A retry here therefore
    also draws the instance of the type variables of `genIndirPoly`, which is
    `sampledTys`. This is what rescues a target whose instance the generator cannot
    fill, however often it retries a fixed argument type.

    The definition is `retryGen` at each point: `retryGenArg fuel g σ` is
    `retryGen fuel (g σ)`. It has a name because that is the type that `retryCont`
    needs. A caller must also keep its outer `retryGen`, because `retryCont`
    reaches each nested level but not the draw at the root. -/
def retryGenArg (fuel : Nat) (g : α → Plausible.Gen β) : α → Plausible.Gen β :=
  fun a => retryGen fuel (g a)
