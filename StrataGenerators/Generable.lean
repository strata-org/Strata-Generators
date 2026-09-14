/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import Basalt.Gen

/-!
# `Generable`: a generator polymorphic in the interpretation

Each type the suite generates has a *canonical* generator that is polymorphic in the Basalt `Gen`
interpretation `G` — the same term runs at `Plausible.Gen` (for `lake test`), and is reasoned about at
`SetGen` for the correctness proofs. `Generable` names that canonical generator once, so it need not be
duplicated across the `Arbitrary` instance and any other consumer.

Convention: the canonical generator is **retry-free** (it uses `genLExpr`'s default `retryCont = id`),
because retrying a failed draw needs the interpretation's own failure mechanism and is therefore a
per-interpretation *harness* concern, not part of the generator. The Plausible `Arbitrary` instances
add that retry (`retryGen` / `retryGenArg`) on top; another interpretation adds its own (or none).
-/

namespace StrataGenerators

/-- A canonical generator for `α`, polymorphic in the Basalt `Gen` interpretation `G`. `size` is the
suite's size knob (e.g. expression depth); each instance maps it to that generator's parameters. -/
class Generable (α : Type) where
  gen : (G : Type → Type) → [Gen G] → (size : Nat) → G α

end StrataGenerators
