/-
Vendored from https://github.com/hgoldstein95/basalt PR #8
(https://github.com/hgoldstein95/basalt/pull/8), not yet merged.

Once PR #8 lands and the pinned Basalt rev is bumped, this file should be deleted
and `vectorOf` / `listOfMaxLength` imported from `Basalt.Combinators` instead.
-/
import Basalt.Gen
import Basalt.Combinators

open RandomChoice

/-!
# List-generation combinators

`Gen`-generic combinators for generating lists, ported from Basalt PR #8. The
`SetGen.Set` support characterizations live in `StrataGenerators/SetGen/Support.lean`.

- `vectorOf n g` — a list of *exactly* `n` elements, each drawn from `g`.
- `listOfMaxLength n g` — a list of length *at most* `n` (possibly empty), each
  element drawn from `g`. Implemented via `vectorOf` after choosing a length in
  `[0, n]`. A user-supplied bound is required because Basalt has no ambient
  "generator size" à la QuickChick's `sized`.
-/

/-- Generate a list of exactly `n` elements, each produced by `g`. -/
def vectorOf [Gen G] (n : Nat) (g : G α) : G (List α) :=
  List.foldr (fun m acc => do
    let x ← m
    let xs ← acc
    pure (x :: xs)) (pure []) (List.replicate n g)

/-- Generate a list of length at most `n` (possibly empty), each element from `g`. -/
def listOfMaxLength [Gen G] (n : Nat) (g : G α) : G (List α) := do
  let ⟨k, _⟩ ← ULift.down <$> RandomChoice.choose 0 n (Nat.zero_le n)
  vectorOf k g

/-- `vectorOf 0 g` produces the empty list. -/
@[simp] theorem vectorOf_zero [Gen G] (g : G α) : vectorOf 0 g = pure [] := rfl

/-- One-step unfolding of `vectorOf` at a successor length. -/
theorem vectorOf_succ [Gen G] (n : Nat) (g : G α) :
    vectorOf (n + 1) g = (do
      let x ← g
      let xs ← vectorOf n g
      pure (x :: xs)) := by
  simp only [vectorOf, List.replicate, List.foldr]
