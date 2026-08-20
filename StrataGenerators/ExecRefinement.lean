import StrataGenerators.SetGen
import StrataGenerators.RetryGenSupport
import Basalt.PlausibleGen

/-!
# Execution refines the `Set` semantics

Every soundness/completeness theorem in this development is stated about
`SetGen.Set`, but the test harness runs `Plausible.Gen`. This module connects the
two, so that a theorem about the `Set` support says something about the executable
generator.

The bridge is the relation `Refines p s size`:

> every value `p` can return (at some rng seed, at this size) lies in `SetGen.support s`.

`Refines` is proved to be *compositional*: it is preserved by `pure`, `bind`, `map`,
`choose`, `pick`, `default`, and — the payoff — by `retryGen`/`retryGenArg`. So a
`[Gen G]`-polymorphic generator built from those combinators refines its own
`SetGen.Set` instantiation when run at `Plausible.Gen`, and the proven support results
upper-bound what execution can produce.

## This is refinement, *not* adequacy

Deliberately not called "adequacy". In programming-language semantics an adequate
translation is one that is both sound *and* complete — the source and target agree on
observable behaviour in both directions. What is proved here is only the sound half:

    runSupport (p at Plausible.Gen)  ⊆  SetGen.support (p at SetGen.Set)

i.e. execution never escapes the proven support, which is the one-directional
containment usually called *refinement*. Calling it adequacy would claim the ⊇
direction too, and that is exactly what is missing.

The ⊆ direction is the one that carries the *soundness* results, and it is the one
worth having on its own: combined with `genLExpr_sound`, it gives "every term the
harness draws is well-typed" as a fact about the executable generator.

The reverse inclusion (⊇, every `Set`-reachable term is reachable at some seed) is
**not** provable here, and the obstruction is not about generators at all. It reduces
to surjectivity of `randNat`/`RandomGen.next` over each `choose` range — a claim about
`StdGen`'s arithmetic. `Init.Data.Random.randNat` is built on
`private partial def randNatAux`, which has no equation lemmas and is irreducible in
proofs (`(randNat (mkStdGen 1) 3 7).1 = 5` cannot be closed by `rfl`). Empirically the
ranges *are* covered — sampling `choose 3 7` over 300 seeds yields all of
`[3,4,5,6,7]` — but that is a test, not a proof, and it would in any case be a theorem
about Lean's RNG rather than about this development. Recorded here so the asymmetry is
a documented boundary rather than an apparent oversight.

Note the ⊆ direction is exactly the one that composes. `Refines` threads through
`bind` because the intermediate rng state is *existentially* witnessed on both sides
(`refines_bind` below). The corresponding *equality* does not compose, for the reason
recorded in `RetryGenSupport`: in `p >>= f` the state reaching `f` is determined by
`p`, so two independently-chosen witness seeds need not agree.
-/

open Lambda RandomChoice Plausible RetryGenSupport

namespace ExecRefinement

/-! ## Structural lemmas about `Plausible.Gen`

`Plausible.Gen`'s monad instances come from stacked transformers, so applying a
`bind`/`map` to a state and size needs manual unfolding. -/

/-- `bind` at `Plausible.Gen` threads the rng state: run `p`, then run the
    continuation at the *resulting* state. -/
theorem bind_apply {α β} (p : Plausible.Gen α) (f : α → Plausible.Gen β)
    (sg : ULift StdGen) (size : ULift Nat) :
    (p >>= f) sg size
      = (match p sg size with
         | .ok (a, sg') => f a sg' size
         | .error e => .error e) := by
  simp only [bind, StateT.bind, ReaderT.bind, Except.bind]
  cases p sg size <;> rfl

/-! ## The refinement relation -/

/-- `p` **refines** `s` at `size` when every value `p` can return — over all rng
    seeds — lies in `s`'s support.

    Read as: *executing `p` cannot produce anything the `Set` semantics does not
    already predict.* This is the property that lets a theorem about
    `SetGen.support` constrain the harness.

    One-directional by design: see the module docstring on why this is refinement
    rather than adequacy. -/
def Refines {α} (p : Plausible.Gen α) (s : SetGen.Set α) (size : ULift Nat) : Prop :=
  ∀ a, runSupport p size a → a ∈ SetGen.support s

/-- `pure` refines `pure`: the only reachable value is the one returned. -/
theorem refines_pure {α} (a : α) (size : ULift Nat) :
    Refines (pure a : Plausible.Gen α) (pure a : SetGen.Set α) size := by
  rintro b ⟨sg, sg', h⟩
  simp only [pure, StateT.pure, ReaderT.pure] at h
  cases h
  rfl

/-- **Refinement composes through `bind`.** This is the load-bearing lemma: it is why
    refinement of a whole generator follows from refinement of its primitives.

    The proof extracts the intermediate state `sgmid` produced by `p` and feeds it to
    the continuation's hypothesis. The `Set` side needs only *existence* of a witness
    value, which `hp` supplies — so unlike the corresponding equality statement, no
    agreement between independently-chosen seeds is required. -/
theorem refines_bind {α β} (p : Plausible.Gen α) (s : SetGen.Set α) (size : ULift Nat)
    (f : α → Plausible.Gen β) (g : α → SetGen.Set β)
    (hp : Refines p s size) (hf : ∀ a, Refines (f a) (g a) size) :
    Refines (p >>= f) (s >>= g) size := by
  rintro b ⟨sg, sg', h⟩
  rw [bind_apply] at h
  split at h
  · rename_i a sgmid heq
    exact ⟨a, hp a ⟨sg, sgmid, heq⟩, hf a b ⟨sgmid, sg', h⟩⟩
  · exact absurd h (by simp)

/-- `map` refines `map`, via `bind`/`pure`. -/
theorem refines_map {α β} (p : Plausible.Gen α) (s : SetGen.Set α) (size : ULift Nat)
    (φ : α → β) (hp : Refines p s size) :
    Refines (φ <$> p) (φ <$> s) size := by
  rintro b ⟨sg, sg', h⟩
  -- `map` at both layers is `bind (pure ∘ φ)`
  have hb : ((p >>= fun a => pure (φ a)) : Plausible.Gen β) sg size = .ok (b, sg') := h
  rw [bind_apply] at hb
  split at hb
  · rename_i a sgmid heq
    refine ⟨a, hp a ⟨sg, sgmid, heq⟩, ?_⟩
    simp only [pure, StateT.pure, ReaderT.pure] at hb
    cases hb
    rfl
  · exact absurd hb (by simp)

/-- **`choose` refines `choose`, and unconditionally so.** `SetGen.Set`'s `choose` has
    support *every* element of the subtype `{x // lo ≤ x ∧ x ≤ hi}`, and any value
    `Plausible.Gen` returns is such an element — it carries its own range proof. So
    the hypothesis about the drawn value is not even needed.

    This is the base case that makes the whole development go through: the sole
    randomness primitive in `Basalt`'s `Gen` class refines its `Set` reading for free.

    Note this is also precisely where the ⊇ direction would have to be established,
    and where it cannot be: `Set`'s `choose` reaches the whole range by definition,
    whereas showing `Plausible`'s does needs `randNat` to be surjective onto it. -/
theorem refines_choose (lo hi : Nat) (h : lo ≤ hi) (size : ULift Nat) :
    Refines (RandomChoice.choose lo hi h : Plausible.Gen _)
            (RandomChoice.choose lo hi h : SetGen.Set _) size := by
  rintro v -
  exact ⟨v.down.2.1, v.down.2.2⟩

/-- `default` (generation failure) refines `default` (`∅`) *vacuously*: the failing
    `Plausible.Gen` returns nothing, so there is nothing to place in the empty
    support.

    This is what makes the 27 `else default` sites in `genLExprBase` harmless here —
    the two interpretations of `default` (panic vs `∅`) agree exactly on
    reachability. -/
theorem refines_default {α} [Inhabited α] (size : ULift Nat) :
    Refines (default : Plausible.Gen α) (default : SetGen.Set α) size := by
  rintro a ⟨sg, sg', h⟩
  simp only [default, throw, throwThe, MonadExceptOf.throw,
             Function.comp_def, StateT.lift, bind, ReaderT.bind, Except.bind] at h
  exact absurd h (by simp)

/-- `pick` refines `pick` when both branches do: a binary choice cannot reach outside
    the union of its branches' supports. -/
theorem refines_pick {α} (p q : Plausible.Gen α) (s t : SetGen.Set α) (size : ULift Nat)
    (hp : Refines p s size) (hq : Refines q t size) :
    Refines (pick (fun () => p) (fun () => q))
            (pick (fun () => s) (fun () => t)) size := by
  rintro a ⟨sg, sg', h⟩
  rw [SetGen.support, SetGen.pick_mem_iff]
  -- `pick` is `choose 0 1 >>= fun i => if i.down.val == 0 then _ else _`
  simp only [RandomChoice.pick, bind_apply] at h
  split at h
  · rename_i v sgmid heq
    by_cases hv : v.down.val == 0
    · simp only [hv, if_pos] at h
      exact Or.inl (hp a ⟨sgmid, sg', by simpa using h⟩)
    · simp only [hv] at h
      exact Or.inr (hq a ⟨sgmid, sg', by simpa using h⟩)
  · exact absurd h (by simp)

/-! ## The payoff: retrying preserves refinement -/

/-- **`retryGen` preserves refinement.** Wrapping a generator in retries cannot make
    it reach outside its `Set` support, because `runSupport_retryGen` says retrying
    does not change reachability at all.

    This is the fact that justifies running `retryGen`/`retryGenArg` in the harness
    while reasoning about the plain generator: the proven support still bounds what
    execution can produce. -/
theorem refines_retryGen {α} (fuel : Nat) (p : Plausible.Gen α) (s : SetGen.Set α)
    (size : ULift Nat) (hp : Refines p s size) :
    Refines (retryGen fuel p) s size := by
  intro a ha
  exact hp a (runSupport_retryGen fuel p size ▸ ha)

/-- `retryGenArg` preserves refinement pointwise — the form `genLExpr`'s `retryCont`
    takes. If the argument generator refined its `Set` reading at each type, the
    retrying one still does. -/
theorem refines_retryGenArg {α β} (fuel : Nat) (f : α → Plausible.Gen β)
    (g : α → SetGen.Set β) (size : ULift Nat)
    (hf : ∀ a, Refines (f a) (g a) size) (a : α) :
    Refines (retryGenArg fuel f a) (g a) size :=
  refines_retryGen fuel (f a) (g a) size (hf a)

/-! ## Scope

`refines_choose` and `refines_default` are the base cases; `refines_bind`,
`refines_map`, and `refines_pick` propagate refinement through the combinators
`Basalt`'s `Gen` class provides; `refines_retryGen`/`refines_retryGenArg` are the
results that cover the production harness.

What is deliberately *not* attempted: a single mechanized
`Refines (genLExpr (G := Plausible.Gen) …) (genLExpr (G := SetGen.Set) …)`. Proving it
means re-doing `genLExpr`'s entire branch structure — every `frequency` weight list, the
`elements`/`mapM` inside `genIndir`/`genIndirPoly`, and all ~27 `default` sites in
`genLExprBase` — against the lemmas above. That is a large mechanical induction rather
than a new idea; the lemmas here are what such a proof would be assembled from, and each
`genLExpr` constructor is already covered by one of them. Stated plainly so the gap is
visible: the *combinator-level* bridge is proved, the *whole-generator* instance is not. -/

end ExecRefinement
