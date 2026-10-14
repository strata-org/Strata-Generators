import StrataGenerators.GenSupport
import StrataGenerators.RetryGenSupport
import Basalt.PlausibleGen

/-!
# Execution refines the `Set` semantics

Each theorem for soundness and for completeness in this package speaks about
`SPMF`, but the test harness runs `Plausible.Gen`. This module connects the two, so
that a theorem about the support in `Set` says something about the executable generator.

The bridge is the relation `Refines p s size`:

> each value that `p` can return, at some seed and at this size, is in
> `SPMF.support s`.

`Refines` is *compositional*. `pure`, `bind`, `map`, `choose`, a two-branch `oneOf` and `default` all
keep it, and `retryGen` and `retryGenArg` also keep it. A generator that is polymorphic
in `[Gen G]` and built from those combinators therefore refines its own instance at
`SPMF` when it runs at `Plausible.Gen`. The proved results about the support then
give an upper bound on what execution can produce.

## This is refinement and *not* adequacy

The name is not "adequacy" on purpose. In the semantics of a programming language, an
adequate translation is sound *and* complete: the source and the target agree on the
observable behaviour in both directions. This module proves only the sound half:

    runSupport (p at Plausible.Gen)  ⊆  SPMF.support (p at SPMF)

Execution therefore never leaves the proved support, and this one-directional containment
is what the word *refinement* means. The name "adequacy" would also claim the other
direction, and that direction is absent.

The `⊆` direction is the one that carries the *soundness* results, and it is useful on
its own. With `genLExpr_sound`, it gives the fact that each term which the harness draws
is well-typed, and that fact is about the executable generator.

The other inclusion says that some seed reaches each term that `Set` can reach. This
module **cannot** prove it, and the obstruction is not about a generator. The claim
reduces to the surjectivity of `randNat` and of `RandomGen.next` over each range of
`choose`, and that is a claim about the arithmetic of `StdGen`.
`Init.Data.Random.randNat` rests on a `private partial def randNatAux`, which has no
equation lemmas and which a proof cannot unfold. For example, `rfl` cannot close
`(randNat (mkStdGen 1) 3 7).1 = 5`. The ranges do appear to be covered, but a test is not
a proof, and such a theorem is about the random number generator of Lean and not about
this package. This note keeps the difference between the two directions visible.

The `⊆` direction is also the direction that composes. `Refines` threads through `bind`,
because both sides give the middle state of the random number generator as an
*existential* witness. See `refines_bind` below. The matching *equation* does not
compose, for the reason that `RetryGenSupport` records: in `p >>= f`, the value of `p`
determines the state that `f` receives, so two independent witness seeds can differ.
-/

open Lambda RandomChoice Plausible RetryGenSupport

namespace ExecRefinement

/-! ## The structural lemmas for `Plausible.Gen`

The monad instances of `Plausible.Gen` come from a stack of monad transformers. A proof
that applies a `bind` or a `map` to a state and a size must therefore unfold the stack by
hand. -/

/-- `bind` at `Plausible.Gen` threads the state of the random number generator through. It
    runs `p`, and then it runs the continuation at the state that `p` gives. -/
theorem bind_apply {α β} (p : Plausible.Gen α) (f : α → Plausible.Gen β)
    (sg : ULift StdGen) (size : ULift Nat) :
    (p >>= f) sg size
      = (match p sg size with
         | .ok (a, sg') => f a sg' size
         | .error e => .error e) := by
  simp only [bind, StateT.bind, ReaderT.bind, Except.bind]
  cases p sg size <;> rfl

/-! ## The refinement relation -/

/-- `p` **refines** `s` at `size` when each value that `p` can return, over each seed of
    the random number generator, is in the support of `s`.

    In words: a run of `p` cannot produce a value that the `Set` semantics does not
    predict. This is the property that lets a theorem about `SPMF.support` constrain the
    harness.

    The relation is one-directional on purpose. The documentation of this module says why
    this is refinement and not adequacy. -/
def Refines {α} (p : Plausible.Gen α) (s : SPMF α) (size : ULift Nat) : Prop :=
  ∀ a, runSupport p size a → a ∈ SPMF.support s

/-- `pure` refines `pure`. The value that it returns is the only value that it can
    reach. -/
theorem refines_pure {α} (a : α) (size : ULift Nat) :
    Refines (pure a : Plausible.Gen α) (pure a : SPMF α) size := by
  rintro b ⟨sg, sg', h⟩
  simp only [pure, StateT.pure, ReaderT.pure] at h
  cases h
  exact mem_support_pure_iff.mpr rfl

/-- **Refinement composes through `bind`.** This is the main lemma of the module. It is
    the reason why the refinement of a whole generator follows from the refinement of its
    primitives.

    The proof takes the middle state `sgmid` that `p` gives, and it gives that state to
    the hypothesis for the continuation. The `Set` side needs only the *existence* of a
    witness value, which `hp` gives. Unlike the matching equation, this claim therefore
    needs no agreement between two independent seeds. -/
theorem refines_bind {α β} (p : Plausible.Gen α) (s : SPMF α) (size : ULift Nat)
    (f : α → Plausible.Gen β) (g : α → SPMF β)
    (hp : Refines p s size) (hf : ∀ a, Refines (f a) (g a) size) :
    Refines (p >>= f) (s >>= g) size := by
  rintro b ⟨sg, sg', h⟩
  rw [bind_apply] at h
  split at h
  · rename_i a sgmid heq
    exact mem_support_bind_iff.mpr ⟨a, hp a ⟨sg, sgmid, heq⟩, hf a b ⟨sgmid, sg', h⟩⟩
  · exact absurd h (by simp)

/-- `map` refines `map`. The proof goes through `bind` and `pure`, because `map` is a
    `bind` with a `pure` continuation at both layers. -/
theorem refines_map {α β} (p : Plausible.Gen α) (s : SPMF α) (size : ULift Nat)
    (φ : α → β) (hp : Refines p s size) :
    Refines (φ <$> p) (φ <$> s) size := by
  rintro b ⟨sg, sg', h⟩
  -- At both layers, `map` is `bind (pure ∘ φ)`.
  have hb : ((p >>= fun a => pure (φ a)) : Plausible.Gen β) sg size = .ok (b, sg') := h
  rw [bind_apply] at hb
  split at hb
  · rename_i a sgmid heq
    refine mem_support_map_iff.mpr ⟨a, hp a ⟨sg, sgmid, heq⟩, ?_⟩
    simp only [pure, StateT.pure, ReaderT.pure] at hb
    cases hb
    rfl
  · exact absurd hb (by simp)

/-- **`choose` refines `choose`, and it does so without a condition.** The support of
    `choose` at `SPMF` is *each* element of the subtype `{x // lo ≤ x ∧ x ≤ hi}`.
    Each value that `Plausible.Gen` returns is such an element, because the value carries
    its own proof of the bounds. The claim therefore needs no hypothesis about the value.

    This is the base case that makes the whole package work: the one primitive for
    randomness in the `Gen` class of `Basalt` refines its reading in `Set` at no cost.

    This is also the exact place where a proof of the other direction must go, and where
    it cannot go. By definition, `choose` at `Set` reaches the whole range. A proof for
    `Plausible` needs `randNat` to be surjective onto that range. -/
theorem refines_choose (lo hi : Nat) (h : lo ≤ hi) (size : ULift Nat) :
    Refines (RandomChoice.choose lo hi h : Plausible.Gen _)
            (RandomChoice.choose lo hi h : SPMF _) size := by
  rintro v -
  exact mem_support_choose_iff.mpr trivial

/-- `default` refines `default`, and it does so *vacuously*. At `Plausible.Gen`, `default`
    is a failure of the generator and it returns no value, so there is no value to put in
    the empty support, which is `default` at `SPMF`.

    This lemma is what makes each `else default` in `genLExprBase` harmless here. The two
    readings of `default`, a panic and `∅`, agree exactly on which values a generator can
    reach. -/
theorem refines_default {α} [Inhabited α] (size : ULift Nat) :
    Refines (default : Plausible.Gen α) (default : SPMF α) size := by
  rintro a ⟨sg, sg', h⟩
  simp only [default, throw, throwThe, MonadExceptOf.throw,
             Function.comp_def, StateT.lift, bind, ReaderT.bind, Except.bind] at h
  exact absurd h (by simp)

/-- A two-branch `oneOf` refines a two-branch `oneOf` when both of its branches refine their
    branches. A choice between two branches cannot reach a value outside the union of the two
    supports. -/
theorem refines_oneOf_pair {α} (p q : Plausible.Gen α) (s t : SPMF α) (size : ULift Nat)
    (hp : Refines p s size) (hq : Refines q t size) :
    Refines (oneOf [fun () => p, fun () => q])
            (oneOf [fun () => s, fun () => t]) size := by
  rintro a ⟨sg, sg', h⟩
  rw [SPMF.mem_support_oneOf_pair_iff]
  -- `oneOf [x, y]` is
  -- `choose 0 1 >>= fun i => ([x, y][i.down.val]'_) ()`. The drawn index is 0 or 1, so the
  -- `getElem` is one of the two branches.
  -- Whichever index the draw gives, the `getElem` *is* one of the two branches. The index sits under
  -- a dependent `getElem` proof, so neither `rw` nor `simp` can substitute for it; casing on the
  -- index inside this `have`, where the proof obligation is discharged per case, avoids that.
  have key : ∀ (j : Nat) (hj : j < ([fun (_ : Unit) => p, fun _ => q]).length),
      ([fun (_ : Unit) => p, fun _ => q][j]'hj) = (fun _ => p)
        ∨ ([fun (_ : Unit) => p, fun _ => q][j]'hj) = (fun _ => q) := by
    intro j hj
    match j with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
    | _ + 2 => simp at hj
  simp only [oneOf, bind_apply] at h
  split at h
  · rename_i v sgmid heq
    rcases key v.down.val (by
      have hlt := v.down.property.2
      simp only [List.length_cons, List.length_nil] at hlt ⊢
      omega) with hk | hk
    · rw [hk] at h
      exact Or.inl (hp a ⟨sgmid, sg', by simpa using h⟩)
    · rw [hk] at h
      exact Or.inr (hq a ⟨sgmid, sg', by simpa using h⟩)
  · exact absurd h (by simp)

/-! ## The result: a retry keeps refinement -/

/-- **`retryGen` keeps refinement.** A wrapper of retries around a generator cannot make
    the generator reach a value outside its support in `Set`, because
    `runSupport_retryGen` says that a retry changes nothing that a generator can reach.

    This fact is what lets the harness run `retryGen` and `retryGenArg` while the proofs
    speak about the plain generator. The proved support still bounds what execution can
    produce. -/
theorem refines_retryGen {α} (fuel : Nat) (p : Plausible.Gen α) (s : SPMF α)
    (size : ULift Nat) (hp : Refines p s size) :
    Refines (retryGen fuel p) s size := by
  intro a ha
  exact hp a (runSupport_retryGen fuel p size ▸ ha)

/-- `retryGenArg` keeps refinement at each point, and this is the form that the `retryCont`
    parameter of `genLExpr` takes. If the generator for an argument refines its reading in
    `Set` at each type, then the generator with retries also refines it. -/
theorem refines_retryGenArg {α β} (fuel : Nat) (f : α → Plausible.Gen β)
    (g : α → SPMF β) (size : ULift Nat)
    (hf : ∀ a, Refines (f a) (g a) size) (a : α) :
    Refines (retryGenArg fuel f a) (g a) size :=
  refines_retryGen fuel (f a) (g a) size (hf a)

/-! ## What this module covers

`refines_choose` and `refines_default` are the base cases. `refines_bind`, `refines_map`
and `refines_oneOf_pair` carry refinement through the combinators of the `Gen` class of
`Basalt`. `refines_retryGen` and `refines_retryGenArg` cover the harness in production.

This module does *not* prove one theorem
`Refines (genLExpr (G := Plausible.Gen) …) (genLExpr (G := SPMF) …)`. Such a proof
must go through the whole branch structure of `genLExpr` against the lemmas above: each
list of weights for a `frequency`, the `elements` and the `mapM` inside `genIndir` and
`genIndirPoly`, and each `default` in `genLExprBase`. That work is a large mechanical
induction and not a new idea. The lemmas here are the parts of such a proof, and one of
them covers each constructor that `genLExpr` uses. The gap is therefore clear: the bridge
holds at the level of a combinator, and not for the whole generator. -/

end ExecRefinement
