# Using Kiro to Synthesize a Correct STLC Generator

A generator is a function used in property-based testing. Its job is to rapidly and randomly produce many values with which to test whether a given property holds. In this short document I describe my experience of using Kiro to synthesize and prove correct a generator, written in Lean, for simply-typed lambda calculus (STLC) terms. The final result of my work is at https://code.amazon.com/packages/Basalt/blobs/mainline/--/Basalt/Examples/STLC.lean.

The main lesson I’ve drawn from this work is: While Kiro can indeed synthesize a sound and complete generator for STLC terms, I am not very confident about its ability to do this reliably and at scale. I had several false starts before I finally landed on what seems like a reasonable generator. A good follow-on experiment would be to give Kiro tools like Specimen and/or Palamedes to generate components of generators that are correct by construction, “manually” filling in gaps in what the tools can do.

## Constrained generators, in Lean

A *constrained* generator is one whose values must satisfy some constraints in order to be useful. For example, suppose my property to test is “for all lambda calculus terms T, if those terms are well-typed then their evaluations will never fail.” Ideally, my generator will produce terms T that are well typed (else it will have to do rejection sampling, which is inefficient). Given a particular constraint C, a generator G is *sound* with respect to C if G always generates values such that C(x) holds, and it is *complete* if for any x such that C(x) holds, G can generate x. We say a constrained generator for C is *correct* if it is both sound and complete.

The main framework in Lean for property-based testing is called Plausible, so ultimately we want a Plausible-compliant generator. However, the Plausible library gives no means to prove properties about generators, like soundness and completeness. For that purpose, we can use a framework called [Basalt](https://code.amazon.com/packages/Basalt/trees/mainline/--/Basalt), which provides a way to view a generator as both a random sampler and a (sub) probability mass function. The former is used to actually perform property testing (and can be made to work in Plausible), and the latter is used to reason about the values the sampler can produce when it runs. I describe the details of Basalt and how it works in [a separate document](https://quip-amazon.com/fPLpA5mnVBQD/How-will-we-build-generators-for-Strata).

## Synthesizing a proved-correct generator for STLC

For my STLC experiment, I produced a constrained generator where the value x is a lambda calculus term, and the constraint C is “this term is well typed”. My workflow had the following steps:

1. Ask Kiro to synthesize a development of STLC: its types, terms, and typing relation.
2. Ask Kiro to synthesize a generator of well-typed STLC terms. I provided to it the artifacts from the first step.
3. Ask Kiro to *prove* that its generator is correct, i.e., sound and complete.

For me, the first two steps of this workflow worked well, but proving soundness and completeness took some iterations that in turn required several refinements to the generator produced in step 2.

### Syntax and typing

Kiro came up with a very sensible encoding of STLC in Lean. This makes sense because STLC has been formalized many times before. Here is the syntax, which uses a “nameless” representation of variables (de Bruijn indexes).

```
inductive typ where
  | Nat : typ
  | Fun : typ → typ → typ
  deriving DecidableEq, Repr

instance : BEq typ := instBEqOfDecidableEq

/-- Terms in the STLC extended with naturals and addition -/
inductive term where
  | Const: Nat → term
  | Add: term → term → term
  | Var: Nat → term
  | App: term → term → term
  | Abs: typ → term → term
  deriving BEq, Repr
```

Here is the typing relation:

```
/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : List typ -> Nat -> typ -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive typing: List typ → term → typ → Prop where
| TConst : ∀ Γ n,
    typing Γ (.Const n) .Nat
| TAdd: ∀ Γ e1 e2,
    typing Γ e1 .Nat →
    typing Γ e2 .Nat →
    typing Γ (.Add e1 e2) .Nat
| TAbs: ∀ Γ e τ1 τ2,
    typing (τ1::Γ) e τ2 →
    typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
| TVar: ∀ Γ x τ,
    lookup Γ x τ →
    typing Γ (.Var x) τ
| TApp: ∀ Γ e1 e2 τ1 τ2,
    typing Γ e2 τ1 →
    typing Γ e1 (.Fun τ1 τ2) →
    typing Γ (.App e1 e2) τ2
```

All of this it got right the first time.

### The generators

Kiro (ultimately, with help from me) produced three Lean functions:

* `def [genType](https://code.amazon.com/packages/Basalt/blobs/ed1d35298afc31a84f9f1e1125ef40c54daa3350/--/Basalt/Examples/STLC.lean#L73) [Gen G] : Nat -> G typ` 
    This function randomly generates a type whose depth is bounded by the given `Nat`
* `def `[`pickVar`](https://code.amazon.com/packages/Basalt/blobs/ed1d35298afc31a84f9f1e1125ef40c54daa3350/--/Basalt/Examples/STLC.lean#L66)` [Gen G] (Γ : List typ) (τ : typ) (depth : Nat) ... → G term` 
    This function randomly chooses a variable of type `τ` from `Γ`, where the type’s size is no larger than the given depth 
* `def `[`genTyped`](https://code.amazon.com/packages/Basalt/blobs/ed1d35298afc31a84f9f1e1125ef40c54daa3350/--/Basalt/Examples/STLC.lean#L94)` [Gen G] (Γ : List typ) : (depth : Nat) → (τ : typ) → G term` 
    This function randomly generates a term having type `τ` in the given context `Γ`, no larger than the given `depth`

It produced variations of these three things at the outset, but they had to change a couple of times to ensure soundness and completeness, as discussed below.

### Soundness and completeness

Basalt provides a bunch of lemmas to aid in proofs about generators. Kiro was able to use these and successfully generate a [proof of soundness](https://code.amazon.com/packages/Basalt/blobs/ed1d35298afc31a84f9f1e1125ef40c54daa3350/--/Basalt/Examples/STLC.lean#L66), stated thus:

```
theorem genTyped_sound (Γ : List typ) (depth : Nat) (τ : typ) (e : term)
    (h : e ∈ SetGen.support (genTyped (G := SetGen.Set) Γ depth τ)) : typing Γ e τ
```

This theorem states that if `e` is produced by `genTyped Γ depth τ`, i.e., it’s in the generator’s `support`, then `e` is type correct, i.e., `typing Γ e τ`  holds. The `G := SetGen.Set` part is filling in Basalt’s `Gen` typeclass argument with an implementation of mathematical sets, to facilitate the proof. (SetGen is a simplification of the sub probability mass function concept I mentioned above.)

Kiro was also able to generate a [proof of completeness](https://code.amazon.com/packages/Basalt/blobs/ed1d35298afc31a84f9f1e1125ef40c54daa3350/--/Basalt/Examples/STLC.lean#L387):  

```
theorem genTyped_complete (Γ : List typ) (e : term) (τ : typ) (depth : Nat)
    (htyp : typing Γ e τ) (hτ : typDepth τ ≤ depth) (he : termDepth Γ e ≤ depth) :
    e ∈ SetGen.support (genTyped (G := SetGen.Set) Γ depth τ)
```

This theorem states that for any `e` such that `typing Γ e τ` then `genTyped` can generate `e` when given `Γ depth τ` as parameters, so long as `depth` is an upper bound on the depth of the generated term and its type.

## The trouble

In the end, it works! But it was not fully automated, and I’m not sure that Kiro could have figured it out all on its own. I did not take careful notes as I went, but here is my recollection of the progression.

### Wrong notion of size/depth

We want generators to take an explicit representation of the size of the terms they produce so that we can avoid generating huge terms. Smaller terms mean faster tests, and the small-world hypothesis suggests that a bug revealed by a large term very likely can be made to manifest with a small one.

It turns out that the initial notion of *size* that Kiro used was not amenable to proving completeness, in the predicate `termSize`. The problem is variables. The first thought is that a variable is size `0`. Suppose `Γ`  ascribes `x` the type `Nat`. Then both the term `Const 0` and `x` have that type, and are size `0` . But what if  `Γ` ascribes `x` the type `Fun Nat Nat`? Then both the term `Abs Nat (Const 0)` and `x` have that type, but the latter would seem like it should have a larger size. TBH, I’m not recalling now why this should matter, but getting past this sticking point and considering the type as part of the size (see line 368/268 of [this commit](https://code.amazon.com/packages/Basalt/commits/09e1d0181bc63aae9f803db4184428fc7bb9aed2)) allowed Kiro to prove completeness (see line 598/493 of the same commit).

### Notion of size is still wrong!

But then it turned out that while a version of soundness and completeness could be proved, they did not line up. In particular, the `size` argument given to the generator would not produce terms `e` such that `termSize e ≤ size`. In particular, `genTyped` could generate an `(Abs _ (Abs _ ... ))` term and it would be given size 0, but that term’s  `termSize` is always greater than 0!

This required another change to the generator to introduce failure. In particular, if asked to produce a term at type `Fun Nat Nat` at size 0, then the generator should simply fail. This failure would precipitate the caller trying again, either from scratch or internally by using a backtracking monad (that’s future work). I prompted Kiro to make these changes and it was able to do so and prove soundness and completeness so that they line up (i.e., the theorems given in this doc, above).

### Inefficiency

Unfortunately, the generator was not particularly efficient — it failed an awful lot. By being a little loose with bounds the size argument of recursive calls, it would often attempt to generate terms with types with incompatible sizes. Without a backtracking monad, such failures would be very costly, and even with one they would be more expensive. So I prompted Kiro to tighten up the arithmetic to not make recursive calls for term forms that were doomed to fail. This change finally landed on a term generator that worked most of the time and was also sound and complete. 

## What lessons can we take from this?

The main lesson to take from all of this is that generating a good generator for a non-trivial language is not easy, and just asking Kiro to do it might not work. It was a substantial effort for me to ultimately land on what I think is a good generator. 

By contrast, Specimen could have produced a generator much like the one Kiro produced automatically. I suspect it would be almost if not equally efficient. While Specimen does not provide soundness and completeness proofs now, it could be made to do that. Specimen is not a panacea though. It only works for constraints expressed as inductive relations, and not all inductive relations are in scope, e.g., those involving dependent types. 

We probably want to improve Specimen, but we also want to make it work with the creativity of Kiro. That way, we have a deterministic tool that Kiro can use as it likes, but can fill in the gaps and improve efficiency too. My suggestion is to

1. Improve Specimen in clear ways that would help particular use-cases
2. Have Specimen’s generators line up with Basalt’s, so we can prove properties about them
3. Make Specimen a tool that Kiro can use to generate larger and more interesting generators, combining proofs of Specimen generators with those of its own components.


