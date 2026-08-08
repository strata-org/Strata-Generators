# `MutualADTWF` does not check arity / kinding — and this blocks generator completeness

**Audience:** authors of `Core.TypeSpec.MutualADTWF` and the `Lambda`-level
datatype well-formedness predicates (`Strata.DL.Lambda.DatatypeWF`).

**TL;DR:** `MutualADTWF` accepts constructor-argument types that apply a type
constructor at the *wrong arity* (e.g. `Sequence a b`, where `Sequence` is
arity-1). These types are ill-kinded and no well-typed program can use them, yet
they satisfy every field of `MutualADTWF`. This is the one and only remaining
obstacle to proving our ADT generator **complete** with respect to `MutualADTWF`
without an ad-hoc side condition. We would like to know whether omitting the arity
check is intentional (checked in a later pipeline phase) or an oversight that
`MutualADTWF` should close — analogous to the recently-added `argVarsScoped` field.

> **Status (current state of the proof).** We have proved completeness against
> `MutualADTWF` with a **single** side condition, `ArityOk`, isolating exactly
> this gap — see `DatatypeGen.genArgTy_complete_of_MutualADTWF` in
> `StrataGenerators/DatatypeGenProofs.lean`, and `not_complete_without_arity` for
> the `Sequence a a` witness that shows the side condition is necessary. Every
> other generator restriction is discharged by an existing `MutualADTWF` field
> (`argsWF`, `argVarsScoped`), so `ArityOk` is the only ad-hoc predicate that
> remains. If `refsKnown` becomes arity-aware (below), `ArityOk` becomes redundant
> and can be dropped; until then it lives on the generator side.
>
> **Block-level completeness is now proved** on top of the per-type
> result: `DatatypeGen.genMutuallyRecursiveDatatypes_complete` shows every target
> block presented in any datatype order is in the generator's support, given some
> inhabitance-topological reordering (`orderedBlock`) reachable by the ordered core
> (`genMutuallyRecursiveDatatypesOrdered_complete`). It composes the two
> permutation-completeness lemmas (`permutationOf_complete`, for both the block
> shuffle and the per-datatype constructor shuffle) with the header/body assembly,
> under existential size caps and `BodyReachable`, which bundles the per-datatype
> reachability side conditions (name reachability/freshness — taken as hypotheses,
> since this file's `genIdentName` has no two-directional support lemma — and the
> `visibleRefs` inhabitance-order discipline). All axiom-clean (`propext,
> Classical.choice, Quot.sound`).

## Background

We have a random generator for well-formed single-datatype blocks
(`StrataGenerators.DatatypeGen.genDatatype`) and prove it **sound** with respect
to `MutualADTWF` (`genDatatype_MutualADTWF`: every generated `d` satisfies all
eight fields, including the new `argVarsScoped`). We also want **completeness** —
every well-formed type within the generator's stated parameters is reachable.

Completeness is proved per constructor-argument type: for `genArgTy`, we want

```
ConstrArgWF [d] ty  →  (ty is within the generator's parameters)  →  ∃ size, ty ∈ support (genArgTy … size)
```

The interesting question is what "within the generator's parameters" must contain.
Ideally it is nothing more than facts *already implied by `MutualADTWF`* (plus the
unavoidable "bounded sampler" caveats below). Today it is not: we must add an
ad-hoc predicate `GenVocab` carrying an **arity** clause, because `MutualADTWF`
has no arity check.

## The gap, concretely

Consider, in a context `C` that knows `Sequence` at arity 1:

```
datatype Foo<a> {
  MkFoo(x : Sequence a a)      -- Sequence applied to TWO arguments
}
```

The argument type `x : Sequence a a` — i.e. `.tcons "Sequence" [.ftvar a, .ftvar a]`
— satisfies **every** field of `MutualADTWF C [Foo]`:

* `argsWF` (`ConstrArgWF`): `Foo` does not occur in the type, so `NotNested` and
  `StrictPosUnif` hold vacuously (`absent_constrArgWF`).
* `refsKnown`: the only referenced type-constructor name is `"Sequence"`, which is
  in `C.knownTypes.keywords`. **This is where arity is lost** — see below.
* `argVarsScoped`: every free variable is `a ∈ Foo.typeArgs`. ✓
* `inhabited`, `namesFresh`, `namesNew`, `namesNodup`, `nonempty`: all fine.

So `MutualADTWF C [Foo]` holds — but `Sequence a a` is **ill-kinded** (`Sequence`
takes one type argument). Our generator never produces it: its application branch
uses `vectorOf arity …`, drawing each constructor at exactly its declared arity.
Hence `MutualADTWF` strictly over-accepts on the arity axis, and completeness
against `MutualADTWF` alone is false for this reason.

## Root cause: `refsKnown` uses `getTypeRefs`, which discards arity

`refsKnown` is stated via `getTypeRefs`:

```lean
-- Strata/Languages/Core/DatatypeTypeSpec.lean
refsKnown : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ ref ∈ getTypeRefs arg.2,
    ref ∈ C.knownTypes.keywords ∨ ref ∈ C.datatypes.allTypeNames ∨ ref ∈ block.map (·.name)
```

and `getTypeRefs` collects only *names*, throwing away the argument count:

```lean
-- Strata/DL/Lambda/TypeFactory.lean
def getTypeRefs (ty: LMonoTy) : List String :=
  match ty with
  | .tcons n args => n :: args.flatMap getTypeRefs   -- `args.length` is dropped
  | _ => []
```

`C.knownTypes.keywords` is likewise just the list of *names* (`Std.HashMap.keys`),
so `ref ∈ C.knownTypes.keywords` says "`Sequence` is a known type," never
"`Sequence` is known *at arity 2*." No other `MutualADTWF` field constrains arity.

## The fix already exists in Strata: `knownInstance`

Strata already has an arity-aware version of exactly this check —
`LMonoTy.knownInstance`, which threads the arity through `KnownTypes.contains`:

```lean
-- Strata/DL/Lambda/LExprTypeEnv.lean
def LMonoTy.knownInstance (ty : LMonoTy) (ks : KnownTypes) : Bool :=
  match ty with
  | .ftvar _ | .bitvec _ => true
  | .tcons name args =>
    (ks.contains { name := name, metadata := args.length }) &&   -- name AT arity
    LMonoTys.knownInstances args ks
```

(`KnownType.arity := k.metadata`; `KnownTypes.contains` matches on `{name, arity}`,
unlike `containsName`/`keywords` which match on name only.)

So the arity information is available; `refsKnown` simply does not consult it.

### Suggested change

Strengthen `refsKnown` (or add a companion field) so that every constructor
argument is a *known instance*, not merely a name-resolving reference — e.g.
requiring `LMonoTy.knownInstance arg.2 C.knownTypes` for references into
`C.knownTypes` (with the analogous arity check for `C.datatypes` and block-local
datatypes). This mirrors what a kind-checker would enforce and matches how
`addMutualBlock` / the type checker treat applied constructors elsewhere.

The precedent is `argVarsScoped`: that field was added to close an analogous gap
(constructor arguments introducing unscoped type variables). Arity is the same
kind of gap on the "applied type constructor" axis.

## What is *not* a spec problem (for completeness of the arity question)

For clarity, arity is the only `MutualADTWF` change we are asking about. The other
differences between the generator's support and `MutualADTWF` are **not** spec
defects and should **not** be "fixed" by weakening `MutualADTWF`:

* **Type-variable scoping** — already closed by `argVarsScoped`. ✓
* **Uniform recursion** — already captured by `StrictPosUnif` /
  `UniformOccur.self`. ✓
* **Bitvector widths** — the AST does not constrain widths, and the generator was
  updated to draw arbitrary widths, so there is no gap. ✓
* **Arbitrary names and arbitrary nesting depth** — `MutualADTWF` correctly
  accepts any resolving name and any depth; these describe an *infinite* set,
  while the generator is a bounded sampler over finite name pools with a fuel
  budget. This is an inherent property of *any* generator, not a spec issue. We
  handle it on our side by (a) stating completeness against a concrete ambient
  context `C` (so "name resolves in `C`" *is* "name is in the generator's pool"),
  and (b) existentially quantifying the size budget (`∃ size, …`). Neither
  requires a spec change.

## Why this matters to us

Our completeness proof already rests on the following correspondence: combined
with stating completeness in `∃ size` form (entirely on the generator side), every
generator restriction *except arity* is a consequence of an existing `MutualADTWF`
field, so the arity clause is the only one we must still carry as an ad-hoc side
condition (`ArityOk`):

| generator restriction | subsumed by | still ad-hoc? |
| --- | --- | --- |
| ftvar `v ∈ tyParams` | `argVarsScoped` | no |
| recursive occurrence is `d.name` applied to `typeArgs` | `argsWF` (`StrictPosUnif` / `UniformOccur.self`) | no |
| referenced name in vocabulary | `refsKnown` against a concrete `C` | no |
| base type at arity 0 / constructor at declared arity | **would be** arity-aware `refsKnown` ← the requested change | **yes — `ArityOk`** |

If `refsKnown` becomes arity-aware, that last row is subsumed too, and we can
**delete `ArityOk` entirely**, proving the generator sound *and* complete against
`MutualADTWF` with no ad-hoc predicates. The arity check is the single missing
piece.

## Question for the authors

Is the absence of an arity/kinding check in `MutualADTWF` intentional — i.e. is
well-kindedness of constructor-argument types deliberately deferred to a later
phase of `addMutualBlock` / type checking — or should `MutualADTWF` (via
`refsKnown` → `knownInstance`, or a new field) enforce it directly? Either answer
resolves our completeness proof; we just need to know which invariant
`MutualADTWF` is intended to carry.
