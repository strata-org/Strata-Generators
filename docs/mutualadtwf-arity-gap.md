# `MutualADTWF` and generator completeness — the arity gap, now closed

**Audience:** authors of `Core.TypeSpec.MutualADTWF` and the `Lambda`-level
datatype well-formedness predicates (`Strata.DL.Lambda.DatatypeWF`).

> ## RESOLVED (2026-08-12)
>
> **The gap this document reported is closed upstream.** `MutualADTWF` gained the
> field `argsWellKinded`, which pairs every type-constructor reference in a
> constructor argument with the argument count at that occurrence
> (`getTypeConsArities`) and requires it to match the referent's declared arity —
> a `C.knownTypes` arity, or a datatype's `typeArgs` count. That is exactly the
> check we asked for below.
>
> **Our side is now aligned.** The hand-written `ArityOk` side condition is
> **deleted** (strata-generators issue #101). Two changes made that possible:
>
> 1. `DatatypeGen.defaultBaseTypes` and `DatatypeGen.defaultTyCons` are now
>    *derived* from `Core.KnownTypes` — the very register `argsWellKinded` speaks
>    about — rather than written by hand. `mem_defaultBaseTypes_iff` and
>    `mem_defaultTyCons_iff` read the derivation back in both directions, so an
>    arity fact about `Core.KnownTypes` becomes membership in the generator's
>    vocabulary. That is what turns `argsWellKinded` into everything `ArityOk`
>    used to assert.
> 2. What `ArityOk` was *also* silently covering is now split out and named, so
>    both residual gaps are visible instead of hidden inside an arity recursion:
>
>    * **`BitvecWidthOnly`** (a condition on the type) — `Core.KnownTypes`
>      registers `("bitvec", 1)`, so `argsWellKinded` accepts `bitvec τ` for a
>      *type* `τ`, and `LContext.addMutualBlock` really does accept such a block.
>      But a bitvector type is `LMonoTy.bitvec n` for a **width** `n : Nat`, and no
>      `LMonoTy` argument position can hold a natural number — so the arity `1`
>      recorded for `bitvec` is not an arity over types at all. `genBaseTy` emits
>      bitvectors through `pickBitvecWidth`; `genArgTy` never applies the *name*
>      `bitvec`. `not_complete_without_bitvecWidthOnly` is the machine-checked
>      witness that this one condition is still needed.
>    * **`VocabOk.noStoredDatatypes`** (a condition on the context) —
>      `argsWellKinded` is a three-way disjunction, and its middle disjunct admits
>      references to datatypes *already stored* in `C`. The generator's vocabulary
>      is `baseTypes`/`tyCons`/`arrow`/`blockRefs`; it cannot emit such a
>      reference. This holds for `coreContext` (`datatypes := #[]`), which is where
>      the capstone is instantiated, but not part-way through the whole-program
>      generator. That is a genuine limit of the result, not an artefact of how it
>      is stated.
>
> `Sequence a a` — the counterexample this document was written around — is now
> rejected by `MutualADTWF` itself; an `example` next to
> `not_complete_without_bitvecWidthOnly` records that.
>
> **Side benefit.** Deriving the vocabulary removed most of the `native_decide` in
> `defaultContextOk`: its four vocabulary fields are now proven from the shape of
> the `filter` and hold for whatever `Core.KnownTypes` contains, so they need no
> revisiting when upstream registers a new primitive. Only the two `arrow` lookups
> remain, because `genArgTy` hardcodes that name.
>
> **One behavioural consequence.** `defaultBaseTypes` must be *exactly* the arity-0
> part of `Core.KnownTypes` for the implication to go through, so it now also
> contains `Triggers` and `TriggerGroup`. The generator therefore emits datatype
> fields at those types, and the Core printer cannot render them
> (`lmonoTyToCoreType: unknown type`). That widens the already-failing
> `printer: no conversion error on generated programs` property — the printer's
> existing gap on most `bitvec` widths — rather than breaking a passing one.
>
> The rest of this document is kept as the original report.

---

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

**Update.** This is what happened, via the new `argsWellKinded` field rather than
by changing `refsKnown`. The table now reads:

| generator restriction | subsumed by | still ad-hoc? |
| --- | --- | --- |
| ftvar `v ∈ tyParams` | `argVarsScoped` | no |
| recursive occurrence is `d.name` applied to `typeArgs` | `argsWF` (`StrictPosUnif` / `UniformOccur.self`) | no |
| referenced name in vocabulary | `refsKnown` against a concrete `C` | no |
| base type at arity 0 / constructor at declared arity | **`argsWellKinded`**, plus the vocabulary being derived from `Core.KnownTypes` | no |
| a bitvector is a width, not an application | none — see `BitvecWidthOnly` | yes (one condition on the type) |
| no reference to a datatype stored in `C` | none — see `VocabOk.noStoredDatatypes` | yes (one condition on the context) |

## Question for the authors

*(Answered: `argsWellKinded` was added. Kept for the record.)*

Is the absence of an arity/kinding check in `MutualADTWF` intentional — i.e. is
well-kindedness of constructor-argument types deliberately deferred to a later
phase of `addMutualBlock` / type checking — or should `MutualADTWF` (via
`refsKnown` → `knownInstance`, or a new field) enforce it directly? Either answer
resolves our completeness proof; we just need to know which invariant
`MutualADTWF` is intended to carry.
