# Exercising the ADT interleaving directions (2), (3), (4)

Companion to `program-gen-design.md`, which documented four interleaving
directions between type aliases / abstract types / ADT blocks and marked (2) as
"clean but not exercised", (3) as "functionally equivalent, documented", and (4)
as "excluded by decision". This note records what changed.

**Outcome.** (2) and (4) are exercised in the generator and proven, `sorry`-clean,
with no new axioms (`genProgram_sound` still depends only on the standard three
plus the pre-existing `native_decide` from `defaultContextOk`). (3) is exercised
behind a separate entry point but its soundness is **open**, and the reason is now
a machine-checked counterexample: alias resolution does not preserve
`MutualADTWF`.

## Direction (2): ADT → prior abstract type

**Before.** `genDeclDatatype` passed the *fixed* `defaultBaseTypes` /
`defaultTyCons` to `genMutuallyRecursiveDatatypes`, so the vocabulary grown by
`GenState.addAbstract` was consumed only by `genDeclAlias` / `genDeclDistinct`.
`Inv.ctxOk` was correspondingly pinned to `ContextOk s.C defaultBaseTypes
defaultTyCons s.reserved`, which made the "known" fields true by monotonicity —
the reason the fixed vocabulary was chosen in the first place.

**After.** The step passes the *threaded* `s.baseTypes` / `s.tyCons`, and
`Inv.ctxOk` is generalized to `ContextOk s.C s.baseTypes s.tyCons s.reserved`.
The abstract-type step must then re-establish `ContextOk` at the *grown*
vocabulary, which needs two facts about the freshly drawn name `nm`:

* `nm ∈ C'.knownTypes.keywords` — immediate from the `insertIfNew` the gate ran
  (`addKnownType_fields`), giving `base_known` / `tyCon_known` for the new entry;
* `C'.datatypes.getType nm = none` — needed for `base_external` /
  `tyCon_external`. `addKnownTypeWithError` leaves `datatypes` alone, so this is
  `C.datatypes.getType nm = none`, which follows from a new fold invariant
  `datatypesReserved` (every datatype name of `C` is in `reserved`) plus
  `nm ∉ reserved`.

`contextOk_addMutualBlock` is generalized from the default vocabulary to an
arbitrary `bt`/`tc` (its proof only ever used the generic
`base_mem_initialReserved` / `tyCon_mem_initialReserved` / `arrow_mem_initialReserved`
lemmas, so this is a signature change).

`genMutuallyRecursiveDatatypes_MutualADTWF` also needs `∀ kc ∈ tyCons, kc.1 ≠
"arrow"`, which at the default vocabulary was the `decide`-able
`defaultTyCons_ne_arrow`. At a grown vocabulary it becomes the new invariant
field `tyConsNeArrow`, re-established at each abstract step from
`arrowReserved` (`"arrow" ∈ reserved`) and the drawn name's freshness
(`nm ∉ reserved`), hence `nm ≠ "arrow"`.

## Direction (4): ADT → prior ADT datatype

This is the direction `program-gen-design.md` refused, and the reason it gave is
correct as far as it goes: a prior datatype `T` is *not* external, so
`TySymInhab.external` does not apply, and `ContextOk.tyCon_external` (`∀ kc ∈
tyCons, C.datatypes.getType kc.1 = none`) is *false* for it. So prior datatypes
cannot simply be appended to `tyCons`.

What the doc missed is that externality is not the only route to `TySymInhab`.
The other constructor, `TySymInhab.datatype`, applies to exactly this case, and
the fact we need — "`T` is inhabited" — is something the fold already knows,
because `T` only entered `C` through a gated `addMutualBlock` whose block we had
already proved `MutualADTWF` (whose `inhabited` field is precisely
`TySymInhab (C.datatypes.push block) d.name`).

So prior datatypes are tracked in a *separate* pool with its own hypothesis
bundle, rather than being merged into the external `tyCons`:

```
structure DatatypePoolOk (C : LContext CoreLParams) (dtCons : List KnownTyCon) : Prop where
  known : ∀ kc ∈ dtCons, kc.1 ∈ C.datatypes.allTypeNames
  inhab : ∀ kc ∈ dtCons, TySymInhab C.datatypes kc.1
```

The generator is handed `tyCons ++ dtCons` as its applied-constructor vocabulary
(so `argsWF` / `argVarsScoped` / the arity discipline are unchanged — a prior
datatype reference is drawn exactly like any other applied constructor, with
`recCallsAllowed := false` in its arguments), and the inhabitance proofs case on
which pool a head symbol came from:

* head in `tyCons` → `.external` via `ContextOk.tyCon_external`, as today;
* head in `dtCons` → `.datatype` via `DatatypePoolOk.inhab`, transported from
  `C.datatypes` to `C.datatypes.push block`.

### The transport obligation

`DatatypePoolOk.inhab` is stated in `C.datatypes`, but `MutualADTWF.inhabited`
is stated in `C.datatypes.push block`. Inhabitance is **not** monotone under
`push` in general: if some stored datatype's constructor mentions a name that is
`none` in `C.datatypes` (so rides `.external`) but *is* a block name (so becomes
`some` after the push), the derivation breaks.

That cannot happen here, but ruling it out is a real side condition, so it is
proven as a lemma with an explicit hypothesis rather than assumed:

```
tySymInhab_push        -- TySymInhab adts n → TySymInhab (adts.push block) n
```

given (a) every block name is fresh in `adts`, (b) `n` is not a block name, and
(c) no block name occurs in any constructor argument of any datatype of `adts`.
The proof is the three-way recursor with the "no block name" condition threaded
through the motives:

* `motive_1 ty := BlockAbsent block ty → TyInhab (push) ty`
* `motive_2 n  := n ∉ blockNames → TySymInhab (push) n`
* `motive_3 c  := (∀ arg ∈ c.args, BlockAbsent block arg.2) → ConstrInhab (push) c`

Condition (c) is discharged by a new fold invariant `storedRefsReserved`: every type
name referenced in any constructor argument of any datatype stored in `C` is in
`reserved`. It holds vacuously at `coreContext` (no datatypes) and is
re-established at each datatype step from `genArgTy_refs`, since a generated
block's references are confined to `baseTypes ∪ tyCons ∪ dtCons ∪ blockNames ∪
{"arrow"}`, all of which are in the grown reserved set. Freshly drawn block
names avoid `reserved`, hence avoid every stored reference — which is (c).

### Why the witness/non-witness split is *not* needed

An earlier version of this design put prior-datatype references only in the
*non-witness* constructors (`MutualADTWF.inhabited` needs only one inhabited
constructor per datatype, so the witness constructor could be kept free of
them, making the inhabitance proof go through untouched). That works, but it
requires threading a second vocabulary parameter through `genConstructors` /
`genConstrs` / `genConstrArgs` and every shape/completeness lemma over them.
With `tySymInhab_push` available, prior datatypes are safe *everywhere*,
including the witness constructor, so the single-vocabulary shape is kept.

### How it lands in the code

The generator hands `genMutuallyRecursiveDatatypes` the combined vocabulary
`s.tyCons ++ s.dtCons`, and the proofs split it back apart. Rather than change
`ContextOk` (and re-run `defaultContextOk`'s `native_decide`), the inhabitance
lemmas take the vocabulary as three parameters — `allTyCons` (what the generator
saw), `tyCons` (external, governed by `ContextOk`), `dtCons` (the pool) — plus
`hsplit : ∀ kc ∈ allTyCons, kc ∈ tyCons ∨ kc ∈ dtCons` and
`hsubTC : tyCons ⊆ allTyCons`. Affected: `tyInhab_of_absent`,
`genArgTy_tyInhab`, `genMutuallyRecursiveDatatypes_inhabited`,
`genMutuallyRecursiveDatatypes_MutualADTWF`. The `_default` corollary instantiates
`dtCons := []`, so `defaultContextOk` and its axiom footprint are untouched.

`refsKnown` also had to widen: a vocabulary reference is now *either* an external
known type (`ContextOk.tyCon_known`) *or* a stored datatype
(`DatatypePoolOk.known`, landing in the `allTypeNames` disjunct).

Three fold-invariant fields carry the pool (`ProgramGen.Inv`): `dtPoolOk`,
`dtConsReserved`, and `storedRefsReserved` (the last discharging
`StoredRefsAbsent` via `storedRefsAbsent_of_inv`). The datatype step
re-establishes `dtPoolOk` at the grown pool by taking `MutualADTWF.inhabited` for
the new entries and `tySymInhab_push` for the old ones.

## Direction (3): ADT → prior alias — exercised, but **soundness is genuinely open**

The checker de-aliases a block (`MutualDatatype.resolveAliases`) *before*
`addMutualBlock`, and `DeclHasType'.type_data` takes the block that is actually
stored. So a `Decl` in the spec's sense is always post-resolution.

A step exercising it was prototyped (`genDeclDatatypeViaAlias`: draw a
pre-resolution block over a vocabulary extended with the in-scope alias names,
run the real `MutualDatatype.resolveAliases` against the fold's `Γ`, gate on
`.ok`, emit the resolved block) and has since been **removed**, along with its
`genProgramViaAlias` / `sampleViaAlias` entry points — the repo keeps only proven
generators. A Lean module holding the counterexample below was also removed; the
worked example now lives in repo issue #65, which tracks the open question.

The obstacle is real:

* the datatype generator's soundness gives `MutualADTWF C block₀` — the block it
  *drew*;
* `DeclHasType'.type_data` needs `MutualADTWF C (resolveAliases block₀)` — the
  block actually *stored*.

`MutualADTWF.argsWF` unfolds to `ConstrArgWF = NotNested ∧ StrictPosUnif`, both
**structural** conditions, and alias expansion rewrites exactly that structure.
The design doc's "functionally equivalent, documented, not a gap" is too
optimistic. Concretely (this was machine-checked before the module was removed;
it is reproduced in issue #65):

* alias `A x = x → int` — *flat*, so exactly the shape this generator produces;
* block `datatype T { MkT (f : A T) }` — pre-resolution, `T` sits under a type
  constructor, a legal strictly-positive position;
* the resolver rewrites the argument to `T → int`;
* which `StrictPosUnif` rejects — hence `MutualADTWF` fails, in *any* ambient `C`.

Note the executable gate does not rescue the declarative premise: the two are
independent, which is the whole reason the generate-and-check design works for
the *other* premises.

Closing this needs a preservation lemma — "`resolveAliases` preserves
`MutualADTWF`" under a side condition on alias bodies (arrow-free, or no block
name reaching an expanded position). That is a substantive proof about Strata's
resolver rather than a corollary of the generator, and *which* lemma to aim for
depends on whether Strata intends positivity to be checked pre- or
post-resolution (issue #65). So the step was removed rather than admitted with a
`sorry` or left in the tree unproven.

**Important caveat on reachability.** The counterexample is *not* reachable by
this generator: `genArgTy` draws application arguments with
`recCallsAllowed := false`, and `genArgTy_absent` proves anything drawn at `false`
contains no block name anywhere. So a block name can never appear inside an alias
application's arguments, and the removed step was **unproven, not
known-unsound**. The counterexample is a statement about `MutualADTWF` and
`resolveAliases`, not a witness against the generator.

Flatness (§"Interleaving" in the design doc) is *not* sufficient here: the alias
`A` above is flat and still breaks the invariant. Flatness prevents alias→alias
cycles; it says nothing about the shape an expansion injects.
