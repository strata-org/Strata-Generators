import StrataGenerators.SetGen
import StrataGenerators.DatatypeGen
import StrataGenerators.FunctionHasTypeAGen.IdentName
import Strata.DL.Lambda.DatatypeWF
import Strata.Languages.Core.DatatypeTypeSpec
import Strata.Languages.Core.Factory

open Lambda RandomChoice ArbNat ArbChar ArbString SetGen

/-!
# Soundness and completeness of the generator for algebraic data types

This file proves that the type generator in `DatatypeGen` is sound and complete against the
declarative typing specification in `Strata.DL.Lambda.DatatypeWF`.

That specification is `Lambda.ConstrArgWF`, and it is the argument half of
`Core.TypeSpec.MutualADTWF`.

The generator now makes *mutually recursive* blocks. Therefore the proofs apply that
specification to a full `block : MutualDatatype Unit`.

They do not apply it to a list `[d]` that holds one datatype.

A **block datatype** is a datatype that the `mutual … end` block declares, which is a member
of `block`. The datatypes of one block can refer to each other, therefore they are mutually
recursive. This file uses the term *block datatype* for each of them.

The change from one datatype to a mutual block makes the conditions weaker. The old code
compared a head symbol against one name `selfName`. The relations `NotNested`, `StrictPosUnif`
and `UniformOccur` now compare that symbol against `block.map (·.name)`, which is the set of
block names.

All three relations already take the block as a parameter in the specification.

## The terms for a recursive occurrence: `blockRefs` and `BlockRefsWF`

The type generators `genLeafTy` and `genArgTy` emit a recursive occurrence from the list
`blockRefs : List BlockRef`. That list holds the block datatypes that the new datatype can
refer to. Each member is a pair `(name, args)`, and `args` holds the type arguments of
that member as rigid type variables.

`BlockRefsWF block tyParams blockRefs` holds the four facts about that list that the
soundness proof needs:

* `mem`. Each reference names a true block datatype. `NotNested.headBlock` needs this fact,
  and so does the third part of `refsKnown`.
* `uniform`. A reference to the name of `d` applies it to exactly `d.typeArgs`.
  `UniformOccur.self` needs this fact.
* `ftvarArgs`. The arguments of a reference are all rigid type variables. Therefore the
  reference is never nested, and it adds no type reference other than its head name.
* `scoped`. The argument variables of a reference are all declared type parameters.
  `argVarsScoped` needs this fact.

`genMutuallyRecursiveDatatypes` gives `visibleRefs` for that list. `visibleRefs` obeys all
four facts by construction. Read `visibleRefs_blockRefsWF`.

## The structure of this file

**Part 1: lemmas about the specification.** These are facts about `DatatypeWF` alone. The
main one is `absent_constrArgWF`. If no block name occurs in a type, then that type is a
well-formed constructor argument. This fact is the value of the flag
`recCallsAllowed := false`, because `genArgTy` with that flag makes exactly such types.
Such a type holds no block name at any position.

**Part 2: the support of the generator, with no helper relation.** The lemmas
`genLeafTy_mem_iff` and `genArgTy_mem_iff` each describe the support of one generator as a
disjunction. The parts of that disjunction are the alternatives of the `oneOf` in the
generator, which are a stop kind, an arrow and an application. The recursive positions
refer back to the support at `size / 2`. This file has no relation with an index for the
size. The proof of soundness and the proof of completeness each do their own strong
induction on `size` through these two lemmas.

**Part 3: soundness against the typing specification.** `genArgTy_constrArgWF` says that
each type in the support is `ConstrArgWF block`. Its proof is a strong induction on `size`
through `genArgTy_notNested`, `genArgTy_strictPosUnif` and `genArgTy_absent`. The output of
`genMutuallyRecursiveDatatypes` then obeys all nine fields of `MutualADTWF`.

Part 3 also uses the rule for the reserved names. Each datatype name is fresh against
`initialReserved`. `namesOk_of_fresh` changes that fact into the side conditions that the
specification needs.

## Completeness against `MutualADTWF`, with a single arity side condition

The support of the generator is smaller than the set of constructor argument types that
`MutualADTWF` accepts. Therefore completeness needs more hypotheses. The result of the
completeness half of this file is that all of those hypotheses except one are already
fields of `MutualADTWF`, and the one that is not is about the **width** of a bitvector.

This file used to carry a hand-written `ArityOk` predicate, because `refsKnown` uses
`getTypeRefs`, which collects only the *names* of the referenced type constructors and
discards the number of their arguments — so `MutualADTWF` accepted an argument type of the
wrong kind, such as `Sequence a a`. The field `argsWellKinded` now checks the argument count
against `C.knownTypes`, and `defaultBaseTypes` / `defaultTyCons` are *derived* from that same
register (`Core.KnownTypes`), so the specification discharges the whole arity discipline by
itself and `ArityOk` is gone. Read `docs/mutualadtwf-arity-gap.md`.

An existing field of `MutualADTWF` discharges every difference between the specification and
the generator except one:

| condition on the generator | field of `MutualADTWF` that gives it |
| --- | --- |
| each free type variable is a member of `d.typeArgs` | `argVarsScoped` |
| a recursive occurrence is a block name with exactly its `typeArgs` | `argsWF`, through `StrictPosUnif` and `UniformOccur.self` |
| strict positivity, and no nested occurrence | `argsWF`, through `ConstrArgWF` |
| each referenced name resolves | `refsKnown`, against one concrete ambient context |
| the arity of an application is correct | `argsWellKinded`, against `C.knownTypes` |
| **a bitvector is a width, not an application** | **none. This is `BitvecWidthOnly`.** |

* **Soundness.** Each type in the support obeys all nine fields of
  `Core.TypeSpec.MutualADTWF`. Read `genArgTy_constrArgWF` and
  `genMutuallyRecursiveDatatypes_MutualADTWF`.
* **Completeness.** Read `genArgTy_complete_of_MutualADTWF`. Take a block that is
  `MutualADTWF` and whose bitvectors are widths (`BitvecWidthOnly`). Then the generator can
  make each constructor argument type of that block, at some size. The size is an existential
  value, and `genArgTy_mono` with `genArgTy_common_size` puts the sizes of the subterms
  at one value. This result also needs the references of the block to be visible to the
  generator, which `BlockRefsWF` gives, and the generator's vocabulary to be `C`'s arity
  register split by arity, which `VocabOk` states and `defaultVocabOk` proves.

`not_complete_without_bitvecWidthOnly` shows why `BitvecWidthOnly` must stay. `Core.KnownTypes`
registers `("bitvec", 1)`, so `MutualADTWF` accepts `bitvec a` for a *type* `a`; but a
bitvector type is `LMonoTy.bitvec n` for a width `n : Nat`, and no `LMonoTy` argument position
can hold a natural number. The generator therefore never makes that type. The same theorem's
neighbouring `example` records that `Sequence a a` — the old counterexample — is now rejected
by `MutualADTWF` itself.

## Completeness for a full block

Completeness holds for one type, and it also holds for a full block. The proof for a block
has two layers:

* `genMutuallyRecursiveDatatypes_complete` is the layer with the rank as a parameter. The
  generator can make a target block when the caller gives a list of ranks. The caller must
  also divide the constructors of each datatype into the inhabited constructor and the
  other constructors. The generator must be able to make the argument types of the
  inhabited constructor from the set of names for a lower rank, which is
  `visibleRefs (lowerRankHeaders …)`. It must be able to make the argument types of the
  other constructors from the full set. This layer needs no topological sort, because the
  drawn ranks alone give that set of names, and no order of the datatypes gives it.
* `genMutuallyRecursiveDatatypes_complete_of_MutualADTWF` is the **capstone, and it is free
  of any order**. It takes only `MutualADTWF`, together with the side conditions about the
  terms of the generator. Those side conditions are the reachability of the names and the
  parameters, `hasDefaultTesterName`, `VocabOk` and `BitvecWidthOnly`. The capstone then builds the rank and
  the division of the constructors itself. It uses `rankExists` for the rank, and the
  lemmas about coverage for the division. Read `visibleRefs_cover_of_appears`. The caller
  gives no order of the datatypes, no rank and no set of names for one position.

These are the parts that the two layers use:

* `permutationOf_complete`. The generator can make each permutation of a list. This lemma
  closes the permutation of the constructors of one datatype.
* `genFreshName_complete`, `genFreshNames_complete`, `genParamsList_complete` and
  `genRanks_complete`. The generator draws each list of names that are different in pairs,
  that it can reach and that are absent from the reserved list. It also draws each list of
  ranks under the limit.
* `genConstrArgs_complete`, `genConstrs_complete` and `genConstructors_complete`. The
  generator can make a target argument list, a target constructor list and a target
  datatype body, when the caller gives their names. It must also be able to make their
  argument types, which `genArgTy_complete_of_wf` and `genArgTy_complete_of_wf_partial`
  give.
* `rankExists`. This lemma builds a rank from `MutualADTWF.inhabited`. The rank has an
  upper limit, and two datatypes can share one rank. Each edge of the graph of name
  references that the inhabited constructors make gets a smaller rank. The proof removes
  one source at a time through `hasSource_of_tySymInhab`. This lemma takes the place of a
  topological sort, and it needs no order.
* `exists_uniform_bound` with `genArgTy_mono`. Each argument has its own size for
  reachability, and no limit on those sizes is present at the start. These two lemmas
  collect the sizes into one limit. Therefore the capstone can end with `∃ maxSize`.

Each result about completeness for a full block is clean in its axioms. It uses only
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace DatatypeGen

/-! ## Part 1: lemmas about the typing specification alone

These lemmas speak only about the terms in `Lambda.DatatypeWF`. They name no generator. -/

section SpecLemmas

/-- `LMonoTys.freeVars` is the `flatMap` of `LMonoTy.freeVars` over the list. This form is
    correct for a proof that takes one argument at a time. -/
theorem freeVars_tcons_eq_flatMap (k : String) (args : LMonoTys) :
    LMonoTy.freeVars (.tcons k args) = args.flatMap LMonoTy.freeVars := by
  rw [LMonoTy.freeVars]
  induction args with
  | nil => simp [LMonoTys.freeVars]
  | cons h t ih => simp [LMonoTys.freeVars, ih]

/-- `LMonoTys.freeVars` gives the free variables of a *list* of monotypes, and it is the
    `flatMap` of `LMonoTy.freeVars`. This lemma is the form of `freeVars_tcons_eq_flatMap`
    for a list. -/
theorem lmonoTys_freeVars_eq_flatMap (args : LMonoTys) :
    LMonoTys.freeVars args = args.flatMap LMonoTy.freeVars := by
  induction args with
  | nil => simp [LMonoTys.freeVars]
  | cons h t ih => simp [LMonoTys.freeVars, ih]

/-- Map each member of `vs` to a rigid type variable. The free variables of the result are
    exactly `vs`. -/
theorem freeVars_map_ftvar (vs : List TyIdentifier) :
    LMonoTys.freeVars (vs.map LMonoTy.ftvar) = vs := by
  induction vs with
  | nil => simp [LMonoTys.freeVars]
  | cons h t ih => simp [LMonoTy.freeVars, ih]

/-- If the name `n` is absent from `n1 args`, then it is absent from each argument. -/
theorem absent_of_mem_args {n n1 : String} {args : LMonoTys} {t : LMonoTy}
    (h : TyNameAbsent n (.tcons n1 args)) (ht : t ∈ args) : TyNameAbsent n t :=
  fun hap => h (.arg n1 args t ht hap)

/-- If the name `n` is absent from `n1 args`, then `n1` is not `n`. If `n1` were `n`, then
    `n` would be the head of the application. -/
theorem ne_of_absent {n n1 : String} {args : LMonoTys}
    (h : TyNameAbsent n (.tcons n1 args)) : n1 ≠ n := by
  intro heq; subst heq; exact h (.head args)

/-- **Inversion of `TyNameAppears` at a `.tcons`.** An occurrence of `n` in `n1 args` has
    one of two forms. Either `n1` is `n`, or `n` occurs in one of the arguments.

    This file states this fact as a lemma, and it does not use the tactic `cases`.
    Therefore the fact also applies when `n` is a projection such as `d.name`. Dependent
    elimination on the head fails for such an `n`. -/
theorem tyNameAppears_tcons_inv {n n1 : String} {args : LMonoTys}
    (h : TyNameAppears n (.tcons n1 args)) :
    n1 = n ∨ ∃ t ∈ args, TyNameAppears n t := by
  generalize hty : LMonoTy.tcons n1 args = t at h
  cases h with
  | head as => injection hty with hn _; exact Or.inl hn
  | arg n' as t ht hat =>
    injection hty with _ has; subst has
    exact Or.inr ⟨t, ht, hat⟩

/-- If the name `n` appears in `ty`, then `n` is one of the type references of `ty`, which
    `getTypeRefs` collects.

    This lemma connects the declarative relation `TyNameAppears` to that function, which
    the proofs can evaluate. `rankExists` says that the inhabited constructor refers only
    to names of a lower rank, and it states that fact with `getTypeRefs` and `constrRefs`.
    This lemma changes that fact into the form of coverage that
    `genArgTy_complete_of_wf_partial` takes, which has `TyNameAppears` as its condition.
    The proof is an induction on `ty`. -/
theorem mem_getTypeRefs_of_tyNameAppears {n : String} :
    ∀ {ty : LMonoTy}, TyNameAppears n ty → n ∈ getTypeRefs ty := by
  intro ty
  induction ty with
  | ftvar v => intro h; cases h
  | bitvec sz => intro h; cases h
  | tcons n1 args ih =>
    intro h
    rcases tyNameAppears_tcons_inv h with rfl | ⟨t, ht, hat⟩
    · simp [getTypeRefs]
    · simp only [getTypeRefs, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨t, ht, ih t ht hat⟩

/-- **The whole type holds the argument variables of a name that occurs uniformly.**
    Assume that `n` occurs uniformly in `ty` with the arguments `uargs`, which
    `UniformOccur` gives. Assume also that `n` truly appears in `ty`, which
    `TyNameAppears` gives. Then each free variable of `uargs` is a free variable of `ty`.

    A uniform occurrence is `n uargs` with no change. Therefore `uargs` is a subterm of
    `ty`, and it gives its variables to `ty`. The proof is an induction on `ty`. The case
    `.self` reads `freeVars (n uargs) = freeVars uargs` from `freeVars_tcons`. -/
theorem uniformOccur_args_freeVars {n : String} {uargs : LMonoTys} :
    ∀ {ty : LMonoTy}, UniformOccur n uargs ty → TyNameAppears n ty →
      ∀ v ∈ LMonoTys.freeVars uargs, v ∈ LMonoTy.freeVars ty := by
  intro ty
  induction ty with
  | ftvar v => intro _ hap; cases hap
  | bitvec sz => intro _ hap; cases hap
  | tcons n1 args1 ih =>
    intro huni hap v hv
    cases huni with
    | self =>
      -- Here `n1 = n` and `args1 = uargs`, therefore
      -- `freeVars (n uargs) = flatMap freeVars uargs`.
      rw [freeVars_tcons_eq_flatMap]
      rwa [lmonoTys_freeVars_eq_flatMap] at hv
    | other n1' args1' hne huni' =>
      rcases tyNameAppears_tcons_inv hap with rfl | ⟨t, ht, hat⟩
      · exact absurd rfl hne
      · rw [freeVars_tcons_eq_flatMap]
        exact List.mem_flatMap.mpr ⟨t, ht, ih t ht (huni' t ht) hat v hv⟩

/-- Assume that the name `n` is absent from a type. Then that type is uniform in `n` for
    each `uargs`, because no occurrence of `n` is present to check. -/
theorem absent_uniform {n : String} {uargs : LMonoTys} {ty : LMonoTy}
    (h : TyNameAbsent n ty) : UniformOccur n uargs ty := by
  induction ty with
  | ftvar v => exact .ftvar v
  | bitvec sz => exact .bitvec sz
  | tcons n1 args ih =>
    exact .other n1 args (ne_of_absent h) (fun t ht => ih t ht (absent_of_mem_args h ht))

/-- The name of each datatype of `block` is absent from `ty`. This condition is the form of
    `TyNameAbsent d.name ty` for a mutual block. A type that the generator makes with
    `recCallsAllowed := false` obeys this condition. Such a type is then a well-formed
    constructor argument. Read `absent_constrArgWF`. -/
def BlockAbsent (block : MutualDatatype Unit) (ty : LMonoTy) : Prop :=
  ∀ d ∈ block, TyNameAbsent d.name ty

/-- If `BlockAbsent` holds for an application, then it holds for each argument of that
    application. -/
theorem blockAbsent_of_mem_args {block : MutualDatatype Unit} {n1 : String}
    {args : LMonoTys} {t : LMonoTy}
    (h : BlockAbsent block (.tcons n1 args)) (ht : t ∈ args) : BlockAbsent block t :=
  fun d hd => absent_of_mem_args (h d hd) ht

/-- If each block name is absent from `n1 args`, then `n1` is not a block name. If `n1`
    were a block name, then it would be the head of an occurrence that the specification
    forbids. -/
theorem head_not_mem_of_blockAbsent {block : MutualDatatype Unit} {n1 : String}
    {args : LMonoTys} (h : BlockAbsent block (.tcons n1 args)) :
    n1 ∉ block.map (·.name) := by
  intro hmem
  obtain ⟨d, hd, hname⟩ := List.mem_map.mp hmem
  exact h d hd (hname ▸ .head args)

/-- Assume that each block name is absent from a type. Then that type holds no nested
    occurrence of a block datatype. The pattern that the specification rejects is a block
    datatype inside the arguments of another type constructor. That pattern needs an
    occurrence, and no occurrence is present. -/
theorem absent_notNested {block : MutualDatatype Unit} {ty : LMonoTy}
    (h : BlockAbsent block ty) : NotNested block ty := by
  induction ty with
  | ftvar v => exact .ftvar v
  | bitvec sz => exact .bitvec sz
  | tcons n1 args ih =>
    by_cases hbin : IsBinaryArrow (LMonoTy.tcons n1 args)
    · -- An arrow of 2 arguments. Recurse into both sides, because the specification
      -- matches `.arrow` first.
      obtain ⟨t1, t2, heq⟩ := hbin
      rw [LMonoTy.arrow] at heq
      injection heq with hn hl
      subst hn; subst hl
      exact .arrow t1 t2 (ih t1 (by simp) (blockAbsent_of_mem_args h (by simp)))
                         (ih t2 (by simp) (blockAbsent_of_mem_args h (by simp)))
    · exact .headOther n1 args hbin (head_not_mem_of_blockAbsent h)
        (fun d' hd' a ha => absent_of_mem_args (h d' hd') ha)
        (fun a ha => ih a ha (blockAbsent_of_mem_args h ha))

/-- Assume that each block name is absent from a type. Then that type is strictly positive
    and uniform for `block`. Again, no occurrence is present to check. -/
theorem absent_strictPosUnif {block : MutualDatatype Unit} {ty : LMonoTy}
    (h : BlockAbsent block ty) : StrictPosUnif block ty := by
  induction ty with
  | ftvar v =>
    exact .base _ (by simp [IsBinaryArrow, LMonoTy.arrow])
      (fun d' hd' => absent_uniform (h d' hd'))
  | bitvec sz =>
    exact .base _ (by simp [IsBinaryArrow, LMonoTy.arrow])
      (fun d' hd' => absent_uniform (h d' hd'))
  | tcons n1 args ih =>
    by_cases hbin : IsBinaryArrow (LMonoTy.tcons n1 args)
    · obtain ⟨t1, t2, heq⟩ := hbin
      rw [LMonoTy.arrow] at heq
      injection heq with hn hl
      subst hn; subst hl
      refine .arrow t1 t2 ?_ (ih t2 (by simp) (blockAbsent_of_mem_args h (by simp)))
      intro d' hd'
      exact absent_of_mem_args (h d' hd') (by simp)
    · exact .base _ hbin (fun d' hd' => absent_uniform (h d' hd'))

/-- **The main lemma about the specification.** Assume that no block name occurs in a type.
    Then that type is a well-formed constructor argument for `block`. Both halves of
    `ConstrArgWF` speak about the *occurrences* of the block datatypes. No occurrence is
    present, therefore the type breaks no condition.

    This lemma is the reason that `DatatypeGen.genArgTy` puts `recCallsAllowed := false`
    into the domain of each arrow and into the arguments of each type constructor. This one
    lemma discharges the obligation of well-formedness for each type that the generator
    makes with that flag. -/
theorem absent_constrArgWF {block : MutualDatatype Unit} {ty : LMonoTy}
    (h : BlockAbsent block ty) : ConstrArgWF block ty :=
  ⟨absent_notNested h, absent_strictPosUnif h⟩

/-! ### A permutation of the block keeps the relations for well-formedness

The relations `NotNested` and `StrictPosUnif` read `block` in only two ways. They read
`block.map (·.name)` for the conditions on a head symbol, and they read `∀ d ∈ block` for
absence and for uniformity. A permutation keeps both of these. Therefore all three
relations hold after a permutation of the block, which `constrArgWF_perm` gives. The
`argsWF` case of `MutualADTWF_perm` uses these lemmas. -/

/-- `NotNested` holds after a permutation of the block. The proof is an induction on the
    derivation. At each point that reads the set of block names or a membership fact, the
    proof puts `block'` in place of `block` through the permutation. -/
theorem notNested_perm {block block' : MutualDatatype Unit} {ty : LMonoTy}
    (hnames : (block.map (·.name)).Perm (block'.map (·.name)))
    (hperm : block.Perm block') (h : NotNested block ty) : NotNested block' ty := by
  induction h with
  | ftvar v => exact .ftvar v
  | bitvec sz => exact .bitvec sz
  | arrow t1 t2 _ _ ih1 ih2 => exact .arrow t1 t2 ih1 ih2
  | headBlock n args hmem => exact .headBlock n args (hnames.mem_iff.mp hmem)
  | headOther n args hbin hnotmem habs _ ih =>
    refine .headOther n args hbin (fun hmem => hnotmem (hnames.mem_iff.mpr hmem)) ?_ ih
    intro d hd a ha; exact habs d (hperm.mem_iff.mpr hd) a ha

/-- `StrictPosUnif` holds after a permutation of the block. -/
theorem strictPosUnif_perm {block block' : MutualDatatype Unit} {ty : LMonoTy}
    (hperm : block.Perm block') (h : StrictPosUnif block ty) : StrictPosUnif block' ty := by
  induction h with
  | arrow t1 t2 habs _ ih =>
    exact .arrow t1 t2 (fun d hd => habs d (hperm.mem_iff.mpr hd)) ih
  | base ty hbin huni =>
    exact .base ty hbin (fun d hd => huni d (hperm.mem_iff.mpr hd))

/-- `ConstrArgWF` holds after a permutation of the block. Both of its halves hold. -/
theorem constrArgWF_perm {block block' : MutualDatatype Unit} {ty : LMonoTy}
    (hnames : (block.map (·.name)).Perm (block'.map (·.name)))
    (hperm : block.Perm block') (h : ConstrArgWF block ty) : ConstrArgWF block' ty :=
  ⟨notNested_perm hnames hperm h.1, strictPosUnif_perm hperm h.2⟩

end SpecLemmas

/-! ## Part 2: a description of the support of the generator

The lemmas `genLeafTy_mem_iff` and `genArgTy_mem_iff` describe what each generator can
make. Each lemma states the support as a disjunction, and this file adds no helper
relation. The proof of soundness and the proof of completeness then do their own strong
induction on `size` through these two lemmas. -/

section Support

/-- Each natural number is in the support of `Nat.arbitrary` at `SetGen.Set`. Therefore the
    width generator inside `pickBitvecWidth` can make each width. Read issue #38.

    A private lemma of the same shape is in `HasTypeAGen.lean`. That file does not export
    it, therefore this file states it again. -/
private theorem Nat_arbitrary_support_set (n : Nat) :
    n ∈ SetGen.support (Nat.arbitrary (G := SetGen.Set)) := by
  induction n with
  | zero => rw [Nat.arbitrary]; simp
  | succ n ih =>
    rw [Nat.arbitrary]
    simp only [mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff]
    exact Or.inr ⟨n, ih, rfl⟩

/-- `genBaseTy` makes exactly two kinds of type. It makes the bitvectors of each width, and
    it makes the applications of a `baseTypes` name to no arguments. -/
theorem genBaseTy_support (baseTypes : List String) (ty : LMonoTy) :
    ty ∈ SetGen.support (genBaseTy (G := SetGen.Set) baseTypes) ↔
      (∃ w, ty = .bitvec w) ∨
      (∃ b ∈ baseTypes, ty = .tcons b []) := by
  simp only [genBaseTy, mem_support_oneOf_iff, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨g, (rfl | ⟨b, hb, rfl⟩), hmem⟩
    · simp only [pickBitvecWidth, mem_support_map_iff] at hmem
      obtain ⟨w, _, rfl⟩ := hmem
      exact Or.inl ⟨w, rfl⟩
    · exact Or.inr ⟨b, hb, hmem⟩
  · rintro (⟨w, rfl⟩ | ⟨b, hb, rfl⟩)
    · refine ⟨_, Or.inl rfl, ?_⟩
      simp only [pickBitvecWidth, mem_support_map_iff]
      exact ⟨w, Nat_arbitrary_support_set w, rfl⟩
    · exact ⟨_, Or.inr ⟨b, hb, rfl⟩, by simp⟩


/-- The support of the generator for a recursive occurrence. That generator makes exactly
    the uniform occurrences `.tcons p.1 p.2` for the block references `p`. -/
theorem genRecOcc_mem_iff (br : BlockRef) (brs : List BlockRef) (t : LMonoTy) :
    t ∈ SetGen.support
      ((do let (n, args) ← elements (br :: brs) (List.cons_ne_nil br brs)
           pure (.tcons n args)) : SetGen.Set LMonoTy) ↔
    ∃ p ∈ br :: brs, t = .tcons p.1 p.2 := by
  simp only [mem_support_bind_iff, mem_support_pure_iff,
             mem_support_elements_iff (List.cons_ne_nil br brs)]

/-- **The support of `genLeafTy` as a disjunction**, with no inductive relation. Each type
    in that support has one of four forms:

    * a bitvector of one width;
    * a base type;
    * a rigid type variable, which is a type parameter of the datatype;
    * a uniform recursive occurrence `br.1 br.2` for a block reference
      `br ∈ blockRefs`. This form is present only when `recCallsAllowed` is `true`.

    This lemma is the base case of the inductions for soundness and for completeness
    below. -/
theorem genLeafTy_mem_iff (baseTypes : List String) (blockRefs : List BlockRef)
    (tyParams : List TyIdentifier) (rca : Bool) (ty : LMonoTy) :
    ty ∈ SetGen.support
      (genLeafTy (G := SetGen.Set) baseTypes blockRefs tyParams rca) ↔
      (∃ w, ty = .bitvec w) ∨
      (∃ b ∈ baseTypes, ty = .tcons b []) ∨
      (∃ v ∈ tyParams, ty = .ftvar v) ∨
      (rca = true ∧ ∃ br ∈ blockRefs, ty = .tcons br.1 br.2) := by
  have hvar : ∀ (v : TyIdentifier) vs t,
      t ∈ SetGen.support
        ((LMonoTy.ftvar <$> elements (v :: vs) (List.cons_ne_nil v vs) : SetGen.Set LMonoTy)) ↔
      ∃ v' ∈ v :: vs, t = .ftvar v' := by
    intro v vs t
    simp only [mem_support_map_iff, mem_support_elements_iff (List.cons_ne_nil v vs)]
  unfold genLeafTy
  match tyParams, rca, blockRefs with
  | [], false, _ =>
    rw [genBaseTy_support]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | ⟨_, hv, _⟩ | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hv (by simp)
      · exact absurd h (by simp)
  | [], true, [] =>
    rw [genBaseTy_support]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | ⟨_, hv, _⟩ | ⟨_, _, hbr, _⟩)
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hv (by simp)
      · exact absurd hbr (by simp)
  | [], true, br :: brs =>
    simp only [mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨g, (rfl | rfl), hmem⟩
      · rcases (genBaseTy_support _ _).mp hmem with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨p, hp, rfl⟩ := (genRecOcc_mem_iff br brs ty).mp hmem
        exact Or.inr (Or.inr (Or.inr ⟨trivial, p, List.mem_cons.mp hp, rfl⟩))
    · rintro (h | h | ⟨_, hv, _⟩ | ⟨_, p, hp, rfl⟩)
      · exact ⟨_, Or.inl rfl, (genBaseTy_support _ _).mpr (Or.inl h)⟩
      · exact ⟨_, Or.inl rfl, (genBaseTy_support _ _).mpr (Or.inr h)⟩
      · exact absurd hv (by simp)
      · exact ⟨_, Or.inr rfl, (genRecOcc_mem_iff br brs _).mpr ⟨p, List.mem_cons.mpr hp, rfl⟩⟩
  | v :: vs, false, _ =>
    simp only [mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨g, (rfl | rfl), hmem⟩
      · rcases (genBaseTy_support _ _).mp hmem with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨v', hv', rfl⟩ := (hvar v vs ty).mp hmem
        exact Or.inr (Or.inr (Or.inl ⟨v', List.mem_cons.mp hv', rfl⟩))
    · rintro (h | h | ⟨v', hv', rfl⟩ | ⟨h, _⟩)
      · exact ⟨_, Or.inl rfl, (genBaseTy_support _ _).mpr (Or.inl h)⟩
      · exact ⟨_, Or.inl rfl, (genBaseTy_support _ _).mpr (Or.inr h)⟩
      · exact ⟨_, Or.inr rfl, (hvar v vs _).mpr ⟨v', List.mem_cons.mpr hv', rfl⟩⟩
      · exact absurd h (by simp)
  | v :: vs, true, [] =>
    simp only [mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨g, (rfl | rfl), hmem⟩
      · rcases (genBaseTy_support _ _).mp hmem with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨v', hv', rfl⟩ := (hvar v vs ty).mp hmem
        exact Or.inr (Or.inr (Or.inl ⟨v', List.mem_cons.mp hv', rfl⟩))
    · rintro (h | h | ⟨v', hv', rfl⟩ | ⟨_, _, hbr, _⟩)
      · exact ⟨_, Or.inl rfl, (genBaseTy_support _ _).mpr (Or.inl h)⟩
      · exact ⟨_, Or.inl rfl, (genBaseTy_support _ _).mpr (Or.inr h)⟩
      · exact ⟨_, Or.inr rfl, (hvar v vs _).mpr ⟨v', List.mem_cons.mpr hv', rfl⟩⟩
      · exact absurd hbr (by simp)
  | v :: vs, true, br :: brs =>
    simp only [mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨g, (rfl | rfl | rfl), hmem⟩
      · rcases (genBaseTy_support _ _).mp hmem with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨v', hv', rfl⟩ := (hvar v vs ty).mp hmem
        exact Or.inr (Or.inr (Or.inl ⟨v', List.mem_cons.mp hv', rfl⟩))
      · obtain ⟨p, hp, rfl⟩ := (genRecOcc_mem_iff br brs ty).mp hmem
        exact Or.inr (Or.inr (Or.inr ⟨trivial, p, List.mem_cons.mp hp, rfl⟩))
    · rintro (h | h | ⟨v', hv', rfl⟩ | ⟨_, p, hp, rfl⟩)
      · exact ⟨_, Or.inl rfl, (genBaseTy_support _ _).mpr (Or.inl h)⟩
      · exact ⟨_, Or.inl rfl, (genBaseTy_support _ _).mpr (Or.inr h)⟩
      · exact ⟨_, Or.inr (Or.inl rfl), (hvar v vs _).mpr ⟨v', List.mem_cons.mpr hv', rfl⟩⟩
      · exact ⟨_, Or.inr (Or.inr rfl), (genRecOcc_mem_iff br brs _).mpr ⟨p, List.mem_cons.mpr hp, rfl⟩⟩

/-! ### The support of `genArgTy`

At each `size` other than `0`, `genArgTy` gives three alternatives. They are an arrow, a
type from `genLeafTy`, and an application of a known type constructor. At `size = 0` it
gives only the type from `genLeafTy`.

The generator sets its flag to `false` in the two positions that keep the output
well-formed. These positions are the domain of an arrow and the arguments of an
application. The recursion at those positions carries the flag `false`.

`genArgTy_mem_iff` describes the support in one step. Its right side is a disjunction, and
that disjunction refers back to `SetGen.support (genArgTy … (size/2))`. This file adds no
helper relation. The theorems for soundness and for completeness then do their own strong
induction on `size` through this lemma. -/

/-- **The support of `genArgTy` in one step**, with no inductive relation.

    At `size = 0` the support holds exactly the types from `genLeafTy`. At a larger size it
    also holds two more kinds. The first kind is an arrow, and the generator makes its
    domain with the flag `false` and its codomain with the flag from the caller. The second
    kind is an application of a `tyCons` constructor. That application has the number of
    arguments that its arity gives, and the generator makes each argument with the flag `false`.
    The recursive positions refer back to the support at `size/2`. -/
theorem genArgTy_mem_iff (baseTypes : List String) (tyCons : List KnownTyCon)
    (blockRefs : List BlockRef) (tyParams : List TyIdentifier)
    (rca : Bool) (size : Nat) (ty : LMonoTy) :
    ty ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs tyParams rca size) ↔
      ty ∈ SetGen.support
        (genLeafTy (G := SetGen.Set) baseTypes blockRefs tyParams rca) ∨
      (size ≠ 0 ∧ ∃ t1 t2, ty = .arrow t1 t2 ∧
        t1 ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
          tyParams false (size / 2)) ∧
        t2 ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
          tyParams rca (size / 2))) ∨
      (size ≠ 0 ∧ ∃ k args, ty = .tcons k args ∧ (k, args.length) ∈ tyCons ∧
        ∀ a ∈ args, a ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons
          blockRefs tyParams false (size / 2))) := by
  by_cases hs : size = 0
  · -- Only the leaf disjunct is available.
    subst hs
    rw [genArgTy]
    simp only [reduceIte, ne_eq, not_true_eq_false, false_and, or_false]
  · rw [genArgTy]
    simp only [if_neg hs]
    -- The arrow branch's support, shared by both `tyCons` cases.
    have harrow : ∀ t, t ∈ SetGen.support
        ((do let t1 ← genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
               tyParams false (size / 2)
             let t2 ← genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
               tyParams rca (size / 2)
             pure (.arrow t1 t2)) : SetGen.Set LMonoTy) ↔
        ∃ t1 t2, t = .arrow t1 t2 ∧
          t1 ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
            tyParams false (size / 2)) ∧
          t2 ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
            tyParams rca (size / 2)) := by
      intro t
      simp only [mem_support_bind_iff, mem_support_pure_iff]
      constructor
      · rintro ⟨t1, ht1, t2, ht2, rfl⟩; exact ⟨t1, t2, rfl, ht1, ht2⟩
      · rintro ⟨t1, t2, rfl, h1, h2⟩; exact ⟨t1, h1, t2, h2, rfl⟩
    match tyCons with
    | [] =>
      simp only [mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨g, (rfl | rfl), hmem⟩
        · exact Or.inr (Or.inl ⟨hs, (harrow ty).mp hmem⟩)
        · exact Or.inl hmem
      · rintro (hleaf | ⟨_, t1, t2, rfl, h1, h2⟩ | ⟨_, k, args, _, hkc, _⟩)
        · exact ⟨_, Or.inr rfl, hleaf⟩
        · exact ⟨_, Or.inl rfl, (harrow _).mpr ⟨t1, t2, rfl, h1, h2⟩⟩
        · exact absurd hkc (by simp)
    | kc :: kcs =>
      have happ : ∀ t, t ∈ SetGen.support
          ((do let (tyCtor, arity) ← elements (kc :: kcs) (List.cons_ne_nil kc kcs)
               let argTys ← vectorOf arity (genArgTy (G := SetGen.Set) baseTypes
                 (kc :: kcs) blockRefs tyParams false (size / 2))
               pure (.tcons tyCtor argTys)) : SetGen.Set LMonoTy) ↔
          ∃ k args, t = .tcons k args ∧ (k, args.length) ∈ kc :: kcs ∧
            ∀ a ∈ args, a ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes
              (kc :: kcs) blockRefs tyParams false (size / 2)) := by
        intro t
        simp only [mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_elements_iff (List.cons_ne_nil kc kcs)]
        constructor
        · rintro ⟨⟨tyCtor, arity⟩, hkc, args, hargs, rfl⟩
          obtain ⟨hlen, hall⟩ := mem_support_vectorOf_iff.mp hargs
          exact ⟨tyCtor, args, rfl, hlen ▸ hkc, hall⟩
        · rintro ⟨k, args, rfl, hkc, hall⟩
          exact ⟨(k, args.length), hkc, args,
            mem_support_vectorOf_iff.mpr ⟨rfl, hall⟩, rfl⟩
      simp only [mem_support_oneOf_iff, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨g, (rfl | rfl | rfl), hmem⟩
        · exact Or.inr (Or.inl ⟨hs, (harrow ty).mp hmem⟩)
        · exact Or.inl hmem
        · obtain ⟨k, args, rfl, hkc, hall⟩ := (happ ty).mp hmem
          exact Or.inr (Or.inr ⟨hs, k, args, rfl, List.mem_cons.mp hkc, hall⟩)
      · rintro (hleaf | ⟨_, t1, t2, rfl, h1, h2⟩ | ⟨_, k, args, rfl, hkc, hall⟩)
        · exact ⟨_, Or.inr (Or.inl rfl), hleaf⟩
        · exact ⟨_, Or.inl rfl, (harrow _).mpr ⟨t1, t2, rfl, h1, h2⟩⟩
        · exact ⟨_, Or.inr (Or.inr rfl),
            (happ _).mpr ⟨k, args, rfl, List.mem_cons.mpr hkc, hall⟩⟩


/-- **The support of `genArgTy` grows with the set of references.** Add more members to
    `blockRefs`, and keep each member that is already present. Then the generator can make
    each type that it could make before, and possibly more. The recursive occurrence is the
    only place that reads `blockRefs`, and a larger set gives more such occurrences. The
    proof is a strong induction on `size` through the one-step description of the support.

    This lemma lifts the argument types of the inhabited constructor. The generator draws
    them from the small set `inhabRefs`, and this lemma puts them in the full set
    `visibleRefs`. Therefore the lemmas for soundness can read one set only. -/
theorem genArgTy_blockRefs_mono {baseTypes : List String} {tyCons : List KnownTyCon}
    {blockRefs blockRefs' : List BlockRef} {tyParams : List TyIdentifier}
    (hsub : ∀ br ∈ blockRefs, br ∈ blockRefs') :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) →
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs'
        tyParams rca size) := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro rca ty h
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · -- A type from `genLeafTy`. Only the part for a recursive occurrence reads
      -- `blockRefs`.
      refine (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)
      rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨w, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨hrca, br, hbrmem, rfl⟩
      · exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inl ⟨w, rfl⟩)
      · exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inl ⟨b, hb, rfl⟩))
      · exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨v, hv, rfl⟩)))
      · exact (genLeafTy_mem_iff _ _ _ _ _).mpr
          (Or.inr (Or.inr (Or.inr ⟨hrca, br, hsub br hbrmem, rfl⟩)))
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      exact (genArgTy_mem_iff _ _ _ _ _ _ _).mpr
        (Or.inr (Or.inl ⟨hsz', t1, t2, rfl, ih _ hhalf h1, ih _ hhalf h2⟩))
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega)
      exact (genArgTy_mem_iff _ _ _ _ _ _ _).mpr
        (Or.inr (Or.inr ⟨hsz, k, args, rfl, hkc, fun a ha => ih _ hhalf (hall a ha)⟩))

end Support

/-! ## Part 3: soundness against the typing specification

This part shows that `ty ∈ support (genArgTy …)` gives `ConstrArgWF [d] ty`. The proof is a
strong induction on `size` through `genArgTy_mem_iff`. Therefore each type that `genArgTy`
makes is a well-formed constructor argument.

### The side conditions, and the reason for them

`LMonoTy.arrow t1 t2` is by definition `LMonoTy.tcons "arrow" [t1, t2]`. Therefore a type
constructor with the name `"arrow"` reads as a true arrow. `NotNested` and `StrictPosUnif`
in the specification match `.arrow` before the general case `.tcons`. Therefore the proofs
must exclude that name:

* No block name is `"arrow"`. If a block name were `"arrow"`, then a recursive occurrence
  `n args` would read as an arrow each time that `args` holds 2 types.
* No `tyCons` name is `"arrow"`. If a `tyCons` name were `"arrow"`, then an application of
  arity 2 would read as an arrow.

Two more conditions stop a name from hiding a block datatype:

* No `tyCons` name is a block name. If one were a block name, then an application would
  read as a recursive occurrence, and that occurrence can be not uniform. Therefore
  uniformity would fail.
* No `baseTypes` name is a block name. If one were a block name, then the type
  `.tcons b []` would read as a recursive occurrence with no arguments. Such an occurrence
  is not uniform when the datatype has type parameters.

`NamesOk` holds these four conditions. It now speaks about the *set* of block names, which
is `block.map (·.name)`, and not about one name `selfName`. The rule for the reserved names
gives three of the four conditions. `initialReserved` holds `"arrow"` and each name from
`baseTypes` and `tyCons`, and the generator draws each block name fresh against that list.
Read `namesOk_of_fresh`.

The fourth condition is `tyCon_ne_arrow`. It puts a limit on the pool that the *caller*
gives, and not on a name that the generator makes. Therefore it stays a hypothesis.
`defaultTyCons` obeys it by `decide`.

`BlockRefsWF` holds what the soundness proof needs to know about the set of references
`blockRefs`. Each reference names a true block datatype, which is `mem`. A reference to a
block datatype applies it to exactly its own type arguments, which is `uniform`. The
arguments of a reference are all type variables, which is `ftvarArgs`.
`genMutuallyRecursiveDatatypes` gives all of these by construction, through
`visibleRefs`. -/

section Soundness

/-- The side conditions on the name parameters of the generator. These conditions are
    necessary for two reasons. `LMonoTy.arrow` is a `.tcons` with the reserved name
    `"arrow"`, and the caller gives the name pools of the generator. This structure speaks
    about the set of block names `blockNames`, which is `block.map (·.name)`. -/
structure NamesOk (baseTypes : List String) (tyCons : List KnownTyCon)
    (blockNames : List String) : Prop where
  /-- No block name is the reserved constructor for an arrow. -/
  block_ne_arrow : ∀ n ∈ blockNames, n ≠ "arrow"
  /-- No applied type constructor is the reserved constructor for an arrow. -/
  tyCon_ne_arrow : ∀ kc ∈ tyCons, kc.1 ≠ "arrow"
  /-- No applied type constructor has the same name as a block datatype. -/
  tyCon_notMem : ∀ kc ∈ tyCons, kc.1 ∉ blockNames
  /-- No base type has the same name as a block datatype. -/
  base_notMem : ∀ b ∈ baseTypes, b ∉ blockNames

/-- The facts about the set of references `blockRefs` that the soundness proof needs, for
    one block and one list of type parameters `tyParams`. `visibleRefs` obeys all four
    fields by construction. Read `visibleRefs_blockRefsWF`. -/
structure BlockRefsWF (block : MutualDatatype Unit) (tyParams : List TyIdentifier)
    (blockRefs : List BlockRef) : Prop where
  /-- Each reference names a true block datatype. -/
  mem : ∀ br ∈ blockRefs, br.1 ∈ block.map (·.name)
  /-- A reference to a block datatype applies it to exactly its own type arguments. This
      field gives uniformity. -/
  uniform : ∀ br ∈ blockRefs, ∀ d ∈ block, d.name = br.1 → br.2 = d.typeArgs.map .ftvar
  /-- The arguments of a reference are all type variables. Therefore the reference is never
      nested, and it adds no reference other than its head name. -/
  ftvarArgs : ∀ br ∈ blockRefs, ∀ a ∈ br.2, ∃ v, a = LMonoTy.ftvar v
  /-- The argument variables of a reference are all declared type parameters. Therefore a
      recursive occurrence adds no variable that is out of scope, which `argVarsScoped`
      needs. -/
  argsScoped : ∀ br ∈ blockRefs, ∀ v ∈ LMonoTys.freeVars br.2, v ∈ tyParams

/-- If `k` is not `"arrow"`, then `.tcons k args` is not an arrow of 2 arguments. -/
theorem not_isBinaryArrow_of_ne {k : String} {args : LMonoTys} (h : k ≠ "arrow") :
    ¬ IsBinaryArrow (.tcons k args) := by
  rintro ⟨t1, t2, heq⟩
  rw [LMonoTy.arrow] at heq
  injection heq with hn _
  exact h hn

/-- **`ConstrArgWF` of an arrow divides into three facts.** Assume that no block name is
    `"arrow"`. Then only the `.arrow` cases of `NotNested` and `StrictPosUnif` apply. The
    three facts are: each block name is absent from the domain, the domain is well-formed,
    and the codomain is well-formed.

    The soundness direction builds `ConstrArgWF` from `absent_...` and the case for an
    arrow. This lemma is the opposite direction, in the form that the recursion for
    completeness takes. -/
theorem constrArgWF_arrow {block : MutualDatatype Unit} {t1 t2 : LMonoTy}
    (harrow : ∀ d ∈ block, d.name ≠ "arrow")
    (h : ConstrArgWF block (.arrow t1 t2)) :
    BlockAbsent block t1 ∧ ConstrArgWF block t1 ∧ ConstrArgWF block t2 := by
  obtain ⟨hnn, hsp⟩ := h
  -- For `NotNested`, only the constructor `.arrow` applies.
  have hnn' : NotNested block t1 ∧ NotNested block t2 := by
    cases hnn with
    | arrow _ _ h1 h2 => exact ⟨h1, h2⟩
    | headBlock _ _ hmem =>
      obtain ⟨d, hd, hname⟩ := List.mem_map.mp hmem
      exact absurd hname (harrow d hd)
    | headOther _ _ hbin _ _ _ => exact absurd ⟨t1, t2, rfl⟩ hbin
  -- For `StrictPosUnif`, only the constructor `.arrow` applies.
  have hsp' : BlockAbsent block t1 ∧ StrictPosUnif block t2 := by
    cases hsp with
    | arrow _ _ hab hsp2 => exact ⟨hab, hsp2⟩
    | base _ hbin _ => exact absurd ⟨t1, t2, rfl⟩ hbin
  exact ⟨hsp'.1, ⟨hnn'.1, absent_strictPosUnif hsp'.1⟩, ⟨hnn'.2, hsp'.2⟩⟩

/-- **`ConstrArgWF` makes each recursive occurrence uniform.** Take a block datatype `d` and
    an application with `d.name` at the head. If that application is `ConstrArgWF block`,
    then it applies `d.name` to exactly `d.typeArgs.map .ftvar`.

    This lemma reads the rule `UniformOccur.self` back from the specification. The case `base`
    of `StrictPosUnif` needs uniformity for each block datatype. The only uniform occurrence with
    `d.name` at the head is the application to its own type arguments.
    Therefore the residual side condition says nothing about a block occurrence, because
    `ConstrArgWF` already fixes its shape. -/
theorem constrArgWF_self_uniform {block : MutualDatatype Unit} {d : LDatatype Unit}
    {args : LMonoTys} (hd : d ∈ block)
    (harrow : ∀ d ∈ block, d.name ≠ "arrow")
    (h : ConstrArgWF block (.tcons d.name args)) :
    args = d.typeArgs.map .ftvar := by
  obtain ⟨_, hsp⟩ := h
  -- Generalize the type at the index, therefore the proof can invert `StrictPosUnif`.
  generalize hty : LMonoTy.tcons d.name args = t at hsp
  cases hsp with
  | arrow t1 t2 _ _ =>
    -- `.arrow` is `.tcons "arrow" [_, _]`, therefore this case gives `d.name = "arrow"`.
    rw [LMonoTy.arrow] at hty
    injection hty with hn _
    exact absurd hn (harrow d hd)
  | base ty _ huni =>
    subst hty
    -- Uniformity for the block datatype `d`. The case `.self` gives the arguments with no
    -- change.
    cases huni d hd with
    | self => rfl
    | other n1 args1 hne _ => exact absurd rfl hne

/-- Each block name is absent from a base type. This lemma needs the condition that no base
    type has the name of a block datatype. It is a separate lemma for two reasons. It is the
    one case of `genLeafTy` that needs `NamesOk`, and several proofs use it. -/
theorem base_absent {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {b : String}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hb : b ∈ baseTypes) : BlockAbsent block (.tcons b []) := by
  intro d hd hap
  cases hap with
  -- In this branch `b` is the same as `d.name`, therefore `b` is a block name. But
  -- `NamesOk` says that no base type is a block name.
  | head _ => exact hn.base_notMem _ hb (List.mem_map.mpr ⟨d, hd, rfl⟩)
  | arg _ _ t ht _ => cases ht

/-- Each block name is absent from a type that `genLeafTy` makes with
    `recCallsAllowed := false`. The proof reads `genLeafTy_mem_iff`. At the flag `false`
    that lemma excludes the part for a recursive occurrence, and no other part holds a
    block name. -/
theorem genLeafTy_absent {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier} {ty : LMonoTy}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (h : ty ∈ SetGen.support (genLeafTy (G := SetGen.Set) baseTypes blockRefs
            tyParams false)) :
    BlockAbsent block ty := by
  rcases (genLeafTy_mem_iff _ _ _ _ _).mp h with
    ⟨w, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨v, _, rfl⟩ | ⟨hrca, _⟩
  · intro d _ hap; cases hap
  · exact base_absent hn hb
  · intro d _ hap; cases hap
  · exact absurd hrca (by simp)

/-- **Each block name is absent from each type that `genArgTy` makes with
    `recCallsAllowed := false`.** This fact is the main property of the flag. The case for an
    arrow and the case for another type constructor in the specification both need it.

    The proof is a strong induction on `size` through `genArgTy_mem_iff`, which describes the
    support in one step. The proof adds no helper relation. -/
theorem genArgTy_absent {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hn : NamesOk baseTypes tyCons (block.map (·.name))) :
    ∀ (size : Nat) {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams false size) →
      BlockAbsent block ty := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro ty h
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · exact genLeafTy_absent hn hleaf
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      intro d hd hap
      rw [LMonoTy.arrow] at hap
      rcases tyNameAppears_tcons_inv hap with harr | ⟨t, ht, hat⟩
      · exact hn.block_ne_arrow _ (List.mem_map.mpr ⟨d, hd, rfl⟩) harr.symm
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact ih _ hhalf h1 d hd hat
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact ih _ hhalf h2 d hd hat
          · cases ht
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega)
      intro d hd hap
      rcases tyNameAppears_tcons_inv hap with hkeq | ⟨t, ht, hat⟩
      · exact hn.tyCon_notMem _ hkc (by rw [hkeq]; exact List.mem_map.mpr ⟨d, hd, rfl⟩)
      · exact ih _ hhalf (hall t ht) d hd hat

/-- **The half of `ConstrArgWF` that is `NotNested`**, on the support of `genArgTy` at each
    value of the flag. The proof is a strong induction on `size` through
    `genArgTy_mem_iff`. -/
theorem genArgTy_notNested {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hbr : BlockRefsWF block tyParams blockRefs) :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) →
      NotNested block ty := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro rca ty h
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · -- A type from `genLeafTy`. Read the four parts of `genLeafTy_mem_iff`.
      rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨w, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨v, _, rfl⟩ | ⟨_, br, hbrmem, rfl⟩
      · exact .bitvec w
      · exact absent_notNested (base_absent hn hb)
      · exact .ftvar v
      · exact .headBlock _ _ (hbr.mem br hbrmem)
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      exact .arrow t1 t2 (absent_notNested (genArgTy_absent hn _ h1)) (ih _ hhalf h2)
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega)
      refine .headOther k args
        (not_isBinaryArrow_of_ne (hn.tyCon_ne_arrow (k, args.length) hkc))
        (hn.tyCon_notMem (k, args.length) hkc) ?_ ?_
      · intro d' hd' a ha
        exact genArgTy_absent hn _ (hall a ha) d' hd'
      · intro a ha
        exact absent_notNested (genArgTy_absent hn _ (hall a ha))

/-- **The half of `ConstrArgWF` that is `StrictPosUnif`**, on the support of `genArgTy`.

    The recursive occurrence is the part that gives uniformity. The generator emits a block
    name, and it applies that name to exactly the `typeArgs.map .ftvar` of that datatype.
    This shape is `UniformOccur.self`, and `BlockRefsWF.uniform` gives it. -/
theorem genArgTy_strictPosUnif {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hbr : BlockRefsWF block tyParams blockRefs) :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) →
      StrictPosUnif block ty := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro rca ty h
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨w, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨v, _, rfl⟩ | ⟨_, br, hbrmem, rfl⟩
      · exact absent_strictPosUnif (by intro d _ hap; cases hap)
      · exact absent_strictPosUnif (base_absent hn hb)
      · exact absent_strictPosUnif (by intro d _ hap; cases hap)
      · -- A recursive occurrence `br.1 br.2`. It is not an arrow of 2 arguments, because
        -- `br.1` is a block name and therefore not `"arrow"`. It is also uniform in each
        -- block datatype. The case `.self` applies to the datatype that it names, and the
        -- case `.other` applies to each other datatype.
        have hmem := hbr.mem br hbrmem
        refine .base _ (not_isBinaryArrow_of_ne (hn.block_ne_arrow _ hmem)) ?_
        intro d' hd'
        by_cases hname : d'.name = br.1
        · -- The datatype that the reference names. Here
          -- `br.2 = d'.typeArgs.map .ftvar`, therefore the case is `.self`.
          have huniform := hbr.uniform br hbrmem d' hd' hname
          rw [← hname, huniform]; exact .self
        · -- Another datatype. The case is `.other`, and each argument is a type variable.
          refine .other br.1 br.2 (fun h => hname h.symm) ?_
          intro a ha
          obtain ⟨v, rfl⟩ := hbr.ftvarArgs br hbrmem a ha
          exact .ftvar v
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      refine .arrow t1 t2 ?_ (ih _ hhalf h2)
      intro d' hd'
      exact genArgTy_absent hn _ h1 d' hd'
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega)
      refine .base _ (not_isBinaryArrow_of_ne (hn.tyCon_ne_arrow (k, args.length) hkc)) ?_
      intro d' hd'
      refine .other k args ?_ ?_
      · intro heq
        exact hn.tyCon_notMem (k, args.length) hkc (heq ▸ List.mem_map.mpr ⟨d', hd', rfl⟩)
      · intro t ht
        exact absent_uniform (genArgTy_absent hn _ (hall t ht) d' hd')

/-- **Soundness on the support of the generator.** Each type that `genArgTy` draws for a
    block is a well-formed constructor argument type. This result holds at each value of the
    flag. -/
theorem genArgTy_constrArgWF {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier} {rca : Bool} {size : Nat} {ty : LMonoTy}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hbr : BlockRefsWF block tyParams blockRefs)
    (h : ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
            tyParams rca size)) :
    ConstrArgWF block ty :=
  ⟨genArgTy_notNested hn hbr size h, genArgTy_strictPosUnif hn hbr size h⟩

/-! ### The rule for the reserved names

`genFreshName reserved` returns a name that is absent from `reserved`. That one fact, with
the contents of `initialReserved`, gives each other result in this section. -/

/-- `fallbackName reserved` is 1 character longer than the longest reserved name. This proof
    uses `indexedFreshName_length` from `CmdHasTypeAGen/Core.lean`, because `fallbackName` is
    `indexedFreshName` at index `0`. -/
private theorem fallbackName_length (reserved : List String) :
    (fallbackName reserved).length = maxNameLength reserved + 1 := by
  simp [fallbackName, indexedFreshName_length]

/-- **The fallback name is never a reserved name.** It is longer than each reserved name,
    therefore it is not equal to any of them. This fact makes `genFreshName` total. The
    random draw can give a name that is already reserved, but the fallback cannot.

    The limit on the length comes from `foldl_max_ge_of_mem` in
    `CmdHasTypeAGen/Core.lean`, at `f := String.length`. -/
theorem fallbackName_not_mem (reserved : List String) :
    fallbackName reserved ∉ reserved := by
  intro hmem
  have hle := foldl_max_ge_of_mem String.length reserved _ hmem 0
  rw [fallbackName_length] at hle
  simp only [maxNameLength] at hle
  omega

/-- **`genFreshName` gives a fresh name.** Each name in its support is absent from
    `reserved`. It returns the random draw only when that draw is absent from `reserved`, and
    the fallback name is never a reserved name. -/
theorem genFreshName_fresh (reserved : List String) :
    ∀ s ∈ SetGen.support (genFreshName (G := SetGen.Set) reserved), s ∉ reserved := by
  intro s hs
  simp only [genFreshName, mem_support_bind_iff, mem_support_ite_iff,
             mem_support_pure_iff] at hs
  obtain ⟨s', _, hbranch⟩ := hs
  rcases hbranch with ⟨_, rfl⟩ | ⟨hne, rfl⟩
  · exact fallbackName_not_mem reserved
  · -- Here `reserved.contains s' = false`, which is `s' ∉ reserved`.
    simpa using hne

/-- **One fresh name obeys the conditions of `NamesOk` for a single name.** Take a name that
    the generator drew fresh against `initialReserved baseTypes tyCons`. That name is not
    `"arrow"`, it is no `tyCons` name, and it is no `baseTypes` name. The reason is that the
    list holds all of those names. `namesOk_of_fresh` applies this lemma to one name at a
    time, and it then builds the structure for the full set. -/
theorem fresh_name_conds {baseTypes : List String} {tyCons : List KnownTyCon}
    {extraReserved : List String} {n : String}
    (hfresh : n ∉ initialReserved baseTypes tyCons extraReserved) :
    n ≠ "arrow" ∧ (∀ kc ∈ tyCons, kc.1 ≠ n) ∧ (∀ b ∈ baseTypes, b ≠ n) := by
  simp only [initialReserved, List.mem_cons, List.mem_append, List.mem_map,
             not_or, not_exists] at hfresh
  obtain ⟨hne_arrow, hrest⟩ := hfresh
  refine ⟨hne_arrow, ?_, ?_⟩
  · intro kc hkc heq
    exact hrest.1.2 kc (by simp [hkc, heq])
  · intro b hb heq
    subst heq
    exact hrest.1.1.2 hb

/-- **`NamesOk` from fresh names.** Assume that the generator drew each block name fresh
    against `initialReserved baseTypes tyCons`. Then the full block obeys three of the four
    conditions of `NamesOk`, because that list holds `"arrow"` and each name from `baseTypes`
    and `tyCons`. The fourth condition is `tyCon_ne_arrow`. It is a condition on the pool
    that the caller gives, therefore this lemma takes it as a hypothesis. -/
theorem namesOk_of_fresh {baseTypes : List String} {tyCons : List KnownTyCon}
    {extraReserved : List String} {blockNames : List String}
    (harrow : ∀ kc ∈ tyCons, kc.1 ≠ "arrow")
    (hfresh : ∀ n ∈ blockNames, n ∉ initialReserved baseTypes tyCons extraReserved) :
    NamesOk baseTypes tyCons blockNames := by
  refine ⟨?_, harrow, ?_, ?_⟩
  · intro n hn
    exact (fresh_name_conds (hfresh n hn)).1
  · intro kc hkc hmem
    exact (fresh_name_conds (hfresh kc.1 hmem)).2.1 kc hkc rfl
  · intro b hb hmem
    exact (fresh_name_conds (hfresh b hmem)).2.2 b hb rfl

/-! ### The default vocabulary is `Core.KnownTypes`, split by arity

`defaultBaseTypes` and `defaultTyCons` are `filter`s of `Core.KnownTypes`
(`StrataGenerators/DatatypeGen.lean`). The three `_iff` lemmas here read those filters back,
in *both* directions.

The `mpr` direction is the interesting one. It turns an arity fact about `Core.KnownTypes` —
which is exactly what `MutualADTWF.argsWellKinded` hands out — into membership in the
generator's own vocabulary. That is what lets completeness drop the hand-written arity side
condition this file used to carry: read `VocabOk` and `BitvecWidthOnly` below.

All three are proven from the shape of the `filter`, not by `decide`/`native_decide`: they
hold for whatever `Core.KnownTypes` happens to contain, so they do not have to be revisited
when upstream registers a new primitive. -/

/-- Reading `defaultBaseTypes` back: it is exactly the arity-`0` part of `Core.KnownTypes`. -/
theorem mem_defaultBaseTypes_iff {b : String} :
    b ∈ defaultBaseTypes ↔ Core.KnownTypes[b]? = some 0 := by
  rw [defaultBaseTypes, List.mem_mergeSort, List.mem_filterMap]
  constructor
  · rintro ⟨⟨k, ar⟩, hmem, hb⟩
    split at hb
    · rename_i har
      injection hb with hb
      subst hb
      have : ar = 0 := by simpa using har
      subst this
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
    · exact absurd hb (by simp)
  · intro h
    exact ⟨(b, 0), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h, by simp⟩

/-- Reading `coreAppliedTyCons` back: it is exactly the part of `Core.KnownTypes` of positive
    arity, minus `arrow`. -/
theorem mem_coreAppliedTyCons_iff {kc : KnownTyCon} :
    kc ∈ coreAppliedTyCons ↔
      Core.KnownTypes[kc.1]? = some kc.2 ∧ kc.2 ≠ 0 ∧ kc.1 ≠ "arrow" := by
  obtain ⟨k, ar⟩ := kc
  rw [coreAppliedTyCons, List.mem_mergeSort, List.mem_filter,
    Std.HashMap.mem_toList_iff_getElem?_eq_some]
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true]

/-- Reading `defaultTyCons` back: `coreAppliedTyCons` minus `bitvec`. -/
theorem mem_defaultTyCons_iff {kc : KnownTyCon} :
    kc ∈ defaultTyCons ↔ kc ∈ coreAppliedTyCons ∧ kc.1 ≠ "bitvec" := by
  rw [defaultTyCons, List.mem_filter]
  simp only [bne_iff_ne, ne_eq]

/-- The default pool of type constructors holds no constructor with the name `"arrow"`.
    Therefore it discharges the one condition of `NamesOk` that a fresh name does not
    give. This now holds by construction: `coreAppliedTyCons` filters `arrow` out. -/
theorem defaultTyCons_ne_arrow : ∀ kc ∈ defaultTyCons, kc.1 ≠ "arrow" :=
  fun _ hkc => (mem_coreAppliedTyCons_iff.mp (mem_defaultTyCons_iff.mp hkc).1).2.2

/-- Every default type constructor is registered in `Core.KnownTypes` at its recorded arity. -/
theorem defaultTyCons_arity : ∀ kc ∈ defaultTyCons, Core.KnownTypes[kc.1]? = some kc.2 :=
  fun _ hkc => (mem_coreAppliedTyCons_iff.mp (mem_defaultTyCons_iff.mp hkc).1).1

/-- Every default base type is registered in `Core.KnownTypes` at arity `0`. -/
theorem defaultBaseTypes_arity : ∀ b ∈ defaultBaseTypes, Core.KnownTypes[b]? = some 0 :=
  fun _ hb => mem_defaultBaseTypes_iff.mp hb

/-- `Sequence` at **2** arguments is not in the default vocabulary, because `Core.KnownTypes`
    registers it at arity `1`. This is the counterexample behind
    `not_complete_without_arity`; `native_decide` is only for the one arity lookup. -/
theorem seq_two_not_mem_defaultTyCons : ("Sequence", 2) ∉ defaultTyCons := by
  intro h
  have h1 := defaultTyCons_arity _ h
  have h2 : Core.KnownTypes["Sequence"]? = some 1 := by native_decide
  rw [h2] at h1
  exact absurd h1 (by simp)

/-! ### From one type to a full constructor and a full datatype -/

/-- The support of `chooseNat lo hi` holds exactly the natural numbers in the range
    `[lo, hi]`. -/
@[simp] theorem mem_support_chooseNat_iff {lo hi n : Nat} {h : lo ≤ hi} :
    n ∈ SetGen.support (chooseNat (G := SetGen.Set) lo hi h) ↔ lo ≤ n ∧ n ≤ hi := by
  simp only [chooseNat, mem_support_map_iff, mem_support_choose_iff]
  constructor
  · rintro ⟨u, ⟨hlo, hhi⟩, rfl⟩; exact ⟨hlo, hhi⟩
  · rintro ⟨hlo, hhi⟩; exact ⟨⟨⟨n, hlo, hhi⟩⟩, ⟨hlo, hhi⟩, rfl⟩

/-- Each argument type in a list from `genConstrArgs` is in the support of `genArgTy` at some
    size. Therefore soundness goes from one type to a full constructor. The size is an
    existential value, because `genConstrArgs` draws a new `chooseNat 0 maxSize` for each
    argument.

    `genConstrArgs` adds the field names with a zip of the new names against the types.
    Therefore `List.of_mem_zip` gets the type back from a member of the result. -/
theorem genConstrArgs_mem_support {baseTypes : List String} {tyCons : List KnownTyCon}
    {blockRefs : List BlockRef} {tyParams : List TyIdentifier}
    {rca : Bool} {maxArgs maxSize : Nat} {reserved reserved' : List String}
    {args : List (Identifier Unit × LMonoTy)}
    (hargs : (args, reserved') ∈ SetGen.support (genConstrArgs (G := SetGen.Set)
            baseTypes tyCons blockRefs tyParams rca maxArgs maxSize reserved)) :
    ∀ arg ∈ args, ∃ size, arg.2 ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs tyParams rca size) := by
  simp only [genConstrArgs, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_vectorOf_iff] at hargs
  obtain ⟨_, _, fieldNames, _, argTys, ⟨_, hall⟩, hpair⟩ := hargs
  -- The `pure` gives both parts of the pair. This proof needs only the first part.
  have hargs_eq : args = (fieldNames.zip argTys).map
      (fun p => ((⟨p.1, ()⟩ : Identifier Unit), p.2)) := (Prod.mk.inj hpair).1
  subst hargs_eq
  intro arg harg
  obtain ⟨⟨nm, ty⟩, hmem, rfl⟩ := List.mem_map.mp harg
  obtain ⟨size, _, hty⟩ := by
    simpa only [mem_support_bind_iff] using hall ty (List.of_mem_zip hmem).2
  exact ⟨size, hty⟩

/-- Each argument type of each constructor from `genConstrs` is in the support of `genArgTy`
    at some size. The proof is an induction on the number of constructors, because
    `genConstrs` recurses on that number. `genConstrs` also threads the list of reserved
    names, but this statement does not name that list. -/
theorem genConstrs_mem_support {baseTypes : List String} {tyCons : List KnownTyCon}
    {blockRefs : List BlockRef} {tyParams : List TyIdentifier}
    {rca : Bool} {maxArgs maxSize : Nat} :
    ∀ (n : Nat) (reserved : List String) (cs : List (LConstr Unit))
      (reserved' : List String),
      (cs, reserved') ∈ SetGen.support (genConstrs (G := SetGen.Set) baseTypes tyCons
        blockRefs tyParams rca maxArgs maxSize n reserved) →
      ∀ c ∈ cs, ∀ arg ∈ c.args, ∃ size, arg.2 ∈ SetGen.support
        (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs tyParams rca size) := by
  intro n
  induction n with
  | zero =>
    intro reserved cs reserved' hcs
    simp only [genConstrs, mem_support_pure_iff] at hcs
    have : cs = [] := (Prod.mk.inj hcs).1
    subst this
    intro c hc; exact absurd hc (by simp)
  | succ n ih =>
    intro reserved cs reserved' hcs
    simp only [genConstrs, mem_support_bind_iff, mem_support_pure_iff] at hcs
    obtain ⟨cname, _, ⟨args, res₁⟩, hargs, ⟨rest, res₂⟩, hrest, hpair⟩ := hcs
    have hcs_eq : cs = { name := ⟨cname, ()⟩, args := args } :: rest :=
      (Prod.mk.inj hpair).1
    subst hcs_eq
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact genConstrArgs_mem_support hargs
    · exact ih res₁ rest res₂ hrest c hc

/-! ### The shape of the support of `genMutuallyRecursiveDatatypes`

`genMutuallyRecursiveDatatypes` builds the block in two phases. Phase 1 makes the headers,
and phase 2 makes the bodies. This section states the shape of its support one time, and
later proofs use that statement.

Each datatype `d` of a generated block obeys three facts. The generator drew its name fresh
against `initialReserved`, which is what `NamesOk` needs. It came from a header whose
parameters are `d.typeArgs`. Each of its constructor argument types comes from `genArgTy` at
the visible references for the parameters of `d`. That type comes from some value of the flag,
and from some size. -/

/-- Each name that `genFreshNames reserved n` makes is absent from `reserved`. The proof is
    an induction on `n`, and it uses `genFreshName_fresh` at each step. The generator draws
    the tail against a longer list of reserved names, and that longer list still holds each
    member of the first list. -/
theorem genFreshNames_fresh :
    ∀ (n : Nat) (reserved : List String) (names : List String),
      names ∈ SetGen.support (genFreshNames (G := SetGen.Set) reserved n) →
      ∀ nm ∈ names, nm ∉ reserved := by
  intro n
  induction n with
  | zero =>
    intro reserved names hnames
    simp only [genFreshNames, mem_support_pure_iff] at hnames
    subst hnames; intro nm hnm; exact absurd hnm (by simp)
  | succ n ih =>
    intro reserved names hnames
    simp only [genFreshNames, mem_support_bind_iff, mem_support_pure_iff] at hnames
    obtain ⟨s, hs, rest, hrest, rfl⟩ := hnames
    intro nm hnm
    rcases List.mem_cons.mp hnm with rfl | hnm
    · exact genFreshName_fresh reserved _ hs
    · -- Each name of the tail is absent from `s :: reserved`, therefore also from
      -- `reserved`.
      exact fun hmem => ih (s :: reserved) rest hrest nm hnm (by simp [hmem])

/-- `genFreshNames reserved n` always makes a list of `n` names. -/
theorem genFreshNames_length :
    ∀ (n : Nat) (reserved : List String) (names : List String),
      names ∈ SetGen.support (genFreshNames (G := SetGen.Set) reserved n) →
      names.length = n := by
  intro n
  induction n with
  | zero =>
    intro reserved names hnames
    simp only [genFreshNames, mem_support_pure_iff] at hnames
    subst hnames; rfl
  | succ n ih =>
    intro reserved names hnames
    simp only [genFreshNames, mem_support_bind_iff, mem_support_pure_iff] at hnames
    obtain ⟨s, hs, rest, hrest, rfl⟩ := hnames
    simp [ih (s :: reserved) rest hrest]

/-- `genParamsList reserved maxTyParams n` always makes a list of `n` parameter lists. -/
theorem genParamsList_length :
    ∀ (n : Nat) (reserved : List String) (maxTyParams : Nat)
      (paramsList : List (List TyIdentifier)),
      paramsList ∈ SetGen.support
        (genParamsList (G := SetGen.Set) reserved maxTyParams n) →
      paramsList.length = n := by
  intro n
  induction n with
  | zero =>
    intro reserved maxTyParams paramsList hpl
    simp only [genParamsList, mem_support_pure_iff] at hpl
    subst hpl; rfl
  | succ n ih =>
    intro reserved maxTyParams paramsList hpl
    simp only [genParamsList, mem_support_bind_iff, mem_support_pure_iff] at hpl
    obtain ⟨numTyParams, _, params, _, rest, hrest, rfl⟩ := hpl
    simp [ih reserved maxTyParams rest hrest]

/-- `genRanks` makes a list of exactly `n` ranks. -/
theorem genRanks_length :
    ∀ (maxRank n : Nat) (ranks : List Nat),
      ranks ∈ SetGen.support (genRanks (G := SetGen.Set) maxRank n) →
      ranks.length = n := by
  intro maxRank n
  induction n with
  | zero =>
    intro ranks hr
    simp only [genRanks, mem_support_pure_iff] at hr
    subst hr; rfl
  | succ n ih =>
    intro ranks hr
    simp only [genRanks, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨r, _, rest, hrest, rfl⟩ := hr
    simp [ih rest hrest]

/-- Build the headers from `names.zip paramsList`. Assume that `names` is not longer than
    `paramsList`. Then the names of those headers are exactly `names`, because a zip and then
    a projection of the first part through `TypeConstructor.name` gives `names` back. -/
theorem map_name_headers_of_length_le :
    ∀ (names : List String) (paramsList : List (List TyIdentifier)),
      names.length ≤ paramsList.length →
      (((names.zip paramsList).map
        (fun p => ({ name := p.1, params := p.2 } : TypeConstructor))).map (·.name)) = names := by
  intro names
  induction names with
  | nil => intro paramsList _; rfl
  | cons a as ih =>
    intro paramsList hlen
    match paramsList, hlen with
    | b :: bs, hlen =>
      simp only [List.zip_cons_cons, List.map_cons, ih bs (by simpa using hlen)]

/-- The names that `genFreshNames reserved n` makes are different in pairs. The generator
    adds each name to the list of reserved names before it draws the tail.
    `genFreshNames_fresh` then says that each name of the tail is absent from that list. -/
theorem genFreshNames_nodup :
    ∀ (n : Nat) (reserved : List String) (names : List String),
      names ∈ SetGen.support (genFreshNames (G := SetGen.Set) reserved n) →
      names.Nodup := by
  intro n
  induction n with
  | zero =>
    intro reserved names hnames
    simp only [genFreshNames, mem_support_pure_iff] at hnames
    subst hnames; exact List.nodup_nil
  | succ n ih =>
    intro reserved names hnames
    simp only [genFreshNames, mem_support_bind_iff, mem_support_pure_iff] at hnames
    obtain ⟨s, hs, rest, hrest, rfl⟩ := hnames
    refine List.nodup_cons.mpr ⟨?_, ih (s :: reserved) rest hrest⟩
    -- `s` is absent from the tail, because each name of the tail is absent from
    -- `s :: reserved`, and that list holds `s`.
    exact fun hmem => genFreshNames_fresh _ _ _ hrest s hmem (by simp)

/-- Membership in `visibleRefs headers params`. A block reference `br` is visible exactly
    when it comes from a header whose parameters are a subset of `params`. It then has the
    form of the uniform occurrence `(h.name, h.params.map .ftvar)`. -/
theorem visibleRefs_mem_iff (headers : List TypeConstructor) (params : List TyIdentifier)
    (br : BlockRef) :
    br ∈ visibleRefs headers params ↔
      ∃ h ∈ headers, h.params ⊆ params ∧ br = (h.name, h.params.map .ftvar) := by
  simp only [visibleRefs, List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, heq⟩
    by_cases hsub : h.params ⊆ params
    · rw [if_pos hsub] at heq
      exact ⟨h, hh, hsub, (Option.some.inj heq).symm⟩
    · rw [if_neg hsub] at heq; exact absurd heq (by simp)
  · rintro ⟨h, hh, hsub, rfl⟩
    exact ⟨h, hh, by rw [if_pos hsub]⟩

/-- `visibleRefs` grows with its list of headers. A reference that is visible against a part of
    the headers is also visible against all of them.

    This lemma discharges the premise `hsub` of `genConstructors_shape`. The set of names for the
    inhabited constructor is a subset of the full set `visibleRefs allHeaders`. -/
theorem visibleRefs_mono {headers headers' : List TypeConstructor} {params : List TyIdentifier}
    (hsub : ∀ h ∈ headers, h ∈ headers') :
    ∀ br ∈ visibleRefs headers params, br ∈ visibleRefs headers' params := by
  intro br hbr
  obtain ⟨h, hh, hpsub, rfl⟩ := (visibleRefs_mem_iff _ _ _).mp hbr
  exact (visibleRefs_mem_iff _ _ _).mpr ⟨h, hsub h hh, hpsub, rfl⟩

/-- Membership in `lowerRankHeaders rankedHeaders r`. A header `h` is a member exactly when a
    pair `(h, r')` is a member of `rankedHeaders` with `r' < r`. -/
theorem lowerRankHeaders_mem_iff (rankedHeaders : List (TypeConstructor × Nat)) (r : Nat)
    (h : TypeConstructor) :
    h ∈ lowerRankHeaders rankedHeaders r ↔ ∃ r', (h, r') ∈ rankedHeaders ∧ r' < r := by
  simp only [lowerRankHeaders, List.mem_filterMap]
  constructor
  · rintro ⟨⟨h', r'⟩, hmem, hif⟩
    by_cases hlt : r' < r
    · simp only [hlt, if_true, Option.some.injEq] at hif
      exact ⟨r', hif ▸ hmem, hlt⟩
    · simp [hlt] at hif
  · rintro ⟨r', hmem, hlt⟩
    exact ⟨(h, r'), hmem, by simp [hlt]⟩

/-- Each header in `lowerRankHeaders rankedHeaders r` is one of the headers of the pairs. This
    lemma discharges the premise `hsub` of `genConstructors_shape`, because the set of names
    for a lower rank is a subset of the full set `visibleRefs`. -/
theorem lowerRankHeaders_subset {rankedHeaders : List (TypeConstructor × Nat)}
    {allHeaders : List TypeConstructor}
    (hsub : ∀ hr ∈ rankedHeaders, hr.1 ∈ allHeaders) (r : Nat) :
    ∀ h ∈ lowerRankHeaders rankedHeaders r, h ∈ allHeaders := by
  intro h hh
  obtain ⟨r', hmem, _⟩ := (lowerRankHeaders_mem_iff _ _ _).mp hh
  exact hsub (h, r') hmem

/-- **The name of a datatype gives its rank in `headers.zip ranks`**, when the header names
    are different in pairs. Two pairs that share a header name hold the same rank.

    Therefore the argument for inhabitance with ranks can speak about "the rank of a block
    name". A block name gives one header with its rank, and therefore one rank.

    The proof is an induction on `headers`. `Nodup` says that the name of the head is absent
    from the tail. That fact excludes the case with one pair at the head and one pair in the
    tail. -/
theorem zip_rank_functional {headers : List TypeConstructor} :
    ∀ {ranks : List Nat}, (headers.map (·.name)).Nodup →
      ∀ {h r h' r'}, (h, r) ∈ headers.zip ranks → (h', r') ∈ headers.zip ranks →
        h.name = h'.name → r = r' := by
  induction headers with
  | nil => intro ranks _ h r h' r' hmem _ _; simp at hmem
  | cons hd tl ih =>
    intro ranks hnd h r h' r' hmem hmem' hname
    cases ranks with
    | nil => simp at hmem
    | cons rr rtl =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hdnotmem, hndtl⟩ := hnd
      rw [List.zip_cons_cons, List.mem_cons] at hmem hmem'
      -- The proof has four cases. Both pairs are at the head, or both pairs are in the
      -- tail, or one pair is at the head and one pair is in the tail. `Nodup` excludes the
      -- last two cases, because the name of the head is absent from the tail.
      rcases hmem with heq | hmemtl <;> rcases hmem' with heq' | hmemtl'
      · rw [Prod.mk.injEq] at heq heq'; omega
      · rw [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
        exact absurd (hname ▸ List.mem_map.mpr ⟨h', (List.of_mem_zip hmemtl').1, rfl⟩) hdnotmem
      · rw [Prod.mk.injEq] at heq'; obtain ⟨rfl, rfl⟩ := heq'
        exact absurd (hname.symm ▸ List.mem_map.mpr ⟨h, (List.of_mem_zip hmemtl).1, rfl⟩) hdnotmem
      · exact ih hndtl hmemtl hmemtl' hname

/-- Take a list of headers whose names are different in pairs. Two headers of that list that
    share a name are equal. `visibleRefs_blockRefsWF.uniform` needs this fact. -/
theorem header_unique_of_nodup {headers : List TypeConstructor} :
    ∀ {h h' : TypeConstructor}, (headers.map (·.name)).Nodup →
      h ∈ headers → h' ∈ headers → h.name = h'.name → h = h' := by
  induction headers with
  | nil => intro h h' _ hh _ _; exact absurd hh (by simp)
  | cons g tl ih =>
    intro h h' hnodup hh hh' heq
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hnodup'⟩ := hnodup
    rcases List.mem_cons.mp hh with hhg | hhtl
    · rcases List.mem_cons.mp hh' with hh'g | hh'tl
      · rw [hhg, hh'g]
      · -- Here `h = g`, and `h' ∈ tl` with `h'.name = g.name`. This case contradicts
        -- `g.name ∉ tl.map (·.name)`.
        exact absurd (List.mem_map.mpr ⟨h', hh'tl, by rw [← heq, hhg]⟩) hnotin
    · rcases List.mem_cons.mp hh' with hh'g | hh'tl
      · exact absurd (List.mem_map.mpr ⟨h, hhtl, by rw [heq, hh'g]⟩) hnotin
      · exact ih hnodup' hhtl hh'tl heq

/-- **`visibleRefs` gives a well-formed set of references.** This lemma has three
    hypotheses. The names of the block are the names of the headers, which is `hnames`. Those
    names are different in pairs, which is `hnodup`. The pair `(name, typeArgs)` of each block
    datatype is a header, which is `hheader`.

    Then the visible references for the parameters of a block datatype `d` obey
    `BlockRefsWF`. This lemma discharges the hypothesis `BlockRefsWF` of the soundness lemmas
    for one type, for the output of `genMutuallyRecursiveDatatypes`.

    * `mem`. The name of a visible reference is a header name, therefore it is a block name.
    * `uniform`. A reference to a block datatype `d'` comes from the one header with the name
      `d'.name`, because the names are different in pairs. `hheader` says that this header is
      `⟨d'.name, d'.typeArgs⟩`. Therefore the reference applies `d'.name` to exactly
      `d'.typeArgs`.
    * `ftvarArgs`. The arguments of a reference are `h.params.map .ftvar`, and each of them is
      a variable.
    * `argsScoped`. The variables of those arguments are `h.params`, and the filter in
      `visibleRefs` keeps `h.params ⊆ d.typeArgs`. -/
theorem visibleRefs_blockRefsWF {headers : List TypeConstructor} {block : MutualDatatype Unit}
    {d : LDatatype Unit}
    (hnames : block.map (·.name) = headers.map (·.name))
    (hnodup : (headers.map (·.name)).Nodup)
    (hheader : ∀ d ∈ block, ∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs)
    (_hd : d ∈ block) :
    BlockRefsWF block d.typeArgs (visibleRefs headers d.typeArgs) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- mem
    intro br hbr
    obtain ⟨h, hh, _, rfl⟩ := (visibleRefs_mem_iff _ _ _).mp hbr
    rw [hnames]
    exact List.mem_map.mpr ⟨h, hh, rfl⟩
  · -- uniform
    intro br hbr d' hd' hd'name
    obtain ⟨h, hh, _, rfl⟩ := (visibleRefs_mem_iff _ _ _).mp hbr
    -- Here `h.name = d'.name`. The header `h''` of `d'` also has `h''.name = d'.name`. The
    -- names are different in pairs, therefore `h = h''`, which gives
    -- `h.params = h''.params = d'.typeArgs`.
    obtain ⟨h'', hh''mem, hh''name, hh''params⟩ := hheader d' hd'
    -- Here `hd'name : d'.name = h.name`, because the `.fst` reduces. Also
    -- `hh''name : h''.name = d'.name`.
    have hhname : h.name = d'.name := hd'name.symm
    have hh1 : h.name = h''.name := hhname.trans hh''name.symm
    have hhe : h = h'' := header_unique_of_nodup hnodup hh hh''mem hh1
    -- The goal reduces to `h.params.map .ftvar = d'.typeArgs.map .ftvar`.
    show (h.params.map LMonoTy.ftvar) = d'.typeArgs.map LMonoTy.ftvar
    rw [hhe, hh''params]
  · -- ftvarArgs
    intro br hbr a ha
    obtain ⟨h, hh, _, rfl⟩ := (visibleRefs_mem_iff _ _ _).mp hbr
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    exact ⟨v, rfl⟩
  · -- argsScoped
    intro br hbr v hv
    obtain ⟨h, hh, hsub, rfl⟩ := (visibleRefs_mem_iff _ _ _).mp hbr
    rw [freeVars_map_ftvar] at hv
    exact hsub hv

/-- **A block name that appears in a strictly positive and uniform type is applied to its own
    `typeArgs`.** Assume that `d'.name` appears in a type `ty` that obeys `StrictPosUnif`.
    Then `d'.name` occurs uniformly in `ty` with the arguments `d'.typeArgs.map .ftvar`.

    The proof recurses through `StrictPosUnif`. At an arrow it goes into the codomain, and at
    a base position it reads `UniformOccur`. `visibleRefs_cover_of_appears` needs this fact
    about one position. -/
theorem uniformOccur_of_appears {block : MutualDatatype Unit} {d' : LDatatype Unit}
    (harrow : ∀ d ∈ block, d.name ≠ "arrow") (hd' : d' ∈ block) :
    ∀ {ty : LMonoTy}, StrictPosUnif block ty → TyNameAppears d'.name ty →
      UniformOccur d'.name (d'.typeArgs.map .ftvar) ty := by
  intro ty
  induction ty with
  | ftvar v => intro _ hap; cases hap
  | bitvec sz => intro _ hap; cases hap
  | tcons n1 args1 ih =>
    intro hsp hap
    -- Divide the structure that `StrictPosUnif` gives.
    cases hsp with
    | arrow t1 t2 habs hsp2 =>
      -- `d'.name` appears in `.arrow t1 t2`. Each block name is absent from the domain
      -- `t1`, therefore `d'.name` appears in the codomain `t2`. There `hsp2` gives
      -- uniformity.
      have hapt2 : TyNameAppears d'.name t2 := by
        rcases tyNameAppears_tcons_inv hap with heq | ⟨t, ht, hat⟩
        · exact absurd heq.symm (harrow d' hd')
        · rcases List.mem_cons.mp ht with rfl | ht2
          · exact absurd hat (habs d' hd')
          · rcases List.mem_cons.mp ht2 with rfl | hbad
            · exact hat
            · exact absurd hbad (by simp)
      have huni2 : UniformOccur d'.name (d'.typeArgs.map .ftvar) t2 := ih t2 (by simp) hsp2 hapt2
      -- Build uniformity for the arrow. `d'.name` is absent from `t1`, and it is uniform
      -- in `t2`.
      refine .other "arrow" [t1, t2] (fun he => harrow d' hd' he.symm) ?_
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht2'
      · exact absent_uniform (habs d' hd')
      · rcases List.mem_cons.mp ht2' with rfl | hb
        · exact huni2
        · exact absurd hb (by simp)
    | base ty' _ huni => exact huni d' hd'

/-- **`visibleRefs` holds each block datatype that appears in a well-formed constructor
    argument whose variables are in scope.** Take a block datatype `d'` whose name occurs in
    a type `ty`, which `TyNameAppears` gives. Assume that `ty` is `ConstrArgWF block`, and
    that each free variable of `ty` is a member of `tyParams`. Assume also that the header of
    `d'` is a member of `headers`. Then the uniform reference
    `(d'.name, d'.typeArgs.map .ftvar)` is a member of `visibleRefs headers tyParams`.

    The occurrence is uniform, which `uniformOccur_of_appears` gives. Therefore its arguments
    are `d'.typeArgs.map .ftvar`. The variables of those arguments are free variables of `ty`,
    which `uniformOccur_args_freeVars` gives. Therefore they are members of `tyParams`, by the
    hypothesis about scope. That condition is exactly the filter in `visibleRefs`. -/
theorem visibleRefs_cover_of_appears {headers : List TypeConstructor} {block : MutualDatatype Unit}
    {d' : LDatatype Unit} {ty : LMonoTy} {tyParams : List TyIdentifier}
    (harrow : ∀ d ∈ block, d.name ≠ "arrow")
    (hd' : d' ∈ block) (hd'header : ∃ h ∈ headers, h.name = d'.name ∧ h.params = d'.typeArgs)
    (hwf : ConstrArgWF block ty)
    (hscoped : ∀ v ∈ LMonoTy.freeVars ty, v ∈ tyParams)
    (happ : TyNameAppears d'.name ty) :
    (d'.name, d'.typeArgs.map .ftvar) ∈ visibleRefs headers tyParams := by
  obtain ⟨h, hhmem, hhname, hhparams⟩ := hd'header
  have huni : UniformOccur d'.name (d'.typeArgs.map .ftvar) ty :=
    uniformOccur_of_appears harrow hd' hwf.2 happ
  have hsubparams : d'.typeArgs ⊆ tyParams := by
    intro v hv
    have hvfv : v ∈ LMonoTys.freeVars (d'.typeArgs.map .ftvar) := by
      rw [freeVars_map_ftvar]; exact hv
    exact hscoped v (uniformOccur_args_freeVars huni happ v hvfv)
  refine (visibleRefs_mem_iff _ _ _).mpr ⟨h, hhmem, ?_, ?_⟩
  · rw [hhparams]; exact hsubparams
  · rw [hhname, hhparams]

/-- **The shape of the support of one datatype body.** Take a datatype `d` from
    `genConstructors … allHeaders inhabRefs nm params …`. Then `d.name = nm` and
    `d.typeArgs = params`. Each of its constructor argument types comes from `genArgTy` at
    the visible references `visibleRefs allHeaders params`. It also has an inhabited
    constructor at the head, and the generator drew the argument types of that constructor
    from the smaller set `inhabRefs`.

    This lemma states the argument types of the inhabited constructor over `inhabRefs`, and
    not over the full set `visibleRefs`. The proof of inhabitance needs that smaller set. The
    general fact for each constructor puts those types in the full set through
    `genArgTy_blockRefs_mono`, with the hypothesis `hsub`, which is
    `inhabRefs ⊆ visibleRefs allHeaders params`. Therefore soundness reads one set only.

    `genConstructors` puts its constructors into a random order. Therefore `d.constrs` is a
    permutation of the ordered list that has the inhabited constructor first. Both facts here
    speak about membership, through `∀ c ∈` and `∃ c₀ ∈`. Therefore they hold after that
    permutation, by `List.Perm.mem_iff`. -/
theorem genConstructors_shape {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List TypeConstructor} {inhabRefs : List BlockRef}
    {nm : String} {params : List TyIdentifier}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String}
    {d : LDatatype Unit}
    (hsub : ∀ br ∈ inhabRefs, br ∈ visibleRefs allHeaders params)
    (hd : d ∈ SetGen.support (genConstructors (G := SetGen.Set) baseTypes tyCons allHeaders
            inhabRefs nm params maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved)) :
    d.name = nm ∧ d.typeArgs = params ∧
    (∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∃ rca size, arg.2 ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons (visibleRefs allHeaders params)
        params rca size)) ∧
    (∃ c₀ ∈ d.constrs, ∀ arg ∈ c₀.args, ∃ size, arg.2 ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons inhabRefs params true size)) := by
  simp only [genConstructors, mem_support_bind_iff, mem_support_pure_iff] at hd
  obtain ⟨cname₀, _, ⟨args₀, res₀⟩, hargs₀, numExtraBase, _, ⟨baseConstrs, res₁⟩,
          hbase, numRec, _, ⟨recConstrs, res₂⟩, hrec, p, _, hdeq⟩ := hd
  subst hdeq
  -- `d.constrs = p.1`, and it is a permutation of the ordered list that has the inhabited
  -- constructor first.
  have hperm : ({ name := ⟨cname₀, ()⟩, args := args₀ } :: (baseConstrs ++ recConstrs)).Perm p.1 :=
    p.2
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro c hc arg harg
    -- Here `c ∈ d.constrs = p.1`, therefore `c` is a member of the ordered list.
    rcases List.mem_cons.mp (hperm.mem_iff.mpr hc) with rfl | hc'
    · -- The inhabited constructor. The generator drew its arguments from `inhabRefs`, and
      -- this proof puts them in the full set.
      obtain ⟨size, hsize⟩ := genConstrArgs_mem_support hargs₀ arg harg
      exact ⟨true, size, genArgTy_blockRefs_mono hsub _ hsize⟩
    · rcases List.mem_append.mp hc' with hc' | hc'
      · obtain ⟨size, hsize⟩ := genConstrs_mem_support _ _ _ _ hbase c hc' arg harg
        exact ⟨false, size, hsize⟩
      · obtain ⟨size, hsize⟩ := genConstrs_mem_support _ _ _ _ hrec c hc' arg harg
        exact ⟨true, size, hsize⟩
  · -- The inhabited constructor is the head of the ordered list. Therefore it is a member
    -- of `d.constrs`, through `hperm`.
    refine ⟨{ name := ⟨cname₀, ()⟩, args := args₀ }, hperm.mem_iff.mp List.mem_cons_self, ?_⟩
    intro arg harg
    exact genConstrArgs_mem_support hargs₀ arg harg

/-- **The names of the block are exactly the names of its headers, in the same order.**
    `genConstructorsForAllTypes` maps each header to a body that holds the name of that
    header, which `genConstructors_shape` gives. Therefore the list of names of the generated
    block is the list of names of the headers. The proof is an induction on the headers. -/
theorem genConstructorsForAllTypes_names {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List TypeConstructor} {rankedHeaders : List (TypeConstructor × Nat)}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String}
    (hrhsub : ∀ hr ∈ rankedHeaders, hr.1 ∈ allHeaders) :
    ∀ (todo : List (TypeConstructor × Nat)) (block : MutualDatatype Unit),
      (∀ hr ∈ todo, hr.1 ∈ allHeaders) →
      block ∈ SetGen.support (genConstructorsForAllTypes (G := SetGen.Set) baseTypes tyCons allHeaders
        rankedHeaders maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved todo) →
      block.map (·.name) = todo.map (·.1.name) := by
  intro todo
  induction todo with
  | nil =>
    intro block _ hblock
    simp only [genConstructorsForAllTypes, mem_support_pure_iff] at hblock
    subst hblock; rfl
  | cons hr tl ih =>
    intro block htodosub hblock
    simp only [genConstructorsForAllTypes, mem_support_bind_iff, mem_support_pure_iff] at hblock
    obtain ⟨d0, hd0, ds, hds, rfl⟩ := hblock
    -- The set of names for a lower rank is a subset of `visibleRefs allHeaders`.
    have hsub : ∀ br ∈ visibleRefs (lowerRankHeaders rankedHeaders hr.2) hr.1.params,
        br ∈ visibleRefs allHeaders hr.1.params :=
      visibleRefs_mono (lowerRankHeaders_subset hrhsub hr.2)
    obtain ⟨hname, _, _, _⟩ := genConstructors_shape hsub hd0
    have htodo' : ∀ h ∈ tl, h.1 ∈ allHeaders := fun h hh => htodosub h (List.mem_cons_of_mem _ hh)
    simp only [List.map_cons, hname, ih ds htodo' hds]

/-- **The shape of the support of the block bodies.** Take a block from
    `genConstructorsForAllTypes … allHeaders … todo`. Each datatype `d` of that block came
    from a header of the list, therefore
    `∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs`. Each datatype also obeys the
    shape for one body, because each of its constructor argument types comes from `genArgTy`
    at `visibleRefs allHeaders d.typeArgs`. The proof is an induction on the headers. -/
theorem genConstructorsForAllTypes_shape {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List TypeConstructor} {rankedHeaders : List (TypeConstructor × Nat)}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String}
    (hrhsub : ∀ hr ∈ rankedHeaders, hr.1 ∈ allHeaders) :
    ∀ (todo : List (TypeConstructor × Nat)) (block : MutualDatatype Unit),
      (∀ hr ∈ todo, hr.1 ∈ allHeaders) →
      block ∈ SetGen.support (genConstructorsForAllTypes (G := SetGen.Set) baseTypes tyCons allHeaders
        rankedHeaders maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved todo) →
      ∀ d ∈ block, (∃ hr ∈ todo, hr.1.name = d.name ∧ hr.1.params = d.typeArgs) ∧
        (∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∃ rca size, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons (visibleRefs allHeaders d.typeArgs)
            d.typeArgs rca size)) := by
  intro todo
  induction todo with
  | nil =>
    intro block _ hblock
    simp only [genConstructorsForAllTypes, mem_support_pure_iff] at hblock
    subst hblock; intro d hd; exact absurd hd (by simp)
  | cons hr tl ih =>
    intro block htodosub hblock
    simp only [genConstructorsForAllTypes, mem_support_bind_iff, mem_support_pure_iff] at hblock
    obtain ⟨d0, hd0, ds, hds, rfl⟩ := hblock
    have hsub : ∀ br ∈ visibleRefs (lowerRankHeaders rankedHeaders hr.2) hr.1.params,
        br ∈ visibleRefs allHeaders hr.1.params :=
      visibleRefs_mono (lowerRankHeaders_subset hrhsub hr.2)
    have htodo' : ∀ h ∈ tl, h.1 ∈ allHeaders := fun h hh => htodosub h (List.mem_cons_of_mem _ hh)
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨hname, hargs, hconstrs, _⟩ := genConstructors_shape hsub hd0
      exact ⟨⟨hr, List.mem_cons_self, hname.symm, hargs.symm⟩, by rw [hargs]; exact hconstrs⟩
    · obtain ⟨⟨h, hhmem, hh1, hh2⟩, hconstrs⟩ := ih ds htodo' hds d hd
      exact ⟨⟨h, List.mem_cons_of_mem _ hhmem, hh1, hh2⟩, hconstrs⟩

/-- **The inhabited constructor of each block body.** Take a block from the map. Each datatype
    `d` of that block comes from a header with its rank, which is `(h, r) ∈ todo`. Therefore
    `h.name = d.name` and `h.params = d.typeArgs`.

    Each datatype also has an inhabited constructor `c₀ ∈ d.constrs`. The generator drew each
    argument type of `c₀` from `visibleRefs (lowerRankHeaders rankedHeaders r) d.typeArgs`. That
    set holds the block datatypes of a rank less than the rank `r` of `d`.

    The old design used the datatypes before `d` in a fixed order for that set of names. This
    lemma is the form with ranks, and the argument for inhabitance with ranks needs it. The
    proof is an induction on `todo`. -/
theorem genConstructorsForAllTypes_witness {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List TypeConstructor} {rankedHeaders : List (TypeConstructor × Nat)}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String}
    (hrhsub : ∀ hr ∈ rankedHeaders, hr.1 ∈ allHeaders) :
    ∀ (todo : List (TypeConstructor × Nat)) (block : MutualDatatype Unit),
      (∀ hr ∈ todo, hr.1 ∈ allHeaders) →
      block ∈ SetGen.support (genConstructorsForAllTypes (G := SetGen.Set) baseTypes tyCons allHeaders
        rankedHeaders maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved todo) →
      ∀ d ∈ block, ∃ hr ∈ todo, hr.1.name = d.name ∧ hr.1.params = d.typeArgs ∧
        ∃ c₀ ∈ d.constrs, ∀ arg ∈ c₀.args, ∃ size, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons
            (visibleRefs (lowerRankHeaders rankedHeaders hr.2) hr.1.params) hr.1.params true size) := by
  intro todo
  induction todo with
  | nil =>
    intro block _ hblock
    simp only [genConstructorsForAllTypes, mem_support_pure_iff] at hblock
    subst hblock; intro d hd; exact absurd hd (by simp)
  | cons hr tl ih =>
    intro block htodosub hblock
    simp only [genConstructorsForAllTypes, mem_support_bind_iff, mem_support_pure_iff] at hblock
    obtain ⟨d0, hd0, ds, hds, rfl⟩ := hblock
    have hsub : ∀ br ∈ visibleRefs (lowerRankHeaders rankedHeaders hr.2) hr.1.params,
        br ∈ visibleRefs allHeaders hr.1.params :=
      visibleRefs_mono (lowerRankHeaders_subset hrhsub hr.2)
    have htodo' : ∀ h ∈ tl, h.1 ∈ allHeaders := fun h hh => htodosub h (List.mem_cons_of_mem _ hh)
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨hname, hargs, _, ⟨c₀, hc₀, hwit⟩⟩ := genConstructors_shape hsub hd0
      -- `hwit` is already over `visibleRefs (lowerRankHeaders … hr.2) hr.1.params`.
      exact ⟨hr, List.mem_cons_self, hname.symm, hargs.symm, c₀, hc₀, hwit⟩
    · obtain ⟨hr', hhr', hh1, hh2, hwit⟩ := ih ds htodo' hds d hd
      exact ⟨hr', List.mem_cons_of_mem _ hhr', hh1, hh2, hwit⟩

/-- **The shape of the support of `genMutuallyRecursiveDatatypes`.** A generated block obeys
    four facts. Its datatype names are fresh and different in pairs, therefore each name is
    absent from `initialReserved`. The parameters of each datatype are the parameters of its
    header. The names of the block are exactly the names of the headers. Each constructor
    argument type comes from `genArgTy` at the visible references for the parameters of that
    datatype.

    This lemma says nothing about inhabitance. `genMutuallyRecursiveDatatypes_inhabited` gives
    that field, through the argument with ranks. -/
theorem genMutuallyRecursiveDatatypes_shape {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∃ headers : List TypeConstructor,
      block ≠ [] ∧
      block.map (·.name) = headers.map (·.name) ∧
      (headers.map (·.name)).Nodup ∧
      (∀ h ∈ headers, h.name ∉ initialReserved baseTypes tyCons extraReserved) ∧
      (∀ d ∈ block, ∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs) ∧
      (∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∃ rca size, arg.2 ∈ SetGen.support
        (genArgTy (G := SetGen.Set) baseTypes tyCons (visibleRefs headers d.typeArgs)
          d.typeArgs rca size)) := by
  simp only [genMutuallyRecursiveDatatypes, mem_support_bind_iff] at hb
  obtain ⟨numExtra, _, names, hnames, paramsList, hparams, ranks, hranksmem, hbodies⟩ := hb
  -- The header names are exactly `names` (the zipped-then-mapped first projection),
  -- which is nodup.
  let headers : List TypeConstructor :=
    (names.zip paramsList).map (fun p => { name := p.1, params := p.2 })
  let rankedHeaders : List (TypeConstructor × Nat) := headers.zip ranks
  have hnameslen : names.length = numExtra + 1 := genFreshNames_length _ _ _ hnames
  have hparamslen : paramsList.length = names.length := by
    rw [genParamsList_length _ _ _ _ hparams, hnameslen]
  have hheadernames : headers.map (·.name) = names :=
    map_name_headers_of_length_le names paramsList (by omega)
  -- The paired headers all come from `headers` (the first projection of the zip).
  have hrhsub : ∀ hr ∈ rankedHeaders, hr.1 ∈ headers := by
    intro hr hhr
    obtain ⟨h, r⟩ := hr
    exact (List.of_mem_zip hhr).1
  have hbnames := genConstructorsForAllTypes_names hrhsub rankedHeaders block hrhsub hbodies
  have hbshape := genConstructorsForAllTypes_shape hrhsub rankedHeaders block hrhsub hbodies
  -- The names of the block are the names of the headers of the pairs. A zip cuts its
  -- result to the shorter length. But the first parts of `rankedHeaders` are exactly
  -- `headers` when `ranks.length = headers.length`, and that holds because both lists have
  -- the length of `names`.
  have hrankslen : ranks.length = names.length := by
    rw [genRanks_length _ _ _ hranksmem, hnameslen]
  have hheaderslen : headers.length = names.length := by
    simp only [headers, List.length_map, List.length_zip, hparamslen]; omega
  have hrhfst : rankedHeaders.map (·.1) = headers := by
    show (headers.zip ranks).map (·.1) = headers
    exact List.map_fst_zip (Nat.le_of_eq (by rw [hheaderslen, hrankslen]))
  -- The names of the block are the names of the headers of the pairs, which are the names
  -- of the headers, which are `names`.
  have hblocknames : block.map (·.name) = names := by
    rw [hbnames]
    have : rankedHeaders.map (fun hr => hr.1.name) = headers.map (·.name) := by
      rw [← hrhfst, List.map_map]; rfl
    rw [this, hheadernames]
  refine ⟨headers, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The block is not empty. Its names are `names`, and that list holds `numExtra + 1`
    -- names, which is more than 0.
    intro hblnil
    rw [hblnil, List.map_nil] at hblocknames
    have : names.length = 0 := by rw [← hblocknames]; rfl
    omega
  · -- The names of the block are the names of the headers.
    rw [hblocknames, hheadernames]
  · -- The header names are different in pairs, because they are `names`, and
    -- `genFreshNames` drew that list.
    rw [hheadernames]; exact genFreshNames_nodup _ _ _ hnames
  · intro h hh
    -- Each header name is a member of `names`, and the generator drew each of those names
    -- fresh against `initialReserved`.
    have : h.name ∈ names := by rw [← hheadernames]; exact List.mem_map.mpr ⟨h, hh, rfl⟩
    exact genFreshNames_fresh _ _ _ hnames h.name this
  · intro d hd
    obtain ⟨⟨hr, hhr, h1, h2⟩, _⟩ := hbshape d hd
    exact ⟨hr.1, hrhsub hr hhr, h1, h2⟩
  · intro d hd c hc arg harg; exact (hbshape d hd).2 c hc arg harg

/-- **The main theorem for soundness, which gives `argsWF`.** Each constructor argument type
    of a block from `genMutuallyRecursiveDatatypes` is well-formed for that block. This
    statement is exactly the field `argsWF` of `Core.TypeSpec.MutualADTWF`.

    The one hypothesis is about the pool `tyCons` that the caller gives. The rule for the
    reserved names gives the conditions about the names of the block, through
    `namesOk_of_fresh`. `visibleRefs_blockRefsWF` gives the facts about a recursive
    occurrence. -/
theorem genMutuallyRecursiveDatatypes_argsWF {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (harrow : ∀ kc ∈ tyCons, kc.1 ≠ "arrow")
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ConstrArgWF block arg.2 := by
  obtain ⟨headers, _, hnames, hnodup, hfresh, hheader, hconstrs⟩ := genMutuallyRecursiveDatatypes_shape hb
  have hn : NamesOk baseTypes tyCons (block.map (·.name)) := by
    refine namesOk_of_fresh (extraReserved := extraReserved) harrow ?_
    rw [hnames]; intro n hn; obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn; exact hfresh h hh
  intro d hd c hc arg harg
  have hbr := visibleRefs_blockRefsWF hnames hnodup hheader hd
  obtain ⟨_, _, hty⟩ := hconstrs d hd c hc arg harg
  exact genArgTy_constrArgWF hn hbr hty

/-- **`argsWF` for the default parameters, with no side condition.** -/
theorem genMutuallyRecursiveDatatypes_argsWF_default
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) defaultBaseTypes
            defaultTyCons maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs
            maxArgs maxSize)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ConstrArgWF block arg.2 :=
  genMutuallyRecursiveDatatypes_argsWF defaultTyCons_ne_arrow hb

/-! ### `refsKnown`, which says that each referenced name is known

This field is the other field of `MutualADTWF` in this section. `getTypeRefs` collects each
type constructor name that occurs in a type. This section shows that each such name is a
`baseTypes` name, a `tyCons` name, the name of a block datatype, or the reserved name
`"arrow"`. -/

/-- Each type reference in a generated type is a `baseTypes` name, a `tyCons` name, a block
    name, or `"arrow"`. This lemma is the half of the field `refsKnown` of `MutualADTWF` that
    speaks about the generator. It holds against each ambient context whose known types and
    datatypes hold all of `baseTypes` and `tyCons`. Such a context also knows `"arrow"`,
    because Strata Core always knows that name.

    The head of a recursive occurrence is a block name, which `BlockRefsWF.mem` gives. Its
    arguments are type variables, which `BlockRefsWF.ftvarArgs` gives. Therefore the
    occurrence adds only its head name.

    The proof is a strong induction on `size` through `genArgTy_mem_iff` and
    `genLeafTy_mem_iff`. It adds no helper relation. -/
theorem genArgTy_refs {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hbr : BlockRefsWF block tyParams blockRefs) :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) →
      ∀ r ∈ getTypeRefs ty,
        r ∈ baseTypes ∨ r ∈ tyCons.map (·.1) ∨ r ∈ block.map (·.name) ∨ r = "arrow" := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro rca ty h
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨w, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨v, _, rfl⟩ | ⟨_, br, hbrmem, rfl⟩
      · intro r hr; simp [getTypeRefs] at hr
      · intro r hr
        simp only [getTypeRefs, List.flatMap_nil, List.mem_singleton] at hr
        subst hr; exact Or.inl hb
      · intro r hr; simp [getTypeRefs] at hr
      · intro r hr
        -- The head is a block name. The arguments are type variables, and they add no
        -- reference.
        simp only [getTypeRefs, List.mem_cons, List.mem_flatMap] at hr
        rcases hr with rfl | ⟨a, ha, hr⟩
        · exact Or.inr (Or.inr (Or.inl (hbr.mem br hbrmem)))
        · obtain ⟨v, rfl⟩ := hbr.ftvarArgs br hbrmem a ha
          simp [getTypeRefs] at hr
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      intro r hr
      rw [LMonoTy.arrow] at hr
      simp only [getTypeRefs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                 List.mem_cons, List.mem_append] at hr
      rcases hr with rfl | hr | hr
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact ih _ hhalf h1 r hr
      · exact ih _ hhalf h2 r hr
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega)
      intro r hr
      simp only [getTypeRefs, List.mem_cons, List.mem_flatMap] at hr
      rcases hr with rfl | ⟨a, ha, hr⟩
      · exact Or.inr (Or.inl (List.mem_map.mpr ⟨_, hkc, rfl⟩))
      · exact ih _ hhalf (hall a ha) r hr

/-! ### `argsWellKinded`, which says that each application has the declared arity

`getTypeConsArities` pairs each type constructor reference with the number of arguments at
that occurrence. This section shows that each such pair is one of four things: a
`baseTypes` name at arity 0, a `tyCons` entry with its own arity, a block datatype with its
own number of `typeArgs`, or `"arrow"` at arity 2.

Upstream added the field `argsWellKinded` to `MutualADTWF` (`strata-org/Strata` PR
"Reject known type constructors applied at wrong arity"). That field closes exactly the
specification gap this file used to document, and which a hand-written `ArityOk` predicate
had to state for the completeness direction. `ArityOk` is now deleted: read the prose above
`ArgsWellKinded`, and `docs/mutualadtwf-arity-gap.md`. -/

/-- Each type-constructor occurrence in a generated type is applied at the arity that its
    name declares. This lemma is the half of the field `argsWellKinded` of `MutualADTWF`
    that speaks about the generator: it is the arity-aware refinement of `genArgTy_refs`,
    and its proof has the same shape.

    Each branch of the generator is arity-correct by construction. A base type is
    `.tcons b []`, therefore its arity is 0. An application draws `(k, arity)` from
    `tyCons` and then `vectorOf arity` arguments, therefore its arity is `arity`. An arrow
    is `.tcons "arrow" [t1, t2]`, therefore its arity is 2. A recursive occurrence applies a
    block name to exactly its own `typeArgs`, which `BlockRefsWF.uniform` gives. -/
theorem genArgTy_arities {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hbr : BlockRefsWF block tyParams blockRefs) :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) →
      ∀ ref n, (ref, n) ∈ getTypeConsArities ty →
        (ref ∈ baseTypes ∧ n = 0) ∨ (ref, n) ∈ tyCons ∨
        (∃ d ∈ block, d.name = ref ∧ d.typeArgs.length = n) ∨ (ref = "arrow" ∧ n = 2) := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro rca ty h
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨w, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨v, _, rfl⟩ | ⟨_, br, hbrmem, rfl⟩
      · intro ref n hn; simp [getTypeConsArities] at hn
      · intro ref n hn
        -- A base type is nullary: `getTypeConsArities (.tcons b []) = [(b, 0)]`.
        simp only [getTypeConsArities, List.flatMap_nil, List.length_nil,
          List.mem_singleton, Prod.mk.injEq] at hn
        exact Or.inl ⟨hn.1 ▸ hb, hn.2⟩
      · intro ref n hn; simp [getTypeConsArities] at hn
      · intro ref n hn
        -- The head is a block name applied to its own `typeArgs`. The arguments are type
        -- variables, therefore they add no occurrence of their own.
        simp only [getTypeConsArities, List.mem_cons, List.mem_flatMap, Prod.mk.injEq] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨a, ha, hn⟩
        · obtain ⟨d, hd, hdname⟩ := List.mem_map.mp (hbr.mem br hbrmem)
          refine Or.inr (Or.inr (Or.inl ⟨d, hd, hdname, ?_⟩))
          rw [hbr.uniform br hbrmem d hd hdname, List.length_map]
        · obtain ⟨v, rfl⟩ := hbr.ftvarArgs br hbrmem a ha
          simp [getTypeConsArities] at hn
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      intro ref n hn
      rw [LMonoTy.arrow] at hn
      simp only [getTypeConsArities, List.length_cons, List.length_nil, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append,
        Prod.mk.injEq] at hn
      rcases hn with ⟨rfl, rfl⟩ | hn | hn
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact ih _ hhalf h1 ref n hn
      · exact ih _ hhalf h2 ref n hn
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega)
      intro ref n hn
      simp only [getTypeConsArities, List.mem_cons, List.mem_flatMap, Prod.mk.injEq] at hn
      rcases hn with ⟨rfl, rfl⟩ | ⟨a, ha, hn⟩
      · exact Or.inr (Or.inl hkc)
      · exact ih _ hhalf (hall a ha) ref n hn

/-! ### `argVarsScoped`, which says that a constructor argument adds no type variable

This field of `MutualADTWF` says that each free type variable of a constructor argument type
is a declared member of `typeArgs` of the datatype. On the side of the generator, the rigid
type variable is the one source of such a variable, and the generator draws it from
`tyParams`. A recursive occurrence adds only the argument variables of the datatype that it
names, and `BlockRefsWF.argsScoped` keeps those variables in `tyParams`. -/

/-- Each free type variable of a type in the support of `genArgTy` is a member of `tyParams`.
    This lemma has the same structure as `genArgTy_refs`, but it follows `LMonoTy.freeVars`
    and not `getTypeRefs`. The proof is a strong induction on `size` through the one-step
    description of the support. `BlockRefsWF.argsScoped` keeps the variables of a recursive
    occurrence in scope. -/
theorem genArgTy_freeVars {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hbr : BlockRefsWF block tyParams blockRefs) :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) →
      ∀ v ∈ LMonoTy.freeVars ty, v ∈ tyParams := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro rca ty h
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨w, rfl⟩ | ⟨b, _, rfl⟩ | ⟨v', hv', rfl⟩ | ⟨_, br, hbrmem, rfl⟩
      · intro v hv; simp [LMonoTy.freeVars] at hv
      · intro v hv; simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv
      · intro v hv; simp only [LMonoTy.freeVars, List.mem_singleton] at hv
        subst hv; exact hv'
      · intro v hv
        simp only [LMonoTy.freeVars] at hv
        exact hbr.argsScoped br hbrmem v hv
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      intro v hv
      rw [LMonoTy.arrow] at hv
      simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ih _ hhalf h1 v hv
      · exact ih _ hhalf h2 v hv
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega)
      intro v hv
      rw [freeVars_tcons_eq_flatMap] at hv
      obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hv
      exact ih _ hhalf (hall a ha) v hv

/-- **`refsKnown`.** Take a constructor argument of a generated block. Each type constructor name
    that it refers to is a `baseTypes` name, a `tyCons` name, a block name, or `"arrow"`.

    This theorem takes `genArgTy_refs` from one type to the full block. It uses
    `genMutuallyRecursiveDatatypes_shape`, which says that each argument comes from `genArgTy`
    at the visible references. It also uses `visibleRefs_blockRefsWF`. -/
theorem genMutuallyRecursiveDatatypes_refsKnown {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ r ∈ getTypeRefs arg.2,
      r ∈ baseTypes ∨ r ∈ tyCons.map (·.1) ∨ r ∈ block.map (·.name) ∨ r = "arrow" := by
  obtain ⟨headers, _, hnames, hnodup, _, hheader, hconstrs⟩ := genMutuallyRecursiveDatatypes_shape hb
  intro d hd c hc arg harg r hr
  have hbr := visibleRefs_blockRefsWF hnames hnodup hheader hd
  obtain ⟨_, size, hty⟩ := hconstrs d hd c hc arg harg
  exact genArgTy_refs hbr size hty r hr

/-- **`argsWellKinded`.** Take a constructor argument of a generated block. Each type
    constructor occurrence in it is applied at the arity that its name declares: a
    `baseTypes` name at 0, a `tyCons` entry at its own arity, a block datatype at its own
    number of `typeArgs`, or `"arrow"` at 2. This theorem takes `genArgTy_arities` to the
    full block, exactly as `genMutuallyRecursiveDatatypes_refsKnown` takes
    `genArgTy_refs`. -/
theorem genMutuallyRecursiveDatatypes_arities {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ ref n, (ref, n) ∈ getTypeConsArities arg.2 →
      (ref ∈ baseTypes ∧ n = 0) ∨ (ref, n) ∈ tyCons ∨
      (∃ d' ∈ block, d'.name = ref ∧ d'.typeArgs.length = n) ∨ (ref = "arrow" ∧ n = 2) := by
  obtain ⟨headers, _, hnames, hnodup, _, hheader, hconstrs⟩ := genMutuallyRecursiveDatatypes_shape hb
  intro d hd c hc arg harg ref n hn
  have hbr := visibleRefs_blockRefsWF hnames hnodup hheader hd
  obtain ⟨_, size, hty⟩ := hconstrs d hd c hc arg harg
  exact genArgTy_arities hbr size hty ref n hn

/-- **`argVarsScoped`.** Each free type variable of a constructor argument type of a generated
    block is a declared member of `typeArgs` of the datatype around it. This theorem takes
    `genArgTy_freeVars` to the full block, in the way that
    `genMutuallyRecursiveDatatypes_refsKnown` takes `genArgTy_refs` to the full block. -/
theorem genMutuallyRecursiveDatatypes_argVarsScoped {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ v ∈ LMonoTy.freeVars arg.2,
      v ∈ d.typeArgs := by
  obtain ⟨headers, _, hnames, hnodup, _, hheader, hconstrs⟩ := genMutuallyRecursiveDatatypes_shape hb
  intro d hd c hc arg harg v hv
  have hbr := visibleRefs_blockRefsWF hnames hnodup hheader hd
  obtain ⟨_, size, hty⟩ := hconstrs d hd c hc arg harg
  exact genArgTy_freeVars hbr size hty v hv

/-! ### The full structure `Core.TypeSpec.MutualADTWF`

`argsWF` and `refsKnown` are the two difficult fields. The other fields are simpler. Two of
them are about fresh names, which are `namesFresh` and `namesNew`. Two of them say that the
block is not empty and that its names are different in pairs, which are `nonempty` and
`namesNodup`. The last one is about inhabitance, which is `inhabited`.

Each field speaks about an ambient `LContext CoreLParams`. Therefore this section first
states what that context must obey, so that a new generated block is well-formed in it. -/

open Core Core.TypeSpec in
/-- What the ambient context `C` must give, so that the output of
    `genMutuallyRecursiveDatatypes` is `MutualADTWF C block`. These conditions are the
    assumptions that the generator cannot control, because they are about the context and not
    about the block that it builds:

    * `refsKnown` needs each name that the generator can refer to to resolve in `C`.
    * `namesFresh` and `namesNew` need the existing type names and datatype names of `C` to be
      members of `initialReserved`. Therefore a name that the generator draws fresh against
      that list is not one of them.
    * `inhabited` needs each head symbol that the generator can refer to to be external in
      `C`, which means that it is not itself a datatype. Therefore an argument type that holds
      no block name is inhabited.

    `defaultContextOk` gives one concrete `C` that obeys all of these conditions. That result
    gives the corollary `genMutuallyRecursiveDatatypes_MutualADTWF_default`, which has no side
    condition. -/
structure ContextOk (C : LContext CoreLParams) (baseTypes : List String)
    (tyCons : List KnownTyCon) (extraReserved : List String) : Prop where
  /-- Each base type resolves as a known type of `C`, or as an existing datatype of `C`. -/
  base_known : ∀ b ∈ baseTypes,
    b ∈ C.knownTypes.keywords ∨ b ∈ C.datatypes.allTypeNames
  /-- Each applied type constructor resolves as a known type of `C`, or as a datatype of
      `C`. -/
  tyCon_known : ∀ kc ∈ tyCons,
    kc.1 ∈ C.knownTypes.keywords ∨ kc.1 ∈ C.datatypes.allTypeNames
  /-- `"arrow"` resolves as a known type of `C`. Strata Core always knows that name. -/
  arrow_known : "arrow" ∈ C.knownTypes.keywords
  /-- Each base type is a **nullary known type constructor** of `C`. The field
      `argsWellKinded` of `MutualADTWF` needs the arity and not only the name, because the
      generator emits a base type as `.tcons b []`.

      Unlike `base_known` this has no "or a datatype of `C`" disjunct: the vocabulary the
      generators draw from is always backed by `knownTypes` (datatype names are threaded
      separately, through `DatatypePoolOk`), and `LContext.WellKindedTy` — which upstream's
      `init` and `signatureWellKinded` rules use — reads only `knownTypes`. -/
  base_arity : ∀ b ∈ baseTypes, C.knownTypes[b]? = some 0
  /-- Each applied type constructor is a known type constructor of `C` at **its own
      arity**. The generator draws `(kc.1, kc.2)` from the pool and then makes exactly
      `kc.2` arguments. -/
  tyCon_arity : ∀ kc ∈ tyCons, C.knownTypes[kc.1]? = some kc.2
  /-- `"arrow"` is registered at **arity 2**, which is the arity at which the generator
      applies it. -/
  arrow_arity : C.knownTypes["arrow"]? = some 2
  /-- Each known type name of `C` is a reserved name. It is reserved by `baseTypes`, by
      `tyCons`, by `"arrow"` or by `extraReserved`. Therefore a fresh name is not one of
      them. -/
  knownTypes_reserved : ∀ k ∈ C.knownTypes.keywords,
    k ∈ initialReserved baseTypes tyCons extraReserved
  /-- Each datatype name of `C` is a reserved name. Therefore a fresh name is not one of
      them. -/
  datatypes_reserved : ∀ n ∈ C.datatypes.allTypeNames,
    n ∈ initialReserved baseTypes tyCons extraReserved
  /-- Each base type is external in `C`, which means that it is a known primitive and not a
      datatype. Therefore it is `TySymInhab` at once. -/
  base_external : ∀ b ∈ baseTypes, C.datatypes.getType b = none
  /-- Each applied type constructor is external in `C`. -/
  tyCon_external : ∀ kc ∈ tyCons, C.datatypes.getType kc.1 = none
  /-- `"arrow"` is external in `C`. It is a known primitive, and it is never a datatype. -/
  arrow_external : C.datatypes.getType "arrow" = none

end Soundness

/-! ## Inhabitance of the generated block

This part gives the one field of `MutualADTWF` that `argsWF`, `refsKnown` and the facts
about fresh names do not give. That field says that each block datatype is inhabited.
For a datatype `d` of the block, the statement is
`TySymInhab (C.datatypes.push block) d.name`.

The inhabited constructor of `d` gives that fact. `genConstructors` makes that constructor
from the set of names for a lower rank. Therefore each of its argument types holds only block
names of a lower rank, and those datatypes are themselves inhabited.
`genMutuallyRecursiveDatatypes_inhabited` does the induction on the rank. -/

section Inhabitance

open Core Core.TypeSpec

/-- If `getType` finds a datatype at `name`, then `name` is one of the type names of the
    factory. The opposite form of this lemma says that a name that is absent from
    `allTypeNames` resolves to `none`. -/
theorem name_mem_allTypeNames_of_getType {F : @TypeFactory Unit} {name : String}
    {d : LDatatype Unit} (h : F.getType name = some d) :
    name ∈ F.allTypeNames := by
  simp only [TypeFactory.getType] at h
  have hmem := List.find?_some h
  have hd_mem := List.mem_of_find?_eq_some h
  simp only [beq_iff_eq] at hmem
  simp only [TypeFactory.allTypeNames, List.mem_map]
  exact ⟨d, hd_mem, hmem⟩

/-- Take a list of datatypes whose names are different in pairs. Then `find?` by name over
    that list returns the one member with that name. The proof is an induction on the
    list. -/
theorem find?_name_eq_of_mem {block : MutualDatatype Unit} {d : LDatatype Unit}
    (hnodup : (block.map (·.name)).Nodup) (hd : d ∈ block) :
    block.find? (fun d' => d'.name == d.name) = some d := by
  induction block with
  | nil => exact absurd hd (by simp)
  | cons hd0 tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hnodup'⟩ := hnodup
    rcases List.mem_cons.mp hd with rfl | hd
    · simp
    · -- `hd0.name ≠ d.name` (else `d.name` would be `hd0.name ∈ tl.map name`).
      have hne : hd0.name ≠ d.name := by
        intro heq; exact hnotin (heq ▸ List.mem_map.mpr ⟨d, hd, rfl⟩)
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hne]
      exact ih hnodup' hd

/-- Take a name that is absent from the names of a list of datatypes. Then `find?` by that
    name returns `none`. -/
theorem find?_name_eq_none {block : MutualDatatype Unit} {name : String}
    (hne : name ∉ block.map (·.name)) :
    block.find? (fun d' => d'.name == name) = none := by
  induction block with
  | nil => rfl
  | cons hd0 tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hne
    obtain ⟨hne0, hne'⟩ := hne
    simp only [List.find?_cons, beq_eq_false_iff_ne.mpr (fun h => hne0 h.symm)]
    exact ih hne'

/-- A push of `block` adds its datatypes to the end of the flat list of datatypes. -/
theorem allDatatypes_push {C : LContext CoreLParams} {block : MutualDatatype Unit} :
    TypeFactory.allDatatypes (C.datatypes.push block) =
      C.datatypes.allDatatypes ++ block := by
  simp [TypeFactory.allDatatypes, Array.toList_push, List.flatten_append]

/-- `allDatatypes_push` for an arbitrary factory (not just one that is some
    context's `datatypes` field). Used by `tySymInhab_push`, which is stated over a
    bare `TypeFactory`. -/
theorem allDatatypes_push' {F : @TypeFactory Unit} {block : MutualDatatype Unit} :
    TypeFactory.allDatatypes (F.push block) = F.allDatatypes ++ block := by
  simp [TypeFactory.allDatatypes, Array.toList_push, List.flatten_append]

/-- `getType` on a factory with `block` added. A push of `block` makes the name of each member
    resolve to that member. This result needs two conditions. The name must not already
    resolve in `C.datatypes`, therefore it is fresh. The block names must be different in
    pairs. -/
theorem getType_push_self {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {d : LDatatype Unit} (hnew : C.datatypes.getType d.name = none)
    (hnodup : (block.map (·.name)).Nodup) (hd : d ∈ block) :
    TypeFactory.getType (C.datatypes.push block) d.name = some d := by
  have hnone : C.datatypes.allDatatypes.find? (fun d' => d'.name == d.name) = none := hnew
  -- `find?` passes over the first part, which holds no such name, and it then matches `d`
  -- in the block at the end.
  rw [TypeFactory.getType, allDatatypes_push, List.find?_append, hnone, Option.none_or,
      find?_name_eq_of_mem hnodup hd]

/-- `getType` on the longer factory, for a name that is absent from the block. The result
    agrees with `C.datatypes`. In particular, an external symbol of `C` stays external. -/
theorem getType_push_other {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {name : String} (hne : name ∉ block.map (·.name))
    (hext : C.datatypes.getType name = none) :
    TypeFactory.getType (C.datatypes.push block) name = none := by
  have hnone : C.datatypes.allDatatypes.find? (fun d' => d'.name == name) = none := hext
  -- The first part gives no result, by `hext`. No block datatype matches, by `hne`.
  rw [TypeFactory.getType, allDatatypes_push, List.find?_append, hnone, Option.none_or,
      find?_name_eq_none hne]

/-! ### Transporting inhabitance of an *existing* datatype across a block push

`MutualADTWF.inhabited` is stated in the *extended* factory
`C.datatypes.push block`, but a datatype that is already stored in `C` carries its
inhabitance in `C.datatypes`. Moving the latter to the former is what lets a
generated block reference a datatype declared by an *earlier* declaration —
interleaving direction (4) of `docs/program-gen-interleaving.md`, which the design
doc had ruled out on the grounds that a stored datatype cannot ride
`TySymInhab.external`. It does not need to: it rides `TySymInhab.datatype`, whose
premise is exactly the inhabitance we already have.

Inhabitance is **not** monotone under `push` in general. A derivation in
`C.datatypes` may use `.external name` for a symbol that is absent from
`C.datatypes` but *is* one of `block`'s names; after the push that symbol resolves
to a block datatype, and `.external` no longer applies. The extra hypothesis
`hstored` rules this out: no block name occurs in any constructor argument of any
datatype stored in `C`. The fold maintains it because every block name is drawn
fresh against a reserved set that already contains every type name referenced by
the stored datatypes. -/

/-- **Inhabitance survives a block push**, given that the pushed names are new and
    do not occur in the existing factory's constructor arguments.

    The proof is the three-relation recursor with the "no block name occurs here"
    side condition threaded through all three motives:

    * `TyInhab ty` transports when `BlockAbsent block ty`;
    * `TySymInhab n` transports when `n` is not a block name;
    * `ConstrInhab c` transports when no block name occurs in `c`'s arguments.

    The `.external` case is where `hstored` is consumed: the symbol stayed `none`
    after the push precisely because it is not a block name. The `.datatype` case
    uses `hstored` to feed the induction hypothesis for the witnessing
    constructor's arguments. -/
theorem tySymInhab_push {adts : @TypeFactory Unit} {block : MutualDatatype Unit}
    (hstored : ∀ d ∈ adts.allDatatypes, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      BlockAbsent block arg.2)
    {name : String} (hname : name ∉ block.map (·.name))
    (h : TySymInhab adts name) :
    TySymInhab (adts.push block) name := by
  -- `getType` on the pushed factory agrees with `adts` off the block names.
  have hget : ∀ n, n ∉ block.map (·.name) →
      TypeFactory.getType (adts.push block) n = adts.getType n := by
    intro n hn
    rcases hsome : adts.getType n with _ | d
    · rw [TypeFactory.getType, allDatatypes_push', List.find?_append,
        (show adts.allDatatypes.find? (fun d' => d'.name == n) = none from hsome),
        Option.none_or, find?_name_eq_none hn]
    · rw [TypeFactory.getType, allDatatypes_push', List.find?_append,
        (show adts.allDatatypes.find? (fun d' => d'.name == n) = some d from hsome),
        Option.some_or]
  refine TySymInhab.rec
    (motive_1 := fun ty _ => BlockAbsent block ty → TyInhab (adts.push block) ty)
    (motive_2 := fun n _ => n ∉ block.map (·.name) → TySymInhab (adts.push block) n)
    (motive_3 := fun c _ => (∀ arg ∈ c.args, BlockAbsent block arg.2) →
      ConstrInhab (adts.push block) c)
    ?ftvar ?bitvec ?tcons ?external ?datatype ?mk h hname
  case ftvar => intro v _; exact .ftvar v
  case bitvec => intro sz _; exact .bitvec sz
  case tcons =>
    -- The head is not a block name (no block name occurs at all), and each argument
    -- is likewise block-absent.
    intro nm args _ _ ihsym ihargs habs
    exact .tcons nm args (ihsym (head_not_mem_of_blockAbsent habs))
      (fun a ha => ihargs a ha (blockAbsent_of_mem_args habs ha))
  case external =>
    -- `nm` stayed unresolved after the push, because it is not a block name.
    intro nm hnone hnm
    exact .external nm (by rw [hget nm hnm]; exact hnone)
  case datatype =>
    -- `nm` resolves to the *same* stored datatype after the push. Its witnessing
    -- constructor's arguments hold no block name (`hstored`), so the induction
    -- hypothesis applies.
    intro nm d c hsome hmem _ ihc hnm
    refine .datatype nm d c (by rw [hget nm hnm]; exact hsome) hmem (ihc ?_)
    have hd : d ∈ adts.allDatatypes := List.mem_of_find?_eq_some hsome
    exact fun arg harg => hstored d hd c hmem arg harg
  case mk =>
    intro c _ ihargs habs
    exact .mk c (fun arg harg => ihargs arg harg (habs arg harg))


/-! #### The pool of *previously declared* datatypes (interleaving direction (4))

`ContextOk`'s externality fields (`base_external` / `tyCon_external`) say that
every referenceable head is a known primitive, *not* a datatype of `C`. That is
how the head gets `TySymInhab` — via `.external`. It is also why a datatype
declared by an earlier declaration cannot simply be appended to `tyCons`: it *is*
a datatype of `C`, so the field is false for it.

But externality is only a *means* to inhabitance. A stored datatype reaches
`TySymInhab` through the other constructor, `.datatype`, and the fold already
knows the required premise, because the datatype entered `C` only through a gated
`addMutualBlock` whose block had been proved `MutualADTWF` (whose `inhabited`
field is exactly this). So prior datatypes are carried in a *separate* pool with
its own hypothesis bundle, and the inhabitance lemmas case on which pool a head
came from. `ContextOk` and `defaultContextOk` are untouched. -/

/-- What the ambient context must give about a pool of *previously declared*
    datatype constructors that a new block may reference. Unlike `ContextOk`'s
    `tyCons`, these names are datatypes of `C`, so they are inhabited by
    `TySymInhab.datatype` rather than `.external`.

    `known` feeds `MutualADTWF.refsKnown` (via the `allTypeNames` disjunct);
    `inhab` feeds `MutualADTWF.inhabited` (transported across the block push by
    `tySymInhab_push`). -/
structure DatatypePoolOk (C : LContext CoreLParams) (dtCons : List KnownTyCon) : Prop where
  /-- Each pool name resolves as an existing datatype of `C`. -/
  known : ∀ kc ∈ dtCons, kc.1 ∈ C.datatypes.allTypeNames
  /-- Each pool name resolves as an existing datatype of `C` *at the pool's arity*: the
      datatype declares exactly `kc.2` type parameters. This is the arity-aware form of
      `known`, and it is what `MutualADTWF.argsWellKinded` needs. -/
  arity : ∀ kc ∈ dtCons,
    ∃ d ∈ C.datatypes.allDatatypes, d.name = kc.1 ∧ d.typeArgs.length = kc.2
  /-- Each pool name is inhabited in `C`'s own factory. -/
  inhab : ∀ kc ∈ dtCons, TySymInhab C.datatypes kc.1

/-- Every constructor argument of every datatype stored in `C` is free of block
    names. This is the side condition `tySymInhab_push` needs, packaged for reuse.
    The fold maintains it because block names are drawn fresh against a reserved
    set that already contains every type name the stored datatypes mention. -/
def StoredRefsAbsent (C : LContext CoreLParams) (block : MutualDatatype Unit) : Prop :=
  ∀ d ∈ C.datatypes.allDatatypes, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, BlockAbsent block arg.2

/-- **A pool datatype is inhabited in the extended factory.** Combines
    `DatatypePoolOk.inhab` (inhabitance in `C.datatypes`) with `tySymInhab_push`
    (transport across the push). The pool name must not be a block name — true
    because block names are freshly drawn while pool names are existing datatypes
    of `C`, hence reserved. -/
theorem datatypePool_inhab_push {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {dtCons : List KnownTyCon} (hpool : DatatypePoolOk C dtCons)
    (hstored : StoredRefsAbsent C block)
    {kc : KnownTyCon} (hkc : kc ∈ dtCons) (hnotblk : kc.1 ∉ block.map (·.name)) :
    TySymInhab (C.datatypes.push block) kc.1 :=
  tySymInhab_push hstored hnotblk (hpool.inhab kc hkc)

/-- **A type that holds no block name is inhabited in the longer factory.** This result needs
    each type constructor head of that type to be a name from `baseTypes`, from `tyCons`,
    from the prior-datatype pool `dtCons`, or `"arrow"`. A `baseTypes`/`tyCons`/`"arrow"`
    head must be external in `C`; a `dtCons` head is inhabited by `DatatypePoolOk`. A block
    name cannot be such a head, because no block name is present.

    The proof is an induction on the structure of the type. A rigid type variable and a
    bitvector are inhabited at once. The head of a `.tcons name args` is `TySymInhab` —
    through `.external` for the first three pools, or through the pool's transported
    `.datatype` derivation for `dtCons`. Each argument is inhabited by the induction
    hypothesis, because each argument also holds no block name. -/
theorem tyInhab_of_absent {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {baseTypes : List String} {tyCons dtCons : List KnownTyCon}
    {extraReserved : List String}
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hpool : DatatypePoolOk C dtCons)
    (hstored : StoredRefsAbsent C block)
    (harrow_ext : TypeFactory.getType (C.datatypes.push block) "arrow" = none)
    {ty : LMonoTy}
    (hrefs : ∀ r ∈ getTypeRefs ty,
      r ∈ baseTypes ∨ r ∈ tyCons.map (·.1) ∨ r ∈ dtCons.map (·.1) ∨
        r ∈ block.map (·.name) ∨ r = "arrow")
    (habsent : BlockAbsent block ty) :
    TyInhab (C.datatypes.push block) ty := by
  induction ty using LMonoTy.induct with
  | ftvar f => exact .ftvar f
  | bitvec n => exact .bitvec n
  | tcons name args ih =>
    -- The head `name` is the first reference. It is not a block name, because no block name
    -- is present.
    have hname_ref : name ∈ getTypeRefs (.tcons name args) := by simp [getTypeRefs]
    have hname_notmem : name ∉ block.map (·.name) := head_not_mem_of_blockAbsent habsent
    have hsym : TySymInhab (C.datatypes.push block) name := by
      rcases hrefs name hname_ref with hb | htc | hdt | hblk | harr
      · exact .external _ (getType_push_other hname_notmem (hctx.base_external _ hb))
      · obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp htc
        exact .external _ (getType_push_other hname_notmem (hctx.tyCon_external _ hkc))
      · -- A prior datatype: inhabited through the pool, transported across the push.
        obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp hdt
        exact datatypePool_inhab_push hpool hstored hkc hname_notmem
      · exact absurd hblk hname_notmem
      · exact .external _ (by subst harr; exact harrow_ext)
    refine .tcons name args hsym (fun a ha => ?_)
    -- Each argument also holds no block name, and its references are a subset of the
    -- references of the whole type.
    refine ih a ha (fun r hr => hrefs r ?_) (blockAbsent_of_mem_args habsent ha)
    simp only [getTypeRefs, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨a, ha, hr⟩

/-- **`BlockRefsWF` also holds for a smaller set of references.** Each field is a fact about
    all members of the set. Therefore a subset of a well-formed set is well-formed. This lemma
    gives `BlockRefsWF` for the set of names that the inhabited constructor may use, from
    `BlockRefsWF` for the full set `visibleRefs allHeaders`. -/
theorem BlockRefsWF.mono {block : MutualDatatype Unit} {tyParams : List TyIdentifier}
    {refs refs' : List BlockRef} (hsub : ∀ br ∈ refs', br ∈ refs)
    (h : BlockRefsWF block tyParams refs) : BlockRefsWF block tyParams refs' :=
  ⟨fun br hbr => h.mem br (hsub br hbr),
   fun br hbr => h.uniform br (hsub br hbr),
   fun br hbr => h.ftvarArgs br (hsub br hbr),
   fun br hbr => h.argsScoped br (hsub br hbr)⟩

/-- **A type that `genArgTy` draws from a set of inhabited references is inhabited.** The
    generator draws the inhabited constructor of each datatype at the flag `true`, from the
    references to the block datatypes of a lower rank. Each of those datatypes is inhabited,
    which `hinhab` gives. This lemma changes that fact into `TyInhab` for the full argument type:

    * A recursive occurrence `br.1 br.2` is a member of the set. Its head is inhabited by
      `hinhab`, and each of its arguments is a type variable by `BlockRefsWF.ftvarArgs`.
      Therefore it is inhabited.
    * A base type and an applied type constructor have an external head, which is not a block
      name. Their arguments hold no block name, because the generator draws those positions at
      the flag `false`. Therefore `tyInhab_of_absent` gives that they are inhabited.
    * An arrow recurses into its codomain, which the generator makes at the flag `rca`. Its
      domain holds no block name, because the generator makes it at the flag `false`.
      Therefore `tyInhab_of_absent` gives the domain.

    The proof is a strong induction on `size` through the one-step description of the
    support. -/
theorem genArgTy_tyInhab {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {baseTypes : List String} {allTyCons tyCons dtCons : List KnownTyCon}
    {extraReserved : List String} {poolRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hpool : DatatypePoolOk C dtCons)
    (hstored : StoredRefsAbsent C block)
    (hsplit : ∀ kc ∈ allTyCons, kc ∈ tyCons ∨ kc ∈ dtCons)
    (hn : NamesOk baseTypes allTyCons (block.map (·.name)))
    (hbr : BlockRefsWF block tyParams poolRefs)
    (harrow_ext : TypeFactory.getType (C.datatypes.push block) "arrow" = none)
    (hinhab : ∀ br ∈ poolRefs, TySymInhab (C.datatypes.push block) br.1) :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes allTyCons poolRefs
        tyParams rca size) →
      TyInhab (C.datatypes.push block) ty := by
  -- A head from `baseTypes` is external in the longer factory. It is not a block name,
  -- therefore `getType_push_other` applies.
  have hbase_ext : ∀ b ∈ baseTypes, TypeFactory.getType (C.datatypes.push block) b = none :=
    fun b hb => getType_push_other (hn.base_notMem b hb) (hctx.base_external b hb)
  -- A head from the *combined* vocabulary is inhabited: external if it came from `tyCons`,
  -- and a transported `.datatype` derivation if it came from the prior-datatype pool.
  have hTyConInhab : ∀ kc ∈ allTyCons, TySymInhab (C.datatypes.push block) kc.1 := by
    intro kc hkc
    rcases hsplit kc hkc with hext | hdt
    · exact .external _ (getType_push_other (hn.tyCon_notMem kc hkc)
        (hctx.tyCon_external kc hext))
    · exact datatypePool_inhab_push hpool hstored hdt (hn.tyCon_notMem kc hkc)
  -- References of a generated type land in the combined vocabulary; re-route them into the
  -- five-way disjunction `tyInhab_of_absent` expects.
  have hrefs_split : ∀ {ty : LMonoTy},
      (∀ r ∈ getTypeRefs ty,
        r ∈ baseTypes ∨ r ∈ allTyCons.map (·.1) ∨ r ∈ block.map (·.name) ∨ r = "arrow") →
      ∀ r ∈ getTypeRefs ty,
        r ∈ baseTypes ∨ r ∈ tyCons.map (·.1) ∨ r ∈ dtCons.map (·.1) ∨
          r ∈ block.map (·.name) ∨ r = "arrow" := by
    intro ty href r hr
    rcases href r hr with hb | htc | hblk | harr
    · exact Or.inl hb
    · obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp htc
      rcases hsplit kc hkc with hext | hdt
      · exact Or.inr (Or.inl (List.mem_map.mpr ⟨kc, hext, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨kc, hdt, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hblk)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr harr)))
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro rca ty h
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨w, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨v, _, rfl⟩ | ⟨_, br, hbrmem, rfl⟩
      · exact .bitvec w
      · exact .tcons b [] (.external _ (hbase_ext b hb)) (by simp)
      · exact .ftvar v
      · -- A recursive occurrence. Its head is inhabited, and each of its arguments is a
        -- type variable.
        refine .tcons br.1 br.2 (hinhab br hbrmem) (fun a ha => ?_)
        obtain ⟨v, rfl⟩ := hbr.ftvarArgs br hbrmem a ha
        exact .ftvar v
    · -- An arrow. Its domain holds no block name, because the flag is `false`. The
      -- induction hypothesis gives its codomain.
      have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      rw [LMonoTy.arrow]
      refine .tcons "arrow" [t1, t2] (.external _ harrow_ext) (fun a ha => ?_)
      rcases List.mem_cons.mp ha with rfl | ha
      · exact tyInhab_of_absent hctx hpool hstored harrow_ext
          (hrefs_split (genArgTy_refs hbr _ h1)) (genArgTy_absent hn _ h1)
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact ih _ hhalf h2
        · cases ha
    · -- An applied type constructor. Its head is inhabited (external, or a prior datatype),
      -- and its arguments hold no block name, because the flag is `false`.
      refine .tcons k args (hTyConInhab (k, args.length) hkc) (fun a ha => ?_)
      exact tyInhab_of_absent hctx hpool hstored harrow_ext
        (hrefs_split (genArgTy_refs hbr _ (hall a ha))) (genArgTy_absent hn _ (hall a ha))

/-! ### A permutation of the block keeps `MutualADTWF`

The rank-based `genMutuallyRecursiveDatatypes` emits the datatypes in the order of the drawn
names, and it applies no permutation to the block. Therefore soundness needs no result about
a permutation. This section keeps that result as a separate fact, because the statement of
completeness for a full block accepts each order of the datatypes.

Each field of `MutualADTWF` has one of three forms. A field can be a fact of the form
`∀ d ∈ block, …`, and a permutation keeps membership. A field can be a fact about
`block.map (·.name)`, and a permutation keeps that list, its property `Nodup` and the
property `≠ []`. The last field is the one about inhabitance, and it reads `block` through
`C.datatypes.push block`.

Inhabitance also holds after a permutation. The three relations for inhabitance read the
factory only through `getType`. Take two blocks that are permutations of each other, with
names that are different in pairs. Then the two longer factories agree on `getType` at each
name, which `getType_push_perm` gives.

`getType` is a `find?` by name. For names that are different in pairs, it returns the one
datatype with that name, at each order of the list. -/

/-- **Two blocks that are permutations of each other, with names that are different in pairs,
    give factories that agree on `getType`.** `getType` is a `find?` by name over
    `C.datatypes ++ block`. At each name, membership gives its result, which
    `find?_name_eq_of_mem` and `find?_name_eq_none` state. A permutation keeps
    membership. -/
theorem getType_push_perm {C : LContext CoreLParams} {block block' : MutualDatatype Unit}
    (hperm : block.Perm block') (hnodup : (block.map (·.name)).Nodup) (name : String) :
    TypeFactory.getType (C.datatypes.push block) name =
      TypeFactory.getType (C.datatypes.push block') name := by
  have hnodup' : (block'.map (·.name)).Nodup := (hperm.map (·.name)).nodup_iff.mp hnodup
  by_cases hmem : name ∈ block.map (·.name)
  · -- `name` resolves in both blocks, and it resolves to the one datatype with that name.
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmem
    have hd' : d ∈ block' := (hperm.mem_iff).mp hd
    rw [TypeFactory.getType, allDatatypes_push, List.find?_append,
        TypeFactory.getType, allDatatypes_push, List.find?_append]
    -- Both blocks match `d`. The first part, which comes from `C.datatypes`, is the same for
    -- both.
    rcases hpre : (C.datatypes.allDatatypes.find? (fun d' => d'.name == d.name)) with _ | dd
    · rw [hpre, Option.none_or, Option.none_or, find?_name_eq_of_mem hnodup hd,
        find?_name_eq_of_mem hnodup' hd']
    · rw [hpre, Option.some_or, Option.some_or]
  · -- `name` resolves in no block. Therefore both sides reduce to the first part.
    have hmem' : name ∉ block'.map (·.name) := fun h => hmem ((hperm.map (·.name)).mem_iff.mpr h)
    rw [TypeFactory.getType, allDatatypes_push, List.find?_append,
        TypeFactory.getType, allDatatypes_push, List.find?_append,
        find?_name_eq_none hmem, find?_name_eq_none hmem']

/-- **Inhabitance holds for two factories that agree on `getType`.** The three relations
    `TyInhab`, `TySymInhab` and `ConstrInhab` read the factory only through `getType`.
    Therefore agreement at each name carries each derivation from one factory to the other.
    The proof uses the recursor for the three relations. This file exports only the part for
    `TySymInhab`. -/
theorem tySymInhab_getType_congr {adts adts' : @TypeFactory Unit}
    (hget : ∀ name, adts.getType name = adts'.getType name) :
    ∀ {name : String}, TySymInhab adts name → TySymInhab adts' name := by
  intro name h
  exact TySymInhab.rec
    (motive_1 := fun ty _ => TyInhab adts' ty)
    (motive_2 := fun n _ => TySymInhab adts' n)
    (motive_3 := fun c _ => ConstrInhab adts' c)
    (fun v => TyInhab.ftvar v)
    (fun sz => TyInhab.bitvec sz)
    (fun name args _ _ ihsym ihargs => TyInhab.tcons name args ihsym ihargs)
    (fun name hnone => TySymInhab.external name (by rw [← hget]; exact hnone))
    (fun name d c hsome hmem _ ihc => TySymInhab.datatype name d c (by rw [← hget]; exact hsome) hmem ihc)
    (fun c _ ihargs => ConstrInhab.mk c ihargs)
    h

end Inhabitance

section MutualADTWFSoundness

open Core Core.TypeSpec

/-- **The field `inhabited` for a generated block.** Each datatype `d` of a generated block is
    inhabited in `C.datatypes.push block`.

    Each datatype draws a rank, and its inhabited constructor refers only to block datatypes of
    a lower rank. `genConstructorsForAllTypes_witness` gives that fact. A block name gives its
    rank, which `zip_rank_functional` gives. Therefore a **strong induction on the rank**
    shows that each datatype is inhabited.

    The inhabited constructor of a datatype at the smallest rank refers to no block datatype.
    Each datatype at a higher rank is inhabited through the block datatypes of a lower rank,
    and those datatypes are themselves inhabited. This proof uses no order of the datatypes. -/
theorem genMutuallyRecursiveDatatypes_inhabited {baseTypes : List String}
    {allTyCons tyCons dtCons : List KnownTyCon}
    {C : LContext CoreLParams}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (harrow : ∀ kc ∈ allTyCons, kc.1 ≠ "arrow")
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hpool : DatatypePoolOk C dtCons)
    (hstored : StoredRefsAbsent C block)
    (hsplit : ∀ kc ∈ allTyCons, kc ∈ tyCons ∨ kc ∈ dtCons)
    (hsubTC : ∀ kc ∈ tyCons, kc ∈ allTyCons)
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes allTyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, TySymInhab (C.datatypes.push block) d.name := by
  simp only [genMutuallyRecursiveDatatypes, mem_support_bind_iff] at hb
  obtain ⟨numExtra, _, names, hnames, paramsList, hparams, ranks, hranksmem, hbodies⟩ := hb
  let headers : List TypeConstructor :=
    (names.zip paramsList).map (fun p => { name := p.1, params := p.2 })
  let rankedHeaders : List (TypeConstructor × Nat) := headers.zip ranks
  have hnameslen : names.length = numExtra + 1 := genFreshNames_length _ _ _ hnames
  have hparamslen : paramsList.length = names.length := by
    rw [genParamsList_length _ _ _ _ hparams, hnameslen]
  have hheadernames : headers.map (·.name) = names :=
    map_name_headers_of_length_le names paramsList (by omega)
  have hrhsub : ∀ hr ∈ rankedHeaders, hr.1 ∈ headers :=
    fun hr hhr => by obtain ⟨h, r⟩ := hr; exact (List.of_mem_zip hhr).1
  have hheaderslen : headers.length = names.length := by
    simp only [headers, List.length_map, List.length_zip, hparamslen]; omega
  have hrankslen : ranks.length = names.length := by
    rw [genRanks_length _ _ _ hranksmem, hnameslen]
  have hrhfst : rankedHeaders.map (·.1) = headers :=
    List.map_fst_zip (Nat.le_of_eq (by rw [hheaderslen, hrankslen]))
  -- Facts about the full block. The proof gets each of them from the concrete `headers`.
  have hbnames : block.map (·.name) = headers.map (·.name) := by
    rw [genConstructorsForAllTypes_names hrhsub rankedHeaders block hrhsub hbodies]
    have : rankedHeaders.map (fun hr => hr.1.name) = headers.map (·.name) := by
      rw [← hrhfst, List.map_map]; rfl
    rw [this]
  have hnodupH : (headers.map (·.name)).Nodup := by
    rw [hheadernames]; exact genFreshNames_nodup _ _ _ hnames
  have hfresh : ∀ h ∈ headers, h.name ∉ initialReserved baseTypes allTyCons extraReserved := by
    intro h hh
    have : h.name ∈ names := by rw [← hheadernames]; exact List.mem_map.mpr ⟨h, hh, rfl⟩
    exact genFreshNames_fresh _ _ _ hnames h.name this
  have hheader : ∀ d ∈ block, ∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs :=
    fun d hd => by
      obtain ⟨⟨h, r⟩, hhr, h1, h2⟩ := (genConstructorsForAllTypes_shape hrhsub rankedHeaders block hrhsub hbodies d hd).1
      exact ⟨h, hrhsub (h, r) hhr, h1, h2⟩
  have hnodup : (block.map (·.name)).Nodup := by rw [hbnames]; exact hnodupH
  have hnfresh : ∀ n ∈ block.map (·.name), n ∉ initialReserved baseTypes allTyCons extraReserved := by
    rw [hbnames]; intro n hn; obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn; exact hfresh h hh
  have hn : NamesOk baseTypes allTyCons (block.map (·.name)) := namesOk_of_fresh harrow hnfresh
  have harrow_notmem : "arrow" ∉ block.map (·.name) :=
    fun hmem => hn.block_ne_arrow _ hmem rfl
  have harrow_ext : TypeFactory.getType (C.datatypes.push block) "arrow" = none :=
    getType_push_other harrow_notmem hctx.arrow_external
  -- `ContextOk` reserves against `tyCons`, while freshness is stated against the wider
  -- `allTyCons`. The former's reserved set is contained in the latter's (`initialReserved`
  -- mentions the vocabulary positively), so freshness against `allTyCons` is the stronger
  -- fact and transfers.
  have hinit_mono : ∀ x, x ∈ initialReserved baseTypes tyCons extraReserved →
      x ∈ initialReserved baseTypes allTyCons extraReserved := by
    intro x hx
    simp only [initialReserved, List.mem_cons, List.mem_append] at hx ⊢
    rcases hx with h | ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
    · obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp h
      exact Or.inr (Or.inl (Or.inr (List.mem_map.mpr ⟨kc, hsubTC kc hkc, rfl⟩)))
    · exact Or.inr (Or.inr h)
  have hnew : ∀ d ∈ block, C.datatypes.getType d.name = none := by
    intro d hd
    rcases hsome : C.datatypes.getType d.name with _ | dd
    · rfl
    · exact absurd
        (hinit_mono _ (hctx.datatypes_reserved _ (name_mem_allTypeNames_of_getType hsome)))
        (hnfresh d.name (List.mem_map.mpr ⟨d, hd, rfl⟩))
  -- Each `d ∈ block` has a header with its rank, which is `(h, r)`. It also has an inhabited
  -- constructor, and the generator drew that constructor from the set of names for a lower
  -- rank.
  have hwitness := genConstructorsForAllTypes_witness hrhsub rankedHeaders block hrhsub hbodies
  -- **A strong induction on the rank.** Each `d ∈ block` with the header `(h, r)` is
  -- inhabited. A reference of its inhabited constructor names a block datatype of a rank less
  -- than `r`, and the induction hypothesis says that this datatype is inhabited.
  have key : ∀ (r : Nat) (d : LDatatype Unit) (h : TypeConstructor),
      d ∈ block → (h, r) ∈ rankedHeaders →
      h.name = d.name → TySymInhab (C.datatypes.push block) d.name := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro d h hd hhr hhname
      obtain ⟨⟨hw, rw'⟩, hwmem, hwname, hwparams, c₀, hc₀, hwit⟩ := hwitness d hd
      -- The pairs `(hw, rw')` and `(h, r)` share the name `d.name`, therefore `rw' = r`.
      have hrweq : rw' = r := by
        apply zip_rank_functional hnodupH hwmem hhr
        rw [hwname, hhname]
      subst hrweq
      -- The set of names for the inhabited constructor is well-formed. Each of its members
      -- has a lower rank, therefore each of them is inhabited.
      have hd_block := hd
      have hfullWF : BlockRefsWF block d.typeArgs (visibleRefs headers d.typeArgs) :=
        visibleRefs_blockRefsWF hbnames hnodupH hheader hd_block
      have hpoolsub : ∀ br ∈ visibleRefs (lowerRankHeaders rankedHeaders rw') hw.params,
          br ∈ visibleRefs headers hw.params :=
        visibleRefs_mono (lowerRankHeaders_subset hrhsub rw')
      have hpoolsub' : ∀ br ∈ visibleRefs (lowerRankHeaders rankedHeaders rw') d.typeArgs,
          br ∈ visibleRefs headers d.typeArgs := hwparams ▸ hpoolsub
      have hpoolWF : BlockRefsWF block d.typeArgs
          (visibleRefs (lowerRankHeaders rankedHeaders rw') d.typeArgs) :=
        hfullWF.mono hpoolsub'
      -- Each member of that set names a block datatype of a lower rank.
      have hpoolInhab : ∀ br ∈ visibleRefs (lowerRankHeaders rankedHeaders rw') d.typeArgs,
          TySymInhab (C.datatypes.push block) br.1 := by
        intro br hbr
        obtain ⟨h', hh', _, rfl⟩ := (visibleRefs_mem_iff _ _ _).mp hbr
        obtain ⟨r'', hr''mem, hr''lt⟩ := (lowerRankHeaders_mem_iff _ _ _).mp hh'
        -- `h'.name` is a block name, therefore a block datatype `d'` has that name.
        have : h'.name ∈ block.map (·.name) := by
          rw [hbnames]; exact List.mem_map.mpr ⟨h', hrhsub (h', r'') hr''mem, rfl⟩
        obtain ⟨d', hd'mem, hd'name⟩ := List.mem_map.mp this
        rw [← hd'name]
        exact ih r'' hr''lt d' h' hd'mem hr''mem hd'name.symm
      -- `d` is inhabited through its inhabited constructor.
      refine .datatype d.name d c₀
        (getType_push_self (hnew d hd_block) hnodup hd_block) hc₀ (.mk c₀ ?_)
      intro arg harg
      obtain ⟨size, hsize⟩ := hwit arg harg
      rw [hwparams] at hsize
      exact genArgTy_tyInhab hctx hpool hstored hsplit hn hpoolWF harrow_ext hpoolInhab size hsize
  -- Each `d ∈ block` has a header with its rank, and that header holds its name. Therefore
  -- `key` applies.
  intro d hd
  obtain ⟨⟨h, r⟩, hhr, hhname, _, _⟩ := hwitness d hd
  exact key r d h hd hhr hhname

/-- **The main theorem. A generated block is `MutualADTWF`.** Each mutually recursive block
    that `genMutuallyRecursiveDatatypes` makes is well-formed in each context `C` that obeys
    `ContextOk`. The block obeys all nine fields of `Core.TypeSpec.MutualADTWF`.

    This theorem has two groups of hypotheses. The first is one condition on the pool `tyCons`
    that the caller gives, which is `tyCon_ne_arrow`, as for `argsWF`. The second is the
    structure `ContextOk`, which says how the ambient context must relate to the names that
    the generator uses. -/
theorem genMutuallyRecursiveDatatypes_MutualADTWF {baseTypes : List String}
    {allTyCons tyCons dtCons : List KnownTyCon}
    {C : LContext CoreLParams}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (harrow : ∀ kc ∈ allTyCons, kc.1 ≠ "arrow")
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hpool : DatatypePoolOk C dtCons)
    (hstored : StoredRefsAbsent C block)
    (hsplit : ∀ kc ∈ allTyCons, kc ∈ tyCons ∨ kc ∈ dtCons)
    (hsubTC : ∀ kc ∈ tyCons, kc ∈ allTyCons)
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes allTyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    MutualADTWF C block := by
  obtain ⟨headers, hne, hbnames, hnodupH, hfresh, hheader, _⟩ := genMutuallyRecursiveDatatypes_shape hb
  have hnfresh : ∀ n ∈ block.map (·.name), n ∉ initialReserved baseTypes allTyCons extraReserved := by
    rw [hbnames]; intro n hn; obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn; exact hfresh h hh
  -- `ContextOk` reserves against `tyCons ⊆ allTyCons`, so its reserved set is contained in
  -- the one block names were drawn fresh against.
  have hinit_mono : ∀ x, x ∈ initialReserved baseTypes tyCons extraReserved →
      x ∈ initialReserved baseTypes allTyCons extraReserved := by
    intro x hx
    simp only [initialReserved, List.mem_cons, List.mem_append] at hx ⊢
    rcases hx with h | ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
    · obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp h
      exact Or.inr (Or.inl (Or.inr (List.mem_map.mpr ⟨kc, hsubTC kc hkc, rfl⟩)))
    · exact Or.inr (Or.inr h)
  refine
    { nonempty := hne
      namesNodup := by rw [hbnames]; exact hnodupH
      namesFresh := ?_
      namesNew := ?_
      argVarsScoped := genMutuallyRecursiveDatatypes_argVarsScoped hb
      argsWF := genMutuallyRecursiveDatatypes_argsWF harrow hb
      refsKnown := ?_
      argsWellKinded := ?_
      inhabited :=
        genMutuallyRecursiveDatatypes_inhabited harrow hctx hpool hstored hsplit hsubTC hb }
  · -- namesFresh: no block name is a known type of `C`.
    intro d hd hcontains
    -- A known-type name of `C` is reserved, but block names are drawn fresh.
    exact hnfresh d.name (List.mem_map.mpr ⟨d, hd, rfl⟩)
      (hinit_mono _ (hctx.knownTypes_reserved _ (by
        simpa [KnownTypes.containsName, KnownTypes.keywords] using hcontains)))
  · -- namesNew: no block name is an existing datatype of `C`.
    intro d hd
    rcases hsome : C.datatypes.getType d.name with _ | dd
    · rfl
    · exact absurd
        (hinit_mono _ (hctx.datatypes_reserved _ (name_mem_allTypeNames_of_getType hsome)))
        (hnfresh d.name (List.mem_map.mpr ⟨d, hd, rfl⟩))
  · -- The field `refsKnown`. Each reference resolves in `C`, or it is a block name, or it is
    -- `"arrow"`.
    intro d hd c hc arg harg r hr
    rcases genMutuallyRecursiveDatatypes_refsKnown hb d hd c hc arg harg r hr with
      hbt | htc | hblk | harr
    · rcases hctx.base_known r hbt with hk | hdt
      · exact Or.inl hk
      · exact Or.inr (Or.inl hdt)
    · obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp htc
      -- A vocabulary reference is either an external known type (`ContextOk`) or a
      -- previously declared datatype (`DatatypePoolOk.known`).
      rcases hsplit kc hkc with hext | hdt
      · rcases hctx.tyCon_known kc hext with hk | hdt'
        · exact Or.inl hk
        · exact Or.inr (Or.inl hdt')
      · exact Or.inr (Or.inl (hpool.known kc hdt))
    · exact Or.inr (Or.inr hblk)
    · subst harr; exact Or.inl hctx.arrow_known
  · -- The field `argsWellKinded`. The generator is arity-correct by construction
    -- (`genMutuallyRecursiveDatatypes_arities`); the arity fields of `ContextOk` and
    -- `DatatypePoolOk` say that `C` registers each of those names at that same arity.
    intro d hd c hc arg harg ref n hn
    rcases genMutuallyRecursiveDatatypes_arities hb d hd c hc arg harg ref n hn with
      ⟨hbt, rfl⟩ | htc | hblk | ⟨rfl, rfl⟩
    · exact Or.inl (hctx.base_arity ref hbt)
    · -- A vocabulary entry is either an external known type (`ContextOk.tyCon_arity`) or a
      -- previously declared datatype (`DatatypePoolOk.arity`), at the pool's arity.
      rcases hsplit (ref, n) htc with hext | hdt
      · exact Or.inl (hctx.tyCon_arity (ref, n) hext)
      · exact Or.inr (Or.inl (hpool.arity (ref, n) hdt))
    · exact Or.inr (Or.inr hblk)
    · exact Or.inl hctx.arrow_arity

/-! ### The corollary for the default parameters and the true Strata Core context

`genMutuallyRecursiveDatatypes_MutualADTWF` speaks about an abstract `C : LContext
CoreLParams`, and it takes `ContextOk` as a hypothesis. This section discharges that
hypothesis for the concrete context that Strata Core uses, which holds `Core.KnownTypes` and
no datatypes. It then shows that the generator is sound against that context.

This section gives `Core.KnownTypes.keywords` for `extraReserved`. That list is the pool of
names that the caller must forbid. Therefore a block name cannot be the same as a symbol that
Core already knows.

`Core.KnownTypes.keywords` is a `HashMap`, and the kernel does not reduce its entries.
Therefore `native_decide` gives the concrete facts about membership in it. That tactic adds
the axiom `Lean.ofReduceBool` to this corollary alone. The abstract theorem
`genMutuallyRecursiveDatatypes_MutualADTWF` stays clean in its axioms. -/

/-- The reference context of Strata Core. Its known types are `Core.KnownTypes`, and it holds
    no datatype from a user. -/
def coreContext : LContext CoreLParams :=
  { functions := .default, datatypes := #[],
    knownTypes := Core.KnownTypes, idents := {} }

/-- The default names of the generator obey `ContextOk` for `coreContext`, with
    `Core.KnownTypes.keywords` for `extraReserved`. Therefore a new name `d.name` is not the
    same as a symbol that Core already knows, such as `Triggers`, `bitvec` or `TriggerGroup`.
    The generator does not refer to those symbols, but the reservation is still
    necessary. -/
theorem defaultContextOk :
    ContextOk coreContext defaultBaseTypes defaultTyCons Core.KnownTypes.keywords := by
  refine
    { base_known := ?_, tyCon_known := ?_, arrow_known := ?_,
      base_arity := ?_, tyCon_arity := ?_, arrow_arity := ?_,
      knownTypes_reserved := ?_, datatypes_reserved := ?_,
      base_external := ?_, tyCon_external := ?_, arrow_external := ?_ }
  · -- Each default base type is a known primitive of `coreContext`: it was *read off*
    -- `Core.KnownTypes`, so this needs no case analysis on the list's contents.
    intro b hb
    refine Or.inl (Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_isSome_getElem?.mpr ?_))
    show Core.KnownTypes[b]?.isSome = true
    rw [defaultBaseTypes_arity b hb]; rfl
  · -- Each default type constructor is a known primitive of `coreContext`.
    intro kc hkc
    refine Or.inl (Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_isSome_getElem?.mpr ?_))
    show Core.KnownTypes[kc.1]?.isSome = true
    rw [defaultTyCons_arity kc hkc]; rfl
  · -- `"arrow"` is a known primitive of `coreContext`. This one *is* a fact about the
    -- particular contents of `Core.KnownTypes`, because `genArgTy` hardcodes the name.
    show "arrow" ∈ Core.KnownTypes.keywords; native_decide
  · -- Each default base type is registered at arity 0, by construction of the list.
    exact defaultBaseTypes_arity
  · -- Each default type constructor is registered at its own arity, by construction.
    exact defaultTyCons_arity
  · -- `"arrow"` is registered at arity 2.
    show Core.KnownTypes["arrow"]? = some 2; native_decide
  · -- Each known type of `coreContext` is a member of the extra reserved list, with no
    -- change.
    intro k hk
    simp only [initialReserved, List.mem_cons, List.mem_append]
    right; right
    exact hk
  · -- `coreContext` holds no datatype, therefore this field has no content.
    intro n hn
    simp [coreContext, TypeFactory.allTypeNames, TypeFactory.allDatatypes] at hn
  · -- `coreContext.datatypes = #[]`, therefore each `getType` gives `none`.
    intro b _
    simp [coreContext, TypeFactory.getType, TypeFactory.allDatatypes]
  · intro kc _
    simp [coreContext, TypeFactory.getType, TypeFactory.allDatatypes]
  · simp [coreContext, TypeFactory.getType, TypeFactory.allDatatypes]

/-- **`MutualADTWF` for the default parameters and the Strata Core context.** Take a block that
    `genMutuallyRecursiveDatatypes` makes at its default parameters, with the known type
    keywords of Core for `extraReserved`. That block is `MutualADTWF` in `coreContext`, which
    is the context that Core programs use.

    `decide` discharges the one side condition, which is `defaultTyCons_ne_arrow`.
    `defaultContextOk` discharges the eight fields of `ContextOk`.

    This corollary uses `native_decide` for membership in `Core.KnownTypes.keywords`.
    Therefore it depends on `Lean.ofReduceBool`, together with the standard axioms. The
    abstract theorem `genMutuallyRecursiveDatatypes_MutualADTWF` does not depend on it. -/
theorem genMutuallyRecursiveDatatypes_MutualADTWF_default
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) defaultBaseTypes
            defaultTyCons maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs
            maxArgs maxSize Core.KnownTypes.keywords)) :
    MutualADTWF coreContext block :=
  -- `coreContext` holds no datatypes, so the prior-datatype pool is empty and both of its
  -- side conditions (`DatatypePoolOk`, `StoredRefsAbsent`) are vacuous.
  genMutuallyRecursiveDatatypes_MutualADTWF (dtCons := []) defaultTyCons_ne_arrow
    defaultContextOk
    { known := by simp, arity := by simp, inhab := by simp }
    (by
      intro d hd
      simp [coreContext, TypeFactory.allDatatypes] at hd)
    (fun kc hkc => Or.inl hkc) (fun kc hkc => hkc) hb

/-! ### A permutation of the block keeps `MutualADTWF`

`MutualADTWF_perm` says that `MutualADTWF` holds after a permutation of the block. The
rank-based `genMutuallyRecursiveDatatypes` emits the datatypes in the order of the drawn
names, and it applies no permutation to the block. Therefore soundness needs no result about
a permutation.

No proof in this file uses `MutualADTWF_perm` now. This file keeps it as a separate fact,
because the statement of completeness for a full block accepts each order of the
datatypes. -/

/-- **`MutualADTWF` holds after a permutation of the block.** Each field has one of three forms.
    A field can be a fact of the form `∀ d ∈ block, …`, and a permutation keeps membership. A
    field can be a fact about `block.map (·.name)`, and a permutation keeps that list, its
    property `Nodup` and the property `≠ []`.

    The last field is the one about inhabitance. It reads `block` only through
    `C.datatypes.push block`, and a permutation keeps the `getType` of that factory, which
    `getType_push_perm` gives. Therefore `tySymInhab_getType_congr` carries inhabitance
    across. -/
theorem MutualADTWF_perm {C : LContext CoreLParams} {block block' : MutualDatatype Unit}
    (hperm : block.Perm block') (h : MutualADTWF C block) : MutualADTWF C block' := by
  have hmem : ∀ {d}, d ∈ block' → d ∈ block := fun hd => hperm.mem_iff.mpr hd
  have hnames : block'.map (·.name) = block.map (·.name) → True := fun _ => trivial
  -- The names of `block` are a permutation of the names of `block'`.
  have hnamesperm : (block.map (·.name)).Perm (block'.map (·.name)) := hperm.map (·.name)
  refine
    { nonempty := ?_
      namesNodup := (hnamesperm.nodup_iff).mp h.namesNodup
      namesFresh := fun d hd => h.namesFresh d (hmem hd)
      namesNew := fun d hd => h.namesNew d (hmem hd)
      argVarsScoped := fun d hd => h.argVarsScoped d (hmem hd)
      argsWF := ?_
      refsKnown := ?_
      argsWellKinded := ?_
      inhabited := ?_ }
  · -- The field `nonempty`. `block'` is not empty, because `block` is not empty and the two
    -- lists are permutations of each other.
    intro hnil
    have : block.Perm [] := hnil ▸ hperm
    exact h.nonempty this.eq_nil
  · -- The field `argsWF`. `ConstrArgWF block'` and `ConstrArgWF block` agree, because the
    -- relations read only `block.map (·.name)`, and a permutation keeps that set.
    intro d hd c hc arg harg
    exact constrArgWF_perm hnamesperm hperm (h.argsWF d (hmem hd) c hc arg harg)
  · -- The field `refsKnown`. A permutation keeps the part about a block name.
    intro d hd c hc arg harg r hr
    rcases h.refsKnown d (hmem hd) c hc arg harg r hr with hk | hdt | hblk
    · exact Or.inl hk
    · exact Or.inr (Or.inl hdt)
    · exact Or.inr (Or.inr (hnamesperm.mem_iff.mp hblk))
  · -- The field `argsWellKinded`. `getTypeConsArities` reads only the argument type, and a
    -- permutation keeps the disjunct about a block datatype.
    intro d hd c hc arg harg ref n hn
    rcases h.argsWellKinded d (hmem hd) c hc arg harg ref n hn with
      hk | hdt | ⟨d', hd', hname, hlen⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inl hdt)
    · exact Or.inr (Or.inr ⟨d', hperm.mem_iff.mp hd', hname, hlen⟩)
  · -- The field `inhabited`. A permutation keeps the `getType` of the longer factory, and
    -- this proof carries inhabitance along that agreement.
    intro d hd
    have hget : ∀ n, TypeFactory.getType (C.datatypes.push block) n
        = TypeFactory.getType (C.datatypes.push block') n :=
      getType_push_perm hperm h.namesNodup
    exact tySymInhab_getType_congr hget (h.inhabited d (hmem hd))

end MutualADTWFSoundness

/-! ## Inhabitance ranks: a rank from `MutualADTWF`, with no order

The rank-based generator draws an explicit rank for each datatype. The inhabited constructor
of a datatype can then refer only to block datatypes of a lower rank.

For the proof of completeness, this file must give a rank for each datatype of an arbitrary
`MutualADTWF` block. The generator must be able to draw that rank, and the rank must make the
true inhabited constructor of each datatype legal. `rankExists` builds such a rank from the
inhabitance of the block, which is `MutualADTWF.inhabited`. Its proof uses **no** topological
order.

`rankExists` removes one inhabitance *source* at a time, through
`hasSource_of_tySymInhab`. It gives each datatype the number of the step at which it removes
that datatype.

Therefore the rank is not more than the number of block datatypes. Each edge of the
graph of name references that the inhabited constructors make also gets a smaller rank. Two
datatypes can share one rank, because only the smaller rank on each edge is necessary. -/

section InhabRank

open Core Core.TypeSpec Lambda

/-- Each type constructor name that the argument types of a constructor refer to, at any
    position. This function is the form of `getTypeRefs` for a constructor. -/
def constrRefs (c : LConstr Unit) : List String :=
  c.args.flatMap (fun a => getTypeRefs a.2)

/-- The set of names `R` holds a *source*. A source is a datatype `src ∈ R` that has a
    constructor which refers to no name of `R`. Therefore, at the step that removes a name from
    `R` to build the rank, `src` can take the current number. -/
def HasSource (adts : @TypeFactory Unit) (R : List String) : Prop :=
  ∃ src ∈ R, ∃ d, adts.getType src = some d ∧
    ∃ c ∈ d.constrs, ∀ ref ∈ constrRefs c, ref ∉ R

/-- **A source exists, from inhabitance.** Take a set `R` of datatype names. Assume that each
    name of `R` resolves in `adts`, and that one `name ∈ R` obeys `TySymInhab adts`. Then `R`
    holds a source.

    The proof uses the recursor for the three relations `TyInhab`, `TySymInhab` and
    `ConstrInhab`. In the case `.datatype`, the constructor of `name` that makes it inhabited
    refers to no name of `R`, therefore `name` is the source. If that constructor refers to
    some `n' ∈ R`, then the derivation for `n'` gives the source, by the induction hypothesis.
    The proof needs no measure, because the recursion is on the derivation. -/
theorem hasSource_of_tySymInhab {adts : @TypeFactory Unit} {name : String}
    (h : TySymInhab adts name) :
    ∀ (R : List String), (∀ n ∈ R, adts.getType n ≠ none) → name ∈ R → HasSource adts R := by
  refine TySymInhab.rec
    (motive_1 := fun ty _ => ∀ (R : List String), (∀ n ∈ R, adts.getType n ≠ none) →
      (∃ ref ∈ getTypeRefs ty, ref ∈ R) → HasSource adts R)
    (motive_2 := fun name _ => ∀ (R : List String), (∀ n ∈ R, adts.getType n ≠ none) →
      name ∈ R → HasSource adts R)
    (motive_3 := fun c _ => ∀ (R : List String), (∀ n ∈ R, adts.getType n ≠ none) →
      (∃ ref ∈ constrRefs c, ref ∈ R) → HasSource adts R)
    ?ftvar ?bitvec ?tcons ?external ?datatype ?mk h
  case ftvar =>
    intro v R _ href
    obtain ⟨ref, href, _⟩ := href
    simp [getTypeRefs] at href
  case bitvec =>
    intro sz R _ href
    obtain ⟨ref, href, _⟩ := href
    simp [getTypeRefs] at href
  case tcons =>
    intro n args _ _ ihsym ihargs R hRgood href
    obtain ⟨ref, hrefmem, hrefR⟩ := href
    simp only [getTypeRefs, List.mem_cons, List.mem_flatMap] at hrefmem
    rcases hrefmem with rfl | ⟨a, ha, hrefa⟩
    · exact ihsym R hRgood hrefR
    · exact ihargs a ha R hRgood ⟨ref, hrefa, hrefR⟩
  case external =>
    intro n hnone R hRgood hnR
    exact absurd hnone (hRgood n hnR)
  case datatype =>
    intro n d c hget hmem _ ihc R hRgood hnR
    by_cases hcref : ∃ ref ∈ constrRefs c, ref ∈ R
    · exact ihc R hRgood hcref
    · refine ⟨n, hnR, d, hget, c, hmem, ?_⟩
      intro ref href hrefR
      exact hcref ⟨ref, href, hrefR⟩
  case mk =>
    intro c hargs ihargs R hRgood href
    obtain ⟨ref, hrefmem, hrefR⟩ := href
    simp only [constrRefs, List.mem_flatMap] at hrefmem
    obtain ⟨a, ha, hrefa⟩ := hrefmem
    exact ihargs a ha R hRgood ⟨ref, hrefa, hrefR⟩

/-- **A rank exists. This lemma is the kernel of the design, and it uses no order.** Take a set
    of names `R` whose members are different in pairs. Assume that each member resolves and obeys
    `TySymInhab`. Then a rank function is present, and each rank is less than `R.length`.

    Each member also has an inhabited constructor. Each reference of that constructor to a name
    of `R` has a lower rank.

    The proof is a well-founded recursion on `R.length`. It removes one source, and it gives
    that source the rank `0`. It then adds 1 to the rank of each other member.

    This lemma gives completeness a legal rank draw for each `MutualADTWF` block. The proof
    builds no topological order. -/
theorem rankExists (adts : @TypeFactory Unit) :
    ∀ (R : List String), R.Nodup → (∀ n ∈ R, adts.getType n ≠ none) →
      (∀ n ∈ R, TySymInhab adts n) →
      ∃ rank : String → Nat,
        (∀ n ∈ R, rank n < R.length) ∧
        (∀ n ∈ R, ∃ d, adts.getType n = some d ∧ ∃ c ∈ d.constrs,
          ∀ ref ∈ constrRefs c, ref ∈ R → rank ref < rank n) := by
  intro R
  induction hwf : R.length generalizing R with
  | zero =>
    intro _ _ _
    have hR : R = [] := List.length_eq_zero_iff.mp hwf
    subst hR
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ k ih =>
    intro hnodup hresolve hinhab
    have hRne : R ≠ [] := by intro h; rw [h] at hwf; simp at hwf
    obtain ⟨n0, hn0mem, _⟩ : ∃ n ∈ R, True := by
      cases R with
      | nil => exact absurd rfl hRne
      | cons a _ => exact ⟨a, List.mem_cons_self, trivial⟩
    obtain ⟨src, hsrcmem, dsrc, hsrcget, csrc, hcsrcmem, hcsrcavoid⟩ :=
      hasSource_of_tySymInhab (hinhab n0 hn0mem) R hresolve hn0mem
    have herase_len : (R.erase src).length = k := by
      rw [List.length_erase_of_mem hsrcmem, hwf]; omega
    have herase_nodup : (R.erase src).Nodup := hnodup.erase src
    have hsub : ∀ n ∈ R.erase src, n ∈ R := fun n hn => List.mem_of_mem_erase hn
    obtain ⟨rank', hrank'bound, hrank'wit⟩ :=
      ih (R.erase src) (by rw [herase_len])
        herase_nodup (fun n hn => hresolve n (hsub n hn)) (fun n hn => hinhab n (hsub n hn))
    refine ⟨fun n => if n = src then 0 else rank' n + 1, ?_, ?_⟩
    · -- The limit on each rank.
      intro n hnR
      simp only
      by_cases hn : n = src
      · rw [if_pos hn]; omega
      · rw [if_neg hn]
        have hne : n ∈ R.erase src := (List.mem_erase_of_ne hn).mpr hnR
        have hb := hrank'bound n hne
        omega
    · -- The property of the inhabited constructor.
      intro n hnR
      by_cases hn : n = src
      · subst hn
        refine ⟨dsrc, hsrcget, csrc, hcsrcmem, ?_⟩
        intro ref href hrefR
        exact absurd hrefR (hcsrcavoid ref href)
      · have hnerase : n ∈ R.erase src := (List.mem_erase_of_ne hn).mpr hnR
        obtain ⟨d, hget, c, hcmem, hcwit⟩ := hrank'wit n hnerase
        refine ⟨d, hget, c, hcmem, ?_⟩
        intro ref href hrefR
        simp only
        rw [if_neg hn]
        by_cases hrefsrc : ref = src
        · rw [if_pos hrefsrc]; omega
        · rw [if_neg hrefsrc]
          have hreferase : ref ∈ R.erase src := (List.mem_erase_of_ne hrefsrc).mpr hrefR
          have hedge := hcwit ref href hreferase
          omega

end InhabRank

/-! ## Completeness, and the exact sense in which it holds

Completeness holds against `MutualADTWF` plus premises that are all about the *context* and
the *names the generator uses*, and one residual side condition on the type itself:
`BitvecWidthOnly`. Read `genArgTy_complete_of_MutualADTWF`. Completeness against
`MutualADTWF` alone is false — read `not_complete_without_arity`. -/

section Completeness

/-! ### What `MutualADTWF` gives, and the one thing it does not

This file used to carry a hand-written `ArityOk` predicate: a recursion over the type
restating the whole arity discipline (base types nullary, applied constructors at their
declared arity, `arrow` binary) against the generator's vocabulary. Upstream's
`MutualADTWF.argsWellKinded` now states the arity discipline itself, and `defaultBaseTypes` /
`defaultTyCons` are *derived* from the very register `argsWellKinded` speaks about
(`Core.KnownTypes`), so the whole predicate is redundant and is gone. What replaces it:

* `ArgsWellKinded` — the `argsWellKinded` field, restated as a predicate on one type so the
  recursion can carry it. This is *not* a new assumption: `MutualADTWF` hands it out.
* `VocabOk` — the generator's vocabulary is exactly `C`'s arity register, split by arity.
  This is a fact about the *context*, not the type, and it is **proven** for the default
  vocabulary (`defaultVocabOk`), not assumed.
* `BitvecWidthOnly` — the one residual condition on the type, and the only hand-written one
  left.

### Why `bitvec` needs its own side condition

`Core.KnownTypes` registers `("bitvec", 1)`, so `argsWellKinded` accepts `bitvec τ` for a
*type* `τ` — and `LContext.addMutualBlock` really does accept such a block. But a bitvector
type is `LMonoTy.bitvec n` for a **width** `n : Nat`, not a type application: the argument
`bitvec` takes is a natural number, and `LMonoTy` has no way to spell one in an argument
position. `genBaseTy` therefore emits bitvectors through `pickBitvecWidth`, and `genArgTy`
never applies the name `bitvec` to a type. `BitvecWidthOnly` records exactly that reading —
"any `bitvec` here is a width, not an application" — and is what `defaultTyCons` excluding
`bitvec` is paid for with. `coreAppliedTyCons` keeps `bitvec`, so no *arity* fact is lost.

### Why `C` must have no stored datatypes

`argsWellKinded` is a three-way disjunction: a reference may be resolved by `C.knownTypes`,
by an *existing* datatype of `C`, or by the block. `genArgTy`'s vocabulary is
`baseTypes`/`tyCons`/`arrow`/`blockRefs` — it has no way to emit a reference to a datatype
already stored in `C`. `VocabOk.noStoredDatatypes` rules that middle disjunct out. It holds
for `coreContext` (whose `datatypes` is `#[]`), which is the context Core programs start
from; it does *not* hold part-way through the whole-program generator, and that is a genuine
limit of this completeness result rather than an artefact of how it is stated.

`ArityOk` used to hide this second gap inside its arity recursion, because requiring
`k ∈ baseTypes` / `(k, n) ∈ tyCons` silently excluded stored-datatype names too. Splitting it
out makes both gaps visible. -/

/-- **`MutualADTWF.argsWellKinded`, as a predicate on one type.** Every type-constructor
    reference in `ty` is applied at the arity its referent declares: a `C.knownTypes` arity,
    the `typeArgs` count of a datatype already stored in `C`, or the `typeArgs` count of a
    datatype declared in `block`.

    This is a restatement, not a new condition. `MutualADTWF.argsWellKinded` gives it for
    every constructor argument of the block — read `argsWellKinded_ty`. -/
def ArgsWellKinded (C : LContext Core.CoreLParams) (block : MutualDatatype Unit)
    (ty : LMonoTy) : Prop :=
  ∀ ref n, (ref, n) ∈ Lambda.getTypeConsArities ty →
    C.knownTypes[ref]? = some n ∨
    (∃ d' ∈ C.datatypes.allDatatypes, d'.name = ref ∧ d'.typeArgs.length = n) ∨
    (∃ d' ∈ block, d'.name = ref ∧ d'.typeArgs.length = n)

/-- `ArgsWellKinded` at the head of an application. -/
theorem ArgsWellKinded.head {C : LContext Core.CoreLParams} {block : MutualDatatype Unit}
    {k : String} {args : List LMonoTy} (h : ArgsWellKinded C block (.tcons k args)) :
    C.knownTypes[k]? = some args.length ∨
    (∃ d' ∈ C.datatypes.allDatatypes, d'.name = k ∧ d'.typeArgs.length = args.length) ∨
    (∃ d' ∈ block, d'.name = k ∧ d'.typeArgs.length = args.length) :=
  h k args.length (by simp [Lambda.getTypeConsArities])

/-- `ArgsWellKinded` passes to each argument of an application: `getTypeConsArities` of an
    application holds the arities of every argument. -/
theorem ArgsWellKinded.arg {C : LContext Core.CoreLParams} {block : MutualDatatype Unit}
    {k : String} {args : List LMonoTy} {a : LMonoTy}
    (h : ArgsWellKinded C block (.tcons k args)) (ha : a ∈ args) :
    ArgsWellKinded C block a := by
  intro ref n hmem
  refine h ref n ?_
  simp only [Lambda.getTypeConsArities, List.mem_cons]
  exact Or.inr (List.mem_flatMap.mpr ⟨a, ha, hmem⟩)

/-- `MutualADTWF.argsWellKinded`, packaged as `ArgsWellKinded` per argument type. -/
theorem argsWellKinded_ty {C : LContext Core.CoreLParams} {block : MutualDatatype Unit}
    (hwf : Core.TypeSpec.MutualADTWF C block) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ArgsWellKinded C block arg.2 :=
  fun d hd c hc arg harg ref n hmem => hwf.argsWellKinded d hd c hc arg harg ref n hmem

/-- **The one residual side condition on the type.** Every `bitvec` in `ty` is a *width*
    (`LMonoTy.bitvec n`, which carries a `Nat`), and not the name `bitvec` applied to a type.

    `Core.KnownTypes` registers `bitvec` at arity `1`, so `MutualADTWF` accepts `bitvec τ` for
    a type `τ`; but the argument `bitvec` takes is a natural-number width, which no `LMonoTy`
    argument position can hold. `genBaseTy` emits bitvectors as `LMonoTy.bitvec n` through
    `pickBitvecWidth`, and `genArgTy` never applies the *name* `bitvec`. Read the section
    prose above. -/
def BitvecWidthOnly : LMonoTy → Prop
  | .bitvec _ => True
  | .ftvar _ => True
  | .tcons k args => k ≠ "bitvec" ∧ ∀ a ∈ args, BitvecWidthOnly a

/-- **The generator's vocabulary is exactly `C`'s arity register, split by arity.** This is a
    fact about the context and the generator's parameters — not about any type — and it is
    *proven* for the default vocabulary (`defaultVocabOk`), because `defaultBaseTypes` and
    `defaultTyCons` are derived from `Core.KnownTypes`.

    * `base` / `tyCon`: every arity `C` registers is one the generator can draw, `arrow`
      (which `genArgTy` has a dedicated branch for) and `bitvec` (whose argument is a width)
      excepted.
    * `arrow`: `C` registers `arrow` binary, so `argsWellKinded` pins an arrow to 2 arguments.
    * `noStoredDatatypes`: `C` stores no datatype, so `argsWellKinded`'s middle disjunct is
      empty. `genArgTy` cannot refer to a stored datatype. -/
structure VocabOk (C : LContext Core.CoreLParams) (baseTypes : List String)
    (tyCons : List KnownTyCon) : Prop where
  base : ∀ k, C.knownTypes[k]? = some 0 → k ∈ baseTypes
  tyCon : ∀ k n, C.knownTypes[k]? = some n → n ≠ 0 → k ≠ "arrow" → k ≠ "bitvec" →
    (k, n) ∈ tyCons
  arrow : C.knownTypes["arrow"]? = some 2
  noStoredDatatypes : C.datatypes.allDatatypes = []

/-- **The default vocabulary satisfies `VocabOk` in `coreContext`.** `base` and `tyCon` hold
    by construction — the lists *are* `Core.KnownTypes` split by arity, read back by
    `mem_defaultBaseTypes_iff` / `mem_defaultTyCons_iff`. Only `arrow`'s arity needs a lookup
    (`native_decide`), because `genArgTy` hardcodes that name. -/
theorem defaultVocabOk : VocabOk coreContext defaultBaseTypes defaultTyCons where
  base := fun _ h => mem_defaultBaseTypes_iff.mpr h
  tyCon := fun k n h hn harrow hbv =>
    mem_defaultTyCons_iff.mpr ⟨mem_coreAppliedTyCons_iff.mpr ⟨h, hn, harrow⟩, hbv⟩
  arrow := by show Core.KnownTypes["arrow"]? = some 2; native_decide
  noStoredDatatypes := by simp [coreContext, TypeFactory.allDatatypes]

/-- The head of a non-block application is registered in `C.knownTypes` at its argument
    count: `VocabOk.noStoredDatatypes` kills `argsWellKinded`'s stored-datatype disjunct and
    `hself` kills its block disjunct. -/
theorem ArgsWellKinded.knownArity {C : LContext Core.CoreLParams} {block : MutualDatatype Unit}
    {baseTypes : List String} {tyCons : List KnownTyCon} {k : String} {args : List LMonoTy}
    (hv : VocabOk C baseTypes tyCons) (h : ArgsWellKinded C block (.tcons k args))
    (hself : k ∉ block.map (·.name)) : C.knownTypes[k]? = some args.length := by
  rcases h.head with hk | ⟨d', hd', hname, _⟩ | ⟨d', hd', hname, _⟩
  · exact hk
  · exact absurd hd' (by rw [hv.noStoredDatatypes]; simp)
  · exact absurd (hname ▸ List.mem_map.mpr ⟨d', hd', rfl⟩) hself

/-- **The support of `genArgTy` grows with the size.** The generator can make a type at the
    size `size`. Then it can also make that type at each larger size. The three kinds from
    `genLeafTy` are present at each size, and the size `size / 2` for an arrow and for an
    application only grows.

    Therefore the proof of completeness can take one size that is large enough for each
    subterm of a type. Therefore the statement can give the size as an existential value. The
    proof is a strong induction on `size` through `genArgTy_mem_iff`. -/
theorem genArgTy_mono {baseTypes : List String} {tyCons : List KnownTyCon}
    {blockRefs : List BlockRef} {tyParams : List TyIdentifier} :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) →
      ∀ {size' : Nat}, size ≤ size' →
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size') := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro rca ty h size' hle
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp h with
      hleaf | ⟨hsz', t1, t2, rfl, h1, h2⟩ | ⟨hsz, k, args, rfl, hkc, hall⟩
    · exact (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl hleaf)
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      refine (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inl ⟨by omega, t1, t2, rfl, ?_, ?_⟩))
      · exact ih _ hhalf h1 (by omega)
      · exact ih _ hhalf h2 (by omega)
    · have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega)
      refine (genArgTy_mem_iff _ _ _ _ _ _ _).mpr
        (Or.inr (Or.inr ⟨by omega, k, args, rfl, hkc, fun a ha => ?_⟩))
      exact ih _ hhalf (hall a ha) (by omega)

/-- **One limit for each member of a finite list.** Assume that each member `a` of a list `l`
    obeys `P a s` for some `s`. Assume also that `P a` holds at each larger value of `s`. Then
    one value `N` is present with `P a N` for each `a ∈ l`.

    That value is the maximum of the values for the members. `P a` holds at each larger value,
    therefore it holds at that maximum. This lemma collects the sizes at which the generator
    can make each argument into one size that the generator can draw. -/
theorem exists_uniform_bound {α : Type} (l : List α) (P : α → Nat → Prop)
    (hmono : ∀ a ∈ l, ∀ (s s' : Nat), s ≤ s' → P a s → P a s')
    (h : ∀ a ∈ l, ∃ s, P a s) : ∃ N, ∀ a ∈ l, P a N := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons hd tl ih =>
    obtain ⟨sHd, hHd⟩ := h hd List.mem_cons_self
    obtain ⟨sTl, hTl⟩ := ih (fun a ha => hmono a (List.mem_cons_of_mem _ ha))
      (fun a ha => h a (List.mem_cons_of_mem _ ha))
    refine ⟨max sHd sTl, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hmono a List.mem_cons_self _ _ (Nat.le_max_left _ _) hHd
    · exact hmono a (List.mem_cons_of_mem _ ha) _ _ (Nat.le_max_right _ _) (hTl a ha)

/-- The form of the facts about each argument with one shared size. Assume that the generator
    can make each member of `args` at some size, with the flag `false`. Then it can make all of
    them at one size. `genArgTy_mono` gives this result. -/
theorem genArgTy_common_size {baseTypes : List String} {tyCons : List KnownTyCon}
    {blockRefs : List BlockRef} {tyParams : List TyIdentifier}
    {args : LMonoTys}
    (h : ∀ a ∈ args, ∃ size, a ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes
          tyCons blockRefs tyParams false size)) :
    ∃ S, ∀ a ∈ args, a ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons
      blockRefs tyParams false S) := by
  induction args with
  | nil => exact ⟨0, by simp⟩
  | cons hd tl ih =>
    obtain ⟨sHd, hHd⟩ := h hd (by simp)
    obtain ⟨sTl, hTl⟩ := ih (fun a ha => h a (by simp [ha]))
    refine ⟨max sHd sTl, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact genArgTy_mono _ hHd (Nat.le_max_left _ _)
    · exact genArgTy_mono _ (hTl a ha) (Nat.le_max_right _ _)

/-- **Completeness of `genArgTy` against the specification.** Take a constructor argument type
    that obeys four conditions. It is `ConstrArgWF block`. Each of its free type variables is
    declared, which `MutualADTWF.argVarsScoped` gives. Its type-constructor references are
    applied at their declared arities, which `MutualADTWF.argsWellKinded` gives
    (`ArgsWellKinded`). And every `bitvec` in it is a width rather than an application, which
    is `BitvecWidthOnly`.

    Then the generator can make that type at some size. This result also needs the uniform
    reference of each block datatype to be a member of `blockRefs`, which is `hcover`.

    The size is an existential value. The premise about absence gives the value of the flag.
    `ConstrArgWF` gives that premise at each recursive position.

    The proof is a recursion on the structure of `ty`. It builds membership in the support through
    `genArgTy_mem_iff` and `genLeafTy_mem_iff`. It adds no relation of its own.

    Two facts work together here. `ConstrArgWF` forbids a block name in exactly the positions
    that the generator draws at the flag `false`. `ConstrArgWF` also fixes each occurrence with
    a block name at the head to the uniform form `n (n's typeArgs)`, through
    `constrArgWF_self_uniform`. `hcover` puts that form in `blockRefs`. Therefore the arity
    premise says nothing about such an occurrence. -/
theorem genArgTy_complete_of_wf {baseTypes : List String} {tyCons : List KnownTyCon}
    {C : LContext Core.CoreLParams}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hvocab : VocabOk C baseTypes tyCons)
    (hcover : ∀ d ∈ block, (d.name, d.typeArgs.map .ftvar) ∈ blockRefs) :
    ∀ (ty : LMonoTy),
      ConstrArgWF block ty →
      (∀ v ∈ LMonoTy.freeVars ty, v ∈ tyParams) →
      ArgsWellKinded C block ty →
      BitvecWidthOnly ty →
      ∀ (rca : Bool), (rca = false → BlockAbsent block ty) →
      ∃ size, ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) := by
  intro ty
  induction ty using LMonoTy.induct with
  | ftvar v =>
    intro _ hvars _ _ rca _
    -- `argVarsScoped` gives `v ∈ tyParams`. That type is the rigid type variable, at the
    -- size 0.
    have hmemv : v ∈ tyParams := hvars v (by simp [LMonoTy.freeVars])
    refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
    exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨v, hmemv, rfl⟩)))
  | bitvec n =>
    -- A bitvector is a *width*, therefore `genBaseTy` draws it through `pickBitvecWidth`.
    intro _ _ _ _ rca _
    refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
    exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inl ⟨n, rfl⟩)
  | tcons k args ih =>
    intro hwf hvars hwk hbv rca habs
    by_cases hself : k ∈ block.map (·.name)
    · -- An occurrence with a block name at the head. `ConstrArgWF` forces it to be uniform,
      -- therefore `args = d.typeArgs.map .ftvar` for the block datatype `d` with the name `k`.
      -- `constrArgWF_self_uniform` gives that fact. The type is then the recursive occurrence,
      -- and that form forces `rca = true`. At the flag `false`, the name `k` would appear at
      -- the head, and that result contradicts the premise about absence. `hcover` puts the
      -- reference in `blockRefs`.
      obtain ⟨d, hd, hdname⟩ := List.mem_map.mp hself
      subst hdname
      have hargs : args = d.typeArgs.map .ftvar :=
        constrArgWF_self_uniform hd (fun d' hd' => hn.block_ne_arrow _ (List.mem_map.mpr ⟨d', hd', rfl⟩)) hwf
      subst hargs
      have hrca : rca = true := by
        cases rca with
        | true => rfl
        | false => exact absurd (habs rfl d hd) (fun hab => hab (.head _))
      subst hrca
      refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
      exact (genLeafTy_mem_iff _ _ _ _ _).mpr
        (Or.inr (Or.inr (Or.inr ⟨rfl, (d.name, d.typeArgs.map .ftvar), hcover d hd, rfl⟩)))
    · -- The head is not a block name, therefore `argsWellKinded` resolves it against
      -- `C.knownTypes`: `VocabOk.noStoredDatatypes` kills the stored-datatype disjunct and
      -- `hself` kills the block disjunct.
      have hk : C.knownTypes[k]? = some args.length := hwk.knownArity hvocab hself
      unfold BitvecWidthOnly at hbv
      obtain ⟨hkbv, hbvargs⟩ := hbv
      by_cases harrow : k = "arrow"
      · -- An arrow `t1 → t2`. `VocabOk.arrow` registers `arrow` binary, therefore
        -- `argsWellKinded` pins the argument count to 2.
        subst harrow
        have hlen : args.length = 2 := by
          rw [hvocab.arrow] at hk
          exact (by simpa using hk : (2 : Nat) = args.length).symm
        obtain ⟨t1, t2, rfl⟩ : ∃ t1 t2, args = [t1, t2] := by
          match args, hlen with
          | [t1, t2], _ => exact ⟨t1, t2, rfl⟩
        · have ha1 : ArgsWellKinded C block t1 := hwk.arg (by simp)
          have ha2 : ArgsWellKinded C block t2 := hwk.arg (by simp)
          have hb1 : BitvecWidthOnly t1 := hbvargs t1 (by simp)
          have hb2 : BitvecWidthOnly t2 := hbvargs t2 (by simp)
          have harr : LMonoTy.tcons "arrow" [t1, t2] = LMonoTy.arrow t1 t2 := rfl
          rw [harr] at hwf
          obtain ⟨hdom_abs, hwf1, hwf2⟩ := constrArgWF_arrow
            (fun d' hd' => hn.block_ne_arrow _ (List.mem_map.mpr ⟨d', hd', rfl⟩)) hwf
          -- The free variables of `t1` / `t2` are among those of the arrow.
          have hvars1 : ∀ v ∈ LMonoTy.freeVars t1, v ∈ tyParams := fun v hv =>
            hvars v (by rw [harr]; simp only [LMonoTy.freeVars, LMonoTys.freeVars,
              List.append_nil, List.mem_append]; exact Or.inl hv)
          have hvars2 : ∀ v ∈ LMonoTy.freeVars t2, v ∈ tyParams := fun v hv =>
            hvars v (by rw [harr]; simp only [LMonoTy.freeVars, LMonoTys.freeVars,
              List.append_nil, List.mem_append]; exact Or.inr hv)
          obtain ⟨s1, h1⟩ := ih t1 (by simp) hwf1 hvars1 ha1 hb1 false (fun _ => hdom_abs)
          obtain ⟨s2, h2⟩ := ih t2 (by simp) hwf2 hvars2 ha2 hb2 rca
            (fun hr => by
              subst hr
              intro d' hd'
              have hab := habs rfl d' hd'
              rw [harr] at hab
              exact fun hap => hab (.arg _ _ _ (by simp) hap))
          refine ⟨2 * (max s1 s2) + 1,
            (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inl ⟨by omega, t1, t2, rfl,
              genArgTy_mono _ h1 (by omega), genArgTy_mono _ h2 (by omega)⟩))⟩
      · by_cases hnil : args = []
        · -- A base leaf `k` with no arguments. `C` registers it at arity 0, and `VocabOk.base`
          -- turns that into `k ∈ baseTypes` — the derivation of `defaultBaseTypes` from
          -- `Core.KnownTypes` is what makes this step available.
          subst hnil
          refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
          exact (genLeafTy_mem_iff _ _ _ _ _).mpr
            (Or.inr (Or.inl ⟨k, hvocab.base k (by simpa using hk), rfl⟩))
        · -- An applied known type constructor. `C` registers it at its argument count, and
          -- `VocabOk.tyCon` turns that into `(k, args.length) ∈ tyCons`; `k ≠ "bitvec"` comes
          -- from `BitvecWidthOnly`, which is the one condition `MutualADTWF` does not give.
          have hkc : (k, args.length) ∈ tyCons :=
            hvocab.tyCon k args.length hk
              (fun h0 => hnil (List.eq_nil_of_length_eq_zero h0)) harrow hkbv
          have hall : ∀ a ∈ args, ArgsWellKinded C block a := fun a ha => hwk.arg ha
          -- Every block name is absent from every argument (the `headOther` case of
          -- `NotNested`).
          have hargs_abs : ∀ a ∈ args, BlockAbsent block a := by
            intro a ha
            obtain ⟨hnn, _⟩ := hwf
            cases hnn with
            | arrow _ _ _ _ => exact absurd rfl harrow
            | headBlock _ _ hmem => exact absurd hmem hself
            | headOther _ _ _ _ habsent _ =>
              intro d' hd'; exact habsent d' hd' a ha
          obtain ⟨S, hS⟩ := genArgTy_common_size (args := args) (fun a ha =>
            ih a ha (absent_constrArgWF (hargs_abs a ha)) (fun v hv =>
              hvars v (by rw [freeVars_tcons_eq_flatMap]; exact List.mem_flatMap.mpr ⟨a, ha, hv⟩))
              (hall a ha) (hbvargs a ha) false (fun _ => hargs_abs a ha))
          refine ⟨2 * S + 1,
            (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inr ⟨by omega, k, args, rfl,
              hkc, fun a ha => genArgTy_mono _ (hS a ha) (by omega)⟩))⟩

open Core Core.TypeSpec in
/-- **Completeness for one type, over a smaller set of references.** This theorem is the same
    as `genArgTy_complete_of_wf`, but its hypothesis about coverage has a condition. Take a block
    datatype whose name appears in `ty`, which `TyNameAppears` gives. Only for such a datatype
    must the uniform reference be a member of `blockRefs`.

    Therefore the design with ranks can reach the inhabited constructor. The argument types of
    that constructor refer only to block datatypes of a lower rank, and the set
    `visibleRefs (lowerRankHeaders …)` holds exactly those datatypes.

    The proof threads the coverage with its condition through the recursion on the structure. A
    name in a subterm also appears in the whole type, which `TyNameAppears.arg` gives. Therefore
    the coverage for each subterm follows. -/
theorem genArgTy_complete_of_wf_partial {baseTypes : List String} {tyCons : List KnownTyCon}
    {C : LContext Core.CoreLParams}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hvocab : VocabOk C baseTypes tyCons) :
    ∀ (ty : LMonoTy),
      (∀ d ∈ block, TyNameAppears d.name ty → (d.name, d.typeArgs.map .ftvar) ∈ blockRefs) →
      ConstrArgWF block ty →
      (∀ v ∈ LMonoTy.freeVars ty, v ∈ tyParams) →
      ArgsWellKinded C block ty →
      BitvecWidthOnly ty →
      ∀ (rca : Bool), (rca = false → BlockAbsent block ty) →
      ∃ size, ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) := by
  intro ty
  induction ty using LMonoTy.induct with
  | ftvar v =>
    intro _ _ hvars _ _ rca _
    have hmemv : v ∈ tyParams := hvars v (by simp [LMonoTy.freeVars])
    refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
    exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨v, hmemv, rfl⟩)))
  | bitvec n =>
    intro _ _ _ _ _ rca _
    refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
    exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inl ⟨n, rfl⟩)
  | tcons k args ih =>
    intro hcover hwf hvars hwk hbv rca habs
    by_cases hself : k ∈ block.map (·.name)
    · obtain ⟨d, hd, hdname⟩ := List.mem_map.mp hself
      subst hdname
      have hargs : args = d.typeArgs.map .ftvar :=
        constrArgWF_self_uniform hd (fun d' hd' => hn.block_ne_arrow _ (List.mem_map.mpr ⟨d', hd', rfl⟩)) hwf
      subst hargs
      have hrca : rca = true := by
        cases rca with
        | true => rfl
        | false => exact absurd (habs rfl d hd) (fun hab => hab (.head _))
      subst hrca
      refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
      -- `d.name` appears at the head, therefore the coverage with its condition applies.
      exact (genLeafTy_mem_iff _ _ _ _ _).mpr
        (Or.inr (Or.inr (Or.inr ⟨rfl, (d.name, d.typeArgs.map .ftvar),
          hcover d hd (.head _), rfl⟩)))
    · -- Not a block name, therefore `argsWellKinded` resolves the head in `C.knownTypes`.
      have hk : C.knownTypes[k]? = some args.length := hwk.knownArity hvocab hself
      unfold BitvecWidthOnly at hbv
      obtain ⟨hkbv, hbvargs⟩ := hbv
      by_cases harrow : k = "arrow"
      · subst harrow
        have hlen : args.length = 2 := by
          rw [hvocab.arrow] at hk
          exact (by simpa using hk : (2 : Nat) = args.length).symm
        obtain ⟨t1, t2, rfl⟩ : ∃ t1 t2, args = [t1, t2] := by
          match args, hlen with
          | [t1, t2], _ => exact ⟨t1, t2, rfl⟩
        · have ha1 : ArgsWellKinded C block t1 := hwk.arg (by simp)
          have ha2 : ArgsWellKinded C block t2 := hwk.arg (by simp)
          have hb1 : BitvecWidthOnly t1 := hbvargs t1 (by simp)
          have hb2 : BitvecWidthOnly t2 := hbvargs t2 (by simp)
          have harr : LMonoTy.tcons "arrow" [t1, t2] = LMonoTy.arrow t1 t2 := rfl
          rw [harr] at hwf
          obtain ⟨hdom_abs, hwf1, hwf2⟩ := constrArgWF_arrow
            (fun d' hd' => hn.block_ne_arrow _ (List.mem_map.mpr ⟨d', hd', rfl⟩)) hwf
          have hvars1 : ∀ v ∈ LMonoTy.freeVars t1, v ∈ tyParams := fun v hv =>
            hvars v (by rw [harr]; simp only [LMonoTy.freeVars, LMonoTys.freeVars,
              List.append_nil, List.mem_append]; exact Or.inl hv)
          have hvars2 : ∀ v ∈ LMonoTy.freeVars t2, v ∈ tyParams := fun v hv =>
            hvars v (by rw [harr]; simp only [LMonoTy.freeVars, LMonoTys.freeVars,
              List.append_nil, List.mem_append]; exact Or.inr hv)
          -- Sub-coverage: a name in `t1`/`t2` appears in the arrow (`TyNameAppears.arg`).
          have hcover1 : ∀ d ∈ block, TyNameAppears d.name t1 →
              (d.name, d.typeArgs.map .ftvar) ∈ blockRefs :=
            fun d hd hap => hcover d hd (.arg _ _ _ (by simp) hap)
          have hcover2 : ∀ d ∈ block, TyNameAppears d.name t2 →
              (d.name, d.typeArgs.map .ftvar) ∈ blockRefs :=
            fun d hd hap => hcover d hd (.arg _ _ _ (by simp) hap)
          obtain ⟨s1, h1⟩ := ih t1 (by simp) hcover1 hwf1 hvars1 ha1 hb1 false
            (fun _ => hdom_abs)
          obtain ⟨s2, h2⟩ := ih t2 (by simp) hcover2 hwf2 hvars2 ha2 hb2 rca
            (fun hr => by
              subst hr
              intro d' hd'
              have hab := habs rfl d' hd'
              rw [harr] at hab
              exact fun hap => hab (.arg _ _ _ (by simp) hap))
          refine ⟨2 * (max s1 s2) + 1,
            (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inl ⟨by omega, t1, t2, rfl,
              genArgTy_mono _ h1 (by omega), genArgTy_mono _ h2 (by omega)⟩))⟩
      · by_cases hnil : args = []
        · subst hnil
          refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
          exact (genLeafTy_mem_iff _ _ _ _ _).mpr
            (Or.inr (Or.inl ⟨k, hvocab.base k (by simpa using hk), rfl⟩))
        · have hkc : (k, args.length) ∈ tyCons :=
            hvocab.tyCon k args.length hk
              (fun h0 => hnil (List.eq_nil_of_length_eq_zero h0)) harrow hkbv
          have hall : ∀ a ∈ args, ArgsWellKinded C block a := fun a ha => hwk.arg ha
          have hargs_abs : ∀ a ∈ args, BlockAbsent block a := by
            intro a ha
            obtain ⟨hnn, _⟩ := hwf
            cases hnn with
            | arrow _ _ _ _ => exact absurd rfl harrow
            | headBlock _ _ hmem => exact absurd hmem hself
            | headOther _ _ _ _ habsent _ =>
              intro d' hd'; exact habsent d' hd' a ha
          -- Each argument is block-absent, so its conditional coverage is vacuous.
          obtain ⟨S, hS⟩ := genArgTy_common_size (args := args) (fun a ha =>
            ih a ha (fun d hd hap => absurd hap (hargs_abs a ha d hd))
              (absent_constrArgWF (hargs_abs a ha)) (fun v hv =>
              hvars v (by rw [freeVars_tcons_eq_flatMap]; exact List.mem_flatMap.mpr ⟨a, ha, hv⟩))
              (hall a ha) (hbvargs a ha) false (fun _ => hargs_abs a ha))
          refine ⟨2 * S + 1,
            (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inr ⟨by omega, k, args, rfl,
              hkc, fun a ha => genArgTy_mono _ (hS a ha) (by omega)⟩))⟩

/-- **Completeness for one type, from the fields of `MutualADTWF`.** Take a constructor
    argument type that obeys four conditions. It is `ConstrArgWF block`, which the field
    `argsWF` gives. Each of its free variables is declared, which the field `argVarsScoped`
    gives. Its type-constructor references are applied at their declared arities, which the
    field `argsWellKinded` gives. And every `bitvec` in it is a width and not an application,
    which is `BitvecWidthOnly` — the one condition `MutualADTWF` does not give.

    Then `genArgTy` draws that type at some size, with `rca := true`, which lets it emit a
    recursive occurrence. This result also needs `blockRefs` to hold the references of the
    block, which is `hcover`, and the vocabulary to match `C`, which is `hvocab`.

    The value `rca := true` discharges the premise about the flag with no content. Therefore
    this theorem needs no separate hypothesis about absence. -/
theorem genArgTy_complete_of_arity {baseTypes : List String} {tyCons : List KnownTyCon}
    {C : LContext Core.CoreLParams}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier} {ty : LMonoTy}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hvocab : VocabOk C baseTypes tyCons)
    (hcover : ∀ d ∈ block, (d.name, d.typeArgs.map .ftvar) ∈ blockRefs)
    (hwf : ConstrArgWF block ty)
    (hvars : ∀ v ∈ LMonoTy.freeVars ty, v ∈ tyParams)
    (hwk : ArgsWellKinded C block ty)
    (hbv : BitvecWidthOnly ty) :
    ∃ size, ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
      tyParams true size) :=
  genArgTy_complete_of_wf hn hvocab hcover ty hwf hvars hwk hbv true (by simp)

open Core Core.TypeSpec in
/-- **Completeness against `MutualADTWF`.** Take a block that is well-formed, which is
    `MutualADTWF C block`. Then `genArgTy` can make each constructor argument type of that
    block, at some size.

    Three hypotheses are more than `MutualADTWF`, and **none of them is an arity condition**.
    The generator's vocabulary is derived from `Core.KnownTypes`, so the field `argsWellKinded`
    now discharges the whole arity discipline by itself; the hand-written `ArityOk` predicate
    this theorem used to carry is gone. Read `docs/mutualadtwf-arity-gap.md`.

    * `hbv` is the one residual condition on the type: every `bitvec` in it is a *width* and
      not the name `bitvec` applied to a type. `Core.KnownTypes` registers `bitvec` at arity
      `1`, so `MutualADTWF` accepts `bitvec τ`, but no `LMonoTy` argument position can hold a
      natural-number width. Read `BitvecWidthOnly`.
    * `hvocab` and `hn`/`hcover` are about the *context* and the *names the generator uses*,
      not about any type. `hvocab` says the vocabulary is `C`'s arity register split by arity
      and that `C` stores no datatype (`genArgTy` cannot refer to one); `defaultVocabOk`
      proves it for the default vocabulary in `coreContext`. `hcover` says the generator's
      set of references holds the block. -/
theorem genArgTy_complete_of_MutualADTWF {baseTypes : List String}
    {tyCons : List KnownTyCon} {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {blockRefs : List BlockRef}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hvocab : VocabOk C baseTypes tyCons)
    (hcover : ∀ d ∈ block, (d.name, d.typeArgs.map .ftvar) ∈ blockRefs)
    (hwf : MutualADTWF C block)
    (hbv : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, BitvecWidthOnly arg.2) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∃ size, arg.2 ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs d.typeArgs true size) := by
  intro d hd c hc arg harg
  refine genArgTy_complete_of_arity hn hvocab hcover
    (hwf.argsWF d hd c hc arg harg)
    (hwf.argVarsScoped d hd c hc arg harg)
    (argsWellKinded_ty hwf d hd c hc arg harg)
    (hbv d hd c hc arg harg)

/-- One example of completeness. Take a datatype `MyList a`, which is like a list. The generator
    can make the argument type `a → MyList a` at the size 1. That type holds a self-reference in
    its codomain and a type parameter in its domain.

    This shape is the important one. It shows that the generator makes true recursive types that
    are strictly positive, and not only the three kinds from `genLeafTy`.

    The proof builds the result through `genArgTy_mem_iff` and `genLeafTy_mem_iff`. The flag
    `false` for the domain is necessary, because the case for an arrow makes the domain at that
    flag. Therefore the generator makes the rigid type variable `a` there. The set of references
    holds the one block datatype `MyList a`. -/
example : (LMonoTy.arrow (.ftvar "a") (.tcons "MyList" [.ftvar "a"])) ∈
    SetGen.support (genArgTy (G := SetGen.Set) defaultBaseTypes defaultTyCons
      [("MyList", [.ftvar "a"])] ["a"] true 1) := by
  refine (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inl
    ⟨by omega, _, _, rfl, ?_, ?_⟩))
  · -- The domain, which is the rigid type variable `a`.
    exact (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl
      ((genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨"a", by simp, rfl⟩)))))
  · -- The codomain, which is the uniform recursive occurrence `MyList a`. The generator makes
    -- it at the flag `true`.
    exact (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl
      ((genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, ("MyList", [.ftvar "a"]), by simp, rfl⟩)))))

/-- **The `Sequence a a` gap is closed.** `Sequence` applied to 2 arguments has the wrong
    kind, and this used to be the standard counterexample to completeness against
    `MutualADTWF` alone: `refsKnown` only checked that `"Sequence"` resolves, never the
    argument count. Upstream's `argsWellKinded` now checks the count, so `MutualADTWF` itself
    rejects this type and the hand-written arity side condition is no longer needed. This
    `example` records that fact. -/
example (d : LDatatype Unit) (a : TyIdentifier) (hd_ne : d.name ≠ "Sequence") :
    ¬ ArgsWellKinded coreContext [d] (.tcons "Sequence" [.ftvar a, .ftvar a]) := by
  intro h
  have h1 : coreContext.knownTypes["Sequence"]? = some 1 := by
    show Core.KnownTypes["Sequence"]? = some 1; native_decide
  rcases h.head with hk | ⟨d', hd', _⟩ | ⟨d', hd', hname, _⟩
  · -- `argsWellKinded` would need `Sequence` registered at arity 2; it is registered at 1.
    rw [h1] at hk; simp at hk
  · -- `coreContext` stores no datatype.
    exact absurd hd' (by simp [coreContext, TypeFactory.allDatatypes])
  · -- The only remaining escape is the block itself declaring a datatype named `Sequence`.
    simp only [List.mem_singleton] at hd'; subst hd'; exact hd_ne hname

/-- **The reason that completeness needs `BitvecWidthOnly`. This is the one gap about the type
    that stays.** Take the type `bitvec a`, which applies the *name* `bitvec` to a type.

    `Core.KnownTypes` registers `("bitvec", 1)`, so every field of `MutualADTWF` accepts this
    type: `refsKnown` resolves the name, `argsWellKinded` sees one argument at arity `1`, and
    the one free variable `a` is declared. `LContext.addMutualBlock` accepts such a block too.

    But no `genArgTy` can make it. A bitvector type is `LMonoTy.bitvec n` for a *width*
    `n : Nat`, and no `LMonoTy` argument position can hold a natural number, so the arity `1`
    that `Core.KnownTypes` records is not an arity over *types* at all. `genBaseTy` therefore
    emits bitvectors through `pickBitvecWidth`, `defaultTyCons` excludes `bitvec`, and the
    generator never applies the name.

    `BitvecWidthOnly` closes exactly this gap, and nothing more:

    * `Sequence a a` — the old counterexample — is now excluded by `MutualADTWF` itself, since
      `argsWellKinded` checks the argument count. Read the `example` above.
    * `bitvec 7` was the standard example before issue #38, when `bitvecWidths` was a fixed
      list. The widths now have no limit, so the generator makes every bitvector.
    * A type with an undeclared free variable is excluded by `argVarsScoped`.

    One further gap is *not* about the type: `argsWellKinded` also admits references to
    datatypes already stored in `C`, which the generator cannot emit. `VocabOk.noStoredDatatypes`
    states that, and it holds for `coreContext`. Read `docs/mutualadtwf-arity-gap.md`. -/
theorem not_complete_without_bitvecWidthOnly (d : LDatatype Unit)
    (a : TyIdentifier) (hd_ne : d.name ≠ "bitvec") (blockRefs : List BlockRef)
    (hbr : ∀ br ∈ blockRefs, br.1 = d.name) (rca : Bool) (size : Nat) :
    -- The type is `ConstrArgWF`, its variables are in scope for each `tyParams` that holds
    -- `a`, and it is well-kinded. Therefore the content of `MutualADTWF` for one type holds.
    ConstrArgWF [d] (.tcons "bitvec" [.ftvar a]) ∧
    (∀ v ∈ LMonoTy.freeVars (.tcons "bitvec" [.ftvar a]), v = a) ∧
    ArgsWellKinded coreContext [d] (.tcons "bitvec" [.ftvar a]) ∧
    -- But the type breaks the side condition about the width.
    ¬ BitvecWidthOnly (.tcons "bitvec" [.ftvar a]) ∧
    -- The generator also cannot make it at any flag and at any size. This result holds for
    -- each set of references whose names are `d.name`, such as the set that
    -- `genMutuallyRecursiveDatatypes` gives for `[d]`.
    (.tcons "bitvec" [.ftvar a]) ∉ SetGen.support
      (genArgTy (G := SetGen.Set) defaultBaseTypes defaultTyCons blockRefs
        d.typeArgs rca size) := by
  -- `d.name` is absent from the type. It is not the head, because `d.name ≠ "bitvec"`, and
  -- it is not in a type variable.
  have habsent : BlockAbsent [d] (.tcons "bitvec" [.ftvar a]) := by
    intro d' hd'
    simp only [List.mem_singleton] at hd'; subst hd'
    intro hap
    generalize hty : LMonoTy.tcons "bitvec" [LMonoTy.ftvar a] = t at hap
    cases hap with
    | head _ => injection hty with hn _; exact hd_ne hn.symm
    | arg _ _ t ht hat =>
      injection hty with _ hargs; subst hargs
      rcases List.mem_cons.mp ht with rfl | ht
      · cases hat
      · cases ht
  refine ⟨absent_constrArgWF habsent, ?_, ?_, ?_, ?_⟩
  · -- The free variables of the type are exactly `a`.
    intro v hv
    simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil,
               List.mem_singleton] at hv
    exact hv
  · -- The type *is* well-kinded: `Core.KnownTypes` registers `bitvec` at arity 1.
    intro ref n hmem
    simp only [Lambda.getTypeConsArities, List.length_cons, List.length_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton,
      Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    refine Or.inl ?_
    show Core.KnownTypes["bitvec"]? = some 1
    native_decide
  · -- `BitvecWidthOnly` fails immediately: its `tcons` case needs `k ≠ "bitvec"`.
    unfold BitvecWidthOnly
    exact fun h => h.1 rfl
  · -- The generator cannot make the type, because the name `bitvec` matches no branch.
    intro hmem
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp hmem with
      hleaf | ⟨_, _, _, hcon, _⟩ | ⟨_, k, args, hcon, hkc, _⟩
    · -- The type is not one of the three kinds from `genLeafTy`. A `.tcons` with 1 argument
      -- is not an `LMonoTy.bitvec`, and it is not a base type with no argument, and it is not
      -- a rigid type variable. It is also not a block occurrence, because the head of such an
      -- occurrence is `d.name`, and `"bitvec" ≠ d.name`.
      rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨_, hcon⟩ | ⟨_, _, hcon⟩ | ⟨_, _, hcon⟩ | ⟨_, br, hbrmem, hcon⟩
      · exact absurd hcon (by simp)
      · exact absurd hcon (by simp)
      · exact absurd hcon (by simp)
      · rw [hbr br hbrmem] at hcon
        exact hd_ne (by injection hcon with h _; exact h.symm)
    · -- The type is not an arrow, because `"bitvec" ≠ "arrow"`.
      exact absurd hcon (by simp [LMonoTy.arrow])
    · -- The type is an application. That case needs `("bitvec", 1) ∈ defaultTyCons`, and
      -- `defaultTyCons` filters `bitvec` out — by construction, not by `decide`.
      injection hcon with hk hargs
      subst hk hargs
      simp only [List.length_cons, List.length_nil] at hkc
      exact (mem_defaultTyCons_iff.mp hkc).2 rfl

/-! ### How to rebuild a list of constructor arguments

`genConstrArgs` builds its result in two steps. It zips the new field names against the
argument types, and it then wraps each name as an `Identifier Unit`.

This file divides a target argument list `args` into two lists. The first holds its field
names, which are `args.map (·.1.name)`. The second holds its types, which are
`args.map (·.2)`. A zip and then a wrap of those two lists rebuilds `args` exactly.

The reason is that the name of an `Identifier Unit` gives that identifier, because its metadata
is the one value `()`. The next lemma states this fact. -/

/-- Take the field names of an argument list, wrap them again as `Identifier Unit` values, and
    pair them again with the argument types. The result is the argument list itself. The
    metadata of an `Identifier Unit` is the one value `()`, therefore `⟨a.1.name, ()⟩ = a.1`. -/
theorem constrArgs_reassemble (args : List (Identifier Unit × LMonoTy)) :
    ((args.map (·.1.name)).zip (args.map (·.2))).map
      (fun p => ((⟨p.1, ()⟩ : Identifier Unit), p.2)) = args := by
  rw [List.zip_map', List.map_map]
  refine List.map_id'' ?_ args |>.symm ▸ ?_
  · intro a; rfl
  · rfl

/-! ### Name reachability

To reach one specific block, the generator must reach its specific names. Those names are the
names of its datatypes, its constructors, its fields and its type parameters. `genFreshName`
draws each such name. It draws a candidate from `genIdentName`, and it returns that candidate
unless the candidate is already in the list of reserved names.

Therefore the generator can reach a name under exactly two conditions. The name must be a legal
identifier that the generator can draw, which is `∈ support genIdentName`. The name must also be
absent from the reserved list. The branch that returns the raw draw is then available.

The lemmas below state the condition `∈ support genIdentName` as a hypothesis, because the callers
give the condition in that form. `mem_support_genIdentName_iff` in
`FunctionHasTypeAGen/IdentName.lean` gives that support in both directions, as

  `IsGenIdentName s ∧ isReservedKeyword s = false`

The first conjunct says that `s` is a bare Core identifier. Its first character is in
`strataIsIdFirst` of Core, and each of the other characters is in `strataIsIdRest`. The proofs show
that the alphabets of the generator are equal to these two classes of the lexer. The second
conjunct says that `s` is not a reserved keyword. Both conjuncts are decidable. Therefore
`genFreshName_complete_of_syntactic` below discharges the hypothesis, and `decide` closes it for a
concrete name. -/

/-- **`genFreshName` reaches each legal identifier that is absent from the reserved list.**
    Assume that `s` is in the support of `genIdentName`, and that `s` is absent from the
    reserved list. Then `genFreshName` returns `s` with no change, through the branch for a
    name that is absent from that list. -/
theorem genFreshName_complete (reserved : List String) (s : String)
    (hident : s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hnotmem : s ∉ reserved) :
    s ∈ SetGen.support (genFreshName (G := SetGen.Set) reserved) := by
  simp only [genFreshName, mem_support_bind_iff, mem_support_ite_iff,
             mem_support_pure_iff]
  refine ⟨s, hident, Or.inr ⟨?_, rfl⟩⟩
  -- The goal is `¬ (reserved.contains s = true)`, and it holds because `s ∉ reserved`.
  rw [List.contains_eq_mem, decide_eq_true_eq]
  exact hnotmem

/-- **`genFreshName` reaches each name that is a legal identifier and is not a keyword.** The name
    must also be absent from the reserved list. This is `genFreshName_complete`, and
    `mem_support_genIdentName_iff` discharges its hypothesis `∈ support genIdentName`. Therefore
    all three hypotheses are decidable syntactic conditions on `s`.

    This form removes the side conditions on name reachability from the completeness results
    downstream. A caller that holds a name from a well-typed program does not assume that the
    generator can draw the name. The caller only does a check that the name is a legal identifier
    and is not a keyword. -/
theorem genFreshName_complete_of_syntactic (reserved : List String) (s : String)
    (hsyn : StrataGenerators.Function.IsGenIdentName s)
    (hnotkw : isReservedKeyword s = false)
    (hnotmem : s ∉ reserved) :
    s ∈ SetGen.support (genFreshName (G := SetGen.Set) reserved) :=
  genFreshName_complete reserved s
    (StrataGenerators.Function.mem_support_genIdentName_of_syntactic hsyn hnotkw) hnotmem

/-- **`genFreshNames` reaches each list of legal identifiers that are different in pairs and
    absent from the reserved list.** Take a list `names` that obeys `Nodup`. Assume that the
    generator can reach each member, which is `∈ support genIdentName`, and that each member is
    absent from `reserved`. Then a draw of `names.length` names makes exactly `names`.

    `genFreshName_complete` reaches each name. `Nodup` says that the names are different in
    pairs. Therefore each name of the tail is still absent from the reserved list after the
    generator adds the earlier names to it. The proof is an induction on `names`. -/
theorem genFreshNames_complete :
    ∀ (names reserved : List String),
      names.Nodup →
      (∀ s ∈ names, s ∈ SetGen.support (genIdentName (G := SetGen.Set))) →
      (∀ s ∈ names, s ∉ reserved) →
      names ∈ SetGen.support (genFreshNames (G := SetGen.Set) reserved names.length) := by
  intro names
  induction names with
  | nil =>
    intro reserved _ _ _
    simp only [List.length_nil, genFreshNames, mem_support_pure_iff]
  | cons a as ih =>
    intro reserved hnodup hident hnotmem
    simp only [List.nodup_cons] at hnodup
    obtain ⟨hanotin, hasnodup⟩ := hnodup
    simp only [List.length_cons, genFreshNames, mem_support_bind_iff, mem_support_pure_iff]
    refine ⟨a, genFreshName_complete reserved a (hident a (by simp)) (hnotmem a (by simp)),
      as, ?_, rfl⟩
    -- Each name of the tail is absent from `a :: reserved`. It is not `a`, by `Nodup`, and it
    -- is absent from `reserved`.
    exact ih (a :: reserved) hasnodup (fun s hs => hident s (by simp [hs]))
      (fun s hs => by
        simp only [List.mem_cons, not_or]
        exact ⟨fun heq => hanotin (heq ▸ hs), hnotmem s (by simp [hs])⟩)

/-! ### Completeness of `permutationOf`

`genConstructors` puts the constructors of each datatype into a random order. Therefore the
generator can make a well-formed datatype body whose inhabited constructor is not first in the
list.

For soundness, the proofs need only the fact that the result is a permutation. For completeness,
they need the opposite fact. Each permutation of `xs` is in the support of
`permutationOf xs`. -/

/-- Remove the member of a list at the index `i`, and then put that member back at the index
    `i`. The result is the list itself.

    The lemma `insertIdx_eraseIdx_getElem` in `Mathlib.Data.List.InsertIdx` states this fact.
    This file does not import the list files of Mathlib. Therefore this file proves the fact
    again, by an induction on the list. -/
theorem insertIdx_eraseIdx_getElem_self {α : Type} :
    ∀ (l : List α) (i : Nat) (h : i < l.length),
      (l.eraseIdx i).insertIdx i l[i] = l := by
  intro l
  induction l with
  | nil => intro i h; exact absurd h (by simp)
  | cons a t ih =>
    intro i h
    cases i with
    | zero => simp
    | succ j =>
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ,
                 List.insertIdx_succ_cons, List.cons.injEq, true_and]
      exact ih j (by simpa using h)

/-- **`permutationOf` is complete.** The generator can reach each permutation `zs` of `xs`,
    because the member `⟨zs, hp⟩` of the subtype is in the support.

    The proof is an induction on `xs`. At the step for `x :: xs'`, the proof finds `x` at an
    index `i` of `zs`. That member is present, because `zs.Perm (x :: xs')`. The proof then takes
    `ys := zs.eraseIdx i`, which is a permutation of `xs'` that the induction hypothesis reaches.
    It then puts `x` back at the index `i`, and that step rebuilds `zs`, by
    `insertIdx_eraseIdx_getElem`. -/
theorem permutationOf_complete {α : Type} :
    ∀ (xs zs : List α) (hp : xs.Perm zs),
      (⟨zs, hp⟩ : { ys // xs.Perm ys }) ∈
        SetGen.support (permutationOf (G := SetGen.Set) xs) := by
  intro xs
  induction xs with
  | nil =>
    intro zs hp
    -- A permutation of `[]` is `[]`; the sole support element is `⟨[], .nil⟩`.
    have hznil : zs = [] := hp.symm.eq_nil
    subst hznil
    rw [permutationOf]
    simp only [mem_support_pure_iff]
  | cons x xs' ih =>
    intro zs hp
    -- `x` occurs in `zs`. Take its index `i`.
    have hxmem : x ∈ zs := hp.mem_iff.mp List.mem_cons_self
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hxmem
    -- The index `i` is not more than the length of `ys`.
    have hilen : i ≤ (zs.eraseIdx i).length := by
      rw [List.length_eraseIdx_of_lt hi]; omega
    -- A second insertion of `x` at the index `i` rebuilds `zs`.
    have hreconstruct : (zs.eraseIdx i).insertIdx i x = zs := by
      rw [← hget]; exact insertIdx_eraseIdx_getElem_self zs i hi
    -- The list `ys := zs.eraseIdx i` is a permutation of `xs'`.
    have hzs_perm : zs.Perm (x :: zs.eraseIdx i) := by
      have hins := List.perm_insertIdx x (zs.eraseIdx i) hilen
      rwa [hreconstruct] at hins
    have hxs'_perm : xs'.Perm (zs.eraseIdx i) := (hp.trans hzs_perm).cons_inv
    rw [permutationOf]
    simp only [mem_support_bind_iff, mem_support_map_iff, mem_support_choose_iff]
    -- Give the shorter list from the induction hypothesis, and then the index `i`.
    refine ⟨⟨zs.eraseIdx i, hxs'_perm⟩, ih _ hxs'_perm,
      ⟨i, Nat.zero_le _, hilen⟩, ⟨⟨⟨i, Nat.zero_le _, hilen⟩⟩, ⟨Nat.zero_le _, hilen⟩, rfl⟩, ?_⟩
    -- The value of the subtype that the generator returns is `⟨zs, hp⟩`. Only the field `.val`
    -- matters here, because two proofs of one statement are equal.
    rw [mem_support_pure_iff]
    exact Subtype.ext hreconstruct.symm

/-! ### Completeness of the generators for the constructors

This section takes the completeness of `genArgTy` up to an argument list, to a constructor list
and to one datatype body. Those generators are `genConstrArgs`, `genConstrs` and
`genConstructors`.

These generators thread a list of reserved names, and that list grows. The generator reads that
list only through membership, because `genFreshName` tests `reserved.contains`. Therefore this
section follows each output list *as a set*, and it does not follow the exact shape of the list.
The set is the union of the new names with the input list. `SameReserved` names that equality of
sets. -/

/-- Two lists of reserved names that agree as *sets*, which is `x ∈ r₁ ↔ x ∈ r₂`. The generators
    for a name read `reserved` only through membership. Therefore membership in the support stays
    the same for two lists that obey `SameReserved`. -/
def SameReserved (r₁ r₂ : List String) : Prop := ∀ x, x ∈ r₁ ↔ x ∈ r₂

/-- The names that a constructor adds. They are its own name, and then its field names. -/
def ctorNames (c : LConstr Unit) : List String :=
  c.name.name :: c.args.map (·.1.name)

/-- All names a constructor list introduces, in order. -/
def ctorsNames (cs : List (LConstr Unit)) : List String :=
  cs.flatMap ctorNames

/-- A permutation of the list of constructors gives a permutation of the names that they add.
    `ctorsNames` is a `flatMap`, and a `flatMap` keeps a permutation. -/
theorem ctorsNames_perm {cs cs' : List (LConstr Unit)} (h : cs.Perm cs') :
    (ctorsNames cs).Perm (ctorsNames cs') :=
  List.Perm.flatMap_right ctorNames h

/-- **Completeness of `genConstrArgs`.** The generator can make a target argument list `args`,
    with the list of reserved names that holds its field names, under three conditions. The
    length of `args` is not more than `maxArgs`. Its field names are identifiers that the
    generator can reach, they are different in pairs, and they are absent from `reserved`. The
    generator can also make each argument type at the size `maxSize`.

    The field names that the generator makes are `args.map (·.1.name)`, and the argument types
    are `args.map (·.2)`. `genFreshNames_complete` reaches the names.
    `constrArgs_reassemble` shows that the zip and then the wrap rebuild `args`. The proof gives
    `maxSize` for the `chooseNat` of each argument. -/
theorem genConstrArgs_complete {baseTypes : List String} {tyCons : List KnownTyCon}
    {blockRefs : List BlockRef} {tyParams : List TyIdentifier}
    {rca : Bool} {maxArgs maxSize : Nat} {reserved : List String}
    {args : List (Identifier Unit × LMonoTy)}
    (hlen : args.length ≤ maxArgs)
    (hnodup : (args.map (·.1.name)).Nodup)
    (hident : ∀ arg ∈ args, arg.1.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hfresh : ∀ arg ∈ args, arg.1.name ∉ reserved)
    (htys : ∀ arg ∈ args, arg.2 ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs tyParams rca maxSize)) :
    (args, args.map (·.1.name) ++ reserved) ∈ SetGen.support
      (genConstrArgs (G := SetGen.Set) baseTypes tyCons blockRefs tyParams rca
        maxArgs maxSize reserved) := by
  simp only [genConstrArgs, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_vectorOf_iff]
  refine ⟨args.length, mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, hlen⟩,
    args.map (·.1.name), ?_, args.map (·.2), ⟨by simp, ?_⟩, ?_⟩
  · -- The generator can reach the field names, and those names are different in pairs.
    have hnames_len : (args.map (·.1.name)).length = args.length := by simp
    rw [← hnames_len]
    exact genFreshNames_complete _ reserved hnodup
      (fun s hs => by obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp hs; exact hident arg harg)
      (fun s hs => by obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp hs; exact hfresh arg harg)
  · -- The generator can make each argument type at the limit `maxSize`.
    intro ty hty
    obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp hty
    exact mem_support_bind_iff.mpr
      ⟨maxSize, mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩, htys arg harg⟩
  · -- The zip and then the wrap rebuild `args`. The output list of reserved names agrees.
    rw [constrArgs_reassemble]

/-- A constructor has the *default name for its tester*, which the generator emits. That name is
    `"is" ++ name.name`. The metadata of the constructor is the one value `()`, which is automatic
    for `Unit`.

    The generator always makes this shape, because it builds `{ name := ⟨cname, () ⟩, args := … }`
    and keeps the default value of `testerName`. Therefore the generator can reach a target
    constructor only when that constructor has this shape.

    `MutualADTWF` puts no condition on `testerName`. Therefore this file takes this condition as
    a hypothesis, in the way that it takes the conditions about the reachability of a name. -/
def hasDefaultTesterName (c : LConstr Unit) : Prop :=
  c.testerName = "is" ++ c.name.name

/-- A normal-form constructor equals the record the generator rebuilds from its
    name and argument list. -/
theorem ctor_reassemble {c : LConstr Unit} (h : hasDefaultTesterName c) :
    ({ name := ⟨c.name.name, ()⟩, args := c.args } : LConstr Unit) = c := by
  cases c with
  | mk name args tn =>
    cases name with
    | mk nm u =>
      cases u
      simp only [hasDefaultTesterName] at h
      simp only [LConstr.mk.injEq, true_and]
      exact h.symm

/-- **Completeness of `genConstrs`.** The generator can make a target list of constructors `cs`
    at the count `cs.length`, with all of them at the same flag `rca`. The output list of
    reserved names then agrees, *as a set*, with the names that `cs` adds together with the
    input list `reserved`.

    This theorem has five hypotheses:

    * each constructor obeys `hasDefaultTesterName`;
    * the number of arguments of each constructor is not more than `maxArgs`;
    * the generator can reach each name that the constructors add;
    * those names are different in pairs, which is `Nodup` for `ctorsNames cs`, and they are
      absent from `reserved`;
    * the generator can make each argument type at the size `maxSize`.

    The proof is an induction on `cs`, and it threads the list of reserved names as a set. -/
theorem genConstrs_complete {baseTypes : List String} {tyCons : List KnownTyCon}
    {blockRefs : List BlockRef} {tyParams : List TyIdentifier}
    {rca : Bool} {maxArgs maxSize : Nat} :
    ∀ (cs : List (LConstr Unit)) (reserved : List String),
      (∀ c ∈ cs, hasDefaultTesterName c) →
      (∀ c ∈ cs, c.args.length ≤ maxArgs) →
      (∀ nm ∈ ctorsNames cs, nm ∈ SetGen.support (genIdentName (G := SetGen.Set))) →
      (ctorsNames cs).Nodup →
      (∀ nm ∈ ctorsNames cs, nm ∉ reserved) →
      (∀ c ∈ cs, ∀ arg ∈ c.args, arg.2 ∈ SetGen.support
        (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs tyParams rca maxSize)) →
      ∃ reserved', SameReserved reserved' (ctorsNames cs ++ reserved) ∧
        (cs, reserved') ∈ SetGen.support (genConstrs (G := SetGen.Set) baseTypes tyCons
          blockRefs tyParams rca maxArgs maxSize cs.length reserved) := by
  intro cs
  induction cs with
  | nil =>
    intro reserved _ _ _ _ _ _
    exact ⟨reserved, fun x => by simp [ctorsNames], by
      simp only [List.length_nil, genConstrs, mem_support_pure_iff]⟩
  | cons c cs ih =>
    intro reserved hnf hargslen hident hnodup hfresh htys
    -- Divide the names that the constructors add. The names of `c` come first, and the names
    -- of the other constructors come after them.
    have hcnames : ctorsNames (c :: cs) = ctorNames c ++ ctorsNames cs := by
      simp [ctorsNames, ctorNames]
    rw [hcnames] at hnodup hident hfresh
    rw [List.nodup_append] at hnodup
    obtain ⟨hcnodup, hcsnodup, hdisj⟩ := hnodup
    -- Here `ctorNames c` is `c.name.name` and then the field names.
    have hcnodup' := hcnodup
    simp only [ctorNames, List.nodup_cons] at hcnodup'
    obtain ⟨hcname_notfield, hfieldnodup⟩ := hcnodup'
    -- Two facts about membership in `ctorNames c`.
    have hcname_in : c.name.name ∈ ctorNames c := List.mem_cons_self
    have hfield_in : ∀ arg ∈ c.args, arg.1.name ∈ ctorNames c :=
      fun arg harg => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨arg, harg, rfl⟩)
    -- The name of `c`.
    have hcname_fresh : c.name.name ∉ reserved :=
      hfresh c.name.name (List.mem_append_left _ hcname_in)
    have hcname_ident : c.name.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
      hident c.name.name (List.mem_append_left _ hcname_in)
    -- The field names are absent from `c.name.name :: reserved`, and the generator can reach
    -- them.
    have hfieldfresh : ∀ arg ∈ c.args, arg.1.name ∉ (c.name.name :: reserved) := by
      intro arg harg
      simp only [List.mem_cons, not_or]
      refine ⟨fun heq => hcname_notfield (heq ▸ List.mem_map.mpr ⟨arg, harg, rfl⟩), ?_⟩
      exact hfresh arg.1.name (List.mem_append_left _ (hfield_in arg harg))
    have hfieldident : ∀ arg ∈ c.args, arg.1.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
      fun arg harg => hident arg.1.name (List.mem_append_left _ (hfield_in arg harg))
    -- Reach the argument list of `c`. The proof adds `c.name.name` to the list of reserved
    -- names, and then the field names.
    have hargs := genConstrArgs_complete (reserved := c.name.name :: reserved)
      (hargslen c (by simp)) hfieldnodup hfieldident hfieldfresh
      (fun arg harg => htys c (by simp) arg harg)
    -- The list of reserved names after the arguments of `c`, as a set.
    let res₁ := c.args.map (·.1.name) ++ c.name.name :: reserved
    -- The names of the other constructors are absent from `res₁`.
    have hcsfresh : ∀ nm ∈ ctorsNames cs, nm ∉ res₁ := by
      intro nm hnm
      show nm ∉ c.args.map (·.1.name) ++ c.name.name :: reserved
      simp only [List.mem_append, List.mem_cons, not_or]
      refine ⟨?_, ?_, hfresh nm (List.mem_append_right _ hnm)⟩
      · -- `nm` is not a field name of `c`, because `ctorNames c` and `ctorsNames cs` share no
        -- name.
        intro hmem
        obtain ⟨arg, harg, hnmeq⟩ := List.mem_map.mp hmem
        exact hdisj (a := nm) (hnmeq ▸ hfield_in arg harg) nm hnm rfl
      · -- Also `nm ≠ c.name.name`, for the same reason.
        intro heq
        exact hdisj (a := nm) (heq ▸ hcname_in) nm hnm rfl
    obtain ⟨reserved', hsame', hrest⟩ := ih res₁
      (fun c' hc' => hnf c' (by simp [hc']))
      (fun c' hc' => hargslen c' (by simp [hc']))
      (fun nm hnm => hident nm (List.mem_append_right _ hnm))
      hcsnodup hcsfresh
      (fun c' hc' arg harg => htys c' (by simp [hc']) arg harg)
    -- Build the result. The head constructor comes first, and the tail comes after it.
    refine ⟨reserved', ?_, ?_⟩
    · -- The output list as a set. It agrees with the union of `ctorsNames cs` and `res₁`, and
      -- that union agrees with the union of `ctorsNames (c :: cs)` and `reserved`.
      intro x
      rw [hsame' x, hcnames]
      show (x ∈ ctorsNames cs ++ (c.args.map (·.1.name) ++ c.name.name :: reserved)) ↔ _
      simp only [List.mem_append, ctorNames, List.mem_cons]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inr h
      · rintro (((h | h) | h) | h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
    · -- The step `n+1` of the generator, which rebuilds `c :: cs`.
      simp only [List.length_cons, genConstrs, mem_support_bind_iff, mem_support_pure_iff]
      refine ⟨c.name.name, genFreshName_complete reserved c.name.name hcname_ident hcname_fresh,
        (c.args, res₁), hargs, (cs, reserved'), hrest, ?_⟩
      -- The head constructor of the result is `c`, because `c` has the default name for its
      -- tester.
      rw [Prod.mk.injEq]
      refine ⟨?_, rfl⟩
      rw [List.cons.injEq]
      exact ⟨(ctor_reassemble (hnf c (by simp))).symm, rfl⟩

/-- **Completeness of `genConstructors`, which makes one datatype body.** The generator can make
    a target datatype `d`, with `d.name = nm` and `d.typeArgs = params`. The caller must divide
    the constructors of `d` into an inhabited constructor `c₀` and the other constructors
    `restCs`. That division holds up to the permutation that the generator applies, which is
    `hperm : (c₀ :: restCs).Perm d.constrs`. The caller must also give these facts:

    * each constructor obeys `hasDefaultTesterName`, and its number of arguments is not more
      than `maxArgs`;
    * the names that the constructors add, which are `ctorsNames (c₀ :: restCs)`, are
      identifiers that the generator can reach, they are different in pairs, and they are absent
      from `params ++ reserved`;
    * the generator can make each argument type of `c₀` from the set `inhabRefs`, at the flag
      `true`. This fact makes the datatype inhabited through the block datatypes of a lower rank.
    * the generator can make each argument type of the other constructors from the full set
      `visibleRefs allHeaders params`, at the flag `true`;
    * the length of `restCs` is not more than `maxRecConstrs`.

    The proof gives `numExtraBase := 0` to the generator. Therefore the generator makes no
    constructor in the group that uses the flag `false`. It makes each constructor other than
    `c₀` from the full set. The proof also gives `numRec := restCs.length`.

    `genConstrArgs_complete` reaches the arguments of `c₀`. `genConstrs_complete` reaches the
    other constructors. `permutationOf_complete` reaches the target order. -/
theorem genConstructors_complete {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List TypeConstructor} {inhabRefs : List BlockRef}
    {nm : String} {params : List TyIdentifier}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String}
    {d : LDatatype Unit} {c₀ : LConstr Unit} {restCs : List (LConstr Unit)}
    (hdname : d.name = nm) (hdparams : d.typeArgs = params)
    (hperm : (c₀ :: restCs).Perm d.constrs)
    (hnf : ∀ c ∈ c₀ :: restCs, hasDefaultTesterName c)
    (hargslen : ∀ c ∈ c₀ :: restCs, c.args.length ≤ maxArgs)
    (hident : ∀ nm' ∈ ctorsNames (c₀ :: restCs), nm' ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hnodup : (ctorsNames (c₀ :: restCs)).Nodup)
    (hfresh : ∀ nm' ∈ ctorsNames (c₀ :: restCs), nm' ∉ params ++ reserved)
    (hreclen : restCs.length ≤ maxRecConstrs)
    (hwit : ∀ arg ∈ c₀.args, arg.2 ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons inhabRefs params true maxSize))
    (hrest : ∀ c ∈ restCs, ∀ arg ∈ c.args, arg.2 ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons (visibleRefs allHeaders params) params true maxSize)) :
    d ∈ SetGen.support (genConstructors (G := SetGen.Set) baseTypes tyCons allHeaders
      inhabRefs nm params maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved) := by
  -- Divide the names that the constructors add. The names of `c₀` come first, and the names of
  -- the other constructors come after them.
  have hcnames : ctorsNames (c₀ :: restCs) = ctorNames c₀ ++ ctorsNames restCs := by
    simp [ctorsNames, ctorNames]
  rw [hcnames] at hident hnodup hfresh
  rw [List.nodup_append] at hnodup
  obtain ⟨hc₀nodup, hrestnodup, hdisj⟩ := hnodup
  -- Here `ctorNames c₀` is `c₀.name.name` and then the field names.
  have hc₀nodup' := hc₀nodup
  simp only [ctorNames, List.nodup_cons] at hc₀nodup'
  obtain ⟨hc₀name_notfield, hfieldnodup⟩ := hc₀nodup'
  have hc₀name_in : c₀.name.name ∈ ctorNames c₀ := List.mem_cons_self
  have hfield_in : ∀ arg ∈ c₀.args, arg.1.name ∈ ctorNames c₀ :=
    fun arg harg => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨arg, harg, rfl⟩)
  -- The name of `c₀` and its field names, against `params ++ reserved`.
  have hc₀name_fresh : c₀.name.name ∉ params ++ reserved :=
    hfresh c₀.name.name (List.mem_append_left _ hc₀name_in)
  have hc₀name_ident : c₀.name.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
    hident c₀.name.name (List.mem_append_left _ hc₀name_in)
  have hfieldfresh : ∀ arg ∈ c₀.args, arg.1.name ∉ (c₀.name.name :: (params ++ reserved)) := by
    intro arg harg
    simp only [List.mem_cons, not_or]
    exact ⟨fun heq => hc₀name_notfield (heq ▸ List.mem_map.mpr ⟨arg, harg, rfl⟩),
      hfresh arg.1.name (List.mem_append_left _ (hfield_in arg harg))⟩
  have hfieldident : ∀ arg ∈ c₀.args, arg.1.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
    fun arg harg => hident arg.1.name (List.mem_append_left _ (hfield_in arg harg))
  -- Unfold `genConstructors`. A `let` binds `blockRefs` and `reserved`.
  simp only [genConstructors, mem_support_bind_iff, mem_support_pure_iff]
  -- The name of the inhabited constructor.
  refine ⟨c₀.name.name,
    genFreshName_complete (params ++ reserved) c₀.name.name hc₀name_ident hc₀name_fresh, ?_⟩
  -- The arguments of the inhabited constructor, from `inhabRefs`, at the flag `true`.
  refine ⟨(c₀.args, c₀.args.map (·.1.name) ++ c₀.name.name :: (params ++ reserved)),
    genConstrArgs_complete (hargslen c₀ (by simp)) hfieldnodup hfieldident hfieldfresh hwit, ?_⟩
  -- Here `numExtraBase := 0`, therefore the generator makes no constructor at the flag
  -- `false`.
  refine ⟨0, mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩, ?_⟩
  let res₁ := c₀.args.map (·.1.name) ++ c₀.name.name :: (params ++ reserved)
  refine ⟨([], res₁), mem_support_pure_iff.mpr rfl, ?_⟩
  -- Here `numRec := restCs.length`. The generator makes the other constructors from the full
  -- set.
  refine ⟨restCs.length, mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, hreclen⟩, ?_⟩
  -- The names of `restCs` are absent from `res₁`. They share no name with `c₀`, and they are
  -- fresh against the other part of that list.
  have hrestfresh : ∀ nm' ∈ ctorsNames restCs, nm' ∉ res₁ := by
    intro nm' hnm'
    show nm' ∉ c₀.args.map (·.1.name) ++ c₀.name.name :: (params ++ reserved)
    rw [List.mem_append, List.mem_cons]
    rintro (hmem | heq | hpr)
    · obtain ⟨arg, harg, hnmeq⟩ := List.mem_map.mp hmem
      exact hdisj (a := nm') (hnmeq ▸ hfield_in arg harg) nm' hnm' rfl
    · exact hdisj (a := nm') (heq ▸ hc₀name_in) nm' hnm' rfl
    · exact hfresh nm' (List.mem_append_right _ hnm') hpr
  obtain ⟨reserved', _, hrec⟩ := genConstrs_complete restCs res₁
    (fun c hc => hnf c (by simp [hc])) (fun c hc => hargslen c (by simp [hc]))
    (fun nm' hnm' => hident nm' (List.mem_append_right _ hnm'))
    hrestnodup hrestfresh
    (fun c hc arg harg => hrest c hc arg harg)
  refine ⟨(restCs, reserved'), hrec, ?_⟩
  -- Put the ordered list `c₀ :: ([] ++ restCs)` into the order of `d.constrs`.
  refine ⟨⟨d.constrs, ?_⟩, ?_, ?_⟩
  · -- The ordered list is a permutation of `d.constrs`, and its head is `c₀`.
    show ({ name := ⟨c₀.name.name, ()⟩, args := c₀.args } :: ([] ++ restCs)).Perm d.constrs
    rw [List.nil_append, ctor_reassemble (hnf c₀ (by simp))]
    exact hperm
  · -- `permutationOf` reaches `d.constrs`.
    exact permutationOf_complete _ d.constrs _
  · -- The record that the generator builds is `d`. `hdname` and `hdparams` fix its two fields.
    -- The field `constrs_ne` is a proof, therefore its value does not matter.
    cases d with
    | mk dname dtyargs dconstrs dne =>
      simp only at hdname hdparams
      subst hdname; subst hdparams; rfl

/-! ### Completeness of the map over the block bodies

`genConstructorsForAllTypes` applies `genConstructors` to each member of a list of headers with
their ranks, which is `todo : List (TypeConstructor × Nat)`. It draws the inhabited constructor
of each datatype from `visibleRefs (lowerRankHeaders rankedHeaders hr.2) hr.1.params`. That set
holds the block datatypes of a lower rank.

To reach one target block, this section gives that block as a list `blockTodo`. Each member of
`blockTodo` agrees with the member of `todo` at the same index. Each datatype body must also
divide, up to a permutation, into an inhabited constructor and the other constructors.

The generator must be able to make the argument types of the inhabited constructor from the set
for a lower rank. It must be able to make the argument types of the other constructors from the
full visible set.

These facts are exactly what `genConstructors_complete` takes. The rank of each member alone
gives the set for the inhabited constructor. Therefore this proof needs **no** accumulator
`done` and no record of a prefix, and the order of the declarations has no effect. -/

/-- **Completeness of `genConstructorsForAllTypes`, which maps over the bodies with their
    ranks.** Take a target block `blockTodo`. Each of its members must agree with the member of
    the list `todo` at the same index, in its name and in its parameters.

    Each datatype of `blockTodo` must also divide, up to a permutation, into an inhabited
    constructor and the other constructors.

    The generator must be able to make the argument types of the inhabited constructor from the
    set for a lower rank. That set is `visibleRefs (lowerRankHeaders rankedHeaders r)`. It must
    also be able to make the argument types of the other constructors from the full set
    `visibleRefs allHeaders`. These facts are the hypotheses that `genConstructors_complete`
    takes.

    Then the generator can make `blockTodo`. The proof is an induction on `todo`, with the
    aligned list `blockTodo`. It threads no accumulator `done`. -/
theorem genConstructorsForAllTypes_complete {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List TypeConstructor} {rankedHeaders : List (TypeConstructor × Nat)}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String} :
    ∀ (todo : List (TypeConstructor × Nat)) (blockTodo : MutualDatatype Unit),
      blockTodo.length = todo.length →
      (∀ i (hi : i < todo.length) (hi' : i < blockTodo.length),
        (todo[i]'hi).1.name = (blockTodo[i]'hi').name ∧
          (todo[i]'hi).1.params = (blockTodo[i]'hi').typeArgs) →
      (∀ i (hi : i < blockTodo.length) (hi' : i < todo.length),
        ∃ (witness : LConstr Unit) (rest : List (LConstr Unit)),
          (witness :: rest).Perm (blockTodo[i]'hi).constrs ∧
          (∀ c ∈ witness :: rest, hasDefaultTesterName c) ∧
          (∀ c ∈ witness :: rest, c.args.length ≤ maxArgs) ∧
          (∀ nm' ∈ ctorsNames (witness :: rest),
            nm' ∈ SetGen.support (genIdentName (G := SetGen.Set))) ∧
          (ctorsNames (witness :: rest)).Nodup ∧
          (∀ nm' ∈ ctorsNames (witness :: rest), nm' ∉ (blockTodo[i]'hi).typeArgs ++ reserved) ∧
          rest.length ≤ maxRecConstrs ∧
          (∀ arg ∈ witness.args, arg.2 ∈ SetGen.support
            (genArgTy (G := SetGen.Set) baseTypes tyCons
              (visibleRefs (lowerRankHeaders rankedHeaders (todo[i]'hi').2) (blockTodo[i]'hi).typeArgs)
              (blockTodo[i]'hi).typeArgs true maxSize)) ∧
          (∀ c ∈ rest, ∀ arg ∈ c.args, arg.2 ∈ SetGen.support
            (genArgTy (G := SetGen.Set) baseTypes tyCons
              (visibleRefs allHeaders (blockTodo[i]'hi).typeArgs)
              (blockTodo[i]'hi).typeArgs true maxSize))) →
      blockTodo ∈ SetGen.support (genConstructorsForAllTypes (G := SetGen.Set) baseTypes tyCons
        allHeaders rankedHeaders maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved todo) := by
  intro todo
  induction todo with
  | nil =>
    intro blockTodo hlen _ _
    have : blockTodo = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst this
    simp only [genConstructorsForAllTypes, mem_support_pure_iff]
  | cons hr todoTl ih =>
    intro blockTodo hlen halign hbody
    match blockTodo, hlen with
    | d :: blockTl, hlen =>
      simp only [genConstructorsForAllTypes, mem_support_bind_iff, mem_support_pure_iff]
      -- The head datatype `d` agrees with the header `hr` and its rank.
      have halign0 := halign 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at halign0
      obtain ⟨hname0, hparams0⟩ := halign0
      have hbody0 := hbody 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at hbody0
      -- Rewrite the sets and the parameters of the hypothesis into the `hr.1.params` of the
      -- generator.
      rw [← hparams0] at hbody0
      obtain ⟨c₀, restCs, hperm, hnf, hargslen, hident, hnodup, hfresh, hreclen, hwit, hrest⟩ := hbody0
      refine ⟨d, ?_, blockTl, ?_, rfl⟩
      · -- `genConstructors_complete` reaches `d`. It makes the inhabited constructor from the
        -- set for a lower rank, which is
        -- `visibleRefs (lowerRankHeaders rankedHeaders hr.2) hr.1.params`. It makes the other
        -- constructors from the full set. `hname0` and `hparams0` fix the name and the
        -- parameters.
        exact genConstructors_complete hname0.symm hparams0.symm hperm hnf hargslen hident
          hnodup hfresh hreclen hwit hrest
      -- Recurse on the tail. The ranks come from `rankedHeaders`, and they do not change.
      refine ih blockTl (by simpa using hlen) ?_ ?_
      · intro i hi hi'
        have := halign (i + 1) (by simpa using hi) (by simpa using hi')
        simpa using this
      · intro i hi hi'
        have hbodyI := hbody (i + 1) (by simpa using hi) (by simpa using hi')
        simp only [List.getElem_cons_succ] at hbodyI ⊢
        exact hbodyI

/-! ### Completeness of phase 1 and of the full generator -/

/-- **Completeness of `genParamsList`.** The generator can make a target list of parameter lists
    `paramsList` at the count `paramsList.length`, under three conditions. The length of each
    inner list is not more than `maxTyParams`. Each inner list obeys `Nodup`. Each of its members
    is an identifier that the generator can reach, and each member is absent from `reserved`.

    Each `chooseNat` picks the length of one inner list, and `genFreshNames_complete` reaches that
    list. The proof is an induction on `paramsList`. -/
theorem genParamsList_complete {reserved : List String} {maxTyParams : Nat} :
    ∀ (paramsList : List (List TyIdentifier)),
      (∀ params ∈ paramsList, params.length ≤ maxTyParams) →
      (∀ params ∈ paramsList, params.Nodup) →
      (∀ params ∈ paramsList, ∀ p ∈ params, p ∈ SetGen.support (genIdentName (G := SetGen.Set))) →
      (∀ params ∈ paramsList, ∀ p ∈ params, p ∉ reserved) →
      paramsList ∈ SetGen.support
        (genParamsList (G := SetGen.Set) reserved maxTyParams paramsList.length) := by
  intro paramsList
  induction paramsList with
  | nil =>
    intro _ _ _ _
    simp only [List.length_nil, genParamsList, mem_support_pure_iff]
  | cons params rest ih =>
    intro hlen hnodup hident hfresh
    simp only [List.length_cons, genParamsList, mem_support_bind_iff, mem_support_pure_iff]
    refine ⟨params.length, mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, hlen params (by simp)⟩,
      params, ?_, rest, ?_, rfl⟩
    · exact genFreshNames_complete params reserved (hnodup params (by simp))
        (fun p hp => hident params (by simp) p hp) (fun p hp => hfresh params (by simp) p hp)
    · exact ih (fun p hp => hlen p (by simp [hp])) (fun p hp => hnodup p (by simp [hp]))
        (fun p hp => hident p (by simp [hp])) (fun p hp => hfresh p (by simp [hp]))

/-- **Completeness of `genRanks`.** The generator can make a target list of ranks `ranks` at the
    count `ranks.length`, when each rank is not more than `maxRank`. Each `chooseNat` picks one
    rank. The proof is an induction on `ranks`. -/
theorem genRanks_complete {maxRank : Nat} :
    ∀ (ranks : List Nat), (∀ r ∈ ranks, r ≤ maxRank) →
      ranks ∈ SetGen.support (genRanks (G := SetGen.Set) maxRank ranks.length) := by
  intro ranks
  induction ranks with
  | nil => intro _; simp only [List.length_nil, genRanks, mem_support_pure_iff]
  | cons r rest ih =>
    intro hle
    simp only [List.length_cons, genRanks, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨r, mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, hle r (by simp)⟩,
      rest, ih (fun r' hr' => hle r' (by simp [hr'])), rfl⟩

/-- The headers that `genMutuallyRecursiveDatatypes` builds for a target block. Each header holds
    the name of one datatype with its own type arguments.

    This definition is one `map`, and it is not a `zip` of the list of names with the list of
    parameter lists. Therefore `take`, `length` and an index all reduce by definition. It agrees
    with the `(names.zip paramsList).map …` of the generator, when `names` is `block.map (·.name)`
    and `paramsList` is `block.map (·.typeArgs)`. Read `blockHeaders_eq_zip`. -/
def blockHeaders (block : MutualDatatype Unit) : List TypeConstructor :=
  block.map (fun d => { name := d.name, params := d.typeArgs })

/-- `blockHeaders` in the form that the generator builds. The generator zips the list of names
    with the list of parameter lists, and it then maps the result into headers. -/
theorem blockHeaders_eq_zip (block : MutualDatatype Unit) :
    blockHeaders block =
      ((block.map (·.name)).zip (block.map (·.typeArgs))).map
        (fun p => { name := p.1, params := p.2 }) := by
  rw [blockHeaders, List.zip_map', List.map_map]
  rfl

/-- `blockHeaders` and `List.take` give the same result in each order. The first `i` headers are
    the headers of the first `i` datatypes. -/
theorem blockHeaders_take (block : MutualDatatype Unit) (i : Nat) :
    (blockHeaders block).take i = blockHeaders (block.take i) := by
  simp only [blockHeaders, List.map_take]

/-- `blockHeaders block` has the same length as `block`. -/
theorem blockHeaders_length (block : MutualDatatype Unit) :
    (blockHeaders block).length = block.length := by
  simp only [blockHeaders, List.length_map]

/-- The header at the index `i` of `blockHeaders block` is
    `⟨block[i].name, block[i].typeArgs⟩`. -/
theorem blockHeaders_getElem (block : MutualDatatype Unit) (i : Nat)
    (hi : i < (blockHeaders block).length) (hi' : i < block.length) :
    (blockHeaders block)[i] = { name := (block[i]'hi').name, params := (block[i]'hi').typeArgs } := by
  simp only [blockHeaders, List.getElem_map]

/-- **Completeness of `genMutuallyRecursiveDatatypes`, with the ranks as a parameter.** The
    generator can make a target block under these conditions:

    * the block is not empty, and its length is not more than `maxExtraDatatypes + 1`;
    * its datatype names are identifiers that the generator can reach, they are different in
      pairs, and they are absent from `initialReserved`. `MutualADTWF` gives `namesNodup`, and
      the name pool of the generator needs the other two facts.
    * the number of type parameters of each datatype is not more than `maxTyParams`, those
      parameters are identifiers that the generator can reach, they are different in pairs, and
      they are absent from the block names and from `initialReserved`;
    * the caller gives a list `ranks`, one rank for each datatype, and each rank is not more than
      `block.length - 1`;
    * each datatype body divides, up to a permutation, into an inhabited constructor and the
      other constructors. The generator must be able to make the argument types of the inhabited
      constructor from the set for the rank of that datatype, which is
      `visibleRefs (lowerRankHeaders ((blockHeaders block).zip ranks) (ranks[i])) …`. It must be
      able to make the argument types of the other constructors from the full set. These facts
      are the hypotheses that `genConstructors_complete` takes, against the list of reserved
      names `block.map (·.name) ++ initialReserved …`.

    The caller gives the ranks, and the proof does not build them.
    `genMutuallyRecursiveDatatypes_complete_of_MutualADTWF` builds them from `MutualADTWF` alone.
    This theorem needs no order of the datatypes, because the drawn ranks alone give the set of
    names for each inhabited constructor.

    Phase 1 draws `numExtra := block.length - 1`, `names := block.map (·.name)` and
    `paramsList := block.map (·.typeArgs)`. Phase 2 is
    `genConstructorsForAllTypes_complete`. -/
theorem genMutuallyRecursiveDatatypes_complete {baseTypes : List String}
    {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hne : block ≠ [])
    (hcount : block.length ≤ maxExtraDatatypes + 1)
    (hnamesNodup : (block.map (·.name)).Nodup)
    (hnamesIdent : ∀ d ∈ block, d.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hnamesFresh : ∀ d ∈ block, d.name ∉ initialReserved baseTypes tyCons extraReserved)
    (hparamsLen : ∀ d ∈ block, d.typeArgs.length ≤ maxTyParams)
    (hparamsNodup : ∀ d ∈ block, d.typeArgs.Nodup)
    (hparamsIdent : ∀ d ∈ block, ∀ p ∈ d.typeArgs, p ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hparamsFresh : ∀ d ∈ block, ∀ p ∈ d.typeArgs,
      p ∉ block.map (·.name) ++ initialReserved baseTypes tyCons extraReserved)
    (ranks : List Nat)
    (hrankslen : ranks.length = block.length)
    (hranksle : ∀ r ∈ ranks, r ≤ block.length - 1)
    (hbodies : ∀ i (hi : i < block.length) (hi' : i < ranks.length),
      ∃ (witness : LConstr Unit) (rest : List (LConstr Unit)),
        (witness :: rest).Perm (block[i]'hi).constrs ∧
        (∀ c ∈ witness :: rest, hasDefaultTesterName c) ∧
        (∀ c ∈ witness :: rest, c.args.length ≤ maxArgs) ∧
        (∀ nm' ∈ ctorsNames (witness :: rest),
          nm' ∈ SetGen.support (genIdentName (G := SetGen.Set))) ∧
        (ctorsNames (witness :: rest)).Nodup ∧
        (∀ nm' ∈ ctorsNames (witness :: rest),
          nm' ∉ (block[i]'hi).typeArgs ++
            (block.map (·.name) ++ initialReserved baseTypes tyCons extraReserved)) ∧
        rest.length ≤ maxRecConstrs ∧
        (∀ arg ∈ witness.args, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons
            (visibleRefs (lowerRankHeaders ((blockHeaders block).zip ranks) (ranks[i]'hi'))
              (block[i]'hi).typeArgs)
            (block[i]'hi).typeArgs true maxSize)) ∧
        (∀ c ∈ rest, ∀ arg ∈ c.args, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons
            (visibleRefs (blockHeaders block) (block[i]'hi).typeArgs)
            (block[i]'hi).typeArgs true maxSize))) :
    block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
      maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
      maxSize extraReserved) := by
  -- The block has the form `d₀ :: _`, therefore `block.length = (block.length - 1) + 1`.
  obtain ⟨len, hlen⟩ : ∃ len, block.length = len + 1 := by
    cases block with
    | nil => exact absurd rfl hne
    | cons d ds => exact ⟨ds.length, by simp⟩
  simp only [genMutuallyRecursiveDatatypes, mem_support_bind_iff]
  -- Here `numExtra := block.length - 1`, which is `len`.
  refine ⟨len, mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, by omega⟩, ?_⟩
  -- Here `names := block.map (·.name)`, and that list holds `len + 1` names.
  refine ⟨block.map (·.name), ?_, ?_⟩
  · -- The generator can reach the names. They are different in pairs, they are fresh, and the
    -- list holds `len + 1` names.
    have hnlen : (block.map (·.name)).length = len + 1 := by simp [hlen]
    rw [← hnlen]
    exact genFreshNames_complete _ _ hnamesNodup
      (fun s hs => by obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hs; exact hnamesIdent d hd)
      (fun s hs => by obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hs; exact hnamesFresh d hd)
  -- Here `paramsList := block.map (·.typeArgs)`.
  refine ⟨block.map (·.typeArgs), ?_, ?_⟩
  · -- The generator can reach the parameters. They are different in pairs, their number is
    -- under the limit, and the length of the list agrees with the length of `names`.
    have hnameslen : (block.map (·.name)).length = (block.map (·.typeArgs)).length := by simp
    rw [hnameslen]
    exact genParamsList_complete _
      (fun params hp => by obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp; exact hparamsLen d hd)
      (fun params hp => by obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp; exact hparamsNodup d hd)
      (fun params hp p hpp => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp; exact hparamsIdent d hd p hpp)
      (fun params hp p hpp => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp; exact hparamsFresh d hd p hpp)
  -- Here `ranks` is the list of ranks that the caller gives, and the generator draws
  -- `names.length` ranks.
  refine ⟨ranks, ?_, ?_⟩
  · -- The generator can reach the ranks. `genRanks` draws `names.length` ranks, and each of
    -- them is not more than `numExtra`, which is `len`. `hranksle` says that each rank is not
    -- more than `block.length - 1`, which is also `len`.
    have hrl : ranks.length = (block.map (·.name)).length := by rw [hrankslen]; simp
    -- The `bind` outside needs `genRanks (G := Set) maxRank ranks.length`, with `maxRank`
    -- equal to `numExtra`, which is `len`. Therefore rewrite `names.length` to
    -- `ranks.length`.
    have hnl : (block.map (·.name)).length = ranks.length := hrl.symm
    rw [hnl]
    exact genRanks_complete ranks (fun r hr => by
      have := hranksle r hr; omega)
  · -- The map over the bodies reaches `block`, with the headers `blockHeaders block` and the
    -- ranks.
    rw [← blockHeaders_eq_zip]
    refine genConstructorsForAllTypes_complete ((blockHeaders block).zip ranks) block ?_ ?_ ?_
    · -- The lengths agree, therefore
      -- `blockTodo.length = ((blockHeaders block).zip ranks).length`.
      rw [List.length_zip, blockHeaders_length, hrankslen, Nat.min_self]
    · -- The two lists agree at each index, therefore
      -- `((blockHeaders block).zip ranks)[i].1 = ⟨block[i].name, block[i].typeArgs⟩`.
      intro i hi hi'
      rw [List.length_zip, blockHeaders_length, hrankslen, Nat.min_self] at hi
      rw [List.getElem_zip, blockHeaders_getElem block i (by rw [blockHeaders_length]; exact hi) hi]
      exact ⟨rfl, rfl⟩
    · -- The generator can make the body at each index `i`. This fact is exactly `hbodies`,
      -- because `((blockHeaders block).zip ranks)[i].2 = ranks[i]`.
      intro i hi hi'
      have hir : i < ranks.length := by rw [hrankslen]; exact hi
      have hzip2 : (((blockHeaders block).zip ranks)[i]'hi').2 = ranks[i]'hir := by
        rw [List.getElem_zip]
      rw [hzip2]
      exact hbodies i hi hir

/-! ### The capstone, which is free of any order: completeness from `MutualADTWF` alone

`genMutuallyRecursiveDatatypes_complete` takes a list of ranks, and it takes the division of
the constructors of each datatype. The capstone below *builds* both of these from the
well-formedness of the block. The caller gives no order, no rank and no set of names for one
position.

`rankExists` takes `MutualADTWF.inhabited`, and it makes a rank. Under that rank, each datatype
has an inhabited constructor that refers only to block datatypes of a lower rank.

`genArgTy_complete_of_wf_partial` with `visibleRefs_cover_of_appears` then shows that the
generator can make each argument at some size, from the correct set of names. That set is the
set for a lower rank for the inhabited constructor, and it is the full set for the other
constructors.

`exists_uniform_bound` with `genArgTy_mono` collects those sizes into one size `N`, and the
generator can make the full block at that size. Therefore the statement ends with
`∃ maxSize`, which says that a large enough size is present.

The caller still gives the other limits of the generator, which are `maxExtraDatatypes`,
`maxTyParams`, `maxExtraBaseConstrs`, `maxRecConstrs` and `maxArgs`. The block is finite in
each of those dimensions. Only the size of one type has no limit at the start. -/

open Core Core.TypeSpec in
/-- **Completeness for a full block, from `MutualADTWF`, with no order.** Take a block that is
    `MutualADTWF` in a context, and that does not define again a datatype of that context, which
    is `hnew`. Each of its constructors obeys `hasDefaultTesterName`, and the block is under the
    limits on the datatypes, the parameters and the constructors. Its names and its parameters
    are identifiers that the generator can reach, and they are fresh against `initialReserved`.

    Then `genMutuallyRecursiveDatatypes` can make that block at some size `maxSize`. This proof
    **builds the rank itself**, through `rankExists`. The caller gives no order of the datatypes,
    and it gives no set of names for one position. The one input about inhabitance is
    `hwf.inhabited`.

    The size is an existential value, because a constructor argument type can be very large.
    Therefore no fixed `maxSize` reaches each block. `genArgTy_mono` makes the statement grow with
    the size, therefore each size that is not less than the one in the result also works. -/
theorem genMutuallyRecursiveDatatypes_complete_of_MutualADTWF {baseTypes : List String}
    {tyCons : List KnownTyCon} {C : LContext CoreLParams}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hwf : MutualADTWF C block)
    (hnew : ∀ d ∈ block, C.datatypes.getType d.name = none)
    (hcount : block.length ≤ maxExtraDatatypes + 1)
    (hnamesIdent : ∀ d ∈ block, d.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hnamesFresh : ∀ d ∈ block, d.name ∉ initialReserved baseTypes tyCons extraReserved)
    (hparamsLen : ∀ d ∈ block, d.typeArgs.length ≤ maxTyParams)
    (hparamsNodup : ∀ d ∈ block, d.typeArgs.Nodup)
    (hparamsIdent : ∀ d ∈ block, ∀ p ∈ d.typeArgs, p ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hparamsFresh : ∀ d ∈ block, ∀ p ∈ d.typeArgs,
      p ∉ block.map (·.name) ++ initialReserved baseTypes tyCons extraReserved)
    (hctors_nf : ∀ d ∈ block, ∀ c ∈ d.constrs, hasDefaultTesterName c)
    (hctors_len : ∀ d ∈ block, ∀ c ∈ d.constrs, c.args.length ≤ maxArgs)
    (hnames_ident : ∀ d ∈ block, ∀ nm' ∈ ctorsNames d.constrs,
      nm' ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hnames_nd : ∀ d ∈ block, (ctorsNames d.constrs).Nodup)
    (hnames_fresh : ∀ d ∈ block, ∀ nm' ∈ ctorsNames d.constrs,
      nm' ∉ d.typeArgs ++ (block.map (·.name) ++ initialReserved baseTypes tyCons extraReserved))
    (hreclen : ∀ d ∈ block, d.constrs.length ≤ maxRecConstrs + 1)
    (hvocab : VocabOk C baseTypes tyCons)
    (hbv : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, BitvecWidthOnly arg.2) :
    ∃ maxSize, block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
      maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
      maxSize extraReserved) := by
  -- Short names, and the facts about the block names that `rankExists` needs.
  have hnodup : (block.map (·.name)).Nodup := hwf.namesNodup
  have harrowB : ∀ d ∈ block, d.name ≠ "arrow" :=
    fun d hd => hn.block_ne_arrow _ (List.mem_map.mpr ⟨d, hd, rfl⟩)
  have hresolve : ∀ nm ∈ block.map (·.name),
      TypeFactory.getType (C.datatypes.push block) nm ≠ none := by
    intro nm hnm
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hnm
    rw [getType_push_self (hnew d hd) hnodup hd]; exact Option.some_ne_none d
  have hinhab : ∀ nm ∈ block.map (·.name), TySymInhab (C.datatypes.push block) nm := by
    intro nm hnm
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hnm
    exact hwf.inhabited d hd
  -- **The rank** from `rankExists`.
  obtain ⟨rank, hrankbound, hrankwit⟩ :=
    rankExists (C.datatypes.push block) (block.map (·.name)) hnodup hresolve hinhab
  let ranks : List Nat := block.map (fun d => rank d.name)
  have hranks : ranks = block.map (fun d => rank d.name) := rfl
  have hrankslen : ranks.length = block.length := by rw [hranks, List.length_map]
  have hranksle : ∀ r ∈ ranks, r ≤ block.length - 1 := by
    intro r hr
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
    have := hrankbound d.name (List.mem_map.mpr ⟨d, hd, rfl⟩)
    rw [List.length_map] at this; omega
  have hranks_get : ∀ i (hi : i < block.length) (hi' : i < ranks.length),
      (ranks[i]'hi') = rank (block[i]'hi).name := fun i hi hi' =>
    List.getElem_map (fun d => rank d.name) (l := block) (h := hi')
  -- For each datatype `d`, `rankExists` gives its inhabited constructor `cw d`, over the set of
  -- names for a lower rank. `hwitness d hd` holds that constructor, and it holds the fact that
  -- each of its references to a block name has a lower rank.
  have hwitness : ∀ d ∈ block, ∃ cw ∈ d.constrs,
      (∀ ref ∈ constrRefs cw, ref ∈ block.map (·.name) → rank ref < rank d.name) := by
    intro d hd
    obtain ⟨dw, hdwget, cw, hcwmem, hcwlower⟩ := hrankwit d.name (List.mem_map.mpr ⟨d, hd, rfl⟩)
    have hdweq : dw = d :=
      Option.some.inj (hdwget.symm.trans (getType_push_self (hnew d hd) hnodup hd))
    subst hdweq
    exact ⟨cw, hcwmem, hcwlower⟩
  -- The set of names that the inhabited constructor of a datatype `d` draws from.
  let witPool : LDatatype Unit → List BlockRef := fun d =>
    visibleRefs (lowerRankHeaders ((blockHeaders block).zip ranks) (rank d.name)) d.typeArgs
  let fullPool : LDatatype Unit → List BlockRef := fun d =>
    visibleRefs (blockHeaders block) d.typeArgs
  -- The names of `blockHeaders block` are the names of `block`.
  have hbhnames : (blockHeaders block).map (·.name) = block.map (·.name) := by
    simp only [blockHeaders, List.map_map]; rfl
  -- **The lemmas about coverage**, for one datatype, one constructor and one argument.
  -- Coverage for the full set. Take an argument that is well-formed and whose variables are in
  -- scope. Then the full set holds each block name that appears in that argument.
  have hcover_full : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      ∀ d' ∈ block, TyNameAppears d'.name arg.2 →
        (d'.name, d'.typeArgs.map .ftvar) ∈ fullPool d := by
    intro d hd c hc arg harg d' hd' happ
    exact visibleRefs_cover_of_appears harrowB hd'
      ⟨{ name := d'.name, params := d'.typeArgs }, List.mem_map.mpr ⟨d', hd', rfl⟩, rfl, rfl⟩
      (hwf.argsWF d hd c hc arg harg) (hwf.argVarsScoped d hd c hc arg harg) happ
  -- Coverage for the set of names for a lower rank. A block name in an argument of the inhabited
  -- constructor has a lower rank, which `rankExists` gives. Therefore its header is a member of
  -- `lowerRankHeaders`.
  have hcover_wit : ∀ d ∈ block, ∀ cw ∈ d.constrs,
      (∀ ref ∈ constrRefs cw, ref ∈ block.map (·.name) → rank ref < rank d.name) →
      ∀ arg ∈ cw.args, ∀ d' ∈ block, TyNameAppears d'.name arg.2 →
        (d'.name, d'.typeArgs.map .ftvar) ∈ witPool d := by
    intro d hd cw hcw hcwlower arg harg d' hd' happ
    have hrefmem : d'.name ∈ constrRefs cw := by
      rw [constrRefs, List.mem_flatMap]
      exact ⟨arg, harg, mem_getTypeRefs_of_tyNameAppears happ⟩
    have hlt : rank d'.name < rank d.name :=
      hcwlower d'.name hrefmem (List.mem_map.mpr ⟨d', hd', rfl⟩)
    -- The header of `d'` with its rank is a member of `lowerRankHeaders … (rank d.name)`.
    have hd'hdr : (({ name := d'.name, params := d'.typeArgs } : TypeConstructor), rank d'.name) ∈
        (blockHeaders block).zip ranks := by
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hd'
      have hjr : j < ranks.length := by rw [hrankslen]; exact hj
      have hjb : j < (blockHeaders block).length := by rw [blockHeaders_length]; exact hj
      have hzip : ((blockHeaders block).zip ranks)[j]'(by
          rw [List.length_zip, blockHeaders_length, hrankslen, Nat.min_self]; exact hj) =
          ((blockHeaders block)[j]'hjb, ranks[j]'hjr) := List.getElem_zip
      have hbh : (blockHeaders block)[j]'hjb = { name := d'.name, params := d'.typeArgs } := by
        rw [blockHeaders_getElem block j hjb hj, hjeq]
      have hrk : (ranks[j]'hjr) = rank d'.name := by rw [hranks_get j hj hjr, hjeq]
      rw [hbh, hrk] at hzip
      exact hzip ▸ List.getElem_mem _
    have hmemlower : ({ name := d'.name, params := d'.typeArgs } : TypeConstructor) ∈
        lowerRankHeaders ((blockHeaders block).zip ranks) (rank d.name) :=
      (lowerRankHeaders_mem_iff _ _ _).mpr ⟨rank d'.name, hd'hdr, hlt⟩
    exact visibleRefs_cover_of_appears harrowB hd' ⟨_, hmemlower, rfl, rfl⟩
      (hwf.argsWF d hd cw hcw arg harg) (hwf.argVarsScoped d hd cw hcw arg harg) happ
  -- **One size for each datatype.** Take each `d ∈ block` with its inhabited constructor `cw`.
  -- Then a size `S` is present. At that size, the generator can make each argument of `cw` from
  -- `witPool d`, and it can make each constructor argument of `d` from `fullPool d`.
  -- `exists_uniform_bound` with `genArgTy_mono` collects the sizes of the arguments into `S`.
  have hthresh : ∀ d ∈ block, ∀ cw ∈ d.constrs,
      (∀ ref ∈ constrRefs cw, ref ∈ block.map (·.name) → rank ref < rank d.name) →
      ∃ S,
      (∀ arg ∈ cw.args, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons (witPool d) d.typeArgs true S)) ∧
      (∀ c ∈ d.constrs, ∀ arg ∈ c.args, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons (fullPool d) d.typeArgs true S)) := by
    intro d hd cw hcw hcwlower
    -- The arguments of the inhabited constructor, from `witPool d`. The generator can make
    -- each of them at some size.
    have hwit_some : ∀ arg ∈ cw.args, ∃ s, arg.2 ∈ SetGen.support
        (genArgTy (G := SetGen.Set) baseTypes tyCons (witPool d) d.typeArgs true s) := by
      intro arg harg
      exact genArgTy_complete_of_wf_partial hn hvocab arg.2
        (fun d' hd' happ => hcover_wit d hd cw hcw hcwlower arg harg d' hd' happ)
        (hwf.argsWF d hd cw hcw arg harg) (hwf.argVarsScoped d hd cw hcw arg harg)
        (argsWellKinded_ty hwf d hd cw hcw arg harg) (hbv d hd cw hcw arg harg) true (by simp)
    obtain ⟨Sw, hSw⟩ := exists_uniform_bound cw.args
      (fun arg s => arg.2 ∈ SetGen.support
        (genArgTy (G := SetGen.Set) baseTypes tyCons (witPool d) d.typeArgs true s))
      (fun _ _ _ _ hle hs => genArgTy_mono _ hs hle) hwit_some
    -- Each constructor argument, from `fullPool d`. The generator can make each of them at some
    -- size. Put the pairs of a constructor and an argument into one list.
    let fullArgs : List (LMonoTy) := d.constrs.flatMap (fun c => c.args.map (·.2))
    have hfull_some : ∀ ty ∈ fullArgs, ∃ s, ty ∈ SetGen.support
        (genArgTy (G := SetGen.Set) baseTypes tyCons (fullPool d) d.typeArgs true s) := by
      intro ty hty
      simp only [fullArgs, List.mem_flatMap, List.mem_map] at hty
      obtain ⟨c, hc, arg, harg, rfl⟩ := hty
      exact genArgTy_complete_of_wf_partial hn hvocab arg.2
        (fun d' hd' happ => hcover_full d hd c hc arg harg d' hd' happ)
        (hwf.argsWF d hd c hc arg harg) (hwf.argVarsScoped d hd c hc arg harg)
        (argsWellKinded_ty hwf d hd c hc arg harg) (hbv d hd c hc arg harg) true (by simp)
    obtain ⟨Sf, hSf⟩ := exists_uniform_bound fullArgs
      (fun ty s => ty ∈ SetGen.support
        (genArgTy (G := SetGen.Set) baseTypes tyCons (fullPool d) d.typeArgs true s))
      (fun _ _ _ _ hle hs => genArgTy_mono _ hs hle) hfull_some
    refine ⟨max Sw Sf, ?_, ?_⟩
    · intro arg harg; exact genArgTy_mono _ (hSw arg harg) (Nat.le_max_left _ _)
    · intro c hc arg harg
      have : arg.2 ∈ fullArgs := by
        simp only [fullArgs, List.mem_flatMap, List.mem_map]
        exact ⟨c, hc, arg, harg, rfl⟩
      exact genArgTy_mono _ (hSf arg.2 this) (Nat.le_max_right _ _)
  -- **Collect one size `N`** for the full block. For one chosen inhabited constructor of `d`,
  -- the property `P d S` holds both facts about the size `S`.
  obtain ⟨N, hN⟩ := exists_uniform_bound block
      (fun d S => ∃ cw ∈ d.constrs,
        (∀ ref ∈ constrRefs cw, ref ∈ block.map (·.name) → rank ref < rank d.name) ∧
        (∀ arg ∈ cw.args, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons (witPool d) d.typeArgs true S)) ∧
        (∀ c ∈ d.constrs, ∀ arg ∈ c.args, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons (fullPool d) d.typeArgs true S)))
      (fun d _ s s' hle hS => by
        obtain ⟨cw, hcw, hcwl, hw, hf⟩ := hS
        exact ⟨cw, hcw, hcwl, fun arg harg => genArgTy_mono _ (hw arg harg) hle,
          fun c hc arg harg => genArgTy_mono _ (hf c hc arg harg) hle⟩)
      (fun d hd => by
        obtain ⟨cw, hcw, hcwl⟩ := hwitness d hd
        obtain ⟨S, hSw, hSf⟩ := hthresh d hd cw hcw hcwl
        exact ⟨S, cw, hcw, hcwl, hSw, hSf⟩)
  -- Apply the completeness with the ranks as a parameter, at `maxSize := N`.
  refine ⟨N, genMutuallyRecursiveDatatypes_complete hwf.nonempty hcount hnodup hnamesIdent
    hnamesFresh hparamsLen hparamsNodup hparamsIdent hparamsFresh ranks hrankslen hranksle ?_⟩
  intro i hi hi'
  have hd : (block[i]'hi) ∈ block := List.getElem_mem hi
  obtain ⟨cw, hcw, _hcwl, hNwit, hNfull⟩ := hN (block[i]'hi) hd
  have hperm : (cw :: (block[i]'hi).constrs.erase cw).Perm (block[i]'hi).constrs :=
    (List.perm_cons_erase hcw).symm
  refine ⟨cw, (block[i]'hi).constrs.erase cw, hperm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; exact hctors_nf _ hd c (hperm.mem_iff.mp hc)
  · intro c hc; exact hctors_len _ hd c (hperm.mem_iff.mp hc)
  · intro nm' hnm'; exact hnames_ident _ hd nm' ((ctorsNames_perm hperm).mem_iff.mp hnm')
  · exact (ctorsNames_perm hperm).nodup_iff.mpr (hnames_nd _ hd)
  · intro nm' hnm'; exact hnames_fresh _ hd nm' ((ctorsNames_perm hperm).mem_iff.mp hnm')
  · have hlen := hreclen _ hd
    have : ((block[i]'hi).constrs.erase cw).length = (block[i]'hi).constrs.length - 1 :=
      List.length_erase_of_mem hcw
    omega
  · -- The arguments of the inhabited constructor, from the set of names for a lower rank, at
    -- the size `N`. Change `ranks[i]` into `rank`.
    intro arg harg
    have hrankget : (ranks[i]'hi') = rank (block[i]'hi).name := hranks_get i hi hi'
    rw [hrankget]
    exact hNwit arg harg
  · -- The arguments of the other constructors, from the full set, at the size `N`.
    intro c hc arg harg
    exact hNfull c (hperm.mem_iff.mp (List.mem_cons_of_mem _ hc)) arg harg

end Completeness

/-! ### Name reachability, discharged at a use site

The example below is a machine-checked witness that the side condition on name reachability is
gone, and is not only in a different place. It shows membership in the support of `genFreshName`
for a concrete name, with no hypothesis `∈ support genIdentName` at any point. The equivalent
tightness checks for `genIdentName` are in `FunctionHasTypeAGen/IdentNameTests.lean`. Those checks
include the names that the generator provably cannot draw. -/

example : "myType" ∈ SetGen.support (genFreshName (G := SetGen.Set) ["bool", "int"]) := by
  apply genFreshName_complete_of_syntactic
  · decide +kernel
  · rw [isReservedKeyword_eq_list_contains]; decide +kernel
  · decide +kernel

end DatatypeGen
