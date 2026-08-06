import StrataGenerators.SetGen
import StrataGenerators.DatatypeGen
import Strata.DL.Lambda.DatatypeWF
import Strata.Languages.Core.DatatypeTypeSpec
import Strata.Languages.Core.Factory

open Lambda RandomChoice ArbNat ArbChar ArbString SetGen

/-!
# Soundness and completeness of the algebraic data type generator

This file proves `DatatypeGen`'s type generator sound and complete with respect
to the declarative typing specification in `Strata.DL.Lambda.DatatypeWF`
(`Lambda.ConstrArgWF`, the argument half of `Core.TypeSpec.MutualADTWF`).

The generator now produces *mutually recursive* blocks, so the spec is applied to
a whole `block : MutualDatatype Unit` rather than a singleton `[d]`. The move from
one datatype to a mutual block relaxes the well-formedness conditions from
equality against a single `selfName` to *membership in the set of block names*:
where the old code compared a head symbol against one datatype name, the relations
`NotNested` / `StrictPosUnif` / `UniformOccur` (all already `block`-parameterized
in the spec) compare it against `block.map (·.name)`.

## The recursive-occurrence vocabulary: `blockRefs` and `BlockRefsWF`

The type generators (`genLeafTy` / `genArgTy`) emit a recursive occurrence by
drawing from `blockRefs : List BlockRef`, the block members the datatype under
construction may refer to (each `(name, args)` with `args` the referee's own type
arguments as `ftvar`s). What the soundness proof needs to know about that list is
bundled in `BlockRefsWF block tyParams blockRefs`:

* `mem` — every reference names an actual block member (for `NotNested.headBlock`
  and the `refsKnown` block-name disjunct);
* `uniform` — a reference to `d`'s name applies it to *exactly* `d.typeArgs`
  (for `UniformOccur.self`);
* `ftvarArgs` — a reference's arguments are all `ftvar`s (so it is never nested
  and contributes no type references beyond its head name);
* `scoped` — a reference's argument variables are all declared type parameters
  (for `argVarsScoped`).

`genMutuallyRecursiveDatatypes` supplies `visibleRefs`, which satisfies all four by construction
(`visibleRefs_blockRefsWF`).

## Structure

**Part 1 — spec lemmas.** Facts about `DatatypeWF` alone. The key one is
`absent_constrArgWF`: if *no* block name occurs in a type, that type is
automatically a well-formed constructor argument. This is what makes
`recCallsAllowed := false` pay off, since `genArgTy` with that flag produces
exactly such types (no block name anywhere).

**Part 2 — support decomposition (no auxiliary inductive).** One-step lemmas
`genLeafTy_mem_iff` and `genArgTy_mem_iff` describe each generator's support as a
plain disjunction: the leaf/arrow/application alternatives of the generator's
`oneOf`, with the recursive positions referring back to the support at `size / 2`.
There is *no* size-indexed inductive predicate — the soundness and completeness
proofs each do their own strong induction on `size` through these lemmas.

**Part 3 — soundness with respect to the typing spec.** `genArgTy_constrArgWF`:
everything in the support is `ConstrArgWF block`, proved by strong induction on
`size` (`genArgTy_notNested` / `genArgTy_strictPosUnif` / `genArgTy_absent`).
`genMutuallyRecursiveDatatypes`'s output then satisfies all nine fields of `MutualADTWF`. This is
also where the reserved-name discipline is cashed in: `namesOk_of_fresh` turns
"each datatype's name was drawn fresh against `initialReserved`" into the side
conditions the spec needs.

## Completeness against `MutualADTWF`, with a single arity side condition

The generator's support is a strict subset of `MutualADTWF`'s constructor-argument
types, so completeness needs *some* extra hypotheses. The point of this file's
completeness half is that all but one of those hypotheses are *already fields of
`MutualADTWF`*: only a single genuinely new side condition is required, and it
concerns exactly the one discipline `MutualADTWF` does not enforce — the **arity**
of applied type constructors.

`MutualADTWF`'s `refsKnown` is stated via `getTypeRefs`, which collects only the
*names* of referenced type constructors and discards their argument count. So
`MutualADTWF C block` accepts an ill-kinded argument type like `Sequence a a`
(applying the arity-1 `Sequence` to two arguments): the name `"Sequence"` resolves,
every other field holds vacuously, yet the generator — whose application branch
draws `vectorOf arity` arguments — never produces it. See
`docs/mutualadtwf-arity-gap.md` for the full write-up of this spec gap.

The single new side condition is `ArityOk` (a `def`, not an inductive relation),
recursing on the *shape* of a type to require every applied type constructor to be
used at its declared arity. Every *other* gap between `MutualADTWF` and the
generator is discharged by an existing `MutualADTWF` field:

| generator restriction | `MutualADTWF` field that supplies it |
| --- | --- |
| free type variables are among `d.typeArgs` | `argVarsScoped` |
| recursive occurrences are a block name applied to exactly its `typeArgs` | `argsWF` (`StrictPosUnif` / `UniformOccur.self`) |
| strict positivity, no nesting | `argsWF` (`ConstrArgWF`) |
| referenced names resolve | `refsKnown` (against a concrete ambient context) |
| **application arity is correct** | **none — this is `ArityOk`** |

* **Soundness** — `genArgTy_constrArgWF` / `genMutuallyRecursiveDatatypesOrdered_MutualADTWF`: everything
  in the support satisfies all nine fields of `Core.TypeSpec.MutualADTWF`.
* **Completeness** — `genArgTy_complete_of_MutualADTWF`: every constructor-argument
  type of a block that is `MutualADTWF` *and* satisfies `ArityOk` is reachable,
  at *some* size (existential budget; `genArgTy_mono` / `genArgTy_common_size`
  align subterm budgets), *provided* the block's own references are visible to the
  generator (`BlockRefsWF`).

`not_complete_without_arity` exhibits why the `ArityOk` hypothesis cannot be
dropped: `Sequence a a` satisfies every field of `MutualADTWF` (it is even
well-scoped) but is unreachable, and it is exactly what `ArityOk` rejects.
-/

namespace DatatypeGen

/-! ## Part 1: lemmas about the typing spec alone

These mention only `Lambda.DatatypeWF` notions, never a generator. -/

section SpecLemmas

/-- `LMonoTys.freeVars` is the `flatMap` of `LMonoTy.freeVars` over the list — the
    form convenient for reasoning argument-by-argument. -/
theorem freeVars_tcons_eq_flatMap (k : String) (args : LMonoTys) :
    LMonoTy.freeVars (.tcons k args) = args.flatMap LMonoTy.freeVars := by
  rw [LMonoTy.freeVars]
  induction args with
  | nil => simp [LMonoTys.freeVars]
  | cons h t ih => simp [LMonoTys.freeVars, ih]

/-- The free variables of `vs` mapped to `ftvar`s are exactly `vs`. -/
theorem freeVars_map_ftvar (vs : List TyIdentifier) :
    LMonoTys.freeVars (vs.map LMonoTy.ftvar) = vs := by
  induction vs with
  | nil => simp [LMonoTys.freeVars]
  | cons h t ih => simp [LMonoTy.freeVars, ih]

/-- If `n` is absent from `n1 args`, it is absent from each argument. -/
theorem absent_of_mem_args {n n1 : String} {args : LMonoTys} {t : LMonoTy}
    (h : TyNameAbsent n (.tcons n1 args)) (ht : t ∈ args) : TyNameAbsent n t :=
  fun hap => h (.arg n1 args t ht hap)

/-- If `n` is absent from `n1 args`, then `n1` is not `n` (else it would be the head). -/
theorem ne_of_absent {n n1 : String} {args : LMonoTys}
    (h : TyNameAbsent n (.tcons n1 args)) : n1 ≠ n := by
  intro heq; subst heq; exact h (.head args)

/-- **Inversion of `TyNameAppears` at a `.tcons`.** An occurrence of `n` in
    `n1 args` is either `n1` being `n` itself, or an occurrence in one of the
    arguments. Stated as a lemma (rather than `cases`) so it applies when `n` is a
    projection like `d.name`, where dependent elimination on the head would
    fail. -/
theorem tyNameAppears_tcons_inv {n n1 : String} {args : LMonoTys}
    (h : TyNameAppears n (.tcons n1 args)) :
    n1 = n ∨ ∃ t ∈ args, TyNameAppears n t := by
  generalize hty : LMonoTy.tcons n1 args = t at h
  cases h with
  | head as => injection hty with hn _; exact Or.inl hn
  | arg n' as t ht hat =>
    injection hty with _ has; subst has
    exact Or.inr ⟨t, ht, hat⟩

/-- A type from which `n` is absent is *vacuously* uniform in `n`: there are no
    occurrences of `n` to check, so any `uargs` will do. -/
theorem absent_uniform {n : String} {uargs : LMonoTys} {ty : LMonoTy}
    (h : TyNameAbsent n ty) : UniformOccur n uargs ty := by
  induction ty with
  | ftvar v => exact .ftvar v
  | bitvec sz => exact .bitvec sz
  | tcons n1 args ih =>
    exact .other n1 args (ne_of_absent h) (fun t ht => ih t ht (absent_of_mem_args h ht))

/-- No name of any datatype in `block` occurs in `ty`. The mutual-block
    generalization of `TyNameAbsent d.name ty`: it is what a type produced under
    `recCallsAllowed := false` satisfies, and what makes such a type automatically
    a well-formed constructor argument (`absent_constrArgWF`). -/
def BlockAbsent (block : MutualDatatype Unit) (ty : LMonoTy) : Prop :=
  ∀ d ∈ block, TyNameAbsent d.name ty

/-- `BlockAbsent` is inherited by every argument of an application. -/
theorem blockAbsent_of_mem_args {block : MutualDatatype Unit} {n1 : String}
    {args : LMonoTys} {t : LMonoTy}
    (h : BlockAbsent block (.tcons n1 args)) (ht : t ∈ args) : BlockAbsent block t :=
  fun d hd => absent_of_mem_args (h d hd) ht

/-- If every block name is absent from `n1 args`, then `n1` is not a block name
    (else it would be the head of a forbidden occurrence). -/
theorem head_not_mem_of_blockAbsent {block : MutualDatatype Unit} {n1 : String}
    {args : LMonoTys} (h : BlockAbsent block (.tcons n1 args)) :
    n1 ∉ block.map (·.name) := by
  intro hmem
  obtain ⟨d, hd, hname⟩ := List.mem_map.mp hmem
  exact h d hd (hname ▸ .head args)

/-- A type from which every block name is absent contains no nested occurrence of a
    block datatype, trivially: the offending pattern (a block datatype inside
    another type constructor's arguments) requires an occurrence in the first
    place. -/
theorem absent_notNested {block : MutualDatatype Unit} {ty : LMonoTy}
    (h : BlockAbsent block ty) : NotNested block ty := by
  induction ty with
  | ftvar v => exact .ftvar v
  | bitvec sz => exact .bitvec sz
  | tcons n1 args ih =>
    by_cases hbin : IsBinaryArrow (LMonoTy.tcons n1 args)
    · -- A binary arrow: recurse into both sides (the spec matches `.arrow` first).
      obtain ⟨t1, t2, heq⟩ := hbin
      rw [LMonoTy.arrow] at heq
      injection heq with hn hl
      subst hn; subst hl
      exact .arrow t1 t2 (ih t1 (by simp) (blockAbsent_of_mem_args h (by simp)))
                         (ih t2 (by simp) (blockAbsent_of_mem_args h (by simp)))
    · exact .headOther n1 args hbin (head_not_mem_of_blockAbsent h)
        (fun d' hd' a ha => absent_of_mem_args (h d' hd') ha)
        (fun a ha => ih a ha (blockAbsent_of_mem_args h ha))

/-- A type from which every block name is absent is strictly positive and uniform
    for `block`, again vacuously. -/
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

/-- **Key spec lemma.** A type in which no block name occurs is automatically a
    well-formed constructor argument for `block`. Both halves of `ConstrArgWF` are
    about *occurrences* of block datatypes, so with no occurrences there is nothing
    to violate.

    This is why `DatatypeGen.genArgTy` threads `recCallsAllowed := false` into the
    domain of every arrow and the arguments of every type constructor: every type
    produced under that flag discharges its well-formedness obligation via this
    lemma alone. -/
theorem absent_constrArgWF {block : MutualDatatype Unit} {ty : LMonoTy}
    (h : BlockAbsent block ty) : ConstrArgWF block ty :=
  ⟨absent_notNested h, absent_strictPosUnif h⟩

/-! ### Permutation invariance of the well-formedness relations

The relations `NotNested` / `StrictPosUnif` consult `block` only through
`block.map (·.name)` (head guards) and `∀ d ∈ block` (absence / uniformity) — both
`Perm`-invariant. So all three transfer along a block permutation, giving
`constrArgWF_perm`. These feed the `argsWF` case of `MutualADTWF_perm`. -/

/-- `NotNested` transfers along a block permutation. By induction on the
    derivation, swapping `block` for `block'` at each block-name-set / membership
    site via the permutation. -/
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

/-- `StrictPosUnif` transfers along a block permutation. -/
theorem strictPosUnif_perm {block block' : MutualDatatype Unit} {ty : LMonoTy}
    (hperm : block.Perm block') (h : StrictPosUnif block ty) : StrictPosUnif block' ty := by
  induction h with
  | arrow t1 t2 habs _ ih =>
    exact .arrow t1 t2 (fun d hd => habs d (hperm.mem_iff.mpr hd)) ih
  | base ty hbin huni =>
    exact .base ty hbin (fun d hd => huni d (hperm.mem_iff.mpr hd))

/-- `ConstrArgWF` transfers along a block permutation (both halves). -/
theorem constrArgWF_perm {block block' : MutualDatatype Unit} {ty : LMonoTy}
    (hnames : (block.map (·.name)).Perm (block'.map (·.name)))
    (hperm : block.Perm block') (h : ConstrArgWF block ty) : ConstrArgWF block' ty :=
  ⟨notNested_perm hnames hperm h.1, strictPosUnif_perm hperm h.2⟩

end SpecLemmas

/-! ## Part 2: characterization of the generator's support

We describe what each generator can produce as *plain disjunctions* over the
support (`genLeafTy_mem_iff`, `genArgTy_mem_iff`) — no auxiliary inductive
predicate. The soundness and completeness proofs then do their own strong
induction on `size` through these one-step lemmas. -/

section Support

/-- Every natural number is in the support of `Nat.arbitrary` at `SetGen.Set`:
    the width generator behind `pickBitvecWidth` reaches every width (issue #38).
    (Mirrors the private lemma of the same shape in `HasTypeAGen.lean`; restated
    here because that one is not exported.) -/
private theorem Nat_arbitrary_support_set (n : Nat) :
    n ∈ SetGen.support (Nat.arbitrary (G := SetGen.Set)) := by
  induction n with
  | zero => rw [Nat.arbitrary]; simp
  | succ n ih =>
    rw [Nat.arbitrary]
    simp only [mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff]
    exact Or.inr ⟨n, ih, rfl⟩

/-- `genBaseTy` produces exactly the bitvectors of *any* width and the nullary
    applications of a `baseTypes` name. -/
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


/-- Support of the recursive-occurrence sub-generator: it produces exactly the
    uniform occurrences `.tcons p.1 p.2` of the block references `p`. -/
theorem genRecOcc_mem_iff (br : BlockRef) (brs : List BlockRef) (t : LMonoTy) :
    t ∈ SetGen.support
      ((do let (n, args) ← elements (br :: brs) (List.cons_ne_nil br brs)
           pure (.tcons n args)) : SetGen.Set LMonoTy) ↔
    ∃ p ∈ br :: brs, t = .tcons p.1 p.2 := by
  simp only [mem_support_bind_iff, mem_support_pure_iff,
             mem_support_elements_iff (List.cons_ne_nil br brs)]

/-- **Leaf support as a plain disjunction** (no inductive predicate). Every type
    in `genLeafTy`'s support is a bitvector of any width, a base type, one of the
    datatype's own type parameters, or — under `recCallsAllowed` — a uniform
    recursive occurrence `br.1 br.2` of some block reference `br ∈ blockRefs`. The
    leaf basis of the soundness/completeness inductions below. -/
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

/-! ### Support of `genArgTy`

`genArgTy` offers, at every `size ≠ 0`: an arrow, a leaf, or an application of a
known type constructor. At `size = 0` only the leaf. The two well-formedness
critical `false`s of the generator show up as the `false` recursion on the domain
of an arrow and on the arguments of an application.

We characterize the support with a *one-step* decomposition lemma
(`genArgTy_mem_iff`) whose right-hand side is a plain disjunction referring back
to `SetGen.support (genArgTy … (size/2))` — no auxiliary inductive predicate. The
soundness and completeness theorems then do their own strong induction on `size`
through this lemma. -/

/-- **One-step support decomposition of `genArgTy`** (no inductive predicate).
    At `size = 0` the support is exactly the leaves; above that it additionally
    contains arrows (domain generated at flag `false`, codomain at the incoming
    flag) and applications of a `tyCons` constructor at its arity (arguments at
    flag `false`). The recursive positions refer back to the support at `size/2`. -/
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


/-- **`genArgTy`'s support is monotone in the reference pool.** Enlarging
    `blockRefs` (keeping every existing reference) only adds reachable types: the
    recursive-occurrence leaf is the sole place `blockRefs` is consulted, and a
    larger pool offers more such leaves. Strong induction on `size` through the
    one-step decomposition. Used to lift the witness constructor's argument types
    (drawn over the small `inhabRefs` pool) up to the full `visibleRefs` pool, so
    the soundness lemmas need not distinguish the two. -/
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
    · -- Leaf: only the recursive-occurrence disjunct mentions `blockRefs`.
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

/-! ## Part 3: soundness with respect to the typing spec

We now show `ty ∈ support (genArgTy …) → ConstrArgWF [d] ty`, by strong induction
on `size` through `genArgTy_mem_iff`: everything `genArgTy` produces is a
well-formed constructor argument.

### The side conditions, and why they are needed

Because `LMonoTy.arrow t1 t2` is *definitionally* `LMonoTy.tcons "arrow" [t1, t2]`,
a type constructor literally named `"arrow"` is indistinguishable from a real
arrow. The spec's `NotNested` / `StrictPosUnif` match `.arrow` before the general
`.tcons` case, so we must rule it out:

* no block name is `"arrow"` — otherwise a recursive occurrence `n args` would
  masquerade as an arrow whenever `args` has length 2.
* every `tyCons` name is `≠ "arrow"` — otherwise an application of arity 2 would
  masquerade as an arrow.

Two further conditions rule out name shadowing of the block's datatypes:

* no `tyCons` name is a block name — otherwise an application would look like a
  (possibly non-uniform) recursive occurrence, breaking uniformity.
* no `baseTypes` name is a block name — otherwise the leaf `.tcons b []` would
  read as a recursive occurrence applied to no arguments, which is non-uniform
  whenever the referenced datatype has type parameters.

These are bundled as `NamesOk`, now stated against the *set* of block names
(`block.map (·.name)`) rather than a single `selfName`. Three of the four are
exactly what the generator's reserved-name discipline buys: `initialReserved`
contains `"arrow"` and every `baseTypes` / `tyCons` name, and each block name is
drawn fresh against it — see `namesOk_of_fresh`. The remaining condition
(`tyCon_ne_arrow`) constrains the *caller-supplied* pool rather than any generated
name, so it stays a hypothesis; `defaultTyCons` satisfies it by `decide`.

A second bundle, `BlockRefsWF`, records what the soundness proof needs to know
about the recursive-occurrence pool `blockRefs`: every reference names an actual
block member (`mem`), a reference to a block member applies it to exactly its own
type arguments (`uniform`), and a reference's arguments are all type variables
(`ftvarArgs`). `genMutuallyRecursiveDatatypes` supplies these by construction via `visibleRefs`. -/

section Soundness

/-- Side conditions on the generator's name parameters, needed because
    `LMonoTy.arrow` is a `.tcons` with the reserved name `"arrow"`, and because
    the generator's name pools are caller-supplied. Stated against the set of
    block names `blockNames` (`block.map (·.name)`). -/
structure NamesOk (baseTypes : List String) (tyCons : List KnownTyCon)
    (blockNames : List String) : Prop where
  /-- No block name is the reserved arrow constructor. -/
  block_ne_arrow : ∀ n ∈ blockNames, n ≠ "arrow"
  /-- No applied type constructor is the reserved arrow constructor. -/
  tyCon_ne_arrow : ∀ kc ∈ tyCons, kc.1 ≠ "arrow"
  /-- No applied type constructor shadows a block name. -/
  tyCon_notMem : ∀ kc ∈ tyCons, kc.1 ∉ blockNames
  /-- No base type shadows a block name. -/
  base_notMem : ∀ b ∈ baseTypes, b ∉ blockNames

/-- What the soundness proof needs to know about the recursive-occurrence pool
    `blockRefs` for a given block and enclosing type-parameter list `tyParams`.
    `visibleRefs` satisfies all four fields by construction
    (`visibleRefs_blockRefsWF`). -/
structure BlockRefsWF (block : MutualDatatype Unit) (tyParams : List TyIdentifier)
    (blockRefs : List BlockRef) : Prop where
  /-- Every reference names an actual block datatype. -/
  mem : ∀ br ∈ blockRefs, br.1 ∈ block.map (·.name)
  /-- A reference to a block datatype applies it to exactly its own type
      arguments (uniformity). -/
  uniform : ∀ br ∈ blockRefs, ∀ d ∈ block, d.name = br.1 → br.2 = d.typeArgs.map .ftvar
  /-- A reference's arguments are all type variables (so it is never nested and
      contributes no references beyond its head name). -/
  ftvarArgs : ∀ br ∈ blockRefs, ∀ a ∈ br.2, ∃ v, a = LMonoTy.ftvar v
  /-- A reference's argument variables are all declared type parameters (so a
      recursive occurrence introduces no unscoped variable — `argVarsScoped`). -/
  argsScoped : ∀ br ∈ blockRefs, ∀ v ∈ LMonoTys.freeVars br.2, v ∈ tyParams

/-- `.tcons k args` with `k ≠ "arrow"` is not a binary arrow. -/
theorem not_isBinaryArrow_of_ne {k : String} {args : LMonoTys} (h : k ≠ "arrow") :
    ¬ IsBinaryArrow (.tcons k args) := by
  rintro ⟨t1, t2, heq⟩
  rw [LMonoTy.arrow] at heq
  injection heq with hn _
  exact h hn

/-- **`ConstrArgWF` of an arrow decomposes**, given no block name is `"arrow"` (so
    the `.arrow` cases of `NotNested`/`StrictPosUnif` are the only applicable
    ones): every block name is absent from the domain, the domain is itself
    well-formed, and the codomain is well-formed. The mirror of `absent`/`arrow`
    building used in the soundness direction, packaged for the completeness
    recursion. -/
theorem constrArgWF_arrow {block : MutualDatatype Unit} {t1 t2 : LMonoTy}
    (harrow : ∀ d ∈ block, d.name ≠ "arrow")
    (h : ConstrArgWF block (.arrow t1 t2)) :
    BlockAbsent block t1 ∧ ConstrArgWF block t1 ∧ ConstrArgWF block t2 := by
  obtain ⟨hnn, hsp⟩ := h
  -- NotNested: only the `.arrow` constructor applies.
  have hnn' : NotNested block t1 ∧ NotNested block t2 := by
    cases hnn with
    | arrow _ _ h1 h2 => exact ⟨h1, h2⟩
    | headBlock _ _ hmem =>
      obtain ⟨d, hd, hname⟩ := List.mem_map.mp hmem
      exact absurd hname (harrow d hd)
    | headOther _ _ hbin _ _ _ => exact absurd ⟨t1, t2, rfl⟩ hbin
  -- StrictPosUnif: only the `.arrow` constructor applies.
  have hsp' : BlockAbsent block t1 ∧ StrictPosUnif block t2 := by
    cases hsp with
    | arrow _ _ hab hsp2 => exact ⟨hab, hsp2⟩
    | base _ hbin _ => exact absurd ⟨t1, t2, rfl⟩ hbin
  exact ⟨hsp'.1, ⟨hnn'.1, absent_strictPosUnif hsp'.1⟩, ⟨hnn'.2, hsp'.2⟩⟩

/-- **`ConstrArgWF` forces recursive occurrences to be uniform.** A `d.name`-headed
    application (for `d` in the block) that is `ConstrArgWF block` must apply
    `d.name` to *exactly* `d.typeArgs.map .ftvar`. This is the `UniformOccur.self`
    discipline read back off the spec: `StrictPosUnif`'s `base` case demands
    uniformity of every block datatype, and the only uniform `d.name`-headed
    occurrence is the self-application. It is what lets the `ArityOk` side
    condition stay silent about block occurrences — their shape is already pinned
    by `ConstrArgWF`. -/
theorem constrArgWF_self_uniform {block : MutualDatatype Unit} {d : LDatatype Unit}
    {args : LMonoTys} (hd : d ∈ block)
    (harrow : ∀ d ∈ block, d.name ≠ "arrow")
    (h : ConstrArgWF block (.tcons d.name args)) :
    args = d.typeArgs.map .ftvar := by
  obtain ⟨_, hsp⟩ := h
  -- Generalize the indexed type so `StrictPosUnif` can be inverted.
  generalize hty : LMonoTy.tcons d.name args = t at hsp
  cases hsp with
  | arrow t1 t2 _ _ =>
    -- `.arrow` is `.tcons "arrow" [_, _]`, so this forces `d.name = "arrow"`.
    rw [LMonoTy.arrow] at hty
    injection hty with hn _
    exact absurd hn (harrow d hd)
  | base ty _ huni =>
    subst hty
    -- Uniformity of `d` (a block datatype): `.self` gives the args verbatim.
    cases huni d hd with
    | self => rfl
    | other n1 args1 hne _ => exact absurd rfl hne

/-- A base type is block-absent (given no base type shadows a block name). Split
    out because it is the one leaf case that needs `NamesOk`, and because it is
    reused in several places. -/
theorem base_absent {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {b : String}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hb : b ∈ baseTypes) : BlockAbsent block (.tcons b []) := by
  intro d hd hap
  cases hap with
  -- In this branch `b` is unified with `d.name`, so `b` is a block name — but
  -- `NamesOk` says no base type is a block name.
  | head _ => exact hn.base_notMem _ hb (List.mem_map.mpr ⟨d, hd, rfl⟩)
  | arg _ _ t ht _ => cases ht

/-- A leaf drawn with `recCallsAllowed := false` is block-absent. Reads off
    `genLeafTy_mem_iff`: at flag `false` the recursive-occurrence disjunct is
    excluded, and none of the surviving leaves contains a block name. -/
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

/-- **Every block name is absent from everything `genArgTy` can produce under
    `recCallsAllowed := false`.** This is the crucial property of the flag, and the
    premise that the arrow and other-type-constructor cases of the spec require.

    Proved by strong induction on `size` through the one-step support
    decomposition `genArgTy_mem_iff` — no auxiliary inductive relation. -/
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

/-- **The `NotNested` half**, directly on `genArgTy`'s support (either flag),
    by strong induction on `size` through `genArgTy_mem_iff`. -/
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
    · -- Leaf: read off `genLeafTy_mem_iff`.
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

/-- **The `StrictPosUnif` half**, directly on `genArgTy`'s support. The recursive
    occurrence leaf is where uniformity is discharged: the generator emits a block
    name applied to *exactly* that datatype's `typeArgs.map .ftvar`, precisely
    `UniformOccur.self` (via `BlockRefsWF.uniform`). -/
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
      · -- A recursive occurrence `br.1 br.2`. It is not a binary arrow (`br.1` is a
        -- block name, hence not `"arrow"`), and it is uniform in every block
        -- datatype: `.self` for the one it names, `.other` for the rest.
        have hmem := hbr.mem br hbrmem
        refine .base _ (not_isBinaryArrow_of_ne (hn.block_ne_arrow _ hmem)) ?_
        intro d' hd'
        by_cases hname : d'.name = br.1
        · -- The named datatype: `br.2 = d'.typeArgs.map .ftvar`, so `.self`.
          have huniform := hbr.uniform br hbrmem d' hd' hname
          rw [← hname, huniform]; exact .self
        · -- A different datatype: `.other`, arguments are all `ftvar`s.
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

/-- **Soundness on the generator's support:** anything `genArgTy` draws (for a
    block, at either flag) is a well-formed constructor-argument type. -/
theorem genArgTy_constrArgWF {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier} {rca : Bool} {size : Nat} {ty : LMonoTy}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hbr : BlockRefsWF block tyParams blockRefs)
    (h : ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
            tyParams rca size)) :
    ConstrArgWF block ty :=
  ⟨genArgTy_notNested hn hbr size h, genArgTy_strictPosUnif hn hbr size h⟩

/-! ### The reserved-name discipline

`genFreshName reserved` returns a name that is *not* in `reserved`. Everything
else in this section follows from that one fact plus the contents of
`initialReserved`. -/

/-- `fallbackName reserved` is one character longer than the longest reserved
    name. Reuses the shared `indexedFreshName_length` from
    `CmdHasTypeAGen/Core.lean` (`fallbackName` is `indexedFreshName` at index 0). -/
private theorem fallbackName_length (reserved : List String) :
    (fallbackName reserved).length = maxNameLength reserved + 1 := by
  simp [fallbackName, indexedFreshName_length]

/-- **The fallback name is never reserved.** It is strictly longer than every
    reserved name, so it cannot equal any of them. This is what makes
    `genFreshName` total: the random draw may collide, but the fallback cannot.

    The length bound is the shared `foldl_max_ge_of_mem` from
    `CmdHasTypeAGen/Core.lean` at `f := String.length`. -/
theorem fallbackName_not_mem (reserved : List String) :
    fallbackName reserved ∉ reserved := by
  intro hmem
  have hle := foldl_max_ge_of_mem String.length reserved _ hmem 0
  rw [fallbackName_length] at hle
  simp only [maxNameLength] at hle
  omega

/-- **`genFreshName` lives up to its name.** Every name in its support is absent
    from `reserved`: the random draw is returned only when it does not collide,
    and the fallback is never reserved. -/
theorem genFreshName_fresh (reserved : List String) :
    ∀ s ∈ SetGen.support (genFreshName (G := SetGen.Set) reserved), s ∉ reserved := by
  intro s hs
  simp only [genFreshName, mem_support_bind_iff, mem_support_ite_iff,
             mem_support_pure_iff] at hs
  obtain ⟨s', _, hbranch⟩ := hs
  rcases hbranch with ⟨_, rfl⟩ | ⟨hne, rfl⟩
  · exact fallbackName_not_mem reserved
  · -- `reserved.contains s' = false`, i.e. `s' ∉ reserved`.
    simpa using hne

/-- **A single fresh name satisfies the per-name `NamesOk` conditions.** A name
    drawn fresh against `initialReserved baseTypes tyCons` is not `"arrow"`, is no
    `tyCons` name, and is no `baseTypes` name — because that list contains all of
    them. Used pointwise by `namesOk_of_fresh` to establish the set-level bundle. -/
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

/-- **`NamesOk` from freshness.** If every block name was drawn fresh against
    `initialReserved baseTypes tyCons`, the whole block satisfies three of the four
    `NamesOk` conditions, because that list contains `"arrow"` and every
    `baseTypes` / `tyCons` name. The fourth (`tyCon_ne_arrow`) is a condition on
    the caller-supplied pool, so it is taken as a hypothesis. -/
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

/-- The default type constructor pool contains no constructor named `"arrow"`, so
    it discharges the one `NamesOk` condition that freshness does not. -/
theorem defaultTyCons_ne_arrow : ∀ kc ∈ defaultTyCons, kc.1 ≠ "arrow" := by
  decide

/-! ### Lifting to whole constructors and datatypes -/

/-- Support of `chooseNat lo hi`: exactly the naturals in `[lo, hi]`. -/
@[simp] theorem mem_support_chooseNat_iff {lo hi n : Nat} {h : lo ≤ hi} :
    n ∈ SetGen.support (chooseNat (G := SetGen.Set) lo hi h) ↔ lo ≤ n ∧ n ≤ hi := by
  simp only [chooseNat, mem_support_map_iff, mem_support_choose_iff]
  constructor
  · rintro ⟨u, ⟨hlo, hhi⟩, rfl⟩; exact ⟨hlo, hhi⟩
  · rintro ⟨hlo, hhi⟩; exact ⟨⟨⟨n, hlo, hhi⟩⟩, ⟨hlo, hhi⟩, rfl⟩

/-- Every argument type in a list drawn from `genConstrArgs` lies in the support
    of `genArgTy` at *some* size, so soundness lifts from types to constructors.
    (The size is existential because `genConstrArgs` draws a fresh
    `chooseNat 0 maxSize` per argument.)

    Field names are attached by zipping the freshly generated names against the
    types, so `List.of_mem_zip` recovers the type from a member of the result. -/
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
  -- The `pure` fixes both components; only the first is needed here.
  have hargs_eq : args = (fieldNames.zip argTys).map
      (fun p => ((⟨p.1, ()⟩ : Identifier Unit), p.2)) := (Prod.mk.inj hpair).1
  subst hargs_eq
  intro arg harg
  obtain ⟨⟨nm, ty⟩, hmem, rfl⟩ := List.mem_map.mp harg
  obtain ⟨size, _, hty⟩ := by
    simpa only [mem_support_bind_iff] using hall ty (List.of_mem_zip hmem).2
  exact ⟨size, hty⟩

/-- Every argument type of every constructor drawn from `genConstrs` lies in the
    support of `genArgTy` at some size. By induction on the number of
    constructors, since `genConstrs` recurses on it (threading the reserved-name
    list, which this statement does not need to mention). -/
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

/-! ### Reading off the shape of `genMutuallyRecursiveDatatypes`'s support

`genMutuallyRecursiveDatatypes` builds the block in two phases (headers, then bodies). We factor
its support decomposition out once: every datatype `d` in a generated block has a
name drawn fresh against `initialReserved` (which is what `NamesOk` needs), came
from a header whose parameters are `d.typeArgs`, and every one of its constructor
argument types comes from `genArgTy` — at the *visible references* for `d`'s
parameters — at some flag setting and size. -/

/-- Every name a `genFreshNames reserved n` draw produces is absent from
    `reserved`. By induction on `n`, using `genFreshName_fresh` at each step (the
    tail is drawn against an extended reserved list, which still contains the
    original). -/
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
    · -- The tail avoids `s :: reserved`, hence `reserved`.
      exact fun hmem => ih (s :: reserved) rest hrest nm hnm (by simp [hmem])

/-- `genFreshNames reserved n` always produces a list of length `n`. -/
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

/-- `genParamsList reserved maxTyParams n` always produces a list of `n`
    parameter lists. -/
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

/-- The header names built from `names.zip paramsList` are exactly `names`, when
    `names` is no longer than `paramsList`: zipping then projecting the first
    component (via `TypeConstructor.name`) recovers `names`. -/
theorem map_name_headers_of_length_le :
    ∀ (names : List String) (paramsList : List (List TyIdentifier)),
      names.length ≤ paramsList.length →
      (((names.zip paramsList).map
        (fun p => ({ name := p.1, params := p.2 } : Header))).map (·.name)) = names := by
  intro names
  induction names with
  | nil => intro paramsList _; rfl
  | cons a as ih =>
    intro paramsList hlen
    match paramsList, hlen with
    | b :: bs, hlen =>
      simp only [List.zip_cons_cons, List.map_cons, ih bs (by simpa using hlen)]

/-- The names a `genFreshNames reserved n` draw produces are pairwise distinct:
    each name is added to the reserved list before the tail is drawn, and
    `genFreshNames_fresh` says the tail then avoids it. -/
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
    -- `s` is not in the tail: the tail avoids `s :: reserved`, which contains `s`.
    exact fun hmem => genFreshNames_fresh _ _ _ hrest s hmem (by simp)

/-- Membership in `visibleRefs headers params`: a block reference `br` is visible
    exactly when it comes from a header whose parameters are a subset of `params`,
    as the uniform occurrence `(h.name, h.params.map .ftvar)`. -/
theorem visibleRefs_mem_iff (headers : List Header) (params : List TyIdentifier)
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

/-- `visibleRefs` is monotone in its header list: references visible against a
    sub-list of headers are visible against the whole. Discharges the `hsub`
    premise of `genConstructors_shape` (the witness pool `visibleRefs done` is a
    subset of the full `visibleRefs allHeaders`). -/
theorem visibleRefs_mono {headers headers' : List Header} {params : List TyIdentifier}
    (hsub : ∀ h ∈ headers, h ∈ headers') :
    ∀ br ∈ visibleRefs headers params, br ∈ visibleRefs headers' params := by
  intro br hbr
  obtain ⟨h, hh, hpsub, rfl⟩ := (visibleRefs_mem_iff _ _ _).mp hbr
  exact (visibleRefs_mem_iff _ _ _).mpr ⟨h, hsub h hh, hpsub, rfl⟩

/-- Two headers of a list with pairwise-distinct names that share a name are
    equal. The uniqueness fact behind `visibleRefs_blockRefsWF.uniform`. -/
theorem header_unique_of_nodup {headers : List Header} :
    ∀ {h h' : Header}, (headers.map (·.name)).Nodup → h ∈ headers → h' ∈ headers →
      h.name = h'.name → h = h' := by
  induction headers with
  | nil => intro h h' _ hh _ _; exact absurd hh (by simp)
  | cons g tl ih =>
    intro h h' hnodup hh hh' heq
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hnodup'⟩ := hnodup
    rcases List.mem_cons.mp hh with hhg | hhtl
    · rcases List.mem_cons.mp hh' with hh'g | hh'tl
      · rw [hhg, hh'g]
      · -- `h = g`, `h' ∈ tl` with `h'.name = g.name`, contradicting `g.name ∉ tl.map (·.name)`.
        exact absurd (List.mem_map.mpr ⟨h', hh'tl, by rw [← heq, hhg]⟩) hnotin
    · rcases List.mem_cons.mp hh' with hh'g | hh'tl
      · exact absurd (List.mem_map.mpr ⟨h, hhtl, by rw [heq, hh'g]⟩) hnotin
      · exact ih hnodup' hhtl hh'tl heq

/-- **`visibleRefs` yields a well-formed reference pool.** Given that the block's
    names match the header names (`hnames`) with those names pairwise distinct
    (`hnodup`), and that every block datatype's `(name, typeArgs)` is a header
    (`hheader`), the visible references for a block datatype `d`'s parameters
    satisfy `BlockRefsWF`. This is what discharges the `BlockRefsWF` hypothesis of
    the type-level soundness lemmas for `genMutuallyRecursiveDatatypes`'s output.

    * `mem` — a visible reference's name is a header name, hence a block name;
    * `uniform` — a reference to a block datatype `d'` comes from the *unique*
      header named `d'.name` (names are distinct), which is `⟨d'.name, d'.typeArgs⟩`
      by `hheader`, so the reference applies `d'.name` to exactly `d'.typeArgs`;
    * `ftvarArgs` — a reference's arguments are `h.params.map .ftvar`, all variables;
    * `argsScoped` — those arguments' variables are `h.params`, and the `visibleRefs`
      filter keeps `h.params ⊆ d.typeArgs`. -/
theorem visibleRefs_blockRefsWF {headers : List Header} {block : MutualDatatype Unit}
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
    -- `h.name = d'.name`, and `d'`'s header `h''` also has `h''.name = d'.name`;
    -- names are distinct so `h = h''`, giving `h.params = h''.params = d'.typeArgs`.
    obtain ⟨h'', hh''mem, hh''name, hh''params⟩ := hheader d' hd'
    -- `hd'name : d'.name = h.name` (the `.fst` reduces); `hh''name : h''.name = d'.name`.
    have hhname : h.name = d'.name := hd'name.symm
    have hh1 : h.name = h''.name := hhname.trans hh''name.symm
    have hhe : h = h'' := header_unique_of_nodup hnodup hh hh''mem hh1
    -- Goal reduces to `h.params.map .ftvar = d'.typeArgs.map .ftvar`.
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

/-- **Decomposition of one datatype body's support.** A datatype `d` drawn from
    `genConstructors … allHeaders inhabRefs nm params …` has `d.name = nm`,
    `d.typeArgs = params`, every constructor argument type coming from `genArgTy` at
    the visible references `visibleRefs allHeaders params`, and a *witness* head
    constructor whose argument types are drawn over the smaller `inhabRefs` pool.

    The witness's argument types are stated over `inhabRefs` (not the full
    `visibleRefs`) — that is what the inhabitance proof needs. The general
    per-constructor fact lifts the witness up to the full pool by
    `genArgTy_blockRefs_mono`, given `inhabRefs ⊆ visibleRefs allHeaders params`
    (`hsub`), so soundness sees a uniform pool.

    `d.constrs` is a *permutation* of the witness-first ordered list, since
    `genConstructors` shuffles its constructors. Both facts here are
    membership-based (`∀ c ∈`, `∃ c₀ ∈`), so they transport across that
    permutation by `List.Perm.mem_iff`. -/
theorem genConstructors_shape {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List Header} {inhabRefs : List BlockRef}
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
  -- `d.constrs = p.1` is a permutation of the witness-first ordered list.
  have hperm : ({ name := ⟨cname₀, ()⟩, args := args₀ } :: (baseConstrs ++ recConstrs)).Perm p.1 :=
    p.2
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro c hc arg harg
    -- `c ∈ d.constrs = p.1`, so `c` is in the ordered list.
    rcases List.mem_cons.mp (hperm.mem_iff.mpr hc) with rfl | hc'
    · -- Witness constructor: args drawn over `inhabRefs`, lifted to full pool.
      obtain ⟨size, hsize⟩ := genConstrArgs_mem_support hargs₀ arg harg
      exact ⟨true, size, genArgTy_blockRefs_mono hsub _ hsize⟩
    · rcases List.mem_append.mp hc' with hc' | hc'
      · obtain ⟨size, hsize⟩ := genConstrs_mem_support _ _ _ _ hbase c hc' arg harg
        exact ⟨false, size, hsize⟩
      · obtain ⟨size, hsize⟩ := genConstrs_mem_support _ _ _ _ hrec c hc' arg harg
        exact ⟨true, size, hsize⟩
  · -- Witness is the head of the ordered list, hence in `d.constrs` via `hperm`.
    refine ⟨{ name := ⟨cname₀, ()⟩, args := args₀ }, hperm.mem_iff.mp List.mem_cons_self, ?_⟩
    intro arg harg
    exact genConstrArgs_mem_support hargs₀ arg harg

/-- **The block's names are exactly its headers' names, in order.** `genConstructorsForAllTypes`
    maps each header to a body carrying that header's name (`genConstructors_shape`), so the
    generated block's name list is the header name list. By induction on
    `headers`. -/
theorem genConstructorsForAllTypes_names {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List Header}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String} :
    ∀ (done headers : List Header) (block : MutualDatatype Unit),
      (∀ h ∈ done, h ∈ allHeaders) → (∀ h ∈ headers, h ∈ allHeaders) →
      block ∈ SetGen.support (genConstructorsForAllTypes (G := SetGen.Set) baseTypes tyCons allHeaders
        maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved done headers) →
      block.map (·.name) = headers.map (·.name) := by
  intro done headers
  induction headers generalizing done with
  | nil =>
    intro block _ _ hblock
    simp only [genConstructorsForAllTypes, mem_support_pure_iff] at hblock
    subst hblock; rfl
  | cons hd tl ih =>
    intro block hdonesub htodosub hblock
    simp only [genConstructorsForAllTypes, mem_support_bind_iff, mem_support_pure_iff] at hblock
    obtain ⟨d0, hd0, ds, hds, rfl⟩ := hblock
    -- The witness pool `visibleRefs done` is a subset of `visibleRefs allHeaders`.
    have hsub : ∀ br ∈ visibleRefs done hd.params, br ∈ visibleRefs allHeaders hd.params :=
      visibleRefs_mono hdonesub
    obtain ⟨hname, _, _, _⟩ := genConstructors_shape hsub hd0
    have hhd_mem : hd ∈ allHeaders := htodosub hd List.mem_cons_self
    have hdone' : ∀ h ∈ done ++ [hd], h ∈ allHeaders := by
      intro h hh
      rcases List.mem_append.mp hh with h' | h'
      · exact hdonesub h h'
      · rw [List.mem_singleton.mp h']; exact hhd_mem
    have htodo' : ∀ h ∈ tl, h ∈ allHeaders := fun h hh => htodosub h (List.mem_cons_of_mem _ hh)
    simp only [List.map_cons, hname, ih (done ++ [hd]) ds hdone' htodo' hds]

/-- **Decomposition of the block bodies' support.** Every datatype `d` of a block
    drawn from `genConstructorsForAllTypes … allHeaders … done headers` came from a
    header of `headers` (so `∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs`)
    and satisfies the per-body shape: every constructor argument type comes from
    `genArgTy` at `visibleRefs allHeaders d.typeArgs`. By induction on `headers`. -/
theorem genConstructorsForAllTypes_shape {baseTypes : List String} {tyCons : List KnownTyCon}
    {allHeaders : List Header}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String} :
    ∀ (done headers : List Header) (block : MutualDatatype Unit),
      (∀ h ∈ done, h ∈ allHeaders) → (∀ h ∈ headers, h ∈ allHeaders) →
      block ∈ SetGen.support (genConstructorsForAllTypes (G := SetGen.Set) baseTypes tyCons allHeaders
        maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved done headers) →
      ∀ d ∈ block, (∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs) ∧
        (∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∃ rca size, arg.2 ∈ SetGen.support
          (genArgTy (G := SetGen.Set) baseTypes tyCons (visibleRefs allHeaders d.typeArgs)
            d.typeArgs rca size)) := by
  intro done headers
  induction headers generalizing done with
  | nil =>
    intro block _ _ hblock
    simp only [genConstructorsForAllTypes, mem_support_pure_iff] at hblock
    subst hblock; intro d hd; exact absurd hd (by simp)
  | cons hdr tl ih =>
    intro block hdonesub htodosub hblock
    simp only [genConstructorsForAllTypes, mem_support_bind_iff, mem_support_pure_iff] at hblock
    obtain ⟨d0, hd0, ds, hds, rfl⟩ := hblock
    have hhd_mem : hdr ∈ allHeaders := htodosub hdr List.mem_cons_self
    have hsub : ∀ br ∈ visibleRefs done hdr.params, br ∈ visibleRefs allHeaders hdr.params :=
      visibleRefs_mono hdonesub
    have hdone' : ∀ h ∈ done ++ [hdr], h ∈ allHeaders := by
      intro h hh
      rcases List.mem_append.mp hh with h' | h'
      · exact hdonesub h h'
      · rw [List.mem_singleton.mp h']; exact hhd_mem
    have htodo' : ∀ h ∈ tl, h ∈ allHeaders := fun h hh => htodosub h (List.mem_cons_of_mem _ hh)
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨hname, hargs, hconstrs, _⟩ := genConstructors_shape hsub hd0
      exact ⟨⟨hdr, List.mem_cons_self, hname.symm, hargs.symm⟩, by rw [hargs]; exact hconstrs⟩
    · obtain ⟨⟨h, hhmem, hh1, hh2⟩, hconstrs⟩ := ih (done ++ [hdr]) ds hdone' htodo' hds d hd
      exact ⟨⟨h, List.mem_cons_of_mem _ hhmem, hh1, hh2⟩, hconstrs⟩

/-- **Top-level decomposition of `genMutuallyRecursiveDatatypes`'s support.** A generated block
    has: pairwise-fresh datatype names (each `∉ initialReserved`); every datatype's
    parameters are those of its header; the block's names are exactly the header
    names; and every constructor argument type comes from `genArgTy` at the visible
    references for that datatype's parameters. (Inhabitance — the ordered witness
    argument — is handled separately by `genConstructorsForAllTypes_inhabited`.) -/
theorem genMutuallyRecursiveDatatypesOrdered_shape {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypesOrdered (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∃ headers : List Header,
      block ≠ [] ∧
      block.map (·.name) = headers.map (·.name) ∧
      (headers.map (·.name)).Nodup ∧
      (∀ h ∈ headers, h.name ∉ initialReserved baseTypes tyCons extraReserved) ∧
      (∀ d ∈ block, ∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs) ∧
      (∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∃ rca size, arg.2 ∈ SetGen.support
        (genArgTy (G := SetGen.Set) baseTypes tyCons (visibleRefs headers d.typeArgs)
          d.typeArgs rca size)) := by
  simp only [genMutuallyRecursiveDatatypesOrdered, mem_support_bind_iff] at hb
  obtain ⟨numExtra, _, names, hnames, paramsList, hparams, hbodies⟩ := hb
  -- Header names are exactly `names` (the zipped-then-mapped first projection),
  -- which is nodup.
  let headers : List Header := (names.zip paramsList).map (fun p => { name := p.1, params := p.2 })
  have hnameslen : names.length = numExtra + 1 := genFreshNames_length _ _ _ hnames
  have hparamslen : paramsList.length = names.length := by
    rw [genParamsList_length _ _ _ _ hparams, hnameslen]
  have hheadernames : headers.map (·.name) = names :=
    map_name_headers_of_length_le names paramsList (by omega)
  -- `genConstructorsForAllTypes` is applied at `done = []`, `headers = headers`.
  have hnil : ∀ h ∈ ([] : List Header), h ∈ headers := by simp
  have hall : ∀ h ∈ headers, h ∈ headers := fun _ h => h
  have hbnames := genConstructorsForAllTypes_names [] headers _ hnil hall hbodies
  have hbshape := genConstructorsForAllTypes_shape [] headers _ hnil hall hbodies
  refine ⟨headers, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The block is non-empty: it has as many datatypes as headers = `numExtra+1`.
    intro hblnil
    rw [hblnil] at hbnames
    simp only [List.map_nil] at hbnames
    have : names.length = 0 := by
      have := congrArg List.length hbnames.symm
      rwa [hheadernames, List.length_nil] at this
    omega
  · -- Block names = header names.
    exact hbnames
  · -- Header names are nodup (they are `names`, drawn by `genFreshNames`).
    rw [hheadernames]; exact genFreshNames_nodup _ _ _ hnames
  · intro h hh
    -- Header names are among `names`, each fresh against `initialReserved`.
    have : h.name ∈ names := by rw [← hheadernames]; exact List.mem_map.mpr ⟨h, hh, rfl⟩
    exact genFreshNames_fresh _ _ _ hnames h.name this
  · intro d hd; exact (hbshape d hd).1
  · intro d hd c hc arg harg; exact (hbshape d hd).2 c hc arg harg

/-- **Main soundness theorem: `argsWF`.** Every constructor argument type of a
    block drawn from `genMutuallyRecursiveDatatypes` is well-formed for the block.

    This is exactly the `argsWF` field of `Core.TypeSpec.MutualADTWF`.

    The only hypothesis is on the caller-supplied `tyCons` pool; the conditions
    concerning the block's own names are supplied by the generator's reserved-name
    discipline via `namesOk_of_fresh`, and the recursive-occurrence facts by
    `visibleRefs_blockRefsWF`. -/
theorem genMutuallyRecursiveDatatypesOrdered_argsWF {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (harrow : ∀ kc ∈ tyCons, kc.1 ≠ "arrow")
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypesOrdered (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ConstrArgWF block arg.2 := by
  obtain ⟨headers, _, hnames, hnodup, hfresh, hheader, hconstrs⟩ := genMutuallyRecursiveDatatypesOrdered_shape hb
  have hn : NamesOk baseTypes tyCons (block.map (·.name)) := by
    refine namesOk_of_fresh (extraReserved := extraReserved) harrow ?_
    rw [hnames]; intro n hn; obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn; exact hfresh h hh
  intro d hd c hc arg harg
  have hbr := visibleRefs_blockRefsWF hnames hnodup hheader hd
  obtain ⟨_, _, hty⟩ := hconstrs d hd c hc arg harg
  exact genArgTy_constrArgWF hn hbr hty

/-- **`argsWF` for the default configuration, with no side conditions at all.** -/
theorem genMutuallyRecursiveDatatypesOrdered_argsWF_default
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypesOrdered (G := SetGen.Set) defaultBaseTypes
            defaultTyCons maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs
            maxArgs maxSize)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ConstrArgWF block arg.2 :=
  genMutuallyRecursiveDatatypesOrdered_argsWF defaultTyCons_ne_arrow hb

/-! ### `refsKnown`: only known names are referenced

The other `MutualADTWF` field within scope. `getTypeRefs` collects every type
constructor name occurring in a type; we show each is a `baseTypes` name, a
`tyCons` name, the datatype's own name, or the reserved `"arrow"`. -/

/-- Every type reference in a generated type is a `baseTypes` name, a `tyCons`
    name, a block name, or `"arrow"`. This is the generator-side half of the
    `refsKnown` field of `MutualADTWF`: it holds against *any* ambient context
    whose known types and datatypes cover `baseTypes` and `tyCons` (and `"arrow"`,
    which Strata Core always knows).

    A recursive occurrence's head is a block name (`BlockRefsWF.mem`) and its
    arguments are `ftvar`s (`BlockRefsWF.ftvarArgs`), so it contributes only its
    head name.

    Proved by strong induction on `size` through `genArgTy_mem_iff` /
    `genLeafTy_mem_iff` — no auxiliary inductive relation. -/
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
        -- The head is a block name; the arguments are `ftvar`s, contributing nothing.
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

/-! ### `argVarsScoped`: constructor arguments introduce no fresh type variables

The `argVarsScoped` field of `MutualADTWF`: every free type variable of a
constructor-argument type is one of the datatype's declared `typeArgs`. On the
generator side, the only source of an `ftvar` leaf is the type-parameter leaf,
which draws from `tyParams`; a recursive occurrence contributes only the
referee's argument variables, which `BlockRefsWF.argsScoped` keeps within `tyParams`. -/

/-- Every free type variable of a type in `genArgTy`'s support lies in `tyParams`.
    Structurally analogous to `genArgTy_refs`, tracking `LMonoTy.freeVars` rather
    than `getTypeRefs`; strong induction on `size` through the one-step
    decomposition. A recursive occurrence's variables are scoped by
    `BlockRefsWF.argsScoped`. -/
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

/-- **`refsKnown`.** Every type constructor name referenced by a constructor
    argument of a generated block is a `baseTypes` name, a `tyCons` name, a block
    name, or `"arrow"`. Lifts `genArgTy_refs` over the block via
    `genMutuallyRecursiveDatatypesOrdered_shape` (each argument comes from `genArgTy` at the visible
    references) and `visibleRefs_blockRefsWF`. -/
theorem genMutuallyRecursiveDatatypesOrdered_refsKnown {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypesOrdered (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ r ∈ getTypeRefs arg.2,
      r ∈ baseTypes ∨ r ∈ tyCons.map (·.1) ∨ r ∈ block.map (·.name) ∨ r = "arrow" := by
  obtain ⟨headers, _, hnames, hnodup, _, hheader, hconstrs⟩ := genMutuallyRecursiveDatatypesOrdered_shape hb
  intro d hd c hc arg harg r hr
  have hbr := visibleRefs_blockRefsWF hnames hnodup hheader hd
  obtain ⟨_, size, hty⟩ := hconstrs d hd c hc arg harg
  exact genArgTy_refs hbr size hty r hr

/-- **`argVarsScoped`.** Every free type variable of a constructor-argument type of
    a generated block is one of the enclosing datatype's declared `typeArgs`. Lifts
    `genArgTy_freeVars` over the block, as `genMutuallyRecursiveDatatypesOrdered_refsKnown` lifts
    `genArgTy_refs`. -/
theorem genMutuallyRecursiveDatatypesOrdered_argVarsScoped {baseTypes : List String} {tyCons : List KnownTyCon}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypesOrdered (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ v ∈ LMonoTy.freeVars arg.2,
      v ∈ d.typeArgs := by
  obtain ⟨headers, _, hnames, hnodup, _, hheader, hconstrs⟩ := genMutuallyRecursiveDatatypesOrdered_shape hb
  intro d hd c hc arg harg v hv
  have hbr := visibleRefs_blockRefsWF hnames hnodup hheader hd
  obtain ⟨_, size, hty⟩ := hconstrs d hd c hc arg harg
  exact genArgTy_freeVars hbr size hty v hv

/-! ### Bundling into `Core.TypeSpec.MutualADTWF`

`argsWF` and `refsKnown` are the two hard fields; the remaining are name-freshness
(`namesFresh`, `namesNew`), non-emptiness and name-distinctness (`nonempty`,
`namesNodup`), and inhabitance (`inhabited`). All of them are stated against an
ambient `LContext CoreLParams`, so we first record what the context must satisfy
for a *freshly generated* block to be well-formed in it. -/

open Core Core.TypeSpec in
/-- What the ambient context `C` must provide for `genMutuallyRecursiveDatatypes`'s output to be
    `MutualADTWF C block`. These are exactly the assumptions the generator cannot
    control because they concern the context, not the block it builds:

    * `refsKnown` needs every referenceable name to actually resolve in `C`;
    * `namesFresh` / `namesNew` need `C`'s existing type/datatype names to be
      inside `initialReserved`, so a name drawn fresh against that list avoids
      them;
    * `inhabited` needs every referenceable head symbol to be *external* in `C`
      (not itself a datatype), so a `d.name`-absent argument type is inhabited.

    `defaultContextOk` shows a concrete `C` satisfying all of this, giving the
    side-condition-free corollary `genDatatype_MutualADTWF_default`. -/
structure ContextOk (C : LContext CoreLParams) (baseTypes : List String)
    (tyCons : List KnownTyCon) (extraReserved : List String) : Prop where
  /-- Every base type resolves as a known type or existing datatype of `C`. -/
  base_known : ∀ b ∈ baseTypes,
    b ∈ C.knownTypes.keywords ∨ b ∈ C.datatypes.allTypeNames
  /-- Every applied type constructor resolves as a known type or datatype of `C`. -/
  tyCon_known : ∀ kc ∈ tyCons,
    kc.1 ∈ C.knownTypes.keywords ∨ kc.1 ∈ C.datatypes.allTypeNames
  /-- `"arrow"` resolves as a known type of `C` (Strata Core always knows it). -/
  arrow_known : "arrow" ∈ C.knownTypes.keywords
  /-- `C`'s known-type names are all reserved (either by baseTypes/tyCons/arrow or
      by `extraReserved`), so a fresh name avoids them. -/
  knownTypes_reserved : ∀ k ∈ C.knownTypes.keywords,
    k ∈ initialReserved baseTypes tyCons extraReserved
  /-- `C`'s datatype names are all reserved, so a fresh name avoids them. -/
  datatypes_reserved : ∀ n ∈ C.datatypes.allTypeNames,
    n ∈ initialReserved baseTypes tyCons extraReserved
  /-- Every base type is external in `C` (a known primitive, not a datatype), so
      it is `TySymInhab` outright. -/
  base_external : ∀ b ∈ baseTypes, C.datatypes.getType b = none
  /-- Every applied type constructor is external in `C`. -/
  tyCon_external : ∀ kc ∈ tyCons, C.datatypes.getType kc.1 = none
  /-- `"arrow"` is external in `C` (it is a known primitive, never a datatype). -/
  arrow_external : C.datatypes.getType "arrow" = none

end Soundness

/-! ## Inhabitance of the generated datatype

The one `MutualADTWF` field that is not already covered by `argsWF` / `refsKnown`
/ freshness: every datatype in the block is inhabited. For our singleton block
`[d]` this is `TySymInhab (C.datatypes.push [d]) d.name`, witnessed by `d`'s
first constructor — which `genDatatype` generates with `recCallsAllowed := false`,
so all of its argument types are `d.name`-absent and hence inhabited. -/

section Inhabitance

open Core Core.TypeSpec

/-- If `getType` finds a datatype under `name`, then `name` is one of the
    factory's type names. Contrapositive: a name absent from `allTypeNames`
    resolves to `none`. -/
theorem name_mem_allTypeNames_of_getType {F : @TypeFactory Unit} {name : String}
    {d : LDatatype Unit} (h : F.getType name = some d) :
    name ∈ F.allTypeNames := by
  simp only [TypeFactory.getType] at h
  have hmem := List.find?_some h
  have hd_mem := List.mem_of_find?_eq_some h
  simp only [beq_iff_eq] at hmem
  simp only [TypeFactory.allTypeNames, List.mem_map]
  exact ⟨d, hd_mem, hmem⟩

/-- `find?` by name over a list of datatypes with distinct names returns the
    (unique) member with that name. By induction on the list. -/
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

/-- `find?` by a name absent from a datatype list's names returns `none`. -/
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

/-- Pushing `block` appends its datatypes to the flattened datatype list. -/
theorem allDatatypes_push {C : LContext CoreLParams} {block : MutualDatatype Unit} :
    TypeFactory.allDatatypes (C.datatypes.push block) =
      C.datatypes.allDatatypes ++ block := by
  simp [TypeFactory.allDatatypes, Array.toList_push, List.flatten_append]

/-- `getType` on a block-extended factory: pushing `block` makes each member's name
    resolve to that member, provided the name did not already resolve in
    `C.datatypes` (fresh) and block names are distinct. -/
theorem getType_push_self {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {d : LDatatype Unit} (hnew : C.datatypes.getType d.name = none)
    (hnodup : (block.map (·.name)).Nodup) (hd : d ∈ block) :
    TypeFactory.getType (C.datatypes.push block) d.name = some d := by
  have hnone : C.datatypes.allDatatypes.find? (fun d' => d'.name == d.name) = none := hnew
  -- `find?` skips the (name-free) prefix and matches `d` in the appended block.
  rw [TypeFactory.getType, allDatatypes_push, List.find?_append, hnone, Option.none_or,
      find?_name_eq_of_mem hnodup hd]

/-- `getType` on the extended factory for a name *outside* the block: it agrees
    with `C.datatypes`. In particular an external symbol of `C` stays external. -/
theorem getType_push_other {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {name : String} (hne : name ∉ block.map (·.name))
    (hext : C.datatypes.getType name = none) :
    TypeFactory.getType (C.datatypes.push block) name = none := by
  have hnone : C.datatypes.allDatatypes.find? (fun d' => d'.name == name) = none := hext
  -- The prefix contributes nothing (`hext`); no block member matches either (`hne`).
  rw [TypeFactory.getType, allDatatypes_push, List.find?_append, hnone, Option.none_or,
      find?_name_eq_none hne]

/-- **A block-absent type is inhabited in the extended factory**, provided every
    type-constructor head it uses is a base/tyCons/"arrow" name external in `C`
    (block names are excluded by absence). Proof by structural induction: `ftvar`
    and `bitvec` are inhabited outright, and a `.tcons name args` head is external
    — hence `TySymInhab` — while every argument is inhabited by the induction
    hypothesis (each is itself block-absent). -/
theorem tyInhab_of_absent {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {baseTypes : List String} {tyCons : List KnownTyCon}
    {extraReserved : List String}
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (harrow_ext : TypeFactory.getType (C.datatypes.push block) "arrow" = none)
    {ty : LMonoTy}
    (hrefs : ∀ r ∈ getTypeRefs ty,
      r ∈ baseTypes ∨ r ∈ tyCons.map (·.1) ∨ r ∈ block.map (·.name) ∨ r = "arrow")
    (habsent : BlockAbsent block ty) :
    TyInhab (C.datatypes.push block) ty := by
  induction ty using LMonoTy.induct with
  | ftvar f => exact .ftvar f
  | bitvec n => exact .bitvec n
  | tcons name args ih =>
    -- The head `name` is the first reference; it is not a block name (absence), and
    -- every base/tyCons/"arrow" name is external in the extended factory, so the
    -- symbol is inhabited via `TySymInhab.external`.
    have hname_ref : name ∈ getTypeRefs (.tcons name args) := by simp [getTypeRefs]
    have hname_notmem : name ∉ block.map (·.name) := head_not_mem_of_blockAbsent habsent
    have hsym : TySymInhab (C.datatypes.push block) name := by
      have hext : TypeFactory.getType (C.datatypes.push block) name = none := by
        rcases hrefs name hname_ref with hb | htc | hblk | harr
        · exact getType_push_other hname_notmem (hctx.base_external _ hb)
        · obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp htc
          exact getType_push_other hname_notmem (hctx.tyCon_external _ hkc)
        · exact absurd hblk hname_notmem
        · subst harr; exact harrow_ext
      exact .external _ hext
    refine .tcons name args hsym (fun a ha => ?_)
    -- Each argument is itself block-absent with a subset of the references.
    refine ih a ha (fun r hr => hrefs r ?_) (blockAbsent_of_mem_args habsent ha)
    simp only [getTypeRefs, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨a, ha, hr⟩

/-- **`BlockRefsWF` is anti-monotone in the reference pool.** Every field is a
    universally-quantified fact over the pool's members, so a subset of a
    well-formed pool is well-formed. Lets the witness pool `visibleRefs done`
    inherit well-formedness from the full `visibleRefs allHeaders` pool. -/
theorem BlockRefsWF.mono {block : MutualDatatype Unit} {tyParams : List TyIdentifier}
    {refs refs' : List BlockRef} (hsub : ∀ br ∈ refs', br ∈ refs)
    (h : BlockRefsWF block tyParams refs) : BlockRefsWF block tyParams refs' :=
  ⟨fun br hbr => h.mem br (hsub br hbr),
   fun br hbr => h.uniform br (hsub br hbr),
   fun br hbr => h.ftvarArgs br (hsub br hbr),
   fun br hbr => h.argsScoped br (hsub br hbr)⟩

/-- **A type drawn by `genArgTy` over an *inhabited* reference pool is inhabited.**
    The witness constructor of each datatype is drawn (at flag `true`) over the
    references to *already-generated* datatypes, all of which are inhabited
    (`hinhab`). This lemma turns that into `TyInhab` for the whole argument type:

    * a recursive occurrence `br.1 br.2` (a pool member) has an inhabited head
      (`hinhab`) and all-`ftvar` arguments (`BlockRefsWF.ftvarArgs`), hence inhabited;
    * base types and applied type constructors have external (non-block) heads and
      block-absent arguments — inhabited by `tyInhab_of_absent`, since the
      generator draws those argument positions at flag `false`;
    * an arrow recurses into its (flag-`rca`) codomain and treats its (flag-`false`)
      block-absent domain by `tyInhab_of_absent`.

    Strong induction on `size` through the one-step support decomposition. -/
theorem genArgTy_tyInhab {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {baseTypes : List String} {tyCons : List KnownTyCon}
    {extraReserved : List String} {poolRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hbr : BlockRefsWF block tyParams poolRefs)
    (harrow_ext : TypeFactory.getType (C.datatypes.push block) "arrow" = none)
    (hinhab : ∀ br ∈ poolRefs, TySymInhab (C.datatypes.push block) br.1) :
    ∀ (size : Nat) {rca : Bool} {ty : LMonoTy},
      ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons poolRefs
        tyParams rca size) →
      TyInhab (C.datatypes.push block) ty := by
  -- A `baseTypes`/`tyCons` head is external in the extended factory (it is not a
  -- block name, so `getType_push_other` applies).
  have hbase_ext : ∀ b ∈ baseTypes, TypeFactory.getType (C.datatypes.push block) b = none :=
    fun b hb => getType_push_other (hn.base_notMem b hb) (hctx.base_external b hb)
  have htyCon_ext : ∀ kc ∈ tyCons, TypeFactory.getType (C.datatypes.push block) kc.1 = none :=
    fun kc hkc => getType_push_other (hn.tyCon_notMem kc hkc) (hctx.tyCon_external kc hkc)
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
      · -- Recursive occurrence: head is inhabited, args are all `ftvar`s.
        refine .tcons br.1 br.2 (hinhab br hbrmem) (fun a ha => ?_)
        obtain ⟨v, rfl⟩ := hbr.ftvarArgs br hbrmem a ha
        exact .ftvar v
    · -- Arrow: domain block-absent (flag `false`); codomain by IH.
      have hhalf : size / 2 < size :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hsz') (by omega)
      rw [LMonoTy.arrow]
      refine .tcons "arrow" [t1, t2] (.external _ harrow_ext) (fun a ha => ?_)
      rcases List.mem_cons.mp ha with rfl | ha
      · exact tyInhab_of_absent hctx harrow_ext (genArgTy_refs hbr _ h1)
          (genArgTy_absent hn _ h1)
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact ih _ hhalf h2
        · cases ha
    · -- Applied type constructor: head external, arguments block-absent (flag `false`).
      refine .tcons k args (.external _ (htyCon_ext (k, args.length) hkc)) (fun a ha => ?_)
      exact tyInhab_of_absent hctx harrow_ext (genArgTy_refs hbr _ (hall a ha))
        (genArgTy_absent hn _ (hall a ha))

/-! ### Permutation invariance

The generator emits datatypes in inhabitance order; `genMutuallyRecursiveDatatypes`
then shuffles the block. To keep the soundness theorem covering the shuffled
output, we show `MutualADTWF` is invariant under permutation of the block. Every
field is either a `∀ d ∈ block, …` fact (`Perm` preserves membership), a fact about
`block.map (·.name)` (`Perm`-stable, as are `Nodup` and `≠ []`), or the inhabitance
field — the one that mentions `block` non-trivially, through
`C.datatypes.push block`.

Inhabitance transfers because the three inhabitance relations consult the factory
*only* through `getType`, and two block-extended factories built from
permutation-equivalent blocks with distinct names agree on `getType` at every name
(`getType_push_perm`): `getType` is `find?`-by-name, which — for `Nodup` names —
returns the unique matching datatype regardless of list order. -/

/-- **Two permutation-equivalent blocks with distinct names give factories that
    agree on `getType`.** `getType` is `find?` by name over `C.datatypes ++ block`;
    for each name it is characterized by *membership* (`find?_name_eq_of_mem` /
    `find?_name_eq_none`), and membership is `Perm`-invariant. -/
theorem getType_push_perm {C : LContext CoreLParams} {block block' : MutualDatatype Unit}
    (hperm : block.Perm block') (hnodup : (block.map (·.name)).Nodup) (name : String) :
    TypeFactory.getType (C.datatypes.push block) name =
      TypeFactory.getType (C.datatypes.push block') name := by
  have hnodup' : (block'.map (·.name)).Nodup := (hperm.map (·.name)).nodup_iff.mp hnodup
  by_cases hmem : name ∈ block.map (·.name)
  · -- `name` resolves in both blocks, to the (unique) same-named datatype.
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmem
    have hd' : d ∈ block' := (hperm.mem_iff).mp hd
    rw [TypeFactory.getType, allDatatypes_push, List.find?_append,
        TypeFactory.getType, allDatatypes_push, List.find?_append]
    -- Both blocks match `d`; the shared `C.datatypes` prefix is identical.
    rcases hpre : (C.datatypes.allDatatypes.find? (fun d' => d'.name == d.name)) with _ | dd
    · rw [hpre, Option.none_or, Option.none_or, find?_name_eq_of_mem hnodup hd,
        find?_name_eq_of_mem hnodup' hd']
    · rw [hpre, Option.some_or, Option.some_or]
  · -- `name` resolves in neither block; both reduce to the shared prefix.
    have hmem' : name ∉ block'.map (·.name) := fun h => hmem ((hperm.map (·.name)).mem_iff.mpr h)
    rw [TypeFactory.getType, allDatatypes_push, List.find?_append,
        TypeFactory.getType, allDatatypes_push, List.find?_append,
        find?_name_eq_none hmem, find?_name_eq_none hmem']

/-- **Inhabitance transfers between factories that agree on `getType`.** Since the
    mutual `TyInhab` / `TySymInhab` / `ConstrInhab` relations consult the factory
    only via `getType`, agreement at every name carries each derivation across.
    Proved by the mutual recursor; we only export the `TySymInhab` component. -/
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

/-- **Ordered inhabitance of the generated bodies.** By induction on the `todo`
    list, carrying the invariant that every *already-generated* datatype (those
    whose header is in `done`) is inhabited (`hdoneInhab`). The head datatype's
    witness constructor is drawn over `visibleRefs done`, whose members all name
    `done` datatypes — inhabited by the invariant — so `genArgTy_tyInhab` makes the
    head datatype inhabited; that extends the invariant to `done ++ [hdr]` for the
    recursive call.

    All the block-wide facts (`hbnames` / `hnodupH` / `hheader` for `BlockRefsWF`,
    `hnew` / `hnodup` for `getType_push_self`) are passed through unchanged. -/
theorem genConstructorsForAllTypes_inhabited {baseTypes : List String} {tyCons : List KnownTyCon}
    {C : LContext CoreLParams} {block : MutualDatatype Unit} {headers : List Header}
    {maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat} {reserved : List String}
    {extraReserved : List String}
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (harrow_ext : TypeFactory.getType (C.datatypes.push block) "arrow" = none)
    (hbnames : block.map (·.name) = headers.map (·.name))
    (hnodupH : (headers.map (·.name)).Nodup)
    (hheader : ∀ d ∈ block, ∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs)
    (hnodup : (block.map (·.name)).Nodup)
    (hnew : ∀ d ∈ block, C.datatypes.getType d.name = none) :
    ∀ (done todo : List Header) (blockTail : MutualDatatype Unit),
      (∀ h ∈ done, h ∈ headers) → (∀ h ∈ todo, h ∈ headers) →
      (∀ d ∈ blockTail, d ∈ block) →
      (∀ h ∈ done, TySymInhab (C.datatypes.push block) h.name) →
      blockTail ∈ SetGen.support (genConstructorsForAllTypes (G := SetGen.Set) baseTypes tyCons
        headers maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved done todo) →
      ∀ d ∈ blockTail, TySymInhab (C.datatypes.push block) d.name := by
  intro done todo
  induction todo generalizing done with
  | nil =>
    intro blockTail _ _ _ _ hbt
    simp only [genConstructorsForAllTypes, mem_support_pure_iff] at hbt
    subst hbt; intro d hd; exact absurd hd (by simp)
  | cons hdr tl ih =>
    intro blockTail hdonesub htodosub hmem hdoneInhab hbt
    simp only [genConstructorsForAllTypes, mem_support_bind_iff, mem_support_pure_iff] at hbt
    obtain ⟨d0, hd0, ds, hds, rfl⟩ := hbt
    have hhd_mem : hdr ∈ headers := htodosub hdr List.mem_cons_self
    have hsub : ∀ br ∈ visibleRefs done hdr.params, br ∈ visibleRefs headers hdr.params :=
      visibleRefs_mono hdonesub
    -- `d0`'s fields and its witness constructor (over the `visibleRefs done` pool).
    obtain ⟨hname, hargs, _, ⟨c₀, hc₀, hwit⟩⟩ := genConstructors_shape hsub hd0
    have hd0_block : d0 ∈ block := hmem d0 List.mem_cons_self
    -- The full pool at `d0` is well-formed; its `visibleRefs done` sub-pool is too.
    have hfullWF : BlockRefsWF block d0.typeArgs (visibleRefs headers d0.typeArgs) :=
      visibleRefs_blockRefsWF hbnames hnodupH hheader hd0_block
    have hsub' : ∀ br ∈ visibleRefs done d0.typeArgs, br ∈ visibleRefs headers d0.typeArgs :=
      hargs ▸ hsub
    have hpoolWF : BlockRefsWF block d0.typeArgs (visibleRefs done d0.typeArgs) :=
      hfullWF.mono hsub'
    -- The witness pool's members all name `done` datatypes, hence are inhabited.
    have hpoolInhab : ∀ br ∈ visibleRefs done d0.typeArgs,
        TySymInhab (C.datatypes.push block) br.1 := by
      intro br hbr
      obtain ⟨h, hh, _, rfl⟩ := (visibleRefs_mem_iff _ _ _).mp hbr
      exact hdoneInhab h hh
    -- `d0` is inhabited via its witness constructor (drawn over `visibleRefs done`).
    have hd0Inhab : TySymInhab (C.datatypes.push block) d0.name := by
      refine .datatype d0.name d0 c₀
        (getType_push_self (hnew d0 hd0_block) hnodup hd0_block) hc₀ (.mk c₀ ?_)
      intro arg harg
      obtain ⟨size, hsize⟩ := hwit arg harg
      -- `hwit` draws over `visibleRefs done hdr.params = visibleRefs done d0.typeArgs`.
      rw [← hargs] at hsize
      exact genArgTy_tyInhab hctx hn hpoolWF harrow_ext hpoolInhab size hsize
    -- Extend the invariant to `done ++ [hdr]` and recurse on the tail.
    have hdoneInhab' : ∀ h ∈ done ++ [hdr], TySymInhab (C.datatypes.push block) h.name := by
      intro h hh
      rcases List.mem_append.mp hh with h' | h'
      · exact hdoneInhab h h'
      · rw [List.mem_singleton.mp h', ← hname]; exact hd0Inhab
    have hdonesub' : ∀ h ∈ done ++ [hdr], h ∈ headers := by
      intro h hh
      rcases List.mem_append.mp hh with h' | h'
      · exact hdonesub h h'
      · rw [List.mem_singleton.mp h']; exact hhd_mem
    have htodo' : ∀ h ∈ tl, h ∈ headers := fun h hh => htodosub h (List.mem_cons_of_mem _ hh)
    have hmem' : ∀ d ∈ ds, d ∈ block := fun d hd => hmem d (List.mem_cons_of_mem _ hd)
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hd0Inhab
    · exact ih (done ++ [hdr]) ds hdonesub' htodo' hmem' hdoneInhab' hds d hd

/-- **`inhabited` for the generated block.** Every datatype `d` of a generated
    block is inhabited in `C.datatypes.push block`. Generating datatypes in order,
    each datatype's witness constructor references only the datatypes generated
    before it, so — starting from the first (which references nothing) —
    `genConstructorsForAllTypes_inhabited` establishes every datatype inhabited by
    ordered induction. -/
theorem genMutuallyRecursiveDatatypesOrdered_inhabited {baseTypes : List String} {tyCons : List KnownTyCon}
    {C : LContext CoreLParams}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (harrow : ∀ kc ∈ tyCons, kc.1 ≠ "arrow")
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypesOrdered (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    ∀ d ∈ block, TySymInhab (C.datatypes.push block) d.name := by
  -- Unfold to the concrete header list `headers`, so the ordered induction can
  -- consume the very `hbodies` membership `block` came from.
  simp only [genMutuallyRecursiveDatatypesOrdered, mem_support_bind_iff] at hb
  obtain ⟨numExtra, _, names, hnames, paramsList, hparams, hbodies⟩ := hb
  let headers : List Header := (names.zip paramsList).map (fun p => { name := p.1, params := p.2 })
  have hnameslen : names.length = numExtra + 1 := genFreshNames_length _ _ _ hnames
  have hparamslen : paramsList.length = names.length := by
    rw [genParamsList_length _ _ _ _ hparams, hnameslen]
  have hheadernames : headers.map (·.name) = names :=
    map_name_headers_of_length_le names paramsList (by omega)
  have hself : ∀ h ∈ headers, h ∈ headers := fun _ h => h
  have hnilsub : ∀ h ∈ ([] : List Header), h ∈ headers := by simp
  -- Block-wide facts, all derived from the concrete `headers`.
  have hbnames : block.map (·.name) = headers.map (·.name) :=
    genConstructorsForAllTypes_names [] headers block hnilsub hself hbodies
  have hnodupH : (headers.map (·.name)).Nodup := by
    rw [hheadernames]; exact genFreshNames_nodup _ _ _ hnames
  have hfresh : ∀ h ∈ headers, h.name ∉ initialReserved baseTypes tyCons extraReserved := by
    intro h hh
    have : h.name ∈ names := by rw [← hheadernames]; exact List.mem_map.mpr ⟨h, hh, rfl⟩
    exact genFreshNames_fresh _ _ _ hnames h.name this
  have hheader : ∀ d ∈ block, ∃ h ∈ headers, h.name = d.name ∧ h.params = d.typeArgs :=
    fun d hd => (genConstructorsForAllTypes_shape [] headers block hnilsub hself hbodies d hd).1
  have hnodup : (block.map (·.name)).Nodup := by rw [hbnames]; exact hnodupH
  have hnfresh : ∀ n ∈ block.map (·.name), n ∉ initialReserved baseTypes tyCons extraReserved := by
    rw [hbnames]; intro n hn; obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn; exact hfresh h hh
  have hn : NamesOk baseTypes tyCons (block.map (·.name)) := namesOk_of_fresh harrow hnfresh
  have harrow_notmem : "arrow" ∉ block.map (·.name) :=
    fun hmem => hn.block_ne_arrow _ hmem rfl
  have harrow_ext : TypeFactory.getType (C.datatypes.push block) "arrow" = none :=
    getType_push_other harrow_notmem hctx.arrow_external
  have hnew : ∀ d ∈ block, C.datatypes.getType d.name = none := by
    intro d hd
    rcases hsome : C.datatypes.getType d.name with _ | dd
    · rfl
    · exact absurd (hctx.datatypes_reserved _ (name_mem_allTypeNames_of_getType hsome))
        (hnfresh d.name (List.mem_map.mpr ⟨d, hd, rfl⟩))
  -- Ordered induction from `done = []` over `todo = headers`.
  exact genConstructorsForAllTypes_inhabited hctx hn harrow_ext hbnames hnodupH hheader hnodup hnew
    [] headers block hnilsub hself (fun _ h => h) (by simp) hbodies

/-- **Main theorem: the generated block is `MutualADTWF`.** Every mutually
    recursive block `genMutuallyRecursiveDatatypes` produces is well-formed in any context `C`
    satisfying `ContextOk` — all nine fields of `Core.TypeSpec.MutualADTWF`.

    Hypotheses split into: one on the caller-supplied `tyCons` pool
    (`tyCon_ne_arrow`, as for `argsWF`), and the `ContextOk` bundle describing how
    the ambient context must relate to the generator's vocabulary. -/
theorem genMutuallyRecursiveDatatypesOrdered_MutualADTWF {baseTypes : List String} {tyCons : List KnownTyCon}
    {C : LContext CoreLParams}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (harrow : ∀ kc ∈ tyCons, kc.1 ≠ "arrow")
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypesOrdered (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    MutualADTWF C block := by
  obtain ⟨headers, hne, hbnames, hnodupH, hfresh, hheader, _⟩ := genMutuallyRecursiveDatatypesOrdered_shape hb
  have hnfresh : ∀ n ∈ block.map (·.name), n ∉ initialReserved baseTypes tyCons extraReserved := by
    rw [hbnames]; intro n hn; obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn; exact hfresh h hh
  refine
    { nonempty := hne
      namesNodup := by rw [hbnames]; exact hnodupH
      namesFresh := ?_
      namesNew := ?_
      argsWF := ?_
      refsKnown := ?_
      inhabited := ?_
      argVarsScoped := ?_ }
  · -- namesFresh: no block name is a known type of `C`.
    intro d hd hcontains
    -- A known-type name of `C` is reserved, but block names are drawn fresh.
    exact hnfresh d.name (List.mem_map.mpr ⟨d, hd, rfl⟩) (hctx.knownTypes_reserved _ (by
      simpa [KnownTypes.containsName, KnownTypes.keywords] using hcontains))
  · -- namesNew: no block name is an existing datatype of `C`.
    intro d hd
    rcases hsome : C.datatypes.getType d.name with _ | dd
    · rfl
    · exact absurd (hctx.datatypes_reserved _ (name_mem_allTypeNames_of_getType hsome))
        (hnfresh d.name (List.mem_map.mpr ⟨d, hd, rfl⟩))
  · -- argsWF: exactly `genMutuallyRecursiveDatatypesOrdered_argsWF`.
    exact genMutuallyRecursiveDatatypesOrdered_argsWF harrow hb
  · -- refsKnown: every reference resolves in `C` or is a block name / `"arrow"`.
    intro d hd c hc arg harg r hr
    rcases genMutuallyRecursiveDatatypesOrdered_refsKnown hb d hd c hc arg harg r hr with
      hbt | htc | hblk | harr
    · rcases hctx.base_known r hbt with hk | hdt
      · exact Or.inl hk
      · exact Or.inr (Or.inl hdt)
    · obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp htc
      rcases hctx.tyCon_known kc hkc with hk | hdt
      · exact Or.inl hk
      · exact Or.inr (Or.inl hdt)
    · exact Or.inr (Or.inr hblk)
    · subst harr; exact Or.inl hctx.arrow_known
  · -- inhabited.
    exact genMutuallyRecursiveDatatypesOrdered_inhabited harrow hctx hb
  · -- argVarsScoped.
    exact genMutuallyRecursiveDatatypesOrdered_argVarsScoped hb

/-! ### The default corollary against the real Strata Core context

`genMutuallyRecursiveDatatypesOrdered_MutualADTWF` is stated against an abstract `C : LContext
CoreLParams` plus a `ContextOk` hypothesis. Below we discharge that hypothesis for
the concrete context that Strata Core actually uses (`Core.KnownTypes` + empty
datatypes) and show the generator is `MutualADTWF`-sound against it, with
`extraReserved` instantiated with `Core.KnownTypes.keywords` — the extra name pool
the caller must forbid so a block name cannot collide with a symbol Core already
knows.

The concrete membership facts about `Core.KnownTypes.keywords` (a `HashMap`
whose entries do not kernel-reduce) are discharged by `native_decide`, which
adds the `Lean.ofReduceBool` axiom to this corollary only. The abstract
`genMutuallyRecursiveDatatypesOrdered_MutualADTWF` remains axiom-clean. -/

/-- The Strata Core reference context: known types are `Core.KnownTypes`, and
    no user datatypes have been declared. -/
def coreContext : LContext CoreLParams :=
  { functions := .default, datatypes := #[],
    knownTypes := Core.KnownTypes, idents := {} }

/-- The generator's default vocabulary satisfies `ContextOk` for `coreContext`,
    with `extraReserved` set to `Core.KnownTypes.keywords` — this is what lets a
    freshly generated `d.name` avoid every symbol Core already knows (`Triggers`,
    `bitvec`, `TriggerGroup`, ...) even though the generator does not reference
    them. -/
theorem defaultContextOk :
    ContextOk coreContext defaultBaseTypes defaultTyCons Core.KnownTypes.keywords := by
  refine
    { base_known := ?_, tyCon_known := ?_, arrow_known := ?_,
      knownTypes_reserved := ?_, datatypes_reserved := ?_,
      base_external := ?_, tyCon_external := ?_, arrow_external := ?_ }
  · -- Every default base type is a known primitive of `coreContext`.
    intro b hb
    left; simp [defaultBaseTypes, nullaryBaseTypeNames] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> (show _ ∈ Core.KnownTypes.keywords; native_decide)
  · -- Every default type constructor is a known primitive of `coreContext`.
    intro kc hkc
    left; simp [defaultTyCons] at hkc
    rcases hkc with rfl | rfl <;> (show _ ∈ Core.KnownTypes.keywords; native_decide)
  · -- `"arrow"` is a known primitive of `coreContext`.
    show "arrow" ∈ Core.KnownTypes.keywords; native_decide
  · -- Every `coreContext` known-type is in the extra reserved list, verbatim.
    intro k hk
    simp only [initialReserved, List.mem_cons, List.mem_append]
    right; right
    exact hk
  · -- No datatypes in `coreContext`, so this is vacuous.
    intro n hn
    simp [coreContext, TypeFactory.allTypeNames, TypeFactory.allDatatypes] at hn
  · -- `coreContext.datatypes = #[]` ⇒ every `getType = none`.
    intro b _
    simp [coreContext, TypeFactory.getType, TypeFactory.allDatatypes]
  · intro kc _
    simp [coreContext, TypeFactory.getType, TypeFactory.allDatatypes]
  · simp [coreContext, TypeFactory.getType, TypeFactory.allDatatypes]

/-- **`MutualADTWF` for the default configuration against the Strata Core
    context.** Every block `genMutuallyRecursiveDatatypes` produces (at its default parameters,
    with `extraReserved` set to Core's known-type keywords) is `MutualADTWF` in
    `coreContext` — the context Core programs actually use. The single side
    condition (`defaultTyCons_ne_arrow`) is discharged by `decide`, and the eight
    `ContextOk` fields are discharged by `defaultContextOk`.

    Uses `native_decide` (for `Core.KnownTypes.keywords` membership), so this
    corollary depends on `Lean.ofReduceBool` in addition to the standard axioms.
    The abstract `genMutuallyRecursiveDatatypesOrdered_MutualADTWF` does not. -/
theorem genMutuallyRecursiveDatatypesOrdered_MutualADTWF_default
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypesOrdered (G := SetGen.Set) defaultBaseTypes
            defaultTyCons maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs
            maxArgs maxSize Core.KnownTypes.keywords)) :
    MutualADTWF coreContext block :=
  genMutuallyRecursiveDatatypesOrdered_MutualADTWF defaultTyCons_ne_arrow defaultContextOk hb

/-! ### Permutation invariance of `MutualADTWF`, and the shuffled generator

`genMutuallyRecursiveDatatypes` produces the ordered block, then `shuffle`s it.
`MutualADTWF_perm` shows the spec survives that permutation, and the shuffle-aware
`genMutuallyRecursiveDatatypes_MutualADTWF` (+ `_default`) transport the ordered
soundness results to the actual (shuffled) output. -/

/-- **`MutualADTWF` is invariant under permutation of the block.** Every field is
    either a `∀ d ∈ block, …` fact (`Perm` preserves membership), a fact about
    `block.map (·.name)` (`Perm`-stable, as are `Nodup`/`≠ []`), or the inhabitance
    field — which mentions `block` only through `C.datatypes.push block`, whose
    `getType` is `Perm`-invariant (`getType_push_perm`), so inhabitance transfers by
    `tySymInhab_getType_congr`. -/
theorem MutualADTWF_perm {C : LContext CoreLParams} {block block' : MutualDatatype Unit}
    (hperm : block.Perm block') (h : MutualADTWF C block) : MutualADTWF C block' := by
  have hmem : ∀ {d}, d ∈ block' → d ∈ block := fun hd => hperm.mem_iff.mpr hd
  have hnames : block'.map (·.name) = block.map (·.name) → True := fun _ => trivial
  -- `block`'s names are `Perm` `block'`'s names.
  have hnamesperm : (block.map (·.name)).Perm (block'.map (·.name)) := hperm.map (·.name)
  refine
    { nonempty := ?_
      namesNodup := (hnamesperm.nodup_iff).mp h.namesNodup
      namesFresh := fun d hd => h.namesFresh d (hmem hd)
      namesNew := fun d hd => h.namesNew d (hmem hd)
      argsWF := ?_
      refsKnown := ?_
      inhabited := ?_
      argVarsScoped := fun d hd => h.argVarsScoped d (hmem hd) }
  · -- nonempty: `block'` is nonempty because `block` is and they are `Perm`.
    intro hnil
    have : block.Perm [] := hnil ▸ hperm
    exact h.nonempty this.eq_nil
  · -- argsWF: `ConstrArgWF block' = ConstrArgWF block` up to the block-name set,
    -- which `Perm` preserves; the relations only consult `block.map (·.name)`.
    intro d hd c hc arg harg
    exact constrArgWF_perm hnamesperm hperm (h.argsWF d (hmem hd) c hc arg harg)
  · -- refsKnown: the block-name disjunct is `Perm`-stable.
    intro d hd c hc arg harg r hr
    rcases h.refsKnown d (hmem hd) c hc arg harg r hr with hk | hdt | hblk
    · exact Or.inl hk
    · exact Or.inr (Or.inl hdt)
    · exact Or.inr (Or.inr (hnamesperm.mem_iff.mp hblk))
  · -- inhabited: transfer along the `Perm`-invariant `getType` of the pushed factory.
    intro d hd
    have hget : ∀ n, TypeFactory.getType (C.datatypes.push block) n
        = TypeFactory.getType (C.datatypes.push block') n :=
      getType_push_perm hperm h.namesNodup
    exact tySymInhab_getType_congr hget (h.inhabited d (hmem hd))

/-- **Main soundness theorem for the (shuffled) generator.** Every block
    `genMutuallyRecursiveDatatypes` produces is `MutualADTWF` in any `ContextOk`
    context. The output is a `shuffle` of the ordered block, so this is the ordered
    result (`genMutuallyRecursiveDatatypesOrdered_MutualADTWF`) transported across
    the permutation by `MutualADTWF_perm`. -/
theorem genMutuallyRecursiveDatatypes_MutualADTWF {baseTypes : List String} {tyCons : List KnownTyCon}
    {C : LContext CoreLParams}
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {extraReserved : List String} {block : MutualDatatype Unit}
    (harrow : ∀ kc ∈ tyCons, kc.1 ≠ "arrow")
    (hctx : ContextOk C baseTypes tyCons extraReserved)
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
            maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs
            maxSize extraReserved)) :
    MutualADTWF C block := by
  -- Unfold the shuffle: `block` is a permutation of an ordered block `block₀`.
  simp only [genMutuallyRecursiveDatatypes, mem_support_bind_iff, mem_support_pure_iff] at hb
  obtain ⟨block₀, hb₀, p, hp, rfl⟩ := hb
  -- `p.2 : block₀.Perm p.1`; the returned block is `p.1`.
  exact MutualADTWF_perm p.2
    (genMutuallyRecursiveDatatypesOrdered_MutualADTWF harrow hctx hb₀)

/-- **`MutualADTWF` for the default configuration** (shuffled generator against the
    Strata Core context). -/
theorem genMutuallyRecursiveDatatypes_MutualADTWF_default
    {maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat}
    {block : MutualDatatype Unit}
    (hb : block ∈ SetGen.support (genMutuallyRecursiveDatatypes (G := SetGen.Set) defaultBaseTypes
            defaultTyCons maxExtraDatatypes maxTyParams maxExtraBaseConstrs maxRecConstrs
            maxArgs maxSize Core.KnownTypes.keywords)) :
    MutualADTWF coreContext block :=
  genMutuallyRecursiveDatatypes_MutualADTWF defaultTyCons_ne_arrow defaultContextOk hb

end MutualADTWFSoundness

/-! ## Completeness, and the exact sense in which it holds

Completeness holds against `MutualADTWF` together with the single `ArityOk` side
condition (`genArgTy_complete_of_MutualADTWF`), and the stronger reading —
completeness w.r.t. `MutualADTWF` *alone* — is genuinely false
(`not_complete_without_arity`), because `MutualADTWF` does not check arity. -/

section Completeness

/-! ### The one gap `MutualADTWF` leaves open: arity

`MutualADTWF` fixes everything the generator restricts *except* the arity of
applied type constructors (see `docs/mutualadtwf-arity-gap.md`). `ArityOk` names
exactly that gap, and nothing more:

* it says nothing about free type variables — `MutualADTWF.argVarsScoped` scopes
  them;
* it says nothing about which occurrences of a block name are uniform — the
  generator emits a block name applied to exactly that datatype's `typeArgs`, and
  `ConstrArgWF` (`StrictPosUnif` / `UniformOccur.self`) forces every block-name
  headed argument type to have that shape, which `constrArgWF_self_uniform` reads
  back off;
* it *only* pins the argument count of every non-block, non-arrow application.

Because the generator's referenceable constructors are supplied as a name↔arity
registry (`baseTypes` are the arity-0 names, `tyCons` the `(name, arity)` pairs),
"used at its declared arity" is phrased against that registry: a nullary
application needs `k ∈ baseTypes`, and an arity-`n` one needs `(k, n) ∈ tyCons`.
The `size` at which the type is reachable is existential, per the chosen framing:
we exhibit *some* budget rather than relating `size` to depth arithmetically. -/

/-- **The single arity side condition.** A `Prop`-valued recursion over the type
    requiring every applied type constructor to be used at its declared arity —
    the one discipline `MutualADTWF` does not enforce. This is a `def`, not an
    inductive relation.

    * a `bitvec` or `ftvar` is always arity-correct (variable scoping is
      `MutualADTWF.argVarsScoped`'s job, not tracked here);
    * a block-name-headed application (`k ∈ blockNames`) is left unconstrained here
      — `ConstrArgWF` already forces it to be the uniform recursive occurrence;
    * an `arrow t1 t2` (i.e. `"arrow"` at exactly two arguments) needs both sides
      arity-correct;
    * any other `tcons k args` must be applied at its declared arity:
      `(k, args.length) ∈ tyCons` when `args ≠ []`, or `k ∈ baseTypes` when
      `args = []`, with every argument arity-correct. -/
def ArityOk (baseTypes : List String) (tyCons : List KnownTyCon)
    (blockNames : List String) :
    LMonoTy → Prop
  | .bitvec _ => True
  | .ftvar _ => True
  | .tcons k args =>
    if k ∈ blockNames then True
    else if k = "arrow" then
      match args with
      | [t1, t2] =>
        ArityOk baseTypes tyCons blockNames t1 ∧
        ArityOk baseTypes tyCons blockNames t2
      | _ => False
    else if args = [] then k ∈ baseTypes
    else (k, args.length) ∈ tyCons ∧
      ∀ a ∈ args, ArityOk baseTypes tyCons blockNames a

/-- **`genArgTy`'s support is monotone in the size budget.** A type reachable
    within `size` fuel is reachable within any larger budget: leaves are available
    at every size, and the arrow/app fuel `size / 2` only grows. This lets the
    completeness proof pick a *single* budget large enough for all of a type's
    subterms, so the reachable `size` can be quantified existentially. Strong
    induction on `size` through the one-step decomposition `genArgTy_mem_iff`. -/
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

/-- A shared-size version of the per-argument reachability facts: if every element
    of `args` is reachable at *some* size (flag `false`), they are all reachable at
    *one common* size, by `genArgTy_mono`. -/
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

/-- **Completeness of `genArgTy`, stated against the spec.** A constructor-argument
    type that is `ConstrArgWF block`, whose free type variables are all declared
    (`varsScoped` — supplied by `MutualADTWF.argVarsScoped`), and which satisfies
    the single arity side condition `ArityOk`, is reachable at *some* size —
    provided every block datatype's uniform reference is available in `blockRefs`
    (`hcover`). The `size` is existential (chosen framing); the flag is derived
    from the absence premise, which `ConstrArgWF` supplies at every recursive
    position.

    Structural recursion on `ty`, building support membership directly through the
    one-step decomposition `genArgTy_mem_iff` and `genLeafTy_mem_iff` — no ad-hoc
    inductive relation. Two key interplays: `ConstrArgWF` forbids block names in
    exactly the positions the generator draws at flag `false`, and — via
    `constrArgWF_self_uniform` — pins every block-name-headed occurrence to the
    uniform `n (n's typeArgs)`, which `hcover` places in `blockRefs`, so `ArityOk`
    need not mention it. -/
theorem genArgTy_complete_of_wf {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hcover : ∀ d ∈ block, (d.name, d.typeArgs.map .ftvar) ∈ blockRefs) :
    ∀ (ty : LMonoTy),
      ConstrArgWF block ty →
      (∀ v ∈ LMonoTy.freeVars ty, v ∈ tyParams) →
      ArityOk baseTypes tyCons (block.map (·.name)) ty →
      ∀ (rca : Bool), (rca = false → BlockAbsent block ty) →
      ∃ size, ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
        tyParams rca size) := by
  intro ty
  induction ty using LMonoTy.induct with
  | ftvar v =>
    intro _ hvars _ rca _
    -- `argVarsScoped` gives `v ∈ tyParams`; that is the `tyParam` leaf, at size 0.
    have hv : v ∈ tyParams := hvars v (by simp [LMonoTy.freeVars])
    refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
    exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨v, hv, rfl⟩)))
  | bitvec n =>
    intro _ _ _ rca _
    refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
    exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inl ⟨n, rfl⟩)
  | tcons k args ih =>
    intro hwf hvars hari rca habs
    by_cases hself : k ∈ block.map (·.name)
    · -- A block-name-headed occurrence. `ConstrArgWF` forces it to be uniform, i.e.
      -- `args = d.typeArgs.map .ftvar` for the block datatype `d` named `k`
      -- (`constrArgWF_self_uniform`); it is then the recursive-occurrence leaf,
      -- which forces `rca = true` (else `k` would appear at the head, contradicting
      -- the absence premise). `hcover` places the reference in `blockRefs`.
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
    · unfold ArityOk at hari
      rw [if_neg hself] at hari
      by_cases harrow : k = "arrow"
      · -- An arrow `t1 → t2`.
        subst harrow
        rw [if_pos rfl] at hari
        match args, hari, hwf, hvars, habs, ih with
        | [t1, t2], hari, hwf, hvars, habs, ih =>
          obtain ⟨ha1, ha2⟩ := hari
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
          obtain ⟨s1, h1⟩ := ih t1 (by simp) hwf1 hvars1 ha1 false (fun _ => hdom_abs)
          obtain ⟨s2, h2⟩ := ih t2 (by simp) hwf2 hvars2 ha2 rca
            (fun hr => by
              subst hr
              intro d' hd'
              have hab := habs rfl d' hd'
              rw [harr] at hab
              exact fun hap => hab (.arg _ _ _ (by simp) hap))
          refine ⟨2 * (max s1 s2) + 1,
            (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inl ⟨by omega, t1, t2, rfl,
              genArgTy_mono _ h1 (by omega), genArgTy_mono _ h2 (by omega)⟩))⟩
      · rw [if_neg harrow] at hari
        by_cases hnil : args = []
        · -- A base leaf `k` with no arguments, `k ∈ baseTypes`.
          subst hnil
          rw [if_pos rfl] at hari
          refine ⟨0, (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl ?_)⟩
          exact (genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inl ⟨k, hari, rfl⟩))
        · rw [if_neg hnil] at hari
          obtain ⟨hkc, hall⟩ := hari
          -- An applied known type constructor at its declared arity. Every block
          -- name is absent from every argument (the `headOther` case of `NotNested`).
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
              (hall a ha) false (fun _ => hargs_abs a ha))
          refine ⟨2 * S + 1,
            (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inr ⟨by omega, k, args, rfl,
              hkc, fun a ha => genArgTy_mono _ (hS a ha) (by omega)⟩))⟩

/-- **Per-type completeness, from the projected `MutualADTWF` fields plus arity.**
    A constructor-argument type that is `ConstrArgWF block` (the `argsWF` field),
    whose free variables are all declared (the `argVarsScoped` field), and which
    satisfies the single arity side condition `ArityOk`, is drawn by `genArgTy`
    with recursive occurrences allowed (`rca := true`) at some size, given the
    block's references are covered by `blockRefs` (`hcover`). Taking `rca := true`
    discharges the flag premise vacuously, so no separate absence hypothesis is
    needed. -/
theorem genArgTy_complete_of_arity {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit} {blockRefs : List BlockRef}
    {tyParams : List TyIdentifier} {ty : LMonoTy}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hcover : ∀ d ∈ block, (d.name, d.typeArgs.map .ftvar) ∈ blockRefs)
    (hwf : ConstrArgWF block ty)
    (hvars : ∀ v ∈ LMonoTy.freeVars ty, v ∈ tyParams)
    (hari : ArityOk baseTypes tyCons (block.map (·.name)) ty) :
    ∃ size, ty ∈ SetGen.support (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs
      tyParams true size) :=
  genArgTy_complete_of_wf hn hcover ty hwf hvars hari true (by simp)

open Core Core.TypeSpec in
/-- **Completeness with respect to `MutualADTWF`.** Every constructor-argument type
    of a block that is well-formed (`MutualADTWF C block`) *and* satisfies the
    single arity side condition `ArityOk` is reachable by `genArgTy` at some size,
    given the block's references are covered by `blockRefs` (`hcover`) and each
    datatype's constructor arguments are scoped to its own parameters (`argsWF`'s
    companion `argVarsScoped` supplies this via the block).

    This is the completeness statement phrased directly against the spec
    `MutualADTWF`: its `argsWF` field supplies `ConstrArgWF` and its `argVarsScoped`
    field supplies variable scoping, so the *only* extra hypotheses beyond
    `MutualADTWF` are `ArityOk` — exactly the arity discipline `MutualADTWF` does
    not enforce (`docs/mutualadtwf-arity-gap.md`) — and the generator-vocabulary
    assumptions `NamesOk` / `hcover` (that the generator's reference pool covers the
    block), neither a fact about the type. -/
theorem genArgTy_complete_of_MutualADTWF {baseTypes : List String}
    {tyCons : List KnownTyCon} {C : LContext CoreLParams} {block : MutualDatatype Unit}
    {blockRefs : List BlockRef}
    (hn : NamesOk baseTypes tyCons (block.map (·.name)))
    (hcover : ∀ d ∈ block, (d.name, d.typeArgs.map .ftvar) ∈ blockRefs)
    (hwf : MutualADTWF C block)
    (hari : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      ArityOk baseTypes tyCons (block.map (·.name)) arg.2) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∃ size, arg.2 ∈ SetGen.support
      (genArgTy (G := SetGen.Set) baseTypes tyCons blockRefs d.typeArgs true size) := by
  intro d hd c hc arg harg
  refine genArgTy_complete_of_arity hn hcover
    (hwf.argsWF d hd c hc arg harg)
    (hwf.argVarsScoped d hd c hc arg harg)
    (hari d hd c hc arg harg)

/-- A worked instance of completeness: for a list-like datatype `MyList a`, the
    argument type `a → MyList a` (self-reference in the codomain, a type parameter
    in the domain) is reachable at size 1. This is the shape that matters — the
    generator really does reach genuinely recursive, strictly-positive types, not
    just leaves.

    Built directly through `genArgTy_mem_iff` / `genLeafTy_mem_iff`. Note the
    `false` domain flag is *forced*: the arrow decomposition generates the domain
    at flag `false`, so the type-parameter leaf `a` is reached there. The reference
    pool is the single block member `MyList a`. -/
example : (LMonoTy.arrow (.ftvar "a") (.tcons "MyList" [.ftvar "a"])) ∈
    SetGen.support (genArgTy (G := SetGen.Set) defaultBaseTypes defaultTyCons
      [("MyList", [.ftvar "a"])] ["a"] true 1) := by
  refine (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inr (Or.inl
    ⟨by omega, _, _, rfl, ?_, ?_⟩))
  · -- domain: the type parameter `a`, a leaf.
    exact (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl
      ((genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨"a", by simp, rfl⟩)))))
  · -- codomain: the uniform recursive occurrence `MyList a`, a leaf under `true`.
    exact (genArgTy_mem_iff _ _ _ _ _ _ _).mpr (Or.inl
      ((genLeafTy_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, ("MyList", [.ftvar "a"]), by simp, rfl⟩)))))

/-- **Why completeness needs the `ArityOk` side condition — the arity gap in
    `MutualADTWF`.** The ill-kinded type `Sequence a a` (the arity-1 `Sequence`
    applied to *two* arguments) is a perfectly well-formed constructor argument:
    the datatype's own name does not occur in it (given `d.name ≠ "Sequence"`), so
    `absent_constrArgWF` gives `ConstrArgWF [d]`, and its only free variable `a` is
    declared. Every field of `MutualADTWF` that mentions this type is therefore
    satisfied — `refsKnown` in particular only checks that `"Sequence"` *resolves*,
    never the arity it is applied at. Yet no `genArgTy` can produce it: the
    application branch draws `vectorOf arity` arguments, so `Sequence` is only ever
    emitted at its declared arity 1, never 2.

    This is exactly the gap `ArityOk` closes (its `tcons` case demands
    `("Sequence", 2) ∈ defaultTyCons`, which is false — `defaultTyCons` lists
    `Sequence` at arity 1): `genArgTy_complete_of_MutualADTWF` adds `ArityOk` as
    the single hypothesis beyond `MutualADTWF`, and this witness fails it. See
    `docs/mutualadtwf-arity-gap.md`.

    (Before issue #38 the canonical unreachability witness was `bitvec 7` — a width
    outside the then-fixed `bitvecWidths`. Now that widths are unconstrained, every
    bitvector *is* generated; and now that the completeness statement rests on
    `MutualADTWF`'s own scoping field rather than a bespoke predicate, the
    unbound-`ftvar` witness is ruled out by `argVarsScoped` rather than the side
    condition. The arity gap is what remains, and `ArityOk` rules it out.) -/
theorem not_complete_without_arity (d : LDatatype Unit)
    (a : TyIdentifier) (hd_ne : d.name ≠ "Sequence") (blockRefs : List BlockRef)
    (hbr : ∀ br ∈ blockRefs, br.1 = d.name) (rca : Bool) (size : Nat) :
    -- The witness is `ConstrArgWF` and well-scoped (into any `tyParams` containing
    -- `a`), so `MutualADTWF`'s per-type content holds…
    ConstrArgWF [d] (.tcons "Sequence" [.ftvar a, .ftvar a]) ∧
    (∀ v ∈ LMonoTy.freeVars (.tcons "Sequence" [.ftvar a, .ftvar a]), v = a) ∧
    -- …yet it violates the arity side condition…
    ¬ ArityOk defaultBaseTypes defaultTyCons [d.name]
        (.tcons "Sequence" [.ftvar a, .ftvar a]) ∧
    -- …and it is unreachable at every flag and size (for any block-`d.name`
    -- reference pool, e.g. the one `genMutuallyRecursiveDatatypes` supplies for `[d]`).
    (.tcons "Sequence" [.ftvar a, .ftvar a]) ∉ SetGen.support
      (genArgTy (G := SetGen.Set) defaultBaseTypes defaultTyCons blockRefs
        d.typeArgs rca size) := by
  -- `d.name` is absent: not the head (`d.name ≠ "Sequence"`) and not in an `ftvar`.
  have habsent : BlockAbsent [d] (.tcons "Sequence" [.ftvar a, .ftvar a]) := by
    intro d' hd'
    simp only [List.mem_singleton] at hd'; subst hd'
    intro hap
    generalize hty : LMonoTy.tcons "Sequence" [LMonoTy.ftvar a, LMonoTy.ftvar a] = t at hap
    cases hap with
    | head _ => injection hty with hn _; exact hd_ne hn.symm
    | arg _ _ t ht hat =>
      injection hty with _ hargs; subst hargs
      rcases List.mem_cons.mp ht with rfl | ht
      · cases hat
      · rcases List.mem_cons.mp ht with rfl | ht
        · cases hat
        · cases ht
  refine ⟨absent_constrArgWF habsent, ?_, ?_, ?_⟩
  · -- Free variables: exactly `a`.
    intro v hv
    simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil,
               List.mem_append, List.mem_singleton] at hv
    rcases hv with rfl | rfl <;> rfl
  · -- `ArityOk` fails: `("Sequence", 2) ∉ defaultTyCons` (it is there at arity 1).
    unfold ArityOk
    rw [if_neg (by simp only [List.mem_singleton]; exact fun h => hd_ne h.symm),
        if_neg (by decide : ¬ ("Sequence" = "arrow")),
        if_neg (by simp : ¬ ([LMonoTy.ftvar a, LMonoTy.ftvar a] = []))]
    rintro ⟨hkc, _⟩
    -- `hkc : ("Sequence", 2) ∈ defaultTyCons` after computing the length.
    simp only [List.length_cons, List.length_nil] at hkc
    exact absurd hkc (by decide)
  · -- Unreachable: `Sequence` at two arguments matches no generator branch.
    intro hmem
    rcases (genArgTy_mem_iff _ _ _ _ _ _ _).mp hmem with
      hleaf | ⟨_, _, _, hcon, _⟩ | ⟨_, k, args, hcon, hkc, _⟩
    · -- Not a leaf: a two-argument `.tcons` is neither a bitvec, an empty-args base
      -- type, an `ftvar`, nor a block occurrence (its head would be `d.name`, but
      -- `"Sequence" ≠ d.name`).
      rcases (genLeafTy_mem_iff _ _ _ _ _).mp hleaf with
        ⟨_, hcon⟩ | ⟨_, _, hcon⟩ | ⟨_, _, hcon⟩ | ⟨_, br, hbrmem, hcon⟩
      · exact absurd hcon (by simp)
      · exact absurd hcon (by simp)
      · exact absurd hcon (by simp)
      · -- `hcon : Sequence… = br.1 br.2` with `br.1 = d.name ≠ "Sequence"`.
        rw [hbr br hbrmem] at hcon
        exact hd_ne (by injection hcon with h _; exact h.symm)
    · -- Not an arrow: `"Sequence" ≠ "arrow"`.
      exact absurd hcon (by simp [LMonoTy.arrow])
    · -- An application, but then `("Sequence", 2) ∈ defaultTyCons` — false.
      injection hcon with hk hargs
      subst hk hargs
      -- The argument list is `[ftvar a, ftvar a]`, so its length is 2.
      simp only [List.length_cons, List.length_nil] at hkc
      exact absurd hkc (by decide)

end Completeness

end DatatypeGen
