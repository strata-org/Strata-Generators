import StrataGenerators.ProgramGen
import StrataGenerators.ProgramGen.ContextOkPreserve
import StrataGenerators.HasTypeAGen
import StrataGenerators.HasTypeAGen.AnnotFacts
import Strata.Languages.Core.WeakTypeSpec
import Strata.DL.Lambda.LExprTypeEnvProps
import Strata.Languages.Core.FactoryProps
import Strata.Languages.Core.TypeCheckSound.Datatype
import Strata.DL.Lambda.TypeFactoryProps
import Strata.DL.Lambda.DatatypeFactoryWFProps
import Strata.DL.Lambda.LTyTypeProps

/-!
# Soundness of the whole-program generator

Every program `ProgramGen.genProgram` produces satisfies the weak program typing
`Core.TypeSpec.ProgramHasTypeW` in `programContext` with no variable in scope.

The proof is layered to mirror the generator:

* **Bridge lemmas** turn a successful checker add into the exact premise a
  `DeclHasTypeW` constructor asks for (`FactoryExtendedBy` from
  `addFactoryFunctionWithError = .ok`).
* **The soundness of one declaration step.** The support of each `genDecl*` step holds a pair of a
  declaration list and a state, and that list is weakly typed from the context of the input state
  to the context of the output state. The steps whose proofs need the function and procedure
  generators are in `StrataGenerators.ProgramGen.SoundProgram`.
* **The fold** chains per-step soundness over the whole program, and the top-level theorem adds
  the distinctness of names.

Everything is stated against `SetGen.Set` (the generator's support semantics),
following the existing sub-generator proofs.
-/

open Lambda RandomChoice Core Core.TypeSpec Imperative SetGen
open StrataGenerators.AnnotFacts
open DatatypeGen
open StrataGenerators.Procedure

namespace ProgramGen

/-! ## Name tracking for `getNames.Nodup`

Each declaration step emits declarations whose names are drawn fresh against
`s.reserved` and then added to `reserved`. `NamesStep s ds s'` bundles exactly the
facts a fold needs to conclude the whole program's names are `Nodup`: the new
`reserved` extends the old by precisely the emitted names, those names are fresh,
and they are internally distinct. -/

/-- The string names of a declaration list (what `reserved` tracks). -/
def declNames (ds : List Decl) : List String :=
  (ds.flatMap Decl.names).map (·.name)

/-- `declNames` distributes over declaration-list append. -/
theorem declNames_append (ds₁ ds₂ : List Decl) :
    declNames (ds₁ ++ ds₂) = declNames ds₁ ++ declNames ds₂ := by
  simp [declNames]

/-- The name-tracking postcondition of a declaration step. `reserved` grows by
    exactly the emitted names, as a *set*. The generator puts each new name at the front, so the literal order
    is reversed across the fold, and only the membership matters for the claim about distinct names. -/
structure NamesStep (s : GenState) (ds : List Decl) (s' : GenState) : Prop where
  /-- Every name reserved after the step is either newly emitted or was already
      reserved. -/
  reserved_sub : ∀ x ∈ s'.reserved, x ∈ declNames ds ∨ x ∈ s.reserved
  /-- Every previously-reserved name stays reserved. -/
  reserved_mono : ∀ x ∈ s.reserved, x ∈ s'.reserved
  /-- Every emitted name becomes reserved. -/
  emitted_reserved : ∀ x ∈ declNames ds, x ∈ s'.reserved
  /-- The emitted names are fresh w.r.t. the incoming reserved set. -/
  fresh : ∀ x ∈ declNames ds, x ∉ s.reserved
  /-- The emitted names are internally distinct. -/
  nodup : (declNames ds).Nodup

/-- Build a `NamesStep` from the concrete "reserved grew by exactly these names,
    prepended" form that each step establishes. -/
theorem namesStep_of_prepend {s s' : GenState} {ds : List Decl}
    (heq : s'.reserved = declNames ds ++ s.reserved)
    (hfresh : ∀ x ∈ declNames ds, x ∉ s.reserved)
    (hnodup : (declNames ds).Nodup) :
    NamesStep s ds s' :=
  { reserved_sub := by intro x hx; rw [heq] at hx; exact List.mem_append.mp hx
    reserved_mono := by intro x hx; rw [heq]; exact List.mem_append_right _ hx
    emitted_reserved := by intro x hx; rw [heq]; exact List.mem_append_left _ hx
    fresh := hfresh
    nodup := hnodup }

/-- `NamesStep` for a step that emits nothing and leaves `reserved` unchanged. -/
theorem namesStep_nil {s : GenState} : NamesStep s [] s :=
  namesStep_of_prepend (by simp [declNames]) (by simp [declNames]) (by simp [declNames])

/-! ## Declaration names the checker accepts -/

/-- The fallback name, a run of `x` characters, uses no reserved prefix. -/
theorem fallbackName_allowed (reserved : List String) :
    isAllowedName (DatatypeGen.fallbackName reserved) = true := by
  simp only [DatatypeGen.fallbackName, indexedFreshName]
  rw [isAllowedName_eq_toList]
  simp [reservedNamePrefixes, List.replicate_succ, List.isPrefixOf, Lambda.genTyPrefix,
    skolemPrefix, Lambda.elimTyPrefix]

/-- A name `genDeclName reserved` draws is absent from `reserved` and uses no reserved prefix. -/
theorem genDeclName_fresh {reserved : List String} {nm : String}
    (h : nm ∈ SetGen.support (genDeclName (G := SetGen.Set) reserved)) :
    nm ∉ reserved ∧ isAllowedName nm = true := by
  simp only [genDeclName, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨d, hd, rfl⟩ := h
  split
  · rename_i hallowed
    exact ⟨DatatypeGen.genFreshName_fresh reserved d hd, hallowed⟩
  · exact ⟨DatatypeGen.fallbackName_not_mem reserved, fallbackName_allowed reserved⟩

/-- The fallback name, a run of `x` characters, is not a local type name. -/
theorem fallbackName_not_local (reserved : List String) :
    StrataGenerators.Stmt.isLocalTypeName (DatatypeGen.fallbackName reserved) = false := by
  rw [Bool.eq_false_iff]
  intro hlocal
  simp only [StrataGenerators.Stmt.isLocalTypeName, DatatypeGen.fallbackName, indexedFreshName,
    String.startsWith_string_iff, String.toList_ofList] at hlocal
  have hl : 'l' ∈ StrataGenerators.Stmt.localTypePrefix.toList := by decide +kernel
  exact absurd (List.mem_replicate.mp (hlocal.subset hl)).2 (by decide)

/-- A name `genDeclTypeName reserved` draws is absent from `reserved` and uses no reserved
    prefix. -/
theorem genDeclTypeName_fresh {reserved : List String} {nm : String}
    (h : nm ∈ SetGen.support (genDeclTypeName (G := SetGen.Set) reserved)) :
    nm ∉ reserved ∧ isAllowedName nm = true := by
  simp only [genDeclTypeName, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨d, hd, rfl⟩ := h
  split
  · exact ⟨DatatypeGen.fallbackName_not_mem reserved, fallbackName_allowed reserved⟩
  · exact genDeclName_fresh hd

/-- A name `genDeclTypeName reserved` draws is not a local type name. -/
theorem genDeclTypeName_not_local {reserved : List String} {nm : String}
    (h : nm ∈ SetGen.support (genDeclTypeName (G := SetGen.Set) reserved)) :
    StrataGenerators.Stmt.isLocalTypeName nm = false := by
  simp only [genDeclTypeName, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨d, _, rfl⟩ := h
  split
  · exact fallbackName_not_local reserved
  · rename_i hlocal
    exact Bool.eq_false_iff.mpr hlocal

/-! ## Chaining declaration-list typings -/

/-- Weak declaration-list typings compose over list append, threading the context through the
    split point. -/
theorem declsHasTypeW_append {P : Program} {C C' C'' : LContext CoreLParams} {ts : TypeScopes}
    {ds₁ ds₂ : List Decl}
    (h₁ : DeclsHasTypeW P C ts ds₁ C') (h₂ : DeclsHasTypeW P C' ts ds₂ C'') :
    DeclsHasTypeW P C ts (ds₁ ++ ds₂) C'' := by
  induction h₁ with
  | nil => exact h₂
  | cons _ _ _ _ _ _ hd _ ih => exact DeclsHasTypeW.cons _ _ _ _ _ _ hd (ih h₂)

/-! ## Bridge lemmas -/

/-- Membership in a pushed factory, proved by unfolding `Factory.push`'s effect
    on the `nameMap` inside it, which is a hash map. The corresponding lemma of Strata is private to its own
    `module`, so this file proves the fact again. -/
theorem mem_push_iff (F : Factory CoreLParams) (fn : LFunc CoreLParams)
    (h : ¬ fn.name.name ∈ F) (name : String) :
    name ∈ F.push fn h ↔ name = fn.name.name ∨ name ∈ F := by
  simp +instances only [Lambda.Factory.instMem, Lambda.Factory.mem, Lambda.Factory.push]
  simp only [Std.HashMap.mem_insert]
  constructor <;> intro hm <;> grind

/-- Looking up a name in a pushed factory returns the pushed function at its name and the old
    entry elsewhere. -/
theorem getElem?_push (F : Factory CoreLParams) (fn : LFunc CoreLParams)
    (h : ¬ fn.name.name ∈ F) (name : String) :
    (F.push fn h)[name]? = if name = fn.name.name then some fn else F[name]? := by
  simp +instances only [Lambda.Factory.push, Lambda.Factory.instGetElem?, Lambda.Factory.get?]
  grind

/-- A name with a factory entry is a member of the factory. -/
theorem mem_of_getElem?_eq_some {F : Factory CoreLParams} {name : String}
    {g : LFunc CoreLParams} (h : F[name]? = some g) : name ∈ F := by
  simp +instances only [Lambda.Factory.instGetElem?, Lambda.Factory.get?,
    Lambda.Factory.instMem, Lambda.Factory.mem] at h ⊢
  grind

/-- A successful `addFactoryFunctionWithError C fn = .ok C'` makes `C'` the extension of `C` by
    exactly `fn`: old entries are unchanged and `fn`'s name stores `fn` itself. -/
theorem factoryExtendedBy_of_addFactory
    {C C' : LContext CoreLParams} {fn : LFunc CoreLParams}
    (h : C.addFactoryFunctionWithError fn = .ok C') :
    FactoryExtendedBy (fun f g => g = f) C C' [fn] := by
  unfold LContext.addFactoryFunctionWithError at h
  -- `tryPush` unfolds to a `dite` on `fn.name.name ∈ C.functions`.
  unfold Lambda.Factory.tryPush at h
  by_cases hmem : fn.name.name ∈ C.functions
  · rw [dif_pos hmem] at h
    simp only [bind, Except.bind] at h
    exact absurd h (by simp)
  · simp only [hmem, dif_neg, not_false_iff, bind, Except.bind, Except.ok.injEq] at h
    -- Now `C' = { C with functions := C.functions.push fn hmem }`.
    subst h
    refine
      { knownTypes_eq := rfl
        datatypes_eq := rfl
        idents_eq := rfl
        rigidTypeVars_eq := rfl
        preserves_old := ?_
        contains_new := ?_
        no_other := ?_ }
    · intro nm g hg
      have hne : nm ≠ fn.name.name := by
        rintro rfl
        exact hmem (mem_of_getElem?_eq_some hg)
      simp only [getElem?_push C.functions fn hmem nm, hne, if_false]
      exact hg
    · intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨f, by simp only [getElem?_push C.functions f hmem, if_true], rfl⟩
    · intro nm hnm
      rcases (mem_push_iff C.functions fn hmem nm).mp hnm with rfl | hmem'
      · right; simp
      · left; exact hmem'

/-- A successful `addFactoryFunctionWithError` means the function's name was not yet in the
    table: adding a name that is already present fails. -/
theorem addFactory_name_fresh {C C' : LContext CoreLParams} {fn : LFunc CoreLParams}
    (h : C.addFactoryFunctionWithError fn = .ok C') : fn.name.name ∉ C.functions := by
  intro hmem
  unfold LContext.addFactoryFunctionWithError Lambda.Factory.tryPush at h
  rw [dif_pos hmem] at h
  simp only [bind, Except.bind] at h
  exact absurd h (by simp)

/-- A successful `addFactoryFunctionWithError` changes only `functions`; the
    `knownTypes` and `datatypes` fields (all `ContextOk` mentions) are unchanged. -/
theorem addFactory_fields {C C' : LContext CoreLParams} {fn : LFunc CoreLParams}
    (h : C.addFactoryFunctionWithError fn = .ok C') :
    C'.knownTypes = C.knownTypes ∧ C'.datatypes = C.datatypes := by
  unfold LContext.addFactoryFunctionWithError at h
  cases hp : C.functions.tryPush fn with
  | error e => simp [hp, bind, Except.bind] at h
  | ok f => simp [hp, bind, Except.bind] at h; subst h; exact ⟨rfl, rfl⟩

/-- A successful `addFactoryFunctionWithError` leaves `rigidTypeVars` unchanged. -/
theorem addFactory_rigid {C C' : LContext CoreLParams} {fn : LFunc CoreLParams}
    (h : C.addFactoryFunctionWithError fn = .ok C') :
    C'.rigidTypeVars = C.rigidTypeVars := by
  unfold LContext.addFactoryFunctionWithError at h
  cases hp : C.functions.tryPush fn with
  | error e => simp [hp, bind, Except.bind] at h
  | ok f => simp [hp, bind, Except.bind] at h; subst h; rfl

/-- `ContextOk` is preserved by `addFactoryFunctionWithError`: no `ContextOk`
    field mentions `functions`, and every other field is unchanged. -/
theorem contextOk_addFactory {C C' : LContext CoreLParams} {fn : LFunc CoreLParams}
    {bt : List String} {tc : List DatatypeGen.KnownTyCon} {R : List String}
    (hok : DatatypeGen.ContextOk C bt tc R)
    (h : C.addFactoryFunctionWithError fn = .ok C') :
    DatatypeGen.ContextOk C' bt tc R := by
  obtain ⟨hkt, hdt⟩ := addFactory_fields h
  refine
    { base_known := ?_, tyCon_known := ?_, arrow_known := ?_,
      base_arity := ?_, tyCon_arity := ?_, arrow_arity := ?_,
      knownTypes_reserved := ?_, datatypes_reserved := ?_,
      base_external := ?_, tyCon_external := ?_, arrow_external := ?_ }
  · rw [hkt, hdt]; exact hok.base_known
  · rw [hkt, hdt]; exact hok.tyCon_known
  · rw [hkt]; exact hok.arrow_known
  · rw [hkt]; exact hok.base_arity
  · rw [hkt]; exact hok.tyCon_arity
  · rw [hkt]; exact hok.arrow_arity
  · rw [hkt]; exact hok.knownTypes_reserved
  · rw [hdt]; exact hok.datatypes_reserved
  · rw [hdt]; exact hok.base_external
  · rw [hdt]; exact hok.tyCon_external
  · rw [hdt]; exact hok.arrow_external

/-- A successful `addKnownTypeWithError {nm, ar}` sets `knownTypes` to
    `insertIfNew nm ar` and leaves `datatypes` unchanged. -/
theorem addKnownType_fields {C C' : LContext CoreLParams} {nm : String} {ar : Nat}
    (h : C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    C'.knownTypes = C.knownTypes.insertIfNew nm ar ∧ C'.datatypes = C.datatypes := by
  unfold LContext.addKnownTypeWithError KnownTypes.addWithError Identifiers.addWithError at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i heq
    split at heq
    · exact absurd heq (by simp)
    · simp only [Except.ok.injEq] at heq h
      subst heq h
      refine ⟨?_, rfl⟩
      show (Std.HashMap.containsThenInsertIfNew C.knownTypes nm
        (KnownType.arity { name := nm, metadata := ar })).snd = _
      rw [Std.HashMap.containsThenInsertIfNew_snd]
      rfl

/-- A successful `addKnownTypeWithError` implies the name was *not* already registered:
    the underlying `Identifiers.addWithError` errors on a clash. -/
theorem addKnownType_name_fresh {C C' : LContext CoreLParams} {nm : String} {ar : Nat}
    (h : C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    nm ∉ C.knownTypes := by
  unfold LContext.addKnownTypeWithError KnownTypes.addWithError Identifiers.addWithError at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i heq
    split at heq
    · exact absurd heq (by simp)
    · rename_i hcontains
      rw [Std.HashMap.containsThenInsertIfNew_fst] at hcontains
      simpa using hcontains

/-- A successful `addKnownTypeWithError` leaves `rigidTypeVars` unchanged. -/
theorem addKnownType_rigid {C C' : LContext CoreLParams} {nm : String} {ar : Nat}
    (h : C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    C'.rigidTypeVars = C.rigidTypeVars := by
  unfold LContext.addKnownTypeWithError KnownTypes.addWithError Identifiers.addWithError at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i heq
    split at heq
    · exact absurd heq (by simp)
    · simp only [Except.ok.injEq] at heq h; subst heq h; rfl

/-- Every key of `insertIfNew nm ar` is `nm` or an old key. -/
theorem mem_keys_insertIfNew_cases {ks : KnownTypes} {nm : String} {ar : Nat} {k : String}
    (h : k ∈ (ks.insertIfNew nm ar).keys) : k = nm ∨ k ∈ ks.keys := by
  rw [Std.HashMap.mem_keys] at h ⊢
  rcases Std.HashMap.mem_insertIfNew.mp h with hb | hmem
  · have : nm = k := by simpa using hb
    exact Or.inl this.symm
  · exact Or.inr hmem

/-- Old keys survive `insertIfNew`. -/
theorem mem_keys_insertIfNew_of_mem {ks : KnownTypes} {nm : String} {ar : Nat} {k : String}
    (h : k ∈ ks.keys) : k ∈ (ks.insertIfNew nm ar).keys := by
  rw [Std.HashMap.mem_keys] at h ⊢
  exact Std.HashMap.mem_insertIfNew.mpr (Or.inr h)

/-- `ContextOk` is preserved by `addKnownTypeWithError` when the new type's name
    is already reserved. Adding a known type only grows `knownTypes` and never
    touches `datatypes`, so the external/known fields transfer. -/
theorem contextOk_addKnownType {C C' : LContext CoreLParams} {nm : String} {ar : Nat}
    {bt : List String} {tc : List DatatypeGen.KnownTyCon} {R : List String}
    (hok : DatatypeGen.ContextOk C bt tc R) (hnmR : nm ∈ R)
    (h : C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    DatatypeGen.ContextOk C' bt tc R := by
  obtain ⟨hkt, hdt⟩ := addKnownType_fields h
  -- `keywords = keys`; monotone under insertIfNew.
  have hkw : ∀ k, k ∈ C.knownTypes.keywords → k ∈ C'.knownTypes.keywords := by
    intro k hk; rw [hkt]; exact mem_keys_insertIfNew_of_mem hk
  refine
    { base_known := ?_, tyCon_known := ?_, arrow_known := ?_,
      base_arity := ?_, tyCon_arity := ?_, arrow_arity := ?_,
      knownTypes_reserved := ?_, datatypes_reserved := ?_,
      base_external := ?_, tyCon_external := ?_, arrow_external := ?_ }
  · intro b hb; rcases hok.base_known b hb with hk | hd
    · exact Or.inl (hkw b hk)
    · exact Or.inr (by rw [hdt]; exact hd)
  · intro kc hkc; rcases hok.tyCon_known kc hkc with hk | hd
    · exact Or.inl (hkw kc.1 hk)
    · exact Or.inr (by rw [hdt]; exact hd)
  · exact hkw "arrow" hok.arrow_known
  -- Arities: `insertIfNew` never overwrites, so every old binding survives.
  · intro b hb
    rw [hkt]; exact getElem?_insertIfNew_of_getElem? (hok.base_arity b hb)
  · intro kc hkc
    rw [hkt]; exact getElem?_insertIfNew_of_getElem? (hok.tyCon_arity kc hkc)
  · rw [hkt]; exact getElem?_insertIfNew_of_getElem? hok.arrow_arity
  · intro k hk
    rw [hkt] at hk
    rcases mem_keys_insertIfNew_cases hk with rfl | hold
    · -- new name `nm ∈ R ⊆ initialReserved bt tc R`.
      simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (hnmR))
    · exact hok.knownTypes_reserved k hold
  · rw [hdt]; exact hok.datatypes_reserved
  · rw [hdt]; exact hok.base_external
  · rw [hdt]; exact hok.tyCon_external
  · rw [hdt]; exact hok.arrow_external

/-! ## `ContextOk` at a *grown* pool (interleaving direction (2))

`contextOk_addKnownType` keeps `ContextOk` at a *fixed* pool across an
abstract-type add. To let a later datatype block *reference* the new abstract
type, the pool itself must grow. Therefore a proof must establish `ContextOk` again,
with `nm` added to `baseTypes` (arity 0) or `tyCons` (arity ≥ 1).

Two facts about the new entry carry it:

* **known**: `nm ∈ C'.knownTypes.keywords`, immediate from the `insertIfNew` the
  gate ran, giving `base_known`/`tyCon_known`;
* **external**: `C'.datatypes.getType nm = none`. `addKnownTypeWithError` leaves
  `datatypes` unchanged, so this is a fact about `C`. The caller gives it, from
  the fold's `datatypesReserved` invariant plus `nm ∉ reserved`. -/

/-- A name absent from `allTypeNames` resolves to `none`. Contrapositive of
    `name_mem_allTypeNames_of_getType`. -/
theorem getType_eq_none_of_not_mem {F : @TypeFactory Unit} {name : String}
    (h : name ∉ F.allTypeNames) : F.getType name = none := by
  rcases hs : F.getType name with _ | d
  · rfl
  · exact absurd (DatatypeGen.name_mem_allTypeNames_of_getType hs) h

/-- A name that *is* in `allTypeNames` does not resolve to `none`. Converse
    direction of `getType_eq_none_of_not_mem`. -/
theorem getType_ne_none_of_mem_allTypeNames {F : @TypeFactory Unit} {name : String}
    (h : name ∈ F.allTypeNames) : F.getType name ≠ none := by
  obtain ⟨d, hd, hdname⟩ := List.mem_map.mp h
  rw [show F.getType name = F.allDatatypes.find? (fun d' => d'.name == name) from rfl]
  intro hnone
  exact absurd (List.find?_eq_none.mp hnone d hd) (by simp [hdname])

/-- **`ContextOk` under an abstract-type add that also grows the pool.**
    The new name `nm` joins `baseTypes` (if `ar = 0`) or `tyCons` (otherwise), and
    `ContextOk` is re-established at that grown pool.

    `hnmR : nm ∈ R` keeps the reserved fields true; `hnm_ext` is the externality
    of the new entry (from the caller's `datatypesReserved` + freshness). Note
    `initialReserved` grows too (it mentions `baseTypes`/`tyCons`), so the old
    reserved facts are re-routed through the `baseTypes`/`tyCons` clauses of the
    *grown* `initialReserved` rather than transported verbatim. -/
theorem contextOk_addKnownType_grow {C C' : LContext CoreLParams} {nm : String} {ar : Nat}
    {bt : List String} {tc : List DatatypeGen.KnownTyCon} {R : List String}
    (hok : DatatypeGen.ContextOk C bt tc R) (hnmR : nm ∈ R)
    (hnm_ext : C.datatypes.getType nm = none)
    (h : C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    DatatypeGen.ContextOk C' (if ar = 0 then nm :: bt else bt)
      (if ar = 0 then tc else (nm, ar) :: tc) R := by
  obtain ⟨hkt, hdt⟩ := addKnownType_fields h
  have hkw : ∀ k, k ∈ C.knownTypes.keywords → k ∈ C'.knownTypes.keywords := by
    intro k hk; rw [hkt]; exact mem_keys_insertIfNew_of_mem hk
  have hnm_known : nm ∈ C'.knownTypes.keywords := by
    rw [hkt, KnownTypes.keywords, Std.HashMap.mem_keys]
    exact Std.HashMap.mem_insertIfNew.mpr (Or.inl (by simp))
  -- `nm ∈ R`, so `nm` is in the grown `initialReserved` via its `R` tail; and every
  -- member of the *old* `initialReserved` stays in the grown one (the
  -- `baseTypes`/`tyCons` clauses only gained an element).
  have hres_mono : ∀ x, x ∈ DatatypeGen.initialReserved bt tc R →
      x ∈ DatatypeGen.initialReserved (if ar = 0 then nm :: bt else bt)
        (if ar = 0 then tc else (nm, ar) :: tc) R := by
    intro x hx
    simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append] at hx ⊢
    by_cases har0 : ar = 0 <;> simp only [har0, if_pos, if_false] <;>
      rcases hx with h | ((h | h) | h) | h
    all_goals first
      | exact Or.inl h
      | exact Or.inr (Or.inl (Or.inl (Or.inl h)))
      | exact Or.inr (Or.inl (Or.inl (Or.inr (List.mem_cons_of_mem _ h))))
      | exact Or.inr (Or.inl (Or.inl (Or.inr h)))
      | exact Or.inr (Or.inl (Or.inr (by
          simp only [List.map_cons, List.mem_cons]; exact Or.inr h)))
      | exact Or.inr (Or.inl (Or.inr h))
      | exact Or.inr (Or.inr h)
  -- The new entry's arity: the gate errors when the name already exists, so `insertIfNew`
  -- really did insert and `nm` is registered at `ar`.
  have hnm_arity : C'.knownTypes[nm]? = some ar := by
    rw [hkt, Std.HashMap.getElem?_insertIfNew]
    have hnew : nm ∉ C.knownTypes := addKnownType_name_fresh h
    simp [hnew]
  refine
    { base_known := ?_, tyCon_known := ?_, arrow_known := ?_,
      base_arity := ?_, tyCon_arity := ?_, arrow_arity := ?_,
      knownTypes_reserved := ?_, datatypes_reserved := ?_,
      base_external := ?_, tyCon_external := ?_, arrow_external := ?_ }
  · -- base types: the new `nm` (if nullary) is known by `hnm_known`; old ones by monotonicity.
    intro b hb
    by_cases har0 : ar = 0
    · simp only [har0, if_pos] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl hnm_known
      · rcases hok.base_known b hb with hk | hd
        · exact Or.inl (hkw b hk)
        · exact Or.inr (by rw [hdt]; exact hd)
    · simp only [if_neg har0] at hb
      rcases hok.base_known b hb with hk | hd
      · exact Or.inl (hkw b hk)
      · exact Or.inr (by rw [hdt]; exact hd)
  · -- applied constructors: symmetric.
    intro kc hkc
    by_cases har0 : ar = 0
    · simp only [har0, if_pos] at hkc
      rcases hok.tyCon_known kc hkc with hk | hd
      · exact Or.inl (hkw kc.1 hk)
      · exact Or.inr (by rw [hdt]; exact hd)
    · simp only [if_neg har0] at hkc
      rcases List.mem_cons.mp hkc with rfl | hkc
      · exact Or.inl hnm_known
      · rcases hok.tyCon_known kc hkc with hk | hd
        · exact Or.inl (hkw kc.1 hk)
        · exact Or.inr (by rw [hdt]; exact hd)
  · exact hkw "arrow" hok.arrow_known
  -- Arities, in the same three shapes: the new entry at `ar`, old entries preserved by
  -- `insertIfNew`.
  · intro b hb
    by_cases har0 : ar = 0
    · simp only [har0, if_pos] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact har0 ▸ hnm_arity
      · rw [hkt]; exact getElem?_insertIfNew_of_getElem? (hok.base_arity b hb)
    · simp only [if_neg har0] at hb
      rw [hkt]; exact getElem?_insertIfNew_of_getElem? (hok.base_arity b hb)
  · intro kc hkc
    by_cases har0 : ar = 0
    · simp only [har0, if_pos] at hkc
      rw [hkt]; exact getElem?_insertIfNew_of_getElem? (hok.tyCon_arity kc hkc)
    · simp only [if_neg har0] at hkc
      rcases List.mem_cons.mp hkc with rfl | hkc
      · exact hnm_arity
      · rw [hkt]; exact getElem?_insertIfNew_of_getElem? (hok.tyCon_arity kc hkc)
  · rw [hkt]; exact getElem?_insertIfNew_of_getElem? hok.arrow_arity
  · intro k hk
    rw [hkt] at hk
    rcases mem_keys_insertIfNew_cases hk with rfl | hold
    · simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr hnmR)
    · exact hres_mono k (hok.knownTypes_reserved k hold)
  · rw [hdt]; intro n hn; exact hres_mono n (hok.datatypes_reserved n hn)
  · -- externality of base types: the new entry by `hnm_ext`, old ones unchanged.
    intro b hb
    rw [hdt]
    by_cases har0 : ar = 0
    · simp only [har0, if_pos] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hnm_ext
      · exact hok.base_external b hb
    · simp only [if_neg har0] at hb; exact hok.base_external b hb
  · intro kc hkc
    rw [hdt]
    by_cases har0 : ar = 0
    · simp only [har0, if_pos] at hkc; exact hok.tyCon_external kc hkc
    · simp only [if_neg har0] at hkc
      rcases List.mem_cons.mp hkc with rfl | hkc
      · exact hnm_ext
      · exact hok.tyCon_external kc hkc
  · rw [hdt]; exact hok.arrow_external

/-! ## Well-kinded operator types -/

/-- The curried function type built from well-kinded argument and result types is well kinded in a
    context that registers `arrow` at arity 2. -/
theorem wellKindedTy_mkArrow' {C : LContext CoreLParams} (harrow : C.knownTypes["arrow"]? = some 2)
    {out : LMonoTy} (hout : C.WellKindedTy out) :
    ∀ (ins : List LMonoTy), (∀ t ∈ ins, C.WellKindedTy t) →
      C.WellKindedTy (LMonoTy.mkArrow' out ins)
  | [], _ => by rw [LMonoTy.mkArrow'_nil]; exact hout
  | m :: ms, hins => by
    intro ref n hn
    simp only [LMonoTy.mkArrow', LMonoTy.arrow, getTypeConsArities, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, List.length_cons,
      List.length_nil, Prod.mk.injEq] at hn
    rcases hn with ⟨rfl, rfl⟩ | hm | hrest
    · exact harrow
    · exact hins m List.mem_cons_self ref n hm
    · exact wellKindedTy_mkArrow' harrow hout ms (fun t ht => hins t (List.mem_cons_of_mem _ ht))
        ref n hrest

/-- The operator entry of a declared monomorphic function has a well-kinded type when the function's
    signature types are well kinded and `arrow` is registered at arity 2. -/
theorem funcOpEntry_wellKinded {C : LContext CoreLParams} (harrow : C.knownTypes["arrow"]? = some 2)
    {f : Function} {entry : String × LMonoTy} (hentry : funcOpEntry f = some entry)
    (hsig : ∀ ty ∈ f.output :: f.inputs.values, C.WellKindedTy ty) : C.WellKindedTy entry.2 := by
  unfold funcOpEntry at hentry
  split at hentry
  · simp only [Option.some.injEq] at hentry
    subst hentry
    refine wellKindedTy_mkArrow' harrow (hsig _ List.mem_cons_self) _ ?_
    intro t ht
    refine hsig t (List.mem_cons_of_mem _ ?_)
    rw [ListMap.values_eq_map_snd]
    exact ht
  · exact absurd hentry (by simp)

/-! ## `ContextOk` monotonicity in the reserved set

`ContextOk` only *uses* the reserved set positively (`knownTypes_reserved` /
`datatypes_reserved` place names *into* it), so enlarging it preserves
`ContextOk`. -/

theorem contextOk_reserved_mono {C : LContext CoreLParams} {bt : List String}
    {tc : List DatatypeGen.KnownTyCon} {R R' : List String}
    (h : DatatypeGen.ContextOk C bt tc R) (hsub : R ⊆ R') :
    DatatypeGen.ContextOk C bt tc R' := by
  -- `initialReserved bt tc R ⊆ initialReserved bt tc R'` since it only appends `R`.
  have hinit : DatatypeGen.initialReserved bt tc R ⊆ DatatypeGen.initialReserved bt tc R' := by
    intro x hx
    simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append] at hx ⊢
    rcases hx with h | ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr (hsub h))
  exact
    { base_known := h.base_known
      tyCon_known := h.tyCon_known
      arrow_known := h.arrow_known
      base_arity := h.base_arity
      tyCon_arity := h.tyCon_arity
      arrow_arity := h.arrow_arity
      knownTypes_reserved := fun k hk => hinit (h.knownTypes_reserved k hk)
      datatypes_reserved := fun n hn => hinit (h.datatypes_reserved n hn)
      base_external := h.base_external
      tyCon_external := h.tyCon_external
      arrow_external := h.arrow_external }

/-! ## The fold invariant

Everything a per-step soundness proof needs about the incoming state, bundled.
Maintained from `initState` across every `genDecl*` step. -/

structure Inv (s : GenState) : Prop where
  /-- The context is `ContextOk` for the *threaded* pool of type constructors,
      reserved against the threaded `reserved` set (what the datatype generator
      needs).

      This field is stated at the pool `s.baseTypes` and `s.tyCons`, which a declaration of an abstract type
      grows, and not at the fixed default pool. That choice is what lets a
      datatype block reference a previously declared abstract type (interleaving
      direction (2)). The abstract-type
      step re-establishes it at the grown pool via
      `contextOk_addKnownType_grow`. -/
  ctxOk : DatatypeGen.ContextOk s.C s.baseTypes s.tyCons s.reserved
  /-- Every type name the context knows is reserved (needed for the alias/type-con
      name-clash guards). -/
  knownReserved : ∀ k ∈ s.C.knownTypes.keywords, k ∈ s.reserved
  /-- The referenceable base/applied pool is a superset of the default (the
      datatype generator uses the default pool; alias/distinct bodies use
      the growing one). Grown only by abstract types. -/
  baseSupset : DatatypeGen.defaultBaseTypes ⊆ s.baseTypes
  tyConsSupset : DatatypeGen.defaultTyCons ⊆ s.tyCons
  /-- Each name of the *current* pool is reserved. Therefore a fresh name,
      (∉ reserved) differs from every base type, applied constructor, and
      `"arrow"`. This is what a new alias/abstract-type name uses to stay
      disjoint from the pool. -/
  baseReserved : ∀ x ∈ s.baseTypes, x ∈ s.reserved
  tyConReserved : ∀ x ∈ s.tyCons.map (·.1), x ∈ s.reserved
  arrowReserved : "arrow" ∈ s.reserved
  /-- The type scope binds no variable: top-level declarations never bind expression variables,
      so `Γ.types` stays empty throughout the fold, matching the empty variable scopes the program
      is typed in. -/
  typesNil : s.Γ.types = []
  /-- The context declares no rigid type variables: top-level declarations never
      introduce any, and only a procedure body checks under rigid type variables. -/
  rigidNil : s.C.rigidTypeVars = []
  /-- No applied constructor in the threaded pool is named `"arrow"`. At the
      default pool this was the `decide`-able `defaultTyCons_ne_arrow`; with
      a growing pool it must be carried, since
      `genMutuallyRecursiveDatatypes_MutualADTWF` needs it. Re-established at each
      abstract step from `arrowReserved` plus the drawn name's freshness. -/
  tyConsNeArrow : ∀ kc ∈ s.tyCons, kc.1 ≠ "arrow"
  /-- Every datatype name the context knows is reserved. Needed by the
      abstract-type step: a freshly drawn name is then absent from
      `C.datatypes`, which is exactly the `getType … = none` that `ContextOk`'s
      externality fields demand of the new pool entry. -/
  datatypesReserved : ∀ n ∈ s.C.datatypes.allTypeNames, n ∈ s.reserved
  /-- Each datatype of the earlier pool resolves in `C` and is inhabited there. That is the hypothesis
      that lets a new block reference a *previously declared* datatype
      (interleaving direction (4)). Re-established at each datatype step from the
      `MutualADTWF.inhabited` field of the block just added. -/
  dtPoolOk : DatatypeGen.DatatypePoolOk s.C s.dtCons
  /-- Every pool name is reserved. Combined with a freshly drawn block name being
      unreserved, this gives "no pool name is a block name", which
      `datatypePool_inhab_push` needs. -/
  dtConsReserved : ∀ x ∈ s.dtCons.map (·.1), x ∈ s.reserved
  /-- Every type name referenced in a constructor argument of a datatype *stored*
      in `C` is reserved. Freshly drawn block names therefore occur nowhere in the
      stored datatypes, which is the `StoredRefsAbsent` side condition of
      `tySymInhab_push` (see `storedRefsAbsent_of_inv`). -/
  storedRefsReserved : ∀ d ∈ s.C.datatypes.allDatatypes, ∀ c ∈ d.constrs,
    ∀ arg ∈ c.args, ∀ r ∈ getTypeRefs arg.2, r ∈ s.reserved
  /-- Every datatype of `C` is registered in its known types at its number of type parameters.
      A constructor argument of a new block may name an earlier datatype, at that arity. -/
  datatypesKnown : s.C.DatatypesKnown
  /-- Every operator type a generated expression can use is well kinded in `C`. -/
  octxWK : ∀ p ∈ s.octx.ops, s.C.WellKindedTy p.2
  /-- The in-out and out-only types of every callable procedure are well kinded in `C`; a call
      declares and writes variables at instances of them. -/
  sigsWK : ∀ sig ∈ s.procs, ∀ ty ∈ (sig.M ++ sig.O).values, s.C.WellKindedTy ty
  /-- The operators and polymorphic schemes generated expressions draw on agree with the functions
      of `C`, and `C` gives every function the type scheme of its signature. -/
  exprCtx : ExprCtxOk s.C [] [] s.octx (s.pctx ++ s.derivedPctx)
  /-- Every polymorphic scheme generated expressions draw on is closed. -/
  polysClosed : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ s.pctx ++ s.derivedPctx →
    ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs

/-- Core's registered types record, for each name of the list they are built from, the arity that
    list gives it. -/
theorem coreKnownTypes_getElem? (k : String) (v : Nat)
    (hmem : (k, v) ∈ (Core.KnownLTys.map (fun ty => ty.toKnownType!)).map
      (fun x => (x.name, x.arity))) :
    Core.KnownTypes[k]? = some v := by
  have hdistinct : ((Core.KnownLTys.map (fun ty => ty.toKnownType!)).map
      (fun x => (x.name, x.arity))).Pairwise (fun a b => (a.1 == b.1) = false) := by decide
  exact Std.HashMap.getElem?_ofList_of_mem BEq.rfl hdistinct hmem

/-- **The fold's invariant already pins the `SimpleTyArities` arities.** The threaded pool
    holds the default pool (`baseSupset` and `tyConsSupset`), and the arity fields of
    `ContextOk` register each of its members at its own arity. This is exactly
    `SimpleTyArities`, the premise that the `init` and `signatureWellKinded` rules need. -/
theorem simpleTyArities_of_inv {s : GenState} (hinv : Inv s) : SimpleTyArities s.C := by
  have hb : ∀ b ∈ DatatypeGen.defaultBaseTypes, s.C.knownTypes[b]? = some 0 :=
    fun b hb => hinv.ctxOk.base_arity b (hinv.baseSupset hb)
  have htc : ∀ kc ∈ DatatypeGen.defaultTyCons, s.C.knownTypes[kc.1]? = some kc.2 :=
    fun kc hkc => hinv.ctxOk.tyCon_arity kc (hinv.tyConsSupset hkc)
  -- Membership in the *derived* pool is a lookup of an arity in `Core.KnownTypes`, which
  -- `mem_defaultBaseTypes_iff` and `mem_defaultTyCons_iff` give.
  have hbase : ∀ b, Core.KnownTypes[b]? = some 0 → s.C.knownTypes[b]? = some 0 :=
    fun b hcore => hb b (DatatypeGen.mem_defaultBaseTypes_iff.mpr hcore)
  refine ⟨?_, ?_, ?_, ?_, ?_, hinv.ctxOk.arrow_arity, ?_, ?_⟩
  · exact hbase "bool" (coreKnownTypes_getElem? _ _ (by decide))
  · exact hbase "int" (coreKnownTypes_getElem? _ _ (by decide))
  · exact hbase "string" (coreKnownTypes_getElem? _ _ (by decide))
  · exact hbase "real" (coreKnownTypes_getElem? _ _ (by decide))
  · exact hbase "regex" (coreKnownTypes_getElem? _ _ (by decide))
  · exact htc ("Map", 2) (DatatypeGen.mem_defaultTyCons_iff.mpr
      ⟨DatatypeGen.mem_coreAppliedTyCons_iff.mpr
        ⟨coreKnownTypes_getElem? _ _ (by decide), by simp, by simp⟩, by simp⟩)
  · exact htc ("Sequence", 1) (DatatypeGen.mem_defaultTyCons_iff.mpr
      ⟨DatatypeGen.mem_coreAppliedTyCons_iff.mpr
        ⟨coreKnownTypes_getElem? _ _ (by decide), by simp, by simp⟩, by simp⟩)

/-! ## Reference confinement for `genNonRecursiveArgTy` -/

/-- `BlockRefsWF [] tyParams []` holds vacuously. -/
theorem blockRefsWF_empty (tyParams : List TyIdentifier) :
    DatatypeGen.BlockRefsWF [] tyParams [] :=
  { mem := by simp, uniform := by simp, ftvarArgs := by simp, argsScoped := by simp }

/-- Every type-constructor name referenced in a type from `genNonRecursiveArgTy`'s support
    is a base type, a `tyCons` name, or `"arrow"`. Specialization of
    `genArgTy_refs` at `block := []`, `blockRefs := []`. -/
theorem genNonRecursiveArgTy_refs {baseTypes : BaseTys} {tyCons : TyCons}
    {tyParams : List TyIdentifier} {size : Nat} {ty : LMonoTy}
    (h : ty ∈ SetGen.support (genNonRecursiveArgTy (G := SetGen.Set) baseTypes tyCons tyParams size)) :
    ∀ r ∈ getTypeRefs ty,
      r ∈ baseTypes ∨ r ∈ tyCons.map (·.1) ∨ r = "arrow" := by
  intro r hr
  have := DatatypeGen.genArgTy_refs (block := []) (blockRefsWF_empty tyParams) size h r hr
  simpa using this

/-- A type drawn over *no* type parameters is ground. Specialization of
    `genArgTy_freeVars` at `blockRefs := []`, `tyParams := []`. -/
theorem genNonRecursiveArgTy_ground {baseTypes : BaseTys} {tyCons : TyCons}
    {size : Nat} {ty : LMonoTy}
    (h : ty ∈ SetGen.support (genNonRecursiveArgTy (G := SetGen.Set) baseTypes tyCons [] size)) :
    LMonoTy.freeVars ty = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr (fun v hv => ?_)
  have := DatatypeGen.genArgTy_freeVars (block := []) (blockRefsWF_empty []) size h v hv
  simp at this

/-- Every type-constructor occurrence in a `genNonRecursiveArgTy`-reachable type is applied at its own
    arity: a `baseTypes` name at 0, a `tyCons` entry at its recorded arity, or `"arrow"` at 2.
    Specialization of `genArgTy_arities` at `blockRefs := []` (so the block disjunct is
    unreachable). -/
theorem genNonRecursiveArgTy_arities {baseTypes : BaseTys} {tyCons : TyCons}
    {tyParams : List TyIdentifier} {size : Nat} {ty : LMonoTy}
    (h : ty ∈ SetGen.support (genNonRecursiveArgTy (G := SetGen.Set) baseTypes tyCons tyParams size)) :
    ∀ ref n, (ref, n) ∈ getTypeConsArities ty →
      (ref ∈ baseTypes ∧ n = 0) ∨ (ref, n) ∈ tyCons ∨ (ref = "arrow" ∧ n = 2) := by
  intro ref n hn
  rcases DatatypeGen.genArgTy_arities (block := []) (blockRefsWF_empty tyParams) size h ref n hn
    with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨d, hd, _⟩ := h3; simp at hd
  · exact Or.inr (Or.inr h4)

/-- **A `genNonRecursiveArgTy`-reachable type is well-kinded in any `ContextOk` context.** The
    pool's arities are exactly what `ContextOk`'s three arity fields record, and
    `LContext.WellKindedTy` asks for nothing else. This is what discharges upstream's
    `WellKindedTy`/`signatureWellKinded` obligations for the declarations typed over the
    pool (constants of a `distinct` group, alias bodies). -/
theorem wellKindedTy_of_genNonRecursiveArgTy {C : LContext CoreLParams}
    {bt : BaseTys} {tc : TyCons} {R : List String}
    (hok : DatatypeGen.ContextOk C bt tc R)
    {tyParams : List TyIdentifier} {size : Nat} {ty : LMonoTy}
    (h : ty ∈ SetGen.support (genNonRecursiveArgTy (G := SetGen.Set) bt tc tyParams size)) :
    C.WellKindedTy ty := by
  intro ref n hn
  rcases genNonRecursiveArgTy_arities h ref n hn with ⟨hb, rfl⟩ | htc | ⟨rfl, rfl⟩
  · exact hok.base_arity ref hb
  · exact hok.tyCon_arity (ref, n) htc
  · exact hok.arrow_arity

/-! ## Synonym bodies -/

/-- A type whose constructors are registered at their arities and whose type variables are all
    admissible passes the resolved checker under that admissibility. -/
theorem typeCheckCore_of_knownInstance {ks : KnownTypes} {adm : TyVarAdmissibility} :
    ∀ (ty : LMonoTy), LMonoTy.knownInstance ty ks = true →
      (∀ v ∈ LMonoTy.freeVars ty, adm v = true) → LMonoTy.typeCheckCore ty ks adm = true := by
  intro ty
  induction ty with
  | ftvar v =>
    intro _ hv
    simpa [LMonoTy.typeCheckCore] using hv v (by simp [LMonoTy.freeVars])
  | bitvec _ => intro _ _; simp [LMonoTy.typeCheckCore]
  | tcons name args ih =>
    intro hk hv
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at hk
    simp only [LMonoTy.typeCheckCore, Bool.and_eq_true]
    refine ⟨hk.1, ?_⟩
    have hkargs := hk.2
    have hvs : ∀ v ∈ LMonoTys.freeVars args, adm v = true := by
      intro v hva; exact hv v (by simpa only [LMonoTy.freeVars] using hva)
    clear hv hk
    induction args with
    | nil => simp [LMonoTys.typeCheckCore]
    | cons hd tl ihl =>
      simp only [LMonoTys.knownInstances] at hkargs
      split at hkargs
      case isFalse => exact absurd hkargs (by simp)
      rename_i hhd
      rw [LMonoTys.freeVars_of_cons] at hvs
      simp only [LMonoTys.typeCheckCore, Bool.and_eq_true]
      exact ⟨ih hd (by simp) hhd (fun v hv => hvs v (List.mem_append_left _ hv)),
        ihl (fun a ha => ih a (by simp [ha])) hkargs
          (fun v hv => hvs v (List.mem_append_right _ hv))⟩

/-- Each element of a generated `distinct` is an operator annotated at `τ`. In a context where each
    of the named constants is declared at `τ`, the element is weakly typed at `τ` with no variable
    in scope. -/
theorem distinctElems_typed {τ : LMonoTy} {names : List String} {C : LContext CoreLParams}
    (hlook : ∀ c ∈ names, C.functions[c]? = some (constantFunc c τ).toLFunc) :
    ∀ e ∈ distinctElems τ names, ExprHasTypeW C [] e τ := by
  intro e he
  simp only [distinctElems, List.mem_map] at he
  obtain ⟨c, hc, rfl⟩ := he
  have hfind := hlook c hc
  refine ⟨LExpr.HasTypeA.op, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [LExpr.binderAnnotations] at ht
  · intro x ann hx
    simp [LExpr.freeVars] at hx
  · intro o ty ho
    simp only [LExpr.opAnnots, Option.toList_some, List.map_cons, List.map_nil,
      List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, hty⟩ := ho
    exact ⟨_, [], τ, hfind, rfl, [], hty.trans (LMonoTy.subst_nil τ).symm⟩
  · intro o ho
    simp only [LExpr.getOps, List.mem_singleton] at ho
    subst ho
    rw [hfind]
    rfl

/-- A ground element type leaves no type variable in the annotations of a `distinct`'s elements. -/
theorem distinctElems_annots {τ : LMonoTy} {names : List String} (hτ : LMonoTy.freeVars τ = []) :
    ∀ e ∈ distinctElems τ names, ∀ v ∈ annotTyVars e, v ∈ ([] : List TyIdentifier) := by
  intro e he v hv
  simp only [distinctElems, List.mem_map] at he
  obtain ⟨c, _, rfl⟩ := he
  simp [annotTyVars, exprAnnotTys, hτ] at hv

/-- The element type a `genDistinctAssertion` draw produces is **ground**: it is drawn
    over `tyParams := []`, so `genArgTy_freeVars` (at the vacuous
    `BlockRefsWF [] [] []`) leaves it no free type variables.

    This is what the field `FuncHasType'.noUndeclaredVars` of each emitted constant needs. A constant declares
    no type argument, so its signature must be closed. -/
theorem genDistinctAssertion_ground {bt : BaseTys} {tc : TyCons}
    {reserved : List String} {maxVars size : Nat}
    {name : String} {τ : LMonoTy} {constNames : List String}
    (h : (name, τ, constNames) ∈ SetGen.support
      (genDistinctAssertion (G := SetGen.Set) bt tc reserved maxVars size)) :
    LMonoTy.freeVars τ = [] := by
  simp only [genDistinctAssertion, mem_support_bind_iff, mem_support_pure_iff,
    Prod.mk.injEq] at h
  obtain ⟨_nm, _hnm, τ', hτ', _k, _hk, _cs, _hcs, _, hτ_eq, _⟩ := h
  subst hτ_eq
  exact genNonRecursiveArgTy_ground hτ'

/-- The names a `genDistinctAssertion` draw produces are all fresh and pairwise
    distinct: the declaration name avoids `reserved`, and each constant name avoids
    `name :: reserved` (so it is fresh *and* differs from the declaration's own
    name). All `numVars + 1` become program-level declaration names, so this is what
    `getNames.Nodup` rests on. -/
theorem genDistinctAssertion_names {bt : BaseTys} {tc : TyCons}
    {reserved : List String} {maxVars size : Nat}
    {name : String} {τ : LMonoTy} {constNames : List String}
    (h : (name, τ, constNames) ∈ SetGen.support
      (genDistinctAssertion (G := SetGen.Set) bt tc reserved maxVars size)) :
    name ∉ reserved ∧ (∀ x ∈ constNames, x ∉ name :: reserved) ∧ constNames.Nodup := by
  simp only [genDistinctAssertion, mem_support_bind_iff, mem_support_pure_iff,
    Prod.mk.injEq] at h
  obtain ⟨nm, hnm, _τ', _hτ', k, _hk, cs, hcs, hnm_eq, _hτ_eq, hcs_eq⟩ := h
  subst hnm_eq
  subst hcs_eq
  exact ⟨(genDeclName_fresh hnm).1,
         fun x hx => DatatypeGen.genFreshNames_fresh _ _ _ hcs x (List.mem_filter.mp hx).1,
         (DatatypeGen.genFreshNames_nodup _ _ _ hcs).filter _⟩

/-! ## Per-declaration soundness: aliases, axioms and distinct

These steps leave the known types and the type-constructor pool unchanged, so `Inv` preservation
is `contextOk_reserved_mono` plus monotonicity of the reserved facts. -/

/-- A state whose only change from `s` is prepending `name` to `reserved`
    preserves `Inv`. -/
theorem inv_cons_reserved {s : GenState} (hinv : Inv s) (name : String) :
    Inv { s with reserved := name :: s.reserved } := by
  refine
    { ctxOk := contextOk_reserved_mono hinv.ctxOk (fun x hx => List.mem_cons_of_mem _ hx)
      knownReserved := fun k hk => List.mem_cons_of_mem _ (hinv.knownReserved k hk)
      tyConsNeArrow := hinv.tyConsNeArrow
      datatypesReserved := fun n hn => List.mem_cons_of_mem _ (hinv.datatypesReserved n hn)
      dtPoolOk := hinv.dtPoolOk
      dtConsReserved := fun x hx => List.mem_cons_of_mem _ (hinv.dtConsReserved x hx)
      storedRefsReserved := fun d hd c hc arg harg r hr =>
        List.mem_cons_of_mem _ (hinv.storedRefsReserved d hd c hc arg harg r hr)
      datatypesKnown := hinv.datatypesKnown
      baseSupset := hinv.baseSupset
      tyConsSupset := hinv.tyConsSupset
      baseReserved := fun x hx => List.mem_cons_of_mem _ (hinv.baseReserved x hx)
      tyConReserved := fun x hx => List.mem_cons_of_mem _ (hinv.tyConReserved x hx)
      arrowReserved := List.mem_cons_of_mem _ hinv.arrowReserved
      typesNil := hinv.typesNil
      rigidNil := hinv.rigidNil
      octxWK := hinv.octxWK
      sigsWK := hinv.sigsWK
      exprCtx := hinv.exprCtx
      polysClosed := hinv.polysClosed }

/-- A state whose only changes from `s` are prepending `name` to `reserved` and `sig` to `procs`
    keeps `Inv`, provided the in-out and out-only types of `sig` are well kinded in `C`. The
    agreement of the callable signatures with the finished program is not part of `Inv`. -/
theorem inv_cons_reserved_procs {s : GenState} (hinv : Inv s) (name : String)
    (sig : StrataGenerators.Stmt.ProcSig)
    (hsigWK : ∀ ty ∈ (sig.M ++ sig.O).values, s.C.WellKindedTy ty) :
    Inv { s with reserved := name :: s.reserved, procs := sig :: s.procs } := by
  -- Every `Inv` field reads only `C`/`Γ`/`baseTypes`/`tyCons`/`dtCons`/`reserved`,
  -- all of which agree with `{ s with reserved := name :: s.reserved }`.
  have h := inv_cons_reserved (s := s) hinv name
  exact
    { ctxOk := h.ctxOk
      knownReserved := h.knownReserved
      baseSupset := h.baseSupset
      tyConsSupset := h.tyConsSupset
      baseReserved := h.baseReserved
      tyConReserved := h.tyConReserved
      arrowReserved := h.arrowReserved
      typesNil := h.typesNil
      rigidNil := h.rigidNil
      tyConsNeArrow := h.tyConsNeArrow
      datatypesReserved := h.datatypesReserved
      dtPoolOk := h.dtPoolOk
      dtConsReserved := h.dtConsReserved
      storedRefsReserved := h.storedRefsReserved
      datatypesKnown := h.datatypesKnown
      octxWK := h.octxWK
      sigsWK := fun g hg => by
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hsigWK
        · exact hinv.sigsWK g hg
      exprCtx := h.exprCtx
      polysClosed := h.polysClosed }

/-- A state whose only change from `s` is prepending a *list* of names to
    `reserved` preserves `Inv`. The list version of `inv_cons_reserved`, needed by
    the `distinct` step (which reserves one name per constant plus the declaration's
    own). Every reserved-mentioning field is monotone in `reserved`. -/
theorem inv_grow_reserved {s : GenState} (hinv : Inv s) (extra : List String) :
    Inv { s with reserved := extra ++ s.reserved } := by
  have mono : ∀ x ∈ s.reserved, x ∈ extra ++ s.reserved :=
    fun x hx => List.mem_append_right _ hx
  refine
    { ctxOk := contextOk_reserved_mono hinv.ctxOk mono
      knownReserved := fun k hk => mono _ (hinv.knownReserved k hk)
      tyConsNeArrow := hinv.tyConsNeArrow
      datatypesReserved := fun n hn => mono _ (hinv.datatypesReserved n hn)
      dtPoolOk := hinv.dtPoolOk
      dtConsReserved := fun x hx => mono _ (hinv.dtConsReserved x hx)
      storedRefsReserved := fun d hd c hc arg harg r hr =>
        mono _ (hinv.storedRefsReserved d hd c hc arg harg r hr)
      datatypesKnown := hinv.datatypesKnown
      baseSupset := hinv.baseSupset
      tyConsSupset := hinv.tyConsSupset
      baseReserved := fun x hx => mono _ (hinv.baseReserved x hx)
      tyConReserved := fun x hx => mono _ (hinv.tyConReserved x hx)
      arrowReserved := mono _ hinv.arrowReserved
      typesNil := hinv.typesNil
      rigidNil := hinv.rigidNil
      octxWK := hinv.octxWK
      sigsWK := hinv.sigsWK
      exprCtx := hinv.exprCtx
      polysClosed := hinv.polysClosed }

/-- Soundness of the alias step: under any program `P`, the emitted declarations are weakly typed
    from the context of `s` to that of `s'`, and `Inv` is preserved. A synonym's parameters are the
    distinct free variables of its body, and the body is drawn over registered constructors. -/
theorem genDeclAlias_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAlias (G := SetGen.Set) s b)) :
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclAlias, genAlias, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨pr, ⟨nm, hnm, ntp, _, tyParams, _, body, hbody, hpr⟩, hmatch⟩ := h
  subst hpr
  simp only [mkAliasDecl] at hmatch
  split at hmatch
  case isFalse =>
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsHasTypeW.nil _ _, hinv⟩
  simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
  obtain ⟨hds, hs'⟩ := hmatch
  have hnm_fresh : nm ∉ s.reserved := (genDeclTypeName_fresh hnm).1
  let syn : TypeSynonym :=
    { name := nm, typeArgs := (LMonoTy.freeVars body).uniq, type := body }
  have hmk : mkAliasDecl nm body = .type (.syn syn) .empty := rfl
  have hNodup : syn.typeArgs.Nodup := (LMonoTy.freeVars body).nodup_uniq
  have hclosed : ∀ v, v ∈ LMonoTy.freeVars syn.type → v ∈ syn.typeArgs := by
    intro v hv; exact (List.mem_of_dedup _ _).mp hv
  have hknown : LMonoTy.knownInstance body s.C.knownTypes = true :=
    Lambda.knownInstance_of_wellKinded body _
      (wellKindedTy_of_genNonRecursiveArgTy hinv.ctxOk hbody)
  have hres : ResolvedTyHasType s.C (fun v => decide (v ∈ syn.typeArgs)) syn.type :=
    LMonoTy.typeCheckCore_sound _ s.C _
      (typeCheckCore_of_knownInstance _ hknown (fun v hv => decide_eq_true (hclosed v hv)))
  have hoccurs : ∀ v ∈ syn.typeArgs, v ∈ LMonoTy.freeVars syn.type :=
    fun v hv => (List.mem_of_dedup _ _).mpr hv
  -- Every known type name is reserved and `nm` is not, so `nm` is not a known type.
  have hnotKnown : ¬ s.C.knownTypes.containsName syn.name := by
    intro hc
    have hmem : nm ∈ s.C.knownTypes :=
      (KnownTypes.containsName_eq_true_iff_mem _ _).mp hc
    exact hnm_fresh (hinv.knownReserved nm (Std.HashMap.mem_keys.mpr hmem))
  have hdecl : DeclHasTypeW P s.C [] (mkAliasDecl nm body) s.C := by
    rw [hmk]
    exact DeclHasTypeW.type_syn s.C [] syn .empty hNodup hnotKnown hoccurs hres
  subst hds hs'
  refine ⟨DeclsHasTypeW.cons _ _ _ _ _ _ hdecl (DeclsHasTypeW.nil _ _), ?_⟩
  -- Only `reserved` (by `nm`) and the alias list change, and no `Inv` field reads the aliases.
  have hgrow := inv_cons_reserved hinv nm
  exact { hgrow with typesNil := hinv.typesNil }

/-- `Inv` survives replacing the operator contexts by ones whose monomorphic operators have
    well-kinded types, that agree with the functions of `C`, and whose schemes are closed. -/
theorem inv_setOpCtxs {s : GenState} (hinv : Inv s)
    (octx : OpCtx) (pctx derivedPctx : PolyOpCtx) (hwk : ∀ p ∈ octx.ops, s.C.WellKindedTy p.2)
    (hctx : ExprCtxOk s.C [] [] octx (pctx ++ derivedPctx))
    (hclosed : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx ++ derivedPctx →
      ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs) :
    Inv { s with octx := octx, pctx := pctx, derivedPctx := derivedPctx } :=
  { hinv with octxWK := hwk, exprCtx := hctx, polysClosed := hclosed }

/-- **`Inv` is preserved by a factory add alone**, with `reserved` unchanged, when the operators
    and schemes of `s` agree with the grown function table. A successful
    `addFactoryFunctionWithError` touches only `C.functions`, so the known types, the datatypes
    and the rigid type variables stay the same. -/
theorem inv_addFactory {s : GenState} (hinv : Inv s) {fn : LFunc CoreLParams}
    {C' : LContext CoreLParams}
    (hadd : s.C.addFactoryFunctionWithError fn = .ok C')
    (hctx : ExprCtxOk C' [] [] s.octx (s.pctx ++ s.derivedPctx)) :
    Inv { s with C := C' } := by
  obtain ⟨hkt, hdt⟩ := addFactory_fields hadd
  refine
    { ctxOk := contextOk_addFactory hinv.ctxOk hadd
      knownReserved := fun k hk => hinv.knownReserved k (by rw [hkt] at hk; exact hk)
      baseSupset := hinv.baseSupset
      tyConsSupset := hinv.tyConsSupset
      baseReserved := hinv.baseReserved
      tyConReserved := hinv.tyConReserved
      arrowReserved := hinv.arrowReserved
      typesNil := hinv.typesNil
      rigidNil := (addFactory_rigid hadd).trans hinv.rigidNil
      tyConsNeArrow := hinv.tyConsNeArrow
      datatypesReserved := fun n hn => hinv.datatypesReserved n (by rw [hdt] at hn; exact hn)
      dtPoolOk := { known := by rw [hdt]; exact hinv.dtPoolOk.known
                    arity := by rw [hdt]; exact hinv.dtPoolOk.arity
                    inhab := by rw [hdt]; exact hinv.dtPoolOk.inhab }
      dtConsReserved := hinv.dtConsReserved
      storedRefsReserved := fun d hd c hc arg harg r hr =>
        hinv.storedRefsReserved d (by rw [hdt] at hd; exact hd) c hc arg harg r hr
      datatypesKnown := fun d hd => by
        rw [hkt]
        exact hinv.datatypesKnown d (by rw [hdt] at hd; exact hd)
      octxWK := fun p hp => by
        unfold LContext.WellKindedTy; rw [hkt]; exact hinv.octxWK p hp
      sigsWK := fun sig hsig ty hty => by
        unfold LContext.WellKindedTy; rw [hkt]; exact hinv.sigsWK sig hsig ty hty
      exprCtx := hctx
      polysClosed := hinv.polysClosed }

/-! ## The axiom expression -/

/-- An axiom drawn at a state of the fold is a boolean that is weakly typed in the context of that
    state with no variable in scope, and its annotations mention no type variable. -/
theorem genAxiom_exprTyped {s : GenState} (hinv : Inv s) {depth : Nat}
    {decl : Decl} {name : String}
    (h : (decl, name) ∈ SetGen.support
      (genAxiom (G := SetGen.Set) s.octx s.pctx s.reserved depth)) :
    ∃ a, decl = .ax a .empty ∧ ExprHasTypeW s.C [] a.e .bool ∧
      ∀ v ∈ annotTyVars a.e, v ∈ ([] : List TyIdentifier) := by
  simp only [genAxiom, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨nm, _, e, he, hdecl, _⟩ := h
  have hops : ∀ p ∈ (opsOver [] s.octx).ops, p ∈ s.octx.ops ∧
      ∀ v ∈ LMonoTy.freeVars p.2, v ∈ ([] : List TyIdentifier) :=
    fun _ hp => mem_opsOver_iff.mp hp
  have hctx : ExprCtxOk s.C [] [] (opsOver [] s.octx) s.pctx :=
    hinv.exprCtx.restrict (fun _ hp => absurd hp List.not_mem_nil) (fun p hp => (hops p hp).1)
      (fun _ hp => List.mem_append_left _ hp)
  have hsc : ExprScopedCtx [] [] (opsOver [] s.octx) s.pctx :=
    ⟨fun _ hp => absurd hp List.not_mem_nil, fun p hp => (hops p hp).2,
      fun nm bvs body hmem => hinv.polysClosed nm bvs body (List.mem_append_left _ hmem)⟩
  have hbool := (closureHyps_annotsOk [] hctx).bool
  have hboolV := (closureHyps_annotTyVars hsc).bool
  exact ⟨{ name := nm, e := e }, hdecl, genLExpr_exprHasTypeW hctx hbool he,
    genLExpr_annotTyVars hsc hboolV he⟩

/-- Soundness of the axiom step: the emitted axiom is weakly typed in the context of `s`, and only
    `reserved` changes. -/
theorem genDeclAxiom_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAxiom (G := SetGen.Set) s b)) :
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclAxiom, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨pr, hpr, hds, hs'⟩ := h
  obtain ⟨a, hdecl_eq, htyped, hscoped⟩ := genAxiom_exprTyped hinv hpr
  subst hds hs'
  refine ⟨?_, inv_cons_reserved hinv _⟩
  rw [hdecl_eq]
  exact DeclsHasTypeW.cons _ _ _ _ _ _
    (DeclHasTypeW.ax s.C [] a .empty htyped hscoped) (DeclsHasTypeW.nil _ _)

/-! ### The constants a `distinct` ranges over

The `distinct` step emits one 0-ary constant per element before the `distinct`
itself. Each constant is an ordinary `.func` declaration, so its proof discharges each
`DeclHasTypeW.func` premise as the step for a function does, and each step is much cheaper, because
a constant has no body, no measure and no type argument. -/

/-- A generated constant is non-recursive: `constantFunc` leaves `isRecursive` at
    its `false` default. -/
theorem constantFunc_nonrec (c : String) (τ : LMonoTy) :
    ¬ (constantFunc c τ).isRecursive := by
  simp [constantFunc]

/-- A constant of a ground, well-kinded type `τ` is a weakly typed function in every context and
    in all variable scopes: it has no formal, type parameter, body, measure, precondition or
    axiom. -/
theorem constantFunc_hasTypeW {C : LContext CoreLParams} {ts : TypeScopes}
    {c : String} {τ : LMonoTy} (hτ : LMonoTy.freeVars τ = []) (hwk : C.WellKindedTy τ) :
    FuncHasTypeW C ts (constantFunc c τ) := by
  refine
    { inputsNodup := by simp [constantFunc, ListMap.keys]
      typeArgsNodup := by simp [constantFunc]
      noUndeclaredVars := ?_
      typeArgsInSignature := by intro ta hta; simp [constantFunc] at hta
      signatureWellKinded := ?_
      bodyTyped := by intro body hb; simp [constantFunc] at hb
      measureOnlyRecursive := fun _ => rfl
      measureTyped := by intro m hm; simp [constantFunc] at hm
      preconditionsTyped := by intro p hp; simp [constantFunc] at hp
      axiomsTyped := by intro ax hax; simp [constantFunc] at hax
      annotsScoped := by intro e he; simp [constantFunc, Strata.DL.Util.Func.exprs] at he
      constrNoBody := by intro h; simp [constantFunc] at h }
  · intro v hv
    simp only [constantFunc, ListMap.values, LMonoTy.mkArrow'_nil, hτ] at hv
    exact absurd hv (by simp)
  · intro ty hty
    simp only [constantFunc, ListMap.values, List.mem_cons, List.not_mem_nil, or_false] at hty
    rw [hty]; exact hwk

/-- A successful `addConstants` run on `c :: cs` adds the constant `c` and then runs on `cs`. -/
theorem addConstants_cons {τ : LMonoTy} {c : String} {cs : List String}
    {C C' : LContext CoreLParams} {ds : List Decl}
    (h : addConstants C τ (c :: cs) = some (C', ds)) :
    ∃ C₁ ds', C.addFactoryFunctionWithError (constantFunc c τ).toLFunc = .ok C₁ ∧
      addConstants C₁ τ cs = some (C', ds') ∧ ds = mkConstantDecl c τ :: ds' := by
  simp only [addConstants] at h
  cases hadd : C.addFactoryFunctionWithError (constantFunc c τ).toLFunc with
  | error e => simp [hadd] at h
  | ok C₁ =>
    simp only [hadd] at h
    cases hrest : addConstants C₁ τ cs with
    | none => simp [hrest] at h
    | some pr =>
      obtain ⟨C₂, ds'⟩ := pr
      simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨C₁, ds', rfl, hrest, rfl⟩

/-- A successful `addConstants` run keeps every function entry of the context it starts from. -/
theorem addConstants_preserves {τ : LMonoTy} :
    ∀ (names : List String) (C C' : LContext CoreLParams) (ds : List Decl),
      addConstants C τ names = some (C', ds) →
      ∀ (nm : String) (g : LFunc CoreLParams), C.functions[nm]? = some g →
        C'.functions[nm]? = some g := by
  intro names
  induction names with
  | nil =>
    intro C C' ds h nm g hg
    simp only [addConstants, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hg
  | cons c cs ih =>
    intro C C' ds h nm g hg
    obtain ⟨C₁, ds', hadd, hrest, rfl⟩ := addConstants_cons h
    exact ih C₁ C' ds' hrest nm g ((factoryExtendedBy_of_addFactory hadd).preserves_old nm g hg)

/-- After a successful `addConstants` run, each of its names holds the constant declared at `τ`. -/
theorem addConstants_lookup {τ : LMonoTy} :
    ∀ (names : List String) (C C' : LContext CoreLParams) (ds : List Decl),
      addConstants C τ names = some (C', ds) →
      ∀ c ∈ names, C'.functions[c]? = some (constantFunc c τ).toLFunc := by
  intro names
  induction names with
  | nil => intro C C' ds _ c hc; exact absurd hc List.not_mem_nil
  | cons d ds ih =>
    intro C C' es h c hc
    obtain ⟨C₁, es', hadd, hrest, rfl⟩ := addConstants_cons h
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨g, hg, rfl⟩ := (factoryExtendedBy_of_addFactory hadd).contains_new _
        List.mem_cons_self
      exact addConstants_preserves ds C₁ C' es' hrest _ _ hg
    · exact ih C₁ C' es' hrest c hc

/-- The constants are weakly typed and extend the context: a successful `addConstants` run is a
    declaration-list typing from `C` to the grown `C'`, one function declaration per constant. -/
theorem addConstants_sound (P : Program) {τ : LMonoTy} (hτ : LMonoTy.freeVars τ = []) :
    ∀ (names : List String) (C C' : LContext CoreLParams) (ds : List Decl),
      C.WellKindedTy τ →
      addConstants C τ names = some (C', ds) → DeclsHasTypeW P C [] ds C' := by
  intro names
  induction names with
  | nil =>
    intro C C' ds _ h
    simp only [addConstants, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact DeclsHasTypeW.nil _ _
  | cons c cs ih =>
    intro C C' ds hwk h
    obtain ⟨C₁, ds', hadd, hrest, rfl⟩ := addConstants_cons h
    -- Adding a factory function leaves `knownTypes` alone, so `WellKindedTy` survives.
    have hwk₁ : C₁.WellKindedTy τ := by
      unfold LContext.WellKindedTy at hwk ⊢
      rw [(addFactory_fields hadd).1]; exact hwk
    exact DeclsHasTypeW.cons _ _ _ _ _ _
      (DeclHasTypeW.func C C₁ [] (constantFunc c τ) .empty
        (constantFunc_nonrec c τ) (addFactory_name_fresh hadd) (constantFunc_hasTypeW hτ hwk)
        (factoryExtendedBy_of_addFactory hadd))
      (ih C₁ C' ds' hwk₁ hrest)

/-- **`Inv` survives the constant run.** Each add only grows the function factory
    (`inv_addFactory`), and `reserved` is untouched until the step's end. -/
theorem addConstants_inv {τ : LMonoTy} :
    ∀ (names : List String) {s : GenState} {C' : LContext CoreLParams} {ds : List Decl},
      Inv s → addConstants s.C τ names = some (C', ds) → Inv { s with C := C' } := by
  intro names
  induction names with
  | nil =>
    intro s C' ds hinv h
    simp only [addConstants, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact hinv
  | cons c cs ih =>
    intro s C' ds hinv h
    obtain ⟨C₁, ds', hadd, hrest, rfl⟩ := addConstants_cons h
    -- Add `c`, then recurse from the grown state (whose `.C` is `C₁`). A constant has the
    -- type scheme of its signature.
    have hty : ∀ f ∈ [(constantFunc c τ).toLFunc], f.type =
        .ok (.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))) := by
      intro f hf
      rw [List.mem_singleton.mp hf]
      rfl
    exact ih (s := { s with C := C₁ })
      (inv_addFactory hinv hadd (hinv.exprCtx.extend (factoryExtendedBy_of_addFactory hadd) hty))
      hrest

/-- The names a successful `addConstants` run declares are exactly its input
    names, in order. -/
theorem addConstants_declNames {τ : LMonoTy} :
    ∀ (names : List String) (C C' : LContext CoreLParams) (ds : List Decl),
      addConstants C τ names = some (C', ds) → declNames ds = names := by
  intro names
  induction names with
  | nil =>
    intro C C' ds h
    simp only [addConstants, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp [declNames]
  | cons c cs ih =>
    intro C C' ds h
    obtain ⟨C₁, ds', hadd, hrest, rfl⟩ := addConstants_cons h
    have hcons : declNames (mkConstantDecl c τ :: ds') = c :: declNames ds' := by
      simp [declNames, mkConstantDecl, constantFunc, Decl.names, Decl.name]
    rw [hcons, ih C₁ C' ds' hrest]

/-- Soundness of the distinct step: the emitted constants are weakly typed and extend `C`, and the
    `distinct` over them is weakly typed in the grown context. On a factory clash nothing is emitted
    and the state is unchanged. -/
theorem genDeclDistinct_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclDistinct (G := SetGen.Set) s b)) :
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclDistinct, mem_support_bind_iff] at h
  obtain ⟨⟨nm, τ, constNames⟩, hparts, hmatch⟩ := h
  have hτ : LMonoTy.freeVars τ = [] := genDistinctAssertion_ground hparts
  -- The group's type comes from `genNonRecursiveArgTy`, so it is well-kinded in `s.C` by `ctxOk`.
  have hτwk : s.C.WellKindedTy τ := by
    simp only [genDistinctAssertion, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hparts
    obtain ⟨_, _, τ', hτ', _, _, _, _, _, hτ_eq, _⟩ := hparts
    exact hτ_eq ▸ wellKindedTy_of_genNonRecursiveArgTy hinv.ctxOk hτ'
  split at hmatch
  case isFalse =>
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsHasTypeW.nil _ _, hinv⟩
  rename_i hgate
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgate
  obtain ⟨hlen, _⟩ := hgate
  cases hadd : addConstants s.C τ constNames with
  | none =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsHasTypeW.nil _ _, hinv⟩
  | some pr =>
    obtain ⟨C', constDecls⟩ := pr
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    refine ⟨?_, ?_⟩
    · -- The constants take `C` to `C'`, then the `distinct` leaves `C'` unchanged.
      refine declsHasTypeW_append
        (addConstants_sound P hτ constNames s.C C' constDecls hτwk hadd) ?_
      have hlen' : 2 ≤ (distinctElems τ constNames).length := by
        simpa [distinctElems] using hlen
      exact DeclsHasTypeW.cons _ _ _ _ _ _
        (DeclHasTypeW.distinct C' [] ⟨nm, ()⟩ (distinctElems τ constNames) .empty
          hlen' ⟨τ, distinctElems_typed (addConstants_lookup constNames s.C C' constDecls hadd)⟩
          (distinctElems_annots hτ))
        (DeclsHasTypeW.nil _ _)
    · -- `C` grew by the constants' factory entries; `reserved` by their names plus `nm`.
      have hgrown := inv_grow_reserved (s := { s with C := C' })
        (addConstants_inv constNames hinv hadd) (constNames ++ [nm])
      simpa using hgrown

/-! ## Per-declaration soundness: abstract types

The abstract-type step draws a fresh name, gates on `addKnownTypeWithError`, and
(on success) grows the context's known types and the referenceable pool. -/

/-- Soundness of the abstract-type step: on a successful add the emitted type constructor is a new
    known type of `C`, and `Inv` holds at the grown pool. -/
theorem genDeclAbstract_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAbstract (G := SetGen.Set) s b)) :
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclAbstract, genAbstractType, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨pr, ⟨nm, hnm, ar, _har, hpr⟩, hmatch⟩ := h
  subst hpr
  -- Freshness of the drawn name.
  have hnm_fresh : nm ∉ s.reserved := (genDeclTypeName_fresh hnm).1
  simp only at hmatch
  -- Case on the gate.
  cases hadd : s.C.addKnownTypeWithError { name := nm, metadata := ar } default with
  | error e =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsHasTypeW.nil _ _, hinv⟩
  | ok C' =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    refine ⟨?_, ?_⟩
    · -- `mkAbstractTypeDecl nm ar` declares `{ name := nm, params := replicate ar "_" }`, whose
      -- number of arguments is `ar`.
      refine DeclsHasTypeW.cons _ _ _ _ _ _ ?_ (DeclsHasTypeW.nil _ _)
      have harw : ({ name := nm, params := List.replicate ar "_" } : TypeConstructor).numargs = ar := by
        simp [TypeConstructor.numargs]
      have hcon := DeclHasTypeW.type_con (P := P) s.C C' []
        { name := nm, params := List.replicate ar "_" } .empty
      rw [harw] at hcon
      exact hcon hadd
    · -- `Inv` preserved via `contextOk_addKnownType`, growing the pool.
      obtain ⟨hkt, hdt⟩ := addKnownType_fields hadd
      have hmono : ∀ (n : String) (v : Nat), s.C.knownTypes[n]? = some v →
          C'.knownTypes[n]? = some v := fun n v hv => by
        rw [hkt]; exact getElem?_insertIfNew_of_getElem? hv
      -- `s' = s.addAbstract nm ar C'`.
      simp only [GenState.addAbstract]
      refine
        { ctxOk := ?_
          knownReserved := ?_
          baseSupset := ?_
          tyConsSupset := ?_
          baseReserved := ?_
          tyConReserved := ?_
          arrowReserved := ?_
          typesNil := hinv.typesNil
          rigidNil := (addKnownType_rigid hadd).trans hinv.rigidNil
          tyConsNeArrow := ?_
          datatypesReserved := ?_
          dtPoolOk := ?_
          dtConsReserved := fun x hx => List.mem_cons_of_mem _ (hinv.dtConsReserved x hx)
          storedRefsReserved := ?_
          datatypesKnown := fun d hd =>
            hmono _ _ (hinv.datatypesKnown d (by rw [hdt] at hd; exact hd))
          octxWK := fun p hp => wellKindedTy_mono hmono (hinv.octxWK p hp)
          sigsWK := fun sig hsig ty hty => wellKindedTy_mono hmono (hinv.sigsWK sig hsig ty hty)
          exprCtx := hinv.exprCtx.mono (addKnownTypeWithError_functions hadd) hmono
          polysClosed := hinv.polysClosed }
      · -- `ContextOk C'` at the *grown* pool (interleaving direction (2)).
        -- Externality of the new entry: `nm` is fresh, and every datatype name of
        -- `C` is reserved, so `nm` is not one of them.
        have hnmR : nm ∈ (nm :: s.reserved) := List.mem_cons_self
        have hnm_ext : s.C.datatypes.getType nm = none :=
          getType_eq_none_of_not_mem (fun hmem => hnm_fresh (hinv.datatypesReserved nm hmem))
        exact contextOk_addKnownType_grow
          (contextOk_reserved_mono hinv.ctxOk (fun x hx => List.mem_cons_of_mem _ hx))
          hnmR hnm_ext hadd
      · -- known types of `C'` reserved: keys are `nm` or old.
        intro k hk
        rw [hkt] at hk
        rcases mem_keys_insertIfNew_cases hk with rfl | hold
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hinv.knownReserved k hold)
      · -- baseSupset: default ⊆ (maybe nm ::) s.baseTypes.
        by_cases har0 : ar = 0
        · subst har0; simp only [if_pos]
          exact fun x hx => List.mem_cons_of_mem _ (hinv.baseSupset hx)
        · simp only [if_neg har0]; exact hinv.baseSupset
      · -- tyConsSupset.
        by_cases har0 : ar = 0
        · subst har0; simp only [if_pos]; exact hinv.tyConsSupset
        · simp only [if_neg har0]
          exact fun x hx => List.mem_cons_of_mem _ (hinv.tyConsSupset hx)
      · -- baseReserved: new base type is `nm ∈ nm :: reserved`; old ones reserved.
        by_cases har0 : ar = 0
        · subst har0; simp only [if_pos]
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hinv.baseReserved x hx)
        · simp only [if_neg har0]
          intro x hx; exact List.mem_cons_of_mem _ (hinv.baseReserved x hx)
      · -- tyConReserved.
        by_cases har0 : ar = 0
        · subst har0; simp only [if_pos]
          intro x hx; exact List.mem_cons_of_mem _ (hinv.tyConReserved x hx)
        · simp only [if_neg har0]
          intro x hx
          simp only [List.map_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hinv.tyConReserved x hx)
      · exact List.mem_cons_of_mem _ hinv.arrowReserved
      · -- tyConsNeArrow: the new applied constructor is `nm`, which is fresh, while
        -- `"arrow"` is reserved, so the new name differs from it.
        by_cases har0 : ar = 0
        · subst har0; simp only [if_pos]; exact hinv.tyConsNeArrow
        · simp only [if_neg har0]
          intro kc hkc
          rcases List.mem_cons.mp hkc with rfl | hkc
          · show nm ≠ "arrow"
            intro heq
            exact hnm_fresh (by rw [heq]; exact hinv.arrowReserved)
          · exact hinv.tyConsNeArrow kc hkc
      · -- datatypesReserved: `addKnownTypeWithError` leaves `datatypes` alone.
        intro n hn
        rw [hdt] at hn
        exact List.mem_cons_of_mem _ (hinv.datatypesReserved n hn)
      · -- dtPoolOk: `datatypes` unchanged.
        exact { known := by rw [hdt]; exact hinv.dtPoolOk.known
                arity := by rw [hdt]; exact hinv.dtPoolOk.arity
                inhab := by rw [hdt]; exact hinv.dtPoolOk.inhab }
      · -- storedRefsReserved: `datatypes` unchanged, reserved only grew.
        intro d hd c hc arg harg r hr
        rw [hdt] at hd
        exact List.mem_cons_of_mem _ (hinv.storedRefsReserved d hd c hc arg harg r hr)

/-! ## Datatype block: `MutualADTWF` from the invariant

Given `Inv s`, any block in the datatype generator's support (at the default
pool, reserved against `s.reserved`) is `MutualADTWF s.C`. This is the
`ContextOk`-consuming half; the checker-success half comes from gating. -/

/-! ## Datatype block: names are globally fresh

For `getNames.Nodup`, the block's datatype names must be pairwise distinct and
disjoint from every other declaration's name. Both read off
`genMutuallyRecursiveDatatypes_shape` directly: it pins the block's names to its
headers' names (`block.map name = headers.map name`), which are `Nodup` and fresh
against `initialReserved`. The proof needs no argument about a permutation, because the generator emits its
datatypes in the order of their ranks and it shuffles nothing. -/

theorem genDatatypeBlock_names {baseTypes : BaseTys} {tyCons : TyCons}
    {mExtra mTyP mBase mRec mArgs mSize : Nat} {extraReserved : List String}
    {block : MutualDatatype Unit}
    (hblock : block ∈ SetGen.support
      (genMutuallyRecursiveDatatypes (G := SetGen.Set) baseTypes tyCons
        mExtra mTyP mBase mRec mArgs mSize extraReserved)) :
    (block.map (·.name)).Nodup ∧
    (∀ d ∈ block, d.name ∉ DatatypeGen.initialReserved baseTypes tyCons extraReserved) := by
  obtain ⟨headers, _hne, hbnames, hnodup, hfresh, _hshape, _⟩ :=
    DatatypeGen.genMutuallyRecursiveDatatypes_shape hblock
  refine ⟨?_, ?_⟩
  · -- The block's names *are* the headers' names, which are `Nodup`.
    rw [hbnames]; exact hnodup
  · -- Freshness: `d.name ∈ block.map name = headers.map name`, and every header
    -- name avoids `initialReserved`.
    intro d hd
    have : d.name ∈ headers.map (·.name) := by
      rw [← hbnames]; exact List.mem_map.mpr ⟨d, hd, rfl⟩
    obtain ⟨hdr, hhdr, hname⟩ := List.mem_map.mp this
    rw [← hname]
    exact hfresh hdr hhdr

/-- **`StoredRefsAbsent` from the invariant.** Every reference in a stored
    datatype's constructor arguments is reserved (`Inv.storedRefsReserved`), while
    the block's names are freshly drawn and hence unreserved. So no block name can
    occur in a stored datatype. That fact is the side condition that
    `tySymInhab_push` needs to transport a prior datatype's inhabitance across the
    push. -/
theorem storedRefsAbsent_of_inv {s : GenState} {block : MutualDatatype Unit}
    (hinv : Inv s)
    (hfresh : ∀ d ∈ block, d.name ∉ s.reserved) :
    DatatypeGen.StoredRefsAbsent s.C block := by
  intro d hd c hc arg harg d' hd' happ
  -- `d'.name` appears in `arg.2`, hence is one of its references, hence reserved;
  -- but block names are fresh.
  exact hfresh d' hd' (hinv.storedRefsReserved d hd c hc arg harg _
    (DatatypeGen.mem_getTypeRefs_of_tyNameAppears happ))

/-- The pool the datatype step hands the generator, split back into the
    external part (`ContextOk`) and the prior-datatype pool (`DatatypePoolOk`). -/
theorem tyCons_append_split {s : GenState} :
    ∀ kc ∈ s.tyCons ++ s.dtCons, kc ∈ s.tyCons ∨ kc ∈ s.dtCons :=
  fun _ hkc => List.mem_append.mp hkc

theorem genDatatypeBlock_MutualADTWF {s : GenState} {b : Bounds}
    (hinv : Inv s) {block : MutualDatatype Unit}
    (hblock : block ∈ SetGen.support
      (genMutuallyRecursiveDatatypes (G := SetGen.Set) s.baseTypes
        (s.tyCons ++ s.dtCons) b.maxExtraDatatypes b.maxTyParams b.maxExtraBaseConstrs
        b.maxRecConstrs b.maxArgs b.maxDatatypeSize s.reserved)) :
    MutualADTWF s.C block := by
  -- Block-name freshness (needed for `StoredRefsAbsent`) comes from the shape lemma.
  obtain ⟨_, hnamesFresh⟩ := genDatatypeBlock_names hblock
  have hfresh_res : ∀ d ∈ block, d.name ∉ s.reserved := by
    intro d hd hmem
    exact hnamesFresh d hd (by
      simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr hmem))
  refine DatatypeGen.genMutuallyRecursiveDatatypes_MutualADTWF
    ?_ hinv.ctxOk hinv.dtPoolOk (storedRefsAbsent_of_inv hinv hfresh_res)
    tyCons_append_split (fun kc hkc => List.mem_append_left _ hkc) hblock
  -- No name in the combined pool is `"arrow"`: external ones by
  -- `tyConsNeArrow`. A pool name is reserved, and `"arrow"` is reserved too, so that route fails. The proof
  -- therefore uses the fact that a pool name is a *datatype* of `C` and `"arrow"` is not.
  intro kc hkc
  rcases List.mem_append.mp hkc with hext | hdt
  · exact hinv.tyConsNeArrow kc hext
  · -- A pool name is a *datatype* of `C`, while `"arrow"` is external there
    -- (`ContextOk.arrow_external`), so a pool name cannot be `"arrow"`.
    intro heq
    have hmem : "arrow" ∈ s.C.datatypes.allTypeNames := heq ▸ hinv.dtPoolOk.known kc hdt
    exact absurd hinv.ctxOk.arrow_external (getType_ne_none_of_mem_allTypeNames hmem)

/-! ## Per-step name tracking -/

/-- Axiom step: emits `[.ax {name := nm} ..]`, adds `nm`. -/
theorem genDeclAxiom_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAxiom (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  simp only [genDeclAxiom, genAxiom, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨pr, ⟨nm, hnm, e, _he, hpreq⟩, hds, hs'⟩ := h
  subst hpreq
  simp only at hds hs'
  subst hds hs'
  have hnm_fresh : nm ∉ s.reserved := (genDeclName_fresh hnm).1
  have hdn : declNames [mkAxiomDecl nm e] = [nm] := by
    simp [declNames, mkAxiomDecl, Decl.names, Decl.name]
  refine namesStep_of_prepend ?_ ?_ ?_
  · rw [hdn]; rfl
  · rw [hdn]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnm_fresh
  · rw [hdn]; simp

/-- Distinct step: emits one `.func` per constant plus `[.distinct nm es ..]`, and
    adds all of `constNames ++ [nm]`.

    Freshness and internal distinctness come from the two draws: `nm` is fresh
    against `s.reserved`, and the constant names are drawn against `nm ::
    s.reserved`. Therefore each of them is fresh, they are different in pairs, and each differs from `nm`. On a
    factory clash nothing is emitted (`namesStep_nil`). -/
theorem genDeclDistinct_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclDistinct (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  simp only [genDeclDistinct, mem_support_bind_iff] at h
  obtain ⟨⟨nm, τ, cs⟩, hparts, hmatch⟩ := h
  obtain ⟨hnm_fresh, hcs_fresh, hcs_nodup⟩ := genDistinctAssertion_names hparts
  split at hmatch
  case isFalse =>
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact namesStep_nil
  cases hadd : addConstants s.C τ cs with
  | none =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact namesStep_nil
  | some pr =>
    obtain ⟨C', constDecls⟩ := pr
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    -- The emitted names are `cs ++ [nm]`.
    have hconst : declNames constDecls = cs :=
      addConstants_declNames cs s.C C' constDecls hadd
    have hdist : declNames [mkDistinctDecl nm (distinctElems τ cs)] = [nm] := by
      simp [declNames, mkDistinctDecl, Decl.names, Decl.name]
    have hdn : declNames (constDecls ++ [mkDistinctDecl nm (distinctElems τ cs)])
        = cs ++ [nm] := by
      rw [declNames_append, hconst, hdist]
    refine namesStep_of_prepend ?_ ?_ ?_
    · rw [hdn]; simp
    · rw [hdn]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact fun hmem => hcs_fresh x hx (List.mem_cons_of_mem _ hmem)
      · simp only [List.mem_singleton] at hx; subst hx; exact hnm_fresh
    · rw [hdn]
      -- `nm ∉ cs`: every constant name avoids `nm :: s.reserved`, `nm` included.
      have hnm_notin : nm ∉ cs := fun hmem => hcs_fresh nm hmem (by simp)
      refine List.nodup_append.mpr ⟨hcs_nodup, by simp, ?_⟩
      intro a ha b hb hab
      have hbn : b = nm := by simpa using hb
      exact hnm_notin (by rw [← hbn, ← hab]; exact ha)

/-- Alias step: emits `[.type (.syn ts) ..]`, adds `nm`. -/
theorem genDeclAlias_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAlias (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  simp only [genDeclAlias, genAlias, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨pr, ⟨nm, hnm, k, _hk, tps, _htps, body, _hbody, hpreq⟩, hmatch⟩ := h
  subst hpreq
  simp only [mkAliasDecl] at hmatch
  split at hmatch
  case isFalse =>
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch; subst hds hs'; exact namesStep_nil
  simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
  obtain ⟨hds, hs'⟩ := hmatch
  subst hds hs'
  have hnm_fresh : nm ∉ s.reserved := (genDeclTypeName_fresh hnm).1
  have hdn : declNames [Decl.type (TypeDecl.syn
      { name := nm, typeArgs := body.freeVars.uniq, type := body }) MetaData.empty] = [nm] := by
    simp [declNames, Decl.names, TypeDecl.names]
  refine namesStep_of_prepend ?_ ?_ ?_
  · rw [hdn]; rfl
  · rw [hdn]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnm_fresh
  · rw [hdn]; simp

/-- Abstract-type step: emits `[.type (.con ..)]` (adds `nm`) or nothing. -/
theorem genDeclAbstract_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAbstract (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  simp only [genDeclAbstract, genAbstractType, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨pr, ⟨nm, hnm, ar, _har, hpreq⟩, hmatch⟩ := h
  subst hpreq
  simp only at hmatch
  have hnm_fresh : nm ∉ s.reserved := (genDeclTypeName_fresh hnm).1
  cases hadd : s.C.addKnownTypeWithError { name := nm, metadata := ar } default with
  | error e =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch; subst hds hs'; exact namesStep_nil
  | ok C' =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch; subst hds hs'
    simp only [GenState.addAbstract]
    have hdn : declNames [mkAbstractTypeDecl nm ar] = [nm] := by
      simp [declNames, mkAbstractTypeDecl, Decl.names, TypeDecl.names]
    refine namesStep_of_prepend ?_ ?_ ?_
    · rw [hdn]; rfl
    · rw [hdn]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnm_fresh
    · rw [hdn]; simp

/-- Function step: emits `[.func func]` (adds fresh `nm`) or nothing. -/
theorem genDeclFunction_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclFunction (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  simp only [genDeclFunction, mem_support_bind_iff] at h
  obtain ⟨func₀, _hfunc₀, nm, hnm, hmatch⟩ := h
  have hnm_fresh : nm ∉ s.reserved := (genDeclName_fresh hnm).1
  let func : Function := { func₀ with name := ⟨nm, ()⟩ }
  cases hadd : s.C.addFactoryFunctionWithError func.toLFunc with
  | error e =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch; subst hds hs'; exact namesStep_nil
  | ok C' =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch; subst hds hs'
    have hdn : declNames [.func func .empty] = [nm] := by
      simp [declNames, Decl.names, Decl.name, func]
    refine namesStep_of_prepend ?_ ?_ ?_
    · rw [hdn]; rfl
    · rw [hdn]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnm_fresh
    · rw [hdn]; simp

/-- Procedure step: emits `[.proc proc]` with the fresh name `nm` (added to
    reserved); never gated (procedures leave `C`/`Γ` unchanged). -/
theorem genDeclProcedure_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclProcedure (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨proc₀, _hproc₀, nm, hnm, hds, hs'⟩ := h
  subst hds hs'
  have hnm_fresh : nm ∉ s.reserved := (genDeclName_fresh hnm).1
  have hdn : declNames [.proc
      { proc₀ with header := { proc₀.header with name := ⟨nm, ()⟩ } } .empty] = [nm] := by
    simp [declNames, Decl.names, Decl.name]
  refine namesStep_of_prepend ?_ ?_ ?_
  · rw [hdn]; rfl
  · rw [hdn]; intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnm_fresh
  · rw [hdn]; simp

/-- Datatype step: emits `[.type (.data block)]` (adds the block's names) or
    nothing. Freshness and `Nodup` of the block's names come from
    `genDatatypeBlock_names`. -/
theorem genDeclDatatype_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclDatatype (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  simp only [genDeclDatatype, mem_support_bind_iff] at h
  obtain ⟨block, hblock, hmatch⟩ := h
  obtain ⟨hNodup, hFresh⟩ := genDatatypeBlock_names hblock
  split at hmatch
  case isFalse =>
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch; subst hds hs'; exact namesStep_nil
  cases hadd : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams s.C block with
  | error e =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch; subst hds hs'; exact namesStep_nil
  | ok C' =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch; subst hds hs'
    -- `declNames [.type (.data block)] = block.map (·.name)`.
    have hdn : declNames [Decl.type (.data block) .empty] = block.map (·.name) := by
      simp [declNames, Decl.names, TypeDecl.names]
    refine namesStep_of_prepend ?_ ?_ ?_
    · rw [hdn]
    · rw [hdn]
      intro x hx
      obtain ⟨d, hd, hdname⟩ := List.mem_map.mp hx
      -- `x = d.name ∉ initialReserved … s.reserved ⊇ s.reserved`.
      rw [← hdname]
      intro hmem
      exact hFresh d hd (by
        simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hmem))
    · rw [hdn]; exact hNodup

/-- Name tracking for one declaration step (six-way dispatch). -/
theorem genDeclStep_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  -- `genDeclStep` is a weighted `frequency`; support inversion yields a
  -- `(weight, generator)` pair, so each branch equation pins both components.
  simp only [genDeclStep, mem_support_frequency_iff, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  obtain ⟨w, g, hg, _hw, hmem⟩ := h
  rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact genDeclAbstract_names hmem
  · exact genDeclAlias_names hmem
  · exact genDeclAxiom_names hmem
  · exact genDeclDistinct_names hmem
  · exact genDeclDatatype_names hmem
  · exact genDeclFunction_names hmem
  · exact genDeclProcedure_names hmem

/-- Name tracking for the whole fold: the emitted declaration names are pairwise
    distinct and disjoint from the initial reserved set; `reserved` grows by
    exactly those names. Proved by induction, composing `NamesStep`s: a later
    step's names are fresh against the *grown* reserved set (which contains the
    earlier names), so the concatenation stays `Nodup`. -/
theorem genDeclsFold_names (n : Nat) {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s b n)) :
    NamesStep s ds s' := by
  induction n generalizing s ds s' with
  | zero =>
    simp only [genDeclsFold, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨hds, hs'⟩ := h; subst hds hs'; exact namesStep_nil
  | succ n ih =>
    simp only [genDeclsFold, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ds₁, s₁⟩, hstep, ⟨rest, s₂⟩, hrest, hds, hs'⟩ := h
    subst hds hs'
    have hn₁ := genDeclStep_names hstep
    have hn₂ := ih hrest
    -- `declNames (ds₁ ++ rest) = declNames ds₁ ++ declNames rest`.
    have hsplit : declNames (ds₁ ++ rest) = declNames ds₁ ++ declNames rest := by
      simp [declNames, List.flatMap_append]
    refine
      { reserved_sub := ?_, reserved_mono := ?_, emitted_reserved := ?_, fresh := ?_, nodup := ?_ }
    · -- reserved after both steps: emitted-by-either or original.
      intro x hx
      rcases hn₂.reserved_sub x hx with hr | hs₁
      · exact Or.inl (hsplit ▸ List.mem_append_right _ hr)
      · rcases hn₁.reserved_sub x hs₁ with hd₁ | hs0
        · exact Or.inl (hsplit ▸ List.mem_append_left _ hd₁)
        · exact Or.inr hs0
    · intro x hx; exact hn₂.reserved_mono x (hn₁.reserved_mono x hx)
    · -- emitted names of the whole become reserved.
      rw [hsplit]
      intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact hn₂.reserved_mono x (hn₁.emitted_reserved x h1)
      · exact hn₂.emitted_reserved x h2
    · -- freshness against `s.reserved`.
      rw [hsplit]
      intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact hn₁.fresh x h1
      · -- `x ∈ declNames rest`, fresh against `s₁.reserved ⊇ s.reserved`.
        exact fun hc => hn₂.fresh x h2 (hn₁.reserved_mono x hc)
    · -- Nodup of the concatenation.
      rw [hsplit, List.nodup_append]
      refine ⟨hn₁.nodup, hn₂.nodup, ?_⟩
      -- disjoint: an emitted-by-step-1 name is reserved in `s₁`, so `rest` avoids it.
      intro x hx1 y hy2 hxy; subst hxy
      exact hn₂.fresh x hy2 (hn₁.emitted_reserved x hx1)

/-! ## Program-level type names are not local type names -/

/-- No type name that the declarations `ds` declare is a local type name. -/
def TypeNamesNotLocal (ds : List Decl) : Prop :=
  ∀ x ∈ programNamesOfKind { decls := ds } .type, ¬ StrataGenerators.Stmt.isLocalTypeName x.name

/-- Declarations none of which is a type declaration declare no type name. -/
theorem typeNamesNotLocal_of_kind {ds : List Decl} (h : ∀ d ∈ ds, declNameKind d ≠ .type) :
    TypeNamesNotLocal ds := by
  intro x hx
  simp only [programNamesOfKind, List.mem_flatMap, List.mem_filter, beq_iff_eq] at hx
  obtain ⟨d, ⟨hd, hkind⟩, _⟩ := hx
  exact absurd hkind (h d hd)

/-- `TypeNamesNotLocal` holds of an append when it holds of both parts. -/
theorem typeNamesNotLocal_append {ds₁ ds₂ : List Decl}
    (h₁ : TypeNamesNotLocal ds₁) (h₂ : TypeNamesNotLocal ds₂) :
    TypeNamesNotLocal (ds₁ ++ ds₂) := by
  intro x hx
  simp only [programNamesOfKind, List.filter_append, List.flatMap_append, List.mem_append] at hx
  rcases hx with hx | hx
  · exact h₁ x hx
  · exact h₂ x hx

/-- A type declaration none of whose names is a local type name declares no local type name. -/
theorem typeNamesNotLocal_type {t : TypeDecl} {md : MetaData Expression}
    (h : ∀ x ∈ t.names, StrataGenerators.Stmt.isLocalTypeName x.name = false) :
    TypeNamesNotLocal [.type t md] := by
  intro x hx
  simp only [programNamesOfKind, declNameKind, Decl.kind, List.filter_cons, List.filter_nil,
    beq_self_eq_true, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Decl.names] at hx
  exact Bool.eq_false_iff.mp (h x hx)

/-- No declaration that `addConstants` emits is a type declaration. -/
theorem addConstants_kind {τ : LMonoTy} :
    ∀ (names : List String) (C C' : LContext CoreLParams) (ds : List Decl),
      addConstants C τ names = some (C', ds) → ∀ d ∈ ds, declNameKind d ≠ .type := by
  intro names
  induction names with
  | nil =>
    intro C C' ds h
    simp only [addConstants, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp
  | cons c cs ih =>
    intro C C' ds h
    obtain ⟨C₁, ds', _, hrest, rfl⟩ := addConstants_cons h
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd'
    · simp [declNameKind, mkConstantDecl, Decl.kind]
    · exact ih C₁ C' ds' hrest d hd'

/-- No type name that a declaration step emits is a local type name. -/
theorem genDeclStep_typeNames {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b)) :
    TypeNamesNotLocal ds := by
  simp only [genDeclStep, mem_support_frequency_iff, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  obtain ⟨w, g, hg, _, hmem⟩ := h
  rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · -- abstract type
    simp only [genDeclAbstract, genAbstractType, mem_support_bind_iff, mem_support_pure_iff] at hmem
    obtain ⟨pr, ⟨nm, hnm, ar, _, rfl⟩, hmatch⟩ := hmem
    simp only at hmatch
    split at hmatch <;> simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch <;>
      obtain ⟨rfl, _⟩ := hmatch
    · refine typeNamesNotLocal_type ?_
      simpa [mkAbstractTypeDecl, TypeDecl.names] using genDeclTypeName_not_local hnm
    · exact typeNamesNotLocal_of_kind (by simp)
  · -- alias
    simp only [genDeclAlias, genAlias, mem_support_bind_iff, mem_support_pure_iff] at hmem
    obtain ⟨pr, ⟨nm, hnm, k, _, tps, _, body, _, rfl⟩, hmatch⟩ := hmem
    simp only [mkAliasDecl] at hmatch
    split at hmatch <;> simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch <;>
      obtain ⟨rfl, _⟩ := hmatch
    · refine typeNamesNotLocal_type ?_
      simpa [TypeDecl.names] using genDeclTypeName_not_local hnm
    · exact typeNamesNotLocal_of_kind (by simp)
  · -- axiom
    simp only [genDeclAxiom, genAxiom, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨pr, ⟨nm, _, e, _, rfl⟩, rfl, _⟩ := hmem
    exact typeNamesNotLocal_of_kind (by simp [declNameKind, mkAxiomDecl, Decl.kind])
  · -- distinct
    simp only [genDeclDistinct, mem_support_bind_iff] at hmem
    obtain ⟨⟨nm, τ, cs⟩, _, hmatch⟩ := hmem
    split at hmatch
    · cases hadd : addConstants s.C τ cs with
      | none =>
        rw [hadd] at hmatch
        simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
        obtain ⟨rfl, _⟩ := hmatch
        exact typeNamesNotLocal_of_kind (by simp)
      | some pr =>
        obtain ⟨C', constDecls⟩ := pr
        rw [hadd] at hmatch
        simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
        obtain ⟨rfl, _⟩ := hmatch
        refine typeNamesNotLocal_append
          (typeNamesNotLocal_of_kind (addConstants_kind cs s.C C' constDecls hadd)) ?_
        exact typeNamesNotLocal_of_kind (by simp [declNameKind, mkDistinctDecl, Decl.kind])
    · simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
      obtain ⟨rfl, _⟩ := hmatch
      exact typeNamesNotLocal_of_kind (by simp)
  · -- datatype block
    simp only [genDeclDatatype, mem_support_bind_iff] at hmem
    obtain ⟨block, _, hmatch⟩ := hmem
    split at hmatch
    · rename_i hgate
      cases hadd : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
          instToFormatIDMetaCoreLParams s.C block with
      | error e =>
        rw [hadd] at hmatch
        simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
        obtain ⟨rfl, _⟩ := hmatch
        exact typeNamesNotLocal_of_kind (by simp)
      | ok C' =>
        rw [hadd] at hmatch
        simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
        obtain ⟨rfl, _⟩ := hmatch
        refine typeNamesNotLocal_type ?_
        intro x hx
        simp only [TypeDecl.names, List.mem_map] at hx
        obtain ⟨d, hd, rfl⟩ := hx
        simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hgate
        exact (hgate d hd).2
    · simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
      obtain ⟨rfl, _⟩ := hmatch
      exact typeNamesNotLocal_of_kind (by simp)
  · -- function
    simp only [genDeclFunction, mem_support_bind_iff] at hmem
    obtain ⟨func₀, _, nm, _, hmatch⟩ := hmem
    split at hmatch <;> simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch <;>
      obtain ⟨rfl, _⟩ := hmatch
    · exact typeNamesNotLocal_of_kind (by simp [declNameKind, Decl.kind])
    · exact typeNamesNotLocal_of_kind (by simp)
  · -- procedure
    simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨proc₀, _, nm, _, rfl, _⟩ := hmem
    exact typeNamesNotLocal_of_kind (by simp [declNameKind, Decl.kind])

/-- No type name that the declaration fold emits is a local type name. -/
theorem genDeclsFold_typeNames (n : Nat) {s : GenState} {b : Bounds} {ds : List Decl}
    {s' : GenState} (h : (ds, s') ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s b n)) :
    TypeNamesNotLocal ds := by
  induction n generalizing s ds s' with
  | zero =>
    simp only [genDeclsFold, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact typeNamesNotLocal_of_kind (by simp)
  | succ n ih =>
    simp only [genDeclsFold, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ds₁, s₁⟩, hstep, ⟨rest, s₂⟩, hrest, rfl, _⟩ := h
    exact typeNamesNotLocal_append (genDeclStep_typeNames hstep) (ih hrest)

/-- `getNames.Nodup` from the fold's `declNames`-Nodup: an `Identifier Unit` list
    is `Nodup` iff its `.name` projection is (the metadata is `Unit`, always
    equal), and `Program.getNames P = P.decls.flatMap Decl.names`. -/
theorem genProgram_getNames_nodup {numDecls : Nat} {b : Bounds} {decls : List Decl}
    {sf : GenState}
    (h : (decls, sf) ∈ SetGen.support (genDeclsFold (G := SetGen.Set) initState b numDecls)) :
    (Program.mk (decls := decls)).getNames.Nodup := by
  have hnames := (genDeclsFold_names numDecls h).nodup
  -- `declNames decls = (getNames).map (·.name)` is `Nodup`; lift to the identifiers.
  simp only [Program.getNames, Program.getNames.go]
  -- `(l.map (·.name)).Nodup → l.Nodup` for `Identifier Unit` (name determines the id).
  have hkey : ∀ (l : List (Identifier Unit)), (l.map (·.name)).Nodup → l.Nodup := by
    intro l
    induction l with
    | nil => intro _; exact List.nodup_nil
    | cons hd tl ih =>
      intro hl
      simp only [List.map_cons, List.nodup_cons] at hl
      obtain ⟨hnotin, htl⟩ := hl
      refine List.nodup_cons.mpr ⟨?_, ih htl⟩
      intro hmem
      exact hnotin (List.mem_map.mpr ⟨hd, hmem, rfl⟩)
  exact hkey _ hnames

/-! ## The functions a datatype block adds -/

/-- A well-formed function has distinct formals. -/
theorem inputs_keys_nodup_of_wf {f : LFunc CoreLParams} (hwf : LFuncWF f) :
    f.inputs.keys.Nodup := by
  rw [ListMap.keys_eq_map_fst]
  have hnames : ((f.inputs.map Prod.fst).map (fun x => x.name)).Nodup := by
    rw [List.map_map]
    exact hwf.arg_nodup
  exact List.Pairwise.of_map _ (fun a b hab heq => hab (congrArg _ heq)) hnames

/-- Pushing the functions of a list one at a time with `tryPush` keeps every entry of the starting
    factory and stores each pushed function under its name, and every entry of the result is an
    old entry or a pushed function. -/
theorem foldlM_tryPush_lookup {i₁ : Inhabited CoreLParams.Metadata}
    {i₂ : Std.ToFormat CoreLParams.IDMeta} :
    ∀ (l : List (LFunc CoreLParams)) (F F' : Factory CoreLParams),
      l.foldlM (fun F fn => @Lambda.Factory.tryPush CoreLParams i₁ i₂ F fn) F = .ok F' →
      (∀ (nm : String) (g : LFunc CoreLParams), F[nm]? = some g → F'[nm]? = some g) ∧
      (∀ fn ∈ l, F'[fn.name.name]? = some fn) ∧
      (∀ (nm : String) (g : LFunc CoreLParams), F'[nm]? = some g → F[nm]? = some g ∨ g ∈ l)
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ _ hg => hg, fun _ hfn => absurd hfn List.not_mem_nil, fun _ _ hg => Or.inl hg⟩
  | fn :: rest, F, F', h => by
    unfold Lambda.Factory.tryPush at h
    by_cases hmem : fn.name.name ∈ F
    · simp only [List.foldlM_cons, dif_pos hmem, bind, Except.bind] at h
      exact absurd h (by simp)
    · simp only [List.foldlM_cons, dif_neg hmem, bind, Except.bind] at h
      obtain ⟨hold, hnew, hall⟩ := foldlM_tryPush_lookup rest _ F' h
      refine ⟨?_, ?_, ?_⟩
      · intro nm g hg
        have hne : nm ≠ fn.name.name := by
          rintro rfl
          exact hmem (mem_of_getElem?_eq_some hg)
        refine hold nm g ?_
        rw [getElem?_push F fn hmem nm, if_neg hne]
        exact hg
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · refine hold _ _ ?_
          rw [getElem?_push F f hmem, if_pos rfl]
        · exact hnew f hf
      · intro nm g hg
        rcases hall nm g hg with hpush | hrest
        · rw [getElem?_push F fn hmem nm] at hpush
          split at hpush
          · simp only [Option.some.injEq] at hpush
            subst hpush
            exact Or.inr List.mem_cons_self
          · exact Or.inl hpush
        · exact Or.inr (List.mem_cons_of_mem _ hrest)

/-- What a successful `addMutualBlock` does to the functions of a context: it adds the factory `F`
    of the block's derived functions, whose functions are well formed and have signature types
    registered in the new context; it keeps every old entry and adds nothing else. -/
structure BlockFunctionsAdded (C C' : LContext CoreLParams) (block : MutualDatatype Unit)
    (F : Factory CoreLParams) : Prop where
  derived : blockDerivedFactory block = some F
  wf : ∀ f ∈ F.toArray, LFuncWF f
  sigsKnown : ∀ f ∈ F.toArray, ∀ ty ∈ f.output :: f.inputs.values,
    LMonoTy.knownInstance ty C'.knownTypes = true
  preserves_old : ∀ (nm : String) (g : LFunc CoreLParams), C.functions[nm]? = some g →
    C'.functions[nm]? = some g
  contains_new : ∀ (nm : String) (g : LFunc CoreLParams), F[nm]? = some g →
    C'.functions[nm]? = some g
  no_other : ∀ (nm : String) (g : LFunc CoreLParams), C'.functions[nm]? = some g →
    C.functions[nm]? = some g ∨ g ∈ F.toArray

/-- A successful `addMutualBlock` of a well-formed block, in a context that registers `arrow`,
    `bool` and each of its datatypes, adds exactly the block's derived functions. -/
theorem blockFunctionsAdded_of_addMutualBlock {C C' : LContext CoreLParams}
    {block : MutualDatatype Unit}
    (h : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams C block = .ok C')
    (hwf : MutualADTWF C block) (hdk : C.DatatypesKnown)
    (harrow : C.knownTypes["arrow"]? = some 2) (hbool : C.knownTypes["bool"]? = some 0) :
    ∃ F, BlockFunctionsAdded C C' block F := by
  have hext := @KnownTypesExtends.of_addMutualBlock CoreLParams instInhabitedPUnit
    instInhabitedPUnit instToFormatIDMetaCoreLParams _ C C' block h
  obtain ⟨-, ds, fgen, fs, ks, hds, hfgen, hfs, hks, rfl⟩ :=
    @LContext.addMutualBlock_ok_inv CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams C _ block h
  have hdec := TypeFactory_addMutualBlock_decompose _ _ block _ hds
  have hblock : ∀ d ∈ block, ks[d.name]? = some d.typeArgs.length :=
    knownTypes_foldlM_add_mem C.knownTypes ks block hks
  -- A constructor argument names a known type, an earlier datatype or a datatype of the block,
  -- each registered in the new table at the arity it is applied at.
  have hargs : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      LMonoTy.knownInstance arg.2 ks = true := by
    intro d hd c hc arg harg
    refine knownInstance_of_wellKinded arg.2 ks ?_
    intro ref n hn
    rcases hwf.argsWellKinded d hd c hc arg harg ref n hn with hk | ⟨d', hd', rfl, rfl⟩ |
        ⟨d', hd', rfl, rfl⟩
    · exact hext _ _ hk
    · exact hext _ _ (hdk d' hd')
    · exact hblock d' hd'
  simp only [Lambda.Factory.addFactory, Lambda.Factory.tryAddAll] at hfs
  rw [← Array.foldlM_toList] at hfs
  obtain ⟨hold, hnew, hall⟩ := foldlM_tryPush_lookup _ C.functions fs hfs
  refine ⟨fgen,
    { derived := ?_
      wf := @genBlockFactory_wf CoreLParams _ instInhabitedPUnit instInhabitedPUnit
        instToFormatIDMetaCoreLParams block fgen hdec.1 hdec.2.2.1 hfgen
      sigsKnown := genBlockFactory_sigsKnown block fgen (hext _ _ harrow) (hext _ _ hbool)
        hblock hargs hfgen
      preserves_old := hold
      contains_new := ?_
      no_other := ?_ }⟩
  · unfold blockDerivedFactory
    rw [hfgen]
    rfl
  · intro nm g hg
    have hname := Lambda.Factory.nameOfGetElem? hg
    subst hname
    exact hnew g (Array.mem_toList_iff.mpr (Lambda.Factory.memToArrayOfGetElem? hg))
  · intro nm g hg
    rcases hall nm g hg with hg' | hg'
    · exact Or.inl hg'
    · exact Or.inr (Array.mem_toList_iff.mp hg')

/-- The curried type of every derived function of a block is well kinded in the context the
    block is added to, when that context registers `arrow`. -/
theorem blockFunction_wellKinded {C C' : LContext CoreLParams} {block : MutualDatatype Unit}
    {F : Factory CoreLParams} (hb : BlockFunctionsAdded C C' block F)
    (harrow : C'.knownTypes["arrow"]? = some 2) {fn : LFunc CoreLParams}
    (hmem : fn ∈ F.toArray) :
    C'.WellKindedTy (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)) := by
  have hknown := hb.sigsKnown fn hmem
  refine wellKindedTy_mkArrow' harrow
    (LMonoTy.knownInstance_wellKinded _ _ (hknown _ List.mem_cons_self)) _ ?_
  intro t ht
  refine LMonoTy.knownInstance_wellKinded _ _ (hknown t (List.mem_cons_of_mem _ ?_))
  rw [ListMap.values_eq_map_snd]
  exact ht

/-- Every monomorphic operator a block derives is the curried type of one of its derived
    functions. -/
theorem mem_adtDerivedOps {block : MutualDatatype Unit} {sel : DerivedOpFamilies}
    {F : Factory CoreLParams} (hF : blockDerivedFactory block = some F)
    {p : String × LMonoTy} (hp : p ∈ adtDerivedOps block sel) :
    ∃ fn, F[p.1]? = some fn ∧ p.2 = LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd) := by
  unfold adtDerivedOps at hp
  rw [hF] at hp
  obtain ⟨nm, τ⟩ := p
  exact factoryOps_mem_char F nm τ (List.mem_filter.mp hp).1

/-- Every monomorphic operator a block derives has a well-kinded type in the context the block is
    added to, when that context registers `arrow`. -/
theorem adtDerivedOps_wellKinded {C C' : LContext CoreLParams} {block : MutualDatatype Unit}
    {F : Factory CoreLParams} (hb : BlockFunctionsAdded C C' block F)
    (harrow : C'.knownTypes["arrow"]? = some 2) (sel : DerivedOpFamilies) :
    ∀ p ∈ adtDerivedOps block sel, C'.WellKindedTy p.2 := by
  intro p hp
  obtain ⟨fn, hfn, heq⟩ := mem_adtDerivedOps hb.derived hp
  rw [heq]
  exact blockFunction_wellKinded hb harrow (Lambda.Factory.memToArrayOfGetElem? hfn)

/-- After a datatype block is added, the operators of the earlier context together with the
    block's derived operators agree with the new functions, as do the earlier schemes together
    with the block's derived schemes. -/
theorem exprCtxOk_addMutualBlock {C C' : LContext CoreLParams} {block : MutualDatatype Unit}
    {F : Factory CoreLParams} {octx : OpCtx} {pctx pctx' : PolyOpCtx} {sel : DerivedOpFamilies}
    (hctx : ExprCtxOk C [] [] octx pctx) (hb : BlockFunctionsAdded C C' block F)
    (hk : KnownTypesExtends C.knownTypes C'.knownTypes)
    (hpctx : ∀ e ∈ pctx', e ∈ adtDerivedPolyOps block sel ∨ e ∈ pctx) :
    ExprCtxOk C' [] [] (OpCtx.ofList (adtDerivedOps block sel ++ octx.ops)) pctx' := by
  have harities := simpleTyArities_mono hctx.arities hk
  refine
    { arities := harities
      sigs := ?_
      fvars := fun _ hp => absurd hp List.not_mem_nil
      ops := ?_
      polys := ?_
      polysKnown := ?_ }
  · intro name f hf
    rcases hb.no_other name f hf with hold | hnew
    · exact hctx.sigs name f hold
    · have hwf := hb.wf f hnew
      exact type_eq_of_sigWF harities.arrow (inputs_keys_nodup_of_wf hwf) hwf.typeArgs_nodup
        (hb.sigsKnown f hnew _ List.mem_cons_self)
  · intro p hp
    rw [OpCtx.ops_ofList] at hp
    rcases List.mem_append.mp hp with hnew | hold
    · obtain ⟨fn, hfn, heq⟩ := mem_adtDerivedOps hb.derived hnew
      refine ⟨knownInstance_of_wellKinded _ _ (adtDerivedOps_wellKinded hb harities.arrow sel p
        hnew), fn, hb.contains_new _ _ hfn, [], ?_⟩
      rw [LMonoTy.subst_nil]
      exact heq
    · obtain ⟨hki, f, hf, σ, hσ⟩ := hctx.ops p hold
      exact ⟨knownInstance_mono _ _ _ hk hki, f, hb.preserves_old _ _ hf, σ, hσ⟩
  · intro name lty hmem
    rcases hpctx _ hmem with hnew | hold
    · obtain ⟨fn, hfn, heq⟩ :=
        PCtxWF_factoryPolyOps F name lty (mem_adtDerivedPolyOps hb.derived hnew)
      exact ⟨fn, hb.contains_new _ _ hfn, heq⟩
    · obtain ⟨fn, hfn, heq⟩ := hctx.polys name lty hold
      exact ⟨fn, hb.preserves_old _ _ hfn, heq⟩
  · intro nm bvs body hmem
    rcases hpctx _ hmem with hnew | hold
    · obtain ⟨fn, hfn, heq⟩ :=
        PCtxWF_factoryPolyOps F nm _ (mem_adtDerivedPolyOps hb.derived hnew)
      simp only [LTy.forAll.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      exact knownInstance_of_wellKinded _ _
        (blockFunction_wellKinded hb harities.arrow (Lambda.Factory.memToArrayOfGetElem? hfn))
    · exact knownInstance_mono _ _ _ hk (hctx.polysKnown nm bvs body hold)

/-- After a datatype block is added, every scheme drawn from the earlier closed schemes or from
    the block's derived schemes is closed. -/
theorem polysClosed_addMutualBlock {C C' : LContext CoreLParams} {block : MutualDatatype Unit}
    {F : Factory CoreLParams} {pctx pctx' : PolyOpCtx} {sel : DerivedOpFamilies}
    (hb : BlockFunctionsAdded C C' block F)
    (hclosed : ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx →
      ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs)
    (hpctx : ∀ e ∈ pctx', e ∈ adtDerivedPolyOps block sel ∨ e ∈ pctx) :
    ∀ nm bvs body, (nm, LTy.forAll bvs body) ∈ pctx' → ∀ v ∈ LMonoTy.freeVars body, v ∈ bvs := by
  intro nm bvs body hmem
  rcases hpctx _ hmem with hnew | hold
  · exact factoryPolyOps_closed ⟨hb.wf⟩ _ (mem_adtDerivedPolyOps hb.derived hnew)
  · exact hclosed nm bvs body hold

/-! ## The invariant holds initially -/

/-- `Core.KnownTypes.keywords ⊆ initialReserved default default Core.KnownTypes.keywords`
    (the seed reserved set includes Core's known type names verbatim). -/
theorem keywords_sub_initReserved :
    Core.KnownTypes.keywords ⊆
      DatatypeGen.initialReserved DatatypeGen.defaultBaseTypes DatatypeGen.defaultTyCons
        Core.KnownTypes.keywords := by
  intro x hx
  simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr hx)

/-- When a curried function type is well kinded, so is its result type. -/
theorem wellKindedTy_of_mkArrow'_out {C : LContext CoreLParams} {out : LMonoTy} :
    ∀ (ins : List LMonoTy), C.WellKindedTy (LMonoTy.mkArrow' out ins) → C.WellKindedTy out
  | [], h => by rw [LMonoTy.mkArrow'_nil] at h; exact h
  | m :: ms, h => by
    refine wellKindedTy_of_mkArrow'_out ms ?_
    intro ref n hn
    refine h ref n ?_
    simp only [LMonoTy.mkArrow', LMonoTy.arrow, getTypeConsArities, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr hn)

/-- `programContext` registers the built-in types at their arities. -/
theorem simpleTyArities_programContext : SimpleTyArities programContext :=
  ⟨coreKnownTypes_getElem? _ _ (by decide), coreKnownTypes_getElem? _ _ (by decide),
    coreKnownTypes_getElem? _ _ (by decide), coreKnownTypes_getElem? _ _ (by decide),
    coreKnownTypes_getElem? _ _ (by decide), coreKnownTypes_getElem? _ _ (by decide),
    coreKnownTypes_getElem? _ _ (by decide), coreKnownTypes_getElem? _ _ (by decide)⟩

/-- The curried type of every function of `Core.Factory` is well kinded in `programContext`. -/
theorem coreFactory_wellKinded {f : LFunc CoreLParams} (hf : f ∈ Core.Factory.toArray) :
    programContext.WellKindedTy (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)) :=
  Core.Factory_opTypes_wellKinded programContext rfl f hf

/-- Every operator of `coreMonoOps` has a well-kinded type in `programContext`. -/
theorem coreMonoOps_wellKinded : ∀ p ∈ coreMonoOps.ops, programContext.WellKindedTy p.2 := by
  intro p hp
  obtain ⟨nm, τ⟩ := p
  obtain ⟨fn, hfn, rfl⟩ := factoryOps_mem_char Core.Factory nm τ hp
  exact coreFactory_wellKinded (Lambda.Factory.memToArrayOfGetElem? hfn)

/-- The operators and polymorphic schemes of `Core.Factory` that the initial state draws on agree
    with the functions of `programContext`, and `programContext` gives each of its functions the
    type scheme of its signature. -/
theorem exprCtxOk_programContext :
    ExprCtxOk programContext [] [] coreMonoOps corePolyOps where
  arities := simpleTyArities_programContext
  sigs := by
    intro name f hf
    have hmem : f ∈ Core.Factory.toArray := Lambda.Factory.memToArrayOfGetElem? hf
    have hwf := Core.Factory_wf.lfuncs_wf f hmem
    have hin : f.inputs.keys.Nodup := inputs_keys_nodup_of_wf hwf
    have hout : LMonoTy.knownInstance f.output programContext.knownTypes = true :=
      knownInstance_of_wellKinded _ _ (wellKindedTy_of_mkArrow'_out _ (coreFactory_wellKinded hmem))
    exact type_eq_of_sigWF simpleTyArities_programContext.arrow hin hwf.typeArgs_nodup hout
  fvars := fun _ hp => absurd hp List.not_mem_nil
  ops := by
    intro p hp
    obtain ⟨nm, τ⟩ := p
    obtain ⟨fn, hfn, rfl⟩ := factoryOps_mem_char Core.Factory nm τ hp
    exact ⟨knownInstance_of_wellKinded _ _ (coreMonoOps_wellKinded _ hp), fn, hfn, [],
      (LMonoTy.subst_nil _).symm⟩
  polys := fun name lty hmem =>
    PCtxWF_factoryPolyOps Core.Factory name lty (corePolyOps_subset_factoryPolyOps _ hmem)
  polysKnown := by
    intro nm bvs body hmem
    have hfp := corePolyOps_subset_factoryPolyOps _ hmem
    simp only [factoryPolyOps, List.mem_filterMap, Option.some.injEq, Prod.mk.injEq,
      LTy.forAll.injEq] at hfp
    obtain ⟨f, hf, -, -, rfl⟩ := hfp
    exact knownInstance_of_wellKinded _ _ (coreFactory_wellKinded (Array.mem_def.mpr hf))

/-- The initial fold state satisfies `Inv`. -/
theorem inv_initState : Inv initState := by
  -- The seed reserved set.
  have hseed : initState.reserved =
      DatatypeGen.initialReserved DatatypeGen.defaultBaseTypes DatatypeGen.defaultTyCons
        Core.KnownTypes.keywords := rfl
  refine
    { ctxOk := ?_
      knownReserved := ?_
      baseSupset := ?_
      tyConsSupset := ?_
      baseReserved := ?_
      tyConReserved := ?_
      arrowReserved := ?_
      typesNil := rfl
      rigidNil := rfl
      tyConsNeArrow := ?_
      datatypesReserved := ?_
      dtPoolOk := { known := by simp [initState], arity := by simp [initState],
                    inhab := by simp [initState] }
      dtConsReserved := by intro x hx; simp [initState] at hx
      storedRefsReserved := ?_
      datatypesKnown := by
        intro d hd
        simp [initState, programContext, DatatypeGen.coreContext, TypeFactory.allDatatypes] at hd
      octxWK := coreMonoOps_wellKinded
      sigsWK := by intro sig hsig; simp [initState] at hsig
      exprCtx := ?_
      polysClosed := ?_ }
  · -- `ContextOk` reads the known types and datatypes only, where `programContext` and
    -- `coreContext` agree.
    rw [hseed]
    have hcore := contextOk_reserved_mono DatatypeGen.defaultContextOk keywords_sub_initReserved
    exact { hcore with }
  · -- The known types of `programContext` are Core's keywords, all in the seed.
    intro k hk
    rw [hseed]
    exact keywords_sub_initReserved hk
  · -- `initState.baseTypes = defaultBaseTypes`.
    exact fun x hx => hx
  · exact fun x hx => hx
  · -- default base types are in the seed reserved set.
    intro x hx
    rw [hseed]
    simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (Or.inl (Or.inr hx)))
  · -- default tyCon names are in the seed.
    intro x hx
    rw [hseed]
    simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (Or.inr hx))
  · -- `"arrow"` heads the seed.
    rw [hseed]
    simp [DatatypeGen.initialReserved]
  · -- `initState.tyCons = defaultTyCons`, none of which is `"arrow"` (`decide`).
    exact DatatypeGen.defaultTyCons_ne_arrow
  · -- `programContext` holds no datatypes, so this is vacuous.
    intro n hn
    simp [initState, programContext, DatatypeGen.coreContext, TypeFactory.allTypeNames,
      TypeFactory.allDatatypes] at hn
  · -- `programContext` holds no datatypes, so there are no stored references either.
    intro d hd
    simp [initState, programContext, DatatypeGen.coreContext, TypeFactory.allDatatypes] at hd

  · simp only [initState, List.append_nil]
    exact exprCtxOk_programContext
  · intro nm bvs body hmem
    simp only [initState, List.append_nil] at hmem
    exact corePolyOps_closed _ hmem

end ProgramGen
