import StrataGenerators.ProgramGen
import StrataGenerators.ProgramGen.ContextOkPreserve
import StrataGenerators.HasTypeAGen

/-!
# Soundness of the whole-program generator

Every program `ProgramGen.genProgram` produces is well-typed with respect to
`Core.TypeSpec.ProgramHasTypeA` — i.e. `ProgramHasType'` at the annotated
`HasTypeA` spec.

The proof is layered to mirror the generator:

* **Bridge lemmas** turn a successful checker add into the exact premise a
  `DeclHasType'` constructor asks for (`FactoryExtendedBy` from
  `addFactoryFunctionWithError = .ok`; the trivial `type_con` success handling).
* **Per-declaration soundness** — each `genDecl*` step's support consists of
  `(ds, s')` with `ds` well-typed under `DeclsHasType'` from the input to the
  output state.
* **The fold** chains per-step soundness into `DeclsHasType'` over the whole
  program, and the top-level theorem adds `getNames.Nodup`.

Everything is stated against `SetGen.Set` (the generator's support semantics),
following the existing sub-generator proofs.
-/

open Lambda RandomChoice Core Core.TypeSpec Imperative SetGen
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
    exactly the emitted names (as a *set* — the generator prepends, so the literal
    order is reversed across the fold, but only membership matters for
    `getNames.Nodup`). -/
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

/-! ## Generic `DeclsHasType'` chaining -/

/-- `DeclsHasType'` composes over list append: threading through the split point. -/
theorem declsHasType_append {P : Program} {C C' C'' : LContext CoreLParams}
    {Γ Γ' Γ'' : TContext Unit} {ds₁ ds₂ : List Decl}
    (h₁ : DeclsHasTypeA P C Γ ds₁ C' Γ')
    (h₂ : DeclsHasTypeA P C' Γ' ds₂ C'' Γ'') :
    DeclsHasTypeA P C Γ (ds₁ ++ ds₂) C'' Γ'' := by
  induction h₁ with
  | nil => simpa using h₂
  | cons _ _ _ _ _ _ _ _ hd _ ih =>
    exact DeclsHasType'.cons _ _ _ _ _ _ _ _ hd (ih h₂)

/-! ## Bridge lemmas -/

/-- Membership in a pushed factory, proved by unfolding `Factory.push`'s effect
    on the underlying `nameMap` (a `HashMap`) — the private `Factory.push_mem_iff`
    is not exported from its `module`, so we re-derive it here. -/
theorem mem_push_iff (F : Factory CoreLParams) (fn : LFunc CoreLParams)
    (h : ¬ fn.name.name ∈ F) (name : String) :
    name ∈ F.push fn h ↔ name = fn.name.name ∨ name ∈ F := by
  simp +instances only [Lambda.Factory.instMem, Lambda.Factory.mem, Lambda.Factory.push]
  simp only [Std.HashMap.mem_insert]
  constructor <;> intro hm <;> grind

/-- A successful `addFactoryFunctionWithError C fn = .ok C'` witnesses
    `FactoryExtendedBy C C' [fn]`: only the function factory changes, every old
    name survives, `fn`'s name is present, and no other name appears. Proved from
    `Factory.tryPush`'s success branch via `mem_push_iff`. -/
theorem factoryExtendedBy_of_addFactory
    {C C' : LContext CoreLParams} {fn : LFunc CoreLParams}
    (h : C.addFactoryFunctionWithError fn = .ok C') :
    FactoryExtendedBy C C' [fn] := by
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
    · intro nm hnm
      exact (mem_push_iff C.functions fn hmem nm).mpr (Or.inr hnm)
    · intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      exact (mem_push_iff C.functions f hmem _).mpr (Or.inl rfl)
    · intro nm hnm
      rcases (mem_push_iff C.functions fn hmem nm).mp hnm with rfl | hmem'
      · right; simp
      · left; exact hmem'

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
type, the pool itself must grow — so `ContextOk` has to be re-established
with `nm` added to `baseTypes` (arity 0) or `tyCons` (arity ≥ 1).

Two facts about the new entry carry it:

* **known**: `nm ∈ C'.knownTypes.keywords`, immediate from the `insertIfNew` the
  gate ran, giving `base_known`/`tyCon_known`;
* **external**: `C'.datatypes.getType nm = none`. `addKnownTypeWithError` leaves
  `datatypes` untouched, so this is a fact about `C` — supplied by the caller from
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

/-! ## Expression-typing bridge

Under the annotated spec `instHasTypeA`, `exprTyped C Γ e mty` is definitionally
`LExpr.HasTypeA [] e mty` — it ignores the context. So a `bool`-typed expression
from `genLExpr … [] [] depth .bool` discharges the `.ax` obligation, and any
annotated expression from the generator discharges a `.distinct` element's
`∃ mty, exprTyped …` obligation. -/

/-- The axiom expression generated by `genAxiom` is `bool`-typed under the
    annotated spec, in any ambient `C`/`Γ`. -/
theorem genAxiom_exprTyped {octx : OpCtx} {pctx : PolyOpCtx}
    {reserved : List String} {depth : Nat}
    {C : LContext CoreLParams} {Γ : TContext Unit}
    {decl : Decl} {name : String}
    (h : (decl, name) ∈ SetGen.support
      (genAxiom (G := SetGen.Set) octx pctx reserved depth)) :
    ∃ a, decl = .ax a .empty ∧
      instHasTypeA.exprTyped C Γ a.e (instHasTypeA.embed .bool) := by
  simp only [genAxiom, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨nm, _hnm, e, he, hdecl, hname⟩ := h
  refine ⟨{ name := nm, e := e }, hdecl, ?_⟩
  -- `instHasTypeA.exprTyped C Γ e (embed .bool) = HasTypeA' [] e .bool`
  show LExpr.HasTypeA [] e .bool
  exact genLExpr_sound [] octx pctx [] [] depth .bool _ e he

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

      This is stated at `s.baseTypes`/`s.tyCons` — the pool grown by abstract-type
      declarations — rather than at the fixed default, which is what lets a
      datatype block reference a previously declared abstract type (interleaving
      direction (2)). The abstract-type
      step re-establishes it at the grown pool via
      `contextOk_addKnownType_grow`. -/
  ctxOk : DatatypeGen.ContextOk s.C s.baseTypes s.tyCons s.reserved
  /-- Every type name the context knows is reserved (needed for the alias/type-con
      name-clash guards). -/
  knownReserved : ∀ k ∈ s.C.knownTypes.keywords, k ∈ s.reserved
  /-- No alias name in `Γ` is a base type, applied constructor, or `"arrow"` — so
      an alias-body reference (confined to those) never matches an alias name,
      giving `aliasFree`. -/
  aliasPoolDisjoint : ∀ a ∈ s.Γ.aliases,
    a.name ∉ s.baseTypes ∧ a.name ∉ s.tyCons.map (·.1) ∧ a.name ≠ "arrow"
  /-- Every alias name in `Γ` is reserved (it was added to `reserved` when the
      alias was declared). Combined with a freshly drawn name being unreserved,
      this keeps a new abstract type's name distinct from every alias name. -/
  aliasNamesReserved : ∀ a ∈ s.Γ.aliases, a.name ∈ s.reserved
  /-- The referenceable base/applied pool is a superset of the default (the
      datatype generator uses the default pool; alias/distinct bodies use
      the growing one). Grown only by abstract types. -/
  baseSupset : DatatypeGen.defaultBaseTypes ⊆ s.baseTypes
  tyConsSupset : DatatypeGen.defaultTyCons ⊆ s.tyCons
  /-- The *current* pool names are all reserved — so a freshly drawn name
      (∉ reserved) differs from every base type, applied constructor, and
      `"arrow"`. This is what a new alias/abstract-type name uses to stay
      disjoint from the pool. -/
  baseReserved : ∀ x ∈ s.baseTypes, x ∈ s.reserved
  tyConReserved : ∀ x ∈ s.tyCons.map (·.1), x ∈ s.reserved
  arrowReserved : "arrow" ∈ s.reserved
  /-- The type scope holds no *value* bindings — only aliases. Top-level
      declarations never bind expression variables, so `Γ.types` stays empty
      throughout the fold. Needed to align a generated procedure body's context
      with `procBodyContext Γ proc` (which pushes the body scope onto `Γ.types`). -/
  typesNil : s.Γ.types = []
  /-- The context declares no rigid type variables (top-level declarations never
      introduce any; only a procedure body checks under rigid vars, internally).
      So `s.C.rigidTypeVars = [] ⊆ proc.header.typeArgs`, which discharges the
      rigidvar side condition of `genProcedure_sound_ambient`. -/
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
  /-- The prior-datatype pool resolves and is inhabited in `C` — the hypothesis
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

/-- **The fold's invariant already pins the `SimpleType` arities.** The default pool
    is contained in the threaded one (`baseSupset` / `tyConsSupset`), and `ContextOk`'s
    arity fields register each of its members at its own arity — which is exactly
    `SimpleTyArities`, the premise upstream's `init` and `signatureWellKinded` rules need. -/
theorem simpleTyArities_of_inv {s : GenState} (hinv : Inv s) : SimpleTyArities s.C := by
  have hb : ∀ b ∈ DatatypeGen.defaultBaseTypes, s.C.knownTypes[b]? = some 0 :=
    fun b hb => hinv.ctxOk.base_arity b (hinv.baseSupset hb)
  have htc : ∀ kc ∈ DatatypeGen.defaultTyCons, s.C.knownTypes[kc.1]? = some kc.2 :=
    fun kc hkc => hinv.ctxOk.tyCon_arity kc (hinv.tyConsSupset hkc)
  -- Membership in the *derived* pool is now an arity lookup in `Core.KnownTypes`
  -- (`mem_defaultBaseTypes_iff` / `mem_defaultTyCons_iff`), which `native_decide` settles.
  refine ⟨?_, ?_, ?_, ?_, ?_, hinv.ctxOk.arrow_arity, ?_, ?_⟩
  · exact hb "bool" (DatatypeGen.mem_defaultBaseTypes_iff.mpr (by native_decide))
  · exact hb "int" (DatatypeGen.mem_defaultBaseTypes_iff.mpr (by native_decide))
  · exact hb "string" (DatatypeGen.mem_defaultBaseTypes_iff.mpr (by native_decide))
  · exact hb "real" (DatatypeGen.mem_defaultBaseTypes_iff.mpr (by native_decide))
  · exact hb "regex" (DatatypeGen.mem_defaultBaseTypes_iff.mpr (by native_decide))
  · exact htc ("Map", 2) (DatatypeGen.mem_defaultTyCons_iff.mpr
      ⟨DatatypeGen.mem_coreAppliedTyCons_iff.mpr ⟨by native_decide, by simp, by simp⟩, by simp⟩)
  · exact htc ("Sequence", 1) (DatatypeGen.mem_defaultTyCons_iff.mpr
      ⟨DatatypeGen.mem_coreAppliedTyCons_iff.mpr ⟨by native_decide, by simp, by simp⟩, by simp⟩)

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

/-! ## Alias well-formedness helpers -/

/-- If every type-constructor name referenced anywhere in `ty` fails to match any
    alias name in `aliases`, then `ty` is alias-free. Structural recursion over
    `ty` mirroring `LMonoTy.aliasFree` / `getTypeRefs`. -/
theorem aliasFree_of_refs_disjoint {aliases : List TypeAlias} :
    ∀ (ty : LMonoTy),
      (∀ r ∈ getTypeRefs ty, aliases.find? (fun a => a.name == r) = none) →
      LMonoTy.aliasFree aliases ty := by
  intro ty
  induction ty with
  | ftvar _ => intro _; exact True.intro
  | bitvec _ => intro _; exact True.intro
  | tcons name args ih =>
    intro href
    refine ⟨?_, ?_⟩
    · -- head does not match any alias by name (⇒ by name ∧ length)
      have hname : aliases.find? (fun a => a.name == name) = none :=
        href name (by simp [getTypeRefs])
      -- refine to the name-and-length predicate
      rw [List.find?_eq_none] at hname ⊢
      intro a ha
      have hn := hname a ha
      rw [Bool.not_eq_true] at hn ⊢
      simp only [Bool.and_eq_false_iff]
      exact Or.inl hn
    · -- arguments are alias-free by the IH; each arg's refs ⊆ ty's refs
      have hargs : ∀ arg ∈ args, LMonoTy.aliasFree aliases arg := by
        intro arg harg
        exact ih arg harg (fun r hr => href r (by
          simp only [getTypeRefs, List.mem_cons, List.mem_flatMap]
          exact Or.inr ⟨arg, harg, hr⟩))
      -- assemble `LMonoTys.aliasFree`
      clear href ih
      induction args with
      | nil => exact True.intro
      | cons hd tl ihl =>
        exact ⟨hargs hd (by simp), ihl (fun a ha => hargs a (by simp [ha]))⟩

/-- Every element of a generated `distinct` is an annotated `.op` node, hence
    well-typed at its annotation — discharging the `∃ mty, exprTyped …` obligation
    of `DeclHasType'.distinct` in any `C`/`Γ`.

    `HasTypeA.op` reads the type off the annotation, exactly as `HasTypeA.fvar` would;
    the difference is invisible here and decisive for the checker, which can resolve
    `.op` at a declared constant but cannot resolve a top-level `.fvar` at all. -/
theorem distinctElems_typed {τ : LMonoTy} {names : List String}
    {C : LContext CoreLParams} {Γ : TContext Unit} :
    ∀ e ∈ distinctElems τ names,
      ∃ mty, instHasTypeA.exprTyped C Γ e (instHasTypeA.embed mty) := by
  intro e he
  simp only [distinctElems, List.mem_map] at he
  obtain ⟨c, _hc, rfl⟩ := he
  exact ⟨τ, LExpr.HasTypeA.op⟩

/-- The element type a `genDistinctAssertion` draw produces is **ground**: it is drawn
    over `tyParams := []`, so `genArgTy_freeVars` (at the vacuous
    `BlockRefsWF [] [] []`) leaves it no free type variables.

    This is what each emitted constant's `FuncHasType'.noUndeclaredVars` needs — a
    constant declares no type arguments, so its signature must be closed. -/
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
  exact ⟨DatatypeGen.genFreshName_fresh _ _ hnm,
         DatatypeGen.genFreshNames_fresh _ _ _ hcs,
         DatatypeGen.genFreshNames_nodup _ _ _ hcs⟩

/-! ## Per-declaration soundness: aliases

The alias step leaves `C` unchanged and extends `Γ` with the generated alias. We
show the emitted declaration is `DeclHasTypeA`, and that `Inv` is preserved. -/

/-- Soundness of the alias step. For any `P`, the emitted declaration list is
    well-typed from `s`'s context/scope to `s'`'s, and `Inv` is preserved. -/
theorem genDeclAlias_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAlias (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  simp only [genDeclAlias, genAlias, mem_support_bind_iff, mem_support_pure_iff,
    Prod.mk.injEq] at h
  obtain ⟨pr, ⟨nm, hnm, ntp, _hntp, tyParams, _htp, body, hbody, hpr⟩, hds, hs'⟩ := h
  -- `pr = (mkAliasDecl nm body, nm)`.
  subst hpr
  simp only at hds hs'
  -- Name freshness: `nm ∉ s.reserved`.
  have hnm_fresh : nm ∉ s.reserved := DatatypeGen.genFreshName_fresh s.reserved nm hnm
  -- The built synonym.
  let ts : TypeSynonym :=
    { name := nm, typeArgs := (LMonoTy.freeVars body).dedup, type := body }
  -- `mkAliasDecl nm body = .type (.syn ts) .empty`.
  have hmk : mkAliasDecl nm body = .type (.syn ts) .empty := rfl
  -- Establish the six `type_syn` premises.
  have hNodup : ts.typeArgs.Nodup := (LMonoTy.freeVars body).nodup_dedup
  have hclosed : ∀ v, v ∈ LMonoTy.freeVars ts.type → v ∈ ts.typeArgs := by
    intro v hv; exact (List.mem_of_dedup _ _).mp hv
  have hnophantom : ∀ v, v ∈ ts.typeArgs → v ∈ LMonoTy.freeVars ts.type := by
    intro v hv; exact (List.mem_of_dedup _ _).mpr hv
  have hname_clash : ¬ s.C.knownTypes.containsName ts.name := by
    intro hc
    have : ts.name ∈ s.C.knownTypes.keywords := by
      simpa [KnownTypes.containsName, KnownTypes.keywords, Std.HashMap.mem_keys] using hc
    exact hnm_fresh (hinv.knownReserved _ this)
  have haliasFree : LMonoTy.aliasFree s.Γ.aliases ts.type := by
    apply aliasFree_of_refs_disjoint
    intro r hr
    have hrefs := genNonRecursiveArgTy_refs (baseTypes := s.baseTypes) (tyCons := s.tyCons)
      (tyParams := tyParams) (size := b.tySize) hbody r hr
    rw [List.find?_eq_none]
    intro a ha
    rw [Bool.not_eq_true, beq_eq_false_iff_ne]
    intro hcontra
    subst hcontra
    obtain ⟨hb1, hb2, hb3⟩ := hinv.aliasPoolDisjoint a ha
    rcases hrefs with hbase | htc | harr
    · exact hb1 hbase
    · exact hb2 htc
    · exact hb3 harr
  have haliasEquiv : AliasEquiv s.Γ.aliases ts.type ts.type := AliasEquiv.refl
  -- The extended type scope.
  let Γ' : TContext Unit :=
    { s.Γ with aliases := { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } :: s.Γ.aliases }
  have hdecl : DeclHasTypeA P s.C s.Γ (mkAliasDecl nm body) s.C Γ' := by
    rw [hmk]
    exact DeclHasType'.type_syn s.C s.Γ ts .empty ts.type hNodup hclosed hnophantom
      hname_clash haliasFree haliasEquiv
  -- The next state.
  subst hds hs'
  refine ⟨?_, ?_⟩
  · -- `DeclsHasTypeA` for the singleton list.
    exact DeclsHasType'.cons _ _ _ _ _ _ _ _ hdecl (DeclsHasType'.nil _ _)
  · -- `Inv` preserved: `C`, pool unchanged; `reserved` grows; new alias respects
    -- pool-disjointness (its name is fresh, so avoids the pool).
    refine
      { ctxOk := ?_
        knownReserved := ?_
        aliasPoolDisjoint := ?_
        aliasNamesReserved := ?_
        tyConsNeArrow := hinv.tyConsNeArrow
        datatypesReserved := fun n hn => List.mem_cons_of_mem _ (hinv.datatypesReserved n hn)
        dtPoolOk := hinv.dtPoolOk
        dtConsReserved := fun x hx => List.mem_cons_of_mem _ (hinv.dtConsReserved x hx)
        storedRefsReserved := fun d hd c hc arg harg r hr =>
          List.mem_cons_of_mem _ (hinv.storedRefsReserved d hd c hc arg harg r hr)
        baseSupset := hinv.baseSupset
        tyConsSupset := hinv.tyConsSupset
        baseReserved := ?_
        tyConReserved := ?_
        arrowReserved := ?_
        typesNil := hinv.typesNil
        rigidNil := hinv.rigidNil }
    · -- `s'.C = s.C`, `s'.reserved = nm :: s.reserved` ⊇ `s.reserved`.
      exact contextOk_reserved_mono hinv.ctxOk (fun x hx => List.mem_cons_of_mem _ hx)
    · intro k hk; exact List.mem_cons_of_mem _ (hinv.knownReserved k hk)
    · intro a ha
      -- `a ∈ (new alias) :: s.Γ.aliases`; reduce the `match` on `mkAliasDecl`.
      simp only [mkAliasDecl, List.mem_cons] at ha
      rcases ha with rfl | ha
      · -- the new alias: name `nm` is fresh, so avoids the pool (all reserved).
        refine ⟨?_, ?_, ?_⟩
        · intro hb; simp only at hb; exact hnm_fresh (hinv.baseReserved _ hb)
        · intro hb; simp only at hb; exact hnm_fresh (hinv.tyConReserved _ hb)
        · intro hb; simp only at hb; exact hnm_fresh (hb ▸ hinv.arrowReserved)
      · exact hinv.aliasPoolDisjoint a ha
    · -- alias names reserved: the new alias's name is `nm` (just added); old ones grow.
      intro a ha
      simp only [mkAliasDecl, List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp only; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hinv.aliasNamesReserved a ha)
    · intro x hx; exact List.mem_cons_of_mem _ (hinv.baseReserved x hx)
    · intro x hx; exact List.mem_cons_of_mem _ (hinv.tyConReserved x hx)
    · exact List.mem_cons_of_mem _ hinv.arrowReserved

/-! ## Per-declaration soundness: axioms and distinct

Both leave `C`, `Γ`, and the type-constructor pool unchanged; only `reserved`
grows. So
`Inv` preservation is `contextOk_reserved_mono` plus monotonicity of the reserved
facts, and the `DeclHasType'` derivation comes from the expression bridge. -/

/-- A state whose only change from `s` is prepending `name` to `reserved`
    preserves `Inv`. -/
theorem inv_cons_reserved {s : GenState} (hinv : Inv s) (name : String) :
    Inv { s with reserved := name :: s.reserved } := by
  refine
    { ctxOk := contextOk_reserved_mono hinv.ctxOk (fun x hx => List.mem_cons_of_mem _ hx)
      knownReserved := fun k hk => List.mem_cons_of_mem _ (hinv.knownReserved k hk)
      aliasPoolDisjoint := hinv.aliasPoolDisjoint
      aliasNamesReserved := fun a ha => List.mem_cons_of_mem _ (hinv.aliasNamesReserved a ha)
      tyConsNeArrow := hinv.tyConsNeArrow
      datatypesReserved := fun n hn => List.mem_cons_of_mem _ (hinv.datatypesReserved n hn)
      dtPoolOk := hinv.dtPoolOk
      dtConsReserved := fun x hx => List.mem_cons_of_mem _ (hinv.dtConsReserved x hx)
      storedRefsReserved := fun d hd c hc arg harg r hr =>
        List.mem_cons_of_mem _ (hinv.storedRefsReserved d hd c hc arg harg r hr)
      baseSupset := hinv.baseSupset
      tyConsSupset := hinv.tyConsSupset
      baseReserved := fun x hx => List.mem_cons_of_mem _ (hinv.baseReserved x hx)
      tyConReserved := fun x hx => List.mem_cons_of_mem _ (hinv.tyConReserved x hx)
      arrowReserved := List.mem_cons_of_mem _ hinv.arrowReserved
      typesNil := hinv.typesNil
      rigidNil := hinv.rigidNil }

/-- A state whose only changes from `s` are prepending `name` to `reserved` and
    `sig` to `procs` preserves `Inv`. No `Inv` field mentions `procs` — the
    callable-signature context is constrained by `ProcSigCorresponds` at the top
    level instead (see `ProgramGen.ProcSigThread`), not by the fold invariant. -/
theorem inv_cons_reserved_procs {s : GenState} (hinv : Inv s) (name : String)
    (sig : StrataGenerators.Stmt.ProcSig) :
    Inv { s with reserved := name :: s.reserved, procs := sig :: s.procs } := by
  -- Every `Inv` field reads only `C`/`Γ`/`baseTypes`/`tyCons`/`dtCons`/`reserved`,
  -- all of which agree with `{ s with reserved := name :: s.reserved }`.
  have h := inv_cons_reserved (s := s) hinv name
  exact
    { ctxOk := h.ctxOk
      knownReserved := h.knownReserved
      aliasPoolDisjoint := h.aliasPoolDisjoint
      aliasNamesReserved := h.aliasNamesReserved
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
      storedRefsReserved := h.storedRefsReserved }

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
      aliasPoolDisjoint := hinv.aliasPoolDisjoint
      aliasNamesReserved := fun a ha => mono _ (hinv.aliasNamesReserved a ha)
      tyConsNeArrow := hinv.tyConsNeArrow
      datatypesReserved := fun n hn => mono _ (hinv.datatypesReserved n hn)
      dtPoolOk := hinv.dtPoolOk
      dtConsReserved := fun x hx => mono _ (hinv.dtConsReserved x hx)
      storedRefsReserved := fun d hd c hc arg harg r hr =>
        mono _ (hinv.storedRefsReserved d hd c hc arg harg r hr)
      baseSupset := hinv.baseSupset
      tyConsSupset := hinv.tyConsSupset
      baseReserved := fun x hx => mono _ (hinv.baseReserved x hx)
      tyConReserved := fun x hx => mono _ (hinv.tyConReserved x hx)
      arrowReserved := mono _ hinv.arrowReserved
      typesNil := hinv.typesNil
      rigidNil := hinv.rigidNil }

/-- **`Inv` is preserved by any change to the operator contexts.** No `Inv`
    field mentions `octx`, `pctx` or `derivedPctx` — under the annotated spec an
    `.op` node is typed from its own annotation, so the operator contexts constrain
    which programs are *drawn*, never which are well-typed — hence every field of
    `hinv` transfers verbatim and `{ hinv with }` copies them.

    Needed because two steps now grow an operator context while `Inv` is being
    re-established: the datatype step (with the block's derived functions) and the
    function step (registering the declared function so a later body can call it).
    Compose with `inv_addFactory` / `inv_grow_reserved`, which cover the fields that
    *do* move. -/
theorem inv_setOpCtxs {s : GenState} (hinv : Inv s)
    (octx : OpCtx) (pctx derivedPctx : PolyOpCtx) :
    Inv { s with octx := octx, pctx := pctx, derivedPctx := derivedPctx } :=
  { hinv with }

/-- **`Inv` is preserved by a factory add alone.** A successful
    `addFactoryFunctionWithError` touches only `C.functions`, and no `Inv` field
    mentions the function factory (`knownTypes`, `datatypes`, `rigidTypeVars` and
    everything derived from them are unchanged — `addFactory_fields`,
    `addFactory_rigid`), so the invariant survives with `reserved` untouched.

    Compose with `inv_grow_reserved` to also account for the names the step
    reserves. Shared by the function step and the `distinct` step's constants. -/
theorem inv_addFactory {s : GenState} (hinv : Inv s) {fn : LFunc CoreLParams}
    {C' : LContext CoreLParams}
    (hadd : s.C.addFactoryFunctionWithError fn = .ok C') :
    Inv { s with C := C' } := by
  obtain ⟨hkt, hdt⟩ := addFactory_fields hadd
  refine
    { ctxOk := contextOk_addFactory hinv.ctxOk hadd
      knownReserved := fun k hk => hinv.knownReserved k (by rw [hkt] at hk; exact hk)
      aliasPoolDisjoint := hinv.aliasPoolDisjoint
      aliasNamesReserved := hinv.aliasNamesReserved
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
        hinv.storedRefsReserved d (by rw [hdt] at hd; exact hd) c hc arg harg r hr }

/-- Soundness of the axiom step. -/
theorem genDeclAxiom_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAxiom (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  simp only [genDeclAxiom, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨pr, hpr, hds, hs'⟩ := h
  -- `pr = (decl, name)` from `genAxiom`; extract the bool-typed body.
  obtain ⟨a, hdecl_eq, htyped⟩ := genAxiom_exprTyped (C := s.C) (Γ := s.Γ) hpr
  subst hds hs'
  refine ⟨?_, inv_cons_reserved hinv _⟩
  -- `ds = [pr.fst] = [.ax a .empty]`.
  rw [hdecl_eq]
  exact DeclsHasType'.cons _ _ _ _ _ _ _ _
    (DeclHasType'.ax s.C s.Γ a .empty htyped) (DeclsHasType'.nil _ _)

/-! ### The constants a `distinct` ranges over

The `distinct` step emits one 0-ary constant per element before the `distinct`
itself. Each constant is an ordinary `.func` declaration, so its
`DeclHasType'.func` premises are discharged exactly as the function step's are —
only far more cheaply, since a constant is body-less, measure-less and
`typeArgs`-free. -/

/-- A generated constant is non-recursive: `constantFunc` leaves `isRecursive` at
    its `false` default. -/
theorem constantFunc_nonrec (c : String) (τ : LMonoTy) :
    ¬ (constantFunc c τ).isRecursive := by
  simp [constantFunc]

/-- A generated constant is well-typed for *any* `C`/`Γ`, provided its type is
    ground. `inputs`/`typeArgs` are empty (so the `Nodup` fields are trivial and the
    signature is just `τ`), and `body`/`measure` are `none` (so the two expression
    obligations are vacuous). Groundness is what `noUndeclaredVars` needs: a
    constant declares no type arguments, so `freeVars τ ⊆ typeArgs = []`. -/
theorem constantFunc_hasTypeA {C : LContext CoreLParams} {Γ : TContext Unit}
    {c : String} {τ : LMonoTy} (hτ : LMonoTy.freeVars τ = [])
    -- Upstream's `signatureWellKinded` field; the constant's only signature type is `τ`.
    (hwk : C.WellKindedTy τ) :
    FuncHasTypeA C Γ (constantFunc c τ) := by
  refine
    { inputsNodup := by simp [constantFunc, ListMap.keys]
      typeArgsNodup := by simp [constantFunc]
      noUndeclaredVars := ?_
      signatureWellKinded := ?_
      bodyTyped := by intro body hb; simp [constantFunc] at hb
      measureTyped := by intro m hm _; simp [constantFunc] at hm }
  · intro v hv
    simp only [constantFunc, ListMap.values, LMonoTy.mkArrow'_nil, hτ] at hv
    exact absurd hv (by simp)
  · -- signatureWellKinded: `tyCompat` is equality here, and the only signature type is `τ`.
    intro ty hty
    refine ⟨ty, rfl, ?_⟩
    simp only [constantFunc, ListMap.values, List.mem_singleton] at hty
    rw [hty]; exact hwk

/-- **The constants are well-typed and extend the context.** A successful
    `addConstants` run yields a `DeclsHasTypeA` derivation from `C` to the grown
    `C'`, leaving `Γ` alone. Induction on the name list, one `DeclHasType'.func` per
    constant with `FactoryExtendedBy` from the gated add. -/
theorem addConstants_sound (P : Program) {Γ : TContext Unit} {τ : LMonoTy}
    (hτ : LMonoTy.freeVars τ = [])
 :
    ∀ (names : List String) (C C' : LContext CoreLParams) (ds : List Decl),
      -- Upstream's `signatureWellKinded`: the constants all carry the same type `τ`, and
      -- adding factory functions never touches `knownTypes`, so it survives the run.
      C.WellKindedTy τ →
      addConstants C τ names = some (C', ds) → DeclsHasTypeA P C Γ ds C' Γ := by
  intro names
  induction names with
  | nil =>
    intro C C' ds _ h
    simp only [addConstants, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact DeclsHasType'.nil _ _
  | cons c cs ih =>
    intro C C' ds hwk h
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
        -- Adding a factory function leaves `knownTypes` alone, so `WellKindedTy` survives.
        have hwk₁ : C₁.WellKindedTy τ := by
          unfold LContext.WellKindedTy at hwk ⊢
          rw [(addFactory_fields hadd).1]; exact hwk
        exact DeclsHasType'.cons _ _ _ _ _ _ _ _
          (DeclHasType'.func C C₁ Γ (constantFunc c τ) .empty
            (constantFunc_nonrec c τ) (constantFunc_hasTypeA hτ hwk)
            (factoryExtendedBy_of_addFactory hadd))
          (ih C₁ C₂ ds' hwk₁ hrest)

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
    simp only [addConstants] at h
    cases hadd : s.C.addFactoryFunctionWithError (constantFunc c τ).toLFunc with
    | error e => simp [hadd] at h
    | ok C₁ =>
      simp only [hadd] at h
      cases hrest : addConstants C₁ τ cs with
      | none => simp [hrest] at h
      | some pr =>
        obtain ⟨C₂, ds'⟩ := pr
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        -- Add `c`, then recurse from the grown state (whose `.C` is `C₁`).
        exact ih (s := { s with C := C₁ }) (inv_addFactory hinv hadd) hrest

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
        obtain ⟨_, rfl⟩ := h
        have hcons : declNames (mkConstantDecl c τ :: ds') = c :: declNames ds' := by
          simp [declNames, mkConstantDecl, constantFunc, Decl.names, Decl.name]
        rw [hcons, ih C₁ C₂ ds' hrest]

/-- Soundness of the distinct step: the emitted constants extend `C` and are
    well-typed, and the `distinct` over them is well-typed by
    `distinctElems_typed`. On a factory clash nothing is emitted and the state is
    unchanged. -/
theorem genDeclDistinct_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclDistinct (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  simp only [genDeclDistinct, mem_support_bind_iff] at h
  obtain ⟨⟨nm, τ, constNames⟩, hparts, hmatch⟩ := h
  have hτ : LMonoTy.freeVars τ = [] := genDistinctAssertion_ground hparts
  -- The group's type comes from `genNonRecursiveArgTy`, so it is well-kinded in `s.C` by `ctxOk`.
  have hτwk : s.C.WellKindedTy τ := by
    simp only [genDistinctAssertion, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hparts
    obtain ⟨_nm, _hnm, τ', hτ', _k, _hk, _cs, _hcs, _, hτ_eq, _⟩ := hparts
    exact hτ_eq ▸ wellKindedTy_of_genNonRecursiveArgTy hinv.ctxOk hτ'
  cases hadd : addConstants s.C τ constNames with
  | none =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsHasType'.nil _ _, hinv⟩
  | some pr =>
    obtain ⟨C', constDecls⟩ := pr
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    refine ⟨?_, ?_⟩
    · -- constants (C → C'), then the `distinct` (C' → C').
      refine declsHasType_append
        (addConstants_sound P hτ constNames s.C C' constDecls hτwk hadd) ?_
      exact DeclsHasType'.cons _ _ _ _ _ _ _ _
        (DeclHasType'.distinct C' s.Γ ⟨nm, ()⟩ (distinctElems τ constNames) .empty
          distinctElems_typed)
        (DeclsHasType'.nil _ _)
    · -- `C` grew by the constants' factory entries; `reserved` by their names plus `nm`.
      have := inv_grow_reserved (s := { s with C := C' })
        (addConstants_inv constNames hinv hadd) (constNames ++ [nm])
      simpa using this

/-! ## Per-declaration soundness: functions

The function step generates a function via `genFunction` (sound for any `C`/`Γ`),
renames it to a globally fresh name (rename preserves `FuncHasType'`, which does
not constrain the name), and gates on `addFactoryFunctionWithError`. Support
membership on the `.ok` branch gives `FactoryExtendedBy` (bridge lemma). -/

/-- `FuncHasType'` (annotated) is invariant under renaming the function: no field
    mentions the name. -/
theorem funcHasTypeA_rename {C : LContext CoreLParams} {Γ : TContext Unit}
    {func : Function} {nm : CoreLParams.Identifier}
    (h : FuncHasTypeA C Γ func) : FuncHasTypeA C Γ { func with name := nm } :=
  { inputsNodup := h.inputsNodup
    typeArgsNodup := h.typeArgsNodup
    noUndeclaredVars := h.noUndeclaredVars
    signatureWellKinded := h.signatureWellKinded
    bodyTyped := h.bodyTyped
    measureTyped := h.measureTyped }

theorem genDeclFunction_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclFunction (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  simp only [genDeclFunction, mem_support_bind_iff] at h
  obtain ⟨func₀, hfunc₀, nm, hnm, hmatch⟩ := h
  -- The renamed function.
  let func : Function := { func₀ with name := ⟨nm, ()⟩ }
  -- It is well-typed for any `C`/`Γ` (rename-invariance of `genFunction_sound`).
  have hwt : FuncHasTypeA s.C s.Γ func :=
    funcHasTypeA_rename
      (StrataGenerators.Function.genFunction_sound [] s.octx b.funcDepth s.C s.Γ
        s.derivedPctx (simpleTyArities_of_inv hinv) func₀ hfunc₀)
  -- Non-recursive: `genFunction` leaves `isRecursive` at its `false` default.
  have hnonrec : ¬ func.isRecursive := by
    -- `func.isRecursive = func₀.isRecursive`; extract from `genFunction`'s support.
    simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff] at hfunc₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hf₀⟩ := hfunc₀
    show ¬ func₀.isRecursive
    subst hf₀
    simp
  -- Case on the gate.
  cases hadd : s.C.addFactoryFunctionWithError func.toLFunc with
  | error e =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsHasType'.nil _ _, hinv⟩
  | ok C' =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    have hext : FactoryExtendedBy s.C C' [func.toLFunc] := factoryExtendedBy_of_addFactory hadd
    refine ⟨?_, ?_⟩
    · -- `DeclHasType'.func` with the gated `FactoryExtendedBy`.
      exact DeclsHasType'.cons _ _ _ _ _ _ _ _
        (DeclHasType'.func s.C C' s.Γ func .empty hnonrec hwt hext)
        (DeclsHasType'.nil _ _)
    · -- `Inv` preserved: `functions` changed (`inv_addFactory`), one reserved name
      -- (`inv_grow_reserved` at `[nm]`), and the operator contexts grew with the
      -- function just declared, which no `Inv` field mentions (`inv_setOpCtxs`).
      have := inv_grow_reserved (s := { s with C := C' }) (inv_addFactory hinv hadd) [nm]
      simpa using inv_setOpCtxs this _ _ _

/-! ## Per-declaration soundness: abstract types

The abstract-type step draws a fresh name, gates on `addKnownTypeWithError`, and
(on success) grows the context's known types and the referenceable pool. -/

theorem genDeclAbstract_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclAbstract (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  simp only [genDeclAbstract, genAbstractType, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨pr, ⟨nm, hnm, ar, _har, hpr⟩, hmatch⟩ := h
  subst hpr
  -- Freshness of the drawn name.
  have hnm_fresh : nm ∉ s.reserved := DatatypeGen.genFreshName_fresh s.reserved nm hnm
  simp only at hmatch
  -- Case on the gate.
  cases hadd : s.C.addKnownTypeWithError { name := nm, metadata := ar } default with
  | error e =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsHasType'.nil _ _, hinv⟩
  | ok C' =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    refine ⟨?_, ?_⟩
    · -- `DeclHasType'.type_con` with the gated `.ok`.
      -- `mkAbstractTypeDecl nm ar = .type (.con {name:=nm, params := replicate ar "_"}) .empty`,
      -- and `tc.numargs = (replicate ar "_").length = ar`.
      refine DeclsHasType'.cons _ _ _ _ _ _ _ _ ?_ (DeclsHasType'.nil _ _)
      have harw : ({ name := nm, params := List.replicate ar "_" } : TypeConstructor).numargs = ar := by
        simp [TypeConstructor.numargs]
      have := DeclHasType'.type_con (τ := LMonoTy) (P := P) s.C C' s.Γ
        { name := nm, params := List.replicate ar "_" } .empty
      rw [harw] at this
      exact this hadd
    · -- `Inv` preserved via `contextOk_addKnownType`, growing the pool.
      obtain ⟨hkt, hdt⟩ := addKnownType_fields hadd
      -- `s' = s.addAbstract nm ar C'`.
      simp only [GenState.addAbstract]
      refine
        { ctxOk := ?_
          knownReserved := ?_
          aliasPoolDisjoint := ?_
          aliasNamesReserved := ?_
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
          storedRefsReserved := ?_ }
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
      · -- alias-pool disjointness: the pool grew by `nm`; existing aliases still
        -- avoid it because `nm ∉ reserved` while every alias name *is* reserved.
        intro a ha
        obtain ⟨hb1, hb2, hb3⟩ := hinv.aliasPoolDisjoint a ha
        have hane : a.name ≠ nm := fun heq => hnm_fresh (heq ▸ hinv.aliasNamesReserved a ha)
        by_cases har0 : ar = 0
        · subst har0
          simp only [if_pos]
          refine ⟨?_, hb2, hb3⟩
          intro hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hane rfl
          · exact hb1 hmem
        · simp only [if_neg har0]
          refine ⟨hb1, ?_, hb3⟩
          intro hmem
          simp only [List.map_cons, List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · exact hane heq
          · exact hb2 hmem
      · -- alias names still reserved (reserved only grew).
        intro a ha; exact List.mem_cons_of_mem _ (hinv.aliasNamesReserved a ha)
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
        -- `"arrow"` is reserved — so `nm ≠ "arrow"`.
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
against `initialReserved`. No permutation reasoning is needed — the rank-based
generator emits its datatypes without a shuffle pass. -/

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
    appear anywhere in the stored datatypes — the side condition
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
  -- `tyConsNeArrow`, pool ones because they are reserved while `"arrow"`… is too —
  -- so instead use that a pool name is a *datatype* of `C` and `"arrow"` is not.
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
  have hnm_fresh : nm ∉ s.reserved := DatatypeGen.genFreshName_fresh s.reserved nm hnm
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
    s.reserved` — hence fresh, pairwise distinct, and different from `nm`. On a
    factory clash nothing is emitted (`namesStep_nil`). -/
theorem genDeclDistinct_names {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclDistinct (G := SetGen.Set) s b)) :
    NamesStep s ds s' := by
  simp only [genDeclDistinct, mem_support_bind_iff] at h
  obtain ⟨⟨nm, τ, cs⟩, hparts, hmatch⟩ := h
  obtain ⟨hnm_fresh, hcs_fresh, hcs_nodup⟩ := genDistinctAssertion_names hparts
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
  simp only [genDeclAlias, genAlias, mem_support_bind_iff, mem_support_pure_iff,
    Prod.mk.injEq] at h
  obtain ⟨pr, ⟨nm, hnm, k, _hk, tps, _htps, body, _hbody, hpreq⟩, hds, hs'⟩ := h
  subst hpreq
  simp only at hds hs'
  subst hds hs'
  have hnm_fresh : nm ∉ s.reserved := DatatypeGen.genFreshName_fresh s.reserved nm hnm
  have hdn : declNames [mkAliasDecl nm body] = [nm] := by
    simp [declNames, mkAliasDecl, Decl.names, TypeDecl.names]
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
  have hnm_fresh : nm ∉ s.reserved := DatatypeGen.genFreshName_fresh s.reserved nm hnm
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
  have hnm_fresh : nm ∉ s.reserved := DatatypeGen.genFreshName_fresh s.reserved nm hnm
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
  have hnm_fresh : nm ∉ s.reserved := DatatypeGen.genFreshName_fresh s.reserved nm hnm
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

/-- The initial fold state satisfies `Inv`. -/
theorem inv_initState : Inv initState := by
  -- The seed reserved set.
  have hseed : initState.reserved =
      DatatypeGen.initialReserved DatatypeGen.defaultBaseTypes DatatypeGen.defaultTyCons
        Core.KnownTypes.keywords := rfl
  refine
    { ctxOk := ?_
      knownReserved := ?_
      aliasPoolDisjoint := ?_
      aliasNamesReserved := ?_
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
      storedRefsReserved := ?_ }
  · -- `ContextOk coreContext … initState.reserved` from `defaultContextOk`, monotone.
    rw [hseed]
    exact contextOk_reserved_mono DatatypeGen.defaultContextOk keywords_sub_initReserved
  · -- `coreContext`'s known types are Core's keywords, all in the seed.
    intro k hk
    rw [hseed]
    -- `initState.C = coreContext`, `coreContext.knownTypes.keywords = Core.KnownTypes.keywords`.
    exact keywords_sub_initReserved hk
  · -- No aliases initially.
    intro a ha; simp [initState] at ha
  · intro a ha; simp [initState] at ha
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
  · -- `coreContext` holds no datatypes, so this is vacuous.
    intro n hn
    simp [initState, DatatypeGen.coreContext, TypeFactory.allTypeNames,
      TypeFactory.allDatatypes] at hn
  · -- `coreContext` holds no datatypes, so there are no stored references either.
    intro d hd
    simp [initState, DatatypeGen.coreContext, TypeFactory.allDatatypes] at hd

end ProgramGen
