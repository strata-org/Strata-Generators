import StrataGenerators.DatatypeGenProofs
import StrataGenerators.HasTypeAGen
import Std.Data.HashMap.Lemmas

open Lambda Core DatatypeGen

namespace ProgramGen

/-!
# `ContextOk`-preservation under `LContext.addMutualBlock`

The whole-program generator (`ProgramGen.genDeclsFold`) grows its ambient
`LContext CoreLParams` one declaration at a time. To reuse the datatype-generator
soundness result (`genMutuallyRecursiveDatatypes_MutualADTWF`, stated against a
`ContextOk` context), the fold must maintain
`DatatypeGen.ContextOk C defaultBaseTypes defaultTyCons R` across a datatype step,
which adds a mutual block via `LContext.addMutualBlock`.

`contextOk_addMutualBlock` discharges that. Adding a block grows `knownTypes` (by
the block's names), `datatypes` (by the block) and `functions` (which no
`ContextOk` field mentions). The reserved set `R` grows to
`block.map (·.name) ++ R` — matching the fold, which prepends the freshly drawn
block names to its reserved list.

Two field-effect helpers are exported for the fold's own reserved/`getNames`
bookkeeping:

* `addMutualBlock_datatypes` — `C'.datatypes = C.datatypes.push block`;
* `addMutualBlock_knownTypes` — a `keywords`-membership characterization.
-/

/-! ## `knownTypes` insertion facts

`KnownTypes = Std.HashMap String Nat` and `keywords = HashMap.keys`. A successful
`addWithError`/`add` replaces the map by `insertIfNew name arity`, so membership
in `keywords` grows by exactly the new key. -/

/-- A successful `Identifiers.addWithError` is an `insertIfNew` of the key. -/
theorem addWithError_eq_insertIfNew {m m' : Identifiers Nat} {x : Identifier Nat}
    {f : Strata.Message} (h : m.addWithError x f = .ok m') :
    m' = m.insertIfNew x.name x.metadata := by
  unfold Identifiers.addWithError at h
  have hsnd := Std.HashMap.containsThenInsertIfNew_snd (m := m) (k := x.name) (v := x.metadata)
  rcases hc : m.containsThenInsertIfNew x.name x.metadata with ⟨b, m''⟩
  rw [hc] at h hsnd
  simp only at h hsnd
  cases b with
  | true => simp at h
  | false => simp only [Bool.false_eq_true, if_false] at h; injection h with h; rw [← h, hsnd]

/-- `keywords`-membership after `insertIfNew`: the resulting keys are the old
    keys plus the inserted name. -/
theorem mem_keys_insertIfNew {m : Identifiers Nat} {nm : String} {ar : Nat} {n : String} :
    n ∈ (m.insertIfNew nm ar).keys ↔ nm = n ∨ n ∈ m.keys := by
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_insertIfNew, Std.HashMap.mem_keys]
  simp only [beq_iff_eq]

/-- `insertIfNew` never overwrites, therefore an existing binding survives it. This is the
    value-level counterpart of `mem_keys_insertIfNew`, needed by the *arity* fields of
    `ContextOk`, which speak about `knownTypes[·]?` and not only about its key set. -/
theorem getElem?_insertIfNew_of_getElem? {m : Identifiers Nat} {nm : String} {ar : Nat}
    {k : String} {v : Nat} (h : m[k]? = some v) : (m.insertIfNew nm ar)[k]? = some v := by
  rw [Std.HashMap.getElem?_insertIfNew]
  split
  · -- `nm == k` and `nm ∉ m`, but `h` puts `k` — hence `nm` — in `m`.
    rename_i hc
    refine absurd ?_ hc.2
    rw [(by simpa using hc.1 : nm = k)]
    exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [h]; rfl)
  · exact h

/-- Folding `Identifiers.add`-of-`toKnownType` over `block` preserves every binding that is
    already present, because each step is an `insertIfNew`. -/
theorem foldlM_add_toKnownType_getElem? {m m' : Identifiers Nat} {block : MutualDatatype Unit}
    (h : block.foldlM (fun ks d => Identifiers.add ks (LDatatype.toKnownType d)) m = .ok m')
    {k : String} {v : Nat} (hk : m[k]? = some v) : m'[k]? = some v := by
  induction block generalizing m with
  | nil => simp only [List.foldlM_nil] at h; injection h with h; subst h; exact hk
  | cons d tl ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases hstep : Identifiers.add m (LDatatype.toKnownType d) with
    | error e => rw [hstep] at h; simp at h
    | ok m1 =>
      rw [hstep] at h
      simp only at h
      have hm1 : m1 = m.insertIfNew (LDatatype.toKnownType d).name
          (LDatatype.toKnownType d).metadata :=
        addWithError_eq_insertIfNew (by unfold Identifiers.add at hstep; exact hstep)
      exact ih h (hm1 ▸ getElem?_insertIfNew_of_getElem? hk)

/-- Folding `Identifiers.add`-of-`toKnownType` over `block` grows the key set by
    exactly the block's names. Proven by induction over the fold, using
    `addWithError_eq_insertIfNew` for the single-step key growth. -/
theorem foldlM_add_toKnownType_keys {m m' : Identifiers Nat} {block : MutualDatatype Unit}
    (h : block.foldlM (fun ks d => Identifiers.add ks (LDatatype.toKnownType d)) m = .ok m')
    (n : String) :
    n ∈ m'.keys ↔ n ∈ block.map (·.name) ∨ n ∈ m.keys := by
  induction block generalizing m with
  | nil =>
    simp only [List.foldlM_nil] at h
    injection h with h; subst h
    simp only [List.map_nil, List.not_mem_nil, false_or]
  | cons d tl ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases hstep : Identifiers.add m (LDatatype.toKnownType d) with
    | error e => rw [hstep] at h; simp at h
    | ok m1 =>
      rw [hstep] at h
      simp only at h
      have hm1 : m1 = m.insertIfNew (LDatatype.toKnownType d).name (LDatatype.toKnownType d).metadata :=
        addWithError_eq_insertIfNew (by unfold Identifiers.add at hstep; exact hstep)
      have hrec := ih h
      rw [hrec, hm1, mem_keys_insertIfNew]
      simp only [List.map_cons, List.mem_cons, LDatatype.toKnownType]
      constructor
      · rintro (hb | (rfl | hm))
        · exact Or.inl (Or.inr hb)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr hm
      · rintro ((rfl | hb) | hm)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hb
        · exact Or.inr (Or.inr hm)

/-! ## Field-effect helpers for `addMutualBlock` (exported)

`LContext.addMutualBlock` is an `Except` do-block that, on success, produces
`{C with datatypes := ds, functions := fs, knownTypes := ks}` where
`ds = C.datatypes.push block` and `ks` is the `toKnownType`-fold over the block.
We extract the two fields `ContextOk` reasons about by casing on the inner
`.ok`s. -/

/-- On success, `TypeFactory.addMutualBlock` is exactly `push`. -/
theorem typeFactory_addMutualBlock_eq_push {t t' : @TypeFactory Unit}
    {block : MutualDatatype Unit} {kw : Std.HashMap String Nat}
    (h : t.addMutualBlock block kw = .ok t') :
    t' = t.push block := by
  unfold TypeFactory.addMutualBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat (split at h <;> try contradiction)
  injection h with h; exact h.symm

/-- **Datatype field-effect of `addMutualBlock`.** On success the datatype factory
    is exactly `C.datatypes.push block`. -/
theorem addMutualBlock_datatypes {C C' : LContext CoreLParams} {block : MutualDatatype Unit}
    {i₁ : DecidableEq CoreLParams.IDMeta} {i₂ : Inhabited CoreLParams.IDMeta}
    {i₃ : Inhabited CoreLParams.Metadata} {i₄ : Std.ToFormat CoreLParams.IDMeta}
    (h : @LContext.addMutualBlock CoreLParams i₁ i₂ i₃ i₄ C block = .ok C') :
    C'.datatypes = C.datatypes.push block := by
  unfold LContext.addMutualBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat (split at h <;> try contradiction)
  injection h with h; subst h
  -- Goal reduces to `v = C.datatypes.push block` where the inner
  -- `TypeFactory.addMutualBlock … = .ok v` hypothesis is in scope.
  apply typeFactory_addMutualBlock_eq_push
  assumption

/-- **Known-type field-effect of `addMutualBlock`.** On success the known-type key
    set grows by exactly the block's names. -/
theorem addMutualBlock_knownTypes {C C' : LContext CoreLParams} {block : MutualDatatype Unit}
    {i₁ : DecidableEq CoreLParams.IDMeta} {i₂ : Inhabited CoreLParams.IDMeta}
    {i₃ : Inhabited CoreLParams.Metadata} {i₄ : Std.ToFormat CoreLParams.IDMeta}
    (h : @LContext.addMutualBlock CoreLParams i₁ i₂ i₃ i₄ C block = .ok C')
    (n : String) :
    n ∈ C'.knownTypes.keywords ↔ n ∈ block.map (·.name) ∨ n ∈ C.knownTypes.keywords := by
  unfold LContext.addMutualBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat (split at h <;> try contradiction)
  injection h with h; subst h
  simp only [KnownTypes.keywords]
  apply foldlM_add_toKnownType_keys
  assumption

/-- **Known-type value-effect of `addMutualBlock`.** On success every arity already
    registered in `C.knownTypes` is still registered, at the same value: the block's names
    are added with `insertIfNew`, which never overwrites. -/
theorem addMutualBlock_knownTypes_getElem? {C C' : LContext CoreLParams}
    {block : MutualDatatype Unit}
    {i₁ : DecidableEq CoreLParams.IDMeta} {i₂ : Inhabited CoreLParams.IDMeta}
    {i₃ : Inhabited CoreLParams.Metadata} {i₄ : Std.ToFormat CoreLParams.IDMeta}
    (h : @LContext.addMutualBlock CoreLParams i₁ i₂ i₃ i₄ C block = .ok C')
    {k : String} {v : Nat} (hk : C.knownTypes[k]? = some v) : C'.knownTypes[k]? = some v := by
  unfold LContext.addMutualBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat (split at h <;> try contradiction)
  injection h with h; subst h
  apply foldlM_add_toKnownType_getElem? (block := block) (hk := hk)
  assumption

/-! ## Membership of the default type names in `initialReserved`

Every default type name (`defaultBaseTypes`, `defaultTyCons` names, `"arrow"`)
lies in `initialReserved defaultBaseTypes defaultTyCons R`. Combined with the
freshness hypothesis (block names avoid `initialReserved`), this shows a default
type name is never a block name — the fact `getType_push_other` needs to keep the
"external" fields true. -/

theorem base_mem_initialReserved {b : String} {baseTypes : List String}
    {tyCons : List KnownTyCon} {R : List String} (hb : b ∈ baseTypes) :
    b ∈ initialReserved baseTypes tyCons R := by
  -- `initialReserved = "arrow" :: ((reservedKeywordsList ++ baseTypes) ++ …) ++ R`.
  unfold initialReserved
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_append_right _ hb

theorem tyCon_mem_initialReserved {kc : KnownTyCon} {baseTypes : List String}
    {tyCons : List KnownTyCon} {R : List String} (hkc : kc ∈ tyCons) :
    kc.1 ∈ initialReserved baseTypes tyCons R := by
  unfold initialReserved
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.mpr ⟨kc, hkc, rfl⟩)

theorem arrow_mem_initialReserved {baseTypes : List String}
    {tyCons : List KnownTyCon} {R : List String} :
    "arrow" ∈ initialReserved baseTypes tyCons R := by
  unfold initialReserved
  exact List.mem_cons_self ..

/-! ## `SimpleTyArities` preservation

The `init` rules and `signatureWellKinded` need the ambient context to register the eight
type constructors at their own arities. The fold only *grows* `knownTypes` (with
`insertIfNew`, which never overwrites). Therefore each step keeps the property. -/

/-- `coreContext` registers each of the eight type constructors at its own arity. Discharged by
    `native_decide` on `Core.KnownTypes`, like `defaultContextOk`. -/
theorem coreContextSimpleTyArities : SimpleTyArities DatatypeGen.coreContext := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (show Core.KnownTypes[_]? = some _; native_decide)

/-- `SimpleTyArities` survives an `insertIfNew` on `knownTypes`: the eight bindings it
    asserts are already present, and `insertIfNew` never overwrites. -/
theorem simpleTyArities_of_insertIfNew {C C' : LContext CoreLParams} {nm : String} {ar : Nat}
    (h : C'.knownTypes = C.knownTypes.insertIfNew nm ar) (hC : SimpleTyArities C) :
    SimpleTyArities C' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h]; exact getElem?_insertIfNew_of_getElem? hC.bool
  · rw [h]; exact getElem?_insertIfNew_of_getElem? hC.int
  · rw [h]; exact getElem?_insertIfNew_of_getElem? hC.string
  · rw [h]; exact getElem?_insertIfNew_of_getElem? hC.real
  · rw [h]; exact getElem?_insertIfNew_of_getElem? hC.regex
  · rw [h]; exact getElem?_insertIfNew_of_getElem? hC.arrow
  · rw [h]; exact getElem?_insertIfNew_of_getElem? hC.map
  · rw [h]; exact getElem?_insertIfNew_of_getElem? hC.seq

/-- `SimpleTyArities` survives `addMutualBlock`: the block's names are added with
    `insertIfNew`, which never overwrites. -/
theorem simpleTyArities_of_addMutualBlock {C C' : LContext CoreLParams}
    {block : MutualDatatype Unit}
    {i₁ : DecidableEq CoreLParams.IDMeta} {i₂ : Inhabited CoreLParams.IDMeta}
    {i₃ : Inhabited CoreLParams.Metadata} {i₄ : Std.ToFormat CoreLParams.IDMeta}
    (h : @LContext.addMutualBlock CoreLParams i₁ i₂ i₃ i₄ C block = .ok C')
    (hC : SimpleTyArities C) : SimpleTyArities C' :=
  ⟨addMutualBlock_knownTypes_getElem? h hC.bool,
   addMutualBlock_knownTypes_getElem? h hC.int,
   addMutualBlock_knownTypes_getElem? h hC.string,
   addMutualBlock_knownTypes_getElem? h hC.real,
   addMutualBlock_knownTypes_getElem? h hC.regex,
   addMutualBlock_knownTypes_getElem? h hC.arrow,
   addMutualBlock_knownTypes_getElem? h hC.map,
   addMutualBlock_knownTypes_getElem? h hC.seq⟩

/-! ## The preservation lemma -/

/-- **Preservation under `addMutualBlock`.** Given `ContextOk C … R`, a successful
    `C.addMutualBlock block = .ok C'`, and a freshness hypothesis that every block
    name avoids `initialReserved defaultBaseTypes defaultTyCons R` (the generator
    draws block names fresh against the reserved set, which contains
    `initialReserved`), the result satisfies `ContextOk` for the reserved set
    grown by the block names.

    * "known" fields: `knownTypes` only grows, so old memberships survive
      (`addMutualBlock_knownTypes`).
    * `knownTypes_reserved` / `datatypes_reserved`: block names are in the grown
      reserved set by construction; old keys/names are in `R ⊆` grown set.
    * "external" fields: `datatypes = C.datatypes.push block`, and a default type
      name is never a block name (freshness vs. `initialReserved`), so
      `getType_push_other` keeps it external. -/
theorem contextOk_addMutualBlock {C C' : LContext CoreLParams} {R : List String}
    {baseTypes : List String} {tyCons : List KnownTyCon}
    {block : MutualDatatype Unit}
    {i₁ : DecidableEq CoreLParams.IDMeta} {i₂ : Inhabited CoreLParams.IDMeta}
    {i₃ : Inhabited CoreLParams.Metadata} {i₄ : Std.ToFormat CoreLParams.IDMeta}
    (hctx : ContextOk C baseTypes tyCons R)
    (h : @LContext.addMutualBlock CoreLParams i₁ i₂ i₃ i₄ C block = .ok C')
    (hfresh : ∀ d ∈ block, d.name ∉ initialReserved baseTypes tyCons R) :
    ContextOk C' baseTypes tyCons (block.map (·.name) ++ R) := by
  have hdt : C'.datatypes = C.datatypes.push block := addMutualBlock_datatypes h
  have hkt := addMutualBlock_knownTypes h
  -- `initialReserved` over the grown reserved set contains the old one and the
  -- block names.
  -- `initialReserved … X = "arrow" :: (P ++ X)` for the shared prefix
  -- `P = reservedKeywordsList ++ defaultBaseTypes ++ defaultTyCons.map (·.1)`.
  have hres_mono : ∀ x, x ∈ initialReserved baseTypes tyCons R →
      x ∈ initialReserved baseTypes tyCons (block.map (·.name) ++ R) := by
    intro x hx
    unfold initialReserved at hx ⊢
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    · apply List.mem_cons_of_mem
      rcases List.mem_append.mp hx with hp | hr
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (List.mem_append_right _ hr)
  have hblk_res : ∀ n ∈ block.map (·.name),
      n ∈ initialReserved baseTypes tyCons (block.map (·.name) ++ R) := by
    intro n hn
    unfold initialReserved
    apply List.mem_cons_of_mem
    exact List.mem_append_right _ (List.mem_append_left _ hn)
  -- A default type name is never a block name: it is in `initialReserved`,
  -- which the block names avoid.
  have hnotblk : ∀ x, x ∈ initialReserved baseTypes tyCons R →
      x ∉ block.map (·.name) := by
    intro x hx hmem
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmem
    exact hfresh d hd hx
  -- The arity disjuncts transfer the same way as the "known" ones: `knownTypes` keeps every
  -- old binding (`addMutualBlock_knownTypes_getElem?`), and `allDatatypes` only grows.
  have hdt_mono : ∀ {d : LDatatype Unit}, d ∈ C.datatypes.allDatatypes →
      d ∈ C'.datatypes.allDatatypes := by
    intro d hd
    rw [hdt, allDatatypes_push]
    exact List.mem_append_left _ hd
  refine
    { base_known := ?_, tyCon_known := ?_, arrow_known := ?_,
      base_arity := ?_, tyCon_arity := ?_, arrow_arity := ?_,
      knownTypes_reserved := ?_, datatypes_reserved := ?_,
      base_external := ?_, tyCon_external := ?_, arrow_external := ?_ }
  · intro b hb
    rcases hctx.base_known b hb with hk | hd
    · exact Or.inl ((hkt b).mpr (Or.inr hk))
    · exact Or.inr (by
        rw [hdt, TypeFactory.allTypeNames, allDatatypes_push, List.map_append]
        exact List.mem_append_left _ hd)
  · intro kc hkc
    rcases hctx.tyCon_known kc hkc with hk | hd
    · exact Or.inl ((hkt kc.1).mpr (Or.inr hk))
    · exact Or.inr (by
        rw [hdt, TypeFactory.allTypeNames, allDatatypes_push, List.map_append]
        exact List.mem_append_left _ hd)
  · exact (hkt "arrow").mpr (Or.inr hctx.arrow_known)
  · intro b hb
    exact addMutualBlock_knownTypes_getElem? h (hctx.base_arity b hb)
  · intro kc hkc
    exact addMutualBlock_knownTypes_getElem? h (hctx.tyCon_arity kc hkc)
  · exact addMutualBlock_knownTypes_getElem? h hctx.arrow_arity
  · intro key hkey
    rcases (hkt key).mp hkey with hblk | hold
    · exact hblk_res key hblk
    · exact hres_mono key (hctx.knownTypes_reserved key hold)
  · intro nm hnm
    rw [hdt, TypeFactory.allTypeNames, allDatatypes_push, List.map_append, List.mem_append] at hnm
    rcases hnm with hold | hblk
    · exact hres_mono nm (hctx.datatypes_reserved nm (by
        rw [TypeFactory.allTypeNames]; exact hold))
    · exact hblk_res nm hblk
  · intro b hb
    rw [hdt]
    exact getType_push_other (hnotblk b (base_mem_initialReserved hb)) (hctx.base_external b hb)
  · intro kc hkc
    rw [hdt]
    exact getType_push_other (hnotblk kc.1 (tyCon_mem_initialReserved hkc)) (hctx.tyCon_external kc hkc)
  · rw [hdt]
    exact getType_push_other (hnotblk "arrow" arrow_mem_initialReserved) hctx.arrow_external

end ProgramGen
