import StrataGenerators.ProgramGen.Sound
import StrataGenerators.ProgramGen.ContextOkPreserve
import StrataGenerators.ProcedureHasTypeAGen
import StrataGenerators.ProgramGen.ProcSigThread

/-!
# Whole-program soundness

Combines the per-declaration soundness lemmas (`StrataGenerators.ProgramGen.Sound`)
and the `ContextOk`-preservation lemmas (`StrataGenerators.ProgramGen.ContextOkPreserve`)
into:

* `genDeclDatatype_sound` — the last per-declaration step (datatype blocks), whose
  `Inv`-preservation needs `contextOk_addMutualBlock`;
* `genDeclStep_sound` — the six-way `oneOf` dispatch;
* `genDeclsFold_sound` — the declaration fold, producing `DeclsHasTypeA` for the
  whole emitted list (for *any* enclosing program `P`);
* `genProgram_sound` — the top-level theorem: every generated program is
  `ProgramHasTypeA coreContext {} P` (soundness w.r.t. `ProgramHasType'` at the
  annotated spec), including `P.getNames.Nodup`.
-/

open Lambda RandomChoice Core Core.TypeSpec Imperative SetGen
open DatatypeGen
open StrataGenerators.Procedure StrataGenerators.Stmt

namespace ProgramGen

/-- A successful `addMutualBlock` leaves `rigidTypeVars` unchanged (it only grows
    `datatypes`/`knownTypes`/`functions`). -/
theorem addMutualBlock_rigid {C C' : LContext CoreLParams} {block : MutualDatatype Unit}
    (h : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams C block = .ok C') :
    C'.rigidTypeVars = C.rigidTypeVars := by
  unfold LContext.addMutualBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat (split at h <;> try contradiction)
  injection h with h; subst h; rfl

/-! ## Datatype per-declaration soundness -/

/-- Soundness of the datatype-block step. `MutualADTWF` comes from the invariant
    (`genDatatypeBlock_MutualADTWF`); the `= .ok C'` premise of
    `DeclHasType'.type_data` comes for free from support membership (gating); and
    `Inv` preservation uses `contextOk_addMutualBlock` with block-name freshness
    from `genDatatypeBlock_names`. -/
theorem genDeclDatatype_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclDatatype (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  simp only [genDeclDatatype, mem_support_bind_iff] at h
  obtain ⟨block, hblock, hmatch⟩ := h
  -- Well-formedness of the block (consumes `ContextOk` from `Inv`).
  have hwf : MutualADTWF s.C block := genDatatypeBlock_MutualADTWF hinv hblock
  -- Block names: Nodup and fresh against `initialReserved … s.reserved`.
  obtain ⟨hnamesNodup, hnamesFresh⟩ := genDatatypeBlock_names hblock
  -- Case on the gate (spec-native `addMutualBlock` instances, matching the generator).
  cases hadd : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams s.C block with
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
    · -- `DeclHasType'.type_data` with `MutualADTWF` and the gated `.ok` (the
      -- generator pins the spec-native `addMutualBlock` instances, so `hadd`
      -- matches the constructor directly).
      exact DeclsHasType'.cons _ _ _ _ _ _ _ _
        (DeclHasType'.type_data s.C C' s.Γ block .empty hwf hadd)
        (DeclsHasType'.nil _ _)
    · -- `Inv` preserved.
      -- Grown reserved set is `block.map (·.name) ++ s.reserved`.
      -- Block names avoid `initialReserved` over the *combined* vocabulary; the
      -- external-only reserved set is contained in it, so freshness transfers.
      have hfresh' : ∀ d ∈ block, d.name ∉
          DatatypeGen.initialReserved s.baseTypes s.tyCons s.reserved := by
        intro d hd hmem
        refine hnamesFresh d hd ?_
        simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append] at hmem ⊢
        rcases hmem with h | ((h | h) | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
        · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
        · obtain ⟨kc, hkc, hkceq⟩ := List.mem_map.mp h
          exact Or.inr (Or.inl (Or.inr
            (List.mem_map.mpr ⟨kc, List.mem_append_left _ hkc, hkceq⟩)))
        · exact Or.inr (Or.inr h)
      -- Freshness against the plain reserved set (used for the pool bookkeeping).
      have hfresh_res : ∀ d ∈ block, d.name ∉ s.reserved := by
        intro d hd hmem
        exact hfresh' d hd (by
          simp only [DatatypeGen.initialReserved, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr hmem))
      have hctx' : DatatypeGen.ContextOk C' s.baseTypes s.tyCons
          (block.map (·.name) ++ s.reserved) :=
        contextOk_addMutualBlock hinv.ctxOk hadd hfresh'
      -- knownTypes / datatypes field effects.
      have hkw := addMutualBlock_knownTypes hadd
      refine
        { ctxOk := hctx'
          knownReserved := ?_
          aliasVocabDisjoint := ?_
          aliasNamesReserved := ?_
          baseSupset := hinv.baseSupset
          tyConsSupset := hinv.tyConsSupset
          baseReserved := ?_
          tyConReserved := ?_
          arrowReserved := ?_
          typesNil := hinv.typesNil
          rigidNil := (addMutualBlock_rigid hadd).trans hinv.rigidNil
          tyConsNeArrow := hinv.tyConsNeArrow
          datatypesReserved := ?_
          dtPoolOk := ?_
          dtConsReserved := ?_
          storedRefsReserved := ?_ }
      · -- known types of `C'` reserved in the grown set.
        intro k hk
        rcases (hkw k).mp hk with hblk | hold
        · exact List.mem_append_left _ hblk
        · exact List.mem_append_right _ (hinv.knownReserved k hold)
      · -- alias-vocab disjointness unchanged (`Γ` and vocab unchanged).
        exact hinv.aliasVocabDisjoint
      · -- alias names still reserved (reserved only grew).
        intro a ha
        exact List.mem_append_right _ (hinv.aliasNamesReserved a ha)
      · intro x hx; exact List.mem_append_right _ (hinv.baseReserved x hx)
      · intro x hx; exact List.mem_append_right _ (hinv.tyConReserved x hx)
      · exact List.mem_append_right _ hinv.arrowReserved
      · -- datatypesReserved: the datatype names of `C'` are the old ones plus the
        -- block's names, and the reserved set grew by exactly the block's names.
        intro n hn
        rw [addMutualBlock_datatypes hadd, TypeFactory.allTypeNames, allDatatypes_push,
          List.map_append, List.mem_append] at hn
        rcases hn with hold | hblk
        · exact List.mem_append_right _ (hinv.datatypesReserved n
            (by rw [TypeFactory.allTypeNames]; exact hold))
        · exact List.mem_append_left _ hblk
      · -- **dtPoolOk at the grown pool (direction (4)).** The new pool is this
        -- block's datatypes followed by the old pool.
        --
        -- * `known`: `C'.datatypes = C.datatypes.push block`, so both the block's
        --   names and the old pool's names are in `allTypeNames`.
        -- * `inhab`: for the *new* entries this is exactly `hwf.inhabited` (the
        --   `MutualADTWF` field we just proved, already stated in
        --   `C.datatypes.push block`); for the *old* entries it is the previous
        --   pool's inhabitance transported across the push by `tySymInhab_push`.
        have hdt : C'.datatypes = s.C.datatypes.push block := addMutualBlock_datatypes hadd
        have hstored : DatatypeGen.StoredRefsAbsent s.C block :=
          storedRefsAbsent_of_inv hinv hfresh_res
        refine { known := ?_, inhab := ?_ }
        · intro kc hkc
          rw [hdt, TypeFactory.allTypeNames, allDatatypes_push, List.map_append]
          rcases List.mem_append.mp hkc with hnew | hold
          · -- A new pool entry's name is a block name.
            obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hnew
            exact List.mem_append_right _ (List.mem_map.mpr ⟨d, hd, by rw [← hdeq]⟩)
          · exact List.mem_append_left _ (hinv.dtPoolOk.known kc hold)
        · intro kc hkc
          rw [hdt]
          rcases List.mem_append.mp hkc with hnew | hold
          · -- New entry: `MutualADTWF.inhabited`.
            obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hnew
            rw [← hdeq]
            exact hwf.inhabited d hd
          · -- Old entry: transport across the push. Its name is reserved
            -- (`dtConsReserved`) while block names are fresh, so it is not a block name.
            refine DatatypeGen.tySymInhab_push hstored ?_ (hinv.dtPoolOk.inhab kc hold)
            intro hmem
            obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hmem
            exact hfresh_res d hd
              (hdeq ▸ hinv.dtConsReserved kc.1 (List.mem_map.mpr ⟨kc, hold, rfl⟩))
      · -- dtConsReserved: new entries are block names (just reserved); old ones grew.
        intro x hx
        obtain ⟨kc, hkc, hkceq⟩ := List.mem_map.mp hx
        rcases List.mem_append.mp hkc with hnew | hold
        · -- A new entry's name is one of the block's names.
          obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hnew
          refine List.mem_append_left _ (List.mem_map.mpr ⟨d, hd, ?_⟩)
          rw [← hkceq, ← hdeq]
        · exact List.mem_append_right _
            (hinv.dtConsReserved x (List.mem_map.mpr ⟨kc, hold, hkceq⟩))
      · -- storedRefsReserved: the stored datatypes of `C'` are the old ones plus the
        -- block. Old references were reserved; the block's own references are
        -- confined to the vocabulary ∪ block names ∪ {"arrow"}, all reserved.
        intro d hd c hc arg harg r hr
        rw [addMutualBlock_datatypes hadd, allDatatypes_push, List.mem_append] at hd
        rcases hd with hold | hblk
        · exact List.mem_append_right _ (hinv.storedRefsReserved d hold c hc arg harg r hr)
        · -- A reference of a freshly generated block.
          rcases DatatypeGen.genMutuallyRecursiveDatatypes_refsKnown hblock d hblk c hc
            arg harg r hr with hbt | htc | hblkn | harr
          · exact List.mem_append_right _ (hinv.baseReserved r hbt)
          · obtain ⟨kc, hkc, hkceq⟩ := List.mem_map.mp htc
            rcases List.mem_append.mp hkc with hext | hdtc
            · exact List.mem_append_right _
                (hinv.tyConReserved r (List.mem_map.mpr ⟨kc, hext, hkceq⟩))
            · exact List.mem_append_right _
                (hinv.dtConsReserved r (List.mem_map.mpr ⟨kc, hdtc, hkceq⟩))
          · exact List.mem_append_left _ hblkn
          · exact List.mem_append_right _ (harr ▸ hinv.arrowReserved)

/-! ## Procedure per-declaration soundness -/

/-- `ProcHasTypeA` is invariant under renaming the procedure's header name: no
    `ProcHasType'` field mentions `proc.header.name` (they read
    `inputs`/`outputs`/`typeArgs`/`getInoutParams`, `body`, and `spec`, all
    preserved by the rename). -/
theorem procHasTypeA_rename {P : Program} {C : LContext CoreLParams} {Γ : TContext Unit}
    {proc : Procedure} {nm : CoreIdent}
    (h : ProcHasTypeA P C Γ proc) :
    ProcHasTypeA P C Γ { proc with header := { proc.header with name := nm } } :=
  { inputsNodup := h.inputsNodup
    outputsNodup := h.outputsNodup
    typeArgsNodup := h.typeArgsNodup
    noUndeclaredVars := h.noUndeclaredVars
    modRights := h.modRights
    preconditionsTyped := h.preconditionsTyped
    postconditionsTyped := h.postconditionsTyped
    bodyTyped := h.bodyTyped }

/-- Soundness of the procedure step. The body is generated under the *real*
    ambient `s.C`/`s.Γ` (Option B), so `genProcedure_sound_ambient` yields
    `ProcHasTypeA P s.C s.Γ proc₀` directly — the `⊆`/`Γ.types = []` side
    conditions are discharged by the fold invariant (`rigidNil`/`typesNil`).
    Renaming to a fresh name preserves it (`procHasTypeA_rename`); the `.proc`
    constructor leaves `C`/`Γ` unchanged, so `Inv` survives (only `reserved`
    grows). -/
theorem genDeclProcedure_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hProcs : ProcSigCorresponds s.procs P)
    {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclProcedure (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨proc₀, hproc₀, nm, hnm, hds, hs'⟩ := h
  subst hds hs'
  -- Body well-typed at the ambient context (Option B), rigid side condition from
  -- `rigidNil`. The body may now contain `call`s to `s.procs`, so this consumes
  -- `hProcs` rather than the vacuous `ProcSigCorresponds [] P`.
  have hpt : ProcHasTypeA P s.C s.Γ proc₀ :=
    genProcedure_sound_ambient P s.octx s.procs hProcs b.procSize b.procLen s.C s.Γ
      hinv.typesNil proc₀ s.derivedPctx hproc₀
      (by rw [hinv.rigidNil]; exact List.nil_subset _)
  -- Rename to the fresh name; `ProcHasTypeA` is name-invariant.
  have hpt' : ProcHasTypeA P s.C s.Γ
      { proc₀ with header := { proc₀.header with name := ⟨nm, ()⟩ } } :=
    procHasTypeA_rename hpt
  refine ⟨?_, ?_⟩
  · exact DeclsHasType'.cons _ _ _ _ _ _ _ _
      (DeclHasType'.proc s.C s.Γ _ .empty hpt') (DeclsHasType'.nil _ _)
  · -- `Inv` ignores `procs` (it constrains only `C`/`Γ`/vocabulary/reserved), and
    -- the step changes `procs` and `reserved` only.
    exact inv_cons_reserved_procs hinv _ _

/-! ## The declaration-step dispatch -/

/-- Soundness of one declaration step: whichever kind `oneOf` selects, the emitted
    declarations are `DeclsHasTypeA` from `s` to `s'`, and `Inv` is preserved. -/
theorem genDeclStep_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hProcs : ProcSigCorresponds s.procs P)
    {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  -- `genDeclStep` is a weighted `frequency`; support inversion yields a
  -- `(weight, generator)` pair, so each branch equation pins both components.
  simp only [genDeclStep, mem_support_frequency_iff, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  obtain ⟨w, g, hg, _hw, hmem⟩ := h
  rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact genDeclAbstract_sound P hinv hmem
  · exact genDeclAlias_sound P hinv hmem
  · exact genDeclAxiom_sound P hinv hmem
  · exact genDeclDistinct_sound P hinv hmem
  · exact genDeclDatatype_sound P hinv hmem
  · exact genDeclFunction_sound P hinv hmem
  · exact genDeclProcedure_sound P hinv hProcs hmem

/-! ## The declaration fold -/

/-- Soundness of the declaration fold: the emitted declaration list is
    `DeclsHasTypeA` from the initial state to the final state, for any enclosing
    program `P`, and `Inv` is preserved throughout. -/
theorem genDeclsFold_sound (P : Program) (n : Nat) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s b n))
    (hProcs : ProcSigCorresponds s'.procs P) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  induction n generalizing s ds s' with
  | zero =>
    simp only [genDeclsFold, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨hds, hs'⟩ := h
    subst hds hs'
    exact ⟨DeclsHasType'.nil _ _, hinv⟩
  | succ n ih =>
    simp only [genDeclsFold, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ds₁, s₁⟩, hstep, ⟨rest, s₂⟩, hrest, hds, hs'⟩ := h
    subst hds hs'
    -- `procs` only grows across the fold, so the *final* correspondence implies the
    -- one this step needs (`ProcSigCorresponds` is antitone — `ProcSigCorresponds.mono`).
    have hsub₁ : ∀ sig ∈ s₁.procs, sig ∈ s'.procs :=
      genDeclsFold_procs_mono _ hrest
    have hsub₀ : ∀ sig ∈ s.procs, sig ∈ s₁.procs :=
      genDeclStep_procs_mono hstep
    -- First step.
    obtain ⟨hstep_sound, hinv₁⟩ :=
      genDeclStep_sound P hinv (ProcSigCorresponds.mono hProcs (fun sig hsig => hsub₁ sig (hsub₀ sig hsig))) hstep
    -- Rest.
    obtain ⟨hrest_sound, hinv₂⟩ := ih hinv₁ hrest hProcs
    refine ⟨?_, hinv₂⟩
    -- Chain: `DeclsHasType'` over `ds₁ ++ rest`.
    exact declsHasType_append hstep_sound hrest_sound

/-! ## Top-level soundness -/

/-- Every program `genProgram` produces is well-typed w.r.t. the annotated
    program-typing spec, starting from the Strata Core reference context. This is
    soundness of the whole-program generator against `ProgramHasType'`
    (instantiated at `HasTypeA`).

    Both conjuncts of `ProgramHasTypeA`:
    * `P.getNames.Nodup` — every declared name is globally distinct (the generator
      draws every declaration name fresh against a threaded reserved set that
      accumulates all prior names); and
    * `∃ C' Γ', DeclsHasType' … P.decls C' Γ'` — the declarations are well-typed
      (the fold). -/
theorem genProgram_sound {numDecls : Nat} {b : Bounds} {P : Program}
    (h : P ∈ SetGen.support (genProgram (G := SetGen.Set) numDecls b)) :
    ProgramHasTypeA DatatypeGen.coreContext {} P := by
  simp only [genProgram, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨⟨decls, sf⟩, hfold, hP⟩ := h
  subst hP
  refine ⟨?_, ?_⟩
  · -- `getNames.Nodup` from the fold's name-distinctness tracking.
    exact genProgram_getNames_nodup hfold
  · -- The declaration list is well-typed (threading from `initState`).
    --
    -- The fold needs `ProcSigCorresponds sf.procs P` for the *finished* program —
    -- the obligation that makes generated `call`s well-typed. It is discharged here,
    -- where `P` finally exists: every registered signature describes a `.proc`
    -- declaration present in `decls` (`ProcsEmitted`, a fold invariant), and the
    -- program's names are distinct, so `Program.Procedure.find?` resolves each one.
    have hem : ProcsEmitted sf.procs decls := by
      have h0 : ProcsEmitted initState.procs [] := by
        intro sig hsig; simp [initState] at hsig
      have := genDeclsFold_procsEmitted numDecls hfold h0
      simpa using this
    have hProcs : ProcSigCorresponds sf.procs { decls := decls } :=
      procSigCorresponds_of_emitted hem (genProgram_getNames_nodup hfold)
    obtain ⟨hsound, _⟩ :=
      genDeclsFold_sound { decls := decls } numDecls inv_initState hfold hProcs
    exact ⟨sf.C, sf.Γ, hsound⟩

end ProgramGen
