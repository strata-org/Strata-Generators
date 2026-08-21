import StrataGenerators.ProgramGen.Sound
import StrataGenerators.ProgramGen.ContextOkPreserve
import StrataGenerators.ProcedureHasTypeAGen
import StrataGenerators.ProgramGen.ProcSigThread

/-!
# Whole-program soundness

Combines the per-declaration soundness lemmas (`StrataGenerators.ProgramGen.Sound`)
and the `ContextOk`-preservation lemmas (`StrataGenerators.ProgramGen.ContextOkPreserve`)
into:

* `genDeclDatatype_sound` covers the last step for one declaration, which gives a block of datatypes. Its proof
  that the step keeps the invariant needs `contextOk_addMutualBlock`.
* `genDeclStep_sound` covers the dispatch of the `oneOf` over the six steps.
* `genDeclsFold_sound` covers the fold over the declarations, and it gives `DeclsHasTypeA` for the whole emitted
  list, at *each* enclosing program.
* `genProgram_sound` is the top-level theorem. Each generated program satisfies
  `ProgramHasTypeA coreContext {} P`, which is soundness against `ProgramHasType'` at the annotated
  specification, and that includes the fact that each name of the program is distinct.
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
      -- Block names avoid `initialReserved` over the *combined* pool; the
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
          aliasPoolDisjoint := ?_
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
      · -- alias-pool disjointness unchanged (`Γ` and pool unchanged).
        exact hinv.aliasPoolDisjoint
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
        -- * The field `inhab`. For a *new* entry, it is exactly the field `inhabited` of the `MutualADTWF` proof
        --   above, which already speaks about the factory after the push. For an *old* entry, it is the
        --   inhabitance of the earlier pool, which `tySymInhab_push` transports across the push.
        have hdt : C'.datatypes = s.C.datatypes.push block := addMutualBlock_datatypes hadd
        have hstored : DatatypeGen.StoredRefsAbsent s.C block :=
          storedRefsAbsent_of_inv hinv hfresh_res
        refine { known := ?_, arity := ?_, inhab := ?_ }
        · intro kc hkc
          rw [hdt, TypeFactory.allTypeNames, allDatatypes_push, List.map_append]
          rcases List.mem_append.mp hkc with hnew | hold
          · -- A new pool entry's name is a block name.
            obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hnew
            exact List.mem_append_right _ (List.mem_map.mpr ⟨d, hd, by rw [← hdeq]⟩)
          · exact List.mem_append_left _ (hinv.dtPoolOk.known kc hold)
        · -- Arity: a new entry records its datatype's own `typeArgs` count; old entries
          -- keep theirs, and `push` only grows `allDatatypes`.
          intro kc hkc
          rw [hdt, allDatatypes_push]
          rcases List.mem_append.mp hkc with hnew | hold
          · obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hnew
            exact ⟨d, List.mem_append_right _ hd, by rw [← hdeq], by rw [← hdeq]⟩
          · obtain ⟨d, hd, hrest⟩ := hinv.dtPoolOk.arity kc hold
            exact ⟨d, List.mem_append_left _ hd, hrest⟩
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
        -- confined to the pool ∪ block names ∪ {"arrow"}, all reserved.
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

/-! ## The assumed statement-level well-kindedness discipline

Upstream's `init` rules and `signatureWellKinded` fields require every stored / declared
monotype to be well-kinded in the ambient context. For the procedure step that reduces to
`StmtHasTypeAGen.WellKindedAmbient` at the states the declaration fold reaches: `arities`
(discharged by `simpleTyArities_of_inv`) plus well-kindedness of the *operator vocabulary*
`s.octx` and of the callable procedure signatures `s.procs`.

Those last two are what remain **assumed**, guarded by `Inv` so the assumption ranges only
over states the fold can actually reach, and threaded unchanged through the fold.
To discharge them, a proof needs results against `ContextOk` about the operators that a generated block of
datatypes gives to the operator context, and about the signatures that `genProcedure` records in the context of
the callable procedures. This file adds no such result.

Two conditions here are theorems, and no theorem assumes them:

* The *scope-local* half, which is the field `WellKindedOk.ctxWK`. `genProcedure_sound` proves it at the seed of
  the body, and `wellKindedOk_preserved` carries it along the body.
* The preservation of well-kindedness, which is the theorem `StrataGenerators.Stmt.wellKindedOk_preserved`.

Both became provable by stating the invariant in `LContext.WellKindedTy` rather
than in the generator's type vocabulary. See the note on
`StmtHasTypeAGen.WellKindedOk`. -/

/-- Assumed: at every state the declaration fold reaches, the *ambient* half of the
    statement generator's well-kindedness discipline holds. See the note above. -/
def ProgramWellKindedAssumption : Prop :=
  ∀ s : GenState, Inv s → ∀ rv : List TyIdentifier,
    StrataGenerators.Stmt.WellKindedAmbient s.octx s.procs { s.C with rigidTypeVars := rv }

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
    signatureWellKinded := h.signatureWellKinded
    modRights := h.modRights
    preconditionsTyped := h.preconditionsTyped
    postconditionsTyped := h.postconditionsTyped
    bodyTyped := h.bodyTyped }

/-- The soundness of the step for a procedure. The generator makes the body under the *real* context and scope of
    the fold, so `genProcedure_sound_ambient` gives `ProcHasTypeA P s.C s.Γ proc₀` directly. The two side
    conditions, about a subset and about an empty list of the value bindings, come from the fields `rigidNil` and
    `typesNil` of the invariant of the fold. A rename to a fresh name keeps the property, which
    `procHasTypeA_rename` proves. The `.proc`
    constructor leaves `C`/`Γ` unchanged, so `Inv` survives (only `reserved`
    grows). -/
theorem genDeclProcedure_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hWKA : ProgramWellKindedAssumption)
    (hProcs : ProcSigCorresponds s.procs P)
    {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclProcedure (G := SetGen.Set) s b)) :
    DeclsHasTypeA P s.C s.Γ ds s'.C s'.Γ ∧ Inv s' := by
  simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨proc₀, hproc₀, nm, hnm, hds, hs'⟩ := h
  subst hds hs'
  -- The body is well typed at the context of the fold, and the field `rigidNil` gives the side condition about
  -- the rigid type variables. The body can hold a `call` to a procedure of the context, so this step uses the
  -- hypothesis `hProcs`, and not a correspondence at an empty context, which has no content.
  have hpt : ProcHasTypeA P s.C s.Γ proc₀ :=
    genProcedure_sound_ambient P s.octx s.procs hProcs b.procSize b.procLen s.C s.Γ
      hinv.typesNil (simpleTyArities_of_inv hinv) (hWKA s hinv)
      proc₀ s.derivedPctx hproc₀
      (by rw [hinv.rigidNil]; exact List.nil_subset _)
  -- Rename to the fresh name; `ProcHasTypeA` is name-invariant.
  have hpt' : ProcHasTypeA P s.C s.Γ
      { proc₀ with header := { proc₀.header with name := ⟨nm, ()⟩ } } :=
    procHasTypeA_rename hpt
  refine ⟨?_, ?_⟩
  · exact DeclsHasType'.cons _ _ _ _ _ _ _ _
      (DeclHasType'.proc s.C s.Γ _ .empty hpt') (DeclsHasType'.nil _ _)
  · -- `Inv` ignores `procs` (it constrains only `C`/`Γ`/pool/reserved), and
    -- the step changes `procs` and `reserved` only.
    exact inv_cons_reserved_procs hinv _ _

/-! ## The declaration-step dispatch -/

/-- Soundness of one declaration step: whichever kind `oneOf` selects, the emitted
    declarations are `DeclsHasTypeA` from `s` to `s'`, and `Inv` is preserved. -/
theorem genDeclStep_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hWKA : ProgramWellKindedAssumption)
    (hProcs : ProcSigCorresponds s.procs P)
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
  · exact genDeclProcedure_sound P hinv hWKA hProcs hmem

/-! ## The declaration fold -/

/-- Soundness of the declaration fold: the emitted declaration list is
    `DeclsHasTypeA` from the initial state to the final state, for any enclosing
    program `P`, and `Inv` is preserved throughout. -/
theorem genDeclsFold_sound (P : Program) (n : Nat) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hWKA : ProgramWellKindedAssumption) {ds : List Decl} {s' : GenState}
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
    -- The context of the callable procedures only grows across the fold, so the correspondence for the *final*
    -- context gives the one that this step needs. `ProcSigCorresponds.mono` proves that.
    have hsub₁ : ∀ sig ∈ s₁.procs, sig ∈ s'.procs :=
      genDeclsFold_procs_mono _ hrest
    have hsub₀ : ∀ sig ∈ s.procs, sig ∈ s₁.procs :=
      genDeclStep_procs_mono hstep
    -- First step.
    obtain ⟨hstep_sound, hinv₁⟩ :=
      genDeclStep_sound P hinv hWKA
        (ProcSigCorresponds.mono hProcs (fun sig hsig => hsub₁ sig (hsub₀ sig hsig))) hstep
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

    The theorem gives both parts of `ProgramHasTypeA`:
    * Each declared name of the program is distinct. The generator draws each declaration name fresh against a
      threaded reserved set, which holds each earlier name.
    * The declarations are well typed, which the fold gives. -/
theorem genProgram_sound {numDecls : Nat} {b : Bounds} {P : Program}
    (hWKA : ProgramWellKindedAssumption)
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
    -- The fold needs the correspondence for the *finished* program, and that obligation is what makes each
    -- generated `call` well typed. This proof discharges it here, where the program exists. Each registered
    -- signature describes a `.proc`
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
      genDeclsFold_sound { decls := decls } numDecls inv_initState hWKA hfold hProcs
    exact ⟨sf.C, sf.Γ, hsound⟩

end ProgramGen
