import StrataGenerators.ProgramGen.Sound
import StrataGenerators.ProgramGen.ContextOkPreserve
import StrataGenerators.ProcedureHasTypeAGen
import StrataGenerators.ProgramGen.ProcSigThread
import Strata.Languages.Core.TypingSpec

/-!
# Whole-program soundness

Combines the per-declaration soundness lemmas (`StrataGenerators.ProgramGen.Sound`)
and the `ContextOk`-preservation lemmas (`StrataGenerators.ProgramGen.ContextOkPreserve`)
into:

* `genDeclDatatype_sound`, `genDeclFunction_sound`, `genDeclProcedure_sound` and
  `genDeclRecFuncBlock_sound` cover the steps whose proofs need the datatype, function and
  procedure generators.
* `genDeclStep_sound` covers the dispatch over the eight steps.
* `genDeclsFold_sound` covers the fold over the declarations, and it gives `DeclsWellTyped` for the
  whole emitted list, at *each* enclosing program.
* `genProgram_sound` is the top-level theorem. Each generated program satisfies
  `ProgramWellTyped programContext [] P`: its names are distinct within each kind of declaration and
  its declarations are well-typed.
-/

open Lambda RandomChoice Core Core.TypeSpec Imperative SetGen
open DatatypeGen
open StrataGenerators.Procedure StrataGenerators.Stmt StrataGenerators.AnnotFacts

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

/-- Soundness of the datatype-block step: a block the context accepts is a well-formed mutual block
    added to `C`, and `Inv` holds after it. -/
theorem genDeclDatatype_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclDatatype (G := SetGen.Set) s b)) :
    DeclsWellTyped P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclDatatype, mem_support_bind_iff] at h
  obtain ⟨block, hblock, hmatch⟩ := h
  -- Well-formedness of the block (consumes `ContextOk` from `Inv`).
  have hwf : MutualADTWF s.C block := genDatatypeBlock_MutualADTWF hinv hblock
  -- Block names: Nodup and fresh against `initialReserved … s.reserved`.
  obtain ⟨hnamesNodup, hnamesFresh⟩ := genDatatypeBlock_names hblock
  -- The gate on allowed datatype names: a rejected block emits nothing.
  split at hmatch
  case isFalse =>
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsWellTyped.nil _ _, hinv⟩
  -- Case on the gate (spec-native `addMutualBlock` instances, matching the generator).
  cases hadd : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams s.C block with
  | error e =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsWellTyped.nil _ _, hinv⟩
  | ok C' =>
    rw [hadd] at hmatch
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    refine ⟨?_, ?_⟩
    · -- The generator pins the spec's `addMutualBlock` instances, so `hadd` matches the
      -- constructor directly.
      exact DeclsWellTyped.cons _ _ _ _ _ _
        (DeclWellTyped.type_data s.C C' [] block .empty hwf hadd)
        (DeclsWellTyped.nil _ _)
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
      have hmono : ∀ (n : String) (v : Nat), s.C.knownTypes[n]? = some v →
          C'.knownTypes[n]? = some v := fun _ _ hv => addMutualBlock_knownTypes_getElem? hadd hv
      have harities := simpleTyArities_of_inv hinv
      obtain ⟨F, hb⟩ := blockFunctionsAdded_of_addMutualBlock hadd hinv.datatypesKnown
        harities.arrow harities.bool
      -- The schemes after the step are the block's derived schemes and the earlier ones.
      have hpctx : ∀ e ∈ (adtDerivedPolyOps block b.derivedFamilies ++ s.pctx) ++
          (adtDerivedPolyOps block b.derivedFamilies ++ s.derivedPctx),
          e ∈ adtDerivedPolyOps block b.derivedFamilies ∨ e ∈ s.pctx ++ s.derivedPctx := by
        intro e he
        simp only [List.mem_append] at he ⊢
        rcases he with (hnew | hold) | (hnew | hold)
        · exact Or.inl hnew
        · exact Or.inr (Or.inl hold)
        · exact Or.inl hnew
        · exact Or.inr (Or.inr hold)
      refine
        { ctxOk := hctx'
          knownReserved := ?_
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
          storedRefsReserved := ?_
          datatypesKnown := datatypesKnown_addMutualBlock hadd hinv.datatypesKnown
          octxWK := ?_
          sigsWK := fun sig hsig ty hty => wellKindedTy_mono hmono (hinv.sigsWK sig hsig ty hty)
          exprCtx := exprCtxOk_addMutualBlock hinv.exprCtx hb hmono hpctx
          polysClosed := polysClosed_addMutualBlock hb hinv.polysClosed hpctx }
      · -- known types of `C'` reserved in the grown set.
        intro k hk
        rcases (hkw k).mp hk with hblk | hold
        · exact List.mem_append_left _ hblk
        · exact List.mem_append_right _ (hinv.knownReserved k hold)
      · intro x hx; exact List.mem_append_right _ (hinv.baseReserved x hx)
      · intro x hx; exact List.mem_append_right _ (hinv.tyConReserved x hx)
      · exact List.mem_append_right _ hinv.arrowReserved
      · -- datatypesReserved: the datatype names of `C'` are the old ones plus the
        -- block's names, and the reserved set grew by exactly the block's names.
        intro n hn
        rw [addMutualBlock_datatypes hadd, allTypeNames_push, List.mem_append] at hn
        rcases hn with hold | hblk
        · exact List.mem_append_right _ (hinv.datatypesReserved n hold)
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
          rw [hdt, allTypeNames_push]
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
      · -- The old operators keep well-kinded types as `C` only gains known types; the block's
        -- derived operators are typed over the block, which `C'` registers.
        intro p hp
        simp only [OpCtx.ops_ofList, List.mem_append] at hp
        rcases hp with hnew | hold
        · exact adtDerivedOps_wellKinded hb (hmono _ _ harities.arrow) _ p hnew
        · exact wellKindedTy_mono hmono (hinv.octxWK p hold)

/-! ## Procedure per-declaration soundness -/

/-- The fold invariant gives the ambient half of the statement generator's well-kindedness
    discipline, at any rigid type variables: the built-in arities, well-kinded operator types and
    well-kinded callee signatures all read only the known types of `C`. -/
theorem wellKindedAmbient_of_inv {s : GenState} (hinv : Inv s) (rv : List TyIdentifier) :
    WellKindedAmbient s.octx s.procs { s.C with rigidTypeVars := rv } :=
  { arities := { simpleTyArities_of_inv hinv with }
    octxWK := hinv.octxWK
    sigsWK := hinv.sigsWK }

/-- Procedure well-typedness does not read the procedure's name, so renaming keeps it. -/
theorem procWellTyped_rename {P : Program} {C : LContext CoreLParams} {ts : TypeScopes}
    {proc : Procedure} {nm : CoreIdent}
    (h : ProcWellTyped P C ts proc) :
    ProcWellTyped P C ts { proc with header := { proc.header with name := nm } } :=
  { inputsNodup := h.inputsNodup
    outputsNodup := h.outputsNodup
    oldNamesFresh := h.oldNamesFresh
    typeArgsNodup := h.typeArgsNodup
    noUndeclaredVars := h.noUndeclaredVars
    signatureWellKinded := h.signatureWellKinded
    modRights := h.modRights
    preconditionsTyped := h.preconditionsTyped
    postconditionsTyped := h.postconditionsTyped
    bodyTyped := h.bodyTyped }

/-- Soundness of the procedure step. The body is generated under the context and scope of the fold,
    so the procedure is well-typed in `C`; renaming it keeps that. `C` is unchanged, and `Inv`
    survives: `reserved` grows, and the new callable signature writes types that are well kinded
    in `C`. -/
theorem genDeclProcedure_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hProcs : ProcSigCorresponds s.procs P)
    (hLocalTypes : ∀ n ∈ programNamesOfKind P .type, ¬ isLocalTypeName n.name)
    {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclProcedure (G := SetGen.Set) s b)) :
    DeclsWellTyped P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨proc₀, hproc₀, nm, _, hds, hs'⟩ := h
  subst hds hs'
  -- The body can hold a `call` to a procedure of the context, so this step uses `hProcs`.
  -- The body draws on the operators of `s.octx` and the derived schemes, which agree with `s.C`.
  have hops : ExprCtxOk s.C [] [] s.octx s.derivedPctx :=
    hinv.exprCtx.restrict (fun _ hp => absurd hp List.not_mem_nil) (fun _ hp => hp)
      (fun _ hp => List.mem_append_right _ hp)
  have hpt : ProcWellTyped P s.C [] proc₀ :=
    genProcedure_sound_ambient P s.octx s.procs hProcs hLocalTypes b.procSize b.procLen s.C s.Γ
      (wellKindedAmbient_of_inv hinv) s.derivedPctx hops proc₀ hproc₀
  have hpt' : ProcWellTyped P s.C []
      { proc₀ with header := { proc₀.header with name := ⟨nm, ()⟩ } } :=
    procWellTyped_rename hpt
  -- The registered signature's written-to blocks are the outputs.
  obtain ⟨M, I, O, hcp, _, hdO, _, houts, _⟩ := genProcedure_commonPrefix_decomp hproc₀
  have hout : ∀ ty ∈ (M ++ O).values, ty ∈ proc₀.header.outputs.values := by
    intro ty hty
    rw [houts]
    exact hty
  have hsigWK : ∀ ty ∈ (M ++ O).values, s.C.WellKindedTy ty :=
    fun ty hty => hpt.signatureWellKinded ty (List.mem_append_right _ (hout ty hty))
  refine ⟨DeclsWellTyped.cons _ _ _ _ _ _
      (DeclWellTyped.proc s.C [] _ .empty hpt') (DeclsWellTyped.nil _ _), ?_⟩
  refine inv_cons_reserved_procs hinv _ _ ?_
  simp only [hcp, hdO]
  exact hsigWK

/-! ## Registering declared functions -/

/-- `Inv` survives registering a function that the context accepts and whose signature meets the
    signature conditions. -/
theorem inv_registerFunc {s : GenState} (hinv : Inv s) {func : Function}
    {C' : LContext CoreLParams} (hadd : s.C.addFactoryFunctionWithError func.toLFunc = .ok C')
    (hsig : StrataGenerators.Function.FuncSigOk s.C func) : Inv (s.registerFunc C' func) := by
  have hext : FactoryExtendedBy (fun f g => g = f) s.C C' [func.toLFunc] :=
    factoryExtendedBy_of_addFactory hadd
  have hkt : C'.knownTypes = s.C.knownTypes := (addFactory_fields hadd).1
  have hsigWK : ∀ ty ∈ func.output :: func.inputs.values, C'.WellKindedTy ty := by
    intro ty hty
    unfold LContext.WellKindedTy
    rw [hkt]
    exact hsig.signatureWellKinded ty hty
  have harrow : C'.knownTypes["arrow"]? = some 2 := by rw [hkt]; exact hinv.ctxOk.arrow_arity
  have hcurWK : C'.WellKindedTy (funcCurriedTy func) :=
    wellKindedTy_mkArrow' harrow (hsigWK _ List.mem_cons_self) _ (fun t ht =>
      hsigWK t (List.mem_cons_of_mem _ (by rw [ListMap.values_eq_map_snd]; exact ht)))
  have hcurK : LMonoTy.knownInstance (funcCurriedTy func) C'.knownTypes = true :=
    Lambda.knownInstance_of_wellKinded _ _ hcurWK
  have hfuncTy : func.toLFunc.type = .ok (.forAll func.toLFunc.typeArgs
      (LMonoTy.mkArrow' func.toLFunc.output (func.toLFunc.inputs.map Prod.snd))) :=
    type_eq_of_sigWF harrow hsig.inputsNodup hsig.typeArgsNodup
      (Lambda.knownInstance_of_wellKinded _ _ (hsigWK _ List.mem_cons_self))
  have hctx' : ExprCtxOk C' [] [] s.octx (s.pctx ++ s.derivedPctx) :=
    hinv.exprCtx.extend hext (fun f hf => by rw [List.mem_singleton.mp hf]; exact hfuncTy)
  have hmemFunc : C'.functions[func.name.name]? = some func.toLFunc := by
    obtain ⟨g, hg, hgf⟩ := hext.contains_new func.toLFunc List.mem_cons_self
    rw [hgf] at hg
    exact hg
  have hclosedFunc : ∀ v ∈ LMonoTy.freeVars (funcCurriedTy func), v ∈ func.typeArgs := by
    intro v hv
    unfold funcCurriedTy at hv
    rw [← ListMap.values_eq_map_snd] at hv
    rcases StrataGenerators.Function.freeVars_mkArrow' _ _ v hv with hout | ⟨t, ht, hvt⟩
    · exact hsig.sigVars _ List.mem_cons_self v hout
    · exact hsig.sigVars t (List.mem_cons_of_mem _ ht) v hvt
  have hgrown := inv_addFactory hinv hadd hctx'
  refine inv_setOpCtxs hgrown _ _ _ ?_ ?_ ?_
  · intro p hp
    split at hp
    · rename_i entry hentry
      simp only [OpCtx.ops_ofList, List.mem_append, List.mem_replicate] at hp
      rcases hp with hold | ⟨_, rfl⟩
      · exact hgrown.octxWK p hold
      · exact funcOpEntry_wellKinded harrow hentry hsigWK
    · exact hgrown.octxWK p hp
  · refine
      { arities := hctx'.arities
        sigs := hctx'.sigs
        fvars := hctx'.fvars
        ops := ?_
        polys := ?_
        polysKnown := ?_ }
    · intro p hp
      split at hp
      · rename_i entry hentry
        simp only [OpCtx.ops_ofList, List.mem_append, List.mem_replicate] at hp
        rcases hp with hold | ⟨_, rfl⟩
        · exact hctx'.ops p hold
        · unfold funcOpEntry at hentry
          split at hentry
          · rw [Option.some.injEq] at hentry
            rw [← hentry]
            exact ⟨hcurK, func.toLFunc, hmemFunc, [], (LMonoTy.subst_nil _).symm⟩
          · exact absurd hentry (by simp)
      · exact hctx'.ops p hp
    · intro name lty hmem
      split at hmem
      · rename_i entry hentry
        rw [List.append_assoc, List.mem_append, List.mem_append, List.mem_replicate] at hmem
        rcases hmem with hold | ⟨_, rfl⟩ | hold
        · exact hctx'.polys name lty (List.mem_append_left _ hold)
        · unfold funcPolyOpEntry at hentry
          split at hentry
          · exact absurd hentry (by simp)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hentry)
            exact ⟨func.toLFunc, hmemFunc, rfl⟩
        · exact hctx'.polys name lty (List.mem_append_right _ hold)
      · exact hctx'.polys name lty hmem
    · intro nm' bvs body hmem
      split at hmem
      · rename_i entry hentry
        rw [List.append_assoc, List.mem_append, List.mem_append, List.mem_replicate] at hmem
        rcases hmem with hold | ⟨_, heq⟩ | hold
        · exact hctx'.polysKnown nm' bvs body (List.mem_append_left _ hold)
        · unfold funcPolyOpEntry at hentry
          split at hentry
          · exact absurd hentry (by simp)
          · rw [← Option.some.inj hentry, Prod.mk.injEq, LTy.forAll.injEq] at heq
            rw [heq.2.2]
            exact hcurK
        · exact hctx'.polysKnown nm' bvs body (List.mem_append_right _ hold)
      · exact hctx'.polysKnown nm' bvs body hmem
  · intro nm' bvs body hmem
    split at hmem
    · rename_i entry hentry
      rw [List.append_assoc, List.mem_append, List.mem_append, List.mem_replicate] at hmem
      rcases hmem with hold | ⟨_, heq⟩ | hold
      · exact hinv.polysClosed nm' bvs body (List.mem_append_left _ hold)
      · unfold funcPolyOpEntry at hentry
        split at hentry
        · exact absurd hentry (by simp)
        · rw [← Option.some.inj hentry, Prod.mk.injEq, LTy.forAll.injEq] at heq
          rw [heq.2.1, heq.2.2]
          exact hclosedFunc
      · exact hinv.polysClosed nm' bvs body (List.mem_append_right _ hold)
    · exact hinv.polysClosed nm' bvs body hmem

/-- Registering, in order, functions that the context accepts and whose signatures meet the
    signature conditions keeps `Inv` and extends the context by exactly those functions, none of
    which it declared before. -/
theorem registerFuncs_sound {s s' : GenState} (hinv : Inv s) {fs : List Function}
    (h : s.registerFuncs fs = some s')
    (hsig : ∀ f ∈ fs, StrataGenerators.Function.FuncSigOk s.C f) :
    Inv s' ∧ FactoryExtendedBy (fun f g => g = f) s.C s'.C (fs.map (·.toLFunc)) ∧
      ∀ f ∈ fs, f.name.name ∉ s.C.functions := by
  induction fs generalizing s with
  | nil =>
    simp only [GenState.registerFuncs, Option.some.injEq] at h
    subst h
    refine ⟨hinv, ⟨rfl, rfl, rfl, rfl, fun _ _ hg => hg, ?_, fun _ hn => Or.inl hn⟩, ?_⟩
    · intro f hf
      exact absurd hf List.not_mem_nil
    · intro f hf
      exact absurd hf List.not_mem_nil
  | cons f fs ih =>
    simp only [GenState.registerFuncs] at h
    split at h
    · rename_i C₁ hadd
      have hinv₁ := inv_registerFunc hinv hadd (hsig f List.mem_cons_self)
      have hkt : C₁.knownTypes = s.C.knownTypes := (addFactory_fields hadd).1
      have hsig₁ : ∀ g ∈ fs, StrataGenerators.Function.FuncSigOk (s.registerFunc C₁ f).C g :=
        fun g hg => (hsig g (List.mem_cons_of_mem _ hg)).congr hkt rfl rfl rfl
      obtain ⟨hinv', hext', hfresh'⟩ := ih hinv₁ h hsig₁
      have hext₁ := factoryExtendedBy_of_addFactory hadd
      refine ⟨hinv', factoryExtendedBy_append s.C C₁ s'.C _ _ hext₁ hext', ?_⟩
      intro g hg hmem
      rcases List.mem_cons.mp hg with rfl | hg
      · exact addFactory_name_fresh hadd hmem
      · obtain ⟨g', hg'⟩ := exists_getElem?_of_mem hmem
        exact hfresh' g hg (mem_of_getElem?_eq_some (hext₁.preserves_old _ _ hg'))
    · exact absurd h (by simp)

/-! ## Per-declaration soundness: functions

The function step generates a function via `genFunction`, renames it to a globally fresh name,
makes it non-recursive with no measure, and gates on `addFactoryFunctionWithError`.
Support membership on the `.ok` branch gives `FactoryExtendedBy`. -/

/-- Function well-typedness survives renaming the function and making it non-recursive with no
    measure. -/
theorem funcWellTyped_rename_nonrec {C : LContext CoreLParams} {ts : TypeScopes}
    {func : Function} {nm : CoreLParams.Identifier}
    (h : FuncWellTyped C ts func) :
    FuncWellTyped C ts { func with name := nm, isRecursive := false, measure := none } :=
  { inputsNodup := h.inputsNodup
    typeArgsNodup := h.typeArgsNodup
    noUndeclaredVars := h.noUndeclaredVars
    typeArgsInSignature := h.typeArgsInSignature
    signatureWellKinded := h.signatureWellKinded
    bodyTyped := h.bodyTyped
    measureOnlyRecursive := fun _ => rfl
    measureTyped := fun _ hm => absurd hm (by simp)
    preconditionsTyped := h.preconditionsTyped
    axiomsTyped := h.axiomsTyped
    annotsScoped := by
      intro e he
      refine h.annotsScoped e ?_
      simp only [Strata.DL.Util.Func.exprs, List.mem_append, Option.toList_none,
        List.not_mem_nil, or_false] at he ⊢
      exact Or.inl he
    constrNoBody := h.constrNoBody }

/-- Every datatype of the fold's datatype pool is declared in the context and registered among its
    known types with its arity. -/
theorem dtCons_registered {s : GenState} (hinv : Inv s) :
    ∀ kc ∈ s.dtCons, (s.C.datatypes.getType kc.1).isSome ∧ s.C.knownTypes[kc.1]? = some kc.2 := by
  intro kc hkc
  obtain ⟨d, hd, hname, hlen⟩ := hinv.dtPoolOk.arity kc hkc
  refine ⟨?_, ?_⟩
  · simp only [Lambda.TypeFactory.getType]
    exact List.find?_isSome.mpr ⟨d, hd, beq_iff_eq.mpr hname⟩
  · rw [← hname, ← hlen]
    exact hinv.datatypesKnown d hd

/-- Soundness of the function step: a function the context accepts is non-recursive, well-typed
    in `C`, and added to `C`; `Inv` holds after it, with the function's operator entry well kinded
    and agreeing with its declaration in the grown context. -/
theorem genDeclFunction_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclFunction (G := SetGen.Set) s b)) :
    DeclsWellTyped P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclFunction, mem_support_bind_iff] at h
  obtain ⟨func₀, hfunc₀, nm, _, hmatch⟩ := h
  let func : Function := { func₀ with name := ⟨nm, ()⟩, isRecursive := false, measure := none }
  have hctx₀ : ExprCtxOk s.C [] [] s.octx s.derivedPctx :=
    hinv.exprCtx.restrict (fun _ hp => absurd hp List.not_mem_nil) (fun _ hp => hp)
      (fun _ hp => List.mem_append_right _ hp)
  have hwt : FuncWellTyped s.C [] func :=
    funcWellTyped_rename_nonrec
      (StrataGenerators.Function.genFunction_sound [] s.octx b.funcDepth s.C [] s.derivedPctx _
        s.dtCons hctx₀
        (fun nm' bvs body hmem => hinv.polysClosed nm' bvs body (List.mem_append_right _ hmem))
        (dtCons_registered hinv) func₀ hfunc₀)
  have hnonrec : ¬ func.isRecursive := Bool.false_ne_true
  split at hmatch
  · rename_i s₁ hreg
    simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    have hsig : ∀ f ∈ [func], StrataGenerators.Function.FuncSigOk s.C f :=
      fun f hf =>
        List.mem_singleton.mp hf ▸ StrataGenerators.Function.FuncSigOk.of_funcWellTyped hwt
    obtain ⟨hinv₁, hext, hfresh⟩ := registerFuncs_sound hinv hreg hsig
    refine ⟨DeclsWellTyped.cons _ _ _ _ _ _
        (DeclWellTyped.func s.C s₁.C [] func .empty hnonrec (hfresh func List.mem_cons_self) hwt
          hext)
        (DeclsWellTyped.nil _ _), ?_⟩
    have hres₁ : s₁.reserved = s.reserved := (registerFuncs_fields hreg).1
    have hgrow := inv_grow_reserved hinv₁ [nm]
    rw [hres₁] at hgrow
    exact hgrow
  · simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
    obtain ⟨hds, hs'⟩ := hmatch
    subst hds hs'
    exact ⟨DeclsWellTyped.nil _ _, hinv⟩

/-! ## Per-declaration soundness: recursive function blocks -/

/-- Dropping `inline` attributes keeps a function well typed. -/
theorem funcWellTyped_dropInline {C : LContext CoreLParams} {ts : TypeScopes} {f : Function}
    (h : FuncWellTyped C ts f) : FuncWellTyped C ts (dropInline f) :=
  { inputsNodup := h.inputsNodup
    typeArgsNodup := h.typeArgsNodup
    noUndeclaredVars := h.noUndeclaredVars
    typeArgsInSignature := h.typeArgsInSignature
    signatureWellKinded := h.signatureWellKinded
    bodyTyped := h.bodyTyped
    measureOnlyRecursive := h.measureOnlyRecursive
    measureTyped := h.measureTyped
    preconditionsTyped := h.preconditionsTyped
    axiomsTyped := h.axiomsTyped
    annotsScoped := h.annotsScoped
    constrNoBody := h.constrNoBody }

/-- A function without its `inline` attributes carries none. -/
theorem dropInline_attr {f : Function} : ∀ a ∈ (dropInline f).attr, a ≠ .inline := by
  intro a ha
  simp only [dropInline, Array.mem_filter, decide_eq_true_eq] at ha
  exact ha.2

/-- Soundness of the recursive-function-block step: a block the context accepts is a non-empty
    list of recursive, non-inline functions, each well-typed against the context extended by the
    stubs of all of them, and the block is added to the context; `Inv` holds after it. -/
theorem genDeclRecFuncBlock_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclRecFuncBlock (G := SetGen.Set) s b)) :
    DeclsWellTyped P s.C [] ds s'.C ∧ Inv s' := by
  rcases genDeclRecFuncBlock_support h with ⟨rfl, rfl⟩ |
    ⟨k, names, stubs, sStub, drawn, s₁, hk, hnames, hstubs, hstub, hdrawn, hreg, rfl, rfl⟩
  · exact ⟨DeclsWellTyped.nil _ _, hinv⟩
  obtain ⟨hlen, _, _⟩ := genDeclNames_spec hnames
  -- Each stub is drawn by `genFuncSig`, so it meets the signature conditions and has no other part.
  have hstubOk : ∀ st ∈ stubs, StrataGenerators.Function.FuncSigOk s.C st ∧
      st.toLFunc = (funcStub st).toLFunc := by
    intro st hst
    obtain ⟨nm, _, hmem⟩ := forall₂_mem_left hstubs st hst
    exact ⟨StrataGenerators.Function.genFuncSig_sound (simpleTyArities_of_inv hinv) nm _ _
        (fun kc hkc => (dtCons_registered hinv kc hkc).2) hmem,
      congrArg (·.toLFunc) (StrataGenerators.Function.genFuncSig_stub hmem).2⟩
  obtain ⟨hinvStub, hextStub, _⟩ :=
    registerFuncs_sound hinv hstub (fun st hst => (hstubOk st hst).1)
  obtain ⟨_, _, hderStub, _, hpolyStub⟩ := registerFuncs_fields hstub
  -- The bodies draw on the stubs' operators and on the stubs' and the derived schemes.
  have hpoolMem : ∀ p ∈ stubs.filterMap funcPolyOpEntry ++ s.derivedPctx,
      p ∈ sStub.pctx ++ sStub.derivedPctx := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨st, hst, hent⟩ := List.mem_filterMap.mp hp
      exact List.mem_append_left _ (hpolyStub st hst p hent)
    · rw [hderStub]
      exact List.mem_append_right _ hp
  have hctxB : ExprCtxOk sStub.C [] [] sStub.octx
      (stubs.filterMap funcPolyOpEntry ++ s.derivedPctx) :=
    hinvStub.exprCtx.restrict (fun _ hp => absurd hp List.not_mem_nil) (fun _ hp => hp) hpoolMem
  have hdtsStub : ∀ kc ∈ s.dtCons, (sStub.C.datatypes.getType kc.1).isSome :=
    fun kc hkc => hextStub.datatypes_eq ▸ (dtCons_registered hinv kc hkc).1
  have hmember : ∀ f ∈ drawn.map dropInline,
      FuncWellTyped sStub.C [] f ∧ StrataGenerators.Function.FuncSigOk s.C f ∧
        f.isRecursive = true := by
    intro f hf
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
    obtain ⟨st, hst, hparts⟩ := forall₂_mem_left hdrawn f₀ hf₀
    obtain ⟨_, hta, hin, hout, hrec⟩ := StrataGenerators.Function.genFuncParts_shape hparts
    have hsigSt := (hstubOk st hst).1
    have hwt := StrataGenerators.Function.genFuncParts_sound _ [] sStub.octx b.funcDepth sStub.C []
      _ s.dtCons hctxB (fun nm bvs body hmem => hinvStub.polysClosed nm bvs body (hpoolMem _ hmem))
      hdtsStub st (hsigSt.congr hextStub.knownTypes_eq rfl rfl rfl) f₀ hparts
    rw [mem_support_pure_iff] at hrec
    exact ⟨funcWellTyped_dropInline hwt, hsigSt.congr rfl hta hin hout, hrec⟩
  obtain ⟨hinv₁, hext₁, hfresh₁⟩ :=
    registerFuncs_sound hinv hreg (fun f hf => (hmember f hf).2.1)
  -- The registered stubs are the stubs of the members.
  have hstubsEq : stubs.map (·.toLFunc) =
      (drawn.map dropInline).map (fun f => (funcStub f).toLFunc) := by
    rw [List.map_congr_left (fun st hst => (hstubOk st hst).2), List.map_map]
    refine (map_eq_map_of_forall₂ hdrawn ?_).symm
    intro f₀ st hparts
    obtain ⟨hname, hta, hin, hout, _⟩ := StrataGenerators.Function.genFuncParts_shape hparts
    show (funcStub f₀).toLFunc = (funcStub st).toLFunc
    simp only [funcStub, hname, hta, hin, hout]
  have hextStub' : FactoryExtendedBy (fun f g => g = f) s.C sStub.C
      ((drawn.map dropInline).map (fun f => (funcStub f).toLFunc)) := by
    rw [← hstubsEq]
    exact hextStub
  have hne : drawn.map dropInline ≠ [] := by
    intro hnil
    have hl : (drawn.map dropInline).length = k := by
      rw [List.length_map, hdrawn.length_eq, hstubs.length_eq, hlen]
    rw [hnil, List.length_nil] at hl
    omega
  have hnoInline : ∀ f ∈ drawn.map dropInline, ∀ a ∈ f.attr, a ≠ .inline := by
    intro f hf
    obtain ⟨f₀, _, rfl⟩ := List.mem_map.mp hf
    exact dropInline_attr
  have hdecl : DeclWellTyped P s.C [] (.recFuncBlock (drawn.map dropInline) .empty) s₁.C :=
    DeclWellTyped.recFuncBlock s.C sStub.C s₁.C [] _ .empty _ _ hne hfresh₁ hnoInline rfl rfl
      hextStub' hext₁ (fun f hf => (hmember f hf).1) (fun f hf => (hmember f hf).2.2)
  refine ⟨DeclsWellTyped.cons _ _ _ _ _ _ hdecl (DeclsWellTyped.nil _ _), ?_⟩
  have hres₁ : s₁.reserved = s.reserved := (registerFuncs_fields hreg).1
  have hgrow := inv_grow_reserved hinv₁ names
  rw [hres₁] at hgrow
  exact hgrow

/-! ## The declaration-step dispatch -/

/-- Soundness of one declaration step: whichever kind the step selects, the emitted declarations are
    well-typed from the context of `s` to that of `s'`, and `Inv` is preserved. -/
theorem genDeclStep_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hProcs : ProcSigCorresponds s.procs P)
    (hLocalTypes : ∀ n ∈ programNamesOfKind P .type, ¬ isLocalTypeName n.name)
    {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b)) :
    DeclsWellTyped P s.C [] ds s'.C ∧ Inv s' := by
  -- `genDeclStep` is a weighted `frequency`; support inversion yields a
  -- `(weight, generator)` pair, so each branch equation pins both components.
  simp only [genDeclStep, mem_support_frequency_iff, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  obtain ⟨w, g, hg, _, hmem⟩ := h
  rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩
  · exact genDeclAbstract_sound P hinv hmem
  · exact genDeclAlias_sound P hinv hmem
  · exact genDeclAxiom_sound P hinv hmem
  · exact genDeclDistinct_sound P hinv hmem
  · exact genDeclDatatype_sound P hinv hmem
  · exact genDeclFunction_sound P hinv hmem
  · exact genDeclProcedure_sound P hinv hProcs hLocalTypes hmem
  · exact genDeclRecFuncBlock_sound P hinv hmem

/-! ## The declaration fold -/

/-- Soundness of the declaration fold: the emitted declaration list is well-typed from the context
    of the initial state to that of the final state, for any enclosing program `P` whose procedures
    the final callable signatures describe and with no local type name among its type names, and
    `Inv` is preserved throughout. -/
theorem genDeclsFold_sound (P : Program) (n : Nat) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s b n))
    (hProcs : ProcSigCorresponds s'.procs P)
    (hLocalTypes : ∀ d ∈ programNamesOfKind P .type, ¬ isLocalTypeName d.name) :
    DeclsWellTyped P s.C [] ds s'.C ∧ Inv s' := by
  induction n generalizing s ds s' with
  | zero =>
    simp only [genDeclsFold, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨hds, hs'⟩ := h
    subst hds hs'
    exact ⟨DeclsWellTyped.nil _ _, hinv⟩
  | succ n ih =>
    simp only [genDeclsFold, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ds₁, s₁⟩, hstep, ⟨rest, s₂⟩, hrest, hds, hs'⟩ := h
    subst hds hs'
    -- The callable signatures only grow across the fold, so the correspondence for the *final*
    -- signatures gives the one this step needs (`ProcSigCorresponds.mono`).
    have hsub₁ : ∀ sig ∈ s₁.procs, sig ∈ s'.procs :=
      genDeclsFold_procs_mono _ hrest
    have hsub₀ : ∀ sig ∈ s.procs, sig ∈ s₁.procs :=
      genDeclStep_procs_mono hstep
    obtain ⟨hstep_sound, hinv₁⟩ :=
      genDeclStep_sound P hinv
        (ProcSigCorresponds.mono hProcs (fun sig hsig => hsub₁ sig (hsub₀ sig hsig)))
        hLocalTypes hstep
    obtain ⟨hrest_sound, hinv₂⟩ := ih hinv₁ hrest hProcs
    exact ⟨declsWellTyped_append hstep_sound hrest_sound, hinv₂⟩

/-! ## Top-level soundness -/

/-- Distinct program names are distinct within each kind of declaration. -/
theorem programNamesOfKind_nodup {P : Program} (h : P.getNames.Nodup) (k : DeclKind) :
    (programNamesOfKind P k).Nodup := by
  have hnames : P.getNames = P.decls.flatMap Decl.names := rfl
  rw [hnames] at h
  exact (List.filter_sublist.flatMap _).nodup h

/-- Every program `genProgram` produces is well-typed in `programContext` with no variable in
    scope.

    * Its names are distinct within each kind of declaration. The generator draws each declaration
      name fresh against a threaded reserved set, so all of its names are distinct.
    * Its declarations are well-typed, which the fold gives. -/
theorem genProgram_sound {numDecls : Nat} {b : Bounds} {P : Program}
    (h : P ∈ SetGen.support (genProgram (G := SetGen.Set) numDecls b)) :
    ProgramWellTyped programContext [] P := by
  simp only [genProgram, mem_support_bind_iff, mem_support_pure_iff] at h
  obtain ⟨⟨decls, sf⟩, hfold, hP⟩ := h
  subst hP
  refine ⟨programNamesOfKind_nodup (genProgram_getNames_nodup hfold), ?_⟩
  -- The fold needs the correspondence for the *finished* program, which is what makes each
  -- generated `call` well typed. Each registered signature describes a `.proc` declaration of
  -- `decls` (`ProcsEmitted`, a fold invariant), and the names are distinct, so
  -- `Program.Procedure.find?` resolves each one.
  have hem : ProcsEmitted sf.procs decls := by
    have h0 : ProcsEmitted initState.procs [] := by
      intro sig hsig; simp [initState] at hsig
    simpa using genDeclsFold_procsEmitted numDecls hfold h0
  have hProcs : ProcSigCorresponds sf.procs { decls := decls } :=
    procSigCorresponds_of_emitted hem (genProgram_getNames_nodup hfold)
  obtain ⟨hsound, _⟩ := genDeclsFold_sound { decls := decls } numDecls inv_initState hfold hProcs
    (genDeclsFold_typeNames numDecls hfold)
  exact ⟨sf.C, hsound⟩

end ProgramGen
