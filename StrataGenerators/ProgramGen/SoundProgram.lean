import StrataGenerators.ProgramGen.Sound
import StrataGenerators.ProgramGen.ContextOkPreserve
import StrataGenerators.ProcedureHasTypeAGen
import StrataGenerators.ProgramGen.ProcSigThread
import Strata.Languages.Core.DatatypeTypeProps
import Strata.Languages.Core.WeakTypeSpec

/-!
# Whole-program soundness

Combines the per-declaration soundness lemmas (`StrataGenerators.ProgramGen.Sound`)
and the `ContextOk`-preservation lemmas (`StrataGenerators.ProgramGen.ContextOkPreserve`)
into:

* `genDeclDatatype_sound`, `genDeclFunction_sound` and `genDeclProcedure_sound` cover the steps
  whose proofs need the datatype, function and procedure generators.
* `genDeclStep_sound` covers the dispatch over the seven steps.
* `genDeclsFold_sound` covers the fold over the declarations, and it gives `DeclsHasTypeW` for the
  whole emitted list, at *each* enclosing program.
* `genProgram_sound` is the top-level theorem. Each generated program satisfies
  `ProgramHasTypeW programContext [] P`: its names are distinct within each kind of declaration and
  its declarations are weakly typed.
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
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
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
    exact ⟨DeclsHasTypeW.nil _ _, hinv⟩
  -- Case on the gate (spec-native `addMutualBlock` instances, matching the generator).
  cases hadd : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams s.C block with
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
    · -- The generator pins the spec's `addMutualBlock` instances, so `hadd` matches the
      -- constructor directly.
      exact DeclsHasTypeW.cons _ _ _ _ _ _
        (DeclHasTypeW.type_data s.C C' [] block .empty hwf hadd)
        (DeclsHasTypeW.nil _ _)
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
      obtain ⟨F, hb⟩ := blockFunctionsAdded_of_addMutualBlock hadd hwf hinv.datatypesKnown
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
  { arities := simpleTyArities_of_inv hinv
    octxWK := hinv.octxWK
    sigsWK := hinv.sigsWK }

/-- Weak procedure typing does not read the procedure's name, so renaming the procedure keeps it. -/
theorem procHasTypeW_rename {P : Program} {C : LContext CoreLParams} {ts : TypeScopes}
    {proc : Procedure} {nm : CoreIdent}
    (h : ProcHasTypeW P C ts proc) :
    ProcHasTypeW P C ts { proc with header := { proc.header with name := nm } } :=
  { inputsNodup := h.inputsNodup
    outputsNodup := h.outputsNodup
    typeArgsNodup := h.typeArgsNodup
    noUndeclaredVars := h.noUndeclaredVars
    signatureWellKinded := h.signatureWellKinded
    modRights := h.modRights
    preconditionsTyped := h.preconditionsTyped
    postconditionsTyped := h.postconditionsTyped
    bodyTyped := h.bodyTyped }

/-- Soundness of the procedure step. The body is generated under the context and scope of the fold,
    so the procedure is weakly typed in `C`; renaming it keeps that. `C` is unchanged, and `Inv`
    survives: `reserved` grows, and the new callable signature writes types that are well kinded
    in `C`. -/
theorem genDeclProcedure_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hProcs : ProcSigCorresponds s.procs P)
    {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclProcedure (G := SetGen.Set) s b)) :
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨proc₀, hproc₀, nm, _, hds, hs'⟩ := h
  subst hds hs'
  -- The body can hold a `call` to a procedure of the context, so this step uses `hProcs`.
  -- The body draws on the operators of `s.octx` and the derived schemes, which agree with `s.C`.
  have hops : ExprCtxOk s.C [] [] s.octx s.derivedPctx :=
    hinv.exprCtx.restrict (fun _ hp => absurd hp List.not_mem_nil) (fun _ hp => hp)
      (fun _ hp => List.mem_append_right _ hp)
  have hpt : ProcHasTypeW P s.C [] proc₀ :=
    genProcedure_sound_ambient P s.octx s.procs hProcs b.procSize b.procLen s.C s.Γ
      (wellKindedAmbient_of_inv hinv) s.derivedPctx hops proc₀ hproc₀
  have hpt' : ProcHasTypeW P s.C []
      { proc₀ with header := { proc₀.header with name := ⟨nm, ()⟩ } } :=
    procHasTypeW_rename hpt
  -- The registered signature's written-to blocks are the outputs.
  obtain ⟨M, I, O, hcp, _, hdO, _, houts, _⟩ := genProcedure_commonPrefix_decomp hproc₀
  have hout : ∀ ty ∈ (M ++ O).values, ty ∈ proc₀.header.outputs.values := by
    intro ty hty
    rw [houts]
    exact hty
  have hsigWK : ∀ ty ∈ (M ++ O).values, s.C.WellKindedTy ty :=
    fun ty hty => hpt.signatureWellKinded ty (List.mem_append_right _ (hout ty hty))
  refine ⟨DeclsHasTypeW.cons _ _ _ _ _ _
      (DeclHasTypeW.proc s.C [] _ .empty hpt') (DeclsHasTypeW.nil _ _), ?_⟩
  refine inv_cons_reserved_procs hinv _ _ ?_
  simp only [hcp, hdO]
  exact hsigWK

/-! ## Per-declaration soundness: functions

The function step generates a function via `genFunction`, renames it to a globally fresh name
(weak function typing does not read the name), and gates on `addFactoryFunctionWithError`. Support
membership on the `.ok` branch gives `FactoryExtendedBy`. -/

/-- Weak function typing does not read the function's name, so renaming the function keeps it. -/
theorem funcHasTypeW_rename {C : LContext CoreLParams} {ts : TypeScopes}
    {func : Function} {nm : CoreLParams.Identifier}
    (h : FuncHasTypeW C ts func) : FuncHasTypeW C ts { func with name := nm } :=
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

/-- Soundness of the function step: a function the context accepts is non-recursive, weakly typed
    in `C`, and added to `C`; `Inv` holds after it, with the function's operator entry well kinded
    and agreeing with its declaration in the grown context. -/
theorem genDeclFunction_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclFunction (G := SetGen.Set) s b)) :
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
  simp only [genDeclFunction, mem_support_bind_iff] at h
  obtain ⟨func₀, hfunc₀, nm, _, hmatch⟩ := h
  let func : Function := { func₀ with name := ⟨nm, ()⟩ }
  have hctx₀ : ExprCtxOk s.C [] [] s.octx s.derivedPctx :=
    hinv.exprCtx.restrict (fun _ hp => absurd hp List.not_mem_nil) (fun _ hp => hp)
      (fun _ hp => List.mem_append_right _ hp)
  have hwt : FuncHasTypeW s.C [] func :=
    funcHasTypeW_rename
      (StrataGenerators.Function.genFunction_sound [] s.octx b.funcDepth s.C [] s.derivedPctx _
        hctx₀
        (fun nm' bvs body hmem => hinv.polysClosed nm' bvs body (List.mem_append_right _ hmem))
        func₀ hfunc₀)
  -- Non-recursive: `genFunction` leaves `isRecursive` at its `false` default.
  have hnonrec : ¬ func.isRecursive := by
    simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff] at hfunc₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hf₀⟩ := hfunc₀
    show ¬ func₀.isRecursive
    subst hf₀
    simp
  cases hadd : s.C.addFactoryFunctionWithError func.toLFunc with
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
    have hext : FactoryExtendedBy (fun f g => g = f) s.C C' [func.toLFunc] :=
      factoryExtendedBy_of_addFactory hadd
    refine ⟨DeclsHasTypeW.cons _ _ _ _ _ _
        (DeclHasTypeW.func s.C C' [] func .empty hnonrec (addFactory_name_fresh hadd) hwt hext)
        (DeclsHasTypeW.nil _ _), ?_⟩
    -- `functions` changed (`inv_addFactory`), one name is reserved, and the operator contexts may
    -- gain the function's entry, whose type is well kinded by the function's signature and is the
    -- signature of the function `C'` declares under its name.
    have hkt : C'.knownTypes = s.C.knownTypes := (addFactory_fields hadd).1
    have hsigWK : ∀ ty ∈ func.output :: func.inputs.values, C'.WellKindedTy ty := by
      intro ty hty
      unfold LContext.WellKindedTy
      rw [hkt]
      exact hwt.signatureWellKinded ty hty
    have harrow : C'.knownTypes["arrow"]? = some 2 := by rw [hkt]; exact hinv.ctxOk.arrow_arity
    have hcurWK : C'.WellKindedTy (funcCurriedTy func) :=
      wellKindedTy_mkArrow' harrow (hsigWK _ List.mem_cons_self) _ (fun t ht =>
        hsigWK t (List.mem_cons_of_mem _ (by rw [ListMap.values_eq_map_snd]; exact ht)))
    have hcurK : LMonoTy.knownInstance (funcCurriedTy func) C'.knownTypes = true :=
      Lambda.knownInstance_of_wellKinded _ _ hcurWK
    have hfuncTy : func.toLFunc.type = .ok (.forAll func.toLFunc.typeArgs
        (LMonoTy.mkArrow' func.toLFunc.output (func.toLFunc.inputs.map Prod.snd))) :=
      type_eq_of_sigWF harrow hwt.inputsNodup hwt.typeArgsNodup
        (Lambda.knownInstance_of_wellKinded _ _ (hsigWK _ List.mem_cons_self))
    have hctx' : ExprCtxOk C' [] [] s.octx (s.pctx ++ s.derivedPctx) :=
      hinv.exprCtx.extend hext (fun f hf => by rw [List.mem_singleton.mp hf]; exact hfuncTy)
    have hmemFunc : C'.functions[func.name.name]? = some func.toLFunc := by
      obtain ⟨g, hg, hgf⟩ := hext.contains_new func.toLFunc List.mem_cons_self
      rw [hgf] at hg
      exact hg
    have hclosedFunc : ∀ v ∈ LMonoTy.freeVars (funcCurriedTy func), v ∈ func.typeArgs := by
      intro v hv
      refine hwt.noUndeclaredVars v ?_
      unfold funcCurriedTy at hv
      rw [← ListMap.values_eq_map_snd] at hv
      exact hv
    have hgrown := inv_grow_reserved (s := { s with C := C' }) (inv_addFactory hinv hadd hctx') [nm]
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

/-! ## The declaration-step dispatch -/

/-- Soundness of one declaration step: whichever kind the step selects, the emitted declarations are
    weakly typed from the context of `s` to that of `s'`, and `Inv` is preserved. -/
theorem genDeclStep_sound (P : Program) {s : GenState} {b : Bounds}
    (hinv : Inv s) (hProcs : ProcSigCorresponds s.procs P)
    {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b)) :
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
  -- `genDeclStep` is a weighted `frequency`; support inversion yields a
  -- `(weight, generator)` pair, so each branch equation pins both components.
  simp only [genDeclStep, mem_support_frequency_iff, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  obtain ⟨w, g, hg, _, hmem⟩ := h
  rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact genDeclAbstract_sound P hinv hmem
  · exact genDeclAlias_sound P hinv hmem
  · exact genDeclAxiom_sound P hinv hmem
  · exact genDeclDistinct_sound P hinv hmem
  · exact genDeclDatatype_sound P hinv hmem
  · exact genDeclFunction_sound P hinv hmem
  · exact genDeclProcedure_sound P hinv hProcs hmem

/-! ## The declaration fold -/

/-- Soundness of the declaration fold: the emitted declaration list is weakly typed from the context
    of the initial state to that of the final state, for any enclosing program `P` whose procedures
    the final callable signatures describe, and `Inv` is preserved throughout. -/
theorem genDeclsFold_sound (P : Program) (n : Nat) {s : GenState} {b : Bounds}
    (hinv : Inv s) {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s b n))
    (hProcs : ProcSigCorresponds s'.procs P) :
    DeclsHasTypeW P s.C [] ds s'.C ∧ Inv s' := by
  induction n generalizing s ds s' with
  | zero =>
    simp only [genDeclsFold, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨hds, hs'⟩ := h
    subst hds hs'
    exact ⟨DeclsHasTypeW.nil _ _, hinv⟩
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
        (ProcSigCorresponds.mono hProcs (fun sig hsig => hsub₁ sig (hsub₀ sig hsig))) hstep
    obtain ⟨hrest_sound, hinv₂⟩ := ih hinv₁ hrest hProcs
    exact ⟨declsHasTypeW_append hstep_sound hrest_sound, hinv₂⟩

/-! ## Top-level soundness -/

/-- Distinct program names are distinct within each kind of declaration. -/
theorem programNamesOfKind_nodup {P : Program} (h : P.getNames.Nodup) (k : DeclKind) :
    (programNamesOfKind P k).Nodup := by
  have hnames : P.getNames = P.decls.flatMap Decl.names := rfl
  rw [hnames] at h
  exact (List.filter_sublist.flatMap _).nodup h

/-- Every program `genProgram` produces is weakly typed in `programContext` with no variable in
    scope.

    * Its names are distinct within each kind of declaration. The generator draws each declaration
      name fresh against a threaded reserved set, so all of its names are distinct.
    * Its declarations are weakly typed, which the fold gives. -/
theorem genProgram_sound {numDecls : Nat} {b : Bounds} {P : Program}
    (h : P ∈ SetGen.support (genProgram (G := SetGen.Set) numDecls b)) :
    ProgramHasTypeW programContext [] P := by
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
  exact ⟨sf.C, hsound⟩

end ProgramGen
