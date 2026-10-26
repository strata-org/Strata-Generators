import StrataGenerators.FunctionHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Dedup

/-! # The completeness of `genFunction` -/

namespace StrataGenerators.Function

/-- `genRareFlag` reaches both values. -/
theorem mem_support_genRareFlag (b : Bool) :
    b ∈ SetGen.support (genRareFlag (G := SetGen.Set)) := by
  rw [genRareFlag, mem_support_frequency_iff]
  cases b
  · exact ⟨7, fun () => pure false, by simp, by omega, by rw [mem_support_pure_iff]⟩
  · exact ⟨1, fun () => pure true, by simp, by omega, by rw [mem_support_pure_iff]⟩

/-- `genFuncAttr depth` reaches every attribute whose parameter index, if any, is at most
    `depth`. -/
theorem genFuncAttr_complete (depth : Nat) (a : Strata.DL.Util.FuncAttr)
    (h : ∀ i ∈ attrParamIdx a, i ≤ depth) :
    a ∈ SetGen.support (genFuncAttr (G := SetGen.Set) depth) := by
  have hzero : 0 ∈ List.range (depth + 1) := List.mem_range.mpr (by omega)
  have hidx : ∀ i, attrParamIdx a = some i → i ∈ List.range (depth + 1) :=
    fun i hi => List.mem_range.mpr (by have hle := h i hi; omega)
  simp only [genFuncAttr, mem_support_bind_iff, mem_support_elements_iff]
  cases a with
  | inline => exact ⟨0, hzero, by simp⟩
  | inlineIfConstr i => exact ⟨i, hidx i rfl, by simp⟩
  | evalIfConstr i => exact ⟨i, hidx i rfl, by simp⟩
  | evalIfValue i => exact ⟨i, hidx i rfl, by simp⟩
  | inlineIfAllValues => exact ⟨0, hzero, by simp⟩

/-- **Completeness of `genFuncSig`.** It reaches the signature of each function whose type
    arguments are distinct reachable names that all occur in the signature, whose formals have
    distinct reachable names that `avoid` does not flag, whose input types `genInputTy dts`
    reaches and whose output type `genLMonoTy` reaches over the type arguments. -/
theorem genFuncSig_complete (depth : Nat) (avoid : String → Bool) (dts : List (String × Nat))
    (func : Function)
    (hTyArgsNodup : func.typeArgs.Nodup) (hInputsNodup : func.inputs.keys.Nodup)
    (hTyArgsInSig : ∀ ta ∈ func.typeArgs,
      ta ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values))
    (hTyArgsLen : func.typeArgs.length ≤ depth)
    (hTyArgsReach : ∀ s ∈ func.typeArgs, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hInputNamesLen : (func.inputs.keys.map (·.name)).length ≤ depth)
    (hInputNamesReach : ∀ s ∈ func.inputs.keys.map (·.name),
      s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hInputTyReach : ∀ ty ∈ func.inputs.values,
      ty ∈ SetGen.support (genInputTy (G := SetGen.Set) dts func.typeArgs depth))
    (hOutputReach : func.output ∈ SetGen.support (genLMonoTy (G := SetGen.Set) func.typeArgs depth))
    (hAvoidInputs : ∀ x ∈ func.inputs.keys, avoid x.name = false) :
    funcStub func ∈
      SetGen.support (genFuncSig (G := SetGen.Set) func.name.name depth avoid dts) := by
  -- Each filter of the generator leaves the parts of `func` unchanged.
  have hInputsEq : func.inputs.filter (fun p => !avoid p.1.name) = func.inputs := by
    refine List.filter_eq_self.mpr ?_
    intro p hp
    have hkey : p.1 ∈ func.inputs.keys := by
      rw [ListMap.keys_eq_map_fst]
      exact List.mem_map_of_mem hp
    simp only [hAvoidInputs p.1 hkey, Bool.not_false]
  have hSigEq : func.typeArgs.filter
      (fun a => (LMonoTy.freeVars (LMonoTy.mkArrow' func.output (ListMap.values func.inputs))).contains a)
      = func.typeArgs := by
    refine List.filter_eq_self.mpr ?_
    intro a ha
    exact List.contains_iff_mem.mpr (hTyArgsInSig a ha)
  simp only [genFuncSig, mem_support_bind_iff, mem_support_pure_iff]
  refine ⟨func.typeArgs, ?_, func.inputs, ?_, func.output, hOutputReach, ?_⟩
  · -- `genTypeArgs` reaches the type arguments. They hold no duplicate, so `List.uniq` leaves
    -- them unchanged.
    exact genTypeArgs_complete depth func.typeArgs hTyArgsNodup
      (mem_support_genNameList_iff depth func.typeArgs |>.mpr ⟨hTyArgsLen, hTyArgsReach⟩)
  · exact genInputs_complete _ depth func.inputs hInputsNodup
      (mem_support_genNameList_iff depth _ |>.mpr ⟨hInputNamesLen, hInputNamesReach⟩)
      hInputTyReach
  · rw [hInputsEq, hSigEq]
    rfl

/-- `genMeasure` reaches every optional measure that is an `int` expression `genLExpr` reaches whose
    bare variable, if it is one, is a formal, or a formal of `datatypeFormals dts inputs` annotated
    with its type. -/
theorem genMeasure_complete (dts : List (String × Nat)) (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (o : Option LExpr')
    (ho : ∀ m, o = some m →
      (measureOnFormal inputs m = true ∧
        m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .int)) ∨
      ∃ p ∈ datatypeFormals dts inputs, m = .fvar () p.1 (some p.2)) :
    o ∈ SetGen.support (genMeasure (G := SetGen.Set) dts fctx octx tvars depth pctx inputs) := by
  have hint : (∀ m, o = some m → measureOnFormal inputs m = true ∧
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .int)) →
      o ∈ SetGen.support (genIntMeasure (G := SetGen.Set) fctx octx tvars depth pctx inputs) := by
    intro h
    rw [genIntMeasure, mem_support_map_iff]
    refine ⟨o, genOptExpr_complete _ _ _ _ _ o (fun m hm => (h m hm).2), ?_⟩
    cases o with
    | none => rfl
    | some m => simp only [Option.filter_some, (h m rfl).1, if_true]
  unfold genMeasure
  split
  · rename_i hne
    rw [mem_support_frequency_iff]
    cases o with
    | none =>
      exact ⟨3, fun () => genIntMeasure fctx octx tvars depth pctx inputs, by simp, by omega,
        hint (fun _ hm => absurd hm (by simp))⟩
    | some m =>
      rcases ho m rfl with hl | ⟨p, hp, rfl⟩
      · exact ⟨3, fun () => genIntMeasure fctx octx tvars depth pctx inputs, by simp, by omega,
          hint (fun m' hm' => Option.some.inj hm' ▸ hl)⟩
      · refine ⟨1, fun () => (fun p => some (.fvar () p.1 (some p.2))) <$>
          elements (datatypeFormals dts inputs) hne, by simp, by omega, ?_⟩
        rw [mem_support_map_iff]
        exact ⟨p, (mem_support_elements_iff hne).mpr hp, rfl⟩
  · rename_i hnil
    refine hint (fun m hm => ?_)
    rcases ho m hm with hl | ⟨p, hp, _⟩
    · exact hl
    · rw [not_not.mp hnil] at hp
      exact absurd hp List.not_mem_nil

/-- **Completeness of `genFuncParts`.** From the signature of a well-typed function, it reaches
    the function when the flag generator reaches its recursion flag and the smaller generators
    reach its parts over the formals, the unshadowed ambient variables of `fctx` whose types are
    over the type arguments (`funcFctx`), the operators of `opsOver func.typeArgs octx` and the
    schemes of `pctx`. -/
theorem genFuncParts_complete (genRecursive : SetGen.Set Bool) (fctx : FVarCtx) (octx : OpCtx)
    (depth : Nat) (pctx : PolyOpCtx) (dts : List (String × Nat)) (C : LContext CoreLParams)
    (ts : TypeScopes)
    (func : Function) (hwt : FuncWellTyped C ts func)
    (hRec : func.isRecursive ∈ SetGen.support genRecursive)
    (hBodyReach : ∀ b, func.body = some b →
      b ∈ SetGen.support (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) pctx func.typeArgs [] depth func.output))
    (hPreLen : func.preconditions.length ≤ maxFuncClauses)
    (hPreReach : ∀ p ∈ func.preconditions, p.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) pctx func.typeArgs [] depth .bool))
    (hAxiomsLen : func.axioms.length ≤ maxFuncClauses)
    (hAxiomsReach : ∀ ax ∈ func.axioms, ax ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) pctx func.typeArgs [] depth .bool))
    (hMeasureReach : ∀ m, func.measure = some m → m ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) pctx func.typeArgs [] depth .int) ∨
      ∃ p ∈ datatypeFormals dts func.inputs, m = .fvar () p.1 (some p.2))
    (hAttrLen : func.attr.size ≤ depth)
    (hAttrIdx : ∀ a ∈ func.attr.toList, ∀ i ∈ attrParamIdx a, i ≤ depth)
    (hLemmasLen : func.lemmas.length ≤ depth)
    (hLemmasReach : ∀ s ∈ func.lemmas, s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    func ∈ SetGen.support (genFuncParts (G := SetGen.Set) genRecursive fctx octx depth pctx dts
      (funcStub func)) := by
  -- A bare-variable measure is a formal.
  have hon : ∀ m, func.measure = some m → measureOnFormal func.inputs m = true := by
    intro m hm
    have hty := hwt.measureTyped m hm
    unfold measureOnFormal
    split
    · obtain ⟨ty, hfind, _⟩ := hty
      exact keys_contains_iff_find?.mpr ⟨ty, hfind⟩
    · rfl
  simp only [genFuncParts, mem_support_bind_iff, mem_support_pure_iff]
  -- The witnesses are the parts of the function itself.
  refine ⟨func.isConstr, mem_support_genRareFlag _,
          func.body, ?_,
          func.preconditions, ?_,
          func.axioms, ?_,
          func.isRecursive, hRec,
          func.measure, ?_,
          func.attr.toList, ?_,
          func.lemmas, mem_support_genNameList_iff depth _ |>.mpr ⟨hLemmasLen, hLemmasReach⟩, rfl⟩
  · cases hc : func.isConstr
    · rw [if_neg (by simp)]
      exact genOptExpr_complete _ _ func.typeArgs depth func.output func.body hBodyReach
    · rw [if_pos rfl, hwt.constrNoBody hc, mem_support_pure_iff]
  · exact genPreconditions_complete _ func.inputs func.typeArgs depth _
      func.preconditions hPreLen hPreReach
  · rw [mem_support_listOfMaxLength_iff]
    exact ⟨hAxiomsLen, hAxiomsReach⟩
  · cases hr : func.isRecursive
    · rw [if_neg (by simp), hwt.measureOnlyRecursive hr, mem_support_pure_iff]
    · rw [if_pos rfl]
      refine genMeasure_complete dts _ _ func.typeArgs depth pctx func.inputs func.measure ?_
      intro m hm
      rcases hMeasureReach m hm with hreach | hdt
      · exact Or.inl ⟨hon m hm, hreach⟩
      · exact Or.inr hdt
  · rw [mem_support_listOfMaxLength_iff]
    refine ⟨by rw [Array.length_toList]; exact hAttrLen, fun a ha => ?_⟩
    exact genFuncAttr_complete depth a (hAttrIdx a ha)

/-- **Completeness of `genFunction`.** The support of `genFunction` holds each well-typed
    function whose formals `avoid` does not flag and whose parts the smaller generators reach.

    Every expression is reached over the formals and the ambient variables of `fctx` that no
    formal shadows and whose types are over the type arguments (`funcFctx`), with the operators of
    `opsOver func.typeArgs octx`. -/
theorem genFunction_complete (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (avoid : String → Bool) (dts : List (String × Nat))
    (C : LContext CoreLParams) (ts : TypeScopes)
    (func : Function)
    (hwt : FuncWellTyped C ts func)
    (hNameReach : func.name.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hTyArgsLen : func.typeArgs.length ≤ depth)
    (hTyArgsReach : ∀ s ∈ func.typeArgs, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hInputNamesLen : (func.inputs.keys.map (·.name)).length ≤ depth)
    (hInputNamesReach : ∀ s ∈ func.inputs.keys.map (·.name),
      s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hInputTyReach : ∀ ty ∈ func.inputs.values,
      ty ∈ SetGen.support (genInputTy (G := SetGen.Set) dts func.typeArgs depth))
    (hOutputReach : func.output ∈ SetGen.support (genLMonoTy (G := SetGen.Set) func.typeArgs depth))
    (hBodyReach : ∀ b, func.body = some b →
      b ∈ SetGen.support (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) [] func.typeArgs [] depth func.output))
    (hPreLen : func.preconditions.length ≤ maxFuncClauses)
    (hPreReach : ∀ p ∈ func.preconditions, p.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) [] func.typeArgs [] depth .bool))
    (hAxiomsLen : func.axioms.length ≤ maxFuncClauses)
    (hAxiomsReach : ∀ ax ∈ func.axioms, ax ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) [] func.typeArgs [] depth .bool))
    (hMeasureReach : ∀ m, func.measure = some m → m ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (funcFctx fctx func.inputs func.typeArgs)
        (opsOver func.typeArgs octx) [] func.typeArgs [] depth .int) ∨
      ∃ p ∈ datatypeFormals dts func.inputs, m = .fvar () p.1 (some p.2))
    (hAttrLen : func.attr.size ≤ depth)
    (hAttrIdx : ∀ a ∈ func.attr.toList, ∀ i ∈ attrParamIdx a, i ≤ depth)
    (hLemmasLen : func.lemmas.length ≤ depth)
    (hLemmasReach : ∀ s ∈ func.lemmas, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hAvoidInputs : ∀ x ∈ func.inputs.keys, avoid x.name = false) :
    func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth [] avoid dts) := by
  simp only [genFunction, mem_support_bind_iff]
  exact ⟨func.name.name, hNameReach, _,
    genFuncSig_complete depth avoid dts func hwt.typeArgsNodup hwt.inputsNodup
      hwt.typeArgsInSignature
      hTyArgsLen hTyArgsReach hInputNamesLen hInputNamesReach hInputTyReach hOutputReach
      hAvoidInputs,
    genFuncParts_complete genRareFlag fctx octx depth [] dts C ts func hwt
      (mem_support_genRareFlag _) hBodyReach hPreLen hPreReach hAxiomsLen hAxiomsReach
      hMeasureReach hAttrLen hAttrIdx hLemmasLen hLemmasReach⟩

end StrataGenerators.Function
