import StrataGenerators.FunctionHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Dedup

/-! # The completeness of `genFunction` -/

namespace StrataGenerators.Function

/-- **Completeness of `genFunction`.** The support of `genFunction` holds each weakly typed
    function whose fields that the generator does not vary hold their default values, whose
    formals `avoid` does not flag, and whose parts the smaller generators can reach.

    The reachability premises name the contexts the generator draws from: the body is drawn over
    the ambient variables of `fctx` that no formal shadows and whose types are over the type
    arguments, the precondition (at most one) over the formals, and both over the operators of
    `opsOver func.typeArgs octx`. -/
theorem genFunction_complete (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (avoid : String → Bool)
    (C : LContext CoreLParams) (ts : TypeScopes)
    (func : Function)
    (hwt : FuncHasTypeW C ts func)
    -- The generator does not vary these fields, so each one must hold its default value.
    (hConstr : func.isConstr = false)
    (hRec : func.isRecursive = false)
    (hAttr : func.attr = #[])
    (hAxioms : func.axioms = [])
    (hPreLen : func.preconditions.length ≤ 1)
    -- The parts that the generator makes must be reachable.
    (hNameReach : func.name.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hTyArgsLen : func.typeArgs.length ≤ depth)
    (hTyArgsReach : ∀ s ∈ func.typeArgs, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hInputNamesLen : (func.inputs.keys.map (·.name)).length ≤ depth)
    (hInputNamesReach : ∀ s ∈ func.inputs.keys.map (·.name),
      s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hInputTyReach : ∀ ty ∈ func.inputs.values,
      ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) func.typeArgs depth))
    (hOutputReach : func.output ∈ SetGen.support (genLMonoTy (G := SetGen.Set) func.typeArgs depth))
    (hBodyReach : ∀ b, func.body = some b →
      b ∈ SetGen.support (genLExpr (G := SetGen.Set)
        (fctx.filter (fun p => !func.inputs.keys.contains ⟨p.1, ()⟩ &&
          (LMonoTy.freeVars p.2).all func.typeArgs.contains))
        (opsOver func.typeArgs octx) [] func.typeArgs [] depth func.output))
    (hPreReach : ∀ p ∈ func.preconditions, p.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (inputsAsFVarCtx func.inputs) (opsOver func.typeArgs octx) []
        func.typeArgs [] depth .bool))
    (hLemmasLen : func.lemmas.length ≤ depth)
    (hLemmasReach : ∀ s ∈ func.lemmas, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hAvoidInputs : ∀ x ∈ func.inputs.keys, avoid x.name = false) :
    func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth [] avoid) := by
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
    exact List.contains_iff_mem.mpr (hwt.typeArgsInSignature a ha)
  have hMeasure : func.measure = none := hwt.measureOnlyRecursive hRec
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff]
  -- The witnesses are the parts of the function itself.
  refine ⟨func.name.name, hNameReach,
          func.typeArgs, ?_,
          func.inputs, ?_,
          func.output, hOutputReach,
          func.body, ?_,
          func.preconditions, ?_,
          func.lemmas, mem_support_genNameList_iff depth _ |>.mpr ⟨hLemmasLen, hLemmasReach⟩, ?_⟩
  · -- `genTypeArgs` reaches the type arguments. They hold no duplicate, so `List.uniq` leaves
    -- them unchanged.
    exact genTypeArgs_complete depth func.typeArgs hwt.typeArgsNodup
      (mem_support_genNameList_iff depth func.typeArgs |>.mpr ⟨hTyArgsLen, hTyArgsReach⟩)
  · exact genInputs_complete func.typeArgs depth func.inputs
      hwt.inputsNodup
      (mem_support_genNameList_iff depth _ |>.mpr ⟨hInputNamesLen, hInputNamesReach⟩)
      hInputTyReach
  · rw [hInputsEq, hSigEq]
    exact genOptExpr_complete _ _ func.typeArgs depth func.output func.body hBodyReach
  · rw [hInputsEq, hSigEq]
    exact genPreconditions_complete _ func.inputs func.typeArgs depth
      func.preconditions hPreLen hPreReach
  · -- The record that the proof builds again equals `func`.
    rw [hInputsEq, hSigEq]
    obtain ⟨fname, ftyArgs, fconstr, frec, finputs, foutput, fbody, fattr,
            faxioms, fpre, fmeasure, flemmas⟩ := func
    obtain ⟨nm, nmeta⟩ := fname
    simp only at hConstr hRec hAttr hAxioms hMeasure ⊢
    subst hConstr hRec hAttr hAxioms hMeasure
    rfl

end StrataGenerators.Function
