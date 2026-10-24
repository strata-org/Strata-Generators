import StrataGenerators.FunctionHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Dedup

/-! # The completeness of `genFunction` -/

namespace StrataGenerators.Function

/-- **Completeness of `genFunction`.** The support of `genFunction` holds each well-typed function
    that meets three conditions. First, the fields that the generator does not vary hold their
    default values. Second, the smaller generators can reach its name, its types, its body and its
    measure, one part at a time. Third, it passes each filter of the generator: `avoid` flags no
    formal parameter, and the binder annotations of its body, its measure and its precondition are
    generable types.

    The hypotheses about reachability follow `hExprComplete`, `hNameReach` and `hTyReach` of
    `genCmd_complete`. They give exactly what the generator must be able to make, beyond good typing:
    - `hNameReach`: `genIdentName` can reach the name of the function and each parameter name.
    - `hTyArgsLen` and `hTyArgsReach`: the `typeArgs` list, which already holds no duplicate, is not
      longer than `depth`, and `genIdentName` can reach each of its names.
    - `hInputNamesLen` and `hInputNamesReach`: the same two conditions for the parameter names.
    - `hInputTyReach` and `hOutputReach`: `genLMonoTy` can reach the output type and each input type.
    - `hBodyReach` and `hMeasureReach`: `genLExpr` can reach the body and the measure, when the
      function has them.
    - `hPreLen` and `hPreReach`: the function has at most one `requires` clause, and `genLExpr` can
      reach its expression at `.bool` **in the context of the formal parameters**, which is
      `inputsAsFVarCtx func.inputs` and not `fctx`. A function whose precondition mentions an ambient
      variable is therefore out of reach by design, and such a function also breaks
      `FuncWF.precond_freevars`.

    The filters on the type arguments and on the shape of the measure need no hypothesis: the
    well-typedness of the function says that each type argument is allowed and occurs in the
    signature, and that a bare-variable measure names a formal parameter.

    `mem_support_genNameList_iff` turns the conditions about `typeArgs` and about the input names into
    concrete conditions: a bound on the length, and the reach of `genIdentName` for each name. -/
theorem genFunction_complete (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (avoid : String → Bool)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (func : Function)
    (hwt : FuncHasTypeA C Γ func)
    -- The generator does not vary these fields, so each one must hold its default value.
    (hConstr : func.isConstr = false)
    (hRec : func.isRecursive = false)
    (hAttr : func.attr = #[])
    (hAxioms : func.axioms = [])
    -- The generator does make the preconditions, but it makes at most one clause, because
    -- `genPreconditions` emits an `Option.toList`. A longer list is therefore out of reach.
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
      b ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] func.typeArgs [] depth func.output))
    (hMeasureReach : ∀ m, func.measure = some m →
      m ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] func.typeArgs [] depth .int))
    -- The generator makes a precondition over the *formal parameters*, which is
    -- `inputsAsFVarCtx`, and not over `fctx`. See `genPrecondition` and
    -- `FuncWF.precond_freevars`.
    (hPreReach : ∀ p ∈ func.preconditions, p.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) (inputsAsFVarCtx func.inputs) octx []
        func.typeArgs [] depth .bool))
    -- The function must pass the filters of the generator.
    (hAvoidInputs : ∀ x ∈ func.inputs.keys, avoid x.name = false)
    (hBodyAnnots : ∀ b, func.body = some b → binderAnnotsGenerable b = true)
    (hMeasureAnnots : ∀ m, func.measure = some m → binderAnnotsGenerable m = true)
    (hPreAnnots : ∀ p ∈ func.preconditions, binderAnnotsGenerable p.expr = true) :
    func ∈ SetGen.support (genFunction (G := SetGen.Set) fctx octx depth [] avoid) := by
  -- Each filter of the generator leaves the parts of `func` unchanged.
  have hAllowedEq : func.typeArgs.filter isAllowedName = func.typeArgs :=
    List.filter_eq_self.mpr hwt.typeArgsAllowed
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
  have hBodyEq : func.body.filter binderAnnotsGenerable = func.body := by
    cases hb : func.body with
    | none => rfl
    | some b => simp only [Option.filter, hBodyAnnots b hb, if_true]
  have hMeasureEq : func.measure.filter (measureShapeOk func.inputs) = func.measure := by
    have hshape : ∀ m, func.measure = some m → measureShapeOk func.inputs m = true := by
      intro m hm
      have hspec := hwt.measureTyped m hm
      have hann := hMeasureAnnots m hm
      cases m with
      | fvar md x ty => simpa only [measureShapeOk, decide_eq_true_eq] using hspec
      | _ => simpa only [measureShapeOk] using hann
    cases hm : func.measure with
    | none => rfl
    | some m => simp only [Option.filter, hshape m hm, if_true]
  have hPreEq : func.preconditions.filter (fun p => binderAnnotsGenerable p.expr)
      = func.preconditions :=
    List.filter_eq_self.mpr hPreAnnots
  simp only [genFunction, mem_support_bind_iff, mem_support_pure_iff]
  -- The witnesses are the parts of the function itself.
  refine ⟨func.name.name, hNameReach,
          func.typeArgs, ?_,
          func.inputs, ?_,
          func.output, ?_,
          func.body, ?_,
          func.measure, ?_,
          func.preconditions, ?_, ?_⟩
  · -- `genTypeArgs` reaches the type arguments. They hold no duplicate, so `List.uniq` leaves
    -- them unchanged.
    exact genTypeArgs_complete depth func.typeArgs hwt.typeArgsNodup
      (mem_support_genNameList_iff depth func.typeArgs |>.mpr ⟨hTyArgsLen, hTyArgsReach⟩)
  · -- `genInputs` reaches the inputs.
    rw [hAllowedEq]
    exact genInputs_complete func.typeArgs depth func.inputs
      hwt.inputsNodup
      (mem_support_genNameList_iff depth _ |>.mpr ⟨hInputNamesLen, hInputNamesReach⟩)
      hInputTyReach
  · rw [hAllowedEq]
    exact hOutputReach
  · -- `genOptExpr` reaches the body.
    rw [hAllowedEq, hInputsEq, hSigEq]
    exact genOptExpr_complete fctx octx func.typeArgs depth func.output func.body hBodyReach
  · -- `genOptExpr` reaches the measure.
    rw [hAllowedEq, hInputsEq, hSigEq]
    exact genOptExpr_complete fctx octx func.typeArgs depth .int func.measure hMeasureReach
  · -- `genPreconditions` reaches the preconditions.
    rw [hAllowedEq, hInputsEq, hSigEq]
    exact genPreconditions_complete octx func.inputs func.typeArgs depth
      func.preconditions hPreLen hPreReach
  · -- The record that the proof builds again equals `func`.
    rw [hAllowedEq, hInputsEq, hSigEq, hBodyEq, hMeasureEq, hPreEq]
    obtain ⟨fname, ftyArgs, fconstr, frec, finputs, foutput, fbody, fattr,
            faxioms, fpre, fmeasure⟩ := func
    obtain ⟨nm, nmeta⟩ := fname
    simp only at hConstr hRec hAttr hAxioms ⊢
    subst hConstr hRec hAttr hAxioms
    rfl

end StrataGenerators.Function
