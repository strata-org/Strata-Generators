import StrataGenerators.ProcedureHasTypeAGen
import StrataGenerators.StmtHasTypeAGenCompleteExists

/-!
# Completeness of `genProcedure` at every large enough size, body length and cap

`genProcedure_complete` is stated at a fixed size, body-length bound and cap, and its premises
mention them: list lengths at most `size`, types and expressions reachable at `size`, and a body
reachable by `genStmtChain` at `size`. `genProcedure_complete_ev` replaces each of them by a
premise that mentions no size, and concludes that the procedure is generated at every large enough
size, at every body-length bound at least the body's length, and at every large enough cap.

The body premise is the statement-level `spec_complete_chain_ev`, at the scope and the immutable
variables that `genProcedure` seeds the body with. So a procedure is complete exactly when its
header is, and its body meets the size-free side conditions of statement completeness.
-/

open Lambda LExpr RandomChoice Core Imperative TypeSpec
open StrataGenerators.Stmt StrataGenerators.Function StrataGenerators.Stmt.SpecComplete

namespace StrataGenerators.Procedure

/-- A type that `genLMonoTy` reaches at some depth, it reaches at every large enough depth. -/
theorem genLMonoTy_eventually {tvars : List TyIdentifier} {τ : LMonoTy}
    (h : ∃ m, τ ∈ SPMF.support (genLMonoTy (G := SPMF) tvars m)) :
    Eventually fun n => τ ∈ SPMF.support (genLMonoTy (G := SPMF) tvars n) := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun n hn => (genLMonoTy_support tvars n τ).mpr
    (inGenLMonoTySupport_mono tvars m n τ hn ((genLMonoTy_support tvars m τ).mp hm))⟩

/-- A list of reachable names is in `genNameList`'s support at every depth at least its length. -/
theorem genNameList_eventually {l : List String}
    (h : ∀ s ∈ l, s ∈ SPMF.support (genIdentName (G := SPMF))) :
    Eventually fun n => l ∈ SPMF.support (genNameList (G := SPMF) n) :=
  ⟨l.length, fun n hn => (mem_support_genNameList_iff n l).mpr ⟨hn, h⟩⟩

theorem le_eventually (a : Nat) : Eventually (a ≤ ·) := ⟨a, fun _ h => h⟩

/-- **The completeness of `genProcedure`, at every large enough size, body length and cap.** The
    premises are `genProcedure_complete`'s, with every length premise dropped, each type premise
    weakened to "reachable at some depth", each contract expression premise weakened to "reachable at
    every large enough depth", and the body premise replaced by the size-free side conditions of
    `spec_complete_chain_ev`, at the scope `M ++ I ++ (M ++ O) ++ oldVars M` and the immutable
    variables `keys (M ++ I) ++ keys (oldVars M)` that `genProcedure` seeds the body with. -/
theorem genProcedure_complete_ev (P : Program) (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (proc : Procedure)
    (M I O : ListMap (Identifier Unit) LMonoTy)
    (bodyss : List Statement) (C' : LContext CoreLParams) (ts ts' : TypeScopes)
    (hBodyEq : proc.body = .structured bodyss)
    (hInputsEq : proc.header.inputs = M ++ I)
    (hOutputsEq : proc.header.outputs = M ++ O)
    (hIdisjM : ∀ k ∈ ListMap.keys I, k ∉ ListMap.keys M)
    (hOdisjMI : ∀ k ∈ ListMap.keys O, k ∉ ListMap.keys (M ++ I))
    (hName : proc.header.name.name ∈ SPMF.support (genIdentName (G := SPMF)))
    (hTyArgsNodup : proc.header.typeArgs.Nodup)
    (hTyArgsReach : ∀ s ∈ proc.header.typeArgs, s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hMNodup : M.keys.Nodup)
    (hMNamesReach : ∀ s ∈ M.keys.map (·.name), s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hMTyReach : ∀ ty ∈ M.values,
      ∃ m, ty ∈ SPMF.support (genLMonoTy (G := SPMF) proc.header.typeArgs m))
    (hINodup : I.keys.Nodup)
    (hINamesReach : ∀ s ∈ I.keys.map (·.name), s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hITyReach : ∀ ty ∈ I.values,
      ∃ m, ty ∈ SPMF.support (genLMonoTy (G := SPMF) proc.header.typeArgs m))
    (hONodup : O.keys.Nodup)
    (hONamesReach : ∀ s ∈ O.keys.map (·.name), s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hOTyReach : ∀ ty ∈ O.values,
      ∃ m, ty ∈ SPMF.support (genLMonoTy (G := SPMF) proc.header.typeArgs m))
    (hFormalsNotFn : ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      id.name ∉ C.functions)
    (hPreLabels : ∀ s ∈ proc.spec.preconditions.keys, s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hPreAttr : ∀ c ∈ proc.spec.preconditions.values, c.attr = .Default)
    (hPreMd : ∀ c ∈ proc.spec.preconditions.values, c.md = #[])
    (hPreExpr : ∀ c ∈ proc.spec.preconditions.values, Eventually fun d =>
      c.expr ∈ SPMF.support (genLExpr (G := SPMF)
        (sigFctx (M ++ I)) octx [] proc.header.typeArgs [] d .bool))
    (hPostLabels : ∀ s ∈ proc.spec.postconditions.keys, s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hPostAttr : ∀ c ∈ proc.spec.postconditions.values, c.attr = .Default)
    (hPostMd : ∀ c ∈ proc.spec.postconditions.values, c.md = #[])
    (hPostExpr : ∀ c ∈ proc.spec.postconditions.values, Eventually fun d =>
      c.expr ∈ SPMF.support (genLExpr (G := SPMF)
        (sigFctx (M ++ I ++ (M ++ O) ++ oldVars M)) octx [] proc.header.typeArgs [] d .bool))
    -- The body, through the size-free statement completeness:
    (hBodyWT : StatementsWellTyped P { C with rigidTypeVars := C.rigidTypeVars ++ proc.header.typeArgs }
      ts [] bodyss C' ts')
    (hBodyΓ : Strata.Util.HMaps.Equiv ts (procToTCtx (M ++ I ++ (M ++ O) ++ oldVars M)).types)
    (hBodyShape : InGenShapeList bodyss)
    (hBodyWrites : WritesOkList (ListMap.keys (M ++ I) ++ ListMap.keys (oldVars M)) bodyss)
    (hBodyNames : AlphabetOkEList proc.header.typeArgs bodyss)
    (hBodyCalls : CallOkEList (octx := octx) (tvars := proc.header.typeArgs)
      (ListMap.keys (M ++ I) ++ ListMap.keys (oldVars M)) procs (M ++ I ++ (M ++ O) ++ oldVars M)
      bodyss)
    (hBodyExprs : ExprOkEList (octx := octx) (tvars := proc.header.typeArgs)
      (M ++ I ++ (M ++ O) ++ oldVars M) bodyss)
    (hLemmasReach : ∀ s ∈ proc.header.lemmas, s ∈ SPMF.support (genIdentName (G := SPMF))) :
    ∃ K, Eventually fun size => ∀ len k, bodyss.length ≤ len → K ≤ k →
      proc ∈ SPMF.support (genProcedure (G := SPMF) octx procs C Γ size len (maxStmtSeqLen := k)) := by
  obtain ⟨K, hbody⟩ := spec_complete_chain_ev P (ListMap.keys (M ++ I) ++ ListMap.keys (oldVars M))
    procs bodyss _ ts [] C' ts' hBodyWT _ hBodyΓ hBodyShape hBodyWrites hBodyNames hBodyCalls
    hBodyExprs
  have hM := Eventually.forall_mem M.values fun ty h => genLMonoTy_eventually (hMTyReach ty h)
  have hI := Eventually.forall_mem I.values fun ty h => genLMonoTy_eventually (hITyReach ty h)
  have hO := Eventually.forall_mem O.values fun ty h => genLMonoTy_eventually (hOTyReach ty h)
  refine ⟨K, (hbody.and (hM.and (hI.and (hO.and ((Eventually.forall_mem _ hPreExpr).and
    ((Eventually.forall_mem _ hPostExpr).and ((genNameList_eventually hPreLabels).and
    ((genNameList_eventually hPostLabels).and ((le_eventually proc.header.typeArgs.length).and
    ((le_eventually (M.keys.map (·.name)).length).and ((le_eventually (I.keys.map (·.name)).length).and
    ((le_eventually (O.keys.map (·.name)).length).and
      (le_eventually proc.header.lemmas.length))))))))))))).mono ?_⟩
  rintro n ⟨hb, hm, hi, ho, hpre, hpost, hprel, hpostl, hta, hmn, hin, hon, hlem⟩ len k hlen hk
  obtain ⟨ctx', -, -, hmem⟩ := hb k hk
  exact genProcedure_complete (maxStmtSeqLen := k) octx procs C Γ n len proc M I O bodyss C' ctx'
    hBodyEq hInputsEq hOutputsEq hIdisjM hOdisjMI hName hTyArgsNodup hta hTyArgsReach
    hMNodup hmn hMNamesReach hm hINodup hin hINamesReach hi hONodup hon hONamesReach ho
    hFormalsNotFn hprel hPreAttr hPreMd hpre hpostl hPostAttr hPostMd hpost bodyss.length hlen hmem
    hlem hLemmasReach

end StrataGenerators.Procedure
