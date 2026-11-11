import StrataGenerators.ProgramGen.CompleteProcedure

/-!
# Whole-program completeness, for some `Bounds`

`Bounds` collects the size parameters of the program generator, so that a statement about the
generator quantifies over one `Bounds` value instead of reasoning about each size separately.
`genProgram_complete_of_fold` composes per-step reachability at one *fixed* `b : Bounds`. This
module removes `b` from the statement: `genProgram_complete_eventually` says that if each
declaration step of a trace is reachable at every large enough bound, the whole program is reachable
by `genProgram … b` for *some* `b`.

Every premise of a step lemma asks a bound to be *large enough*, so it suffices to look at the
`Bounds` values whose numeric fields all equal one number `N` (`Bounds.uniform N fam`). "At every large
enough bound" is then `Eventually` over `N`, and the steps of a trace combine through
`Eventually.and`.

The per-kind lemmas `step*_eventually` lift each declaration kind's step lemma to this form. A
premise that bounds a length by a field holds eventually by itself. A premise about a sub-generator's
support at one field (`genNonRecursiveArgTy` at `tySize`, `genLExpr` at `exprDepth`, `genFuncSig` and
`genFuncParts` at `funcDepth`, the datatype generator at its fields) becomes an `Eventually` premise
in that field. The procedure step reads its bounds through `genDeclProcedure_complete`, so it
inherits the size-free statement completeness.

A plain function declaration (`genDeclFunction`) has no step lemma yet, so a trace covered here
declares its functions in recursive function blocks.
-/

open Lambda RandomChoice Core Imperative
open StrataGenerators StrataGenerators.Procedure StrataGenerators.Stmt.SpecComplete
open StrataGenerators.Stmt (isLocalTypeName)

namespace ProgramGen

/-- The `Bounds` value whose numeric fields are all `N`, with the derived-operator families `fam`. -/
def Bounds.uniform (N : Nat) (fam : DerivedOpFamilies) : Bounds where
  maxTyConArity := N
  maxAliasTyParams := N
  tySize := N
  exprDepth := N
  funcDepth := N
  maxRecFuncs := N
  maxDistinctVars := N
  maxExtraDatatypes := N
  maxTyParams := N
  maxExtraBaseConstrs := N
  maxRecConstrs := N
  maxArgs := N
  maxDatatypeSize := N
  procSize := N
  procLen := N
  maxStmtSeqLen := N
  derivedFamilies := fam

-- ── Per-kind steps, at every large enough uniform bound ─────────────────────

section steps
variable {fam : DerivedOpFamilies} {s : GenState}

theorem stepAbstract_eventually {nm : String} {ar : Nat} {C' : LContext CoreLParams}
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hnmAllowed : isAllowedName nm = true) (hnmNotLocal : isLocalTypeName nm = false)
    (hC : s.C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    Eventually fun N => (([mkAbstractTypeDecl nm ar]), s.addAbstract nm ar C') ∈
      SPMF.support (genDeclStep (G := SPMF) s (Bounds.uniform N fam)) :=
  (le_eventually ar).mono fun _ h =>
    genDeclStep_complete_of_mem (.inl (genDeclAbstract_complete hnm hnmAllowed hnmNotLocal h hC))

theorem stepAlias_eventually {nm : String} {tyParams : List TyIdentifier} {body : LMonoTy}
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hnmAllowed : isAllowedName nm = true) (hnmNotLocal : isLocalTypeName nm = false)
    (hparams : tyParams ∈ SPMF.support
      (DatatypeGen.genFreshNames (G := SPMF) s.reserved tyParams.length))
    (hbody : Eventually fun d => body ∈ SPMF.support
      (genNonRecursiveArgTy (G := SPMF) s.baseTypes s.tyCons tyParams d))
    (hallowed : aliasNamesAllowed
      { name := nm, typeArgs := (LMonoTy.freeVars body).uniq, type := body } = true) :
    Eventually fun N => (([mkAliasDecl nm body]),
        { s with
          Γ := { s.Γ with aliases :=
                   { typeArgs := (LMonoTy.freeVars body).uniq, name := nm, type := body }
                     :: s.Γ.aliases }
          reserved := nm :: s.reserved }) ∈ SPMF.support
          (genDeclStep (G := SPMF) s (Bounds.uniform N fam)) :=
  ((le_eventually tyParams.length).and hbody).mono fun _ ⟨h₁, h₂⟩ =>
    genDeclStep_complete_of_mem (.inr (.inl
      (genDeclAlias_complete hnm hnmAllowed hnmNotLocal h₁ hparams h₂ hallowed)))

theorem stepAxiom_eventually {nm : String} {e : PExpr}
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hnmAllowed : isAllowedName nm = true)
    (he : Eventually fun d => e ∈ SPMF.support
      (genLExpr (G := SPMF) [] (opsOver [] s.octx) s.pctx [] [] d .bool)) :
    Eventually fun N => (([mkAxiomDecl nm e]), { s with reserved := nm :: s.reserved }) ∈
      SPMF.support (genDeclStep (G := SPMF) s (Bounds.uniform N fam)) :=
  he.mono fun _ h =>
    genDeclStep_complete_of_mem (.inr (.inr (.inl (genDeclAxiom_complete hnm hnmAllowed h))))

theorem stepDistinct_eventually {nm : String} {τ : LMonoTy} {constNames : List String}
    {C' : LContext CoreLParams} {constDecls : List Decl}
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hnmAllowed : isAllowedName nm = true)
    (hτ : Eventually fun d => τ ∈ SPMF.support
      (genNonRecursiveArgTy (G := SPMF) s.baseTypes s.tyCons [] d))
    (hτAllowed : mtyAllTyConsNames isAllowedName τ = true)
    (hlen2 : 2 ≤ constNames.length)
    (hconsts : constNames ∈ SPMF.support
      (DatatypeGen.genFreshNames (G := SPMF) (nm :: s.reserved) constNames.length))
    (hconstsAllowed : ∀ c ∈ constNames, isAllowedName c = true)
    (hadd : addConstants s.C τ constNames = some (C', constDecls)) :
    Eventually fun N => ((constDecls ++ [mkDistinctDecl nm (distinctElems τ constNames)]),
        { s with C := C', reserved := constNames ++ nm :: s.reserved }) ∈
      SPMF.support (genDeclStep (G := SPMF) s (Bounds.uniform N fam)) :=
  (hτ.and (le_eventually constNames.length)).mono fun _ ⟨h₁, h₂⟩ =>
    genDeclStep_complete_of_mem (.inr (.inr (.inr (.inl
      (genDeclDistinct_complete hnm hnmAllowed h₁ hτAllowed hlen2 (le_max_of_le_right h₂) hconsts
        hconstsAllowed hadd)))))

theorem stepDatatype_eventually {block : MutualDatatype Unit} {C' : LContext CoreLParams}
    (hblock : Eventually fun N => block ∈ SPMF.support
      (DatatypeGen.genMutuallyRecursiveDatatypes (G := SPMF)
        s.baseTypes (s.tyCons ++ s.dtCons) N N N N N N s.reserved))
    (hnamesAllowed : ∀ d ∈ block, isAllowedName d.name = true)
    (hnamesNotLocal : ∀ d ∈ block, isLocalTypeName d.name = false)
    (hC : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      _ s.C block = .ok C') :
    Eventually fun N => (([.type (.data block) .empty]),
        { s with C := C'
                 reserved := block.map (·.name) ++ s.reserved
                 dtCons := block.map (fun d => (d.name, d.typeArgs.length)) ++ s.dtCons
                 octx := OpCtx.ofList (adtDerivedOps block fam ++ s.octx.ops)
                 pctx := adtDerivedPolyOps block fam ++ s.pctx
                 derivedPctx := adtDerivedPolyOps block fam ++ s.derivedPctx }) ∈
      SPMF.support (genDeclStep (G := SPMF) s (Bounds.uniform N fam)) :=
  hblock.mono fun _ h => genDeclStep_complete_of_mem (.inr (.inr (.inr (.inr (.inl
    (genDeclDatatype_complete h hnamesAllowed hnamesNotLocal hC))))))

theorem stepProcedure_eventually {proc : Procedure} {nm : String} {L : Nat}
    (hname : proc.header.name = ⟨nm, ()⟩)
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hallowed : isAllowedName nm = true)
    (hproc : ∃ K, Eventually fun size => ∀ len k, L ≤ len → K ≤ k →
      proc ∈ SPMF.support (genProcedure (G := SPMF) s.octx s.procs s.C s.Γ size len s.derivedPctx
        (maxStmtSeqLen := k))) :
    Eventually fun N => ([.proc proc .empty], procStepState s proc nm) ∈
      SPMF.support (genDeclStep (G := SPMF) s (Bounds.uniform N fam)) := by
  obtain ⟨K, N, h⟩ := genDeclProcedure_complete hname hnm hallowed hproc
  exact ⟨max K (max N L), fun M hM => genDeclStep_complete_of_mem (.inr (.inr (.inr (.inr (.inr
    (.inr (.inl (h (Bounds.uniform M fam) (show N ≤ M by omega) (show L ≤ M by omega)
      (show K ≤ M by omega)))))))))⟩

theorem stepRecFuncBlock_eventually {names : List String} {funcs : List Function}
    {sStub s₁ : GenState}
    (hlen : 1 ≤ names.length)
    (hnames : DeclNamesReach s.reserved names)
    (hfnames : funcs.map (fun f => f.name.name) = names)
    (hsigs : ∀ f ∈ funcs, Eventually fun d => funcStub f ∈ SPMF.support (genFuncSig (G := SPMF)
      f.name.name d
      (fun x => (StrataGenerators.Stmt.functionNames s.C).contains x || names.contains x)
      s.dtCons))
    (hstub : s.registerFuncs (funcs.map funcStub) = some sStub)
    (hparts : ∀ f ∈ funcs, Eventually fun d => f ∈ SPMF.support (genFuncParts (G := SPMF)
      (pure true) [] sStub.octx d ((funcs.map funcStub).filterMap funcPolyOpEntry ++ s.derivedPctx)
      s.dtCons (funcStub f)))
    (hnoInline : ∀ f ∈ funcs, ∀ a ∈ f.attr, a ≠ .inline)
    (hreg : s.registerFuncs funcs = some s₁) :
    Eventually fun N =>
      ([.recFuncBlock funcs .empty], { s₁ with reserved := names ++ s.reserved }) ∈
        SPMF.support (genDeclStep (G := SPMF) s (Bounds.uniform N fam)) :=
  ((le_eventually names.length).and ((Eventually.forall_mem funcs hsigs).and
    (Eventually.forall_mem funcs hparts))).mono fun _ ⟨h₁, h₂, h₃⟩ =>
    genDeclStep_complete_of_mem (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (genDeclRecFuncBlock_complete hlen (le_max_of_le_right h₁) hnames hfnames h₂ hstub h₃
        hnoInline hreg))))))))

end steps

-- ── Traces and whole programs ───────────────────────────────────────────────

/-- The state at the end of a trace of declaration steps from `s`. -/
def traceFinal : GenState → List (List Decl × GenState) → GenState
  | s, [] => s
  | _, (_, s') :: rest => traceFinal s' rest

/-- Each step of the trace, from the state the previous step leaves, is reachable by
    `genDeclStep` at every large enough uniform bound with the families `fam`. -/
def TraceReach (fam : DerivedOpFamilies) : GenState → List (List Decl × GenState) → Prop
  | _, [] => True
  | s, (ds, s') :: rest =>
      (Eventually fun N =>
        (ds, s') ∈ SPMF.support (genDeclStep (G := SPMF) s (Bounds.uniform N fam))) ∧
      TraceReach fam s' rest

/-- **The fold, at every large enough uniform bound.** A trace whose steps are each eventually
    reachable is, as a whole, eventually reachable by `genDeclsFold`. -/
theorem genDeclsFold_complete_eventually (fam : DerivedOpFamilies) :
    ∀ (steps : List (List Decl × GenState)) (s : GenState), TraceReach fam s steps →
      Eventually fun N => ((steps.map Prod.fst).flatten, traceFinal s steps) ∈
        SPMF.support (genDeclsFold (G := SPMF) s (Bounds.uniform N fam) steps.length)
  | [], s, _ => .of_forall fun _ => by
    simp [traceFinal, genDeclsFold]
  | (ds, s') :: rest, s, ⟨h, hrest⟩ =>
    (h.and (genDeclsFold_complete_eventually fam rest s' hrest)).mono fun _ ⟨h₁, h₂⟩ => by
      simpa [traceFinal] using genDeclsFold_cons_complete h₁ h₂

/-- **Whole-program completeness, for some `Bounds`.** If each declaration step of a trace
    from `initState` is reachable at every large enough uniform bound (`TraceReach`, built from the
    `step*_eventually` lemmas), then `genProgram` reaches the program of the trace's declarations at
    some `b : Bounds` with the families `fam`. -/
theorem genProgram_complete_eventually (fam : DerivedOpFamilies)
    (steps : List (List Decl × GenState)) (h : TraceReach fam initState steps) :
    ∃ b : Bounds, b.derivedFamilies = fam ∧
      Program.mk (decls := (steps.map Prod.fst).flatten) ∈
        SPMF.support (genProgram (G := SPMF) steps.length b) := by
  obtain ⟨N, hN⟩ := genDeclsFold_complete_eventually fam steps initState h
  exact ⟨Bounds.uniform N fam, rfl, genProgram_complete_of_fold (hN N (Nat.le_refl N))⟩

end ProgramGen
