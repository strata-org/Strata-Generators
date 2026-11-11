import StrataGenerators.ProgramGen.CompleteProcedure

/-!
# Whole-program completeness, for some bounds record

`genProgram_complete_of_fold` composes per-step reachability at one *fixed* bounds record `b`. This
module removes the bounds from the statement. `genProgram_complete_eventually` says that if each
declaration step of a trace is reachable at every large enough bounds record, the whole program is
reachable by `genProgram … b` for *some* `b`.

The bounds records are ordered field by field (`Bounds.Le`): every numeric field is at most the
other's, and the derived-operator families (`derivedFamilies`, which is not a size) are equal.
`BoundsEventually fam P` says that `P` holds at every bounds record above some threshold with the
families `fam`. Two such conditions combine through the field-wise maximum (`Bounds.sup`), so a
finite trace has one threshold that serves every step.

The per-kind lemmas `step*_eventually` lift each declaration kind's step lemma to this form. A
premise that bounds a length by a field holds eventually by itself. A premise about a
sub-generator's support at one field (`genNonRecursiveArgTy` at `tySize`, `genLExpr` at `exprDepth`,
`genFuncSig` and `genFuncParts` at `funcDepth`) becomes an `Eventually` premise in that field, and
the datatype block's premise, which reads several fields, becomes a `BoundsEventually` premise. The
procedure step reads its bounds through `genDeclProcedure_complete`, so it inherits the size-free
statement completeness.

A plain function declaration (`genDeclFunction`) has no step lemma yet, so a trace covered here
declares its functions in recursive function blocks.
-/

open Lambda RandomChoice Core Imperative
open StrataGenerators StrataGenerators.Procedure StrataGenerators.Stmt.SpecComplete
open StrataGenerators.Stmt (isLocalTypeName)

namespace ProgramGen

-- ── The order on bounds records ─────────────────────────────────────────────

/-- `b₀` is below `b` in every numeric field, and the two have the same derived-operator
    families. -/
structure Bounds.Le (b₀ b : Bounds) : Prop where
  maxTyConArity : b₀.maxTyConArity ≤ b.maxTyConArity
  maxAliasTyParams : b₀.maxAliasTyParams ≤ b.maxAliasTyParams
  tySize : b₀.tySize ≤ b.tySize
  exprDepth : b₀.exprDepth ≤ b.exprDepth
  funcDepth : b₀.funcDepth ≤ b.funcDepth
  maxRecFuncs : b₀.maxRecFuncs ≤ b.maxRecFuncs
  maxDistinctVars : b₀.maxDistinctVars ≤ b.maxDistinctVars
  maxExtraDatatypes : b₀.maxExtraDatatypes ≤ b.maxExtraDatatypes
  maxTyParams : b₀.maxTyParams ≤ b.maxTyParams
  maxExtraBaseConstrs : b₀.maxExtraBaseConstrs ≤ b.maxExtraBaseConstrs
  maxRecConstrs : b₀.maxRecConstrs ≤ b.maxRecConstrs
  maxArgs : b₀.maxArgs ≤ b.maxArgs
  maxDatatypeSize : b₀.maxDatatypeSize ≤ b.maxDatatypeSize
  procSize : b₀.procSize ≤ b.procSize
  procLen : b₀.procLen ≤ b.procLen
  maxStmtSeqLen : b₀.maxStmtSeqLen ≤ b.maxStmtSeqLen
  derivedFamilies : b₀.derivedFamilies = b.derivedFamilies

theorem Bounds.Le.refl (b : Bounds) : b.Le b :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, rfl⟩

theorem Bounds.Le.trans {b₀ b₁ b₂ : Bounds} (h₁ : b₀.Le b₁) (h₂ : b₁.Le b₂) : b₀.Le b₂ :=
  ⟨Nat.le_trans h₁.maxTyConArity h₂.maxTyConArity,
   Nat.le_trans h₁.maxAliasTyParams h₂.maxAliasTyParams,
   Nat.le_trans h₁.tySize h₂.tySize,
   Nat.le_trans h₁.exprDepth h₂.exprDepth,
   Nat.le_trans h₁.funcDepth h₂.funcDepth,
   Nat.le_trans h₁.maxRecFuncs h₂.maxRecFuncs,
   Nat.le_trans h₁.maxDistinctVars h₂.maxDistinctVars,
   Nat.le_trans h₁.maxExtraDatatypes h₂.maxExtraDatatypes,
   Nat.le_trans h₁.maxTyParams h₂.maxTyParams,
   Nat.le_trans h₁.maxExtraBaseConstrs h₂.maxExtraBaseConstrs,
   Nat.le_trans h₁.maxRecConstrs h₂.maxRecConstrs,
   Nat.le_trans h₁.maxArgs h₂.maxArgs,
   Nat.le_trans h₁.maxDatatypeSize h₂.maxDatatypeSize,
   Nat.le_trans h₁.procSize h₂.procSize,
   Nat.le_trans h₁.procLen h₂.procLen,
   Nat.le_trans h₁.maxStmtSeqLen h₂.maxStmtSeqLen,
   h₁.derivedFamilies.trans h₂.derivedFamilies⟩

/-- The field-wise maximum of two bounds records, with the first one's families. -/
def Bounds.sup (b₁ b₂ : Bounds) : Bounds where
  maxTyConArity := max b₁.maxTyConArity b₂.maxTyConArity
  maxAliasTyParams := max b₁.maxAliasTyParams b₂.maxAliasTyParams
  tySize := max b₁.tySize b₂.tySize
  exprDepth := max b₁.exprDepth b₂.exprDepth
  funcDepth := max b₁.funcDepth b₂.funcDepth
  maxRecFuncs := max b₁.maxRecFuncs b₂.maxRecFuncs
  maxDistinctVars := max b₁.maxDistinctVars b₂.maxDistinctVars
  maxExtraDatatypes := max b₁.maxExtraDatatypes b₂.maxExtraDatatypes
  maxTyParams := max b₁.maxTyParams b₂.maxTyParams
  maxExtraBaseConstrs := max b₁.maxExtraBaseConstrs b₂.maxExtraBaseConstrs
  maxRecConstrs := max b₁.maxRecConstrs b₂.maxRecConstrs
  maxArgs := max b₁.maxArgs b₂.maxArgs
  maxDatatypeSize := max b₁.maxDatatypeSize b₂.maxDatatypeSize
  procSize := max b₁.procSize b₂.procSize
  procLen := max b₁.procLen b₂.procLen
  maxStmtSeqLen := max b₁.maxStmtSeqLen b₂.maxStmtSeqLen
  derivedFamilies := b₁.derivedFamilies

theorem Bounds.le_sup_left (b₁ b₂ : Bounds) : b₁.Le (b₁.sup b₂) :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, rfl⟩

theorem Bounds.le_sup_right {b₁ b₂ : Bounds} (h : b₂.derivedFamilies = b₁.derivedFamilies) :
    b₂.Le (b₁.sup b₂) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, h⟩

/-- The least bounds record with the families `fam`: every numeric field is `0`. -/
def Bounds.base (fam : DerivedOpFamilies) : Bounds where
  maxTyConArity := 0
  maxAliasTyParams := 0
  tySize := 0
  exprDepth := 0
  funcDepth := 0
  maxRecFuncs := 0
  maxDistinctVars := 0
  maxExtraDatatypes := 0
  maxTyParams := 0
  maxExtraBaseConstrs := 0
  maxRecConstrs := 0
  maxArgs := 0
  maxDatatypeSize := 0
  procSize := 0
  procLen := 0
  maxStmtSeqLen := 0
  derivedFamilies := fam

-- ── "At every large enough bounds record" ──────────────────────────────────

/-- `P b` holds at every bounds record `b` above some threshold with the families `fam`. -/
def BoundsEventually (fam : DerivedOpFamilies) (P : Bounds → Prop) : Prop :=
  ∃ b₀ : Bounds, b₀.derivedFamilies = fam ∧ ∀ b, b₀.Le b → P b

theorem BoundsEventually.of_forall {fam : DerivedOpFamilies} {P : Bounds → Prop} (h : ∀ b, P b) :
    BoundsEventually fam P := ⟨Bounds.base fam, rfl, fun b _ => h b⟩

theorem BoundsEventually.mono {fam : DerivedOpFamilies} {P Q : Bounds → Prop}
    (hP : BoundsEventually fam P) (h : ∀ b, P b → Q b) : BoundsEventually fam Q := by
  obtain ⟨b₀, hf, hb⟩ := hP; exact ⟨b₀, hf, fun b hle => h b (hb b hle)⟩

theorem BoundsEventually.and {fam : DerivedOpFamilies} {P Q : Bounds → Prop}
    (hP : BoundsEventually fam P) (hQ : BoundsEventually fam Q) :
    BoundsEventually fam fun b => P b ∧ Q b := by
  obtain ⟨b₁, hf₁, h₁⟩ := hP; obtain ⟨b₂, hf₂, h₂⟩ := hQ
  exact ⟨b₁.sup b₂, hf₁, fun b hle =>
    ⟨h₁ b ((Bounds.le_sup_left b₁ b₂).trans hle),
     h₂ b ((Bounds.le_sup_right (hf₂.trans hf₁.symm)).trans hle)⟩⟩

/-- Every bounds record above a threshold with the families `fam` has the families `fam`. -/
theorem BoundsEventually.families (fam : DerivedOpFamilies) :
    BoundsEventually fam fun b => b.derivedFamilies = fam :=
  ⟨Bounds.base fam, rfl, fun _ hle => hle.derivedFamilies.symm⟩

theorem BoundsEventually.maxTyConArity {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxTyConArity := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxTyConArity := N }, rfl, fun b hle => hN _ hle.maxTyConArity⟩

theorem BoundsEventually.maxAliasTyParams {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxAliasTyParams := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxAliasTyParams := N }, rfl, fun b hle => hN _ hle.maxAliasTyParams⟩

theorem BoundsEventually.tySize {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.tySize := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with tySize := N }, rfl, fun b hle => hN _ hle.tySize⟩

theorem BoundsEventually.exprDepth {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.exprDepth := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with exprDepth := N }, rfl, fun b hle => hN _ hle.exprDepth⟩

theorem BoundsEventually.funcDepth {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.funcDepth := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with funcDepth := N }, rfl, fun b hle => hN _ hle.funcDepth⟩

theorem BoundsEventually.maxRecFuncs {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxRecFuncs := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxRecFuncs := N }, rfl, fun b hle => hN _ hle.maxRecFuncs⟩

theorem BoundsEventually.maxDistinctVars {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxDistinctVars := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxDistinctVars := N }, rfl, fun b hle => hN _ hle.maxDistinctVars⟩

theorem BoundsEventually.maxExtraDatatypes {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxExtraDatatypes := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxExtraDatatypes := N }, rfl, fun b hle => hN _ hle.maxExtraDatatypes⟩

theorem BoundsEventually.maxTyParams {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxTyParams := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxTyParams := N }, rfl, fun b hle => hN _ hle.maxTyParams⟩

theorem BoundsEventually.maxExtraBaseConstrs {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxExtraBaseConstrs := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxExtraBaseConstrs := N }, rfl, fun b hle => hN _ hle.maxExtraBaseConstrs⟩

theorem BoundsEventually.maxRecConstrs {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxRecConstrs := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxRecConstrs := N }, rfl, fun b hle => hN _ hle.maxRecConstrs⟩

theorem BoundsEventually.maxArgs {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxArgs := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxArgs := N }, rfl, fun b hle => hN _ hle.maxArgs⟩

theorem BoundsEventually.maxDatatypeSize {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxDatatypeSize := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxDatatypeSize := N }, rfl, fun b hle => hN _ hle.maxDatatypeSize⟩

theorem BoundsEventually.procSize {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.procSize := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with procSize := N }, rfl, fun b hle => hN _ hle.procSize⟩

theorem BoundsEventually.procLen {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.procLen := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with procLen := N }, rfl, fun b hle => hN _ hle.procLen⟩

theorem BoundsEventually.maxStmtSeqLen {fam : DerivedOpFamilies} {P : Nat → Prop} (h : Eventually P) :
    BoundsEventually fam fun b => P b.maxStmtSeqLen := by
  obtain ⟨N, hN⟩ := h; exact ⟨{ Bounds.base fam with maxStmtSeqLen := N }, rfl, fun b hle => hN _ hle.maxStmtSeqLen⟩

-- ── Per-kind steps, at every large enough bounds record ─────────────────────

section steps
variable {fam : DerivedOpFamilies} {s : GenState}

theorem stepAbstract_eventually {nm : String} {ar : Nat} {C' : LContext CoreLParams}
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hnmAllowed : isAllowedName nm = true) (hnmNotLocal : isLocalTypeName nm = false)
    (hC : s.C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    BoundsEventually fam fun b => (([mkAbstractTypeDecl nm ar]), s.addAbstract nm ar C') ∈
      SPMF.support (genDeclStep (G := SPMF) s b) :=
  (BoundsEventually.maxTyConArity (le_eventually ar)).mono fun _ h =>
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
    BoundsEventually fam fun b => (([mkAliasDecl nm body]),
        { s with
          Γ := { s.Γ with aliases :=
                   { typeArgs := (LMonoTy.freeVars body).uniq, name := nm, type := body }
                     :: s.Γ.aliases }
          reserved := nm :: s.reserved }) ∈ SPMF.support (genDeclStep (G := SPMF) s b) :=
  ((BoundsEventually.maxAliasTyParams (le_eventually tyParams.length)).and
    (BoundsEventually.tySize hbody)).mono fun _ ⟨h₁, h₂⟩ =>
    genDeclStep_complete_of_mem (.inr (.inl
      (genDeclAlias_complete hnm hnmAllowed hnmNotLocal h₁ hparams h₂ hallowed)))

theorem stepAxiom_eventually {nm : String} {e : PExpr}
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hnmAllowed : isAllowedName nm = true)
    (he : Eventually fun d => e ∈ SPMF.support
      (genLExpr (G := SPMF) [] (opsOver [] s.octx) s.pctx [] [] d .bool)) :
    BoundsEventually fam fun b => (([mkAxiomDecl nm e]), { s with reserved := nm :: s.reserved }) ∈
      SPMF.support (genDeclStep (G := SPMF) s b) :=
  (BoundsEventually.exprDepth he).mono fun _ h =>
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
    BoundsEventually fam fun b => ((constDecls ++ [mkDistinctDecl nm (distinctElems τ constNames)]),
        { s with C := C', reserved := constNames ++ nm :: s.reserved }) ∈
      SPMF.support (genDeclStep (G := SPMF) s b) :=
  ((BoundsEventually.tySize hτ).and
    (BoundsEventually.maxDistinctVars (le_eventually constNames.length))).mono fun _ ⟨h₁, h₂⟩ =>
    genDeclStep_complete_of_mem (.inr (.inr (.inr (.inl
      (genDeclDistinct_complete hnm hnmAllowed h₁ hτAllowed hlen2 (le_max_of_le_right h₂) hconsts
        hconstsAllowed hadd)))))

theorem stepDatatype_eventually {block : MutualDatatype Unit} {C' : LContext CoreLParams}
    (hblock : BoundsEventually fam fun b => block ∈ SPMF.support
      (DatatypeGen.genMutuallyRecursiveDatatypes (G := SPMF)
        s.baseTypes (s.tyCons ++ s.dtCons) b.maxExtraDatatypes b.maxTyParams
        b.maxExtraBaseConstrs b.maxRecConstrs b.maxArgs b.maxDatatypeSize s.reserved))
    (hnamesAllowed : ∀ d ∈ block, isAllowedName d.name = true)
    (hnamesNotLocal : ∀ d ∈ block, isLocalTypeName d.name = false)
    (hC : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      _ s.C block = .ok C') :
    BoundsEventually fam fun b => (([.type (.data block) .empty]),
        { s with C := C'
                 reserved := block.map (·.name) ++ s.reserved
                 dtCons := block.map (fun d => (d.name, d.typeArgs.length)) ++ s.dtCons
                 octx := OpCtx.ofList (adtDerivedOps block fam ++ s.octx.ops)
                 pctx := adtDerivedPolyOps block fam ++ s.pctx
                 derivedPctx := adtDerivedPolyOps block fam ++ s.derivedPctx }) ∈
      SPMF.support (genDeclStep (G := SPMF) s b) :=
  (hblock.and (BoundsEventually.families fam)).mono fun b ⟨h, hf⟩ => by
    subst hf
    exact genDeclStep_complete_of_mem (.inr (.inr (.inr (.inr (.inl
      (genDeclDatatype_complete h hnamesAllowed hnamesNotLocal hC))))))

theorem stepProcedure_eventually {proc : Procedure} {nm : String} {L : Nat}
    (hname : proc.header.name = ⟨nm, ()⟩)
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hallowed : isAllowedName nm = true)
    (hproc : ∃ K, Eventually fun size => ∀ len k, L ≤ len → K ≤ k →
      proc ∈ SPMF.support (genProcedure (G := SPMF) s.octx s.procs s.C s.Γ size len s.derivedPctx
        (maxStmtSeqLen := k))) :
    BoundsEventually fam fun b => ([.proc proc .empty], procStepState s proc nm) ∈
      SPMF.support (genDeclStep (G := SPMF) s b) := by
  obtain ⟨K, N, h⟩ := genDeclProcedure_complete hname hnm hallowed hproc
  exact ⟨{ Bounds.base fam with procSize := N, procLen := L, maxStmtSeqLen := K }, rfl,
    fun b hle => genDeclStep_complete_of_mem (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      (h b hle.procSize hle.procLen hle.maxStmtSeqLen))))))))⟩

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
    BoundsEventually fam fun b =>
      ([.recFuncBlock funcs .empty], { s₁ with reserved := names ++ s.reserved }) ∈
        SPMF.support (genDeclStep (G := SPMF) s b) :=
  ((BoundsEventually.maxRecFuncs (le_eventually names.length)).and
    (BoundsEventually.funcDepth ((Eventually.forall_mem funcs hsigs).and
      (Eventually.forall_mem funcs hparts)))).mono fun _ ⟨h₁, h₂, h₃⟩ =>
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
    `genDeclStep` at every large enough bounds record with the families `fam`. -/
def TraceReach (fam : DerivedOpFamilies) : GenState → List (List Decl × GenState) → Prop
  | _, [] => True
  | s, (ds, s') :: rest =>
      BoundsEventually fam (fun b => (ds, s') ∈ SPMF.support (genDeclStep (G := SPMF) s b)) ∧
      TraceReach fam s' rest

/-- **The fold, at every large enough bounds record.** A trace whose steps are each eventually
    reachable is, as a whole, eventually reachable by `genDeclsFold`. -/
theorem genDeclsFold_complete_eventually (fam : DerivedOpFamilies) :
    ∀ (steps : List (List Decl × GenState)) (s : GenState), TraceReach fam s steps →
      BoundsEventually fam fun b => ((steps.map Prod.fst).flatten, traceFinal s steps) ∈
        SPMF.support (genDeclsFold (G := SPMF) s b steps.length)
  | [], s, _ => .of_forall fun b => by
    simp [traceFinal, genDeclsFold]
  | (ds, s') :: rest, s, ⟨h, hrest⟩ =>
    (h.and (genDeclsFold_complete_eventually fam rest s' hrest)).mono fun _ ⟨h₁, h₂⟩ => by
      simpa [traceFinal] using genDeclsFold_cons_complete h₁ h₂

/-- **Whole-program completeness, for some bounds record.** If each declaration step of a trace
    from `initState` is reachable at every large enough bounds record (`TraceReach`, built from the
    `step*_eventually` lemmas), then `genProgram` reaches the program of the trace's declarations at
    some bounds record with the families `fam`. -/
theorem genProgram_complete_eventually (fam : DerivedOpFamilies)
    (steps : List (List Decl × GenState)) (h : TraceReach fam initState steps) :
    ∃ b : Bounds, b.derivedFamilies = fam ∧
      Program.mk (decls := (steps.map Prod.fst).flatten) ∈
        SPMF.support (genProgram (G := SPMF) steps.length b) := by
  obtain ⟨b, hb, hP⟩ := genDeclsFold_complete_eventually fam steps initState h
  exact ⟨b, hb, genProgram_complete_of_fold (hP b (Bounds.Le.refl b))⟩

end ProgramGen
