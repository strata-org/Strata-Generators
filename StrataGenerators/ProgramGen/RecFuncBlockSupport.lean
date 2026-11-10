import StrataGenerators.ProgramGen
import StrataGenerators.FunctionHasTypeAGen

/-!
# The shape of a recursive-function-block step

What `genDeclRecFuncBlock` emits, and the fields of the fold state that
`GenState.registerFuncs` leaves unchanged.
-/

open Lambda RandomChoice Core Core.TypeSpec

namespace ProgramGen

/-- Two lists related elementwise by `R` have equal images when `f` and `g` agree on related
    elements. -/
theorem map_eq_map_of_forall₂ {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (hfg : ∀ a b, R a b → f a = g b) :
    l₁.map f = l₂.map g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, hfg _ _ hab, ih]

/-- Registering functions leaves the reserved names, the callable procedures and the derived
    schemes unchanged, keeps every polymorphic scheme, and adds the scheme of each registered
    polymorphic function. -/
theorem registerFuncs_fields {s s' : GenState} {fs : List Function}
    (h : s.registerFuncs fs = some s') :
    s'.reserved = s.reserved ∧ s'.procs = s.procs ∧ s'.derivedPctx = s.derivedPctx ∧
      (∀ p ∈ s.pctx, p ∈ s'.pctx) ∧
      ∀ f ∈ fs, ∀ e, funcPolyOpEntry f = some e → e ∈ s'.pctx := by
  induction fs generalizing s with
  | nil =>
    simp only [GenState.registerFuncs, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, fun _ hp => hp, fun _ hf => absurd hf List.not_mem_nil⟩
  | cons f fs ih =>
    simp only [GenState.registerFuncs] at h
    split at h
    · rename_i C' _
      obtain ⟨hres, hprocs, hder, hmono, hpoly⟩ := ih h
      have hgrow : ∀ p ∈ s.pctx, p ∈ (s.registerFunc C' f).pctx := by
        intro p hp
        simp only [GenState.registerFunc]
        split
        · exact List.mem_append_left _ hp
        · exact hp
      refine ⟨hres, hprocs, hder, fun p hp => hmono p (hgrow p hp), ?_⟩
      intro g hg e he
      rcases List.mem_cons.mp hg with rfl | hg
      · refine hmono e ?_
        simp only [GenState.registerFunc, he]
        exact List.mem_append_right _ (List.mem_replicate.mpr ⟨by decide, rfl⟩)
      · exact hpoly g hg e he
    · exact absurd h (by simp)

/-- A step of `genDeclRecFuncBlock` emits nothing, or a block whose members are drawn as follows:
    fresh names, a signature for each name, the stubs registered as `sStub`, each member's parts
    drawn against `sStub` and the stubs' schemes, and the members (without `inline`) registered
    as `s₁`, whose reserved names grow by the members' names. -/
theorem genDeclRecFuncBlock_support {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SPMF.support (genDeclRecFuncBlock (G := SPMF) s b)) :
    (ds = [] ∧ s' = s) ∨
    ∃ (k : Nat) (names : List String) (stubs : List Function) (sStub : GenState)
      (drawn : List Function) (s₁ : GenState),
      1 ≤ k ∧ names ∈ SPMF.support (genDeclNames (G := SPMF) s.reserved k) ∧
      List.Forall₂ (fun st nm => st ∈ SPMF.support (genFuncSig (G := SPMF) nm b.funcDepth
        (fun x => (StrataGenerators.Stmt.functionNames s.C).contains x || names.contains x)
        s.dtCons)) stubs names ∧
      s.registerFuncs stubs = some sStub ∧
      List.Forall₂ (fun f st => f ∈ SPMF.support (genFuncParts (G := SPMF) (pure true) []
        sStub.octx b.funcDepth (stubs.filterMap funcPolyOpEntry ++ s.derivedPctx) s.dtCons st))
        drawn stubs ∧
      s.registerFuncs (drawn.map dropInline) = some s₁ ∧
      ds = [.recFuncBlock (drawn.map dropInline) .empty] ∧
      s' = { s₁ with reserved := names ++ s.reserved } := by
  refine IsSoundFor.of_mem_pair h ?_
  rw [IsSoundFor.iff_obs]; unfold genDeclRecFuncBlock; dsimp only
  walk [fun k => (isSoundFor_self_support (genDeclNames (G := SPMF) s.reserved k)).obs,
    fun α β (f : α → SPMF β) l => (isSoundFor_self_support (List.mapM (m := SPMF) f l)).obs]
  all_goals try exact .inl ⟨rfl, rfl⟩
  next k hk names hnames stubs hstubs sStub hstub drawn hdrawn s₁ hreg =>
    exact .inr ⟨k, names, stubs, sStub, drawn, s₁, hk.1, hnames,
      (mem_support_mapM_iff _ _ _).mp hstubs, hstub, (mem_support_mapM_iff _ _ _).mp hdrawn, hreg,
      rfl, rfl⟩

/-- The members of a drawn block carry the drawn names, in order. -/
theorem recFuncBlock_member_names {depth : Nat} {avoid : String → Bool}
    {genRecursive : SPMF Bool} {octx : OpCtx} {pctx : PolyOpCtx}
    {dts : List (String × Nat)} {names : List String} {stubs drawn : List Function}
    (hstubs : List.Forall₂ (fun st nm => st ∈ SPMF.support
      (genFuncSig (G := SPMF) nm depth avoid dts)) stubs names)
    (hdrawn : List.Forall₂ (fun f st => f ∈ SPMF.support
      (genFuncParts (G := SPMF) genRecursive [] octx depth pctx dts st)) drawn stubs) :
    (drawn.map dropInline).map (fun f => f.name.name) = names := by
  have hd : drawn.map (fun f => f.name.name) = stubs.map (fun f => f.name.name) := by
    refine map_eq_map_of_forall₂ hdrawn ?_
    intro f st hf
    show f.name.name = st.name.name
    rw [(StrataGenerators.Function.genFuncParts_shape hf).1]
  have hs : stubs.map (fun f => f.name.name) = names.map id := by
    refine map_eq_map_of_forall₂ hstubs ?_
    intro st nm hst
    show st.name.name = id nm
    rw [(StrataGenerators.Function.genFuncSig_stub hst).1]
    rfl
  have hdrop : (fun f : Function => f.name.name) ∘ dropInline = fun f => f.name.name := rfl
  rw [List.map_map, hdrop, hd, hs, List.map_id]

/-- A recursive-function-block step leaves the callable procedures unchanged. -/
theorem genDeclRecFuncBlock_procs {s : GenState} {b : Bounds} {ds : List Decl} {s' : GenState}
    (h : (ds, s') ∈ SPMF.support (genDeclRecFuncBlock (G := SPMF) s b)) :
    s'.procs = s.procs := by
  rcases genDeclRecFuncBlock_support h with ⟨_, rfl⟩ | ⟨_, _, _, _, _, s₁, _, _, _, _, _, hreg,
    _, rfl⟩
  · rfl
  · exact (registerFuncs_fields hreg).2.1

end ProgramGen
