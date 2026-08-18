import StrataGenerators.CmdHasTypeAGen
import Strata.Languages.Core.StatementTypeSpec

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen

/-!
# Soundness of the procedure-call statement generator

This file collects the *context-independent* helper lemmas required to establish
`genCallStmt` sound (the `.call` case of `genStmt_sound`, assembled in
`StmtHasTypeAGen.lean`). None of them refers to `genStmt`/`genStmts`, so they can
be developed and verified in isolation, without perturbing the (large) main
statement-generator proof.

- `mkArgs` — the call-argument recipe, with the two projection lemmas
  `getIn_mkArgs` / `getLhs_mkArgs` computing `getInputExprs` / `getLhs`.
- `call_recipe_inout_sound` — discharges the 7 premises of `CmdExtHasTypeA.call`.
- `initChain` / `insertAll` / `initChain_types` — the `init … nondet` chain that
  brings the required `M ∪ O` names into scope at their declared types.
- `StatementsHasTypeA_append` — chaining two statement-list judgments.
-/

namespace StrataGenerators.Stmt

open Core.TypeSpec

-- ── Procedure-signature context (call targets) ────────────────────────────

/-- A callee's signature description, stored *directly* with the shared in-out
    block leading both roles. This layout is not automatic for an arbitrary
    `P`-procedure; it is what `genProcedure` emits and what a call site must
    respect. `M` = in-out block, `I` = input-only block, `O` = output-only block,
    so `inputs = M ++ I` and `outputs = M ++ O`.

    `typeArgs` are the callee's **own** type parameters. A call site instantiates
    them with a concrete substitution `σ` (the `CmdExtHasType'.call` rule's
    existential `σ`), so the argument/target types the caller must supply are the
    *instantiated* blocks `substSig σ M` etc. The declared blocks `M`/`I`/`O` are
    stored un-instantiated (over `typeArgs`); `substSig` applies `σ` on demand.
    `typeArgs = []` recovers the monomorphic case (`σ = []`, `substSig [] = id`). -/
structure ProcSig where
  /-- The callee's name (matched against `Program.Procedure.find?`). -/
  pname : String
  /-- The callee's own type parameters (empty for a monomorphic callee). -/
  typeArgs : List TyIdentifier
  /-- The in-out (mutable) parameter block. -/
  M : @LMonoTySignature Unit
  /-- The input-only parameter block. -/
  I : @LMonoTySignature Unit
  /-- The output-only parameter block. -/
  O : @LMonoTySignature Unit

/-- The empty-signature procedure, so `ProcSig` is `Inhabited` (needed by
    `elements` and its support-inversion lemma inside `genCallStmt`). -/
instance : Inhabited ProcSig := ⟨⟨"", [], [], [], []⟩⟩

/-- Instantiate a parameter block's *types* by a substitution `σ`, leaving the
    parameter *names* untouched. Used to turn a callee's declared (over-`typeArgs`)
    block into the concrete block a call site must satisfy under the chosen
    instantiation `σ`. The call rule substitutes with `[σ]` (a single-scope
    substitution), so `substSig` does likewise. -/
def substSig (σ : List (TyIdentifier × LMonoTy)) (block : @LMonoTySignature Unit) :
    @LMonoTySignature Unit :=
  block.map (fun p => (p.1, LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) p.2))

/-- `substSig` preserves keys (it only rewrites types). -/
@[simp] theorem substSig_keys (σ : List (TyIdentifier × LMonoTy))
    (block : @LMonoTySignature Unit) : (substSig σ block).keys = block.keys := by
  simp only [substSig, ListMap.keys_eq_map_fst, List.map_map, Function.comp_def]

/-- `substSig` preserves length. -/
@[simp] theorem substSig_length (σ : List (TyIdentifier × LMonoTy))
    (block : @LMonoTySignature Unit) : (substSig σ block).length = block.length :=
  List.length_map ..

/-- The values of an instantiated block are the pointwise `subst [σ]` of the
    declared values. -/
theorem substSig_values (σ : List (TyIdentifier × LMonoTy))
    (block : @LMonoTySignature Unit) :
    (substSig σ block).values = block.values.map (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])) := by
  simp only [substSig, ListMap.values_eq_map_snd, List.map_map, Function.comp_def]

/-- `substSig` distributes over block append. -/
theorem substSig_append (σ : List (TyIdentifier × LMonoTy))
    (a b : @LMonoTySignature Unit) :
    substSig σ (a ++ b) = substSig σ a ++ substSig σ b :=
  List.map_append ..

/-- Pointwise key access commutes with `substSig` (keys are untouched). -/
theorem substSig_keys_getElem (σ : List (TyIdentifier × LMonoTy))
    (b : @LMonoTySignature Unit) (i : Nat) (h : i < (substSig σ b).keys.length)
    (h' : i < b.keys.length) : (substSig σ b).keys[i]'h = b.keys[i]'h' := by
  simp only [substSig_keys]

/-- Pointwise value access commutes with `substSig` via `subst [σ]`. -/
theorem substSig_values_getElem (σ : List (TyIdentifier × LMonoTy))
    (b : @LMonoTySignature Unit) (i : Nat) (h : i < (substSig σ b).values.length)
    (h' : i < b.values.length) :
    (substSig σ b).values[i]'h = LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (b.values[i]'h') := by
  simp only [substSig_values, List.getElem_map]

/-- With the empty (identity) instantiation, `substSig` is the identity: `subst [[]]`
    fixes every monotype, so both name and type are unchanged. This is the bridge
    that makes the monomorphic path (`typeArgs = []`, `σ = []`) a definitional
    special case of the polymorphic one. -/
@[simp] theorem substSig_nil (block : @LMonoTySignature Unit) :
    substSig [] block = block := by
  simp only [substSig]
  rw [show (fun p : Identifier Unit × LMonoTy =>
        (p.1, LMonoTy.subst (Strata.Util.HMaps.ofScopes [[]]) p.2)) = id from by
    funext p
    -- `ofScopes [[]]` is the single empty scope, and `subst` over it is the identity.
    simp only [id_eq, Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
      show Strata.Util.HMap.ofList ([] : List (TyIdentifier × LMonoTy))
        = Strata.Util.HMap.empty from rfl, LMonoTy.subst_single_empty],
    List.map_id]

/-- The set of callable procedures, each with its signature (shared in-out block
    leading both roles). -/
abbrev ProcSigCtx := List ProcSig

/-- `procs` faithfully describes callable procedures of `P`: each entry names a
    procedure of `P` whose type parameters are `s.typeArgs` and whose (declared,
    over-`typeArgs`) signature decomposes as recorded (shared block `M` leading both
    `inputs` and `outputs`), with the input-only keys disjoint from the LHS (`M ∪ O`)
    keys. Exactly the hypotheses `call_mixed_body_sound` consumes for the `.call`
    case, once the caller instantiates the blocks by its chosen `σ`.

    The callee may be **polymorphic** (`s.typeArgs ≠ []`): the call site picks a
    concrete instantiation `σ` and supplies arguments/targets at `substSig σ` of the
    declared blocks. The disjointness clause is stated over the *declared* keys, but
    `substSig` preserves keys (`substSig_keys`), so it transfers to the instantiated
    blocks unchanged. -/
def ProcSigCorresponds (procs : ProcSigCtx) (P : Program) : Prop :=
  ∀ s ∈ procs, ∃ proc, Program.Procedure.find? P s.pname = some proc ∧
    proc.header.typeArgs = s.typeArgs ∧
    proc.header.inputs = s.M ++ s.I ∧
    proc.header.outputs = s.M ++ s.O ∧
    (∀ i (hi : i < s.I.keys.length), (s.M ++ s.O).keys.contains (s.I.keys[i]'hi) = false)

/-- **The converse correspondence, for completeness (Part 1 of call completeness).**
    Whereas `ProcSigCorresponds` says every generator-side callee `s ∈ procs`
    resolves in `P` (what *soundness* needs — a generated call is well-typed),
    `ProcSigComplete` says the reverse: every procedure resolvable in `P` whose
    signature admits the `M`/`I`/`O` decomposition is *listed in* `procs` (what
    *completeness* needs — a well-typed call is reachable), recording its type
    parameters `typeArgs` so the call site can instantiate them. -/
def ProcSigComplete (procs : ProcSigCtx) (P : Program) : Prop :=
  ∀ pname proc typeArgs M I O,
    Program.Procedure.find? P pname = some proc →
    proc.header.typeArgs = typeArgs →
    proc.header.inputs = M ++ I →
    proc.header.outputs = M ++ O →
    (∀ i (hi : i < I.keys.length), (M ++ O).keys.contains (I.keys[i]'hi) = false) →
    ∃ s ∈ procs, s.pname = pname ∧ s.typeArgs = typeArgs ∧ s.M = M ∧ s.I = I ∧ s.O = O

-- ── filterMap helper lemmas ───────────────────────────────────────────────

/-- `filterMap` of a constantly-`none` function is empty. -/
theorem filterMap_const_none {α β} (l : List α) :
    List.filterMap (fun _ => (none : Option β)) l = [] := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih]

/-- `filterMap` of `some ∘ f` is `map f`. -/
theorem filterMap_some_comp {α β} (f : α → β) (l : List α) :
    List.filterMap (fun x => some (f x)) l = l.map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih]

-- ── ListMap append helpers ────────────────────────────────────────────────

/-- Keys distribute over `ListMap` append (which is `List.append`). -/
theorem lm_keys_append {α β} [DecidableEq α] (a b : ListMap α β) :
    (a ++ b).keys = a.keys ++ b.keys := by
  simp only [ListMap.keys_eq_map_fst]
  exact List.map_append ..

/-- Values distribute over `ListMap` append. -/
theorem lm_values_append {α β} [DecidableEq α] (a b : ListMap α β) :
    (a ++ b).values = a.values ++ b.values := by
  simp only [ListMap.values_eq_map_snd]
  exact List.map_append ..

/-- Length distributes over `ListMap` append. -/
@[simp]
theorem lm_length_append {α β} (a b : ListMap α β) :
    (a ++ b).length = a.length + b.length := List.length_append ..

/-- The values list has the same length as the map. -/
@[simp]
theorem lm_values_length {α β} (m : ListMap α β) : m.values.length = m.length := by
  simp only [ListMap.values_eq_map_snd, List.length_map]

-- ── mapM support inversion (public) ───────────────────────────────────────

/-- Membership in `List.mapM f l` on `SetGen.Set`: `args` is in the support iff
    each element is pointwise in the support of `f` at the corresponding input.
    A public re-statement of the private lemma in `HasTypeAGen.lean`, generic in
    the element/index types. -/
theorem mem_support_mapM_iff {α β} (f : α → SetGen.Set β)
    (inputs : List α) (outs : List β) :
    outs ∈ SetGen.support (List.mapM (m := SetGen.Set) f inputs) ↔
    List.Forall₂ (fun out σ => out ∈ SetGen.support (f σ)) outs inputs := by
  induction inputs generalizing outs with
  | nil =>
    simp only [List.mapM_nil, mem_support_pure_iff]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | cons σ rest ih =>
    simp only [List.mapM_cons, mem_support_bind_iff, mem_support_pure_iff]
    constructor
    · rintro ⟨x, hx, tl, htl, rfl⟩
      exact .cons hx ((ih _).mp htl)
    · intro h
      match outs, h with
      | _ :: _, .cons harg htail =>
        exact ⟨_, harg, _, (ih _).mpr htail, rfl⟩

/-- Membership on the left of a `List.Forall₂`: every element of the first list is related
    to some element of the second. (Lean core has no `List.Forall₂.mem_left`.) -/
theorem forall₂_mem_left {α β} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ a ∈ as, ∃ b ∈ bs, R a b := by
  intro as bs h
  induction h with
  | nil => intro a ha; simp at ha
  | cons hab _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hR⟩ := ih a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hR⟩

/-- Every value bound by a single-scope substitution built with `HMaps.ofScopes` comes from
    the association list it was built from. Bridges the `find?` side condition of
    `subst_wellKinded` to a membership fact about the sampled instantiation. -/
theorem mem_values_of_find?_ofScopes (σ : List (TyIdentifier × LMonoTy))
    (v : TyIdentifier) (t : LMonoTy)
    (h : Strata.Util.HMaps.find? (Strata.Util.HMaps.ofScopes [σ]) v = some t) :
    t ∈ σ.map Prod.snd := by
  rw [show Strata.Util.HMaps.ofScopes [σ] = [Strata.Util.HMap.ofList σ] from rfl,
    Strata.Util.HMaps.find?_single_scope] at h
  exact Strata.Util.HMap.mem_values_ofList σ t (Strata.Util.HMap.find?_mem_values _ h)

/-- **Well-kindedness survives a `substSig`.** If a block's declared types and the sampled
    instantiation are all well-kinded in `C`, so is every instantiated type. This is what
    discharges the `WellKindedTy` premise upstream's `init` rules impose on the types the
    call generator's inline `init` chain stores. -/
theorem substSig_values_wellKinded {C : LContext CoreLParams}
    (σ : List (TyIdentifier × LMonoTy)) (block : @LMonoTySignature Unit)
    (hσ : ∀ t ∈ σ.map Prod.snd, C.WellKindedTy t)
    (hblock : ∀ ty ∈ block.values, C.WellKindedTy ty) :
    ∀ ty ∈ (substSig σ block).values, C.WellKindedTy ty := by
  intro ty hty
  rw [substSig_values, List.mem_map] at hty
  obtain ⟨ty0, hty0, rfl⟩ := hty
  exact subst_wellKinded _
    (fun v t hfind => hσ t (mem_values_of_find?_ofScopes σ v t hfind))
    ty0 (hblock ty0 hty0)

-- ── The call-argument recipe ──────────────────────────────────────────────

/-- Merge two lists under a Boolean mask, and keep the relative order inside each
    list. `true` takes the next element of `xs`, and `false` takes the next element
    of `ys`. When the mask ends, or when the chosen list is empty, the rest of both
    lists follows. Every order-preserving interleaving of `xs` and `ys` is
    `mergeBy bs xs ys` for some `bs`. -/
def mergeBy {α : Type} : List Bool → List α → List α → List α
  | [], xs, ys => xs ++ ys
  | true :: bs, x :: xs, ys => x :: mergeBy bs xs ys
  | true :: bs, [], ys => mergeBy bs [] ys
  | false :: bs, xs, y :: ys => y :: mergeBy bs xs ys
  | false :: bs, xs, [] => mergeBy bs xs []

/-- A `filterMap` that drops every element of `ys` sees `mergeBy bs xs ys` as `xs`.
    The merge keeps the relative order inside `xs`. -/
theorem filterMap_mergeBy_left {α β : Type} (f : α → Option β) (bs : List Bool) :
    ∀ (xs ys : List α), (∀ a ∈ ys, f a = none) →
      (mergeBy bs xs ys).filterMap f = xs.filterMap f := by
  induction bs with
  | nil =>
    intro xs ys hy
    rw [mergeBy, List.filterMap_append,
      List.filterMap_eq_nil_iff.mpr (fun a ha => hy a ha), List.append_nil]
  | cons b bs ih =>
    intro xs ys hy
    cases b with
    | true =>
      cases xs with
      | nil => rw [mergeBy, ih [] ys hy]
      | cons x xs => rw [mergeBy, List.filterMap_cons, List.filterMap_cons, ih xs ys hy]
    | false =>
      cases ys with
      | nil => rw [mergeBy, ih xs [] (by simp)]
      | cons y ys =>
        rw [mergeBy, List.filterMap_cons, hy y List.mem_cons_self,
          ih xs ys (fun a ha => hy a (List.mem_cons_of_mem y ha))]

/-- A `filterMap` that drops every element of `xs` sees `mergeBy bs xs ys` as `ys`. -/
theorem filterMap_mergeBy_right {α β : Type} (f : α → Option β) (bs : List Bool) :
    ∀ (xs ys : List α), (∀ a ∈ xs, f a = none) →
      (mergeBy bs xs ys).filterMap f = ys.filterMap f := by
  induction bs with
  | nil =>
    intro xs ys hx
    rw [mergeBy, List.filterMap_append,
      List.filterMap_eq_nil_iff.mpr (fun a ha => hx a ha), List.nil_append]
  | cons b bs ih =>
    intro xs ys hx
    cases b with
    | true =>
      cases xs with
      | nil => rw [mergeBy, ih [] ys (by simp)]
      | cons x xs =>
        rw [mergeBy, List.filterMap_cons, hx x List.mem_cons_self,
          ih xs ys (fun a ha => hx a (List.mem_cons_of_mem x ha))]
    | false =>
      cases ys with
      | nil => rw [mergeBy, ih xs [] hx]
      | cons y ys => rw [mergeBy, List.filterMap_cons, List.filterMap_cons, ih xs ys hx]

/-- Build the call arguments for a callee whose signature decomposes as
    `inputs = M ++ I`, `outputs = M ++ O` (`M` = in-out, `I` = input-only,
    `O` = output-only, the shared block `M` leading both). The in-out block leads
    (as `inoutArg` nodes, so each is a
    pass-by-reference variable named exactly `M.keys[i]`, as the call rule's in-out
    premise requires). Then come the by-value inputs `exprs` (as `inArg` nodes) and
    the output-only *targets* `T` (as `outArg` nodes), merged under the mask `mask`.
    This layout makes the argument positions line up with the parameter positions
    the callee declares — see `getIn_mkArgs` / `getLhs_mkArgs`.

    **Why `mask` exists.** The `call` rule constrains the input positions and the
    write positions one at a time, through `CallArg.getInputExprs` and
    `CallArg.getLhs`. Each of those drops the other kind of node, so the rule leaves
    the relative order of an `inArg` and an `outArg` free. `mask` gives the
    generator that same freedom, so a call such as `call p(out y, 1);` is now
    reachable. The in-out block still has to lead: `M` heads both projections, so
    an `inoutArg` after an `inArg` or after an `outArg` would break the positional
    match.

    `T` is a **separate** argument rather than the callee's own `O`, because the
    Core spec does not constrain an out argument's *name*: any writable
    variable of the declared type will do. `T` is therefore a caller-chosen list of
    receiving variables, required only to be as long as `O` and to match it
    *positionally in type* — see `outTargets` (the generator's choice) and the
    `hTinΓ` premise of the soundness theorems below, which pairs `T.keys[i]` with
    `O.values[i]`. -/
def mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool) : List (CallArg Expression) :=
  M.map (fun p => CallArg.inoutArg p.1) ++
    mergeBy mask (exprs.map CallArg.inArg) (T.map (fun p => CallArg.outArg p.1))

-- **Which swaps the `call` rule can see.** `CmdExtHasType'.call` constrains the
-- *projections* `getInputExprs` and `getLhs`, position by position. An `inArg`
-- appears in the first projection only, and an `outArg` in the second only, so a
-- swap of the two changes neither. An `inoutArg` appears in *both*, so a swap of an
-- `inoutArg` with either other kind is visible. That is why `mask` merges the
-- by-value inputs with the out targets, and why the in-out block still has to lead.
section
private def gcaExpr : Expression.Expr := LExpr.const () (.intConst 1)
private def gcaY : Identifier Unit := ⟨"y", ()⟩
private def gcaZ : Identifier Unit := ⟨"z", ()⟩
private abbrev GcaArgs := List (CallArg Expression)

-- An `inArg`/`outArg` swap is invisible to the input positions.
#guard CallArg.getInputExprs [CallArg.inArg gcaExpr, CallArg.outArg gcaY]
     == CallArg.getInputExprs [CallArg.outArg gcaY, CallArg.inArg gcaExpr]
-- An `inArg`/`outArg` swap is invisible to the write positions.
#guard CallArg.getLhs [CallArg.inArg gcaExpr, CallArg.outArg gcaY]
     == CallArg.getLhs [CallArg.outArg gcaY, CallArg.inArg gcaExpr]
-- An `inArg`/`inoutArg` swap *does* change the input positions.
#guard ! (CallArg.getInputExprs [CallArg.inArg gcaExpr, CallArg.inoutArg gcaY]
       == CallArg.getInputExprs [CallArg.inoutArg gcaY, CallArg.inArg gcaExpr])
-- An `outArg`/`inoutArg` swap *does* change the write positions.
#guard ! (CallArg.getLhs ([CallArg.outArg gcaZ, CallArg.inoutArg gcaY] : GcaArgs)
       == CallArg.getLhs ([CallArg.inoutArg gcaY, CallArg.outArg gcaZ] : GcaArgs))
end

/-- `getInputExprs (mkArgs M T exprs mask)` is the in-out block turned into bare
    unannotated `fvar`s, followed by the by-value inputs. The out-argument targets
    contribute nothing to the input positions, at every mask. -/
theorem getIn_mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool) :
    CallArg.getInputExprs (mkArgs M T exprs mask)
      = M.map (fun p => LExpr.fvar () p.1 none) ++ exprs := by
  rw [mkArgs, CallArg.getInputExprs, List.filterMap_append,
    filterMap_mergeBy_left _ mask _ _
      (by rintro a ha; simp only [List.mem_map] at ha; obtain ⟨p, _, rfl⟩ := ha; rfl)]
  simp only [List.filterMap_map, Function.comp_def, filterMap_some_comp,
    List.filterMap_some]

/-- `getLhs (mkArgs M T exprs mask)` is the LHS (assignable) positions: the in-out
    keys followed by the out-argument target names. The by-value inputs contribute
    nothing, at every mask. -/
theorem getLhs_mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool) :
    CallArg.getLhs (mkArgs M T exprs mask) = M.keys ++ T.keys := by
  rw [mkArgs, CallArg.getLhs, List.filterMap_append,
    filterMap_mergeBy_right _ mask _ _
      (by rintro a ha; simp only [List.mem_map] at ha; obtain ⟨e, _, rfl⟩ := ha; rfl)]
  simp only [List.filterMap_map, Function.comp_def, filterMap_some_comp,
    ListMap.keys_eq_map_fst]

-- ── The init-chain that brings the required names into scope ───────────────

/-- The statement list `var x₁ : mty₁ := *; … ; var xₙ : mtyₙ := *` that
    declares every `(x, mty) ∈ news` (nondeterministically, so no initializer
    expression is required). -/
def initChain (news : List (Identifier Unit × LMonoTy)) : List Statement :=
  news.map (fun p => Statement.init p.1 (.forAll [] p.2) .nondet default)

/-- The type-context after running `initChain news` on `Γ`: fold each declared
    `(x, mty)` in as `x ↦ ∀[]. mty`. -/
def insertAll (Γ : TContext Unit) (news : List (Identifier Unit × LMonoTy)) :
    TContext Unit :=
  news.foldl (fun Γ p => { Γ with types := Γ.types.insert p.1 (.forAll [] p.2) }) Γ

/-- `insertAll` respects `TContext.Equiv`: inserting the same bindings into equivalent
    contexts keeps them equivalent. Needed because a `TContext` scope is an opaque hash map,
    so the generator-side and semantic-side scopes agree only up to `Equiv`. -/
theorem insertAll_equiv (news : List (Identifier Unit × LMonoTy)) {Γ Γ' : TContext Unit}
    (h : TContext.Equiv (T := CoreLParams) Γ Γ') :
    TContext.Equiv (T := CoreLParams) (insertAll Γ news) (insertAll Γ' news) := by
  induction news generalizing Γ Γ' with
  | nil => exact h
  | cons hd tl ih =>
    refine ih ?_
    exact ⟨Strata.Util.HMaps.insert_equiv h.1 hd.1 (.forAll [] hd.2), h.2⟩

/-- The flat `VarCtx` analogue of `insertAll`: the *generator-side* scope after
    running `initChain news` in the ambient scope. Because the chain is emitted
    **inline** (not inside a block), these declarations genuinely escape into the
    enclosing sequence, so this — not `ctx` — is the call chunk's output scope.
    `toTCtx_insertAllCtx` (in `StmtHasTypeAGen.lean`) relates it to `insertAll`. -/
def insertAllCtx (ctx : VarCtx) (news : List (Identifier Unit × LMonoTy)) : VarCtx :=
  news.foldl (fun ctx p => Map.insert ctx p.1 p.2) ctx

/-- `insertAllCtx` peels one declaration off the front (it is a `foldl`). -/
theorem insertAllCtx_cons (ctx : VarCtx) (hd : Identifier Unit × LMonoTy)
    (tl : List (Identifier Unit × LMonoTy)) :
    insertAllCtx ctx (hd :: tl) = insertAllCtx (Map.insert ctx hd.1 hd.2) tl := by
  simp [insertAllCtx]

/-- Looking up a name absent from `news` in `insertAllCtx ctx news` falls through
    to `ctx` — the flat-context mirror of `insertAll_find_not_mem`. -/
theorem insertAllCtx_find_not_mem (news : List (Identifier Unit × LMonoTy)) :
    ∀ (ctx : VarCtx) (x : Identifier Unit),
    x ∉ news.map Prod.fst → Map.find? (insertAllCtx ctx news) x = Map.find? ctx x := by
  induction news with
  | nil => intro ctx x _; rfl
  | cons hd tl ih =>
    intro ctx x hx
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [insertAllCtx_cons, ih _ x hx.2]
    exact Map.find?_insert_ne ctx x hd.1 _ hx.1

/-- Declaring a `Nodup` list of names, each absent from `ctx`, preserves
    functionality: every insert is of a key fresh at the point it happens (fresh in
    `ctx` by hypothesis, and undisturbed by the earlier — distinct — inserts). This
    is what carries the `Map.Functional` invariant across an inline `init` chain. -/
theorem insertAllCtx_functional (news : List (Identifier Unit × LMonoTy)) :
    ∀ (ctx : VarCtx), Map.Functional ctx → (news.map Prod.fst).Nodup →
    (∀ p ∈ news, Map.find? ctx p.1 = none) →
    Map.Functional (insertAllCtx ctx news) := by
  induction news with
  | nil => intro ctx hFun _ _; exact hFun
  | cons hd tl ih =>
    intro ctx hFun hnd hfresh
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    obtain ⟨hnotin, hndtl⟩ := hnd
    rw [insertAllCtx_cons]
    refine ih _ (Map.insert_functional_of_fresh ctx hd.1 hd.2 hFun
      (hfresh hd (List.mem_cons_self ..))) hndtl ?_
    intro p hp
    -- `p.1 ≠ hd.1` (the keys are `Nodup`), so the head insert does not affect it.
    have hne : p.1 ≠ hd.1 := fun h => hnotin p hp h
    rw [Map.find?_insert_ne ctx p.1 hd.1 _ hne]
    exact hfresh p (List.mem_cons_of_mem _ hp)

/-- Declaring `news` can only add the declared names as keys. Used to justify the
    call chunk's *output* scope keys against the chunk's `definedVars`. -/
theorem insertAllCtx_keys_subset (news : List (Identifier Unit × LMonoTy)) :
    ∀ (ctx : VarCtx),
    Map.keys (insertAllCtx ctx news) ⊆ Map.keys ctx ++ news.map Prod.fst := by
  induction news with
  | nil => intro ctx k hk; exact List.mem_append_left _ hk
  | cons hd tl ih =>
    intro ctx k hk
    rw [insertAllCtx_cons] at hk
    rcases List.mem_append.mp (ih _ hk) with h | h
    · -- a key of `ctx.insert hd.1 hd.2`: either `hd.1` or an old key
      rcases List.mem_cons.mp (Map.insert_keys ctx h) with rfl | h'
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- Declaring `news` can only add the declared *types* as values. The value analogue of
    `insertAllCtx_keys_subset`, used to carry the "every type in scope is well-kinded in
    the ambient context" invariant across an inline `init` chain. -/
theorem mem_values_insertAllCtx (news : List (Identifier Unit × LMonoTy)) :
    ∀ (ctx : VarCtx) {v : LMonoTy},
      v ∈ (insertAllCtx ctx news).values → v ∈ news.map Prod.snd ∨ v ∈ ctx.values := by
  induction news with
  | nil => intro ctx v h; exact Or.inr h
  | cons hd tl ih =>
    intro ctx v h
    rw [insertAllCtx_cons] at h
    rcases ih _ h with h' | h'
    · exact Or.inl (List.mem_cons_of_mem _ h')
    · rcases mem_values_insert ctx hd.1 hd.2 h' with rfl | h''
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr h''

/-- Running `initChain news` from `Γ` (where each declared name is fresh at the
    point it is declared, and every declared type is well-kinded in `C`) is well-typed
    and yields `insertAll Γ news`.

    `hwk` discharges the `WellKindedTy` premise of `CmdHasType'.init_nondet`. The caller
    gets it from `SimpleTyArities`, because the generator makes all of the declared
    types. -/
theorem initChain_types {P : Program} {C : LContext CoreLParams} {L : List String}
    (news : List (Identifier Unit × LMonoTy))
    (hwk : ∀ p ∈ news, C.WellKindedTy p.2) : ∀ (Γ : TContext Unit),
    (∀ i (hi : i < news.length),
      (insertAll Γ (news.take i)).types.find? (news[i].1) = none) →
    StatementsHasTypeA P C Γ L (initChain news) C (insertAll Γ news) := by
  induction news with
  | nil => intro Γ _; exact StatementsHasType'.nil C Γ L Γ (tctxEquivRefl Γ)
  | cons hd tl ih =>
    intro Γ hfresh
    -- head is fresh in Γ = insertAll Γ (take 0)
    have hfresh0 : Γ.types.find? hd.1 = none := by
      have := hfresh 0 (by simp)
      simpa [insertAll, List.take] using this
    -- the head statement types Γ → {Γ with x ↦ ∀[].mty}
    have hhead : StatementHasTypeA P C Γ L
        (Statement.init hd.1 (.forAll [] hd.2) .nondet default) C
        { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) } :=
      StatementHasType'.cmd C Γ _ L _ _
        (CmdExtHasType'.cmd Γ _ _
          (CmdHasType'.init_nondet Γ hd.1 (.forAll [] hd.2) hd.2 [] default _ hfresh0 rfl
            (rigidAnnotCompat_forAll_nil hd.2) (hwk hd List.mem_cons_self) (tctxEquivRefl _)))
        (tctxEquivRefl _)
    -- the tail types from the inserted context
    have htail : StatementsHasTypeA P C
        { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) } L
        (initChain tl) C (insertAll Γ (hd :: tl)) := by
      have hins : insertAll Γ (hd :: tl)
          = insertAll { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) } tl := by
        simp [insertAll]
      rw [hins]
      apply ih (fun p hp => hwk p (List.mem_cons_of_mem _ hp))
      intro i hi
      have := hfresh (i + 1) (by simpa using Nat.succ_lt_succ hi)
      simpa [insertAll, List.take] using this
    exact StatementsHasType'.cons C C C Γ
      { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) }
      (insertAll Γ (hd :: tl)) L _ _ hhead htail

-- ── `insertAll` lookup bookkeeping ────────────────────────────────────────

/-- Looking up a name absent from `news` in `insertAll Γ news` falls through to
    `Γ` (none of the inserted names is `x`). -/
theorem insertAll_find_not_mem (news : List (Identifier Unit × LMonoTy)) :
    ∀ (Γ : TContext Unit) (x : Identifier Unit),
    x ∉ news.map Prod.fst →
    (insertAll Γ news).types.find? x = Γ.types.find? x := by
  induction news with
  | nil => intro Γ x _; rfl
  | cons hd tl ih =>
    intro Γ x hx
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    obtain ⟨hne, hxtl⟩ := hx
    have hins : insertAll Γ (hd :: tl)
        = insertAll { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) } tl := by
      simp [insertAll]
    rw [hins, ih _ x hxtl]
    exact Strata.Util.HMaps.find?_insert_ne _ x hd.1 _ hne

/-- Looking up a member key of `news` in `insertAll Γ news` returns that member's
    (wrapped) value, provided the keys are `Nodup` (so no later insert shadows an
    earlier one). -/
theorem insertAll_find_mem (news : List (Identifier Unit × LMonoTy)) :
    ∀ (Γ : TContext Unit) (x : Identifier Unit) (mty : LMonoTy),
    (news.map Prod.fst).Nodup → (x, mty) ∈ news →
    (insertAll Γ news).types.find? x = some (.forAll [] mty) := by
  induction news with
  | nil => intro _ _ _ _ hmem; exact absurd hmem (by simp)
  | cons hd tl ih =>
    intro Γ x mty hnd hmem
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hndtl⟩ := hnd
    have hins : insertAll Γ (hd :: tl)
        = insertAll { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) } tl := by
      simp [insertAll]
    rw [hins]
    rcases List.mem_cons.mp hmem with heq | hmemtl
    · -- x is the head key: the head is never overwritten by the (disjoint) tail.
      have hx : x = hd.1 := (Prod.mk.injEq .. ▸ heq).1
      have hm : mty = hd.2 := (Prod.mk.injEq .. ▸ heq).2
      subst hx; subst hm
      rw [insertAll_find_not_mem tl _ hd.1 hnotin]
      exact Strata.Util.HMaps.find?_insert_self _ hd.1 _
    · exact ih _ x mty hndtl hmemtl

/-- `Nodup` index lookup: the `i`-th key of `news` maps to the `i`-th value in
    `insertAll Γ news`. -/
theorem insertAll_find_idx (news : List (Identifier Unit × LMonoTy))
    (Γ : TContext Unit) (hnd : (news.map Prod.fst).Nodup)
    (i : Nat) (hi : i < news.length) :
    (insertAll Γ news).types.find? (news[i].1) = some (.forAll [] news[i].2) := by
  refine insertAll_find_mem news Γ (news[i].1) (news[i].2) hnd ?_
  have hmem : news[i] ∈ news := List.getElem_mem hi
  exact hmem

/-- In a `Nodup` list, the element at index `i` does not appear in the length-`i`
    prefix. -/
theorem nodup_getElem_not_mem_take {α} {l : List α} (hnd : l.Nodup)
    (i : Nat) (hi : i < l.length) : l[i] ∉ l.take i := by
  intro h
  rw [List.mem_iff_getElem] at h
  obtain ⟨j, hj, hval⟩ := h
  rw [List.length_take] at hj
  rw [List.getElem_take] at hval
  have hji : j < i := by omega
  have : j = i := List.getElem?_inj (by omega) hnd (by
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hi, hval])
  omega

/-- The `i`-th key/value pair of a `ListMap` is a member of its underlying list. -/
theorem keyval_mem {α β} (m : ListMap α β) (i : Nat)
    (hi : i < m.keys.length) (hj : i < m.values.length) :
    (m.keys[i], m.values[i]) ∈ m.toList := by
  have hidx : i < m.toList.length := by
    rw [ListMap.keys_eq_map_fst, List.length_map] at hi; exact hi
  rw [List.mem_iff_getElem]
  refine ⟨i, hidx, ?_⟩
  simp only [ListMap.keys_eq_map_fst, ListMap.values_eq_map_snd, List.getElem_map]
  rfl

-- ── The 7-premise call-typing obligation ─────────────────────────────────

/-- Soundness of the in-out call recipe (shared block `M` leading both roles).
    Given a monomorphic callee
    `proc` with `inputs = M ++ I`, `outputs = M ++ O` (M/I/O mutually key-disjoint),
    out-argument targets `T` positionally as long as `O`, every `M` name and every
    `T` name in scope at its declared type (`M.values[i]` resp. `O.values[i]`), and
    by-value inputs `exprs` that are well-typed and not bare unannotated `fvar`s,
    the call `CmdExt.call pname (mkArgs M T exprs mask) md` type-checks (leaving `Γ`
    unchanged).

    Note the asymmetry between the two written-to blocks, which mirrors the spec:
    the in-out names are `M`'s own (the call rule pins them), whereas the out-only
    positions are filled by the *caller-chosen* `T` and are related to `O` only
    through their types (`hTinΓ`). -/
theorem call_recipe_inout_sound
    {C : LContext CoreLParams} {P : Program} {Γ : TContext Unit}
    {pname : String} {proc : Procedure} {md : MetaData Expression}
    (σ : List (TyIdentifier × LMonoTy))
    (M I O T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool)
    (hfind : Program.Procedure.find? P pname = some proc)
    (hInputs : proc.header.inputs = M ++ I)
    (hOutputs : proc.header.outputs = M ++ O)
    (hExLen : exprs.length = I.length)
    (hTLen : T.length = O.length)
    -- The variables the call writes back through are bound in `Γ` at the *instantiated*
    -- formal type `subst [σ] (declared value)` — the type the caller supplied them at.
    (hMinΓ : ∀ i (hi : i < M.keys.length) (hj : i < M.values.length),
      Γ.types.find? (M.keys[i]'hi) = some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (M.values[i]'hj))))
    (hTinΓ : ∀ i (hi : i < T.keys.length) (hj : i < O.values.length),
      Γ.types.find? (T.keys[i]'hi) = some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (O.values[i]'hj))))
    -- Each by-value input is typed at the *instantiated* formal input type.
    (hExTy : ∀ i (hi : i < exprs.length) (hj : i < I.values.length),
      LExpr.HasTypeA [] (exprs[i]'hi) (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (I.values[i]'hj)))
    (hExNoFvar : ∀ i (hi : i < exprs.length) m x, (exprs[i]'hi) ≠ LExpr.fvar m x none)
    (hIdisjOut : ∀ i (hi : i < I.keys.length),
      (M ++ O).keys.contains (I.keys[i]'(by simpa using hi)) = false) :
    CmdExtHasTypeA C P Γ (CmdExt.call pname (mkArgs M T exprs mask) md) Γ := by
  -- length facts
  have hkeysM : M.keys.length = M.length := ListMap.keys.length
  have hvalsM : M.values.length = M.length := lm_values_length M
  have hkeysI : I.keys.length = I.length := ListMap.keys.length
  have hvalsI : I.values.length = I.length := lm_values_length I
  have hkeysO : O.keys.length = O.length := ListMap.keys.length
  have hvalsO : O.values.length = O.length := lm_values_length O
  have hkeysT : T.keys.length = O.length := by rw [ListMap.keys.length, hTLen]
  have hgetIn := getIn_mkArgs M T exprs mask
  have hgetLhs := getLhs_mkArgs M T exprs mask
  apply CmdExtHasType'.call Γ pname (mkArgs M T exprs mask) proc md σ Γ
  case _ => -- (1) find?
    exact hfind
  case _ => -- (2) input arity
    rw [hgetIn, hInputs]
    show (List.map _ M ++ exprs).length = (M ++ I).length
    rw [List.length_append, List.length_map, hExLen, lm_length_append]
  case _ => -- (3) output arity
    rw [hgetLhs, hOutputs]
    show (M.keys ++ T.keys).length = (M ++ O).length
    rw [List.length_append, hkeysM, hkeysT, lm_length_append]
  case _ => -- (4) all LHS in Γ
    intro v hv
    rw [hgetLhs, List.mem_append] at hv
    rcases hv with hvM | hvT
    · -- v ∈ M.keys
      rw [List.mem_iff_getElem] at hvM
      obtain ⟨i, hi, hveq⟩ := hvM
      have hj : i < M.values.length := by rw [hvalsM]; rw [hkeysM] at hi; exact hi
      rw [← hveq, hMinΓ i hi hj]
      rfl
    · -- v ∈ T.keys: in scope at the *declared* type `O.values[i]`
      rw [List.mem_iff_getElem] at hvT
      obtain ⟨i, hi, hveq⟩ := hvT
      have hj : i < O.values.length := by rw [hvalsO]; rw [hkeysT] at hi; exact hi
      rw [← hveq, hTinΓ i hi hj]
      rfl
  case _ => -- (5) input types
    intro i hi hj
    -- Rewrite the input positions and the callee's input signature.
    simp only [hgetIn] at hi ⊢
    simp only [hInputs, lm_values_append] at hj ⊢
    -- length of the mapped M block
    have hmaplen : (List.map (fun p => (LExpr.fvar () p.1 none : Expression.Expr)) M).length
        = M.length := List.length_map ..
    -- pick the witness = the *instantiated* value at position i (AliasEquiv is refl).
    refine ⟨LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) ((M.values ++ I.values)[i]'hj), AliasEquiv.refl, ?_⟩
    by_cases hlt : i < M.length
    · -- in-out block: the argument is the bare fvar `fvar () M[i].1 none`.
      have hidxM : i < M.values.length := by rw [hvalsM]; exact hlt
      have hidxK : i < M.keys.length := by rw [hkeysM]; exact hlt
      have harg : (List.map (fun p => LExpr.fvar () p.1 none) M ++ exprs)[i]
          = LExpr.fvar () (M.keys[i]'hidxK) none := by
        simp only [List.getElem_append_left (by rw [hmaplen]; exact hlt), List.getElem_map,
          ListMap.keys_eq_map_fst]
      have hval : (M.values ++ I.values)[i]'hj = M.values[i]'hidxM :=
        List.getElem_append_left hidxM
      rw [harg, hval]
      -- match reduces to the fvar branch
      exact hMinΓ i hidxK hidxM
    · -- by-value input block: i ≥ M.length, so the argument is `exprs[i - M.length]`.
      have hge : M.length ≤ i := Nat.le_of_not_lt hlt
      have hiex : i - M.length < exprs.length := by
        rw [List.length_append, hmaplen] at hi; omega
      have harg : (List.map (fun p => LExpr.fvar () p.1 none) M ++ exprs)[i]
          = exprs[i - M.length]'hiex := by
        rw [List.getElem_append_right (by rw [hmaplen]; exact hge)]
        congr 1
        rw [hmaplen]
      have hjI : i - M.length < I.values.length := by
        rw [hvalsI]; rw [List.length_append, hvalsM, hvalsI] at hj; omega
      have hval : (M.values ++ I.values)[i]'hj = I.values[i - M.length]'hjI := by
        rw [List.getElem_append_right (by rw [hvalsM]; exact hge)]
        congr 1
        rw [hvalsM]
      rw [harg, hval]
      -- the by-value argument is not a bare unannotated fvar, so the match takes
      -- the `e` branch → `exprTyped C Γ e mty` = `HasTypeA [] e mty`.
      have hne := hExNoFvar (i - M.length) hiex
      -- split on the expr's head; only the bare-fvar-none shape hits the fvar arm.
      have hExTyi := hExTy (i - M.length) hiex hjI
      -- turn the match into the exprTyped obligation
      cases hcase : exprs[i - M.length]'hiex with
      | fvar m x ty =>
        cases ty with
        | none => exact absurd hcase (hne m x)
        | some t =>
          simp only []
          rw [hcase] at hExTyi
          exact hExTyi
      | _ => simp only []; rw [hcase] at hExTyi; exact hExTyi
  case _ => -- (6) output types
    intro i hi hj
    simp only [hgetLhs] at hi ⊢
    simp only [hOutputs, lm_values_append] at hj ⊢
    refine ⟨LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) ((M.values ++ O.values)[i]'hj), AliasEquiv.refl, ?_⟩
    by_cases hlt : i < M.length
    · -- in-out block
      have hidxK : i < M.keys.length := by rw [hkeysM]; exact hlt
      have hidxM : i < M.values.length := by rw [hvalsM]; exact hlt
      have hlhs : (M.keys ++ T.keys)[i]'hi = M.keys[i]'hidxK :=
        List.getElem_append_left hidxK
      have hval : (M.values ++ O.values)[i]'hj = M.values[i]'hidxM :=
        List.getElem_append_left hidxM
      rw [hlhs, hval]
      exact hMinΓ i hidxK hidxM
    · -- output-only block: target name `T.keys[i']`, declared type `O.values[i']`
      have hge : M.length ≤ i := Nat.le_of_not_lt hlt
      have hidxKT : i - M.length < T.keys.length := by
        rw [List.length_append, hkeysM] at hi; rw [hkeysT]; omega
      have hidxVO : i - M.length < O.values.length := by
        rw [List.length_append, hvalsM] at hj; rw [hvalsO]; omega
      have hlhs : (M.keys ++ T.keys)[i]'hi = T.keys[i - M.length]'hidxKT := by
        rw [List.getElem_append_right (by rw [hkeysM]; exact hge)]
        congr 1
        rw [hkeysM]
      have hval : (M.values ++ O.values)[i]'hj = O.values[i - M.length]'hidxVO := by
        rw [List.getElem_append_right (by rw [hvalsM]; exact hge)]
        congr 1
        rw [hvalsM]
      rw [hlhs, hval]
      exact hTinΓ (i - M.length) hidxKT hidxVO
  case _ => -- (7) inout matching names
    intro i hi hcontains
    -- Rewrite the callee signature keys as `M.keys ++ {I,O}.keys`.
    simp only [hInputs, lm_keys_append] at hi hcontains ⊢
    simp only [hOutputs, lm_keys_append] at hcontains
    by_cases hlt : i < M.length
    · -- in-out block: the argument at position i is `fvar () M.keys[i] none`.
      have hidxK : i < M.keys.length := by rw [hkeysM]; exact hlt
      rw [hgetIn, List.getElem_append_left hidxK]
      refine ⟨(), none, ?_⟩
      -- position i lies in the mapped M block
      have hmaplen : (List.map (fun p => (LExpr.fvar () p.1 none : Expression.Expr)) M).length
          = M.length := List.length_map ..
      rw [List.getElem?_append_left (by rw [hmaplen]; exact hlt)]
      rw [List.getElem?_eq_getElem (by rw [hmaplen]; exact hlt)]
      simp only [List.getElem_map, ListMap.keys_eq_map_fst]
    · -- input-only block: `hIdisjOut` says its key is absent from `(M ++ O).keys`,
      -- contradicting the `contains` hypothesis.
      exfalso
      have hge : M.length ≤ i := Nat.le_of_not_lt hlt
      have hidxI : i - M.length < I.keys.length := by
        rw [List.length_append, hkeysM] at hi; rw [hkeysI]; omega
      rw [List.getElem_append_right (by rw [hkeysM]; exact hge)] at hcontains
      have hdisj := hIdisjOut (i - M.length) hidxI
      rw [lm_keys_append] at hdisj
      -- align the index arithmetic between hcontains and hdisj
      simp only [hkeysM] at hcontains
      rw [hdisj] at hcontains
      exact absurd hcontains (by simp)
  case _ => -- (8) the output context, up to `TContext.Equiv`
    exact tctxEquivRefl Γ

/-- Discharge `call_recipe_inout_sound`'s `hTinΓ` from a *membership* fact about the
    out-argument targets. That premise wants the target name at position `i` bound at
    the type `O.values[i]` the callee declares; `hTVals` says the targets carry
    exactly those types positionally, so binding each target at its **own** recorded
    type suffices. This is the only place the `T`-vs-`O` type alignment is used. -/
theorem outTargets_inΓ {Γ : TContext Unit} (O T : @LMonoTySignature Unit)
    (hTVals : T.values = O.values)
    (hInScope : ∀ p ∈ T.toList, Γ.types.find? p.1 = some (.forAll [] p.2)) :
    ∀ i (hi : i < T.keys.length) (hj : i < O.values.length),
      Γ.types.find? (T.keys[i]'hi) = some (.forAll [] (O.values[i]'hj)) := by
  intro i hi hj
  have hiv : i < T.values.length := by
    rw [lm_values_length]; rw [ListMap.keys.length] at hi; exact hi
  have hval : T.values[i]'hiv = O.values[i]'hj := by
    simp only [← hTVals]
  rw [← hval]
  exact hInScope _ (keyval_mem T i hi hiv)

/-- Positionally type-aligned out-argument targets have the same length as the
    callee's out-only block. -/
theorem lm_length_eq_of_values_eq {O T : @LMonoTySignature Unit}
    (hTVals : T.values = O.values) : T.length = O.length := by
  rw [← lm_values_length T, ← lm_values_length O, hTVals]

-- ── Chaining and block-wrapping ───────────────────────────────────────────

-- ── `TContext.Equiv`-congruence of the annotated specs ────────────────────
-- Upstream constrains every rule's *output* context only up to `TContext.Equiv`
-- (an `HMap`-backed scope stack ignores insertion order). Chaining two derivations
-- therefore needs the relations to be congruent in their *input* context as well:
-- `StatementsHasTypeA_append` inverts a `nil`, which hands back a context that is
-- only `Equiv` to the one the tail was typed in. At the annotated (`HasTypeA`)
-- instantiation this congruence is cheap: `exprTyped` ignores `Γ` outright and
-- `tyCompat` is plain equality, so `Γ` is read only through `types.find?` and
-- `aliases`, both of which `TContext.Equiv` preserves.

/-- `TContext.Equiv` gives pointwise agreement of variable lookups. -/
theorem tctxEquiv_find? {Γ Γ' : TContext Unit}
    (h : TContext.Equiv (T := CoreLParams) Γ Γ') (x : Identifier Unit) :
    Γ.types.find? x = Γ'.types.find? x :=
  Strata.Util.HMaps.Equiv.find? h.1 x

/-- `TContext.Equiv` survives inserting the same binding on both sides. -/
theorem tctxEquiv_insert {Γ Γ' : TContext Unit}
    (h : TContext.Equiv (T := CoreLParams) Γ Γ') (x : Identifier Unit) (v : LTy) :
    TContext.Equiv (T := CoreLParams)
      { Γ with types := Γ.types.insert x v } { Γ' with types := Γ'.types.insert x v } :=
  ⟨Strata.Util.HMaps.insert_equiv h.1 x v, h.2⟩

/-- **`FuncHasTypeA` does not depend on the type-scope at all.** Every field is either
    `Γ`-free or routed through `exprTyped`/`tyCompat`, which ignore `Γ` at the annotated
    instantiation. -/
theorem funcHasTypeA_ctx_irrel {C : LContext CoreLParams} {Γ Γ₂ : TContext Unit}
    {func : Function} (h : FuncHasTypeA C Γ func) : FuncHasTypeA C Γ₂ func :=
  ⟨h.inputsNodup, h.typeArgsNodup, h.noUndeclaredVars, h.signatureWellKinded,
   h.bodyTyped, h.measureTyped⟩

/-- **`CmdHasTypeA` is congruent in its input context up to `TContext.Equiv`.** -/
theorem cmdHasTypeA_equiv_congr {C : LContext CoreLParams} {Γ Γ₂ Δ : TContext Unit}
    {c : Cmd Expression} (h : CmdHasTypeA C Γ c Δ)
    (he : TContext.Equiv (T := CoreLParams) Γ₂ Γ) :
    CmdHasTypeA C Γ₂ c Δ := by
  cases h with
  | init_det x xty e mty tys md Δ' hfresh hnovar hlen hrac hwk hexpr heq =>
    exact CmdHasType'.init_det Γ₂ x xty e mty tys md _
      ((tctxEquiv_find? he x).trans hfresh) hnovar hlen (by rw [he.2]; exact hrac) hwk hexpr
      (heq.trans (tctxEquiv_insert he.symm x _))
  | init_nondet x xty mty tys md Δ' hfresh hlen hrac hwk heq =>
    exact CmdHasType'.init_nondet Γ₂ x xty mty tys md _
      ((tctxEquiv_find? he x).trans hfresh) hlen (by rw [he.2]; exact hrac) hwk
      (heq.trans (tctxEquiv_insert he.symm x _))
  | set_det x mty e md Δ' hfind hexpr heq =>
    exact CmdHasType'.set_det Γ₂ x mty e md _
      ((tctxEquiv_find? he x).trans hfind) hexpr (heq.trans he.symm)
  | set_nondet x mty md Δ' hfind heq =>
    exact CmdHasType'.set_nondet Γ₂ x mty md _
      ((tctxEquiv_find? he x).trans hfind) (heq.trans he.symm)
  | assert l e md Δ' hexpr heq =>
    exact CmdHasType'.assert Γ₂ l e md _ hexpr (heq.trans he.symm)
  | assume l e md Δ' hexpr heq =>
    exact CmdHasType'.assume Γ₂ l e md _ hexpr (heq.trans he.symm)
  | cover l e md Δ' hexpr heq =>
    exact CmdHasType'.cover Γ₂ l e md _ hexpr (heq.trans he.symm)

/-- **`CmdExtHasTypeA` is congruent in its input context up to `TContext.Equiv`.** -/
theorem cmdExtHasTypeA_equiv_congr {C : LContext CoreLParams} {P : Program}
    {Γ Γ₂ Δ : TContext Unit} {c : Command} (h : CmdExtHasTypeA C P Γ c Δ)
    (he : TContext.Equiv (T := CoreLParams) Γ₂ Γ) :
    CmdExtHasTypeA C P Γ₂ c Δ := by
  cases h with
  | cmd Γ' c hc => exact CmdExtHasType'.cmd Γ₂ _ c (cmdHasTypeA_equiv_congr hc he)
  | call pname callArgs proc md σ Δ' hfind hin hout hlhs hinTy houtTy hinout heq =>
    refine CmdExtHasType'.call Γ₂ pname callArgs proc md σ _ hfind hin hout ?_ ?_ ?_ hinout
      (heq.trans he.symm)
    · intro v hv; rw [tctxEquiv_find? he v]; exact hlhs v hv
    · intro i hi hj
      obtain ⟨mty, halias, hty⟩ := hinTy i hi hj
      refine ⟨mty, by rw [he.2]; exact halias, ?_⟩
      -- The per-argument obligation matches on the argument shape, but only its
      -- unannotated-`fvar` branch reads `Γ` (through `types.find?`); every other branch
      -- goes through `exprTyped`, which ignores `Γ` at this instantiation.
      first
        | (simp only [tctxEquiv_find? he]; exact hty)
        | exact hty
    · intro i hi hj
      obtain ⟨mty, halias, hty⟩ := houtTy i hi hj
      exact ⟨mty, by rw [he.2]; exact halias, (tctxEquiv_find? he _).trans hty⟩

/-- Fuel-indexed form of `statementsHasTypeA_equiv_congr`.

    The statement case is inlined rather than split off into a mutually recursive lemma: the
    relation lives in `Prop`, so the equation compiler cannot recurse on a derivation, and
    recursing on the *syntax* covers both halves of the mutual definition in one function —
    a block/branch/loop body nested inside the head statement is strictly smaller than the
    list. The recursion is on an explicit `Nat` fuel bounding `sizeOf ss` rather than on
    `sizeOf ss` directly, so that every context stays a genuine local variable that `cases`
    can substitute (as a fixed function parameter it would instead pick up an equation, and
    the recursive applications would not typecheck). -/
private theorem statementsHasTypeA_equiv_congr_fuel {P : Program} : ∀ (n : Nat)
    (ss : List Statement) {C C' : LContext CoreLParams} {Γ Γ₂ Δ : TContext Unit}
    {L : List String}, sizeOf ss ≤ n →
    StatementsHasTypeA P C Γ L ss C' Δ →
    TContext.Equiv (T := CoreLParams) Γ₂ Γ →
    StatementsHasTypeA P C Γ₂ L ss C' Δ := by
  intro n
  induction n with
  | zero =>
    -- `sizeOf` of a list is at least 1, so there is no fuel-0 case.
    intro ss C C' Γ Γ₂ Δ L hfuel _ _
    cases ss <;> simp at hfuel
  | succ n ih =>
    intro ss C C' Γ Γ₂ Δ L hfuel h he
    cases h with
    | nil _ _ L _ heq => exact StatementsHasType'.nil C Γ₂ L _ (heq.trans he.symm)
    | cons _ Ca _ _ Γa _ L s ss' hs hss =>
      refine StatementsHasType'.cons C Ca _ Γ₂ Γa _ L s ss' ?_ hss
      -- Only the head statement is retyped; the tail already starts from `Γa`.
      cases hs with
      | cmd _ _ Γ' L c _ hc heq =>
        exact StatementHasType'.cmd C Γ₂ Γ' L c _ (cmdExtHasTypeA_equiv_congr hc he) heq
      | block _ _ C_body Γ_body L label body md _ hlab hbody heq =>
        exact StatementHasType'.block C Γ₂ C_body Γ_body L label body md _ hlab
          (ih body (by simp at hfuel; omega) hbody he) (heq.trans he.symm)
      | ite_det _ _ C_t Γ_t C_e Γ_e L cond thenb elseb md _ hcond hthen helse heq =>
        exact StatementHasType'.ite_det C Γ₂ C_t Γ_t C_e Γ_e L cond thenb elseb md _ hcond
          (ih thenb (by simp at hfuel; omega) hthen he)
          (ih elseb (by simp at hfuel; omega) helse he) (heq.trans he.symm)
      | ite_nondet _ _ C_t Γ_t C_e Γ_e L thenb elseb md _ hthen helse heq =>
        exact StatementHasType'.ite_nondet C Γ₂ C_t Γ_t C_e Γ_e L thenb elseb md _
          (ih thenb (by simp at hfuel; omega) hthen he)
          (ih elseb (by simp at hfuel; omega) helse he) (heq.trans he.symm)
      | loop _ _ C_body Γ_body L guard measure invariants body md _ hg hm hinv hbody heq =>
        exact StatementHasType'.loop C Γ₂ C_body Γ_body L guard measure invariants body md _
          hg hm hinv (ih body (by simp at hfuel; omega) hbody he) (heq.trans he.symm)
      | exit _ _ L label md _ hlab heq =>
        exact StatementHasType'.exit C Γ₂ L label md _ hlab (heq.trans he.symm)
      | funcDecl _ _ L decl func md _ hrec hfunc heq =>
        exact StatementHasType'.funcDecl C Γ₂ L decl func md _ hrec
          (funcHasTypeA_ctx_irrel hfunc) (heq.trans he.symm)
      | typeDecl _ C'' _ L tc md _ hadd heq =>
        exact StatementHasType'.typeDecl C _ Γ₂ L tc md _ hadd (heq.trans he.symm)

/-- **`StatementsHasTypeA` is congruent in its input context up to `TContext.Equiv`.**
    Instantiates `statementsHasTypeA_equiv_congr_fuel` at exactly `sizeOf ss`. -/
theorem statementsHasTypeA_equiv_congr {P : Program} {ss : List Statement}
    {C C' : LContext CoreLParams} {Γ Γ₂ Δ : TContext Unit} {L : List String}
    (h : StatementsHasTypeA P C Γ L ss C' Δ)
    (he : TContext.Equiv (T := CoreLParams) Γ₂ Γ) :
    StatementsHasTypeA P C Γ₂ L ss C' Δ :=
  statementsHasTypeA_equiv_congr_fuel (sizeOf ss) ss (Nat.le_refl _) h he

/-- Concatenating two well-typed statement lists (threading the mid context)
    yields a well-typed statement list. -/
theorem StatementsHasTypeA_append {P : Program} {L : List String}
    {l1 : List Statement} :
    ∀ {C Γ Γ' Γ'' : _} {C' C'' : _} {l2 : List Statement},
    StatementsHasTypeA P C Γ L l1 C' Γ' →
    StatementsHasTypeA P C' Γ' L l2 C'' Γ'' →
    StatementsHasTypeA P C Γ L (l1 ++ l2) C'' Γ'' := by
  induction l1 with
  | nil =>
    intro C Γ Γ' Γ'' C' C'' l2 h1 h2
    cases h1 with
    | nil _ _ _ _ heq =>
      -- The empty list's output context is only `Equiv` to its input, so the tail's
      -- derivation has to be transported back along that equivalence.
      simpa using statementsHasTypeA_equiv_congr h2 heq.symm
  | cons hd tl ih =>
    intro C Γ Γ' Γ'' C' C'' l2 h1 h2
    cases h1 with
    | cons _ Ca _ _ Γa _ _ _ _ hs hss =>
      exact StatementsHasType'.cons _ _ _ _ _ _ _ _ _ hs (ih hss h2)

/-- The output context of a well-typed statement list moves along `TContext.Equiv`:
    appending the empty list lets its `nil` rule absorb the equivalence. -/
theorem StatementsHasTypeA_out_equiv {P : Program} {C C' : LContext CoreLParams}
    {Γ Δ Δ' : TContext Unit} {L : List String} {ss : List Statement}
    (h : StatementsHasTypeA P C Γ L ss C' Δ)
    (he : TContext.Equiv (T := CoreLParams) Δ' Δ) :
    StatementsHasTypeA P C Γ L ss C' Δ' := by
  have hz := StatementsHasTypeA_append h (StatementsHasType'.nil C' Δ L Δ' he)
  rwa [List.append_nil] at hz

/-- A single well-typed statement is a well-typed statement list of length one.
    Used throughout the generator's soundness proof: every `genStmt` branch but
    `call` produces a singleton list, so its per-constructor `StatementHasTypeA` fact is
    lifted through this. -/
theorem StatementsHasTypeA_singleton {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {L : List String} {s : Statement}
    (h : StatementHasTypeA P C Γ L s C' Γ') :
    StatementsHasTypeA P C Γ L [s] C' Γ' :=
  StatementsHasType'.cons _ _ _ _ _ _ _ _ _ h (StatementsHasType'.nil _ _ _ _ (tctxEquivRefl _))

-- ── Reuse-or-init: the general case (block-free when nothing is missing) ──

/-- The sub-list of `news` whose names are **not** yet bound in `Γ`: exactly the
    names a call site must `init` before calling. Names already bound (at the
    right type — see `call_mixed_body_sound`'s `hReuse`) are reused as-is. -/
def missingIn (Γ : TContext Unit) (news : List (Identifier Unit × LMonoTy)) :
    List (Identifier Unit × LMonoTy) :=
  news.filter (fun p => (Γ.types.find? p.1).isNone)

theorem missingIn_sublist (Γ : TContext Unit) (news : List (Identifier Unit × LMonoTy)) :
    (missingIn Γ news).Sublist news := List.filter_sublist

/-- Every `missingIn` name is genuinely absent from `Γ`. -/
theorem missingIn_find_none (Γ : TContext Unit) (news : List (Identifier Unit × LMonoTy))
    {p : Identifier Unit × LMonoTy} (hp : p ∈ missingIn Γ news) :
    Γ.types.find? p.1 = none := by
  have := (List.mem_filter.mp hp).2
  simpa [Option.isNone_iff_eq_none] using this

/-- A name bound in `Γ` is untouched by `insertAll Γ (missingIn Γ news)` — the
    chain only inserts names that were absent, so reused bindings survive. -/
theorem insertAll_missing_preserves (Γ : TContext Unit)
    (news : List (Identifier Unit × LMonoTy))
    (x : Identifier Unit) (v : LTy) (hx : Γ.types.find? x = some v) :
    (insertAll Γ (missingIn Γ news)).types.find? x = some v := by
  have hnotin : x ∉ (missingIn Γ news).map Prod.fst := by
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨p, hp, hpx⟩ := hmem
    have := missingIn_find_none Γ news hp
    rw [hpx, hx] at this
    simp at this
  rw [insertAll_find_not_mem (missingIn Γ news) Γ x hnotin]
  exact hx

/-- **The general call case: reuse what is in scope, `init` only what is missing.**

    `news := M ++ T` are the variables the call writes to: the callee's in-out
    names `M` (which the call rule pins) and the caller-chosen out-argument targets
    `T` (positionally type-aligned with the callee's out-only block `O`, `hTVals`).
    Those already bound in `Γ` at exactly their recorded type (`hReuse`) are reused;
    the rest (`missingIn Γ news`) are brought into scope by an `init … nondet`
    chain. The emitted body is `initChain (missingIn Γ news) ++ [call …]`, well-typed
    in `insertAll Γ (missingIn Γ news)`.

    When `missingIn Γ news = []` the chain is empty, so the body degenerates to the
    bare `[call …]` and the output scope is `Γ` unchanged — the common shape in real
    Strata code. Because this one lemma covers both the all-reused and the
    some-missing case uniformly, it is the *sole* soundness engine for the call
    group; `genCallStmt` needs no `isEmpty` split. -/
theorem call_mixed_body_sound
    {C : LContext CoreLParams} {P : Program} {Γ : TContext Unit} {L : List String}
    {pname : String} {proc : Procedure}
    (σ : List (TyIdentifier × LMonoTy))
    (M I O T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool)
    (hfind : Program.Procedure.find? P pname = some proc)
    (hInputs : proc.header.inputs = M ++ I)
    (hOutputs : proc.header.outputs = M ++ O)
    (hExLen : exprs.length = I.length)
    -- The out targets are positionally type-aligned with the *instantiated* out block.
    (hTVals : T.values = (substSig σ O).values)
    -- The by-value inputs are typed at the *instantiated* formal input types.
    (hExTy : ∀ i (hi : i < exprs.length) (hj : i < I.values.length),
      LExpr.HasTypeA [] (exprs[i]'hi) (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (I.values[i]'hj)))
    (hIdisjOut : ∀ i (hi : i < I.keys.length),
      (M ++ O).keys.contains (I.keys[i]'(by simpa using hi)) = false)
    -- The write-list is the *instantiated* in-out block followed by the targets.
    (hNodup : (substSig σ M ++ T).keys.Nodup)
    -- Each written-to name is *either* already bound at its recorded type, *or* absent.
    (hReuse : ∀ p ∈ (substSig σ M ++ T).toList,
      Γ.types.find? p.1 = some (.forAll [] p.2) ∨ Γ.types.find? p.1 = none)
    -- Every written-to name's type is well-kinded in `C` — the premise upstream added to
    -- the `init` rules that `initChain_types` now has to discharge.
    (hwk : ∀ p ∈ (substSig σ M ++ T).toList, C.WellKindedTy p.2) :
    StatementsHasTypeA P C Γ L
      (initChain (missingIn Γ (substSig σ M ++ T)) ++
        [Statement.call pname (mkArgs M T exprs mask) default]) C
      (insertAll Γ (missingIn Γ (substSig σ M ++ T))) := by
  -- The instantiated write-list; kept spelled out (no `set` — Mathlib absent).
  have hExNoFvar : ∀ i (hi : i < exprs.length) m x, (exprs[i]'hi) ≠ LExpr.fvar m x none := by
    intro i hi m x heq
    have hlen : i < I.values.length := by rw [lm_values_length, ← hExLen]; exact hi
    have := hExTy i hi hlen
    rw [heq] at this
    cases this
  have hNodup' : ((substSig σ M ++ T).map Prod.fst).Nodup := by
    rw [← ListMap.keys_eq_map_fst]; exact hNodup
  -- The missing-only chain is Nodup (a sublist of a Nodup list).
  have hmissNodup : ((missingIn Γ (substSig σ M ++ T)).map Prod.fst).Nodup :=
    List.Nodup.sublist (List.Sublist.map _ (missingIn_sublist Γ (substSig σ M ++ T))) hNodup'
  -- The chain is well-typed: each missing name is fresh at its declaration point.
  have hchain : StatementsHasTypeA P C Γ L
      (initChain (missingIn Γ (substSig σ M ++ T))) C (insertAll Γ (missingIn Γ (substSig σ M ++ T))) := by
    apply initChain_types (missingIn Γ (substSig σ M ++ T))
      (fun p hp => hwk p (missingIn_sublist Γ (substSig σ M ++ T) |>.mem hp)) Γ
    intro i hi
    rw [insertAll_find_not_mem ((missingIn Γ (substSig σ M ++ T)).take i) Γ _ ?_]
    · exact missingIn_find_none Γ (substSig σ M ++ T) (List.getElem_mem hi)
    · rw [List.map_take]
      have hidx : i < ((missingIn Γ (substSig σ M ++ T)).map Prod.fst).length := by
        rw [List.length_map]; exact hi
      have := nodup_getElem_not_mem_take hmissNodup i hidx
      simpa [List.getElem_map] using this
  -- Every written-to name is in scope at its recorded type in the chained context:
  -- reused names survive `insertAll` (they were not inserted), init'ed names are
  -- inserted at exactly that type.
  have hInScope : ∀ p ∈ (substSig σ M ++ T).toList,
      (insertAll Γ (missingIn Γ (substSig σ M ++ T))).types.find? p.1 = some (.forAll [] p.2) := by
    intro p hp
    rcases hReuse p hp with hbound | habsent
    · exact insertAll_missing_preserves Γ (substSig σ M ++ T) p.1 _ hbound
    · refine insertAll_find_mem (missingIn Γ (substSig σ M ++ T)) Γ p.1 p.2 hmissNodup ?_
      exact List.mem_filter.mpr ⟨hp, by simp [habsent]⟩
  -- `hMinΓ`: the in-out names are bound at their *instantiated* types. The
  -- instantiated block `substSig σ M` has keys `= M.keys` and values `= subst [σ] …`.
  have hMinΓ : ∀ i (hi : i < M.keys.length) (hj : i < M.values.length),
      (insertAll Γ (missingIn Γ (substSig σ M ++ T))).types.find? (M.keys[i]'hi)
        = some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (M.values[i]'hj))) := by
    intro i hi hj
    have hiK : i < (substSig σ M).keys.length := by rw [substSig_keys]; exact hi
    have hiV : i < (substSig σ M).values.length := by
      rw [lm_values_length, substSig_length, ← lm_values_length]; exact hj
    have hmem := List.mem_append_left T.toList (keyval_mem (substSig σ M) i hiK hiV)
    rw [substSig_keys_getElem σ M i hiK hi, substSig_values_getElem σ M i hiV hj] at hmem
    exact hInScope _ hmem
  -- `hTinΓ`: the targets are bound at their own recorded type, which equals the
  -- instantiated out type positionally (`hTVals`).
  have hTinΓ : ∀ i (hi : i < T.keys.length) (hj : i < O.values.length),
      (insertAll Γ (missingIn Γ (substSig σ M ++ T))).types.find? (T.keys[i]'hi)
        = some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (O.values[i]'hj))) := by
    intro i hi hj
    have hjOσ : i < (substSig σ O).values.length := by
      rw [lm_values_length, substSig_length, ← lm_values_length]; exact hj
    have h := outTargets_inΓ (substSig σ O) T hTVals
      (Γ := insertAll Γ (missingIn Γ (substSig σ M ++ T)))
      (fun p hp => hInScope _ (List.mem_append_right (substSig σ M).toList hp)) i hi hjOσ
    rwa [substSig_values_getElem σ O i hjOσ hj] at h
  have hcall : StatementHasTypeA P C (insertAll Γ (missingIn Γ (substSig σ M ++ T))) L
      (Statement.call pname (mkArgs M T exprs mask) default) C
      (insertAll Γ (missingIn Γ (substSig σ M ++ T))) :=
    StatementHasType'.cmd C _ _ L _ _
      (call_recipe_inout_sound σ M I O T exprs mask hfind hInputs hOutputs hExLen
        (by rw [← lm_values_length T, ← lm_values_length O, hTVals, substSig_values,
              List.length_map])
        hMinΓ hTinΓ hExTy hExNoFvar hIdisjOut)
      (tctxEquivRefl _)
  exact StatementsHasTypeA_append hchain
    (StatementsHasType'.cons _ _ _ _ _ _ _ _ _ hcall
      (StatementsHasType'.nil C _ L _ (tctxEquivRefl _)))
