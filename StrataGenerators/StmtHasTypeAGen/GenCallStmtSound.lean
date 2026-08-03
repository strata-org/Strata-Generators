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
- `StmtsHasTypeA_append` — chaining two statement-list judgments.
-/

namespace StrataGenerators.Stmt

open Core.TypeSpec

-- ── Procedure-signature context (call targets) ────────────────────────────

/-- A callee's signature description, stored *directly* with the shared in-out
    block leading both roles. This layout is not automatic for an arbitrary
    `P`-procedure; it is what `genProcedure` emits and what a call site must
    respect. `M` = in-out block, `I` = input-only block, `O` = output-only block,
    so `inputs = M ++ I` and `outputs = M ++ O`. -/
structure ProcSig where
  /-- The callee's name (matched against `Program.Procedure.find?`). -/
  pname : String
  /-- The in-out (mutable) parameter block. -/
  M : @LMonoTySignature Unit
  /-- The input-only parameter block. -/
  I : @LMonoTySignature Unit
  /-- The output-only parameter block. -/
  O : @LMonoTySignature Unit

/-- The empty-signature procedure, so `ProcSig` is `Inhabited` (needed by
    `elements` and its support-inversion lemma inside `genCallStmt`). -/
instance : Inhabited ProcSig := ⟨⟨"", [], [], []⟩⟩

/-- The set of callable procedures, each with its signature (shared in-out block
    leading both roles). -/
abbrev ProcSigCtx := List ProcSig

/-- `procs` faithfully describes callable procedures of `P`: each entry names a
    monomorphic procedure of `P` whose signature decomposes as recorded (shared
    block `M` leading both `inputs` and `outputs`), with the input-only keys
    disjoint from the LHS (`M ∪ O`) keys. Exactly the hypotheses
    `call_mixed_body_sound` consumes for the `.call` case. -/
def ProcSigCorresponds (procs : ProcSigCtx) (P : Program) : Prop :=
  ∀ s ∈ procs, ∃ proc, Program.Procedure.find? P s.pname = some proc ∧
    proc.header.typeArgs = [] ∧
    proc.header.inputs = s.M ++ s.I ∧
    proc.header.outputs = s.M ++ s.O ∧
    (∀ i (hi : i < s.I.keys.length), (s.M ++ s.O).keys.contains (s.I.keys[i]'hi) = false)

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

-- ── The call-argument recipe ──────────────────────────────────────────────

/-- Build the call arguments for a callee whose signature decomposes as
    `inputs = M ++ I`, `outputs = M ++ O` (`M` = in-out, `I` = input-only,
    `O` = output-only, the shared block `M` leading both). The in-out block leads
    (as `inoutArg` nodes, so each is a
    pass-by-reference variable named exactly `M.keys[i]`, as the call rule's in-out
    premise requires), followed by the by-value inputs `exprs` (as `inArg` nodes),
    followed by the output-only *targets* `T` (as `outArg` nodes). This layout makes
    the argument positions line up with the parameter positions the callee declares —
    see `getIn_mkArgs` / `getLhs_mkArgs`.

    `T` is a **separate** argument rather than the callee's own `O`, because the
    Core spec (§4.6.4) does not constrain an out argument's *name*: any writable
    variable of the declared type will do. `T` is therefore a caller-chosen list of
    receiving variables, required only to be as long as `O` and to match it
    *positionally in type* — see `outTargets` (the generator's choice) and the
    `hTinΓ` premise of the soundness theorems below, which pairs `T.keys[i]` with
    `O.values[i]`. -/
def mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr) : List (CallArg Expression) :=
  M.map (fun p => CallArg.inoutArg p.1) ++
    exprs.map CallArg.inArg ++
    T.map (fun p => CallArg.outArg p.1)

/-- `getInputExprs (mkArgs M T exprs)` is the in-out block turned into bare
    unannotated `fvar`s, followed by the by-value inputs (the out-argument targets
    contribute nothing to the input positions). -/
theorem getIn_mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr) :
    CallArg.getInputExprs (mkArgs M T exprs)
      = M.map (fun p => LExpr.fvar () p.1 none) ++ exprs := by
  simp only [mkArgs, CallArg.getInputExprs, List.filterMap_append, List.filterMap_map,
    Function.comp_def, filterMap_some_comp, filterMap_const_none, List.filterMap_some,
    List.append_nil]

/-- `getLhs (mkArgs M T exprs)` is the LHS (assignable) positions: the in-out keys
    followed by the out-argument target names (the by-value inputs contribute
    nothing). -/
theorem getLhs_mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr) :
    CallArg.getLhs (mkArgs M T exprs) = M.keys ++ T.keys := by
  simp only [mkArgs, CallArg.getLhs, List.filterMap_append, List.filterMap_map,
    Function.comp_def, filterMap_some_comp, filterMap_const_none, List.append_nil,
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

/-- Running `initChain news` from `Γ` (where each declared name is fresh at the
    point it is declared) is well-typed and yields `insertAll Γ news`. -/
theorem initChain_types {P : Program} {C : LContext CoreLParams} {L : List String}
    (news : List (Identifier Unit × LMonoTy)) : ∀ (Γ : TContext Unit),
    (∀ i (hi : i < news.length),
      (insertAll Γ (news.take i)).types.find? (news[i].1) = none) →
    StmtsHasTypeA P C Γ L (initChain news) C (insertAll Γ news) := by
  induction news with
  | nil => intro Γ _; exact StmtsHasType'.nil C Γ L
  | cons hd tl ih =>
    intro Γ hfresh
    -- head is fresh in Γ = insertAll Γ (take 0)
    have hfresh0 : Γ.types.find? hd.1 = none := by
      have := hfresh 0 (by simp)
      simpa [insertAll, List.take] using this
    -- the head statement types Γ → {Γ with x ↦ ∀[].mty}
    have hhead : StmtHasTypeA P C Γ L
        (Statement.init hd.1 (.forAll [] hd.2) .nondet default) C
        { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) } :=
      StmtHasType'.cmd C Γ _ L _
        (CmdExtHasType'.cmd Γ _ _
          (CmdHasType'.init_nondet Γ hd.1 (.forAll [] hd.2) hd.2 [] default hfresh0 rfl
            (rigidAnnotCompat_forAll_nil hd.2)))
    -- the tail types from the inserted context
    have htail : StmtsHasTypeA P C
        { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) } L
        (initChain tl) C (insertAll Γ (hd :: tl)) := by
      have hins : insertAll Γ (hd :: tl)
          = insertAll { Γ with types := Γ.types.insert hd.1 (.forAll [] hd.2) } tl := by
        simp [insertAll]
      rw [hins]
      apply ih
      intro i hi
      have := hfresh (i + 1) (by simpa using Nat.succ_lt_succ hi)
      simpa [insertAll, List.take] using this
    exact StmtsHasType'.cons C C C Γ
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
    exact Maps.find?_insert_ne _ x hd.1 _ hne

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
      exact Maps.find?_insert_self _ hd.1 _
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
    the call `CmdExt.call pname (mkArgs M T exprs) md` type-checks (leaving `Γ`
    unchanged).

    Note the asymmetry between the two written-to blocks, which mirrors the spec:
    the in-out names are `M`'s own (the call rule pins them), whereas the out-only
    positions are filled by the *caller-chosen* `T` and are related to `O` only
    through their types (`hTinΓ`). -/
theorem call_recipe_inout_sound
    {C : LContext CoreLParams} {P : Program} {Γ : TContext Unit}
    {pname : String} {proc : Procedure} {md : MetaData Expression}
    (M I O T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (hfind : Program.Procedure.find? P pname = some proc)
    (hInputs : proc.header.inputs = M ++ I)
    (hOutputs : proc.header.outputs = M ++ O)
    (hExLen : exprs.length = I.length)
    (hTLen : T.length = O.length)
    (hMinΓ : ∀ i (hi : i < M.keys.length) (hj : i < M.values.length),
      Γ.types.find? (M.keys[i]'hi) = some (.forAll [] (M.values[i]'hj)))
    (hTinΓ : ∀ i (hi : i < T.keys.length) (hj : i < O.values.length),
      Γ.types.find? (T.keys[i]'hi) = some (.forAll [] (O.values[i]'hj)))
    (hExTy : ∀ i (hi : i < exprs.length) (hj : i < I.values.length),
      LExpr.HasTypeA [] (exprs[i]'hi) (I.values[i]'hj))
    (hExNoFvar : ∀ i (hi : i < exprs.length) m x, (exprs[i]'hi) ≠ LExpr.fvar m x none)
    (hIdisjOut : ∀ i (hi : i < I.keys.length),
      (M ++ O).keys.contains (I.keys[i]'(by simpa using hi)) = false) :
    CmdExtHasTypeA C P Γ (CmdExt.call pname (mkArgs M T exprs) md) Γ := by
  -- σ := [] (identity substitution), so subst is the identity on all declared types.
  have hEmpty : Subst.hasEmptyScopes ([([] : List (TyIdentifier × LMonoTy))] : Subst) := by
    simp +ground
  -- length facts
  have hkeysM : M.keys.length = M.length := ListMap.keys.length
  have hvalsM : M.values.length = M.length := lm_values_length M
  have hkeysI : I.keys.length = I.length := ListMap.keys.length
  have hvalsI : I.values.length = I.length := lm_values_length I
  have hkeysO : O.keys.length = O.length := ListMap.keys.length
  have hvalsO : O.values.length = O.length := lm_values_length O
  have hkeysT : T.keys.length = O.length := by rw [ListMap.keys.length, hTLen]
  have hgetIn := getIn_mkArgs M T exprs
  have hgetLhs := getLhs_mkArgs M T exprs
  apply CmdExtHasType'.call Γ pname (mkArgs M T exprs) proc md []
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
    -- subst [[]] is the identity on all declared types.
    have hsubst : ∀ t : LMonoTy, LMonoTy.subst [[]] t = t := fun t => LMonoTy.subst_emptyS hEmpty
    rw [hsubst]
    -- length of the mapped M block
    have hmaplen : (List.map (fun p => (LExpr.fvar () p.1 none : Expression.Expr)) M).length
        = M.length := List.length_map ..
    -- pick the witness = the exact value at position i (so AliasEquiv is refl).
    refine ⟨(M.values ++ I.values)[i]'hj, AliasEquiv.refl, ?_⟩
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
    have hsubst : ∀ t : LMonoTy, LMonoTy.subst [[]] t = t := fun t => LMonoTy.subst_emptyS hEmpty
    rw [hsubst]
    refine ⟨(M.values ++ O.values)[i]'hj, AliasEquiv.refl, ?_⟩
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

/-- Concatenating two well-typed statement lists (threading the mid context)
    yields a well-typed statement list. -/
theorem StmtsHasTypeA_append {P : Program} {L : List String}
    {l1 : List Statement} :
    ∀ {C Γ Γ' Γ'' : _} {C' C'' : _} {l2 : List Statement},
    StmtsHasTypeA P C Γ L l1 C' Γ' →
    StmtsHasTypeA P C' Γ' L l2 C'' Γ'' →
    StmtsHasTypeA P C Γ L (l1 ++ l2) C'' Γ'' := by
  induction l1 with
  | nil =>
    intro C Γ Γ' Γ'' C' C'' l2 h1 h2
    cases h1 with
    | nil => simpa using h2
  | cons hd tl ih =>
    intro C Γ Γ' Γ'' C' C'' l2 h1 h2
    cases h1 with
    | cons _ Ca _ _ Γa _ _ _ _ hs hss =>
      exact StmtsHasType'.cons _ _ _ _ _ _ _ _ _ hs (ih hss h2)

/-- A single well-typed statement is a well-typed statement list of length one.
    Used throughout the generator's soundness proof: every `genStmt` branch but
    `call` produces a singleton list, so its per-constructor `StmtHasTypeA` fact is
    lifted through this. -/
theorem StmtsHasTypeA_singleton {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {L : List String} {s : Statement}
    (h : StmtHasTypeA P C Γ L s C' Γ') :
    StmtsHasTypeA P C Γ L [s] C' Γ' :=
  StmtsHasType'.cons _ _ _ _ _ _ _ _ _ h (StmtsHasType'.nil _ _ _)

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
    (M I O T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (hfind : Program.Procedure.find? P pname = some proc)
    (hInputs : proc.header.inputs = M ++ I)
    (hOutputs : proc.header.outputs = M ++ O)
    (hExLen : exprs.length = I.length)
    (hTVals : T.values = O.values)
    (hExTy : ∀ i (hi : i < exprs.length) (hj : i < I.values.length),
      LExpr.HasTypeA [] (exprs[i]'hi) (I.values[i]'hj))
    (hIdisjOut : ∀ i (hi : i < I.keys.length),
      (M ++ O).keys.contains (I.keys[i]'(by simpa using hi)) = false)
    (hNodup : (M ++ T).keys.Nodup)
    -- Each such name is *either* already bound at its recorded type, *or* absent.
    (hReuse : ∀ p ∈ (M ++ T).toList,
      Γ.types.find? p.1 = some (.forAll [] p.2) ∨ Γ.types.find? p.1 = none) :
    StmtsHasTypeA P C Γ L
      (initChain (missingIn Γ (M ++ T)) ++
        [Statement.call pname (mkArgs M T exprs) default]) C
      (insertAll Γ (missingIn Γ (M ++ T))) := by
  have hExNoFvar : ∀ i (hi : i < exprs.length) m x, (exprs[i]'hi) ≠ LExpr.fvar m x none := by
    intro i hi m x heq
    have hlen : i < I.values.length := by rw [lm_values_length, ← hExLen]; exact hi
    have := hExTy i hi hlen
    rw [heq] at this
    cases this
  have hNodup' : ((M ++ T).map Prod.fst).Nodup := by
    rw [← ListMap.keys_eq_map_fst]; exact hNodup
  -- The missing-only chain is Nodup (a sublist of a Nodup list).
  have hmissNodup : ((missingIn Γ (M ++ T)).map Prod.fst).Nodup :=
    List.Nodup.sublist (List.Sublist.map _ (missingIn_sublist Γ (M ++ T))) hNodup'
  -- The chain is well-typed: each missing name is fresh at its declaration point.
  have hchain : StmtsHasTypeA P C Γ L
      (initChain (missingIn Γ (M ++ T))) C (insertAll Γ (missingIn Γ (M ++ T))) := by
    apply initChain_types (missingIn Γ (M ++ T)) Γ
    intro i hi
    rw [insertAll_find_not_mem ((missingIn Γ (M ++ T)).take i) Γ _ ?_]
    · exact missingIn_find_none Γ (M ++ T) (List.getElem_mem hi)
    · rw [List.map_take]
      have hidx : i < ((missingIn Γ (M ++ T)).map Prod.fst).length := by
        rw [List.length_map]; exact hi
      have := nodup_getElem_not_mem_take hmissNodup i hidx
      simpa [List.getElem_map] using this
  -- Every written-to name is in scope at its recorded type in the chained context:
  -- reused names survive `insertAll` (they were not inserted), init'ed names are
  -- inserted at exactly that type.
  have hInScope : ∀ p ∈ (M ++ T).toList,
      (insertAll Γ (missingIn Γ (M ++ T))).types.find? p.1 = some (.forAll [] p.2) := by
    intro p hp
    rcases hReuse p hp with hbound | habsent
    · exact insertAll_missing_preserves Γ (M ++ T) p.1 _ hbound
    · refine insertAll_find_mem (missingIn Γ (M ++ T)) Γ p.1 p.2 hmissNodup ?_
      exact List.mem_filter.mpr ⟨hp, by simp [habsent]⟩
  have hMinΓ : ∀ i (hi : i < M.keys.length) (hj : i < M.values.length),
      (insertAll Γ (missingIn Γ (M ++ T))).types.find? (M.keys[i]'hi)
        = some (.forAll [] (M.values[i]'hj)) := by
    intro i hi hj
    exact hInScope _ (List.mem_append_left _ (keyval_mem M i hi hj))
  have hTinΓ := outTargets_inΓ O T hTVals
    (Γ := insertAll Γ (missingIn Γ (M ++ T)))
    (fun p hp => hInScope _ (List.mem_append_right _ hp))
  have hcall : StmtHasTypeA P C (insertAll Γ (missingIn Γ (M ++ T))) L
      (Statement.call pname (mkArgs M T exprs) default) C
      (insertAll Γ (missingIn Γ (M ++ T))) :=
    StmtHasType'.cmd C _ _ L _
      (call_recipe_inout_sound M I O T exprs hfind hInputs hOutputs hExLen
        (lm_length_eq_of_values_eq hTVals) hMinΓ hTinΓ hExTy hExNoFvar hIdisjOut)
  exact StmtsHasTypeA_append hchain
    (StmtsHasType'.cons _ _ _ _ _ _ _ _ _ hcall
      (StmtsHasType'.nil C _ L))
