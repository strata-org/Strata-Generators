import StrataGenerators.CmdHasTypeAGen
import StrataGenerators.StmtHasTypeAGen.CallDefs
import Strata.Languages.Core.StatementTypeSpec
import Strata.Languages.Core.TypingSpec
import Strata.Languages.Core.CallWFProps

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen

/-!
# Soundness of the procedure-call statement generator

This file collects the *context-independent* helper lemmas required to establish
`genCallStmt` sound (the `.call` case of `genStmt_sound`, assembled in
`StmtHasTypeAGen.lean`). None of them refers to `genStmt`/`genStmts`.

- `mkArgs` builds the argument list of a call. `getIn_mkArgs`, `getLhs_mkArgs`,
  `inputArgs_mkArgs` and `resultArgs_mkArgs` compute its projections, and `argsMatch_mkArgs`
  matches it with the callee's signature.
- `call_recipe_inout_sound` discharges the premises of `CmdExtWellTyped.call`.
- `initChain`, `insertAll` and `initChain_types` describe the chain of `init … nondet` statements
  that brings each necessary name into scope, at its declared type.
- `StatementsWellTyped_append` joins two judgments about a statement list.
-/

namespace StrataGenerators.Stmt

open Core.TypeSpec

-- ── filterMap helper lemmas ───────────────────────────────────────────────

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

-- ── Forall₂ and substitution lemmas ───────────────────────────────────────

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

/-- `Interleave xs ys zs` says that `zs` is an **interleaving that keeps the order** of `xs` and of `ys`. It
    holds each element of both lists, and it keeps the relative order inside `xs` and the relative order inside
    `ys`. It puts no other condition, so the two lists can interleave in any way.

    This is exactly the freedom the `call` rule leaves between the by-value inputs
    and the out targets: `CallArg.getInputExprs` keeps the `inArg` order and drops
    every `outArg`, and `CallArg.getLhs` does the reverse, so neither projection can
    see how the two kinds interleave. -/
inductive Interleave {α : Type} : List α → List α → List α → Prop
  | nil : Interleave [] [] []
  | left {x : α} {xs ys zs : List α} :
      Interleave xs ys zs → Interleave (x :: xs) ys (x :: zs)
  | right {y : α} {xs ys zs : List α} :
      Interleave xs ys zs → Interleave xs (y :: ys) (y :: zs)

/-- **Surjectivity of the mask.** *Every* order-preserving interleaving of `xs` and
    `ys` is `mergeBy mask xs ys` for some `mask`. The mask bits are read straight off
    the derivation: `left` becomes `true`, `right` becomes `false`.

    That fact is what makes the existential over the mask in `CallOk` cost nothing. Read
    `mkArgs_surjective` for the form of this claim at the level of a call argument. -/
theorem mergeBy_surjective {α : Type} {xs ys zs : List α} (h : Interleave xs ys zs) :
    ∃ mask : List Bool, mergeBy mask xs ys = zs := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | left _ ih =>
    obtain ⟨mask, hm⟩ := ih
    exact ⟨true :: mask, by rw [mergeBy, hm]⟩
  | right _ ih =>
    obtain ⟨mask, hm⟩ := ih
    exact ⟨false :: mask, by rw [mergeBy, hm]⟩

/-- Taking every element from the right list is an interleaving. -/
theorem interleave_nil_left {α : Type} (ys : List α) : Interleave [] ys ys := by
  induction ys with
  | nil => exact .nil
  | cons _ _ ih => exact .right ih

/-- Concatenation is an interleaving. This is the case an exhausted mask falls back
    to, and it is why the `[]` equation of `mergeBy` does not escape the relation. -/
theorem interleave_append {α : Type} (xs ys : List α) : Interleave xs ys (xs ++ ys) := by
  induction xs with
  | nil => exact interleave_nil_left ys
  | cons _ _ ih => exact .left ih

/-- **The mask gives an interleaving only.** This lemma is the converse of `mergeBy_surjective`. The
    statement below needs both directions, so that it says that the mask is neither too weak nor too
    strong. -/
theorem mergeBy_interleave {α : Type} (mask : List Bool) :
    ∀ (xs ys : List α), Interleave xs ys (mergeBy mask xs ys) := by
  induction mask with
  | nil => intro xs ys; rw [mergeBy]; exact interleave_append xs ys
  | cons b mask ih =>
    intro xs ys
    cases b with
    | true =>
      cases xs with
      | nil => rw [mergeBy]; exact ih [] ys
      | cons x xs => rw [mergeBy]; exact .left (ih xs ys)
    | false =>
      cases ys with
      | nil => rw [mergeBy]; exact ih xs []
      | cons y ys => rw [mergeBy]; exact .right (ih xs ys)

/-- **The mask ranges over exactly the order-preserving interleavings**, no fewer and
    no more. -/
theorem exists_mask_iff_interleave {α : Type} {xs ys zs : List α} :
    (∃ mask : List Bool, mergeBy mask xs ys = zs) ↔ Interleave xs ys zs :=
  ⟨fun ⟨mask, hm⟩ => hm ▸ mergeBy_interleave mask xs ys, mergeBy_surjective⟩

-- The mask semantics, executably: a leading `false` takes the right list first, and
-- the merge genuinely interleaves rather than concatenating.
#guard mergeBy [false] [1, 2] [3] == ([3, 1, 2] : List Nat)
#guard mergeBy [true, false] [1, 2] [3] == ([1, 3, 2] : List Nat)
-- An exhausted mask falls back to concatenation (`interleave_append`).
#guard mergeBy [] [1, 2] [3] == ([1, 2, 3] : List Nat)

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
  rw [mkArgs, CallArg.getInputExprs, Calls.getInputExprs, List.filterMap_append,
    filterMap_mergeBy_left _ mask _ _
      (by rintro a ha; simp only [List.mem_map] at ha; obtain ⟨p, _, rfl⟩ := ha; rfl)]
  simp only [List.filterMap_map, Function.comp_def, filterMap_some_comp,
    List.filterMap_some]
  rfl

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

/-- **Every argument order the `call` rule leaves free is reachable.** Fix a callee
    block `M`/`T` and by-value inputs `exprs`. For *any* order-preserving
    interleaving `rest` of the `inArg` nodes with the `outArg` nodes, some mask makes
    `mkArgs` emit exactly the in-out block followed by `rest`.

    Therefore `mkArgs` fixes only what the rule itself forces, which is that the in-out block comes first,
    because that block heads both projections. Read the `#guard`s above. The existential over the mask in
    `CallOk` puts no other limit on the order. `mkArgs_out_then_in` is one instance of this theorem, at the
    call `call p(out y, 1);`. -/
-- **`Interleave` holds at the swap that matters**, so `mkArgs_surjective` has real content. The one out
-- target before the one by-value input is exactly the shape of the call `call p(out y, 1);`.
example : Interleave [CallArg.inArg gcaExpr] [CallArg.outArg gcaY]
    ([CallArg.outArg gcaY, CallArg.inArg gcaExpr] : GcaArgs) :=
  .right (.left .nil)

theorem mkArgs_surjective (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (rest : List (CallArg Expression))
    (h : Interleave (exprs.map CallArg.inArg)
      (T.map (fun p => CallArg.outArg p.1)) rest) :
    ∃ mask : List Bool,
      mkArgs M T exprs mask = M.map (fun p => CallArg.inoutArg p.1) ++ rest := by
  obtain ⟨mask, hm⟩ := mergeBy_surjective h
  exact ⟨mask, by rw [mkArgs, hm]⟩

/-- The `mkArgs` counterpart of `exists_mask_iff_interleave`: an argument list is
    reachable at *some* mask precisely when its tail interleaves the by-value inputs
    with the out targets. -/
theorem exists_mask_mkArgs_iff (M T : @LMonoTySignature Unit)
    (exprs : List Expression.Expr) (rest : List (CallArg Expression)) :
    (∃ mask : List Bool,
      mkArgs M T exprs mask = M.map (fun p => CallArg.inoutArg p.1) ++ rest)
      ↔ Interleave (exprs.map CallArg.inArg) (T.map (fun p => CallArg.outArg p.1)) rest := by
  rw [← exists_mask_iff_interleave]
  constructor
  · rintro ⟨mask, hm⟩
    exact ⟨mask, by rw [mkArgs] at hm; exact List.append_cancel_left hm⟩
  · rintro ⟨mask, hm⟩
    exact ⟨mask, by rw [mkArgs, hm]⟩

-- ── The init-chain that brings the required names into scope ───────────────

/-- The variable scopes after running `initChain news` from `ts`: each declared `(x, mty)` is
    inserted as `x ↦ ∀[]. mty`. -/
def insertAll (ts : TypeScopes) (news : List (Identifier Unit × LMonoTy)) : TypeScopes :=
  news.foldl (fun ts p => ts.insert p.1 (.forAll [] p.2)) ts

/-- `insertAll` respects `HMaps.Equiv`: inserting the same bindings into equivalent scopes keeps
    them equivalent. -/
theorem insertAll_equiv (news : List (Identifier Unit × LMonoTy)) {ts ts' : TypeScopes}
    (h : Strata.Util.HMaps.Equiv ts ts') :
    Strata.Util.HMaps.Equiv (insertAll ts news) (insertAll ts' news) := by
  induction news generalizing ts ts' with
  | nil => exact h
  | cons hd tl ih => exact ih (Strata.Util.HMaps.insert_equiv h hd.1 (.forAll [] hd.2))

/-- `insertAllCtx` peels one declaration off the front (it is a `foldl`). -/
theorem insertAllCtx_cons (ctx : VarCtx) (hd : Identifier Unit × LMonoTy)
    (tl : List (Identifier Unit × LMonoTy)) :
    insertAllCtx ctx (hd :: tl) = insertAllCtx (Map.insert ctx hd.1 hd.2) tl := by
  simp [insertAllCtx]

/-- Declaring a `Nodup` list of names, each absent from `ctx`, preserves
    functionality: every insert is of a key fresh at the point it happens (fresh in
    `ctx` by hypothesis, and each earlier insert uses a different key. This
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

/-- Running `initChain news` from `ts` is well-typed and yields `insertAll ts news`, when each
    declared name is fresh at the point it is declared and every declared type is well kinded in
    `C`. These are the premises of `CmdWellTyped.init_nondet`. -/
theorem initChain_types {P : Program} {C : LContext CoreLParams} {L : List String}
    (news : List (Identifier Unit × LMonoTy))
    (hwk : ∀ p ∈ news, C.WellKindedTy p.2) : ∀ (ts : TypeScopes),
    (∀ i (hi : i < news.length), (insertAll ts (news.take i)).find? (news[i].1) = none) →
    StatementsWellTyped P C ts L (initChain news) C (insertAll ts news) := by
  induction news with
  | nil => intro ts _; exact .nil C ts L ts (Strata.Util.HMaps.Equiv.refl ts)
  | cons hd tl ih =>
    intro ts hfresh
    have hfresh0 : ts.find? hd.1 = none := by
      have h0 := hfresh 0 (by simp)
      simpa [insertAll, List.take] using h0
    have hhead : StatementWellTyped P C ts L
        (Statement.init hd.1 (.forAll [] hd.2) .nondet default) C
        (ts.insert hd.1 (.forAll [] hd.2)) :=
      .cmd C ts _ L _ _
        (.cmd ts _ _ (.init_nondet ts hd.1 (.forAll [] hd.2) hd.2 default _ hfresh0 rfl
          (hwk hd List.mem_cons_self) (Strata.Util.HMaps.Equiv.refl _)))
        (Strata.Util.HMaps.Equiv.refl _)
    have htail : StatementsWellTyped P C (ts.insert hd.1 (.forAll [] hd.2)) L
        (initChain tl) C (insertAll ts (hd :: tl)) := by
      refine ih (fun p hp => hwk p (List.mem_cons_of_mem _ hp)) _ ?_
      intro i hi
      have hi' := hfresh (i + 1) (by simpa using Nat.succ_lt_succ hi)
      simpa [insertAll, List.take] using hi'
    exact .cons C C C ts _ _ L _ _ hhead htail

-- ── `insertAll` lookup bookkeeping ────────────────────────────────────────

/-- Looking up a name absent from `news` in `insertAll ts news` falls through to `ts`. -/
theorem insertAll_find_not_mem (news : List (Identifier Unit × LMonoTy)) :
    ∀ (ts : TypeScopes) (x : Identifier Unit),
    x ∉ news.map Prod.fst → (insertAll ts news).find? x = ts.find? x := by
  induction news with
  | nil => intro ts x _; rfl
  | cons hd tl ih =>
    intro ts x hx
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    obtain ⟨hne, hxtl⟩ := hx
    show (insertAll (ts.insert hd.1 (.forAll [] hd.2)) tl).find? x = ts.find? x
    rw [ih _ x hxtl]
    exact Strata.Util.HMaps.find?_insert_ne _ x hd.1 _ hne

/-- Looking up a member key of `news` in `insertAll ts news` returns that member's (wrapped)
    value, provided the keys are `Nodup` (so no later insert shadows an earlier one). -/
theorem insertAll_find_mem (news : List (Identifier Unit × LMonoTy)) :
    ∀ (ts : TypeScopes) (x : Identifier Unit) (mty : LMonoTy),
    (news.map Prod.fst).Nodup → (x, mty) ∈ news →
    (insertAll ts news).find? x = some (.forAll [] mty) := by
  induction news with
  | nil => intro _ _ _ _ hmem; exact absurd hmem (by simp)
  | cons hd tl ih =>
    intro ts x mty hnd hmem
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hndtl⟩ := hnd
    show (insertAll (ts.insert hd.1 (.forAll [] hd.2)) tl).find? x = some (.forAll [] mty)
    rcases List.mem_cons.mp hmem with heq | hmemtl
    · -- `x` is the head key: the head is never overwritten by the (disjoint) tail.
      have hx : x = hd.1 := (Prod.mk.injEq .. ▸ heq).1
      have hm : mty = hd.2 := (Prod.mk.injEq .. ▸ heq).2
      subst hx; subst hm
      rw [insertAll_find_not_mem tl _ hd.1 hnotin]
      exact Strata.Util.HMaps.find?_insert_self _ hd.1 _
    · exact ih _ x mty hndtl hmemtl

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
  have : j = i := (List.getElem?_inj (by omega) hnd).mp (by
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

-- ── The call-typing obligation ───────────────────────────────────────────

/-- A filter that keeps every element of `xs` and drops every element of `ys` sees
    `mergeBy bs xs ys` as `xs`. -/
theorem filter_mergeBy_left {α : Type} (p : α → Bool) (bs : List Bool) (xs ys : List α)
    (hx : ∀ a ∈ xs, p a = true) (hy : ∀ a ∈ ys, p a = false) :
    (mergeBy bs xs ys).filter p = xs := by
  rw [← List.filterMap_eq_filter, filterMap_mergeBy_left _ bs xs ys ?_, List.filterMap_eq_filter]
  · exact List.filter_eq_self.mpr hx
  · intro a ha
    simp [Option.guard, hy a ha]

/-- A filter that drops every element of `xs` and keeps every element of `ys` sees
    `mergeBy bs xs ys` as `ys`. -/
theorem filter_mergeBy_right {α : Type} (p : α → Bool) (bs : List Bool) (xs ys : List α)
    (hx : ∀ a ∈ xs, p a = false) (hy : ∀ a ∈ ys, p a = true) :
    (mergeBy bs xs ys).filter p = ys := by
  rw [← List.filterMap_eq_filter, filterMap_mergeBy_right _ bs xs ys ?_, List.filterMap_eq_filter]
  · exact List.filter_eq_self.mpr hy
  · intro a ha
    simp [Option.guard, hx a ha]

/-- The arguments of `mkArgs M T exprs mask` for the input formals, in order: the in-out block,
    then the by-value inputs. -/
theorem inputArgs_mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool) :
    CallArg.inputArgs (mkArgs M T exprs mask) =
      M.map (fun p => CallArg.inoutArg p.1) ++ exprs.map CallArg.inArg := by
  rw [mkArgs, CallArg.inputArgs, List.filter_append, filter_mergeBy_left _ mask _ _ ?_ ?_]
  · rw [List.filter_eq_self.mpr]
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    rfl
  · intro a ha
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
    rfl
  · intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    rfl

/-- The arguments of `mkArgs M T exprs mask` for the output formals, in order: the in-out block,
    then the out targets. -/
theorem resultArgs_mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool) :
    CallArg.resultArgs (mkArgs M T exprs mask) =
      M.map (fun p => CallArg.inoutArg p.1) ++ T.map (fun p => CallArg.outArg p.1) := by
  rw [mkArgs, CallArg.resultArgs, List.filter_append, filter_mergeBy_right _ mask _ _ ?_ ?_]
  · rw [List.filter_eq_self.mpr]
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    rfl
  · intro a ha
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
    rfl
  · intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    rfl

/-- A pair in the `zip` of the keys of a signature with the images of its keys under `f` is a key
    paired with its own image. -/
theorem mem_zip_keys_map {β γ : Type} (M : ListMap (Identifier Unit) β)
    (f : Identifier Unit → γ) {k : Identifier Unit} {a : γ}
    (h : (k, a) ∈ M.keys.zip (M.map (fun p => f p.1))) : k ∈ M.keys ∧ a = f k := by
  rw [ListMap.keys_eq_map_fst] at h ⊢
  induction M with
  | nil => exact absurd h (by simp)
  | cons q M ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨hk, ha⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hk, ha⟩

/-- In `xs ++ ys`, the first position of a member of `xs` is its first position in `xs`. -/
theorem idxOf?_append_of_mem {α : Type} [BEq α] [LawfulBEq α] {xs ys : List α} {a : α}
    (h : a ∈ xs) : (xs ++ ys).idxOf? a = xs.idxOf? a := by
  induction xs with
  | nil => exact absurd h List.not_mem_nil
  | cons x xs ih =>
    rw [List.cons_append, List.idxOf?_cons, List.idxOf?_cons]
    split
    · rfl
    · rename_i hne
      have hmem : a ∈ xs := by
        rcases List.mem_cons.mp h with rfl | hm
        · exact absurd (beq_self_eq_true a) hne
        · exact hm
      rw [ih hmem]

/-- **The arguments of `mkArgs` match the callee's signature.** Take a callee whose inputs are
    `M ++ I` and whose outputs are `M ++ O`, where no input-only name is an in-out or output-only
    name and no in-out name is an output-only name. With one by-value input for each input-only
    parameter and one target for each output-only parameter, every in-out argument names the
    result variable at its own output position, every input-only formal receives an `in`
    argument, and every output-only formal receives an `out` argument. -/
theorem argsMatch_mkArgs {proc : Procedure} (M I O T : @LMonoTySignature Unit)
    (exprs : List Expression.Expr) (mask : List Bool)
    (hInputs : proc.header.inputs = M ++ I) (hOutputs : proc.header.outputs = M ++ O)
    (hExLen : exprs.length = I.length) (hTLen : T.length = O.length)
    (hInotMO : ∀ k ∈ I.keys, k ∉ (M ++ O).keys) (hMnotO : ∀ k ∈ M.keys, k ∉ O.keys) :
    WF.ArgsMatchSignature proc (mkArgs M T exprs mask) := by
  have hkM : M.keys.length = (M.map (fun p => CallArg.inoutArg (P := Expression) p.1)).length := by
    rw [List.length_map, ListMap.keys.length]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getIn_mkArgs, hInputs, List.length_append, List.length_map, hExLen, lm_length_append]
  · rw [getLhs_mkArgs, hOutputs, List.length_append, ListMap.keys.length, ListMap.keys.length,
      hTLen, lm_length_append]
  · rintro ⟨k, a⟩ hka
    rw [hInputs, lm_keys_append, inputArgs_mkArgs, List.zip_append hkM] at hka
    rw [hOutputs, lm_keys_append, getLhs_mkArgs]
    rcases List.mem_append.mp hka with hM | hI
    · obtain ⟨hk, rfl⟩ := mem_zip_keys_map M (fun x => CallArg.inoutArg (P := Expression) x) hM
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hk)
      obtain ⟨hjlt, hjeq, _⟩ := List.idxOf?_eq_some_iff.mp hj
      simp [WF.inputArgMatches, idxOf?_append_of_mem hk, hj, List.getElem?_append_left hjlt,
        List.getElem?_eq_getElem hjlt, hjeq]
    · obtain ⟨hk, ha⟩ := List.of_mem_zip hI
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
      have hnone : (M.keys ++ O.keys).idxOf? k = none := by
        rw [List.idxOf?_eq_none_iff, ← lm_keys_append]
        exact hInotMO k hk
      simp only [WF.inputArgMatches, hnone]
  · rintro ⟨k, a⟩ hka
    rw [hOutputs, lm_keys_append, resultArgs_mkArgs, List.zip_append hkM] at hka
    rw [hInputs, lm_keys_append]
    rcases List.mem_append.mp hka with hM | hO
    · obtain ⟨hk, rfl⟩ := mem_zip_keys_map M (fun x => CallArg.inoutArg (P := Expression) x) hM
      simp only [WF.outputArgMatches]
      exact List.contains_iff_mem.mpr (List.mem_append_left _ hk)
    · obtain ⟨hk, ha⟩ := List.of_mem_zip hO
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
      have hnotin : k ∉ M.keys ++ I.keys := by
        rw [List.mem_append, not_or]
        refine ⟨fun hkM' => hMnotO k hkM' hk, fun hkI => hInotMO k hkI ?_⟩
        rw [lm_keys_append]
        exact List.mem_append_right _ hk
      simp only [WF.outputArgMatches, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact Bool.eq_false_iff.mpr (fun hc => hnotin (List.contains_iff_mem.mp hc))

/-- Soundness of the in-out call recipe (shared block `M` leading both roles).
    Given a callee `proc` with `inputs = M ++ I`, `outputs = M ++ O`, where no input-only name is
    an in-out or output-only name and no in-out name is an output-only name, out-argument targets
    `T` positionally as long as `O`, every `M` name and every `T` name in scope at its
    instantiated declared type (`M.values[i]` resp. `O.values[i]`), by-value inputs `exprs` that
    are well-typed at the instantiated input types and are not bare unannotated `fvar`s, and
    written-to names `M.keys ++ T.keys` that are distinct, the call
    `CmdExt.call pname (mkArgs M T exprs mask) md` is well-typed and keeps the scopes.

    Note the asymmetry between the two written-to blocks, which mirrors the spec:
    the in-out names are `M`'s own (the call rule pins them), whereas the out-only
    positions are filled by the *caller-chosen* `T` and are related to `O` only
    through their types (`hTinΓ`). -/
theorem call_recipe_inout_sound
    {C : LContext CoreLParams} {P : Program} {ts : TypeScopes}
    {pname : String} {proc : Procedure} {md : MetaData Expression}
    (σ : List (TyIdentifier × LMonoTy))
    (M I O T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool)
    (hfind : Program.Procedure.find? P pname = some proc)
    (hInputs : proc.header.inputs = M ++ I)
    (hOutputs : proc.header.outputs = M ++ O)
    (hExLen : exprs.length = I.length)
    (hTLen : T.length = O.length)
    -- The variables the call writes back through are bound in `ts` at the *instantiated*
    -- formal type `subst [σ] (declared value)`, which is the type that the caller gave them at.
    (hMinΓ : ∀ i (hi : i < M.keys.length) (hj : i < M.values.length),
      ts.find? (M.keys[i]'hi) =
        some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (M.values[i]'hj))))
    (hTinΓ : ∀ i (hi : i < T.keys.length) (hj : i < O.values.length),
      ts.find? (T.keys[i]'hi) =
        some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (O.values[i]'hj))))
    -- Each by-value input is well-typed at the *instantiated* formal input type.
    (hExTy : ∀ i (hi : i < exprs.length) (hj : i < I.values.length),
      ExprWellTyped C ts (exprs[i]'hi)
        (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (I.values[i]'hj)))
    (hExNoFvar : ∀ i (hi : i < exprs.length) m x, (exprs[i]'hi) ≠ LExpr.fvar m x none)
    (hIdisjOut : ∀ i (hi : i < I.keys.length),
      (M ++ O).keys.contains (I.keys[i]'(by simpa using hi)) = false)
    (hMnotO : ∀ k ∈ M.keys, k ∉ O.keys)
    (hLhsNodup : (M.keys ++ T.keys).Nodup) :
    CmdExtWellTyped C P ts (CmdExt.call pname (mkArgs M T exprs mask) md) ts := by
  -- length facts
  have hkeysM : M.keys.length = M.length := ListMap.keys.length
  have hvalsM : M.values.length = M.length := lm_values_length M
  have hvalsI : I.values.length = I.length := lm_values_length I
  have hvalsO : O.values.length = O.length := lm_values_length O
  have hkeysT : T.keys.length = O.length := by rw [ListMap.keys.length, hTLen]
  have hgetIn := getIn_mkArgs M T exprs mask
  have hgetLhs := getLhs_mkArgs M T exprs mask
  have hInotMO : ∀ k ∈ I.keys, k ∉ (M ++ O).keys := by
    intro k hk hmem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
    have hc : (M ++ O).keys.contains (I.keys[i]'hi) = true := List.contains_iff_mem.mpr hmem
    rw [hIdisjOut i hi] at hc
    exact Bool.false_ne_true hc
  have hwf : WF.WFcallProp P pname (mkArgs M T exprs mask) :=
    WF.WFcallProp.of_argsMatch hfind
      (argsMatch_mkArgs M I O T exprs mask hInputs hOutputs hExLen hTLen hInotMO hMnotO)
      (by rw [hgetLhs]; exact hLhsNodup)
  refine .call ts pname (mkArgs M T exprs mask) proc md σ ts hfind hwf ?_ ?_ ?_
    (Strata.Util.HMaps.Equiv.refl ts)
  · -- every written-to variable is in scope
    intro v hv
    rw [hgetLhs, List.mem_append] at hv
    rcases hv with hvM | hvT
    · rw [List.mem_iff_getElem] at hvM
      obtain ⟨i, hi, hveq⟩ := hvM
      have hj : i < M.values.length := by rw [hvalsM]; rw [hkeysM] at hi; exact hi
      rw [← hveq, hMinΓ i hi hj]
      rfl
    · rw [List.mem_iff_getElem] at hvT
      obtain ⟨i, hi, hveq⟩ := hvT
      have hj : i < O.values.length := by rw [hvalsO]; rw [hkeysT] at hi; exact hi
      rw [← hveq, hTinΓ i hi hj]
      rfl
  · -- input types
    intro i hi hj
    simp only [hgetIn] at hi ⊢
    simp only [hInputs, lm_values_append] at hj ⊢
    have hmaplen : (List.map (fun p => (LExpr.fvar () p.1 none : Expression.Expr)) M).length
        = M.length := List.length_map ..
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
      exact hMinΓ i hidxK hidxM
    · -- by-value input block: `i ≥ M.length`, so the argument is `exprs[i - M.length]`.
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
      -- The by-value argument is not a bare unannotated `fvar`, so the match takes its
      -- expression branch.
      have hne := hExNoFvar (i - M.length) hiex
      have hExTyi := hExTy (i - M.length) hiex hjI
      cases hcase : exprs[i - M.length]'hiex with
      | fvar m x ty =>
        cases ty with
        | none => exact absurd hcase (hne m x)
        | some t =>
          rw [hcase] at hExTyi
          exact hExTyi
      | _ => rw [hcase] at hExTyi; exact hExTyi
  · -- output types
    intro i hi hj
    simp only [hgetLhs] at hi ⊢
    simp only [hOutputs, lm_values_append] at hj ⊢
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

/-- When out targets `T` carry, position by position, the types of the output signature `O`, and
    the scopes bind every target at its own type, then the scopes bind the target at each position
    `i` at the type `O` declares at `i`. -/
theorem outTargets_inΓ {ts : TypeScopes} (O T : @LMonoTySignature Unit)
    (hTVals : T.values = O.values)
    (hInScope : ∀ p ∈ T.toList, ts.find? p.1 = some (.forAll [] p.2)) :
    ∀ i (hi : i < T.keys.length) (hj : i < O.values.length),
      ts.find? (T.keys[i]'hi) = some (.forAll [] (O.values[i]'hj)) := by
  intro i hi hj
  have hiv : i < T.values.length := by
    rw [lm_values_length]; rw [ListMap.keys.length] at hi; exact hi
  have hval : T.values[i]'hiv = O.values[i]'hj := by
    simp only [← hTVals]
  rw [← hval]
  exact hInScope _ (keyval_mem T i hi hiv)

-- ── The typing rules respect equivalent and larger scopes ─────────────
--
-- Each typing-spec rule constrains its *output* scopes up to `HMaps.Equiv` only, because a stack
-- of scopes over a hash map reads no order of the insertions. Therefore a proof that joins two
-- derivations also needs each relation to respect that equivalence in its *input* scopes. A rule
-- reads its input scopes through `find?` only, and so does expression well-typedness.

/-- A well-typed expression stays well-typed in larger variable scopes: scopes that bind every
    name the original scopes bind, at the same type. Well-typedness reads the scopes through `find?`
    only. -/
theorem exprWellTyped_mono {C : LContext CoreLParams} {ts ts' : TypeScopes}
    {e : Expression.Expr} {τ : LMonoTy} (h : ExprWellTyped C ts e τ)
    (hts : ∀ x v, ts.find? x = some v → ts'.find? x = some v) : ExprWellTyped C ts' e τ :=
  ⟨h.1, h.2.1, ⟨fun x ann hx => hts _ _ (h.2.2.fvarsDeclared x ann hx), h.2.2.opsInstantiate,
    h.2.2.opsKnown⟩⟩

/-- A well-typed command stays well-typed, with the same output scopes, when its input scopes
    are replaced by equivalent ones: scopes with the same lookup for every name. -/
theorem cmdWellTyped_equiv_congr {C : LContext CoreLParams} {ts ts₂ ts' : TypeScopes}
    {c : Cmd Expression} (h : CmdWellTyped C ts c ts')
    (he : Strata.Util.HMaps.Equiv ts₂ ts) : CmdWellTyped C ts₂ c ts' := by
  have hf : ∀ x, ts₂.find? x = ts.find? x := fun x => Strata.Util.HMaps.Equiv.find? he x
  have hm : ∀ x v, ts.find? x = some v → ts₂.find? x = some v := fun x _ hx => (hf x).trans hx
  cases h with
  | init_det x _ _ _ _ _ hfind hfv hxty hwk hexpr heq =>
    exact .init_det _ _ _ _ _ _ _ ((hf x).trans hfind) hfv hxty hwk (exprWellTyped_mono hexpr hm)
      (heq.trans (Strata.Util.HMaps.insert_equiv he.symm x _))
  | init_nondet x _ _ _ _ hfind hxty hwk heq =>
    exact .init_nondet _ _ _ _ _ _ ((hf x).trans hfind) hxty hwk
      (heq.trans (Strata.Util.HMaps.insert_equiv he.symm x _))
  | set_det x _ _ _ _ hfind hexpr heq =>
    exact .set_det _ _ _ _ _ _ ((hf x).trans hfind) (exprWellTyped_mono hexpr hm)
      (heq.trans he.symm)
  | set_nondet x _ _ _ hfind heq =>
    exact .set_nondet _ _ _ _ _ ((hf x).trans hfind) (heq.trans he.symm)
  | assert _ _ _ _ hexpr heq =>
    exact .assert _ _ _ _ _ (exprWellTyped_mono hexpr hm) (heq.trans he.symm)
  | assume _ _ _ _ hexpr heq =>
    exact .assume _ _ _ _ _ (exprWellTyped_mono hexpr hm) (heq.trans he.symm)
  | cover _ _ _ _ hexpr heq =>
    exact .cover _ _ _ _ _ (exprWellTyped_mono hexpr hm) (heq.trans he.symm)

/-- A well-typed command or call stays well-typed, with the same output scopes, when its input
    scopes are replaced by equivalent ones: scopes with the same lookup for every name. -/
theorem cmdExtWellTyped_equiv_congr {C : LContext CoreLParams} {P : Program}
    {ts ts₂ ts' : TypeScopes} {c : Command} (h : CmdExtWellTyped C P ts c ts')
    (he : Strata.Util.HMaps.Equiv ts₂ ts) : CmdExtWellTyped C P ts₂ c ts' := by
  have hf : ∀ x, ts₂.find? x = ts.find? x := fun x => Strata.Util.HMaps.Equiv.find? he x
  have hm : ∀ x v, ts.find? x = some v → ts₂.find? x = some v := fun x _ hx => (hf x).trans hx
  cases h with
  | cmd c _ hc => exact .cmd ts₂ c _ (cmdWellTyped_equiv_congr hc he)
  | call pname callArgs proc md σ _ hfind hwf hlhs hargs hlhsTy heq =>
    refine .call ts₂ pname callArgs proc md σ _ hfind hwf ?_ ?_ ?_ (heq.trans he.symm)
    · intro v hv
      rw [hf v]
      exact hlhs v hv
    · intro i hi hj
      have hty := hargs i hi hj
      cases hcase : (CallArg.getInputExprs callArgs)[i] with
      | fvar m x ann =>
        cases ann with
        | none =>
          rw [hcase] at hty
          exact (hf x).trans hty
        | some t =>
          rw [hcase] at hty
          exact exprWellTyped_mono hty hm
      | _ =>
        rw [hcase] at hty
        exact exprWellTyped_mono hty hm
    · intro i hi hj
      exact (hf _).trans (hlhsTy i hi hj)

/-- The form of `statementsWellTyped_equiv_congr` that takes a fuel parameter.

    The relation is a `Prop`, so the equation compiler cannot recurse on a derivation. Recursion on
    the *syntax* covers both halves of the mutual definition in one function, because the body of a
    block, of a branch or of a loop inside the head statement is strictly smaller than the list.
    The recursion is on an explicit `Nat` fuel that bounds the size of the list, so each context
    stays a local variable that `cases` can substitute. -/
private theorem statementsWellTyped_equiv_congr_fuel {P : Program} : ∀ (n : Nat)
    (ss : List Statement) {C C' : LContext CoreLParams} {ts ts₂ ts' : TypeScopes}
    {L : List String}, sizeOf ss ≤ n →
    StatementsWellTyped P C ts L ss C' ts' →
    Strata.Util.HMaps.Equiv ts₂ ts →
    StatementsWellTyped P C ts₂ L ss C' ts' := by
  intro n
  induction n with
  | zero =>
    -- `sizeOf` of a list is at least 1, so there is no fuel-0 case.
    intro ss C C' ts ts₂ ts' L hfuel _ _
    cases ss <;> simp at hfuel
  | succ n ih =>
    intro ss C C' ts ts₂ ts' L hfuel h he
    have hm : ∀ x v, ts.find? x = some v → ts₂.find? x = some v :=
      fun x _ hx => (Strata.Util.HMaps.Equiv.find? he x).trans hx
    cases h with
    | nil _ _ L _ heq => exact .nil C ts₂ L _ (heq.trans he.symm)
    | cons _ Ca _ _ tsa _ L s ss' hs hss =>
      refine .cons C Ca _ ts₂ tsa _ L s ss' ?_ hss
      -- Only the head statement is retyped; the tail already starts from `tsa`.
      cases hs with
      | cmd _ _ tsc L c _ hc heq =>
        exact .cmd C ts₂ tsc L c _ (cmdExtWellTyped_equiv_congr hc he) heq
      | block _ _ C_body ts_body L label body md _ hfresh hbody heq =>
        exact .block C ts₂ C_body ts_body L label body md _ hfresh
          (ih body (by simp at hfuel; omega) hbody he) (heq.trans he.symm)
      | ite_det _ _ C_t ts_t C_e ts_e L cond thenb elseb md _ hcond hthen helse heq =>
        exact .ite_det C ts₂ C_t ts_t C_e ts_e L cond thenb elseb md _
          (exprWellTyped_mono hcond hm)
          (ih thenb (by simp at hfuel; omega) hthen he)
          (ih elseb (by simp at hfuel; omega) helse he) (heq.trans he.symm)
      | ite_nondet _ _ C_t ts_t C_e ts_e L thenb elseb md _ hthen helse heq =>
        exact .ite_nondet C ts₂ C_t ts_t C_e ts_e L thenb elseb md _
          (ih thenb (by simp at hfuel; omega) hthen he)
          (ih elseb (by simp at hfuel; omega) helse he) (heq.trans he.symm)
      | loop _ _ C_body ts_body L guard measure invariants body md _ hg hmeas hinv hbody heq =>
        exact .loop C ts₂ C_body ts_body L guard measure invariants body md _
          (fun g hgd => exprWellTyped_mono (hg g hgd) hm)
          (fun m hmd => exprWellTyped_mono (hmeas m hmd) hm)
          (fun p hp => exprWellTyped_mono (hinv p hp) hm)
          (ih body (by simp at hfuel; omega) hbody he) (heq.trans he.symm)
      | exit _ _ L label md _ hlab heq =>
        exact .exit C ts₂ L label md _ hlab (heq.trans he.symm)
      | typeDecl _ C'' _ L tc md _ hname hadd heq =>
        exact .typeDecl C _ ts₂ L tc md _ hname hadd (heq.trans he.symm)

/-- A well-typed statement list stays well-typed, with the same output context and scopes, when
    its input scopes are replaced by equivalent ones: scopes with the same lookup for every name. -/
theorem statementsWellTyped_equiv_congr {P : Program} {ss : List Statement}
    {C C' : LContext CoreLParams} {ts ts₂ ts' : TypeScopes} {L : List String}
    (h : StatementsWellTyped P C ts L ss C' ts')
    (he : Strata.Util.HMaps.Equiv ts₂ ts) :
    StatementsWellTyped P C ts₂ L ss C' ts' :=
  statementsWellTyped_equiv_congr_fuel (sizeOf ss) ss (Nat.le_refl _) h he

/-- Concatenating two well-typed statement lists (threading the middle scopes) gives a well-typed
    statement list. -/
theorem StatementsWellTyped_append {P : Program} {L : List String}
    {l1 : List Statement} :
    ∀ {C : LContext CoreLParams} {ts ts' ts'' : TypeScopes} {C' C'' : LContext CoreLParams}
      {l2 : List Statement},
    StatementsWellTyped P C ts L l1 C' ts' →
    StatementsWellTyped P C' ts' L l2 C'' ts'' →
    StatementsWellTyped P C ts L (l1 ++ l2) C'' ts'' := by
  induction l1 with
  | nil =>
    intro C ts ts' ts'' C' C'' l2 h1 h2
    cases h1 with
    | nil _ _ _ _ heq =>
      -- The empty list's output scopes are only `Equiv` to its input, so the tail's
      -- derivation has to be transported back along that equivalence.
      simpa using statementsWellTyped_equiv_congr h2 heq.symm
  | cons hd tl ih =>
    intro C ts ts' ts'' C' C'' l2 h1 h2
    cases h1 with
    | cons _ Ca _ _ tsa _ _ _ _ hs hss =>
      exact .cons _ _ _ _ _ _ _ _ _ hs (ih hss h2)

/-- A well-typed statement list stays well-typed when its output scopes are replaced by
    equivalent ones: scopes with the same lookup for every name. -/
theorem StatementsWellTyped_out_equiv {P : Program} {C C' : LContext CoreLParams}
    {ts ts' ts'' : TypeScopes} {L : List String} {ss : List Statement}
    (h : StatementsWellTyped P C ts L ss C' ts')
    (he : Strata.Util.HMaps.Equiv ts'' ts') :
    StatementsWellTyped P C ts L ss C' ts'' := by
  have hz := StatementsWellTyped_append h (.nil C' ts' L ts'' he)
  rwa [List.append_nil] at hz

/-- A single well-typed statement is a well-typed statement list of length one. Every
    `genStmt` branch but `call` produces a singleton list. -/
theorem StatementsWellTyped_singleton {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {s : Statement}
    (h : StatementWellTyped P C ts L s C' ts') :
    StatementsWellTyped P C ts L [s] C' ts' :=
  .cons _ _ _ _ _ _ _ _ _ h (.nil _ _ _ _ (Strata.Util.HMaps.Equiv.refl _))

-- ── Reuse-or-init: the general case (block-free when nothing is missing) ──

/-- The sub-list of `news` whose names are **not** yet bound in `ts`: exactly the names a call
    site must `init` before calling. Names already bound (at the right type, which the premise
    `hReuse` of `call_mixed_body_sound` gives) stay as they are. -/
def missingIn (ts : TypeScopes) (news : List (Identifier Unit × LMonoTy)) :
    List (Identifier Unit × LMonoTy) :=
  news.filter (fun p => (ts.find? p.1).isNone)

/-- The bindings that `missingIn` keeps form a sublist of the given bindings. -/
theorem missingIn_sublist (ts : TypeScopes) (news : List (Identifier Unit × LMonoTy)) :
    (missingIn ts news).Sublist news := List.filter_sublist

/-- Every `missingIn` name is absent from `ts`. -/
theorem missingIn_find_none (ts : TypeScopes) (news : List (Identifier Unit × LMonoTy))
    {p : Identifier Unit × LMonoTy} (hp : p ∈ missingIn ts news) :
    ts.find? p.1 = none := by
  have hsel := (List.mem_filter.mp hp).2
  simpa [Option.isNone_iff_eq_none] using hsel

/-- `insertAll ts (missingIn ts news)` does not change a name that `ts` already binds. The
    chain only inserts names that were absent, so reused bindings survive. -/
theorem insertAll_missing_preserves (ts : TypeScopes)
    (news : List (Identifier Unit × LMonoTy))
    (x : Identifier Unit) (v : LTy) (hx : ts.find? x = some v) :
    (insertAll ts (missingIn ts news)).find? x = some v := by
  have hnotin : x ∉ (missingIn ts news).map Prod.fst := by
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨p, hp, hpx⟩ := hmem
    have hnone := missingIn_find_none ts news hp
    rw [hpx, hx] at hnone
    exact absurd hnone (by simp)
  rw [insertAll_find_not_mem (missingIn ts news) ts x hnotin]
  exact hx

/-- **The general call case: reuse what is in scope, `init` only what is missing.**

    `news := M ++ T` are the variables the call writes to: the callee's in-out names `M` (which
    the call rule pins) and the caller-chosen out-argument targets `T` (positionally type-aligned
    with the callee's out-only block `O`, `hTVals`). Those already bound in `ts` at exactly their
    recorded type (`hReuse`) are reused; the rest (`missingIn ts news`) are brought into scope by
    an `init … nondet` chain. The emitted body is `initChain (missingIn ts news) ++ [call …]`,
    well-typed in `insertAll ts (missingIn ts news)`.

    When `missingIn ts news = []` the chain is empty, so the body is the bare call and the output
    scopes are `ts` itself, which is the common shape in real Strata code. -/
theorem call_mixed_body_sound
    {C : LContext CoreLParams} {P : Program} {ts : TypeScopes} {L : List String}
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
    -- The by-value inputs are well-typed at the *instantiated* formal input types.
    (hExTy : ∀ i (hi : i < exprs.length) (hj : i < I.values.length),
      ExprWellTyped C ts (exprs[i]'hi)
        (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (I.values[i]'hj)))
    (hIdisjOut : ∀ i (hi : i < I.keys.length),
      (M ++ O).keys.contains (I.keys[i]'(by simpa using hi)) = false)
    (hMnotO : ∀ k ∈ M.keys, k ∉ O.keys)
    -- The write-list is the *instantiated* in-out block followed by the targets.
    (hNodup : (substSig σ M ++ T).keys.Nodup)
    -- Each written-to name is *either* already bound at its recorded type, *or* absent.
    (hReuse : ∀ p ∈ (substSig σ M ++ T).toList,
      ts.find? p.1 = some (.forAll [] p.2) ∨ ts.find? p.1 = none)
    -- The type of each written-to name is well-kinded in `C`. That is the premise of the `init`
    -- rule that `initChain_types` discharges.
    (hwk : ∀ p ∈ (substSig σ M ++ T).toList, C.WellKindedTy p.2) :
    StatementsWellTyped P C ts L
      (initChain (missingIn ts (substSig σ M ++ T)) ++
        [Statement.call pname (mkArgs M T exprs mask) default]) C
      (insertAll ts (missingIn ts (substSig σ M ++ T))) := by
  have hExNoFvar : ∀ i (hi : i < exprs.length) m x, (exprs[i]'hi) ≠ LExpr.fvar m x none := by
    intro i hi m x heq
    have hlen : i < I.values.length := by rw [lm_values_length, ← hExLen]; exact hi
    have hty := (hExTy i hi hlen).1
    rw [heq] at hty
    cases hty
  have hLhsNodup : (M.keys ++ T.keys).Nodup := by
    rw [← substSig_keys σ M, ← lm_keys_append]; exact hNodup
  have hNodup' : ((substSig σ M ++ T).map Prod.fst).Nodup := by
    rw [← ListMap.keys_eq_map_fst]; exact hNodup
  -- The missing-only chain is Nodup (a sublist of a Nodup list).
  have hmissNodup : ((missingIn ts (substSig σ M ++ T)).map Prod.fst).Nodup :=
    List.Nodup.sublist (List.Sublist.map _ (missingIn_sublist ts (substSig σ M ++ T))) hNodup'
  -- The chain is well-typed: each missing name is fresh at its declaration point.
  have hchain : StatementsWellTyped P C ts L
      (initChain (missingIn ts (substSig σ M ++ T))) C
      (insertAll ts (missingIn ts (substSig σ M ++ T))) := by
    apply initChain_types (missingIn ts (substSig σ M ++ T))
      (fun p hp => hwk p (missingIn_sublist ts (substSig σ M ++ T) |>.mem hp)) ts
    intro i hi
    rw [insertAll_find_not_mem ((missingIn ts (substSig σ M ++ T)).take i) ts _ ?_]
    · exact missingIn_find_none ts (substSig σ M ++ T) (List.getElem_mem hi)
    · rw [List.map_take]
      have hidx : i < ((missingIn ts (substSig σ M ++ T)).map Prod.fst).length := by
        rw [List.length_map]; exact hi
      have hnot := nodup_getElem_not_mem_take hmissNodup i hidx
      simpa [List.getElem_map] using hnot
  -- The scopes after the chain extend the scopes before it.
  have hext : ∀ x v, ts.find? x = some v →
      (insertAll ts (missingIn ts (substSig σ M ++ T))).find? x = some v :=
    fun x v hx => insertAll_missing_preserves ts (substSig σ M ++ T) x v hx
  -- Every written-to name is in scope at its recorded type in the chained scopes:
  -- reused names survive `insertAll` (they were not inserted), init'ed names are
  -- inserted at exactly that type.
  have hInScope : ∀ p ∈ (substSig σ M ++ T).toList,
      (insertAll ts (missingIn ts (substSig σ M ++ T))).find? p.1 = some (.forAll [] p.2) := by
    intro p hp
    rcases hReuse p hp with hbound | habsent
    · exact hext p.1 _ hbound
    · refine insertAll_find_mem (missingIn ts (substSig σ M ++ T)) ts p.1 p.2 hmissNodup ?_
      exact List.mem_filter.mpr ⟨hp, by simp [habsent]⟩
  -- The in-out names are bound at their *instantiated* types. The instantiated block
  -- `substSig σ M` has keys `= M.keys` and values `= subst [σ] …`.
  have hMinΓ : ∀ i (hi : i < M.keys.length) (hj : i < M.values.length),
      (insertAll ts (missingIn ts (substSig σ M ++ T))).find? (M.keys[i]'hi)
        = some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (M.values[i]'hj))) := by
    intro i hi hj
    have hiK : i < (substSig σ M).keys.length := by rw [substSig_keys]; exact hi
    have hiV : i < (substSig σ M).values.length := by
      rw [lm_values_length, substSig_length, ← lm_values_length]; exact hj
    have hmem := List.mem_append_left T.toList (keyval_mem (substSig σ M) i hiK hiV)
    rw [substSig_keys_getElem σ M i hiK hi, substSig_values_getElem σ M i hiV hj] at hmem
    exact hInScope _ hmem
  -- The targets are bound at their own recorded type, which equals the instantiated out type
  -- positionally (`hTVals`).
  have hTinΓ : ∀ i (hi : i < T.keys.length) (hj : i < O.values.length),
      (insertAll ts (missingIn ts (substSig σ M ++ T))).find? (T.keys[i]'hi)
        = some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (O.values[i]'hj))) := by
    intro i hi hj
    have hjOσ : i < (substSig σ O).values.length := by
      rw [lm_values_length, substSig_length, ← lm_values_length]; exact hj
    have h := outTargets_inΓ (substSig σ O) T hTVals
      (ts := insertAll ts (missingIn ts (substSig σ M ++ T)))
      (fun p hp => hInScope _ (List.mem_append_right (substSig σ M).toList hp)) i hi hjOσ
    rwa [substSig_values_getElem σ O i hjOσ hj] at h
  have hcall : StatementWellTyped P C (insertAll ts (missingIn ts (substSig σ M ++ T))) L
      (Statement.call pname (mkArgs M T exprs mask) default) C
      (insertAll ts (missingIn ts (substSig σ M ++ T))) :=
    .cmd C _ _ L _ _
      (call_recipe_inout_sound σ M I O T exprs mask hfind hInputs hOutputs hExLen
        (by rw [← lm_values_length T, ← lm_values_length O, hTVals, substSig_values,
              List.length_map])
        hMinΓ hTinΓ (fun i hi hj => exprWellTyped_mono (hExTy i hi hj) hext) hExNoFvar
        hIdisjOut hMnotO hLhsNodup)
      (Strata.Util.HMaps.Equiv.refl _)
  exact StatementsWellTyped_append hchain (StatementsWellTyped_singleton hcall)

end StrataGenerators.Stmt
