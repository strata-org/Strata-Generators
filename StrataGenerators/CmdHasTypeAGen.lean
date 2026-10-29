import StrataGenerators.SetGen
import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen
import Strata.DL.Lambda.LExprTypeSpecProps
import Strata.Languages.Core.TypingSpec

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.AnnotFacts (ExprCtxOk ScopesCtxOk genLExpr_exprWellTyped
  genLExpr_scopesAnnotAgree annotsOk_of_empty)

/-!
# A generator for a well-typed command

A random generator on the `SetGen` interpretation of Basalt, for a well-typed imperative
command of Strata. Such a command is a `Cmd Expression`. Every command it draws satisfies the
typing spec `CmdWellTyped`.

## Contents

- The support of the generator: `genCmd_support_iff`
- Soundness: `genCmd_sound`, against `CmdWellTyped`

## The approach

The generator works with a flat `VarCtx`, which is a list of pairs of a name and a type.
The theorem for soundness is compositional. It takes the well-typedness of a drawn expression,
which `genLExpr_exprWellTyped` gives when the operators agree with the context, and it takes the
freshness properties of `genFreshName`. It then concludes that each generated command
satisfies `CmdWellTyped`.
-/

-- ── The correspondence between a `VarCtx` and a `TContext` ───────────

/-- A `VarCtx` corresponds to a `TContext` when the two agree on each lookup. If `ctx.find?`
    resolves a name to a monotype `mty`, then `Γ` resolves the same name to the monomorphic
    polytype `forAll [] mty`. A name that is fresh for `ctx` is also absent from `Γ`.

    The first condition speaks about `ctx.find?`, which is the *resolved* binding and
    therefore the first pair that matches. It does **not** speak about a raw `List.Mem`. This
    matters, because a flat `VarCtx` can hold two entries with one key, and the `find?` of a
    `TContext` can agree with only one binding for a name. Both sides use `find?`, so the
    correspondence holds for *each* `ctx`, and it holds even for a `ctx` that has two entries
    with one key. An environment for soundness can therefore give `corr : ∀ ctx` with no
    condition.

    Each context that the generator reaches has keys with no duplicate, because the first
    context has that property and `Map.insert` removes a duplicate. That fact is what lets the
    `set` case recover a `find?`, because `elements` draws the target of a `set` from *any*
    member of the context. -/
def VarCtxCorresponds (ctx : VarCtx) (Γ : TContext Unit) : Prop :=
  (∀ (x : Identifier Unit) mty, ctx.find? x = some mty →
    Γ.types.find? x = some (.forAll [] mty)) ∧
  (∀ (x : Identifier Unit), VarCtx.isFresh ctx x = true →
    Γ.types.find? x = none)

/-- In a map whose keys hold no duplicate, membership gives the result of `find?`. If `(x, v)` is
    a member of the map and the keys hold no duplicate, then `find? x = some v`, because no
    earlier binding hides `x`.

    This lemma is what lets the `set` cases recover the resolved fact
    `ctx.find? x = some mty`, which the `find?` in `VarCtxCorresponds` needs. `elements` draws
    the target `(x, mty)` of a `set` from *any* member of `ctx`. -/
theorem Map.find?_of_mem_of_nodup {α β : Type} [DecidableEq α]
    (m : Map α β) (x : α) (v : β)
    (hnodup : m.keys.Nodup) (hmem : List.Mem (x, v) m) :
    Map.find? m x = some v := by
  induction m with
  | nil => cases hmem
  | cons hd rest ih =>
    obtain ⟨a, b⟩ := hd
    rw [Map.keys_eq_map_fst (m := (a, b) :: rest)] at hnodup
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hrest⟩ := hnodup
    show (if a = x then some b else Map.find? rest x) = some v
    cases hmem with
    | head => simp
    | tail _ hmem' =>
      -- `x` is a key of `rest`, and `a` is not a key of `rest`, therefore `a ≠ x`.
      have hxkey : x ∈ rest.map Prod.fst :=
        List.mem_map.mpr ⟨(x, v), hmem', rfl⟩
      have hne : a ≠ x := fun h => hnotin (h ▸ hxkey)
      simp only [hne, if_false]
      exact ih (by rw [Map.keys_eq_map_fst (m := rest)]; exact hrest) hmem'

/-- `Map.insert` keeps the list of keys free of a duplicate. An insertion replaces a binding that
    exists, and the keys then do not change, or it adds a key that is fresh, and the keys then
    still hold no duplicate. This lemma carries that invariant across the `init` command, whose
    output context is `ctx.insert x mty`. -/
theorem Map.insert_keys_nodup {α β : Type} [DecidableEq α]
    (m : Map α β) (x : α) (v : β) (hnodup : (Map.keys m).Nodup) :
    (Map.keys (Map.insert m x v)).Nodup := by
  induction m with
  | nil => simp [Map.insert, Map.keys]
  | cons hd rest ih =>
    obtain ⟨a, b⟩ := hd
    rw [Map.keys_eq_map_fst (m := (a, b) :: rest)] at hnodup
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hrest⟩ := hnodup
    have hrest' : (Map.keys rest).Nodup := by rw [Map.keys_eq_map_fst (m := rest)]; exact hrest
    by_cases hax : a = x
    · -- The key is at the head, therefore the keys do not change.
      rw [Map.insert_cons_of_eq hax]
      subst hax
      rw [Map.keys_eq_map_fst (m := (a, v) :: rest)]
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨hnotin, hrest⟩
    · -- Recurse. The head key `a` stays, and it is fresh for the result of the recursion.
      rw [Map.insert_cons_of_ne hax]
      refine List.nodup_cons.mpr ⟨?_, ih hrest'⟩
      -- The keys of `insert rest x v` are a subset of `x :: keys rest`. However, `a ≠ x` holds
      -- and `a` is not a key of `rest`.
      intro hmem
      have hin := Map.insert_keys rest (key := x) (val := v) hmem
      simp only [List.mem_cons] at hin
      rcases hin with h | h
      · exact hax h
      · exact hnotin (by rw [← Map.keys_eq_map_fst (m := rest)]; exact h)

-- ── A functional context, which is a weaker condition than no duplicate ──

/-- A `Map` is *functional* when two entries that share a key also share a value. This condition
    is weaker than the condition that the keys hold no duplicate. It allows two entries with one
    key, if both entries hold the same value. An `inout` parameter gives exactly that shape,
    because it occurs in the input scope and in the output scope at the *same* type.

    The condition is still enough to resolve the target of a `set` to a definite `find?`, which
    `Map.find?_of_mem_of_functional` states. A fresh insertion also keeps it, which
    `Map.insert_functional_of_fresh` states. It can therefore replace the invariant about
    duplicate keys in each proof of soundness for a command and for a statement. -/
def Map.Functional {α β : Type} [DecidableEq α] (m : Map α β) : Prop :=
  ∀ (x : α) (v₁ v₂ : β), List.Mem (x, v₁) m → List.Mem (x, v₂) m → v₁ = v₂

/-- A map whose keys hold no duplicate is functional. Each key occurs one time, so two entries
    with one key are the same entry. This lemma lets a first context whose disjointness already
    gives keys with no duplicate satisfy the weaker invariant `Functional`, which the proofs of
    soundness thread. -/
theorem Map.functional_of_nodup {α β : Type} [DecidableEq α]
    (m : Map α β) (hnodup : m.keys.Nodup) : Map.Functional m := by
  intro x v₁ v₂ h₁ h₂
  have e₁ := Map.find?_of_mem_of_nodup m x v₁ hnodup h₁
  have e₂ := Map.find?_of_mem_of_nodup m x v₂ hnodup h₂
  rw [e₁] at e₂
  exact (Option.some.injEq _ _).mp e₂

/-- If `find? m x = none` holds, then `x` is not a key of `m`, and `m` therefore holds no entry
    `(x, w)`. -/
theorem Map.not_mem_of_find?_none {α β : Type} [DecidableEq α]
    (m : Map α β) (x : α) (h : Map.find? m x = none) :
    ∀ w, ¬ List.Mem (x, w) m := by
  intro w hmem
  induction m with
  | nil => cases hmem
  | cons hd rest ih =>
    obtain ⟨a, b⟩ := hd
    simp only [Map.find?] at h
    split at h
    · simp at h
    · rename_i hne
      cases hmem with
      | head => exact hne rfl
      | tail _ hmem' => exact ih h hmem'

/-- In a *functional* map, membership gives `find?`: if `(x, v)` is a member, then
    `find? x = some v`. The first entry with the key `x` binds some value `v'`, and
    functionality forces `v' = v`.

    This lemma is the form of `Map.find?_of_mem_of_nodup` for a functional map. It lets the
    `set` cases recover the resolved `find?`, because `elements` draws the target of a `set`
    from *any* member. -/
theorem Map.find?_of_mem_of_functional {α β : Type} [DecidableEq α]
    (m : Map α β) (x : α) (v : β)
    (hfun : Map.Functional m) (hmem : List.Mem (x, v) m) :
    Map.find? m x = some v := by
  induction m with
  | nil => cases hmem
  | cons hd rest ih =>
    obtain ⟨a, b⟩ := hd
    simp only [Map.find?]
    cases hmem with
    | head =>
      simp
    | tail _ hmem' =>
      split
      · -- The head key `a` equals `x`, so the head value `b` and the tail value `v` share the
        -- key `x`.
        rename_i hax; subst hax
        have hb : b = v := hfun a b v (List.Mem.head _) (List.Mem.tail _ hmem')
        rw [hb]
      · -- The head key differs, so recurse. Functionality also holds for the tail.
        exact ih (fun y w₁ w₂ h₁ h₂ =>
          hfun y w₁ w₂ (List.Mem.tail _ h₁) (List.Mem.tail _ h₂)) hmem'

/-- Each member of `m.insert x v` is a member of `m`, or it is the new entry `(x, v)`. An
    insertion replaces the first entry with the key `x`, which leaves a new head `(x, v)` and a
    tail that `m` also holds, or it adds `(x, v)` to the end. -/
theorem Map.mem_insert {α β : Type} [DecidableEq α]
    (m : Map α β) (x : α) (v : β) (y : α) (w : β)
    (hmem : List.Mem (y, w) (m.insert x v)) :
    List.Mem (y, w) m ∨ (y, w) = (x, v) := by
  induction m with
  | nil =>
    simp only [Map.insert] at hmem
    cases hmem with
    | head => exact Or.inr rfl
    | tail _ h => cases h
  | cons hd rest ih =>
    obtain ⟨a, b⟩ := hd
    by_cases hax : a = x
    · -- The insertion replaces the head, which gives `(x, v) :: rest`.
      rw [Map.insert_cons_of_eq hax] at hmem
      cases hmem with
      | head => exact Or.inr rfl
      | tail _ h => exact Or.inl (List.Mem.tail _ h)
    · -- The insertion keeps the head, so recurse.
      rw [Map.insert_cons_of_ne hax] at hmem
      cases hmem with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ h =>
        rcases ih h with h' | h'
        · exact Or.inl (List.Mem.tail _ h')
        · exact Or.inr h'

/-- An insertion at a *fresh* key keeps functionality. `x` is absent from `m`, so the insertion
    adds `(x, v)` to the end, it changes no binding that exists, and no entry that exists shares
    its key. This lemma carries the invariant `Functional` across the `init` command. The output
    context of that command is `ctx.insert x mty`, and `genFreshName_produces_fresh` says that
    `x` is fresh. -/
theorem Map.insert_functional_of_fresh {α β : Type} [DecidableEq α]
    (m : Map α β) (x : α) (v : β)
    (hfun : Map.Functional m) (hfresh : Map.find? m x = none) :
    Map.Functional (m.insert x v) := by
  intro y w₁ w₂ h₁ h₂
  have hnotin := Map.not_mem_of_find?_none m x hfresh
  rcases Map.mem_insert m x v y w₁ h₁ with hm₁ | he₁ <;>
    rcases Map.mem_insert m x v y w₂ h₂ with hm₂ | he₂
  · exact hfun y w₁ w₂ hm₁ hm₂
  · -- `m` holds `(y, w₁)`, and `(y, w₂) = (x, v)`. Therefore `y = x`, and that contradicts
    -- the freshness of `x`.
    obtain ⟨hy, _⟩ := Prod.mk.injEq .. |>.mp he₂
    exact absurd (hy ▸ hm₁) (hnotin w₁)
  · obtain ⟨hy, _⟩ := Prod.mk.injEq .. |>.mp he₁
    exact absurd (hy ▸ hm₂) (hnotin w₂)
  · rw [(Prod.mk.injEq ..).mp he₁ |>.2, (Prod.mk.injEq ..).mp he₂ |>.2]

/-- If `(x, v)` is a member of `m₁ ++ m₂` and `x` is not a key of `m₁`, then `m₂` holds the
    entry. The entry with the key `x` cannot be in the `m₁` half. -/
theorem Map.mem_of_append_not_mem_keys {α β : Type} [DecidableEq α]
    (m₁ m₂ : Map α β) (x : α) (v : β)
    (hmem : List.Mem (x, v) (m₁ ++ m₂)) (hnk : x ∉ Map.keys m₁) :
    List.Mem (x, v) m₂ := by
  rcases List.mem_append.mp hmem with h | h
  · exact absurd (by rw [Map.keys_eq_map_fst]; exact List.mem_map.mpr ⟨(x, v), h, rfl⟩) hnk
  · exact h

/-- The mirror of `Map.mem_of_append_not_mem_keys`. If `(x, v)` is a member of `m₁ ++ m₂` and `x`
    is not a key of `m₂`, then `m₁` holds the entry. -/
theorem Map.mem_left_of_append_not_mem_keys {α β : Type} [DecidableEq α]
    (m₁ m₂ : Map α β) (x : α) (v : β)
    (hmem : List.Mem (x, v) (m₁ ++ m₂)) (hnk : x ∉ Map.keys m₂) :
    List.Mem (x, v) m₁ := by
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · exact absurd (by rw [Map.keys_eq_map_fst]; exact List.mem_map.mpr ⟨(x, v), h, rfl⟩) hnk

/-- If `(x, v)` is a member of `m`, then `x` is a key of `m`. -/
theorem Map.mem_keys_of_mem {α β : Type} [DecidableEq α]
    (m : Map α β) (x : α) (v : β) (hmem : List.Mem (x, v) m) : x ∈ Map.keys m := by
  rw [Map.keys_eq_map_fst]; exact List.mem_map.mpr ⟨(x, v), hmem, rfl⟩

/-- Functionality composes over an append when the two halves *agree* on a shared key. If `m₁` and
    `m₂` are each functional, and each key of both maps binds equal values in the two maps, then
    the join `m₁ ++ m₂` is functional.

    This lemma serves the first context of a procedure body, whose scope is
    `inputs ++ outputs ++ old`. An `inout` parameter occurs in `inputs` and in `outputs` at the
    *same* type, so the two agree. Each other overlap is empty, so the agreement is vacuous. -/
theorem Map.functional_append {α β : Type} [DecidableEq α]
    (m₁ m₂ : Map α β)
    (h₁ : Map.Functional m₁) (h₂ : Map.Functional m₂)
    (hagree : ∀ (x : α) (v₁ v₂ : β),
      List.Mem (x, v₁) m₁ → List.Mem (x, v₂) m₂ → v₁ = v₂) :
    Map.Functional (m₁ ++ m₂) := by
  intro x v₁ v₂ hm₁ hm₂
  rcases List.mem_append.mp hm₁ with p₁ | p₁ <;>
    rcases List.mem_append.mp hm₂ with p₂ | p₂
  · exact h₁ x v₁ v₂ p₁ p₂
  · exact hagree x v₁ v₂ p₁ p₂
  · exact (hagree x v₂ v₁ p₂ p₁).symm
  · exact h₂ x v₁ v₂ p₁ p₂

-- ── Well-typedness of the parts of a command ──────────────────────────

/-- The free variables that `genLExpr` reads from a scope `ctx` meet the context conditions at the
    variable scopes of a context `Γ` that agrees with `ctx`, when the operators and schemes meet
    them, the scope is functional and every type of the scope is well kinded in `C`. -/
theorem exprCtxOk_of_corresponds {C : LContext CoreLParams} {ts : TypeScopes} {octx : OpCtx}
    {pctx : PolyOpCtx} (hops : ExprCtxOk C ts [] octx pctx) {ctx : VarCtx} {Γ : TContext Unit}
    (hCorr : VarCtxCorresponds ctx Γ) (hFun : Map.Functional ctx)
    (hwk : ∀ ty ∈ ctx.values, C.WellKindedTy ty) :
    ExprCtxOk C Γ.types ctx.toFVarCtx octx pctx := by
  refine hops.restrict ?_ (fun _ hp => hp) (fun _ hp => hp)
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hval : q.2 ∈ ctx.values := by
    rw [Map.values_eq_map_snd]
    exact List.mem_map_of_mem hq
  exact ⟨Lambda.knownInstance_of_wellKinded q.2 C.knownTypes (hwk q.2 hval),
    hCorr.1 q.1 q.2 (Map.find?_of_mem_of_functional ctx q.1 q.2 hFun hq)⟩

/-- The free variables that `genLExpr` reads from a scope `ctx` are declared, at their types, in
    the variable scopes of a context `Γ` that agrees with `ctx`, when the scope is functional; with
    operators and schemes that agree with `C`, this gives the context conditions under which every
    generated expression satisfies `ScopesAnnotAgree`: its free-variable and operator annotations
    agree with the scopes of `Γ` and the function table of `C`. -/
theorem scopesCtxOk_of_corresponds {C : LContext CoreLParams} {ts : TypeScopes} {octx : OpCtx}
    {pctx : PolyOpCtx} (hops : ExprCtxOk C ts [] octx pctx) {ctx : VarCtx} {Γ : TContext Unit}
    (hCorr : VarCtxCorresponds ctx Γ) (hFun : Map.Functional ctx) :
    ScopesCtxOk C Γ.types ctx.toFVarCtx octx pctx := by
  refine ⟨hops.sigs, ?_, fun p hp => (hops.ops p hp).2, hops.polys⟩
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hCorr.1 q.1 q.2 (Map.find?_of_mem_of_functional ctx q.1 q.2 hFun hq)

/-- `binderAnnotsKnownIn C.knownTypes` decides `BinderAnnotsKnown C`. -/
theorem binderAnnotsKnownIn_iff {C : LContext CoreLParams} {e : LExpr'} :
    binderAnnotsKnownIn C.knownTypes e = true ↔ BinderAnnotsKnown C e := by
  simp only [binderAnnotsKnownIn, List.all_eq_true, BinderAnnotsKnown]

/-- An expression that `genLExpr` draws from the scope `ctx` and whose binder annotations are
    known instances in `C` is well-typed at its type in the variable scopes of a context `Γ` that
    agrees with `ctx`, when the operators and schemes agree with `C` and the scope is functional. -/
theorem genLExpr_exprWellTyped_of_known {C : LContext CoreLParams} {ts : TypeScopes}
    {octx : OpCtx} {pctx : PolyOpCtx} (hops : ExprCtxOk C ts [] octx pctx) {ctx : VarCtx}
    {Γ : TContext Unit} (hCorr : VarCtxCorresponds ctx Γ) (hFun : Map.Functional ctx)
    {tvars : List TyIdentifier} {depth : Nat} {τ : LMonoTy} {e : LExpr'}
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx pctx tvars [] depth τ))
    (hknown : binderAnnotsKnownIn C.knownTypes e = true) : ExprWellTyped C Γ.types e τ :=
  ⟨genLExpr_sound ctx.toFVarCtx octx pctx tvars [] depth τ _ e he,
    binderAnnotsKnownIn_iff.mp hknown,
    genLExpr_scopesAnnotAgree (scopesCtxOk_of_corresponds hops hCorr hFun) he⟩

/-- The expression that `knownOrTrue kt` keeps from a `bool` expression that is well-typed when
    its binder annotations are known instances of `kt` is well-typed at `bool`: it is that
    expression or the constant `true`. -/
theorem knownOrTrue_exprWellTyped {C : LContext CoreLParams} {ts : TypeScopes}
    {kt : Lambda.KnownTypes} {e : LExpr'}
    (he : binderAnnotsKnownIn kt e = true → ExprWellTyped C ts e .bool) :
    ExprWellTyped C ts (knownOrTrue kt e) .bool := by
  unfold knownOrTrue
  split
  · rename_i hknown
    exact he hknown
  · exact ⟨LExpr.HasTypeA.const, annotsOk_of_empty rfl rfl rfl rfl⟩

/-- A well-typed command stays well-typed when its output scopes are replaced by equivalent
    ones: scopes with the same lookup for every name. -/
theorem StrataGenerators.cmdWellTyped_out_equiv {C : LContext CoreLParams} {ts ts₁ ts₂ : TypeScopes}
    {c : Cmd Expression} (h : CmdWellTyped C ts c ts₁) (he : Strata.Util.HMaps.Equiv ts₂ ts₁) :
    CmdWellTyped C ts c ts₂ := by
  cases h with
  | init_det _ _ _ _ _ _ hfind hfv hxty hwk hexpr heq =>
    exact .init_det _ _ _ _ _ _ _ hfind hfv hxty hwk hexpr (he.trans heq)
  | init_nondet _ _ _ _ _ hfind hxty hwk heq =>
    exact .init_nondet _ _ _ _ _ _ hfind hxty hwk (he.trans heq)
  | set_det _ _ _ _ _ hfind hexpr heq => exact .set_det _ _ _ _ _ _ hfind hexpr (he.trans heq)
  | set_nondet _ _ _ _ hfind heq => exact .set_nondet _ _ _ _ _ hfind (he.trans heq)
  | assert _ _ _ _ hexpr heq => exact .assert _ _ _ _ _ hexpr (he.trans heq)
  | assume _ _ _ _ hexpr heq => exact .assume _ _ _ _ _ hexpr (he.trans heq)
  | cover _ _ _ _ hexpr heq => exact .cover _ _ _ _ _ hexpr (he.trans heq)

/-- The variable scopes after a command: an `init` declares its variable at its declared type, and
    every other command keeps the scopes. -/
def cmdOutScopes (ts : TypeScopes) : Cmd Expression → TypeScopes
  | .init x xty _ _ => ts.insert x xty
  | _ => ts

-- ── The support of `genCmd` ─────────────────────────────────────────

/-- The support of `genCmd`. A result is in the support exactly when one of the smaller
    generators gives it. This theorem states the soundness and the completeness of the generator
    at the syntactic level, before a proof reads the result against a typing relation. -/
theorem genCmd_support_iff
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (r : GenCmdResult) (pctx : PolyOpCtx := []) (avoid : List String := [])
    (kt : Lambda.KnownTypes := Core.KnownTypes) :
    r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx avoid kt) ↔
    (r ∈ SetGen.support (genInitDet (G := SetGen.Set) octx tvars ctx depth depth pctx avoid kt) ∨
     r ∈ SetGen.support (genInitNondet (G := SetGen.Set) tvars ctx depth avoid) ∨
     (∃ h : (ctx.writable immutableVars).length > 0, r ∈ SetGen.support
       (genSetDet (G := SetGen.Set) octx tvars immutableVars ctx depth h pctx kt)) ∨
     (∃ h : (ctx.writable immutableVars).length > 0, r ∈ SetGen.support (genSetNondet (G := SetGen.Set) immutableVars ctx h)) ∨
     r ∈ SetGen.support (genAssertCmd (G := SetGen.Set) octx tvars ctx depth pctx kt) ∨
     r ∈ SetGen.support (genAssumeCmd (G := SetGen.Set) octx tvars ctx depth pctx kt) ∨
     r ∈ SetGen.support (genCoverCmd (G := SetGen.Set) octx tvars ctx depth pctx kt)) := by
  simp only [genCmd, mem_support_dite_iff]
  constructor
  · intro hr
    rcases hr with ⟨h, hr⟩ | ⟨hne, hr⟩
    · rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)] at hr
      obtain ⟨w, g, hg, _, hr⟩ := hr
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ <;>
        subst heq <;>
        first
        | exact Or.inl hr
        | exact Or.inr (Or.inl hr)
        | exact Or.inr (Or.inr (Or.inl ⟨h, hr⟩))
        | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hr⟩)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
    · rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)] at hr
      obtain ⟨w, g, hg, _, hr⟩ := hr
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
      rcases hg with ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ <;>
        subst heq <;>
        first
        | exact Or.inl hr
        | exact Or.inr (Or.inl hr)
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
  · intro hr
    rcases hr with hr | (hr | (⟨h, hr⟩ | (⟨h, hr⟩ | (hr | (hr | hr)))))
    · by_cases h : (ctx.writable immutableVars).length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .head _, by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨3, _, .head _, by omega, hr⟩⟩
    · by_cases h : (ctx.writable immutableVars).length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨1, _, .tail _ (.head _), by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨1, _, .tail _ (.head _), by omega, hr⟩⟩
    · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨3, _, .tail _ (.tail _ (.head _)), by omega, hr⟩⟩
    · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩⟩
    · by_cases h : (ctx.writable immutableVars).length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.head _)), by omega, hr⟩⟩
    · by_cases h : (ctx.writable immutableVars).length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.head _))), by omega, hr⟩⟩
    · by_cases h : (ctx.writable immutableVars).length > 0
      · exact Or.inl ⟨h, by rw [mem_support_frequency_iff (by show 0 < 2+1+3+2+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), by omega, hr⟩⟩
      · exact Or.inr ⟨h, by rw [mem_support_frequency_iff (by show 0 < 3+1+2+2+2; omega)]; exact ⟨2, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, hr⟩⟩

-- ── The proof that `genFreshName` gives a fresh name ────────────────

/-- If no entry of `ctx` has the key `x`, then `find?` returns `none`. -/
private theorem VarCtx.find?_none_of_ne_all (ctx : VarCtx) (x : Identifier Unit)
    (h : ∀ entry : Identifier Unit × LMonoTy, List.Mem entry ctx → entry.1 ≠ x) :
    VarCtx.find? ctx x = none := by
  unfold VarCtx.find?
  apply Map.find?_none_of_not_mem_keys'
  intro hmem
  rw [Map.keys_eq_map_fst] at hmem
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
  exact h entry hentry heq

/-- Two strings of different lengths are not equal. -/
private theorem String.ne_of_length_ne {s₁ s₂ : String} (h : s₁.length ≠ s₂.length) :
    s₁ ≠ s₂ := fun heq => absurd (congrArg String.length heq) h

/-- A name that is longer than each name in `ctx` is fresh in `ctx`. -/
private theorem isFresh_of_maxlen_lt (ctx : VarCtx) (s : String)
    (h : (VarCtx.names ctx).foldl (fun acc nm => max acc nm.length) 0 < s.length) :
    VarCtx.isFresh ctx ⟨s, ()⟩ = true := by
  unfold VarCtx.isFresh
  have hfind : VarCtx.find? ctx ⟨s, ()⟩ = none := by
    apply VarCtx.find?_none_of_ne_all
    intro entry hmem
    -- Two identifiers are equal exactly when their names are equal, so the argument from the
    -- length gives that the two names differ.
    have hname_ne : entry.1.name ≠ s := by
      apply String.ne_of_length_ne
      have hname_mem : entry.1.name ∈ VarCtx.names ctx :=
        List.mem_map.mpr ⟨entry, hmem, rfl⟩
      have hle := foldl_max_ge_of_mem String.length (VarCtx.names ctx) entry.1.name hname_mem 0
      omega
    intro heq
    exact hname_ne (congrArg Identifier.name heq)
  simp [hfind]

/-- The length of `fallbackFreshName ctx avoid` is one more than the length of the longest name in
    the context or in `avoid`. -/
private theorem fallbackFreshName_length (ctx : VarCtx) (avoid : List String) :
    (fallbackFreshName ctx avoid).length =
      (VarCtx.names ctx ++ avoid).foldl (fun acc nm => max acc nm.length) 0 + 1 := by
  simp [fallbackFreshName, String.length_ofList, List.length_replicate]

/-- The longest name in the context is no longer than the longest name in the context or in
    `avoid`. -/
private theorem maxlen_names_le_append (ctx : VarCtx) (avoid : List String) :
    (VarCtx.names ctx).foldl (fun acc nm => max acc nm.length) 0 ≤
      (VarCtx.names ctx ++ avoid).foldl (fun acc nm => max acc nm.length) 0 := by
  rw [List.foldl_append]
  exact foldl_max_ge_init String.length avoid _

/-- `dodgeKeyword` never makes its argument shorter. It returns the argument without a change, or
    it adds a `_` to the end. -/
private theorem length_le_dodgeKeyword (s : String) :
    s.length ≤ (dodgeKeyword s).length := by
  unfold dodgeKeyword
  split
  · simp [String.length_append]
  · exact Nat.le_refl _

/-- `dodgeKeyword (fallbackFreshName ctx avoid)` is fresh in `ctx`. The fallback name is longer
    than each name in the context, and `dodgeKeyword` only makes a name longer. -/
private theorem dodgeKeyword_fallbackFreshName_isFresh (ctx : VarCtx) (avoid : List String) :
    VarCtx.isFresh ctx ⟨dodgeKeyword (fallbackFreshName ctx avoid), ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  have hdodge := length_le_dodgeKeyword (fallbackFreshName ctx avoid)
  rw [fallbackFreshName_length] at hdodge
  have hle := maxlen_names_le_append ctx avoid
  omega

/-- Each name in the support of `genFreshName ctx avoid` is fresh in `ctx`. The identifier
    `⟨name, ()⟩` of such a name is therefore absent from the context. -/
theorem genFreshName_produces_fresh (ctx : VarCtx) {avoid : List String} :
    ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx avoid) →
      VarCtx.isFresh ctx ⟨name, ()⟩ = true := by
  intro name hmem
  simp only [genFreshName, mem_support_bind_iff] at hmem
  obtain ⟨s, _, hname⟩ := hmem
  simp only [mem_support_ite_iff, mem_support_pure_iff] at hname
  rcases hname with ⟨hfresh, rfl⟩ | ⟨_, rfl⟩
  · exact (Bool.and_eq_true _ _ ▸ hfresh).1
  · exact dodgeKeyword_fallbackFreshName_isFresh ctx avoid

-- ── The family of fresh names with an index ─────────────────────────────

/-- The length of each name in a list of pairs of an identifier and a type is not more than
    `maxNameLen`. This is `foldl_max_ge_of_mem` at `f := String.length`, over the list of the
    names. -/
theorem length_le_maxNameLen {l : List (Identifier Unit × LMonoTy)}
    {q : Identifier Unit × LMonoTy} (hq : q ∈ l) : q.1.name.length ≤ maxNameLen l :=
  foldl_max_ge_of_mem String.length _ q.1.name (List.mem_map.mpr ⟨q, hq, rfl⟩) 0

/-- **The family is injective in the index.** Two different indices give names of two different
    lengths, and therefore two different names. `outTargets` therefore never picks one target for
    two output arguments. -/
theorem indexedFreshName_inj {base i j : Nat}
    (h : indexedFreshName base i = indexedFreshName base j) : i = j := by
  have hlen := congrArg String.length h
  rw [indexedFreshName_length, indexedFreshName_length] at hlen
  omega

/-- **The family avoids a list of names.** `indexedFreshName (maxNameLen l) i` is longer than each
    name in `l`, therefore it equals no name in `l`. -/
theorem indexedFreshName_ne_of_mem {l : List (Identifier Unit × LMonoTy)}
    {q : Identifier Unit × LMonoTy} (hq : q ∈ l) (i : Nat) :
    q.1.name ≠ indexedFreshName (maxNameLen l) i := by
  intro heq
  have hle := length_le_maxNameLen hq
  rw [heq, indexedFreshName_length] at hle
  omega

/-- **The family is fresh for a `VarCtx`.** With `base := maxNameLen ctx`, each member of the
    family is absent from `ctx`. -/
theorem indexedFreshName_isFresh (ctx : VarCtx) (i : Nat) :
    VarCtx.isFresh ctx ⟨indexedFreshName (maxNameLen ctx) i, ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  rw [indexedFreshName_length]
  show maxNameLen ctx < maxNameLen ctx + 1 + i
  omega

/-- `indexedFreshName base i` is fresh for `ctx` at each base that is not less than the length of
    the longest name of `ctx`. -/
theorem indexedFreshName_isFresh_of_le (ctx : VarCtx) {base : Nat} (h : maxNameLen ctx ≤ base)
    (i : Nat) : VarCtx.isFresh ctx ⟨indexedFreshName base i, ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  rw [indexedFreshName_length]
  show maxNameLen ctx < base + 1 + i
  omega

/-- No reserved Core keyword is a string of `x` characters that is not empty. This is the part of
    `indexedFreshName_not_keyword` that `decide` can check. -/
private theorem reservedKeyword_not_all_x : ∀ k ∈ reservedKeywordsList,
    ¬ ((k.toList.all (· == 'x')) = true ∧ 0 < String.length k) := by decide +kernel

/-- **No member of the indexed family is a keyword.** Each member is a string of `x` characters
    that is not empty, and no reserved Core keyword has that shape. The names that `outTargets`
    picks for an output argument are therefore never a reserved word, and the Core parser accepts
    each of them in the position of an identifier. -/
theorem indexedFreshName_not_keyword (base i : Nat) :
    isReservedKeyword (indexedFreshName base i) = false := by
  rw [isReservedKeyword_eq_list_contains, Bool.eq_false_iff]
  intro hcontains
  refine reservedKeyword_not_all_x _ (List.mem_of_elem_eq_true hcontains) ⟨?_, ?_⟩
  · simp [indexedFreshName, String.toList_ofList]
  · rw [indexedFreshName_length]; omega

/-- **No name in the support of `genFreshName` is a keyword.** The random candidate comes from
    `genIdentName`, and the support of that generator holds no keyword. The fallback goes through
    `dodgeKeyword`, which never returns a keyword. The variable names that `genInitDet` and
    `genInitNondet` bind in an `init` command are therefore never a reserved word, and the Core
    parser accepts each of them in the position of an identifier. -/
theorem genFreshName_not_keyword (ctx : VarCtx) {avoid : List String} :
    ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx avoid) →
      isReservedKeyword name = false := by
  intro name hmem
  simp only [genFreshName, mem_support_bind_iff] at hmem
  obtain ⟨s, hs, hname⟩ := hmem
  simp only [mem_support_ite_iff, mem_support_pure_iff] at hname
  rcases hname with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact StrataGenerators.Function.genIdentName_not_keyword _ hs
  · exact StrataGenerators.Function.dodgeKeyword_not_keyword _

/-- The `WellKindedTy` premise of the two `init` rules, for each type that the generator can emit.
    `genLMonoTy` gives only a type that the generator can make, and `SimpleTyArities C` says that
    `C` registers each constructor of such a type at its own arity. -/
theorem wellKindedTy_of_genLMonoTy {C : LContext CoreLParams} (hC : SimpleTyArities C)
    (tvars : List TyIdentifier) (depth : Nat) (mty : LMonoTy)
    (hmty : mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth)) :
    C.WellKindedTy mty :=
  genLMonoTy_mem_wellKindedTy hC ⟨_, hmty⟩

-- ── The soundness of `genCmd` ────────────────────────────────────────

/-- The predicate that says that a name fresh for `ctx` occurs as a free variable in no
    expression from `genLExpr`. This claim follows from the structure of the generator, because
    `pickFVar` draws each free variable from `fctx`. `freshNamesDisjointFromExprs_toFVarCtx`
    proves it for `fctx := ctx.toFVarCtx`. -/
def FreshNamesDisjointFromExprs (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (ctx : VarCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : Prop :=
  ∀ name, VarCtx.isFresh ctx ⟨name, ()⟩ = true →
    ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ) →
      (⟨name, ()⟩ : Identifier Unit) ∉ HasFvars.getFvars (P := Expression) e

/-- **Soundness of `genCmd` at the scopes of a context.** Every command that `genCmd` draws from a
    scope `ctx` is well-typed from the variable scopes of a context `Γ` that agrees with `ctx` to
    those scopes with the declared variable added, if the command is an `init`. This holds when the
    operators and schemes agree with `C` (`ExprCtxOk`), the scope is functional, and no fresh name
    is a free variable of a drawn expression. -/
theorem genCmd_sound_scopes
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit) {pctx : PolyOpCtx} {avoid : List String}
    (hops : ExprCtxOk C [] [] octx pctx)
    (hCorr : VarCtxCorresponds ctx Γ)
    (hFun : Map.Functional ctx)
    (hDisjoint : FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx depth pctx)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx avoid C.knownTypes)) :
    CmdWellTyped C Γ.types r.cmd (cmdOutScopes Γ.types r.cmd) := by
  rw [genCmd_support_iff octx tvars immutableVars ctx depth r pctx avoid C.knownTypes] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det, or init_nondet when the initializer is filtered out.
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, e, he, rfl⟩ := hr
    have hfreshCtx := genFreshName_produces_fresh ctx name hname
    have hfreshΓ := hCorr.2 ⟨name, ()⟩ hfreshCtx
    have hwkm := wellKindedTy_of_genLMonoTy hops.arities tvars depth mty hmty
    dsimp only
    split
    · rename_i hknown
      exact .init_det _ _ _ e mty default _ hfreshΓ (hDisjoint name hfreshCtx mty e he) rfl hwkm
        (genLExpr_exprWellTyped_of_known hops hCorr hFun he hknown)
        (Strata.Util.HMaps.Equiv.refl _)
    · exact .init_nondet _ _ _ mty default _ hfreshΓ rfl hwkm (Strata.Util.HMaps.Equiv.refl _)
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, rfl⟩ := hr
    have hfreshΓ := hCorr.2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    exact .init_nondet _ _ _ mty default _ hfreshΓ rfl
      (wellKindedTy_of_genLMonoTy hops.arities tvars depth mty hmty)
      (Strata.Util.HMaps.Equiv.refl _)
  · -- set_det, or set_nondet when the expression is filtered out.
    simp only [genSetDet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, e, he, rfl⟩ := hr
    have hmemCtx : List.Mem (name, mty) ctx := (List.mem_filter.mp hmem).1
    have hfind := hCorr.1 name mty (Map.find?_of_mem_of_functional ctx name mty hFun hmemCtx)
    dsimp only
    split
    · rename_i hknown
      exact .set_det _ _ _ e default _ hfind
        (genLExpr_exprWellTyped_of_known hops hCorr hFun he hknown)
        (Strata.Util.HMaps.Equiv.refl _)
    · exact .set_nondet _ _ _ default _ hfind (Strata.Util.HMaps.Equiv.refl _)
  · -- set_nondet
    simp only [genSetNondet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, rfl⟩ := hr
    have hmemCtx : List.Mem (name, mty) ctx := (List.mem_filter.mp hmem).1
    exact .set_nondet _ _ _ default _
      (hCorr.1 name mty (Map.find?_of_mem_of_functional ctx name mty hFun hmemCtx))
      (Strata.Util.HMaps.Equiv.refl _)
  · -- assert. `genIdentName` draws the label, and the typing rule ignores it.
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _, e, he, rfl⟩ := hr
    exact .assert _ _ _ default _
      (knownOrTrue_exprWellTyped (genLExpr_exprWellTyped_of_known hops hCorr hFun he))
      (Strata.Util.HMaps.Equiv.refl _)
  · -- assume
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _, e, he, rfl⟩ := hr
    exact .assume _ _ _ default _
      (knownOrTrue_exprWellTyped (genLExpr_exprWellTyped_of_known hops hCorr hFun he))
      (Strata.Util.HMaps.Equiv.refl _)
  · -- cover
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _, e, he, rfl⟩ := hr
    exact .cover _ _ _ default _
      (knownOrTrue_exprWellTyped (genLExpr_exprWellTyped_of_known hops hCorr hFun he))
      (Strata.Util.HMaps.Equiv.refl _)

/-- **Soundness of `genCmd`**: every command that `genCmd` draws from a scope `ctx` is well-typed
    from the variable scopes of a context `Γ` that agrees with `ctx`, when the operators and
    schemes agree with `C`, the scope is functional, and no fresh name is a free variable of a
    drawn expression. -/
theorem genCmd_sound
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit) {pctx : PolyOpCtx} {avoid : List String}
    (hops : ExprCtxOk C [] [] octx pctx)
    (hCorr : VarCtxCorresponds ctx Γ)
    (hFun : Map.Functional ctx)
    (hDisjoint : FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx depth pctx)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx avoid C.knownTypes)) :
    ∃ ts', CmdWellTyped C Γ.types r.cmd ts' :=
  ⟨_, genCmd_sound_scopes octx tvars immutableVars ctx depth C Γ hops hCorr hFun hDisjoint r hr⟩

-- ── Facts for the completeness of commands ──

/-- The predicate that says that `genLExpr` is complete at every type: the support of the
    generator holds each expression that `HasTypeA` accepts in the empty context. -/
def GenLExprComplete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : Prop :=
  ∀ τ e, LExpr.HasTypeA (T := LExprParams') [] e τ →
    e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ)

/-- `knownOrTrue` keeps an expression whose binder annotations are known. -/
theorem knownOrTrue_of_known {kt : Lambda.KnownTypes} {e : LExpr'}
    (hknown : binderAnnotsKnownIn kt e = true) : knownOrTrue kt e = e := by
  simp only [knownOrTrue, hknown, if_true]

-- ── The typing of a sequence of commands, as a chain ────────────────

/-- Well-typedness of a sequence of commands: each command is typed from one variable scope to the
    next, so the commands form a chain `ts₀ → ts₁ → ... → tsₙ`. -/
inductive CmdsWellTyped (C : LContext CoreLParams) :
    TypeScopes → List (Cmd Expression) → TypeScopes → Prop where
  | nil : ∀ ts, CmdsWellTyped C ts [] ts
  | cons : ∀ ts ts' ts'' cmd cmds,
      CmdWellTyped C ts cmd ts' →
      CmdsWellTyped C ts' cmds ts'' →
      CmdsWellTyped C ts (cmd :: cmds) ts''

/-- The facts about the scopes that a proof of `genCmd_sound` needs at *each* context that a draw
    of a sequence can reach. The structure holds three parts:
    - a function that gives a `TContext` for each `VarCtx`, with the correspondence between the
      two;
    - the fact that a fresh name equals no free variable of a generated expression, at each
      context that a draw can reach;
    - the agreement of the context of a longer scope with an insertion. -/
structure GenCmdSoundEnv (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (C : LContext CoreLParams) (pctx : PolyOpCtx := []) where
  /-- Gives the semantic `TContext` for a flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The correspondence holds for each context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- A fresh name occurs as a free variable in no generated expression. The generator draws each
      free variable from `ctx.toFVarCtx`, whose names are the names of `ctx`, and a fresh name for
      an `init` avoids `ctx`. This field therefore holds at each `ctx` with no condition, as
      `freshNamesDisjointFromExprs_toFVarCtx` states. -/
  freshDisjoint :
    ∀ (ctx : VarCtx), FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx depth pctx
  /-- The `TContext` for `ctx.insert x mty` agrees with an insertion into the `TContext` for `ctx`.
      This field is what makes the output context of an `init` command equal to the context that
      `toTCtx` gives for the longer `VarCtx`.

      The agreement is `TContext.Equiv` and not equality. The scopes of a `TContext` are opaque
      hash maps upstream, and a map that `HMap.ofList` builds from a longer association list is not
      *structurally* the map that an insertion into the shorter map gives. -/
  toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
    TContext.Equiv (T := CoreLParams) (toTCtx (ctx.insert x mty))
      { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }

/-- The output scope of a command that `genCmd` draws: an `init` adds its variable at its stored
    type to the scope, and to the variable scopes after it; every other command keeps both. -/
theorem genCmd_outCtx_cases
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    {pctx : PolyOpCtx} {avoid : List String} {kt : Lambda.KnownTypes} (r : GenCmdResult)
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx avoid kt)) :
    (r.outCtx = ctx ∧ ∀ ts, cmdOutScopes ts r.cmd = ts) ∨
    ∃ x mty, r.outCtx = ctx.insert x mty ∧
      ∀ ts, cmdOutScopes ts r.cmd = ts.insert x (.forAll [] mty) := by
  rw [genCmd_support_iff octx tvars immutableVars ctx depth r pctx avoid kt] at hr
  rcases hr with hr | (hr | (⟨_, hr⟩ | (⟨_, hr⟩ | (hr | (hr | hr)))))
  · simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, _, e, _, rfl⟩ := hr
    refine Or.inr ⟨⟨name, ()⟩, mty, rfl, fun ts => ?_⟩
    dsimp only
    split <;> rfl
  · simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, _, rfl⟩ := hr
    exact Or.inr ⟨⟨name, ()⟩, mty, rfl, fun _ => rfl⟩
  · simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
      mem_support_elements_iff] at hr
    obtain ⟨_, _, e, _, rfl⟩ := hr
    refine Or.inl ⟨rfl, fun ts => ?_⟩
    dsimp only
    split <;> rfl
  · simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
      mem_support_elements_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    exact Or.inl ⟨rfl, fun _ => rfl⟩
  · simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr
    exact Or.inl ⟨rfl, fun _ => rfl⟩
  · simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr
    exact Or.inl ⟨rfl, fun _ => rfl⟩
  · simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr
    exact Or.inl ⟨rfl, fun _ => rfl⟩

/-- Soundness of `genCmd` through a `GenCmdSoundEnv`: each command in the support of the generator
    is well-typed from the variable scopes of `env.toTCtx ctx` to those of
    `env.toTCtx r.outCtx`, when the operators and schemes agree with `C` and the scope is
    functional. -/
theorem genCmd_sound_env
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (pctx : PolyOpCtx) {avoid : List String}
    (env : GenCmdSoundEnv octx tvars depth C pctx)
    (hops : ExprCtxOk C [] [] octx pctx)
    (hFun : Map.Functional ctx)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx avoid C.knownTypes)) :
    CmdWellTyped C (env.toTCtx ctx).types r.cmd (env.toTCtx r.outCtx).types := by
  refine StrataGenerators.cmdWellTyped_out_equiv
    (genCmd_sound_scopes octx tvars immutableVars ctx depth C (env.toTCtx ctx) hops
      (env.corr ctx) hFun (env.freshDisjoint ctx) r hr) ?_
  rcases genCmd_outCtx_cases octx tvars immutableVars ctx depth r hr with
    ⟨hout, hts⟩ | ⟨x, mty, hout, hts⟩
  · rw [hout, hts]
  · rw [hout, hts]
    exact (env.toTCtx_insert ctx x mty).1

/-- `genCmd` keeps the context *functional*. For a `set`, an `assert`, an `assume` and a `cover`,
    the output `VarCtx` is the input `ctx`. For an `init`, it is `ctx.insert x mty` for a **fresh**
    `x`, and `Map.insert_functional_of_fresh` says that such an insertion keeps functionality. This
    theorem carries the invariant `Functional` along a sequence of commands, so `genCmds_sound` can
    use the invariant at each context of the chain. -/
theorem genCmd_outCtx_functional
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) {avoid : List String}
    (hFun : Map.Functional ctx)
    {kt : Lambda.KnownTypes} (r : GenCmdResult)
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx avoid kt)) :
    Map.Functional r.outCtx := by
  rw [genCmd_support_iff octx tvars immutableVars ctx depth r pctx avoid kt] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det. The output context is `ctx.insert ⟨name, ()⟩ mty`, and `name` is fresh in `ctx`.
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, _, e, _, rfl⟩ := hr
    have hfresh := genFreshName_produces_fresh ctx name hname
    simp only [VarCtx.isFresh, VarCtx.find?, Option.isNone_iff_eq_none] at hfresh
    exact Map.insert_functional_of_fresh ctx ⟨name, ()⟩ mty hFun hfresh
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, _, rfl⟩ := hr
    have hfresh := genFreshName_produces_fresh ctx name hname
    simp only [VarCtx.isFresh, VarCtx.find?, Option.isNone_iff_eq_none] at hfresh
    exact Map.insert_functional_of_fresh ctx ⟨name, ()⟩ mty hFun hfresh
  · -- set_det. The output context is `ctx`.
    simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr; exact hFun
  · -- set_nondet
    simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr; exact hFun
  · -- assert
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr; exact hFun
  · -- assume
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr; exact hFun
  · -- cover
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr; exact hFun

/-- **`genCmd` keeps each type in the scope well-kinded in `C`.** The two `init` commands are the
    only commands that change the scope. The type that such a command stores comes from
    `genLMonoTy`, and that type is therefore well-kinded in each context which registers the
    arities that `SimpleTyArities` names. This theorem is the `cmd` case of the invariant
    `StrataGenerators.Stmt.WellKindedOk.ctxWK` for the statement generators. -/
theorem genCmd_outCtx_wellKinded
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) {C : LContext CoreLParams}
    (hC : SimpleTyArities C) (ctx : VarCtx) (depth : Nat)
    (hctx : ∀ ty ∈ ctx.values, C.WellKindedTy ty)
    {kt : Lambda.KnownTypes} (r : GenCmdResult)
    {avoid : List String}
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx avoid kt)) :
    ∀ ty ∈ r.outCtx.values, C.WellKindedTy ty := by
  rw [genCmd_support_iff octx tvars immutableVars ctx depth r pctx avoid kt] at hr
  rcases hr with hr | (hr | (⟨_, hr⟩ | (⟨_, hr⟩ | (hr | (hr | hr)))))
  · -- init_det. The scope gains `mty`, which comes from `genLMonoTy`.
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, hmty, _, _, rfl⟩ := hr
    intro ty hty
    rcases mem_values_insert ctx ⟨name, ()⟩ mty hty with rfl | hty'
    · exact genLMonoTy_mem_wellKindedTy hC ⟨_, hmty⟩
    · exact hctx ty hty'
  · -- init_nondet. The same argument applies.
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, hmty, rfl⟩ := hr
    intro ty hty
    rcases mem_values_insert ctx ⟨name, ()⟩ mty hty with rfl | hty'
    · exact genLMonoTy_mem_wellKindedTy hC ⟨_, hmty⟩
    · exact hctx ty hty'
  · -- A `set`, an `assert`, an `assume` and a `cover` do not change the scope.
    simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
      mem_support_elements_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr; exact hctx
  · simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
      mem_support_elements_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr; exact hctx
  · simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr; exact hctx
  · simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr; exact hctx
  · simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr; exact hctx

/-- Soundness of `genCmds`: each sequence of commands in the support of the generator satisfies the
    chain relation `CmdsWellTyped`, when the operators agree with `C` and the scope is functional.
    Proved by induction on the fuel `n`; the scope stays functional along the chain. -/
theorem genCmds_sound
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) (n : Nat)
    (C : LContext CoreLParams)
    (env : GenCmdSoundEnv octx tvars depth C) {avoid : List String}
    (hops : ExprCtxOk C [] [] octx [])
    (hFun : Map.Functional ctx)
    (result : List (Cmd Expression) × VarCtx)
    (hr : result ∈ SetGen.support
      (genCmds (G := SetGen.Set) octx tvars immutableVars ctx depth n avoid C.knownTypes)) :
    CmdsWellTyped C (env.toTCtx ctx).types result.1 (env.toTCtx result.2).types := by
  induction n generalizing ctx result with
  | zero =>
    simp only [genCmds, genCmdsWith, mem_support_pure_iff] at hr
    subst hr
    exact CmdsWellTyped.nil _
  | succ n ih =>
    simp only [genCmds, genCmdsWith, mem_support_bind_iff] at hr
    obtain ⟨⟨cmd, ctx'⟩, hcmd, rest_hr⟩ := hr
    dsimp only [GenCmdResult.outCtx, GenCmdResult.cmd] at rest_hr
    obtain ⟨⟨cmds, ctx''⟩, hcmds, hpure⟩ := rest_hr
    simp only [mem_support_pure_iff] at hpure
    have heq : result = (cmd :: cmds, ctx'') := by
      cases hpure; rfl
    subst heq
    have htyCmd := genCmd_sound_env octx tvars immutableVars ctx depth C [] env hops hFun
      ⟨cmd, ctx'⟩ hcmd
    have hFun' : Map.Functional ctx' :=
      genCmd_outCtx_functional octx [] tvars immutableVars ctx depth hFun ⟨cmd, ctx'⟩ hcmd
    exact CmdsWellTyped.cons _ _ _ cmd cmds htyCmd (ih ctx' hFun' (cmds, ctx'') hcmds)

-- ── A quick check that the generator runs ─────────────────────────────

open Std in
instance instToFormatUnitCmdHasTypeAGen : ToFormat Unit where
  format _ := .nil

#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨cmd, _⟩ ← genCmd [] [] [] [] 2
  IO.println <| Std.format cmd |>.pretty : IO Unit)

#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨cmd, ctx'⟩ ← genCmd [] [] [] [(⟨"x", ()⟩, .int), (⟨"y", ()⟩, .bool)] 2
  IO.println <| s!"{Std.format cmd |>.pretty} -- ctx: {ctx'}" : IO Unit)
