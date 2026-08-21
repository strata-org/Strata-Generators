import StrataGenerators.SetGen
import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString

/-!
# A generator for a well-typed command that satisfies `CmdHasTypeA`

A random generator on the `SetGen` interpretation of Basalt, for a well-typed imperative
command of Strata. Such a command is a `Cmd Expression`, and it satisfies the relation
`CmdHasTypeA`.

## Contents

- The support of the generator: `genCmd_support_iff`
- Soundness: `genCmd_sound`
- Completeness: `genCmd_complete`
- The lemmas for the soundness and the completeness of each constructor

## The approach

The generator works with a flat `VarCtx`, which is a list of pairs of a name and a type.
The theorem for soundness is compositional. It takes the soundness of the generator for an
expression, which says that `genLExpr` makes a well-typed expression, and it takes the
freshness properties of `genFreshName`. It then concludes that each generated command
satisfies `CmdHasTypeA`.
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
    rw [Map.keys_eq_map_fst] at hnodup
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hrest⟩ := hnodup
    simp only [Map.find?]
    cases hmem with
    | head => simp
    | tail _ hmem' =>
      -- `x` is a key of `rest`, and `a` is not a key of `rest`, therefore `a ≠ x`.
      have hxkey : x ∈ rest.map Prod.fst :=
        List.mem_map.mpr ⟨(x, v), hmem', rfl⟩
      have hne : a ≠ x := fun h => hnotin (h ▸ hxkey)
      simp only [if_neg hne]
      exact ih (by rw [Map.keys_eq_map_fst]; exact hrest) hmem'

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
    rw [Map.keys_eq_map_fst] at hnodup
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hrest⟩ := hnodup
    have hrest' : (Map.keys rest).Nodup := by rw [Map.keys_eq_map_fst]; exact hrest
    simp only [Map.insert]
    split
    · -- The key is at the head, therefore the keys do not change.
      rename_i hax; subst hax
      rw [Map.keys_eq_map_fst]
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨hnotin, hrest⟩
    · -- Recurse. The head key `a` stays, and it is fresh for the result of the recursion.
      rename_i hax
      rw [Map.keys_eq_map_fst]
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, by rw [← Map.keys_eq_map_fst]; exact ih hrest'⟩
      -- The keys of `insert rest x v` are a subset of `x :: keys rest`. However, `a ≠ x` holds
      -- and `a` is not a key of `rest`.
      intro hmem
      have hsub := Map.insert_keys rest (key := x) (val := v)
      rw [← Map.keys_eq_map_fst] at hmem
      have hin := hsub hmem
      simp only [List.mem_cons] at hin
      rcases hin with h | h
      · exact hax h
      · exact hnotin (by rw [← Map.keys_eq_map_fst]; exact h)

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
    simp only [Map.insert] at hmem
    split at hmem
    · -- The insertion replaces the head, which gives `(x, v) :: rest`.
      rename_i hax; subst hax
      cases hmem with
      | head => exact Or.inr rfl
      | tail _ h => exact Or.inl (List.Mem.tail _ h)
    · -- The insertion keeps the head, so recurse.
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

-- ── The soundness of each constructor ────────────────────────────────

/-- `TContext.Equiv` at `CoreLParams` is reflexive.

    The command rules of upstream constrain the output context only up to `TContext.Equiv`. A
    context on an `HMap` ignores the order of the insertions, so structural equality is too
    strong. Each rule that this module builds returns the canonical output context, so
    reflexivity discharges that premise. `TContext Unit` does not determine the parameter `T`,
    so a caller must give `T` and this wrapper does that. -/
theorem tctxEquivRefl (Γ : TContext Unit) : TContext.Equiv (T := CoreLParams) Γ Γ :=
  TContext.Equiv.refl (T := CoreLParams) Γ


/-- Soundness of an `assert`. If `e` has the type `bool` in the empty context of bound variables,
    then `.assert l e default` satisfies `CmdHasTypeA C Γ _ Γ` for *any* label `l`. The rule for
    an `assert` puts no condition on the label. -/
theorem genAssertCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (l : String)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.assert l e default) Γ :=
  CmdHasType'.assert Γ l e default Γ hwt (tctxEquivRefl Γ)

/-- Soundness of an `assume`. If `e` has the type `bool`, then `.assume l e default` satisfies
    `CmdHasTypeA C Γ _ Γ` for any label `l`. -/
theorem genAssumeCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (l : String)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.assume l e default) Γ :=
  CmdHasType'.assume Γ l e default Γ hwt (tctxEquivRefl Γ)

/-- Soundness of a `cover`. If `e` has the type `bool`, then `.cover l e default` satisfies
    `CmdHasTypeA C Γ _ Γ` for any label `l`. -/
theorem genCoverCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (l : String)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.cover l e default) Γ :=
  CmdHasType'.cover Γ l e default Γ hwt (tctxEquivRefl Γ)

/-- Soundness of a deterministic `set`. If `x` has the monotype `mty` in `Γ` and `e` has the type
    `mty`, then `.set x (det e) default` satisfies `CmdHasTypeA C Γ _ Γ`. -/
theorem genSetDet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfind : Γ.types.find? x = some (.forAll [] mty))
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e mty) :
    CmdHasTypeA C Γ (.set x (.det e) default) Γ :=
  CmdHasType'.set_det Γ x mty e default Γ hfind hwt (tctxEquivRefl Γ)

/-- Soundness of a nondeterministic `set`. If `x` has the monotype `mty` in `Γ`, then
    `.set x nondet default` satisfies `CmdHasTypeA C Γ _ Γ`. -/
theorem genSetNondet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfind : Γ.types.find? x = some (.forAll [] mty)) :
    CmdHasTypeA C Γ (.set x .nondet default) Γ :=
  CmdHasType'.set_nondet Γ x mty default Γ hfind (tctxEquivRefl Γ)

/-- A monomorphic type scheme `∀ []. mty`, which binds no variable, is `RigidAnnotCompat` with
    itself. An open with an empty list of type arguments gives `mty` without a change, because
    the empty substitution is the identity. The check for compatibility therefore reduces to
    reflexivity. -/
theorem rigidAnnotCompat_forAll_nil (mty : LMonoTy) :
    ∀ {aliases rigidVars},
    RigidAnnotCompat aliases rigidVars ((LTy.forAll [] mty).openFull []) mty := by
  intro aliases rigidVars
  have h : (LTy.forAll [] mty).openFull [] = mty := by
    simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
    exact LMonoTy.subst_single_empty mty
  rw [h]
  -- `RigidAnnotCompat` is an existential over one scope, and the empty scope is a witness.
  exact ⟨Strata.Util.HMap.empty, fun v _ => LMonoTy.subst_single_empty _,
    by rw [LMonoTy.subst_single_empty]; exact AliasEquiv.refl⟩

/-- Soundness of a deterministic `init`. If `x` is fresh in `Γ`, `x` is not a variable of `e`, and
    `e` has the type `mty`, then `init x (.forAll [] mty) (det e) default` is well-typed. Its
    output context is `{Γ with types := Γ.types.insert x (.forAll [] mty)}`. -/
theorem genInitDet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfresh : Γ.types.find? x = none)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e mty)
    (hnovar : x ∉ HasFvars.getFvars (P := Expression) e)
    (hwk : C.WellKindedTy mty) :
    CmdHasTypeA C Γ (.init x (.forAll [] mty) (.det e) default)
      { Γ with types := Γ.types.insert x (.forAll [] mty) } :=
  CmdHasType'.init_det Γ x (.forAll [] mty) e mty [] default _ hfresh hnovar rfl
    (rigidAnnotCompat_forAll_nil mty) hwk hwt (tctxEquivRefl _)

/-- Soundness of a nondeterministic `init`. If `x` is fresh in `Γ`, then
    `init x (.forAll [] mty) nondet default` is well-typed. -/
theorem genInitNondet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfresh : Γ.types.find? x = none) (hwk : C.WellKindedTy mty) :
    CmdHasTypeA C Γ (.init x (.forAll [] mty) .nondet default)
      { Γ with types := Γ.types.insert x (.forAll [] mty) } :=
  CmdHasType'.init_nondet Γ x (.forAll [] mty) mty [] default _ hfresh rfl
    (rigidAnnotCompat_forAll_nil mty) hwk (tctxEquivRefl _)

-- ── The support of `genCmd` ─────────────────────────────────────────

/-- The support of `genCmd`. A result is in the support exactly when one of the smaller
    generators gives it. This theorem states the soundness and the completeness of the generator
    at the syntactic level, before a proof reads the result against `CmdHasTypeA`. -/
theorem genCmd_support_iff
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (r : GenCmdResult) (pctx : PolyOpCtx := []) :
    r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx) ↔
    (r ∈ SetGen.support (genInitDet (G := SetGen.Set) octx tvars ctx depth depth pctx) ∨
     r ∈ SetGen.support (genInitNondet (G := SetGen.Set) tvars ctx depth) ∨
     (∃ h : (ctx.writable immutableVars).length > 0, r ∈ SetGen.support (genSetDet (G := SetGen.Set) octx tvars immutableVars ctx depth h pctx)) ∨
     (∃ h : (ctx.writable immutableVars).length > 0, r ∈ SetGen.support (genSetNondet (G := SetGen.Set) immutableVars ctx h)) ∨
     r ∈ SetGen.support (genAssertCmd (G := SetGen.Set) octx tvars ctx depth pctx) ∨
     r ∈ SetGen.support (genAssumeCmd (G := SetGen.Set) octx tvars ctx depth pctx) ∨
     r ∈ SetGen.support (genCoverCmd (G := SetGen.Set) octx tvars ctx depth pctx)) := by
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

/-- The length of `fallbackFreshName ctx` is one more than the length of the longest name in the
    context. -/
private theorem fallbackFreshName_length (ctx : VarCtx) :
    (fallbackFreshName ctx).length =
      (VarCtx.names ctx).foldl (fun acc nm => max acc nm.length) 0 + 1 := by
  simp [fallbackFreshName, String.length_ofList, List.length_replicate]

/-- `dodgeKeyword` never makes its argument shorter. It returns the argument without a change, or
    it adds a `_` to the end. -/
private theorem length_le_dodgeKeyword (s : String) :
    s.length ≤ (dodgeKeyword s).length := by
  unfold dodgeKeyword
  split
  · simp [String.length_append]
  · exact Nat.le_refl _

/-- `fallbackFreshName ctx` is fresh in `ctx`, because it is longer than each name in the
    context. -/
private theorem fallbackFreshName_isFresh (ctx : VarCtx) :
    VarCtx.isFresh ctx ⟨fallbackFreshName ctx, ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  rw [fallbackFreshName_length]; omega

/-- `dodgeKeyword (fallbackFreshName ctx)` is also fresh. The fallback name is already long
    enough, and `dodgeKeyword` only makes a name longer, so the result is also longer than each
    name in the context. -/
private theorem dodgeKeyword_fallbackFreshName_isFresh (ctx : VarCtx) :
    VarCtx.isFresh ctx ⟨dodgeKeyword (fallbackFreshName ctx), ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  have h := length_le_dodgeKeyword (fallbackFreshName ctx)
  rw [fallbackFreshName_length] at h
  omega

/-- Each name in the support of `genFreshName ctx` is fresh in `ctx`. The identifier
    `⟨name, ()⟩` of such a name is therefore absent from the context. -/
theorem genFreshName_produces_fresh (ctx : VarCtx) :
    ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
      VarCtx.isFresh ctx ⟨name, ()⟩ = true := by
  intro name hmem
  simp only [genFreshName, mem_support_bind_iff] at hmem
  obtain ⟨s, _, hname⟩ := hmem
  simp only [mem_support_ite_iff, mem_support_pure_iff] at hname
  rcases hname with ⟨hfresh, rfl⟩ | ⟨_, rfl⟩
  · exact hfresh
  · exact dodgeKeyword_fallbackFreshName_isFresh ctx

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
theorem genFreshName_not_keyword (ctx : VarCtx) :
    ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
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

/-- The predicate that says that `genLExpr` is sound at a type `τ`: each expression in the support
    of the generator is well-typed. `genLExpr_sound` proves this claim, and this module takes it as
    a hypothesis. -/
def GenLExprSound (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (pctx : PolyOpCtx := []) : Prop :=
  ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ) →
    LExpr.HasTypeA (T := LExprParams') [] e τ

/-- The predicate that says that a fresh name from `genFreshName` occurs as a free variable in no
    expression from `genLExpr`. This claim follows from the structure of the generator, because
    `pickFVar` draws each free variable from `fctx`.
    `freshNamesDisjointFromExprs_toFVarCtx` proves it. -/
def FreshNamesDisjointFromExprs (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (ctx : VarCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : Prop :=
  ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
    ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ) →
      (⟨name, ()⟩ : Identifier Unit) ∉ HasFvars.getFvars (P := Expression) e

/-- Soundness of `genCmd`: each result in the support of the generator gives a well-typed command.
    The output context `Γ'` satisfies `CmdHasTypeA C Γ cmd Γ'`.

    The condition that the name is fresh in `Γ` comes from `genFreshName_produces_fresh` and from
    `hCorr`. The hypothesis `hDisjoint` says that a fresh name equals no free variable of a
    generated expression. -/
theorem genCmd_sound
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit)
    (hC : SimpleTyArities C)
    (hCorr : VarCtxCorresponds ctx Γ)
    (hFun : Map.Functional ctx)
    (hExprSound : GenLExprSound ctx.toFVarCtx octx tvars depth)
    (hDisjoint : FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx depth)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth)) :
    ∃ Γ', CmdHasTypeA C Γ r.cmd Γ' := by
  rw [genCmd_support_iff] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, e, he, rfl⟩ := hr
    have hfreshΓ := hCorr.2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    have hnovar := hDisjoint name hname mty e he
    have hwt := hExprSound mty e he
    exact ⟨_, CmdHasType'.init_det Γ ⟨name, ()⟩ _ e mty [] default _ hfreshΓ hnovar rfl
      (rigidAnnotCompat_forAll_nil mty) (wellKindedTy_of_genLMonoTy hC tvars depth mty hmty) hwt
      (tctxEquivRefl _)⟩
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, rfl⟩ := hr
    have hfreshΓ := hCorr.2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    exact ⟨_, CmdHasType'.init_nondet Γ ⟨name, ()⟩ _ mty [] default _ hfreshΓ rfl
      (rigidAnnotCompat_forAll_nil mty) (wellKindedTy_of_genLMonoTy hC tvars depth mty hmty)
      (tctxEquivRefl _)⟩
  · -- set_det
    simp only [genSetDet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, e, he, rfl⟩ := hr
    have hmemCtx : List.Mem (name, mty) ctx := (List.mem_filter.mp hmem).1
    have hfind := hCorr.1 name mty (Map.find?_of_mem_of_functional ctx name mty hFun hmemCtx)
    have hwt := hExprSound mty e he
    exact ⟨Γ, CmdHasType'.set_det Γ name mty e default Γ hfind hwt (tctxEquivRefl Γ)⟩
  · -- set_nondet
    simp only [genSetNondet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, rfl⟩ := hr
    have hmemCtx : List.Mem (name, mty) ctx := (List.mem_filter.mp hmem).1
    have hfind := hCorr.1 name mty (Map.find?_of_mem_of_functional ctx name mty hFun hmemCtx)
    exact ⟨Γ, CmdHasType'.set_nondet Γ name mty default Γ hfind (tctxEquivRefl Γ)⟩
  · -- assert. `genIdentName` draws the label, and the typing rule ignores it.
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _hl, e, he, rfl⟩ := hr
    have hwt := hExprSound .bool e he
    exact ⟨Γ, CmdHasType'.assert Γ l e default Γ hwt (tctxEquivRefl Γ)⟩
  · -- assume
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _hl, e, he, rfl⟩ := hr
    have hwt := hExprSound .bool e he
    exact ⟨Γ, CmdHasType'.assume Γ l e default Γ hwt (tctxEquivRefl Γ)⟩
  · -- cover
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _hl, e, he, rfl⟩ := hr
    have hwt := hExprSound .bool e he
    exact ⟨Γ, CmdHasType'.cover Γ l e default Γ hwt (tctxEquivRefl Γ)⟩

-- ── The completeness of `genCmd` ─────────────────────────────────────

/-- The predicate that says that `genLExpr` is complete at a type `τ`: the support of the generator
    holds each well-typed expression that satisfies the side conditions of the generator.
    `genLExprBase_complete` proves this claim, and its proof needs Mathlib. This module takes the
    claim as a hypothesis. -/
def GenLExprComplete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : Prop :=
  ∀ τ e, LExpr.HasTypeA (T := LExprParams') [] e τ →
    e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ)

/-- Completeness of `genCmd` against `CmdHasTypeA`: if a command is well-typed and the smaller
    generators can reach each of its parts, then the support of `genCmd` holds it.

    The proof inverts the derivation of `CmdHasTypeA`. The hypotheses give what the generator needs
    beyond good typing:
    - `hExprComplete`: the support of `genLExpr` holds each well-typed expression.
    - `hNameReach`: the generator can reach the name of the target of an `init` or a `set`.
    - `hTyReach`: the support of `genLMonoTy` holds the type of the target of an `init`.
    - `hVarInCtx`: `ctx` holds the target of a `set` command.

    The generator fixes each label to `"l"` and each piece of metadata to `default`. The conclusion
    says that the generator gives a command with the same *expression* and the same *variable*, and
    its label and metadata can differ. Any label in the support of `genIdentName` also works.

    **This theorem is vacuous.** The hypothesis `hExprComplete : GenLExprComplete …` has no
    witness, and `SpecComplete.Gaps.not_GenLExprComplete` proves it false at *each* depth. A free
    variable with an annotation is well-typed against the empty context, and the generator cannot
    reach it when the scope is empty. `spec_complete` takes no hypothesis of this shape. It uses
    `SpecComplete.ExprOk`, which threads the scope and the size, and which claims reachability for
    one expression at a time. A fix for this theorem is the same change: replace `hExprComplete`
    with a condition for one command, as `SpecComplete.CmdExprOk` does. `spec_complete` does
    **not** call this theorem. It inverts the derivation of `CmdHasTypeA` itself. -/
theorem genCmd_complete
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (Γ Γ' : TContext Unit)
    (cmd : Cmd Expression)
    (hwt : CmdHasTypeA C Γ cmd Γ')
    (hExprComplete : GenLExprComplete ctx.toFVarCtx octx tvars depth)
    (hNameReach : ∀ x : Identifier Unit,
      (∃ xty eOrNd md, cmd = .init x xty eOrNd md) →
      x.name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx))
    (hTyReach : ∀ (mty : LMonoTy),
      mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth))
    (hVarInCtx : ∀ (x : Identifier Unit) (mty : LMonoTy),
      Γ.types.find? x = some (.forAll [] mty) →
      List.Mem (x, mty) (ctx.writable immutableVars)) :
    ∃ r : GenCmdResult,
      r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth) ∧
      CmdHasTypeA C Γ r.cmd Γ' := by
  cases hwt with
  | init_det x xty e mty tys md Δ hfresh hnovar _ _ hwk hexpr hequiv =>
    have hname := hNameReach x ⟨xty, .det e, md, rfl⟩
    have hmty := hTyReach mty
    have he := hExprComplete mty e hexpr
    have hinSupport : (⟨.init x (.forAll [] mty) (.det e) default, ctx.insert ⟨x.name, ()⟩ mty⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inl (by
        simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨x.name, hname, mty, hmty, e, he, rfl⟩))
    exact ⟨_, hinSupport, CmdHasType'.init_det _ x _ e mty [] default _ hfresh hnovar rfl
      (rigidAnnotCompat_forAll_nil mty) hwk hexpr hequiv⟩
  | init_nondet x xty mty tys md Δ hfresh _ _ hwk hequiv =>
    have hname := hNameReach x ⟨xty, .nondet, md, rfl⟩
    have hmty := hTyReach mty
    have hinSupport : (⟨.init x (.forAll [] mty) .nondet default, ctx.insert ⟨x.name, ()⟩ mty⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inl (by
        simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨x.name, hname, mty, hmty, rfl⟩)))
    exact ⟨_, hinSupport, CmdHasType'.init_nondet _ x _ mty [] default _ hfresh rfl
      (rigidAnnotCompat_forAll_nil mty) hwk hequiv⟩
  | set_det x mty e md Δ hfind hexpr hequiv =>
    have hentry := hVarInCtx x mty hfind
    have he := hExprComplete mty e hexpr
    have hinSupport : (⟨.set x (.det e) default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inl ⟨List.length_pos_of_mem hentry, by
        simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_elements_iff]
        exact ⟨(x, mty), hentry, e, he, rfl⟩⟩)))
    exact ⟨_, hinSupport, CmdHasType'.set_det _ x mty e default _ hfind hexpr hequiv⟩
  | set_nondet x mty md Δ hfind hequiv =>
    have hentry := hVarInCtx x mty hfind
    have hinSupport : (⟨.set x .nondet default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨List.length_pos_of_mem hentry, by
        simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
                   mem_support_elements_iff]
        exact ⟨(x, mty), hentry, rfl⟩⟩))))
    exact ⟨_, hinSupport, CmdHasType'.set_nondet _ x mty default _ hfind hequiv⟩
  | assert l e md Δ hexpr hequiv =>
    have he := hExprComplete .bool e hexpr
    -- `"l"` is a legal identifier and not a keyword, so the support of `genIdentName` holds it.
    have hlblL : "l" ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
      StrataGenerators.Function.mem_support_genIdentName_of_syntactic'
        (by decide +kernel) (by decide +kernel)
    have hinSupport : (⟨.assert "l" e default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨"l", hlblL, e, he, rfl⟩))))))
    exact ⟨_, hinSupport, CmdHasType'.assert _ "l" e default _ hexpr hequiv⟩
  | assume l e md Δ hexpr hequiv =>
    have he := hExprComplete .bool e hexpr
    have hlblL : "l" ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
      StrataGenerators.Function.mem_support_genIdentName_of_syntactic'
        (by decide +kernel) (by decide +kernel)
    have hinSupport : (⟨.assume "l" e default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨"l", hlblL, e, he, rfl⟩)))))))
    exact ⟨_, hinSupport, CmdHasType'.assume _ "l" e default _ hexpr hequiv⟩
  | cover l e md Δ hexpr hequiv =>
    have he := hExprComplete .bool e hexpr
    have hlblL : "l" ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
      StrataGenerators.Function.mem_support_genIdentName_of_syntactic'
        (by decide +kernel) (by decide +kernel)
    have hinSupport : (⟨.cover "l" e default, ctx⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth) :=
      (genCmd_support_iff ..).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
        simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨"l", hlblL, e, he, rfl⟩)))))))
    exact ⟨_, hinSupport, CmdHasType'.cover _ "l" e default _ hexpr hequiv⟩

-- ── The typing of a sequence of commands, as a chain ────────────────

/-- Good typing for a sequence of commands. Each command has a type from one context to the next
    context, and the commands therefore form a chain `Γ₀ → Γ₁ → ... → Γₙ`. -/
inductive CmdsHasTypeA (C : LContext CoreLParams) :
    TContext Unit → List (Cmd Expression) → TContext Unit → Prop where
  | nil : ∀ Γ, CmdsHasTypeA C Γ [] Γ
  | cons : ∀ Γ Γ' Γ'' cmd cmds,
      CmdHasTypeA C Γ cmd Γ' →
      CmdsHasTypeA C Γ' cmds Γ'' →
      CmdsHasTypeA C Γ (cmd :: cmds) Γ''

/-- The hypotheses that a proof of `genCmd_sound` needs at *each* context that a draw of a sequence
    can reach. The structure holds four parts:
    - a function that gives a `TContext` for each `VarCtx`;
    - the correspondence between the two contexts;
    - the soundness of the generator for an expression;
    - the fact that a fresh name equals no free variable of a generated expression, at each context
      that a draw can reach. -/
structure GenCmdSoundEnv (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (C : LContext CoreLParams) (pctx : PolyOpCtx := []) where
  /-- Gives the semantic `TContext` for a flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The correspondence holds for each context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- The soundness of the generator for an expression, at the free-variable context of *each*
      scope. The command generators give `ctx.toFVarCtx` to `genLExpr`, so the proof needs
      soundness at that context. -/
  exprSound : ∀ (ctx : VarCtx), GenLExprSound ctx.toFVarCtx octx tvars depth pctx
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
      *structurally* the map that an insertion into the shorter map gives. `Equiv` is agreement of
      `find?` at each name, and the `init` rules of upstream ask for exactly that. -/
  toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
    TContext.Equiv (T := CoreLParams) (toTCtx (ctx.insert x mty))
      { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }

/-- Soundness of `genCmd` through a `GenCmdSoundEnv`: each result in the support of the generator
    gives a command whose type goes from `env.toTCtx ctx` to `env.toTCtx r.outCtx`. The proof uses
    the same cases as `genCmd_sound`, and it also shows that the output context equals `toTCtx` at
    the output `VarCtx` of the generator. -/
theorem genCmd_sound_env
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (C : LContext CoreLParams) (pctx : PolyOpCtx)
    (env : GenCmdSoundEnv octx tvars depth C pctx)
    (hC : SimpleTyArities C)
    (hFun : Map.Functional ctx)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx)) :
    CmdHasTypeA C (env.toTCtx ctx) r.cmd (env.toTCtx r.outCtx) := by
  rw [genCmd_support_iff octx tvars immutableVars ctx depth r pctx] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, e, he, rfl⟩ := hr
    have hfreshΓ := (env.corr ctx).2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    have hnovar := (env.freshDisjoint ctx) name hname mty e he
    have hwt := env.exprSound ctx mty e he
    exact CmdHasType'.init_det _ ⟨name, ()⟩ _ e mty [] default _ hfreshΓ hnovar rfl
      (rigidAnnotCompat_forAll_nil mty) (wellKindedTy_of_genLMonoTy hC tvars depth mty hmty) hwt
      (env.toTCtx_insert ctx ⟨name, ()⟩ mty)
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, hname, mty, hmty, rfl⟩ := hr
    have hfreshΓ := (env.corr ctx).2 ⟨name, ()⟩ (genFreshName_produces_fresh ctx name hname)
    exact CmdHasType'.init_nondet _ ⟨name, ()⟩ _ mty [] default _ hfreshΓ rfl
      (rigidAnnotCompat_forAll_nil mty) (wellKindedTy_of_genLMonoTy hC tvars depth mty hmty)
      (env.toTCtx_insert ctx ⟨name, ()⟩ mty)
  · -- set_det
    simp only [genSetDet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, e, he, rfl⟩ := hr
    have hmemCtx : List.Mem (name, mty) ctx := (List.mem_filter.mp hmem).1
    have hfind := (env.corr ctx).1 name mty (Map.find?_of_mem_of_functional ctx name mty hFun hmemCtx)
    have hwt := env.exprSound ctx mty e he
    exact CmdHasType'.set_det _ name mty e default _ hfind hwt (tctxEquivRefl _)
  · -- set_nondet
    simp only [genSetNondet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, rfl⟩ := hr
    have hmemCtx : List.Mem (name, mty) ctx := (List.mem_filter.mp hmem).1
    have hfind := (env.corr ctx).1 name mty (Map.find?_of_mem_of_functional ctx name mty hFun hmemCtx)
    exact CmdHasType'.set_nondet _ name mty default _ hfind (tctxEquivRefl _)
  · -- assert. `genIdentName` draws the label, and the typing rule ignores it.
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _hl, e, he, rfl⟩ := hr
    exact CmdHasType'.assert _ l e default _ (env.exprSound ctx .bool e he) (tctxEquivRefl _)
  · -- assume
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _hl, e, he, rfl⟩ := hr
    exact CmdHasType'.assume _ l e default _ (env.exprSound ctx .bool e he) (tctxEquivRefl _)
  · -- cover
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨l, _hl, e, he, rfl⟩ := hr
    exact CmdHasType'.cover _ l e default _ (env.exprSound ctx .bool e he) (tctxEquivRefl _)

/-- `genCmd` keeps the context *functional*. For a `set`, an `assert`, an `assume` and a `cover`,
    the output `VarCtx` is the input `ctx`. For an `init`, it is `ctx.insert x mty` for a **fresh**
    `x`, and `Map.insert_functional_of_fresh` says that such an insertion keeps functionality. This
    theorem carries the invariant `Functional` along a sequence of commands, so `genCmds_sound` can
    use the invariant at each context of the chain. -/
theorem genCmd_outCtx_functional
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) (hFun : Map.Functional ctx)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx)) :
    Map.Functional r.outCtx := by
  rw [genCmd_support_iff octx tvars immutableVars ctx depth r pctx] at hr
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
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx)) :
    ∀ ty ∈ r.outCtx.values, C.WellKindedTy ty := by
  rw [genCmd_support_iff octx tvars immutableVars ctx depth r pctx] at hr
  rcases hr with hr | (hr | (⟨_, hr⟩ | (⟨_, hr⟩ | (hr | (hr | hr)))))
  · -- init_det. The scope gains `mty`, which comes from `genLMonoTy`.
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, hmty, _e, _, rfl⟩ := hr
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
    chain relation `CmdsHasTypeA`.

    The proof is by induction on the fuel `n`. At each step it types the head command with
    `genCmd_sound_env`, and it then applies the induction hypothesis to the tail with the new
    context. `genCmd_outCtx_functional` keeps the invariant `Functional` on the context of the
    chain. -/
theorem genCmds_sound
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) (n : Nat)
    (C : LContext CoreLParams)
    (env : GenCmdSoundEnv octx tvars depth C)
    (hC : SimpleTyArities C)
    (hFun : Map.Functional ctx)
    (result : List (Cmd Expression) × VarCtx)
    (hr : result ∈ SetGen.support (genCmds (G := SetGen.Set) octx tvars immutableVars ctx depth n)) :
    CmdsHasTypeA C (env.toTCtx ctx) result.1 (env.toTCtx result.2) := by
  induction n generalizing ctx result with
  | zero =>
    simp only [genCmds, mem_support_pure_iff] at hr
    subst hr
    exact CmdsHasTypeA.nil _
  | succ n ih =>
    simp only [genCmds, mem_support_bind_iff] at hr
    obtain ⟨⟨cmd, ctx'⟩, hcmd, rest_hr⟩ := hr
    dsimp only [GenCmdResult.outCtx, GenCmdResult.cmd] at rest_hr
    obtain ⟨⟨cmds, ctx''⟩, hcmds, hpure⟩ := rest_hr
    simp only [mem_support_pure_iff] at hpure
    have heq : result = (cmd :: cmds, ctx'') := by
      cases hpure; rfl
    subst heq
    have htyCmd := genCmd_sound_env octx tvars immutableVars ctx depth C [] env hC hFun ⟨cmd, ctx'⟩ hcmd
    have hFun' : Map.Functional ctx' :=
      genCmd_outCtx_functional octx [] tvars immutableVars ctx depth hFun ⟨cmd, ctx'⟩ hcmd
    exact CmdsHasTypeA.cons _ _ _ cmd cmds htyCmd (ih ctx' hFun' (cmds, ctx'') hcmds)

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
