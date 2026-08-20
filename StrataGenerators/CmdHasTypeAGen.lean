import StrataGenerators.SetGen
import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString

/-!
# Generator of well-typed commands satisfying `CmdHasTypeA`

A Basalt `SetGen`-based random generator for well-typed Strata imperative
commands (`Cmd Expression`) that satisfy the `CmdHasTypeA` relation.

## Contents

- Support characterization: `genCmd_support_iff`
- Full soundness: `genCmd_sound`
- Full completeness: `genCmd_complete`
- Per-constructor soundness and completeness lemmas

## Approach

The generator works with a flat `VarCtx` (list of name-type pairs). The full
soundness theorem is stated compositionally: it takes expression-level soundness
(`genLExpr` produces well-typed expressions) and freshness properties of
`genFreshName` as hypotheses, then concludes that every generated command
satisfies `CmdHasTypeA`.
-/

-- ── VarCtx ↔ TContext correspondence ─────────────────────────────────

/-- A `VarCtx` corresponds to a `TContext` if every lookup agrees: whatever
    `ctx.find?` resolves a name to (a monotype `mty`) `Γ` resolves to the
    monomorphic polytype `forAll [] mty`, and names fresh for `ctx` are absent
    from `Γ`.

    Condition 1 is phrased in terms of `ctx.find?` (the *resolved* binding, i.e.
    the first matching pair), **not** raw `List.Mem`. This matters because a flat
    `VarCtx` may in principle carry duplicate keys, and a `TContext`'s `find?`
    can only agree with one binding per name. Using `find?` on both sides makes
    the correspondence hold for *every* `ctx` — even ill-formed duplicate-key
    ones — so a soundness environment can supply `corr : ∀ ctx` unconditionally.
    (The reachable contexts are in fact always `Nodup`-keyed, since the seed is
    and `Map.insert` deduplicates; that `Nodup` fact is what lets the `set` case,
    whose target is drawn by `elements` from *any* member, recover a `find?`.) -/
def VarCtxCorresponds (ctx : VarCtx) (Γ : TContext Unit) : Prop :=
  (∀ (x : Identifier Unit) mty, ctx.find? x = some mty →
    Γ.types.find? x = some (.forAll [] mty)) ∧
  (∀ (x : Identifier Unit), VarCtx.isFresh ctx x = true →
    Γ.types.find? x = none)

/-- In a `Nodup`-key map, membership determines the `find?` result: if `(x, v)`
    is a member and the keys are `Nodup`, then `find? x = some v` (there is no
    earlier, shadowing binding for `x`). This is what lets the `set` cases — whose
    target `(x, mty)` is drawn by `elements` from *any* member of `ctx` — recover
    the resolved `ctx.find? x = some mty` needed by the `find?`-based
    `VarCtxCorresponds`. -/
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
      -- `x` is a key of `rest`, and `a ∉ rest.keys`, so `a ≠ x`.
      have hxkey : x ∈ rest.map Prod.fst :=
        List.mem_map.mpr ⟨(x, v), hmem', rfl⟩
      have hne : a ≠ x := fun h => hnotin (h ▸ hxkey)
      simp only [if_neg hne]
      exact ih (by rw [Map.keys_eq_map_fst]; exact hrest) hmem'

/-- `Map.insert` preserves `Nodup` of the key list: inserting either replaces an
    existing binding in place (keys unchanged) or appends a genuinely fresh key
    (keys stay `Nodup`). This is what carries the `Nodup` invariant across the
    `init` command, whose output context is `ctx.insert x mty`. -/
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
    · -- key found at head: keys unchanged
      rename_i hax; subst hax
      rw [Map.keys_eq_map_fst]
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨hnotin, hrest⟩
    · -- recurse; head key `a` stays, fresh w.r.t. the recursive result
      rename_i hax
      rw [Map.keys_eq_map_fst]
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, by rw [← Map.keys_eq_map_fst]; exact ih hrest'⟩
      -- `a ∈ keys (insert rest x v) ⊆ x :: keys rest`, but `a ≠ x` and `a ∉ keys rest`.
      intro hmem
      have hsub := Map.insert_keys rest (key := x) (val := v)
      rw [← Map.keys_eq_map_fst] at hmem
      have hin := hsub hmem
      simp only [List.mem_cons] at hin
      rcases hin with h | h
      · exact hax h
      · exact hnotin (by rw [← Map.keys_eq_map_fst]; exact h)

-- ── Functional contexts (Nodup-weakening) ────────────────────────────

/-- A `Map` is *functional* when any two entries sharing a key share a value.
    This is strictly weaker than `Nodup`-keys: it permits duplicate keys as long
    as they are bound to equal values (exactly the situation created by an `inout`
    parameter, which appears in both the input and output scopes with the *same*
    type). It is nonetheless enough to resolve `set` targets to a definite
    `find?` (`Map.find?_of_mem_of_functional`) and is preserved by fresh
    insertion (`Map.insert_functional_of_fresh`), so it can replace the threaded
    `keys.Nodup` invariant throughout the command/statement soundness proofs. -/
def Map.Functional {α β : Type} [DecidableEq α] (m : Map α β) : Prop :=
  ∀ (x : α) (v₁ v₂ : β), List.Mem (x, v₁) m → List.Mem (x, v₂) m → v₁ = v₂

/-- A `Nodup`-keyed map is functional (each key appears once, so any two entries
    with the same key are literally the same entry). This lets a seed context
    whose disjointness already yields `Nodup` keys satisfy the weaker
    `Functional` invariant the soundness proofs now thread. -/
theorem Map.functional_of_nodup {α β : Type} [DecidableEq α]
    (m : Map α β) (hnodup : m.keys.Nodup) : Map.Functional m := by
  intro x v₁ v₂ h₁ h₂
  have e₁ := Map.find?_of_mem_of_nodup m x v₁ hnodup h₁
  have e₂ := Map.find?_of_mem_of_nodup m x v₂ hnodup h₂
  rw [e₁] at e₂
  exact (Option.some.injEq _ _).mp e₂

/-- If `find? m x = none` then `x` is not a key of `m` (no entry `(x, w)`). -/
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

/-- In a *functional* map, membership determines `find?`: if `(x, v)` is a member
    then `find? x = some v`. (The first entry with key `x` binds some value `v'`;
    functionality forces `v' = v`.) This is the functional analogue of
    `Map.find?_of_mem_of_nodup`, and is what lets the `set` cases — whose target
    is drawn by `elements` from *any* member — recover the resolved `find?`. -/
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
      · -- head key `a = x`; head value `b` and tail value `v` share key `x`
        rename_i hax; subst hax
        have hb : b = v := hfun a b v (List.Mem.head _) (List.Mem.tail _ hmem')
        rw [hb]
      · -- head key differs; recurse (functionality restricts to the tail)
        exact ih (fun y w₁ w₂ h₁ h₂ =>
          hfun y w₁ w₂ (List.Mem.tail _ h₁) (List.Mem.tail _ h₂)) hmem'

/-- Every member of `m.insert x v` is either a member of `m` or the new entry
    `(x, v)`. (Insertion either overwrites the first `x`-entry — leaving a new
    head `(x, v)` and the untouched tail ⊆ `m` — or appends `(x, v)`.) -/
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
    · -- overwrite head: `(x, v) :: rest`
      rename_i hax; subst hax
      cases hmem with
      | head => exact Or.inr rfl
      | tail _ h => exact Or.inl (List.Mem.tail _ h)
    · -- keep head, recurse
      cases hmem with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ h =>
        rcases ih h with h' | h'
        · exact Or.inl (List.Mem.tail _ h')
        · exact Or.inr h'

/-- Inserting a *fresh* key preserves functionality: since `x` is absent from `m`,
    the insertion appends `(x, v)` without disturbing any existing binding, and no
    existing entry shares its key. This carries the `Functional` invariant across
    the `init` command (whose output context is `ctx.insert x mty` with `x` fresh
    by `genFreshName_produces_fresh`). -/
theorem Map.insert_functional_of_fresh {α β : Type} [DecidableEq α]
    (m : Map α β) (x : α) (v : β)
    (hfun : Map.Functional m) (hfresh : Map.find? m x = none) :
    Map.Functional (m.insert x v) := by
  intro y w₁ w₂ h₁ h₂
  have hnotin := Map.not_mem_of_find?_none m x hfresh
  rcases Map.mem_insert m x v y w₁ h₁ with hm₁ | he₁ <;>
    rcases Map.mem_insert m x v y w₂ h₂ with hm₂ | he₂
  · exact hfun y w₁ w₂ hm₁ hm₂
  · -- `(y, w₁) ∈ m` and `(y, w₂) = (x, v)`: then `y = x`, contradicting freshness
    obtain ⟨hy, _⟩ := Prod.mk.injEq .. |>.mp he₂
    exact absurd (hy ▸ hm₁) (hnotin w₁)
  · obtain ⟨hy, _⟩ := Prod.mk.injEq .. |>.mp he₁
    exact absurd (hy ▸ hm₂) (hnotin w₂)
  · rw [(Prod.mk.injEq ..).mp he₁ |>.2, (Prod.mk.injEq ..).mp he₂ |>.2]

/-- If `(x, v)` is a member of `m₁ ++ m₂` and `x` is not a key of `m₁`, then the
    entry lives in `m₂`. (The `x`-entry cannot be in the `m₁` half.) -/
theorem Map.mem_of_append_not_mem_keys {α β : Type} [DecidableEq α]
    (m₁ m₂ : Map α β) (x : α) (v : β)
    (hmem : List.Mem (x, v) (m₁ ++ m₂)) (hnk : x ∉ Map.keys m₁) :
    List.Mem (x, v) m₂ := by
  rcases List.mem_append.mp hmem with h | h
  · exact absurd (by rw [Map.keys_eq_map_fst]; exact List.mem_map.mpr ⟨(x, v), h, rfl⟩) hnk
  · exact h

/-- Symmetric to `Map.mem_of_append_not_mem_keys`: if `(x, v) ∈ m₁ ++ m₂` and `x`
    is not a key of `m₂`, then the entry lives in `m₁`. -/
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

/-- Functionality composes over append when the two halves *agree* on shared
    keys: if `m₁` and `m₂` are each functional and any key common to both binds
    equal values across them, the concatenation `m₁ ++ m₂` is functional. This is
    the workhorse for the in-out body seed, whose scope is
    `inputs ++ outputs ++ old`: the inout block appears in both `inputs` and
    `outputs` bound to the *same* type (agreement), while every other overlap is
    empty (vacuous agreement). -/
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

-- ── Per-constructor soundness ────────────────────────────────────────

/-- Reflexivity of `TContext.Equiv` at `CoreLParams`.

    Upstream's command rules constrain the output context only up to `TContext.Equiv`
    (the `HMap`-backed context ignores insertion order, so structural equality is too
    strong). Every rule we build hands back the canonical output context, so reflexivity
    discharges that premise. The parameter `T` is not determined by `TContext Unit`, so it
    has to be supplied explicitly — hence this wrapper. -/
theorem tctxEquivRefl (Γ : TContext Unit) : TContext.Equiv (T := CoreLParams) Γ Γ :=
  TContext.Equiv.refl (T := CoreLParams) Γ


/-- Soundness of assert: if `e` has type `bool` (in the empty bvar context),
    then `.assert l e default` satisfies `CmdHasTypeA C Γ _ Γ` for *any* label `l`
    (the `assert` rule does not constrain the label). -/
theorem genAssertCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (l : String)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.assert l e default) Γ :=
  CmdHasType'.assert Γ l e default Γ hwt (tctxEquivRefl Γ)

/-- Soundness of assume: if `e` has type `bool`, then `.assume l e default`
    satisfies `CmdHasTypeA C Γ _ Γ` for any label `l`. -/
theorem genAssumeCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (l : String)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.assume l e default) Γ :=
  CmdHasType'.assume Γ l e default Γ hwt (tctxEquivRefl Γ)

/-- Soundness of cover: if `e` has type `bool`, then `.cover l e default`
    satisfies `CmdHasTypeA C Γ _ Γ` for any label `l`. -/
theorem genCoverCmd_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (l : String)
    (e : Expression.Expr)
    (hwt : LExpr.HasTypeA (T := LExprParams') [] e .bool) :
    CmdHasTypeA C Γ (.cover l e default) Γ :=
  CmdHasType'.cover Γ l e default Γ hwt (tctxEquivRefl Γ)

/-- Soundness of set_det: if `x` has monotype `mty` in `Γ` and `e` has type
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

/-- Soundness of set_nondet: if `x` has monotype `mty` in `Γ`,
    then `.set x nondet default` satisfies `CmdHasTypeA C Γ _ Γ`. -/
theorem genSetNondet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfind : Γ.types.find? x = some (.forAll [] mty)) :
    CmdHasTypeA C Γ (.set x .nondet default) Γ :=
  CmdHasType'.set_nondet Γ x mty default Γ hfind (tctxEquivRefl Γ)

/-- A monomorphic type scheme `∀ []. mty` (no bound variables) is trivially
    `RigidAnnotCompat` with itself: opening with an empty list of type arguments
    yields `mty` unchanged (the empty substitution is the identity), so the
    compatibility check reduces to reflexivity. -/
theorem rigidAnnotCompat_forAll_nil (mty : LMonoTy) :
    ∀ {aliases rigidVars},
    RigidAnnotCompat aliases rigidVars ((LTy.forAll [] mty).openFull []) mty := by
  intro aliases rigidVars
  have h : (LTy.forAll [] mty).openFull [] = mty := by
    simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
    exact LMonoTy.subst_single_empty mty
  rw [h]
  -- `RigidAnnotCompat` is an existential over a single scope; the empty scope works.
  exact ⟨Strata.Util.HMap.empty, fun v _ => LMonoTy.subst_single_empty _,
    by rw [LMonoTy.subst_single_empty]; exact AliasEquiv.refl⟩

/-- Soundness of init_det: if `x` is fresh in `Γ`, `x ∉ vars(e)`, and `e`
    has type `mty`, then `init x (.forAll [] mty) (det e) default` is well-typed
    with output context `{Γ with types := Γ.types.insert x (.forAll [] mty)}`. -/
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

/-- Soundness of init_nondet: if `x` is fresh in `Γ`,
    then `init x (.forAll [] mty) nondet default` is well-typed. -/
theorem genInitNondet_sound
    (C : LContext CoreLParams)
    (Γ : TContext Unit)
    (x : Identifier Unit) (mty : LMonoTy)
    (hfresh : Γ.types.find? x = none) (hwk : C.WellKindedTy mty) :
    CmdHasTypeA C Γ (.init x (.forAll [] mty) .nondet default)
      { Γ with types := Γ.types.insert x (.forAll [] mty) } :=
  CmdHasType'.init_nondet Γ x (.forAll [] mty) mty [] default _ hfresh rfl
    (rigidAnnotCompat_forAll_nil mty) hwk (tctxEquivRefl _)

-- ── Support characterization of genCmd ──────────────────────────────

/-- Full support characterization of `genCmd`: a result is in the support iff
    it comes from one of the sub-generators. This is the combined
    soundness/completeness theorem at the syntactic level (before interpreting
    against `CmdHasTypeA`). -/
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

-- ── Freshness proof for genFreshName ────────────────────────────────

/-- If no entry in `ctx` has key equal to `x`, then `find?` returns `none`. -/
private theorem VarCtx.find?_none_of_ne_all (ctx : VarCtx) (x : Identifier Unit)
    (h : ∀ entry : Identifier Unit × LMonoTy, List.Mem entry ctx → entry.1 ≠ x) :
    VarCtx.find? ctx x = none := by
  unfold VarCtx.find?
  apply Map.find?_none_of_not_mem_keys'
  intro hmem
  rw [Map.keys_eq_map_fst] at hmem
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
  exact h entry hentry heq

/-- Strings of different lengths are unequal. -/
private theorem String.ne_of_length_ne {s₁ s₂ : String} (h : s₁.length ≠ s₂.length) :
    s₁ ≠ s₂ := fun heq => absurd (congrArg String.length heq) h

/-- Any name strictly longer than every name in `ctx` is fresh in `ctx`. -/
private theorem isFresh_of_maxlen_lt (ctx : VarCtx) (s : String)
    (h : (VarCtx.names ctx).foldl (fun acc nm => max acc nm.length) 0 < s.length) :
    VarCtx.isFresh ctx ⟨s, ()⟩ = true := by
  unfold VarCtx.isFresh
  have hfind : VarCtx.find? ctx ⟨s, ()⟩ = none := by
    apply VarCtx.find?_none_of_ne_all
    intro entry hmem
    -- Identifiers are equal iff their names are; derive name inequality by length.
    have hname_ne : entry.1.name ≠ s := by
      apply String.ne_of_length_ne
      have hname_mem : entry.1.name ∈ VarCtx.names ctx :=
        List.mem_map.mpr ⟨entry, hmem, rfl⟩
      have hle := foldl_max_ge_of_mem String.length (VarCtx.names ctx) entry.1.name hname_mem 0
      omega
    intro heq
    exact hname_ne (congrArg Identifier.name heq)
  simp [hfind]

/-- `fallbackFreshName ctx` has length one greater than the longest context name. -/
private theorem fallbackFreshName_length (ctx : VarCtx) :
    (fallbackFreshName ctx).length =
      (VarCtx.names ctx).foldl (fun acc nm => max acc nm.length) 0 + 1 := by
  simp [fallbackFreshName, String.length_ofList, List.length_replicate]

/-- `dodgeKeyword` never shortens its argument: it either returns it unchanged or
    appends `_`. -/
private theorem length_le_dodgeKeyword (s : String) :
    s.length ≤ (dodgeKeyword s).length := by
  unfold dodgeKeyword
  split
  · simp [String.length_append]
  · exact Nat.le_refl _

/-- `fallbackFreshName ctx` is fresh in `ctx` because it is strictly longer
    than every name in the context. -/
private theorem fallbackFreshName_isFresh (ctx : VarCtx) :
    VarCtx.isFresh ctx ⟨fallbackFreshName ctx, ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  rw [fallbackFreshName_length]; omega

/-- `dodgeKeyword (fallbackFreshName ctx)` is also fresh: `dodgeKeyword` only ever
    lengthens the already-long-enough fallback name, so it too exceeds every
    context name in length. -/
private theorem dodgeKeyword_fallbackFreshName_isFresh (ctx : VarCtx) :
    VarCtx.isFresh ctx ⟨dodgeKeyword (fallbackFreshName ctx), ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  have h := length_le_dodgeKeyword (fallbackFreshName ctx)
  rw [fallbackFreshName_length] at h
  omega

/-- Every name in the support of `genFreshName ctx` is fresh in `ctx` (i.e. its
    identifier `⟨name, ()⟩` is absent from the context). -/
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

-- ── The indexed fresh-name family ───────────────────────────────────────

/-- Every name in a list of `(identifier, type)` pairs is at most `maxNameLen`
    long. A specialization of the polymorphic `foldl_max_ge_of_mem` at
    `f := String.length` over the mapped list of names. -/
theorem length_le_maxNameLen {l : List (Identifier Unit × LMonoTy)}
    {q : Identifier Unit × LMonoTy} (hq : q ∈ l) : q.1.name.length ≤ maxNameLen l :=
  foldl_max_ge_of_mem String.length _ q.1.name (List.mem_map.mpr ⟨q, hq, rfl⟩) 0

/-- **The family is injective in the index.** Distinct indices yield names of
    distinct lengths, hence distinct names — so `outTargets` never picks the same
    out-argument target twice. -/
theorem indexedFreshName_inj {base i j : Nat}
    (h : indexedFreshName base i = indexedFreshName base j) : i = j := by
  have hlen := congrArg String.length h
  rw [indexedFreshName_length, indexedFreshName_length] at hlen
  omega

/-- **The family avoids a list of names.** `indexedFreshName (maxNameLen l) i` is
    strictly longer than every name occurring in `l`, hence occurs in none of them. -/
theorem indexedFreshName_ne_of_mem {l : List (Identifier Unit × LMonoTy)}
    {q : Identifier Unit × LMonoTy} (hq : q ∈ l) (i : Nat) :
    q.1.name ≠ indexedFreshName (maxNameLen l) i := by
  intro heq
  have hle := length_le_maxNameLen hq
  rw [heq, indexedFreshName_length] at hle
  omega

/-- **The family is fresh for a `VarCtx`.** Taking `base := maxNameLen ctx`, every
    member of the family is absent from `ctx`. -/
theorem indexedFreshName_isFresh (ctx : VarCtx) (i : Nat) :
    VarCtx.isFresh ctx ⟨indexedFreshName (maxNameLen ctx) i, ()⟩ = true := by
  apply isFresh_of_maxlen_lt
  rw [indexedFreshName_length]
  show maxNameLen ctx < maxNameLen ctx + 1 + i
  omega

/-- No reserved Core keyword is a non-empty string of `x` characters — the
    `decide`-checkable core of `indexedFreshName_not_keyword`. -/
private theorem reservedKeyword_not_all_x : ∀ k ∈ reservedKeywordsList,
    ¬ ((k.toList.all (· == 'x')) = true ∧ 0 < String.length k) := by decide +kernel

/-- **Keyword-freedom of the indexed family.** Each member is a non-empty string of
    `x` characters, and no reserved Core keyword has that shape — so the
    out-argument names `outTargets` picks are never reserved words the Core parser
    would reject in identifier position. -/
theorem indexedFreshName_not_keyword (base i : Nat) :
    isReservedKeyword (indexedFreshName base i) = false := by
  rw [isReservedKeyword_eq_list_contains, Bool.eq_false_iff]
  intro hcontains
  refine reservedKeyword_not_all_x _ (List.mem_of_elem_eq_true hcontains) ⟨?_, ?_⟩
  · simp [indexedFreshName, String.toList_ofList]
  · rw [indexedFreshName_length]; omega

/-- **Keyword-freedom of `genFreshName`.** Every name in the support of
    `genFreshName ctx` is a non-keyword. The random candidate comes from
    `genIdentName`, whose support holds no keyword. The fallback passes through
    `dodgeKeyword`, which never returns a keyword. So the variable names
    `genInitDet` / `genInitNondet` bind in `init` commands are never reserved
    words the Core parser would reject in identifier position. -/
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

/-- The `WellKindedTy` premise of the two `init` rules, discharged for any type the
    generator can emit: `genLMonoTy` produces only generable types, and
    `SimpleTyArities C` says that `C` registers each of their constructors at its own
    arity. -/
theorem wellKindedTy_of_genLMonoTy {C : LContext CoreLParams} (hC : SimpleTyArities C)
    (tvars : List TyIdentifier) (depth : Nat) (mty : LMonoTy)
    (hmty : mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars depth)) :
    C.WellKindedTy mty :=
  genLMonoTy_mem_wellKindedTy hC ⟨_, hmty⟩

-- ── Full soundness of genCmd ─────────────────────────────────────────

/-- Predicate asserting that `genLExpr` is sound at type `τ`: every expression
    in the generator's support is well-typed. This is proved as `genLExpr_sound`
    in `HasTypeAGen.lean`; we take it as a hypothesis here. -/
def GenLExprSound (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (pctx : PolyOpCtx := []) : Prop :=
  ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ) →
    LExpr.HasTypeA (T := LExprParams') [] e τ

/-- Predicate asserting that fresh names generated by `genFreshName` do not
    appear as free variables in any expression generated by `genLExpr`.
    This is a consequence of the generator's structure (fvars are drawn from
    `fctx` via `pickFVar`, and fresh names are random strings unlikely to
    collide) but has not yet been proved as a standalone theorem. -/
def FreshNamesDisjointFromExprs (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (ctx : VarCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : Prop :=
  ∀ name, name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) →
    ∀ τ e, e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth τ) →
      (⟨name, ()⟩ : Identifier Unit) ∉ HasFvars.getFvars (P := Expression) e

/-- Full soundness of `genCmd`: every result in the generator's support produces
    a well-typed command. The output context `Γ'` satisfies `CmdHasTypeA C Γ cmd Γ'`.

    The freshness-in-Γ condition is derived from the proven `genFreshName_produces_fresh`
    and `hCorr`. The only unproven hypothesis is `hDisjoint`, which asserts that
    fresh names do not collide with free variables in generated expressions. -/
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
  · -- assert (label sampled via `genIdentName`, typing-irrelevant)
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

-- ── Full completeness of genCmd ──────────────────────────────────────

/-- Predicate asserting that `genLExpr` is complete at type `τ`: every well-typed
    expression satisfying the generator's side conditions is in the support.
    This is proved as `genLExprBase_complete` in `HasTypeAGen.lean` (which
    requires Mathlib); we take it as a hypothesis here. -/
def GenLExprComplete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : Prop :=
  ∀ τ e, LExpr.HasTypeA (T := LExprParams') [] e τ →
    e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth τ)

/-- Full completeness of `genCmd` with respect to `CmdHasTypeA`: if a command
    is well-typed and its sub-components are reachable by the respective
    sub-generators, then it is in `genCmd`'s support.

    The proof proceeds by inversion on the `CmdHasTypeA` derivation. The
    hypotheses capture what the generator requires beyond well-typedness:
    - `hExprComplete`: well-typed expressions are in `genLExpr`'s support
    - `hNameReach`: the name of any init/set target is reachable
    - `hTyReach`: the type of any init target is in `genLMonoTy`'s support
    - `hVarInCtx`: the target of any set command exists in `ctx`

    The generator fixes labels to `"l"` and metadata to `default`; the
    conclusion states that the generator produces a command with the same
    *expression* and *variable* content (but possibly different label/metadata).
    Any label in `genIdentName`'s support would do here.

    **This theorem is vacuous**, and knowingly left so for now.
    `hExprComplete : GenLExprComplete …` is unsatisfiable:
    `SpecComplete.Gaps.not_GenLExprComplete` proves it false at *every* depth, because
    an annotated free variable is well-typed against the empty context yet is
    unreachable when the scope is empty. `spec_complete` no longer takes a hypothesis
    of this shape — it uses the scope- and size-threaded `SpecComplete.ExprOk`, which
    claims reachability one expression at a time. Repairing this theorem is the same
    move: replace `hExprComplete` with a per-command condition, as
    `SpecComplete.CmdExprOk` does. Note `spec_complete` does **not** route through
    here; it inverts the `CmdHasTypeA` derivation itself. -/
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
    -- `"l"` is a legal non-keyword identifier, so it is in `genIdentName`'s support.
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

-- ── Chained typing for command sequences ────────────────────────────

/-- Well-typedness for a sequence of commands: each command is typed from one
    context to the next, forming a chain `Γ₀ → Γ₁ → ... → Γₙ`. -/
inductive CmdsHasTypeA (C : LContext CoreLParams) :
    TContext Unit → List (Cmd Expression) → TContext Unit → Prop where
  | nil : ∀ Γ, CmdsHasTypeA C Γ [] Γ
  | cons : ∀ Γ Γ' Γ'' cmd cmds,
      CmdHasTypeA C Γ cmd Γ' →
      CmdsHasTypeA C Γ' cmds Γ'' →
      CmdsHasTypeA C Γ (cmd :: cmds) Γ''

/-- A uniform soundness environment packages the hypotheses needed to prove
    `genCmd_sound` at *any* context reachable during sequence generation.
    This bundles:
    - A way to produce a `TContext` from any `VarCtx`
    - Correspondence between them
    - Expression-level soundness (context-independent)
    - Disjointness of fresh names from expression fvars at every reachable context -/
structure GenCmdSoundEnv (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (C : LContext CoreLParams) (pctx : PolyOpCtx := []) where
  /-- Produce the semantic `TContext` for any flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The correspondence holds for every context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- Expression soundness at each context's *own* free-variable projection: the
      command generators feed `ctx.toFVarCtx` into `genLExpr`, so soundness is
      needed at that derived context. -/
  exprSound : ∀ (ctx : VarCtx), GenLExprSound ctx.toFVarCtx octx tvars depth pctx
  /-- Fresh names do not appear as free variables in generated expressions. Because
      the generator draws free variables from `ctx.toFVarCtx` (whose names are
      exactly `ctx`'s) and a fresh `init` name avoids `ctx`, this now holds
      *unconditionally* at every `ctx` — see `freshNamesDisjointFromExprs_toFVarCtx`. -/
  freshDisjoint :
    ∀ (ctx : VarCtx), FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx depth pctx
  /-- The `TContext` produced for `ctx.insert x mty` agrees with the insertion into the
      `TContext` for `ctx`. This is what makes the output context of an `init` command
      match what `toTCtx` produces for the extended `VarCtx`.

      Agreement is `TContext.Equiv`, not equality: a `TContext`'s scopes are opaque
      hash maps upstream, and building one by `HMap.ofList` of an already-extended
      association list is not *structurally* the same map as inserting into the
      un-extended one. `Equiv` (pointwise `find?` agreement) is exactly what upstream's
      `init` rules ask for, so nothing is lost. -/
  toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
    TContext.Equiv (T := CoreLParams) (toTCtx (ctx.insert x mty))
      { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }

/-- Lifted soundness of `genCmd` using a `GenCmdSoundEnv`: every result in the
    generator's support produces a command typed from `env.toTCtx ctx` to
    `env.toTCtx r.outCtx`. This follows the same case analysis as `genCmd_sound`
    but additionally shows the output context matches `toTCtx` applied to the
    generator's output `VarCtx`. -/
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
  · -- assert (label sampled via `genIdentName`, typing-irrelevant)
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

/-- `genCmd` preserves *functionality* of the context: the output `VarCtx` is
    either the input `ctx` (for `set`/`assert`/`assume`/`cover`) or
    `ctx.insert x mty` for a **fresh** `x` (for `init`), and a fresh insertion
    preserves functionality (`Map.insert_functional_of_fresh`). This carries the
    `Functional` invariant along a command sequence, so `genCmds_sound` can appeal
    to it at every threaded context. -/
theorem genCmd_outCtx_functional
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) (hFun : Map.Functional ctx)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support
      (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth pctx)) :
    Map.Functional r.outCtx := by
  rw [genCmd_support_iff octx tvars immutableVars ctx depth r pctx] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det: outCtx = ctx.insert ⟨name,()⟩ mty, with name fresh in ctx
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
  · -- set_det: outCtx = ctx
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

/-- **`genCmd` keeps every type in scope well-kinded in `C`.** The only commands that
    change the scope are the two `init`s, and the type they store comes from `genLMonoTy`,
    and is therefore well-kinded wherever the `SimpleTyArities` arities are
    registered. This is the `cmd` case of the statement generators' well-kindedness
    invariant (`StrataGenerators.Stmt.WellKindedOk.ctxWK`). -/
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
  · -- init_det: the scope gains `mty`, drawn from `genLMonoTy`
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, hmty, _e, _, rfl⟩ := hr
    intro ty hty
    rcases mem_values_insert ctx ⟨name, ()⟩ mty hty with rfl | hty'
    · exact genLMonoTy_mem_wellKindedTy hC ⟨_, hmty⟩
    · exact hctx ty hty'
  · -- init_nondet: likewise
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, hmty, rfl⟩ := hr
    intro ty hty
    rcases mem_values_insert ctx ⟨name, ()⟩ mty hty with rfl | hty'
    · exact genLMonoTy_mem_wellKindedTy hC ⟨_, hmty⟩
    · exact hctx ty hty'
  · -- set_det / set_nondet / assert / assume / cover leave the scope alone
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

/-- Soundness of `genCmds`: every command sequence in the generator's support
    satisfies the chained `CmdsHasTypeA` relation.

    The proof proceeds by induction on the fuel `n`. At each step, we use
    `genCmd_sound_env` to type the head command, then invoke the inductive
    hypothesis on the tail with the updated context. The `Functional` invariant on
    the threaded context is maintained via `genCmd_outCtx_functional`. -/
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

-- ── Quick test ────────────────────────────────────────────────────────

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
