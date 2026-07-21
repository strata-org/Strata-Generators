import Basalt
import Basalt.PlausibleGen
import StrataGenerators.SetGen
import BasaltExamples.ArbNat

open RandomChoice ArbNat SetGen

inductive typ where
  | Nat : typ
  | Fun : typ → typ → typ
  deriving DecidableEq, Repr

instance : BEq typ := instBEqOfDecidableEq

/-- Terms in the STLC extended with naturals and addition -/
inductive term where
  | Const: Nat → term
  | Add: term → term → term
  | Var: Nat → term
  | App: term → term → term
  | Abs: typ → term → term
  deriving BEq, Repr

/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : List typ -> Nat -> typ -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive typing: List typ → term → typ → Prop where
| TConst : ∀ Γ n,
    typing Γ (.Const n) .Nat
| TAdd: ∀ Γ e1 e2,
    typing Γ e1 .Nat →
    typing Γ e2 .Nat →
    typing Γ (.Add e1 e2) .Nat
| TAbs: ∀ Γ e τ1 τ2,
    typing (τ1::Γ) e τ2 →
    typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
| TVar: ∀ Γ x τ,
    lookup Γ x τ →
    typing Γ (.Var x) τ
| TApp: ∀ Γ e1 e2 τ1 τ2,
    typing Γ e2 τ1 →
    typing Γ e1 (.Fun τ1 τ2) →
    typing Γ (.App e1 e2) τ2

-- Depth measures (moved before indicesOfType so it can be used there)

/-- Depth of a type. -/
def typDepth : typ → Nat
  | .Nat => 0
  | .Fun τ1 τ2 => max (typDepth τ1) (typDepth τ2) + 1

-- Helpers

/-- Indices into `Γ` that have type `τ` and satisfy `typDepth τ ≤ bound`. -/
def indicesOfType (Γ : List typ) (τ : typ) (bound : Nat) : List Nat :=
  if typDepth τ ≤ bound then go Γ 0 else []
where
  go : List typ → Nat → List Nat
    | [], _ => []
    | τ' :: Γ, i => if τ' == τ then i :: go Γ (i + 1) else go Γ (i + 1)

/-- Pick a random variable of type `τ` from `Γ`, given that at least one exists. -/
def pickVar [Gen G] (Γ : List typ) (τ : typ) (bound : Nat)
    (_h : (indicesOfType Γ τ bound).length > 0) : G term := do
  let vars := indicesOfType Γ τ bound
  let idx ← choose 0 (vars.length - 1) (by omega)
  return .Var (vars.getD idx.down 0)

/-- Generate a random type with bounded depth. -/
def genType [Gen G] : Nat → G typ
  | 0 => pure .Nat
  | depth + 1 =>
    pick
      (fun () => pure .Nat)
      (fun () => do
        let τ1 ← genType depth
        let τ2 ← genType depth
        return .Fun τ1 τ2)

/-- Generate a well-typed term of type `τ` under context `Γ`, with bounded depth.

Returns `default` (empty/failure) when `typDepth τ > depth`.
At depth 0: base cases only (Const for Nat, Var if available).
At depth+1: all forms — Const, Add, App, Abs, Var.

Note: When instantiated at a non-backtracking monad (e.g., `Plausible.Gen`), the App
case can still fail if `pick` chooses it repeatedly, exhausting the depth budget on
function types that eventually reach depth 0. A backtracking monad would recover by
trying alternative branches (Const, Abs, Var) when App fails, significantly improving
the success rate without changing the generator's support set. -/
def genTyped [Gen G] (Γ : List typ) : (depth : Nat) → (τ : typ) → G term
  | 0, .Fun _ _ => default
  | depth + 1, .Fun τ1 τ2 =>
    if typDepth (.Fun τ1 τ2) > depth + 1 then default
    else
      let vars := indicesOfType Γ (.Fun τ1 τ2) (depth + 1)
      pick
        (fun () => do  -- Abs
          let e ← genTyped (τ1 :: Γ) depth τ2
          return .Abs τ1 e)
        (fun () => pick
          (fun () =>  -- App (only when there's room for the extra Fun wrapper)
            if typDepth (.Fun τ1 τ2) + 1 ≤ depth then do
              let τ' ← genType (depth - 1)
              let e2 ← genTyped Γ depth τ'
              let e1 ← genTyped Γ depth (.Fun τ' (.Fun τ1 τ2))
              return .App e1 e2
            else do  -- fallback to Abs
              let e ← genTyped (τ1 :: Γ) depth τ2
              return .Abs τ1 e)
          (fun () =>  -- Var (or fallback to Abs)
            if hv : vars.length > 0 then
              pickVar Γ _ _ hv
            else do
              let e ← genTyped (τ1 :: Γ) depth τ2
              return .Abs τ1 e))
  | 0, .Nat =>
    let vars := indicesOfType Γ .Nat 0
    if hv : vars.length > 0 then
      pick (fun () => do let n ← Nat.arbitrary; return .Const n)
           (fun () => pickVar Γ _ _ hv)
    else do
      let n ← Nat.arbitrary
      return .Const n
  | depth + 1, .Nat =>
    let vars := indicesOfType Γ .Nat (depth + 1)
    pick
      (fun () => do  -- Const
        let n ← Nat.arbitrary
        return .Const n)
      (fun () => pick
        (fun () => do  -- Add
          let e1 ← genTyped Γ depth .Nat
          let e2 ← genTyped Γ depth .Nat
          return .Add e1 e2)
        (fun () => pick
          (fun () =>  -- App (only when depth ≥ 1)
            if depth ≥ 1 then do
              let τ1 ← genType (depth - 1)
              let e2 ← genTyped Γ depth τ1
              let e1 ← genTyped Γ depth (.Fun τ1 .Nat)
              return .App e1 e2
            else do  -- fallback to Const
              let n ← Nat.arbitrary
              return .Const n)
          (fun () =>  -- Var (or fallback to Const)
            if hv : vars.length > 0 then
              pickVar Γ _ _ hv
            else do
              let n ← Nat.arbitrary
              return .Const n)))

/-- Generate a well-typed closed term with bounded depth. -/
def term.genTerm [Gen G] (depth : Nat) : G term := do
  let τ ← genType depth
  genTyped [] depth τ

/-- The predicate characterizing the support of `genType depth`. -/
def typBounded (depth : Nat) (τ : typ) : Prop := typDepth τ ≤ depth

private theorem Nat.arbitrary_support_set : n ∈ (Nat.arbitrary (G := SetGen.Set)) := by
  induction n with
  | zero => rw [Nat.arbitrary]; simp
  | succ n ih => rw [Nat.arbitrary]; simp; exact ih

-- genType support theorem

theorem genType_support (τ : typ) (depth : Nat) :
    τ ∈ SetGen.support (genType (G := SetGen.Set) depth) ↔ typBounded depth τ := by
  induction depth generalizing τ with
  | zero =>
    simp [genType, typBounded]
    constructor
    · intro h; cases h; rfl
    · intro h; cases τ with
      | Nat => exact rfl
      | Fun => simp [typDepth] at h
  | succ n ih =>
    simp [genType, typBounded]
    constructor
    · intro h
      cases h with
      | inl h => cases h; simp [typDepth]
      | inr h =>
        obtain ⟨τ1, h1, τ2, h2, heq⟩ := h
        cases heq
        simp [typDepth]
        exact ⟨(ih τ1).mp h1, (ih τ2).mp h2⟩
    · intro h
      cases τ with
      | Nat => left; rfl
      | Fun τ1 τ2 =>
        right
        simp [typDepth] at h
        exact ⟨τ1, (ih τ1).mpr h.1, τ2, (ih τ2).mpr h.2, rfl⟩

/-- Spec for `indicesOfType.go`: `x ∈ go τ Γ i ↔ ∃ k < Γ.length, x = i + k ∧ Γ[k] = τ`. -/
private theorem indicesOfType_go_mem (τ : typ) : ∀ (Γ : List typ) (i x : Nat),
    x ∈ indicesOfType.go τ Γ i ↔ ∃ k, k < Γ.length ∧ x = i + k ∧ Γ[k]? = some τ := by
  intro Γ; induction Γ with
  | nil => simp [indicesOfType.go]
  | cons τ' Γ ih =>
    intro i x; unfold indicesOfType.go
    split
    · rename_i heq
      have hτeq : τ' = τ := beq_iff_eq.mp heq
      simp only [List.mem_cons]; rw [ih]
      constructor
      · rintro (rfl | ⟨k, hk, rfl, hget⟩)
        · exact ⟨0, by simp, by omega, by simp [hτeq]⟩
        · exact ⟨k + 1, by simp; omega, by omega, by simp [List.getElem?_cons_succ]; exact hget⟩
      · rintro ⟨k, hk, hx, hget⟩
        match k with
        | 0 => left; omega
        | k + 1 => right; exact ⟨k, by simp at hk; omega, by omega, by simp [List.getElem?_cons_succ] at hget; exact hget⟩
    · rename_i heq
      have hτne : τ' ≠ τ := by intro h; simp [h] at heq
      rw [ih]
      constructor
      · rintro ⟨k, hk, rfl, hget⟩
        exact ⟨k + 1, by simp; omega, by omega, by simp [List.getElem?_cons_succ]; exact hget⟩
      · rintro ⟨k, hk, hx, hget⟩
        match k with
        | 0 => simp at hget; exact absurd hget hτne
        | k + 1 => exact ⟨k, by simp at hk; omega, by omega, by simp [List.getElem?_cons_succ] at hget; exact hget⟩

private theorem lookup_iff_getElem? {Γ : List typ} {x : Nat} {τ : typ} :
    lookup Γ x τ ↔ Γ[x]? = some τ := by
  constructor
  · intro h; induction h with
    | Now => simp
    | Later _ _ _ _ _ ih => simpa
  · intro h; induction Γ generalizing x with
    | nil => simp at h
    | cons τ' Γ ih =>
      cases x with
      | zero => simp at h; subst h; exact .Now _ _
      | succ x => exact .Later _ _ _ _ (ih (by simp [List.getElem?_cons_succ] at h; exact h))

/-- All values in `indicesOfType Γ τ bound` correspond to valid lookups. -/
private theorem indicesOfType_mem_lookup (Γ : List typ) (τ : typ) (bound : Nat) (x : Nat)
    (h : x ∈ indicesOfType Γ τ bound) : lookup Γ x τ := by
  unfold indicesOfType at h
  split at h
  · rw [indicesOfType_go_mem] at h
    obtain ⟨k, hk, hx, hget⟩ := h
    have : x = k := by omega
    subst this; exact lookup_iff_getElem?.mpr hget
  · simp at h

/-- If `lookup Γ x τ` and `typDepth τ ≤ bound`, then `x ∈ indicesOfType Γ τ bound`. -/
private theorem lookup_mem_indicesOfType (Γ : List typ) (τ : typ) (bound : Nat) (x : Nat)
    (h : lookup Γ x τ) (hb : typDepth τ ≤ bound) : x ∈ indicesOfType Γ τ bound := by
  unfold indicesOfType
  simp [hb]
  rw [indicesOfType_go_mem]
  have hget := lookup_iff_getElem?.mp h
  have hlt : x < Γ.length := by
    rw [List.getElem?_eq_some_iff] at hget; exact hget.1
  exact ⟨x, hlt, by omega, hget⟩

private theorem pickVar_typing (Γ : List typ) (τ : typ) (bound : Nat)
    (hv : (indicesOfType Γ τ bound).length > 0)
    (e : term) (he : e ∈ SetGen.support (pickVar (G := SetGen.Set) Γ τ bound hv)) :
    typing Γ e τ := by
  unfold pickVar at he
  simp only [SetGen.mem_support_iff, Set.mem_bind, Set.mem_pure] at he
  obtain ⟨idx, ⟨_, hidx⟩, heq⟩ := he; subst heq
  apply typing.TVar; apply indicesOfType_mem_lookup
  set vars := indicesOfType Γ τ bound
  have hlt : idx.down < vars.length := by omega
  show vars.getD idx.down 0 ∈ vars
  simp [List.getD, List.getElem?_eq_getElem hlt]

/-- If `lookup Γ x τ` and `typDepth τ ≤ bound`, then `indicesOfType Γ τ bound` is non-empty. -/
private theorem lookup_indicesOfType_nonempty (Γ : List typ) (τ : typ) (bound : Nat) (x : Nat)
    (h : lookup Γ x τ) (hb : typDepth τ ≤ bound) : (indicesOfType Γ τ bound).length > 0 :=
  List.length_pos_of_mem (lookup_mem_indicesOfType Γ τ bound x h hb)

private theorem pickVar_complete (Γ : List typ) (τ : typ) (bound : Nat) (x : Nat)
    (hlook : lookup Γ x τ) (hb : typDepth τ ≤ bound)
    (hv : (indicesOfType Γ τ bound).length > 0) :
    .Var x ∈ SetGen.support (pickVar (G := SetGen.Set) Γ τ bound hv) := by
  have hmem := lookup_mem_indicesOfType Γ τ bound x hlook hb
  obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hmem
  simp only [pickVar, SetGen.mem_support_iff, Set.mem_bind, Set.mem_pure]
  have hle : idx ≤ (indicesOfType Γ τ bound).length - 1 := by omega
  refine ⟨⟨idx⟩, ⟨Nat.zero_le _, hle⟩, ?_⟩
  simp [List.getD, List.getElem?_eq_getElem hidx_lt, hidx_eq]

theorem genTyped_sound (Γ : List typ) (depth : Nat) (τ : typ) (e : term)
    (h : e ∈ SetGen.support (genTyped (G := SetGen.Set) Γ depth τ)) : typing Γ e τ := by
  induction depth generalizing Γ τ e with
  | zero =>
    cases τ with
    | Nat =>
      simp only [mem_support_iff, genTyped.eq_3, SetGen.mem_dite] at h
      cases h with
      | inl h =>
        obtain ⟨hv, h⟩ := h
        simp only [pick_mem_iff] at h
        cases h with
        | inl h =>
          simp only [Set.mem_bind, Set.mem_pure] at h
          obtain ⟨n, _, heq⟩ := h; cases heq; exact .TConst _ _
        | inr h => exact pickVar_typing Γ _ _ _ _ h
      | inr h =>
        obtain ⟨_, h⟩ := h
        simp only [Set.mem_bind, Set.mem_pure] at h
        obtain ⟨n, _, heq⟩ := h; cases heq; exact .TConst _ _
    | Fun _ _ =>
      simp only [mem_support_iff, genTyped.eq_1, bot_mem_iff] at h
  | succ n ih =>
    match τ with
    | .Fun τ1 τ2 =>
      simp only [mem_support_iff, genTyped.eq_2] at h
      split at h
      · exact absurd h (bot_mem_iff e).mp
      · simp only [pick_mem_iff, Set.mem_bind, Set.mem_pure, SetGen.mem_dite] at h
        cases h with
        | inl h => obtain ⟨b, hb, heq⟩ := h; cases heq; exact .TAbs _ _ _ _ (ih _ _ _ hb)
        | inr h => cases h with
          | inl h =>
            split at h
            · simp only [Set.mem_bind, Set.mem_pure] at h
              obtain ⟨τ', _, e2, he2, e1, he1, heq⟩ := h
              cases heq; exact .TApp _ _ _ _ _ (ih _ _ _ he2) (ih _ _ _ he1)
            · simp only [Set.mem_bind, Set.mem_pure] at h
              obtain ⟨b, hb, heq⟩ := h; cases heq; exact .TAbs _ _ _ _ (ih _ _ _ hb)
          | inr h =>
            cases h with
            | inl h => obtain ⟨_, h⟩ := h; exact pickVar_typing Γ _ _ _ _ h
            | inr h => obtain ⟨_, b, hb, heq⟩ := h; cases heq; exact .TAbs _ _ _ _ (ih _ _ _ hb)
    | .Nat =>
      simp only [mem_support_iff, genTyped.eq_4, pick_mem_iff, Set.mem_bind, Set.mem_pure, SetGen.mem_dite] at h
      cases h with
      | inl h => obtain ⟨n', _, heq⟩ := h; cases heq; exact .TConst _ _
      | inr h => cases h with
        | inl h =>
          obtain ⟨e1, he1, e2, he2, heq⟩ := h
          cases heq; exact .TAdd _ _ _ (ih _ _ _ he1) (ih _ _ _ he2)
        | inr h => cases h with
          | inl h =>
            split at h
            · simp only [Set.mem_bind, Set.mem_pure] at h
              obtain ⟨τ1, _, e2, he2, e1, he1, heq⟩ := h
              cases heq; exact .TApp _ _ _ _ _ (ih _ _ _ he2) (ih _ _ _ he1)
            · simp only [Set.mem_bind, Set.mem_pure] at h
              obtain ⟨n', _, heq⟩ := h; cases heq; exact .TConst _ _
          | inr h =>
            cases h with
            | inl h => obtain ⟨_, h⟩ := h; exact pickVar_typing Γ _ _ _ _ h
            | inr h => obtain ⟨_, n', _, heq⟩ := h; cases heq; exact .TConst _ _

-- termDepth and completeness

/-- Depth of a term relative to a context. -/
def termDepth (Γ : List typ) : term → Nat
  | .Const _ => 0
  | .Var x => typDepth (Γ.getD x .Nat)
  | .Abs τ e => max (typDepth τ) (termDepth (τ :: Γ) e) + 1
  | .Add e1 e2 => max (termDepth Γ e1) (termDepth Γ e2) + 1
  | .App e1 e2 => max (termDepth Γ e1) (termDepth Γ e2) + 1

/-- The predicate bounding term depth, parallel to `typBounded`. -/
def termBounded (Γ : List typ) (depth : Nat) (e : term) : Prop := termDepth Γ e ≤ depth

private theorem lookup_getD {Γ : List typ} {x : Nat} {τ : typ}
    (h : lookup Γ x τ) : Γ.getD x .Nat = τ := by
  have hget := lookup_iff_getElem?.mp h
  simp [List.getD, hget]

private theorem typDepth_le_termDepth_of_typing {Γ : List typ} {e : term} {τ : typ}
    (h : typing Γ e τ) : typDepth τ ≤ termDepth Γ e := by
  induction h with
  | TConst => simp [typDepth, termDepth]
  | TAdd _ _ _ _ _ _ _ => simp [typDepth, termDepth]
  | TAbs _ _ _ _ _ ih => simp [termDepth, typDepth]; omega
  | TVar _ _ _ hlook =>
    simp only [termDepth]
    have h := lookup_iff_getElem?.mp hlook
    simp [h]
  | TApp _ _ _ _ _ _ _ _ ih2 => simp [termDepth, typDepth] at ih2 ⊢; omega

private theorem genTyped_complete (Γ : List typ) (e : term) (τ : typ) (depth : Nat)
    (htyp : typing Γ e τ) (hτ : typDepth τ ≤ depth) (he : termDepth Γ e ≤ depth) :
    e ∈ SetGen.support (genTyped (G := SetGen.Set) Γ depth τ) := by
  induction htyp generalizing depth with
  | TConst Γ n =>
    cases depth with
    | zero =>
      simp only [mem_support_iff, genTyped.eq_3, SetGen.mem_dite]
      by_cases hv : (indicesOfType Γ .Nat 0).length > 0
      · left; refine ⟨hv, ?_⟩
        simp only [pick_mem_iff, Set.mem_bind, Set.mem_pure]
        left; exact ⟨n, Nat.arbitrary_support_set, rfl⟩
      · apply Or.inr; refine ⟨by omega, ?_⟩
        simp only [Set.mem_bind, Set.mem_pure]
        exact ⟨n, Nat.arbitrary_support_set, rfl⟩
    | succ s =>
      simp only [mem_support_iff, genTyped.eq_4, pick_mem_iff, Set.mem_bind, Set.mem_pure]
      left; exact ⟨n, Nat.arbitrary_support_set, rfl⟩
  | TAdd Γ e1 e2 _ _ ih1 ih2 =>
    cases depth with
    | zero => simp [termDepth] at he
    | succ s =>
      simp only [mem_support_iff, genTyped.eq_4, pick_mem_iff, Set.mem_bind, Set.mem_pure]
      right; left
      have hs1 : termDepth Γ e1 ≤ s := by simp [termDepth] at he; omega
      have hs2 : termDepth Γ e2 ≤ s := by simp [termDepth] at he; omega
      exact ⟨e1, ih1 s (by simp [typDepth]) hs1, e2, ih2 s (by simp [typDepth]) hs2, rfl⟩
  | TAbs Γ e τ1 τ2 _ ih =>
    cases depth with
    | zero => simp [typDepth] at hτ
    | succ s =>
      simp only [mem_support_iff, genTyped.eq_2]
      have hguard : ¬(typDepth (.Fun τ1 τ2) > s + 1) := by omega
      simp only [hguard, ↓reduceIte, pick_mem_iff, Set.mem_bind, Set.mem_pure]
      left
      have hs_e : termDepth (τ1 :: Γ) e ≤ s := by simp [termDepth] at he; omega
      have hs_τ2 : typDepth τ2 ≤ s := by simp [typDepth] at hτ; omega
      exact ⟨e, ih s hs_τ2 hs_e, rfl⟩
  | TVar Γ x τ hlook =>
    cases depth with
    | zero =>
      cases τ with
      | Nat =>
        simp only [mem_support_iff, genTyped.eq_3, SetGen.mem_dite]
        have hv := lookup_indicesOfType_nonempty Γ .Nat 0 x hlook (by simp [typDepth])
        left; refine ⟨hv, ?_⟩
        simp only [pick_mem_iff]
        right; exact pickVar_complete Γ .Nat 0 x hlook (by simp [typDepth]) _
      | Fun τ1 τ2 => simp [typDepth] at hτ
    | succ s =>
      cases τ with
      | Nat =>
        simp only [mem_support_iff, genTyped.eq_4, pick_mem_iff, Set.mem_bind, Set.mem_pure, SetGen.mem_dite]
        right; right; right; left
        have hv := lookup_indicesOfType_nonempty Γ .Nat (s + 1) x hlook (by simp [typDepth])
        exact ⟨hv, pickVar_complete Γ .Nat (s + 1) x hlook (by simp [typDepth]) _⟩
      | Fun τ1 τ2 =>
        simp only [mem_support_iff, genTyped.eq_2]
        have hguard : ¬(typDepth (.Fun τ1 τ2) > s + 1) := by omega
        simp only [hguard, ↓reduceIte, pick_mem_iff, Set.mem_bind, Set.mem_pure, SetGen.mem_dite]
        right; right; left
        have hv := lookup_indicesOfType_nonempty Γ (.Fun τ1 τ2) (s + 1) x hlook hτ
        exact ⟨hv, pickVar_complete Γ (.Fun τ1 τ2) (s + 1) x hlook hτ _⟩
  | TApp Γ e1 e2 τ1 τ2 htyp2 htyp1 ih1 ih2 =>
    cases depth with
    | zero => simp [termDepth] at he
    | succ s =>
      have hs1 : termDepth Γ e1 ≤ s := by simp [termDepth] at he; omega
      have hs2 : termDepth Γ e2 ≤ s := by simp [termDepth] at he; omega
      have hτ1_depth : typDepth τ1 ≤ s - 1 := by
        have h := typDepth_le_termDepth_of_typing htyp1
        simp [typDepth] at h; omega
      have hFun_depth : typDepth (.Fun τ1 τ2) ≤ s := by
        have h := typDepth_le_termDepth_of_typing htyp1; omega
      cases τ2 with
      | Nat =>
        simp only [mem_support_iff, genTyped.eq_4, pick_mem_iff, Set.mem_bind, Set.mem_pure]
        right; right; left
        have hs_ge : s ≥ 1 := by simp [typDepth] at hFun_depth; omega
        simp only [hs_ge, ↓reduceIte]
        refine ⟨τ1, (genType_support τ1 (s - 1)).mpr hτ1_depth, e2, ih1 s ?_ hs2, e1, ih2 s ?_ hs1, rfl⟩
        · exact Nat.le_trans hτ1_depth (by omega)
        · exact hFun_depth
      | Fun τ2a τ2b =>
        simp only [mem_support_iff, genTyped.eq_2]
        have hguard : ¬(typDepth (.Fun τ2a τ2b) > s + 1) := by omega
        simp only [hguard, ↓reduceIte, pick_mem_iff, Set.mem_bind, Set.mem_pure]
        right; left
        have happ_guard : typDepth (.Fun τ2a τ2b) + 1 ≤ s := by
          have h := hFun_depth; simp [typDepth] at h ⊢; omega
        simp only [happ_guard, ↓reduceIte]
        refine ⟨τ1, (genType_support τ1 (s - 1)).mpr hτ1_depth, e2, ih1 s ?_ hs2, e1, ih2 s ?_ hs1, rfl⟩
        · exact Nat.le_trans hτ1_depth (by omega)
        · exact hFun_depth

-- SetGen.IsSoundAndComplete instances

instance {depth : Nat} : SetGen.IsSoundAndComplete (genType (G := SetGen.Set) depth) (typBounded depth) where
  support_iff τ := genType_support τ _

private theorem pickVar_termDepth_bound (Γ : List typ) (τ : typ) (bound : Nat)
    (hv : (indicesOfType Γ τ bound).length > 0)
    (e : term) (he : e ∈ SetGen.support (pickVar (G := SetGen.Set) Γ τ bound hv)) :
    termDepth Γ e ≤ bound := by
  unfold pickVar at he
  simp only [SetGen.mem_support_iff, Set.mem_bind, Set.mem_pure] at he
  obtain ⟨idx, ⟨_, hidx⟩, heq⟩ := he; subst heq
  show typDepth (Γ.getD ((indicesOfType Γ τ bound).getD idx.down 0) .Nat) ≤ bound
  have hlt : idx.down < (indicesOfType Γ τ bound).length := by omega
  have hmem : (indicesOfType Γ τ bound).getD idx.down 0 ∈ indicesOfType Γ τ bound := by
    simp [List.getD, List.getElem?_eq_getElem hlt]
  have hlook := indicesOfType_mem_lookup Γ τ bound _ hmem
  rw [lookup_getD hlook]
  unfold indicesOfType at hv; split at hv
  · assumption
  · simp at hv

theorem genTyped_termDepth_bound (Γ : List typ) (depth : Nat) (τ : typ) (e : term)
    (h : e ∈ SetGen.support (genTyped (G := SetGen.Set) Γ depth τ)) : termDepth Γ e ≤ depth := by
  induction depth generalizing Γ τ e with
  | zero =>
    cases τ with
    | Fun _ _ => simp only [mem_support_iff, genTyped.eq_1, bot_mem_iff] at h
    | Nat =>
      simp only [mem_support_iff, genTyped.eq_3, SetGen.mem_dite] at h
      cases h with
      | inl h =>
        obtain ⟨hv, h⟩ := h
        simp only [pick_mem_iff] at h
        cases h with
        | inl h =>
          simp only [Set.mem_bind, Set.mem_pure] at h
          obtain ⟨n, _, heq⟩ := h; cases heq; simp [termDepth]
        | inr h => exact pickVar_termDepth_bound Γ _ _ _ _ h
      | inr h =>
        obtain ⟨_, h⟩ := h
        simp only [Set.mem_bind, Set.mem_pure] at h
        obtain ⟨n, _, heq⟩ := h; cases heq; simp [termDepth]
  | succ n ih =>
    match τ with
    | .Fun τ1 τ2 =>
      simp only [mem_support_iff, genTyped.eq_2] at h
      split at h
      · exact absurd h (bot_mem_iff e).mp
      · rename_i hguard
        push Not at hguard
        simp only [pick_mem_iff, Set.mem_bind, Set.mem_pure, SetGen.mem_dite] at h
        cases h with
        | inl h =>
          obtain ⟨b, hb, heq⟩ := h; cases heq
          simp [termDepth]
          constructor
          · simp [typDepth] at hguard; omega
          · exact ih _ _ _ hb
        | inr h => cases h with
          | inl h =>
            split at h
            · simp only [Set.mem_bind, Set.mem_pure] at h
              obtain ⟨τ', _, e2, he2, e1, he1, heq⟩ := h
              cases heq; simp [termDepth]
              exact ⟨ih _ _ _ he1, ih _ _ _ he2⟩
            · simp only [Set.mem_bind, Set.mem_pure] at h
              obtain ⟨b, hb, heq⟩ := h; cases heq
              simp [termDepth]
              constructor
              · simp [typDepth] at hguard; omega
              · exact ih _ _ _ hb
          | inr h =>
            cases h with
            | inl h =>
              obtain ⟨_, h⟩ := h
              exact pickVar_termDepth_bound Γ _ _ _ _ h
            | inr h =>
              obtain ⟨_, b, hb, heq⟩ := h; cases heq
              simp [termDepth]
              constructor
              · simp [typDepth] at hguard; omega
              · exact ih _ _ _ hb
    | .Nat =>
      simp only [mem_support_iff, genTyped.eq_4, pick_mem_iff, Set.mem_bind, Set.mem_pure, SetGen.mem_dite] at h
      cases h with
      | inl h =>
        obtain ⟨n', _, heq⟩ := h; cases heq; simp [termDepth]
      | inr h => cases h with
        | inl h =>
          obtain ⟨e1, he1, e2, he2, heq⟩ := h
          cases heq; simp [termDepth]
          exact ⟨ih _ _ _ he1, ih _ _ _ he2⟩
        | inr h => cases h with
          | inl h =>
            split at h
            · simp only [Set.mem_bind, Set.mem_pure] at h
              obtain ⟨τ1, _, e2, he2, e1, he1, heq⟩ := h
              cases heq; simp [termDepth]
              exact ⟨ih _ _ _ he1, ih _ _ _ he2⟩
            · simp only [Set.mem_bind, Set.mem_pure] at h
              obtain ⟨n', _, heq⟩ := h; cases heq; simp [termDepth]
          | inr h =>
            cases h with
            | inl h =>
              obtain ⟨_, h⟩ := h
              exact pickVar_termDepth_bound Γ _ _ _ _ h
            | inr h =>
              obtain ⟨_, n', _, heq⟩ := h; cases heq; simp [termDepth]

/-- The predicate characterizing the support of `genTyped Γ depth τ`. -/
def typedBounded (Γ : List typ) (depth : Nat) (τ : typ) (e : term) : Prop :=
  typing Γ e τ ∧ termBounded Γ depth e

theorem genTyped_support (Γ : List typ) (depth : Nat) (τ : typ) (e : term) :
    e ∈ SetGen.support (genTyped (G := SetGen.Set) Γ depth τ) ↔ typedBounded Γ depth τ e := by
  simp only [typedBounded, termBounded]
  constructor
  · intro h
    exact ⟨genTyped_sound Γ depth τ e h, genTyped_termDepth_bound Γ depth τ e h⟩
  · intro ⟨htyp, hdepth⟩
    exact genTyped_complete Γ e τ depth htyp
      (Nat.le_trans (typDepth_le_termDepth_of_typing htyp) hdepth) hdepth

instance {Γ : List typ} {depth : Nat} {τ : typ} :
    SetGen.IsSoundAndComplete (genTyped (G := SetGen.Set) Γ depth τ) (typedBounded Γ depth τ) where
  support_iff e := genTyped_support Γ depth τ e

-- Demonstrate running the same generator via Plausible's Gen
section PlausibleGenDemo
open Basalt.PlausibleGen

/-- Run a generator, returning `none` on failure and `some` on success. -/
def tryGen (g : Plausible.Gen α) (size : Nat) : IO (Option α) :=
  try pure (some (← Plausible.Gen.run g size))
  catch _ => pure none

#guard_msgs(drop all) in
#eval (for _ in [0:20] do
  IO.println <| repr (← tryGen (term.genTerm 3) 10) : IO Unit)

#guard_msgs(drop info) in
#eval (for _ in [0:10] do
  IO.println <| repr (← Plausible.Gen.run (genType (G := Plausible.Gen) 2) 10) : IO Unit)

end PlausibleGenDemo
