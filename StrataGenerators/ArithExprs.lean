import Basalt
import Basalt.PlausibleGen
import StrataGenerators.SetGen
import BasaltExamples.ArbNat

open RandomChoice ArbNat SetGen Set

-- A simple language of arithmetic expressions
-- (from Chapter 8 of *Types & Programming Languages*)
inductive Expr
  | True
  | False
  | IfThenElse : Expr → Expr → Expr → Expr
  | Zero
  | Succ : Expr → Expr
  | Pred : Expr → Expr
  | IsZero : Expr → Expr
  deriving Repr, BEq

-- Types are either Bool or Nat
inductive Ty
  | Bool
  | Nat
  deriving Repr, BEq

-- Typing relation: `HasType e τ` means `· ⊢ e : τ`
inductive HasType : Expr → Ty → Prop where
  | TTrue : HasType .True .Bool
  | TFalse : HasType .False .Bool
  | TZero : HasType .Zero .Nat
  | TIf (e1 e2 e3 : Expr) (τ : Ty) :
      HasType e1 .Bool →
      HasType e2 τ →
      HasType e3 τ →
      HasType (.IfThenElse e1 e2 e3) τ
  | TSucc (e : Expr) :
      HasType e .Nat → HasType (.Succ e) .Nat
  | TPred (e : Expr) :
      HasType e .Nat → HasType (.Pred e) .Nat
  | TIsZero (e : Expr) :
      HasType e .Nat → HasType (.IsZero e) .Bool

-- Generates a random well-typed arithmetic expr
-- of a particular `size` at type `τ`
@[simp]
def genExpr [Gen G] (size : ℕ) (τ : Ty) : G Expr :=
  match size, τ with
  | 0, .Nat => return .Zero
  | 0, .Bool => pick (fun _ => return .True) (fun _ => return .False)
  | size' + 1, .Nat =>
    pick
      (fun _ => return .Zero)
      (fun _ =>
        pick
          (fun _ => do
            -- Generate `Succ e'` for some `e'`
            let e ← genExpr size' .Nat
            return .Succ e)
          (fun _ =>
            pick
              (fun _ => do
                -- Generate `Pred e'` for some `e'`
                let e ← genExpr size' .Nat
                return .Pred e)
              (fun _ => do
                -- Generate an `IfThenElse`
                let e1 ← genExpr size' .Bool
                let e2 ← genExpr size' .Nat
                let e3 ← genExpr size' .Nat
                return .IfThenElse e1 e2 e3)))
  | size' + 1, .Bool =>
    pick
      (fun _ => return .True)
      (fun _ =>
        pick
          (fun _ => return .False)
          (fun _ =>
            pick
              (fun _ => do
                let e ← genExpr size' .Nat
                return .IsZero e)
              (fun _ => do
                let e1 ← genExpr size' .Bool
                let e2 ← genExpr size' .Bool
                let e3 ← genExpr size' .Bool
                return .IfThenElse e1 e2 e3)))

-- Soundness: `genExpr` only produces well-typed arithmetic exprs
theorem genExpr_sound : ∀ (size : ℕ) (τ : Ty) (e : Expr),
  e ∈ SetGen.support (genExpr size τ) → HasType e τ := by
  intros size τ e H
  induction size generalizing τ e with
  | zero =>
    cases τ with
    | Bool =>
      simp only [genExpr, mem_support_pick_iff, mem_support_pure_iff] at H
      rcases H with rfl | rfl <;> constructor
    | Nat =>
      simp only [genExpr, mem_support_pure_iff] at H
      subst H
      constructor
  | succ size' IH =>
    cases τ with
    | Bool =>
      simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H
      rcases H with rfl | rfl | ⟨ e', He', rfl ⟩ | ⟨ e1, He1, e2, He2, e3, He3, rfl ⟩
      . -- HasType True Bool
        constructor
      . -- HasType False Bool
        constructor
      . -- HasType (IsZero e') Bool
        constructor
        exact IH _ _ He'
      . -- HasType (IfThenElse e1 e2 e3) Bool
        constructor <;> (apply IH; assumption)
    | Nat =>
      simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H
      rcases H with rfl | ⟨ e', He', rfl ⟩ | ⟨ e', He', rfl ⟩ | ⟨ e1, He1, e2, He2, e3, He3, rfl ⟩
      . -- HasType Zero Nat
        constructor
      . -- HasType (Succ e') Nat
        constructor
        exact IH _ _ He'
      . -- HasType (Pred e') Nat
        constructor
        exact IH _ _ He'
      . -- HasType (IfThenElse e1 e2 e3) Nat
        constructor <;> (apply IH; assumption)

-- Helper lemma: if `genExpr` can produce some `e` at a particular `size`,
-- it can also produce `e` if we increment `size`
lemma genExpr_monotone_succ : ∀ (size : ℕ) (τ : Ty) (e : Expr),
    e ∈ SetGen.support (genExpr size τ) → e ∈ SetGen.support (genExpr (size + 1) τ) := by
  intro size τ e H
  induction size generalizing τ e with
  | zero =>
    cases τ with
    | Bool =>
      simp only [genExpr, mem_support_pick_iff, mem_support_pure_iff] at *
      rcases H with rfl | rfl
      · left; rfl
      · right; left; rfl
    | Nat =>
      simp only [genExpr, mem_support_pick_iff, mem_support_pure_iff] at *
      subst H
      left; rfl
  | succ size' IH =>
    cases τ with
    | Bool =>
      simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H
      rcases H with rfl | rfl | ⟨e', He', rfl⟩ | ⟨e1, He1, e2, He2, e3, He3, rfl⟩
      · -- True
        dsimp only [genExpr]
        rw [mem_support_pick_iff]; left
        rw [mem_support_pure_iff]
      · -- False
        dsimp only [genExpr]
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; left
        rw [mem_support_pure_iff]
      · -- IsZero e'
        dsimp only [genExpr]
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; left
        rw [mem_support_bind_iff]
        refine ⟨e', IH _ _ He', ?_⟩
        rw [mem_support_pure_iff]
      · -- IfThenElse e1 e2 e3
        dsimp only [genExpr]
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; right
        rw [mem_support_bind_iff]
        refine ⟨e1, IH _ _ He1, ?_⟩
        rw [mem_support_bind_iff]
        refine ⟨e2, IH _ _ He2, ?_⟩
        rw [mem_support_bind_iff]
        refine ⟨e3, IH _ _ He3, ?_⟩
        rw [mem_support_pure_iff]
    | Nat =>
      simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H
      rcases H with rfl | ⟨e', He', rfl⟩ | ⟨e', He', rfl⟩ | ⟨e1, He1, e2, He2, e3, He3, rfl⟩
      · -- Zero
        dsimp only [genExpr]
        rw [mem_support_pick_iff]; left
        rw [mem_support_pure_iff]
      · -- Succ e'
        dsimp only [genExpr]
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; left
        rw [mem_support_bind_iff]
        refine ⟨e', IH _ _ He', ?_⟩
        rw [mem_support_pure_iff]
      · -- Pred e'
        dsimp only [genExpr]
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; left
        rw [mem_support_bind_iff]
        refine ⟨e', IH _ _ He', ?_⟩
        rw [mem_support_pure_iff]
      · -- IfThenElse e1 e2 e3
        dsimp only [genExpr]
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; right
        rw [mem_support_pick_iff]; right
        rw [mem_support_bind_iff]
        refine ⟨e1, IH _ _ He1, ?_⟩
        rw [mem_support_bind_iff]
        refine ⟨e2, IH _ _ He2, ?_⟩
        rw [mem_support_bind_iff]
        refine ⟨e3, IH _ _ He3, ?_⟩
        rw [mem_support_pure_iff]

-- Helper lemma: `genExpr` is monotonic in its `size` parameter (necessary for completeness proof)
lemma genExpr_monotone : ∀ (size1 size2 : ℕ) (τ : Ty) (e : Expr),
  size1 ≤ size2 → e ∈ SetGen.support (genExpr size1 τ) → e ∈ SetGen.support (genExpr size2 τ) := by
  intro size1 size2 τ e Hsize Hsupport
  -- From soundness, it follows that `e` is well-typed at type `τ`
  induction Hsize with
  | refl => assumption
  | step _ IH =>
    apply genExpr_monotone_succ
    assumption

-- Completeness: for all well-typed arithmetic exprs, there exists some `size` such that `genExpr`
-- is capable of generating that expr
theorem genExpr_complete : ∀ (τ : Ty) (e : Expr),
    HasType e τ → ∃ size, e ∈ SetGen.support (genExpr size τ) := by
  intro τ e H
  induction H with
  | TTrue =>
    exists .zero
    dsimp [genExpr]
    rw [mem_support_pick_iff]
    left
    rw [mem_support_pure_iff]
  | TFalse =>
    exists .zero
    dsimp [genExpr]
    rw [mem_support_pick_iff]
    right
    rw [mem_support_pure_iff]
  | TZero =>
    exists 0
  | TSucc e' He' IH =>
    obtain ⟨ size', He' ⟩ := IH
    exists size' + 1
    simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff]
    right; left
    exists e'
  | TPred e' He' IH =>
    obtain ⟨ size', He' ⟩ := IH
    exists size' + 1
    simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff]
    right; right; left
    exists e'
  | TIsZero e' He' IH =>
    obtain ⟨ size', He' ⟩ := IH
    exists size' + 1
    simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff]
    right; right; left
    exists e'
  | TIf e1 e2 e3 τ H1 H2 H3 IH1 IH2 IH3 =>
    obtain ⟨ s1, IH1 ⟩ := IH1
    obtain ⟨ s2, IH2 ⟩ := IH2
    obtain ⟨ s3, IH3 ⟩ := IH3
    let maxSize := max s1 (max s2 s3)
    exists (maxSize + 1)
    have h1 : s1 ≤ maxSize := by omega
    have h2 : s2 ≤ maxSize := by omega
    have h3 : s3 ≤ maxSize := by omega
    cases τ with
    | Bool =>
      simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff]
      right; right; right
      exists e1
      constructor
      . -- e1 ∈ support (genExpr maxSize Ty.Bool)
        apply (genExpr_monotone s1) <;> assumption
      . exists e2
        constructor
        . -- e2 ∈ support (genExpr maxSize Ty.Bool)
          apply (genExpr_monotone s2) <;> assumption
        . exists e3
          constructor
          . -- e3 ∈ support (genExpr maxSize Ty.Bool)
            apply (genExpr_monotone s3) <;> assumption
          . rfl
    | Nat =>
      simp only [genExpr, mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff]
      right; right; right
      exists e1
      constructor
      . -- e1 ∈ support (genExpr maxSize Ty.Bool)
        apply (genExpr_monotone s1) <;> assumption
      . exists e2
        constructor
        . -- e2 ∈ support (genExpr maxSize Ty.Bool)
          apply (genExpr_monotone s2) <;> assumption
        . exists e3
          constructor
          . -- e3 ∈ support (genExpr maxSize Ty.Bool)
            apply (genExpr_monotone s3) <;> assumption
          . rfl




-------------------



-- Variant of the monotonicity helper lemma above that uses the `fun_induction` tactic
lemma genExpr_monotone_succ' : ∀ (size : ℕ) (τ : Ty) (e : Expr),
    e ∈ SetGen.support (genExpr size τ) → e ∈ SetGen.support (genExpr (size + 1) τ) := by
  intro size τ
  fun_induction genExpr (G := SetGen.Set) size τ with
  | case1 =>
    -- size = 0, Nat
    intro e H
    simp only [mem_support_pure_iff] at H
    subst H
    dsimp only [genExpr]
    rw [mem_support_pick_iff]; left
    rw [mem_support_pure_iff]
  | case2 =>
    -- size = 0, Bool
    intro e H
    simp only [mem_support_pick_iff, mem_support_pure_iff] at H
    dsimp only [genExpr]
    rw [mem_support_pick_iff]
    rcases H with rfl | rfl
    · -- True
      left; rw [mem_support_pure_iff]
    · -- False
      right; rw [mem_support_pick_iff]; left; rw [mem_support_pure_iff]
  | case3 size' ih_nat ih_bool =>
    -- size = succ size', Nat
    intro e H
    simp only [mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H
    rcases H with rfl | ⟨e', He', rfl⟩ | ⟨e', He', rfl⟩ | ⟨e1, He1, e2, He2, e3, He3, rfl⟩
    · -- Zero
      dsimp only [genExpr]
      rw [mem_support_pick_iff]; left
      rw [mem_support_pure_iff]
    · -- Succ e'
      dsimp only [genExpr]
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; left
      rw [mem_support_bind_iff]
      refine ⟨e', ih_nat _ He', ?_⟩
      rw [mem_support_pure_iff]
    · -- Pred e'
      dsimp only [genExpr]
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; left
      rw [mem_support_bind_iff]
      refine ⟨e', ih_nat _ He', ?_⟩
      rw [mem_support_pure_iff]
    · -- IfThenElse e1 e2 e3
      dsimp only [genExpr]
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; right
      rw [mem_support_bind_iff]
      refine ⟨e1, ih_bool _ He1, ?_⟩
      rw [mem_support_bind_iff]
      refine ⟨e2, ih_nat _ He2, ?_⟩
      rw [mem_support_bind_iff]
      refine ⟨e3, ih_nat _ He3, ?_⟩
      rw [mem_support_pure_iff]
  | case4 size' ih_nat ih_bool =>
    -- size = succ size', Bool
    intro e H
    simp only [mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H
    rcases H with rfl | rfl | ⟨e', He', rfl⟩ | ⟨e1, He1, e2, He2, e3, He3, rfl⟩
    · -- True
      dsimp only [genExpr]
      rw [mem_support_pick_iff]; left
      rw [mem_support_pure_iff]
    · -- False
      dsimp only [genExpr]
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; left
      rw [mem_support_pure_iff]
    · -- IsZero e'
      dsimp only [genExpr]
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; left
      rw [mem_support_bind_iff]
      refine ⟨e', ih_nat _ He', ?_⟩
      rw [mem_support_pure_iff]
    · -- IfThenElse e1 e2 e3
      dsimp only [genExpr]
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; right
      rw [mem_support_pick_iff]; right
      rw [mem_support_bind_iff]
      refine ⟨e1, ih_bool _ He1, ?_⟩
      rw [mem_support_bind_iff]
      refine ⟨e2, ih_bool _ He2, ?_⟩
      rw [mem_support_bind_iff]
      refine ⟨e3, ih_bool _ He3, ?_⟩
      rw [mem_support_pure_iff]

-- Variant of the soundness proof above that uses the `fun_induction` tactic introduced in Lean 4.80
theorem genExpr_sound' : ∀ (size : ℕ) (τ : Ty) (e : Expr),
  e ∈ SetGen.support (genExpr size τ) → HasType e τ := by
  intro size τ
  fun_induction genExpr (G := SetGen.Set) size τ with
  | case1 =>
    -- size = 0, τ = Bool
    intro e H
    simp only [mem_support_pure_iff] at H
    subst H
    constructor
  | case2 =>
    -- size = 0, τ = Nat
    intro e H
    simp only [mem_support_pick_iff, mem_support_pure_iff] at H
    rcases H with rfl | rfl <;> constructor
  | case3 size' ih_nat ih_bool =>
    -- size = succ size', τ = Nat
    intro e H
    simp only [mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H
    rcases H with rfl | ⟨e', He', rfl⟩ | ⟨e', He', rfl⟩ | ⟨e1, He1, e2, He2, e3, He3, rfl⟩
    · -- HasType Zero Nat
      constructor
    · -- HasType (Succ e') Nat
      constructor
      apply ih_nat
      assumption
    · -- HasType (Pred e') Nat
      constructor
      apply ih_nat
      assumption
    · -- HasType (IfThenElse e1 e2 e3) Nat
      constructor
      · apply ih_bool
        assumption
      · apply ih_nat
        assumption
      · apply ih_nat
        assumption
  | case4 size' ih_nat ih_bool =>
    -- size = succ size', τ = Bool
    intro e H
    simp only [mem_support_pick_iff, mem_support_bind_iff, mem_support_pure_iff] at H
    rcases H with rfl | rfl | ⟨e', He', rfl⟩ | ⟨e1, He1, e2, He2, e3, He3, rfl⟩
    · -- HasType True Bool
      constructor
    · -- HasType False Bool
      constructor
    · -- HasType (IsZero e') Bool
      constructor
      apply ih_nat
      assumption
    · -- HasType (IThenElse e1 e2 e3) Bool
      constructor <;> apply ih_bool <;> assumption
