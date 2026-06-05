import Basalt
import Basalt.PlausibleGen
import StrataGenerators.SetGen
import Basalt.Examples.ArbNat

open RandomChoice ArbNat SetGen Set

-- Arithmetic expressions from Chapter 8 of TAPL
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

-- Typing relation
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

-- Generates a random type
def genTy [Gen G] : G Ty :=
  pick (fun _ => return .Nat) (fun _ => return .Bool)

-- Generates a random well-typed arithmetic expr
def genExpr [Gen G] (size : ℕ) (τ : Ty) : G Expr :=
  match size, τ with
  | 0, .Nat => return .Zero
  | 0, .Bool => pick (fun _ => return .True) (fun _ => return .False)
  | size' + 1, .Nat =>
    pick
      (fun _ => do
        let e ← genExpr size' .Nat
        return .Succ e)
      (fun _ =>
        pick
          (fun _ => do
            let e ← genExpr size' .Nat
            return .Pred e)
          (fun _ => do
            let e1 ← genExpr size' .Bool
            let e2 ← genExpr size' .Nat
            let e3 ← genExpr size' .Nat
            return .IfThenElse e1 e2 e3))
  | size' + 1, .Bool =>
    pick
      (fun _ => do
        let e ← genExpr size' .Nat
        return .IsZero e)
      (fun _ => do
        let e1 ← genExpr size' .Bool
        let e2 ← genExpr size' .Bool
        let e3 ← genExpr size' .Bool
        return .IfThenElse e1 e2 e3)

-- genExpr produces well-typed arithmetic exprs
theorem genExpr_sound : ∀ (size : ℕ) (τ : Ty) (e : Expr),
  e ∈ SetGen.support (genExpr size τ) → HasType e τ := by
  intros size τ e H
  induction size generalizing τ e with
  | zero =>
    cases τ with
    | Bool =>
      dsimp [genExpr] at H
      rw [mem_support_pick_iff] at H
      cases H with
      | inl Htrue =>
        -- e ∈ support (pure .True)
        rw [mem_support_pure_iff] at Htrue
        rw [Htrue]
        constructor
      | inr HFalse =>
        -- e ∈ support (pure .False)
        rw [mem_support_pure_iff] at HFalse
        rw [HFalse]
        constructor
    | Nat =>
      dsimp [genExpr] at H
      rw [SetGen.Set.mem_singleton_iff] at H
      rw [H]
      constructor
  | succ size' ih =>
    cases τ with
    | Bool =>
      dsimp [genExpr] at H
      rw [mem_support_pick_iff] at H
      cases H with
      | inl HIsZero =>
        rw [mem_support_bind_iff] at HIsZero
        obtain ⟨ e', ⟨ He', He ⟩ ⟩ := HIsZero
        rw [mem_support_pure_iff] at He
        rw [He]
        constructor
        apply ih
        assumption
      | inr HIf =>
        rw [mem_support_bind_iff] at HIf
        obtain ⟨ e1, ⟨ He1, H ⟩ ⟩ := HIf
        rw [mem_support_bind_iff] at H
        obtain ⟨ e2, ⟨ He2, H ⟩ ⟩ := H
        rw [mem_support_bind_iff] at H
        obtain ⟨ e3, ⟨ He3, H ⟩ ⟩ := H
        rw [mem_support_pure_iff] at H
        rw [H]
        constructor
        . -- HasType e1 Bool
          apply ih
          assumption
        . -- HasType e2 Bool
          apply ih
          assumption
        . -- HasType e3 Bool
          apply ih
          assumption
    | Nat =>
      dsimp [genExpr] at H
      rw [mem_support_pick_iff] at H
      cases H with
      | inl HSucc =>
        rw [mem_support_bind_iff] at HSucc
        obtain ⟨ e', ⟨ He', He ⟩ ⟩ := HSucc
        rw [mem_support_pure_iff] at He
        rw [He]
        constructor
        apply ih
        assumption
      | inr H =>
        rw [mem_support_pick_iff] at H
        cases H with
        | inl HPred =>
          rw [mem_support_bind_iff] at HPred
          obtain ⟨ e', ⟨ He', He ⟩ ⟩ := HPred
          rw [mem_support_pure_iff] at He
          rw [He]
          constructor
          apply ih
          assumption
        | inr HIf =>
          rw [mem_support_bind_iff] at HIf
          obtain ⟨ e1, ⟨ He1, H ⟩ ⟩ := HIf
          rw [mem_support_bind_iff] at H
          obtain ⟨ e2, ⟨ He2, H ⟩ ⟩ := H
          rw [mem_support_bind_iff] at H
          obtain ⟨ e3, ⟨ He3, H ⟩ ⟩ := H
          rw [mem_support_pure_iff] at H
          rw [H]
          constructor
          . -- HasType e1 Bool
            apply ih
            assumption
          . -- HasType e2 Nat
            apply ih
            assumption
          . -- HasType e3 Nat
            apply ih
            assumption
