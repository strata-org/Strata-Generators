/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein

Vendored from https://github.com/hgoldstein95/basalt (SetGen branch, not yet on `main`).
-/

/-!
# Self-contained Set definitions for SetGen

This file provides a minimal `Set` type and monad instance, avoiding a dependency on Mathlib.
Everything lives in the `SetGen` namespace to avoid collisions when Mathlib is also imported.
-/

namespace SetGen

/-- A set is a predicate on a type. -/
def Set (α : Type u) := α → Prop

namespace Set

/-- Membership in a set. -/
protected def Mem (s : Set α) (a : α) : Prop := s a

instance : Membership α (Set α) := ⟨Set.Mem⟩

/-- The set of elements satisfying a predicate. -/
def setOf (p : α → Prop) : Set α := p

/-- Set-builder notation. -/
scoped notation "{" x " | " p "}" => SetGen.Set.setOf (fun x => p)

instance : EmptyCollection (Set α) := ⟨fun _ => False⟩

@[simp] theorem mem_empty_iff {a : α} : a ∈ (∅ : Set α) ↔ False := Iff.rfl

instance : Singleton α (Set α) := ⟨fun a b => b = a⟩

@[simp] theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl

instance : Union (Set α) := ⟨fun s t a => s a ∨ t a⟩

/-- Extensionality for sets. -/
@[ext]
theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext fun x => propext (h x)

@[simp] theorem mem_setOf_eq {x : α} {p : α → Prop} : x ∈ (setOf p : Set α) ↔ p x := Iff.rfl

@[simp] theorem mem_union_iff {a : α} {s t : Set α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := Iff.rfl

/-- Image of a set under a function. -/
def image (f : α → β) (s : Set α) : Set β := fun b => ∃ a, s a ∧ f a = b

@[simp] theorem mem_image {f : α → β} {s : Set α} {b : β} :
    b ∈ image f s ↔ ∃ a, a ∈ s ∧ f a = b := Iff.rfl

/-- Bind for sets. -/
def bind (s : Set α) (f : α → Set β) : Set β := fun b => ∃ a, s a ∧ f a b

/-- The monad instance for `Set`. -/
instance monad : Monad Set where
  pure a := fun b => b = a
  bind := Set.bind
  map f s := image f s

theorem pure_def (a : α) : (pure a : Set α) = fun b => b = a := rfl

theorem bind_def' {s : Set α} {f : α → Set β} :
    (s >>= f) = fun b => ∃ a, s a ∧ f a b := rfl

@[simp] theorem mem_pure {a b : α} : a ∈ (pure b : Set α) ↔ a = b := Iff.rfl

@[simp] theorem mem_bind {s : Set α} {f : α → Set β} {b : β} :
    b ∈ (s >>= f) ↔ ∃ a, a ∈ s ∧ b ∈ f a := Iff.rfl

@[simp] theorem fmap_eq_image {f : α → β} {s : Set α} : (f <$> s) = image f s := rfl

/-- Instance of `LawfulMonad` for `Set` -/
instance instLawfulMonadSet : LawfulMonad Set :=
  LawfulMonad.mk' Set
    (id_map := fun x => by
      ext b; simp only [fmap_eq_image, mem_image, id_eq]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro h; exact ⟨b, h, rfl⟩)
    (pure_bind := fun a f => by
      ext b; simp only [mem_bind, mem_pure]
      constructor
      · rintro ⟨_, rfl, h⟩; exact h
      · intro h; exact ⟨a, rfl, h⟩)
    (bind_assoc := fun s f g => by
      ext c; simp only [mem_bind]
      constructor
      · rintro ⟨b, ⟨a, ha, hf⟩, hg⟩; exact ⟨a, ha, b, hf, hg⟩
      · rintro ⟨a, ha, b, hf, hg⟩; exact ⟨b, ⟨a, ha, hf⟩, hg⟩)
    (bind_pure_comp := fun f x => by
      ext b; simp only [mem_bind, mem_pure, fmap_eq_image, mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)


end Set

end SetGen
