module
public import Strata.DL.Lambda.Factory
public import Strata.Languages.Core.Factory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps

/-!
# The functions of a factory built from an array

`Lambda.Factory.ofArray` adds the functions of an array one at a time, and it looks each name up in
a hash map before it adds the function. The kernel does not compute a `String` hash, so the kernel
cannot compute the functions of such a factory, and `decide` cannot check a concrete fact about
them.

`Factory.toArrayOfArray` removes the hash map from the question. If the names of the array are
distinct, the factory has exactly that array as its functions, in the same order. A concrete fact
about `Core.Factory` is then a fact about the array literal `Core.WFFactoryArray`, which the kernel
can evaluate.

This file is a module, like `HasTypeAGen/OpsConsistentBridge.lean`, because the lemmas of Strata
about the inside of a `Factory` are not public.
-/

namespace Lambda
open Lambda

set_option linter.unusedSectionVars false

variable {T : LExprParams} [DecidableEq T.IDMeta]

/-- The fold of `Factory.pushIfNew` over a list of functions with distinct names, none of them a
    name of `F`, appends the list to the functions of `F`. -/
private theorem Factory.toArray_foldl_pushIfNew :
    ∀ (l : List (LFunc T)) (F : @Factory T),
      (∀ g ∈ l, g.name.name ∉ F) → List.Nodup (l.map (·.name.name)) →
      (l.foldl Factory.pushIfNew F).toArray = F.toArray ++ l.toArray := by
  intro l
  induction l with
  | nil => intro F _ _; simp
  | cons g rest ih =>
    intro F hnew hnodup
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hg_notin, hrest_nodup⟩ := hnodup
    have hnew_g : g.name.name ∉ F := hnew g List.mem_cons_self
    have hpush : F.pushIfNew g = F.push g hnew_g := by
      unfold Factory.pushIfNew; rw [dite_eq_right hnew_g]
    have hrest : ∀ h ∈ rest, h.name.name ∉ F.push g hnew_g := by
      intro h hh
      rw [Factory.push_mem_iff F g hnew_g]
      simp only [not_or]
      refine ⟨fun heq => hg_notin ?_, hnew h (List.mem_cons_of_mem _ hh)⟩
      rw [← heq]
      exact List.mem_map.mpr ⟨h, hh, rfl⟩
    rw [List.foldl_cons, hpush, ih (F.push g hnew_g) hrest hrest_nodup]
    simp [Factory.push]

/-- A factory that `Factory.ofArray` builds from an array of functions with distinct names has
    exactly that array as its functions, in the same order. -/
public theorem Factory.toArrayOfArray {a : Array (LFunc T)}
    (hnodup : List.Nodup (a.toList.map (·.name.name))) :
    (Factory.ofArray a).toArray = a := by
  unfold Factory.ofArray Factory.append
  rw [← Array.foldl_toList, Factory.toArray_foldl_pushIfNew a.toList Factory.default
    (fun g _ => Factory.default_empty g.name.name) hnodup]
  simp

end Lambda

/-- The functions of `Core.Factory` are the functions of the array `Core.WFFactoryArray`, in the
    same order. -/
public theorem Core.factory_toArray :
    Core.Factory.toArray = Core.WFFactoryArray.map (·.func) :=
  Lambda.Factory.toArrayOfArray Core.WFFactoryArray_func_name_nodup
