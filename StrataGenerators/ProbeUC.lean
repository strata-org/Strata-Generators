module
public import Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.LTyUnify
open Lambda

theorem subst_ground (S : Subst) (A : LMonoTy) (hA : A.freeVars = []) :
    LMonoTy.subst S A = A := by
  have h1 : LMonoTy.subst S A = LMonoTy.subst Subst.empty A := by
    apply agree_on_freeVars_implies_subst_eq
    intro v hv; rw [hA] at hv; simp at hv
  rw [h1, LMonoTy.subst_emptyS (by simp)]
