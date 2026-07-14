module
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.LExprTypeSpec

/-!
# Ground-matching completeness for Strata's unifier

Strata proves unification *soundness* but not completeness. Here we prove the
one completeness fact the generator's `OpsConsistent` proof needs: if `A` is a
*ground* monotype and a substitution instance of a pattern `P`
(`A = P.subst σ`), then `Constraints.unify [(A, P)] .empty` succeeds and the
resulting substitution `R` reconstructs `A` from `P` (`A = P.subst R`).
-/

namespace Lambda
open Lambda

/-- Ground monotypes are fixed by any substitution. -/
public theorem subst_ground (S : Subst) (A : LMonoTy) (hA : A.freeVars = []) :
    LMonoTy.subst S A = A := by
  have h1 : LMonoTy.subst S A = LMonoTy.subst Subst.empty A := by
    apply agree_on_freeVars_implies_subst_eq
    intro v hv; rw [hA] at hv; simp at hv
  rw [h1, LMonoTy.subst_emptyS (by simp)]

/-- The accumulator `S` is consistent with the ground matcher `σ`: every binding
    already recorded in `S` agrees with `σ` and is ground. -/
def Matchesσ (σ S : SubstInfo) : Prop :=
  ∀ id t, Maps.find? S.subst id = some t →
    t = LMonoTy.subst σ.subst (.ftvar id) ∧ t.freeVars = []

theorem Matchesσ_empty (σ : SubstInfo) : Matchesσ σ SubstInfo.empty := by
  intro id t h
  simp [SubstInfo.empty, Subst.empty, Maps.find?] at h

/-- If a list of monotypes has no free variables, each element is ground. -/
theorem freeVars_nil_of_mem {args : List LMonoTy} {a : LMonoTy}
    (hg : LMonoTys.freeVars args = []) (ha : a ∈ args) : a.freeVars = [] := by
  have : a.freeVars ⊆ LMonoTys.freeVars args := LMonoTys.freeVars_mem_subset ha
  rw [hg] at this
  exact List.subset_nil.mp this

/-- `LMonoTys.subst` is the pointwise `map` of `LMonoTy.subst`. -/
theorem LMonoTys_subst_eq_map (S : Subst) (args : List LMonoTy) :
    LMonoTys.subst S args = args.map (LMonoTy.subst S) := by
  have h := LMonoTy.subst_eq_substReduce S (LMonoTy.tcons "x" args)
  rw [LMonoTy.subst_tcons] at h
  simp only [LMonoTy.substReduce, LMonoTy.substReduceList_eq_map] at h
  injection h with _ hh
  rw [hh]
  exact List.map_congr_left (fun a _ => (LMonoTy.subst_eq_substReduce S a).symm)

/-- Membership in `zip (map g l) l` yields the mapped-equation for each pair. -/
theorem mem_zip_map {β : Type} (g : β → β) (l : List β) (a p : β)
    (h : (a, p) ∈ (l.map g).zip l) : a = g p := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · injection h with h1 h2; subst h1; subst h2; rfl
    · exact ih h

/-- **Induction workhorse for `unify_ground_instance`.** Every constraint `(a, p)`
    in `cs` is a *ground match*: `a` is ground and `a = p.subst σ` for one fixed,
    shared matcher `σ`. Under that hypothesis `Constraints.unifyCore` cannot fail —
    it returns some `r` whose accumulated substitution `r.newS` still `Matchesσ σ`
    (every recorded binding agrees with `σ` and is ground).

    This is the completeness fact Strata does not ship: its unifier comes with
    *soundness* lemmas (a successful unification yields equal types) but no
    guarantee that a solvable system actually succeeds. We only need the
    ground-matching special case, where the shared `σ` witnesses solvability and
    pins down the direction the unifier must solve each equation.

    Proof shape (why it is the longest lemma here): it is a mutual well-founded
    induction driven by the auto-generated `Constraints.unifyCore.induct`
    principle, so it has one subgoal per branch of `Constraint.unifyOne` /
    `Constraints.unifyCore` — 17 in total. `Matchesσ` is the invariant carried
    through the recursion. Groundness does most of the work: in the branches that
    would otherwise fail or diverge (`ftvar`-vs-ground mismatch, the occurs check,
    name/arity mismatch, bitvec-vs-`tcons`), `subst_ground` collapses `a` to a
    fixed ground type, so the ground-match hypothesis makes the failing case
    contradictory. The two substantive cases are the `ftvar id` binding steps
    (find-hit re-derives the same ground type; find-miss extends `S` and re-proves
    `Matchesσ`) and the `tcons` case (recurse into the argument lists, transporting
    the ground-match hypothesis pointwise via `mem_zip_map`). -/
theorem unifyCore_success (σ : SubstInfo) (cs : Constraints) (S : SubstInfo)
    (hM : Matchesσ σ S)
    (hcs : ∀ a p, (a, p) ∈ cs → a.freeVars = [] ∧ a = LMonoTy.subst σ.subst p) :
    ∃ r, Constraints.unifyCore cs S = .ok r ∧ Matchesσ σ r.newS := by
  revert hM hcs
  refine Constraints.unifyCore.induct
    (motive1 := fun c S => Matchesσ σ S → c.1.freeVars = [] → c.1 = LMonoTy.subst σ.subst c.2 →
      ∃ relS, Constraint.unifyOne c S = .ok relS ∧ Matchesσ σ relS.newS)
    (motive2 := fun cs S => Matchesσ σ S → (∀ a p, (a, p) ∈ cs → a.freeVars = [] ∧ a = LMonoTy.subst σ.subst p) →
      ∃ r, Constraints.unifyCore cs S = .ok r ∧ Matchesσ σ r.newS)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ cs S
  case _ =>
    intro S t1 t2 hbeq hsub hM hg hinst
    refine ⟨{ newS := S, goodSubset := ?_ }, ?_, hM⟩
    · simp [Subst.freeVars_subset_prop]
    · unfold Constraint.unifyOne
      simp only [hbeq, reduceDIte]
  case _ => intros; simp_all [LMonoTy.freeVars] -- 2 ftvar-t1: ground contradiction
  case _ => intros; simp_all [LMonoTy.freeVars] -- 3
  case _ => intros; simp_all [LMonoTy.freeVars] -- 4
  case _ => intros; simp_all [LMonoTy.freeVars] -- 5
  case _ => -- 6 orig ground, ftvar id == lty true: impossible (lty ground, ftvar not)
    intro S orig id _h1 _h1b lty hp1 hp2 hguard hM hgnd
    -- hgnd : orig.freeVars = [] ; hguard : (ftvar id == lty) = true ; lty := subst S.subst orig
    have hlty : lty = orig := Lambda.subst_ground S.subst orig hgnd
    rw [hlty] at hguard
    simp only [beq_iff_eq] at hguard
    rw [← hguard] at hgnd
    simp [LMonoTy.freeVars] at hgnd
  case _ => -- 7 occurs check: id ∈ lty.freeVars but lty ground → impossible
    intro S orig id _h1 _h1b lty hp1 hp2 hne hocc hM hgnd
    have hlty : lty = orig := Lambda.subst_ground S.subst orig hgnd
    rw [hlty, hgnd] at hocc
    simp at hocc
  case _ => -- 8 find? = some sty, recurse on (sty, lty)
    intro S orig id _h1 _h1b lty hp1 hp2 hne hnocc sty hfind IH hM hgnd hinst
    -- hgnd : orig.freeVars = [] ; hinst : orig = subst σ (ftvar id) ; lty := subst S orig
    have hlty : lty = orig := Lambda.subst_ground S.subst orig hgnd
    obtain ⟨hsty_eq, hsty_g⟩ := hM id sty hfind
    -- hsty_eq : sty = subst σ (ftvar id) ; hsty_g : sty.freeVars = []
    have hsty_orig : sty = orig := by rw [hsty_eq, ← hinst]
    obtain ⟨relS, hrelS_eq, hrelS_M⟩ := IH hM (by rw [hlty]; exact hsty_g) (by
      rw [hlty, ← hsty_orig, Lambda.subst_ground σ.subst sty hsty_g])
    refine ⟨⟨relS.newS, ?_⟩, ?_, hrelS_M⟩
    · have := Subst.freeVars_subset_prop_of_ftvar_id_when_id_in_S S id orig sty lty rfl hnocc hfind relS
      simp_all [Subst.freeVars_subset_prop_single_constraint_comm]
    · have hne2 : ¬(LMonoTy.ftvar id == LMonoTy.subst S.subst orig) = true := hne
      have hnocc2 : ¬id ∈ (LMonoTy.subst S.subst orig).freeVars := hnocc
      have hrelS_eq2 : Constraint.unifyOne (sty, LMonoTy.subst S.subst orig) S = Except.ok relS := hrelS_eq
      unfold Constraint.unifyOne
      simp only [dif_neg (show ¬((orig == LMonoTy.ftvar id) = true) from _h1),
        dif_neg hne2, dif_neg hnocc2]
      split
      · rename_i s heq2
        rw [hfind] at heq2; injection heq2 with h; subst h
        rw [hrelS_eq2]; rfl
      · rename_i heq2
        rw [hfind] at heq2; exact absurd heq2 (by simp)
  case _ => -- 9 find? = none, add binding [id ↦ lty]
    intro S orig id _h1 _h1b lty hp1 hp2 hne hnocc hfindnone hwf1 hwf2 new_subst h' newS hp1' hp2'
    intro hM hgnd hinst
    -- hgnd : orig.freeVars = [] ; hinst : orig = subst σ (ftvar id) ; lty := subst S orig
    have hlty : lty = orig := Lambda.subst_ground S.subst orig hgnd
    -- The new substitution
    have hnewM : Matchesσ σ ⟨new_subst, h'⟩ := by
      intro id' t' hf'
      simp only [new_subst] at hf'
      by_cases hid : id' = id
      · subst hid
        rw [Maps.find?_insert_self] at hf'
        injection hf' with ht'
        subst ht'
        refine ⟨?_, ?_⟩
        · rw [hlty]; simpa using hinst
        · rw [hlty]; exact hgnd
      · rw [Maps.find?_insert_ne _ _ _ _ hid] at hf'
        rw [Subst.find?_apply] at hf'
        cases hsv : Maps.find? S.subst id' with
        | none => rw [hsv] at hf'; simp at hf'
        | some v =>
          rw [hsv] at hf'
          simp only [Option.map_some] at hf'
          obtain ⟨hv_eq, hv_g⟩ := hM id' v hsv
          have hvv : LMonoTy.subst [[(id, lty)]] v = v := Lambda.subst_ground _ v hv_g
          rw [hvv] at hf'
          injection hf' with ht'
          subst ht'
          exact ⟨hv_eq, hv_g⟩
    refine ⟨⟨⟨new_subst, h'⟩, ?_⟩, ?_, hnewM⟩
    · exact hp2'
    · have hne2 : ¬(LMonoTy.ftvar id == LMonoTy.subst S.subst orig) = true := hne
      have hnocc2 : ¬id ∈ (LMonoTy.subst S.subst orig).freeVars := hnocc
      unfold Constraint.unifyOne
      simp only [dif_neg (show ¬((orig == LMonoTy.ftvar id) = true) from _h1),
        dif_neg hne2, dif_neg hnocc2]
      split
      · rename_i s heq2
        rw [hfindnone] at heq2; exact absurd heq2 (by simp)
      · rfl
  case _ => intro S n1 n2 hbeq heq; exfalso; apply hbeq; simp_all -- 10 bitvec: beq false but n1==n2
  case _ => -- 11 bitvec mismatch: instance forces n1=n2
    intro S n1 n2 hbeq hne hM hg hinst
    rw [LMonoTy.subst_bitvec] at hinst; simp_all
  case _ => -- 12 tcons match: recurse into args
    intro S name1 args1 name2 args2 hbeq hguard _nc IHc hM hg hinst
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_substLogic] at hinst
    simp only at hinst hg
    injection hinst with hn ha
    subst hn
    -- hg : LMonoTys.freeVars args1 = [] ; ha : args1 = substLogic σ.subst args2
    have hmap : args1 = args2.map (LMonoTy.subst σ.subst) := by
      rw [ha, ← LMonoTys.subst_eq_substLogic, LMonoTys_subst_eq_map]
    obtain ⟨r, hr_eq, hr_M⟩ := IHc hM (by
      intro a p hmem
      have hmem2 : (a, p) ∈ args1.zip args2 := hmem
      have hmem' : (a, p) ∈ (args2.map (LMonoTy.subst σ.subst)).zip args2 := by
        rw [← hmap]; exact hmem2
      refine ⟨?_, mem_zip_map (LMonoTy.subst σ.subst) args2 a p hmem'⟩
      have : a ∈ args1 := (List.of_mem_zip hmem2).1
      exact freeVars_nil_of_mem hg this)
    have hr_eq2 : Constraints.unifyCore (args1.zip args2) S = Except.ok r := hr_eq
    refine ⟨⟨r.newS, ?_⟩, ?_, hr_M⟩
    · exact Subst.freeVars_subset_prop_of_tcons S name1 name1 args1 args2 rfl r
    · unfold Constraint.unifyOne
      simp only [hbeq, dif_pos hguard, hr_eq2, bind, Except.bind, Bool.false_eq_true, dif_neg,
        not_false_eq_true]
  case _ => -- 13 tcons name/length mismatch: instance forces equality
    intro S name1 args1 name2 args2 hbeq hne hM hg hinst
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_substLogic] at hinst
    injection hinst with hn ha
    subst hn
    exfalso; apply hne
    have hlen : args1.length = args2.length := by
      rw [ha, LMonoTys.substLogic_length]
    simp [hlen]
  case _ => -- 14 bitvec vs tcons: instance impossible
    intro S size name args hbeq hM hg hinst
    rw [LMonoTy.subst_tcons] at hinst; simp at hinst
  case _ => -- 15 tcons vs bitvec: instance impossible
    intro S name args size hbeq hM hg hinst
    rw [LMonoTy.subst_bitvec] at hinst; simp at hinst
  case _ => -- 16 empty constraints
    intro S hM _
    refine ⟨{ newS := S, goodSubset := ?_ }, ?_, hM⟩
    · simp [Subst.freeVars_subset_prop_of_empty]
    · simp [Constraints.unifyCore]
  case _ => -- 17 cons
    intro S c c_rest ih1 ih2 hM hcs
    have hc : c.fst.freeVars = [] ∧ c.fst = LMonoTy.subst σ.subst c.snd :=
      hcs c.1 c.2 (by exact List.mem_cons_self ..)
    obtain ⟨relS, hrelS_eq, hrelS_M⟩ := ih1 hM hc.1 hc.2
    obtain ⟨r, hr_eq, hr_M⟩ := ih2 relS hrelS_M
      (fun a p hmem => hcs a p (List.mem_cons_of_mem _ hmem))
    refine ⟨⟨r.newS, Subst.freeVars_subset_prop_mk_cons relS r⟩, ?_, hr_M⟩
    unfold Constraints.unifyCore
    simp only [hrelS_eq, Except.mapError, hr_eq, bind, Except.bind]

/-- **Ground-matching completeness.** If `A` is a ground type and equals `P.subst σ`
    for some `σ` (where `P` is a monotype),
    then unifying `A` against `P` succeeds with resultant substitution `R`,
    and applying the substitution `R` to `P` should give us back `A`. -/
public theorem unify_ground_instance (A P : LMonoTy) (σ : SubstInfo)
    (hground : A.freeVars = []) (hinst : A = LMonoTy.subst σ.subst P) :
    ∃ R : SubstInfo, Constraints.unify [(A, P)] SubstInfo.empty = .ok R
      ∧ A = LMonoTy.subst R.subst P := by
  -- Part 1: unification succeeds (the completeness core).
  obtain ⟨R, hR⟩ : ∃ R, Constraints.unify [(A, P)] SubstInfo.empty = .ok R := by
    obtain ⟨r, hr_eq, _⟩ := unifyCore_success σ [(A, P)] SubstInfo.empty
      (Matchesσ_empty σ) (by
        intro a p hmem
        simp only [List.mem_singleton] at hmem
        rw [Prod.ext_iff] at hmem
        obtain ⟨ha, hp⟩ := hmem
        subst ha; subst hp
        exact ⟨hground, hinst⟩)
    refine ⟨r.newS, ?_⟩
    unfold Constraints.unify
    simp only [hr_eq, bind, Except.bind]
  refine ⟨R, hR, ?_⟩
  -- Part 2: reconstruction, from soundness + groundness of A.
  have hmk := LExpr.unify_makes_equal A P SubstInfo.empty R hR
  -- hmk : A.subst R.subst = P.subst R.subst
  rw [subst_ground R.subst A hground] at hmk
  exact hmk

end Lambda
