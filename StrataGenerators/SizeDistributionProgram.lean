import StrataGenerators.SizeDistributionStmt
import StrataGenerators.ProgramGen
import StrataGenerators.FunctionHasTypeAGen

/-!
# How the size knobs shape whole Strata Core programs

`genProgram numDecls b` folds `numDecls` declaration steps; the `Bounds` record `b` holds the
per-declaration size knobs. This module proves size results about the *program* distribution.

* `genProgram_nesting_threshold` — **a sharp threshold on `procSize`.** With `procSize = 0` no
  generated program holds a procedure whose body has a top-level `block`, `ite` or `loop`
  (probability exactly `0`, for every `numDecls`). With `procSize ≥ 1` and `procLen ≥ 1`, a program
  of `m + 1` declarations holds one with a top-level `loop` with probability at least
  `1/14 · procBound · (1/28)^m > 0`.

`prob_genProgram_ge` is the transfer lemma: an event that the first declaration step reaches with
probability `c` is reached by a program of `m + 1` declarations with probability
`c · stepMass ^ m`. The `stepMass ^ m` factor is a lower bound on the mass of the other `m` steps
(each at least the abstract-type step), not an estimate. Every positive bound here is a single-witness product and far from tight; the zero sides
are exact.
-/

open Lambda RandomChoice SPMF NNReal ENNReal Core Imperative
open StrataGenerators.SizeDistribution StrataGenerators.SizeDistributionStmt StrataGenerators.Stmt
open ProgramGen StrataGenerators.Procedure

namespace StrataGenerators.SizeDistributionProgram

theorem prob_dtFreshName_univ (reserved : List String) :
    nameMass ≤ prob (DatatypeGen.genFreshName (G := SPMF) reserved) Set.univ := by
  rw [nameMass]
  unfold DatatypeGen.genFreshName
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge prob_genIdentName_univ fun s => ?_)
  split <;> exact (prob_pure_of_mem (Set.mem_univ _)).ge

theorem prob_genDeclAbstract_univ (s : GenState) (b : Bounds) :
    nameMass ≤ prob (genDeclAbstract (G := SPMF) s b) Set.univ := by
  rw [nameMass]
  unfold genDeclAbstract genAbstractType
  refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge ?_ fun x => ?_)
  · refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge (prob_dtFreshName_univ _)
      fun _ => ?_)
    refine le_trans (le_of_eq (one_mul _).symm) (prob_bind_univ_ge ?_ fun _ =>
      (prob_pure_of_mem (Set.mem_univ _)).ge)
    rw [prob_univ, mass_chooseNat]
  · obtain ⟨decl, name, arity⟩ := x
    dsimp only
    split <;> exact (prob_pure_of_mem (Set.mem_univ _)).ge

theorem prob_genDeclStep_ge (s : GenState) (b : Bounds) (E : Set StepResult) :
    stepShare * prob (genDeclAbstract (G := SPMF) s b) E ≤ prob (genDeclStep (G := SPMF) s b) E := by
  rw [stepShare]
  unfold genDeclStep
  by_cases hc : hasCallableFunc s = true <;>
    simp only [hc, ite_true, ite_false, Bool.false_eq_true]
  all_goals
    refine le_trans ?_ (prob_frequency_ge _ _ 0 (by simp) _)
    simp only [List.getElem_cons_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    exact mul_le_mul' (le_of_eq (by norm_num)) le_rfl


theorem prob_genDeclStep_proc_ge (s : GenState) (b : Bounds) (E : Set StepResult) :
    stepShare * prob (genDeclProcedure (G := SPMF) s b) E ≤ prob (genDeclStep (G := SPMF) s b) E := by
  rw [stepShare]
  unfold genDeclStep
  by_cases hc : hasCallableFunc s = true <;>
    simp only [hc, ite_true, ite_false, Bool.false_eq_true]
  all_goals
    refine le_trans ?_ (prob_frequency_ge _ _ 6 (by simp) _)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    exact mul_le_mul' (by ennr) le_rfl

theorem prob_genDeclsFold_univ (b : Bounds) :
    ∀ (m : Nat) (s : GenState), stepMass ^ m ≤ prob (genDeclsFold (G := SPMF) s b m) Set.univ := by
  rw [stepMass]
  intro m
  induction m with
  | zero => intro s; rw [genDeclsFold, pow_zero]; exact (prob_pure_of_mem (Set.mem_univ _)).ge
  | succ m ih =>
    intro s
    rw [genDeclsFold, pow_succ, mul_comm]
    refine prob_bind_univ_ge ?_ fun x => ?_
    · refine le_trans ?_ (prob_genDeclStep_ge s b Set.univ)
      refine le_trans ?_ (mul_le_mul' le_rfl (prob_genDeclAbstract_univ s b))
      rw [stepShare, nameMass]
      ennr
    · obtain ⟨ds, s'⟩ := x
      refine le_trans (le_of_eq (mul_one _).symm) (prob_bind_univ_ge (ih s') fun y => ?_)
      obtain ⟨_, _⟩ := y
      exact (prob_pure_of_mem (Set.mem_univ _)).ge

-- ── Axioms ──────────────────────────────────────────────────────────


-- ── Procedures ──────────────────────────────────────────────────────

theorem prob_map_ge {α β} (x : SPMF α) (f : α → β) (F : Set α) (E : Set β)
    (h : ∀ a ∈ F, f a ∈ E) : prob x F ≤ prob (f <$> x) E := by
  rw [map_eq_pure_bind]
  exact le_trans (le_of_eq (mul_one _).symm)
    (prob_bind_ge F fun a ha => (prob_pure_of_mem (h a ha)).ge)

theorem prob_listOfMaxLength_nil {α} (m : Nat) (g : SPMF α) :
    1 / ((m : ℝ≥0∞) + 1) ≤ prob (listOfMaxLength m g) {[]} := by
  unfold listOfMaxLength
  rw [map_eq_pure_bind, LawfulMonad.bind_assoc]
  refine le_trans (le_of_eq (mul_one _).symm)
    (le_trans (mul_le_mul' (prob_choose_zero m (Nat.zero_le _)) le_rfl)
      (prob_bind_ge _ fun x hx => ?_))
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Set.mem_setOf_eq] at hx; subst hx
  simp only [LawfulMonad.pure_bind, vectorOf, List.replicate, List.foldr]
  exact (prob_pure_of_mem (Set.mem_singleton _)).ge

theorem prob_genNameList_nil (d : Nat) :
    1 / ((d : ℝ≥0∞) + 1) ≤ prob (genNameList (G := SPMF) d) {[]} := by
  unfold genNameList; exact prob_listOfMaxLength_nil _ _

theorem prob_genInputs_nil (tv : List TyIdentifier) (d : Nat) :
    1 / ((d : ℝ≥0∞) + 1) ≤ prob (genInputs (G := SPMF) tv d) {[]} := by
  unfold genInputs genIdents
  rw [map_eq_pure_bind, LawfulMonad.bind_assoc]
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' (prob_genNameList_nil d) le_rfl)
    (prob_bind_ge {[]} fun x hx => ?_))
  rw [Set.mem_singleton_iff.mp hx]
  simp only [LawfulMonad.pure_bind, List.map_nil]
  simp [List.uniq]
  exact (prob_pure_of_mem (Set.mem_singleton _)).ge

theorem prob_genTypeArgs_nil (d : Nat) :
    1 / ((d : ℝ≥0∞) + 1) ≤ prob (genTypeArgs (G := SPMF) d) {[]} := by
  unfold genTypeArgs
  exact le_trans (prob_genNameList_nil d) (prob_map_ge _ _ _ _ fun a ha => by
    rw [Set.mem_singleton_iff.mp ha]; simp [List.uniq])

theorem prob_genChecks_univ (fc : FVarCtx) (octx : OpCtx) (tv : List TyIdentifier) (d : Nat)
    (pctx : PolyOpCtx) :
    1 / ((d : ℝ≥0∞) + 1) ≤ prob (genChecks (G := SPMF) fc octx tv d pctx) Set.univ := by
  unfold genChecks
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' (prob_genNameList_nil d) le_rfl)
    (prob_bind_ge {[]} fun x hx => ?_))
  rw [Set.mem_singleton_iff.mp hx]
  exact (prob_pure_of_mem (Set.mem_univ _)).ge

/-- A procedure whose body holds, at its top level, a statement satisfying `P`. -/
def ProcTop (P : Statement → Prop) (p : Procedure) : Prop :=
  ∃ ss, p.body = .structured ss ∧ ∃ st ∈ ss, P st

/-- **A procedure body inherits a top-level event from its first statement.** All six list-valued
header draws are taken at their empty value (probability at least `1/(size+1)` each), and the
remaining `len` body statements contribute their mass. `B` is any lower bound on the first
statement's event that holds uniformly in the scope. -/
theorem prob_genProcedure_top_ge (P : Statement → Prop) (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (size len : Nat) (pctx : PolyOpCtx)
    (k : Nat) (B : ℝ≥0∞)
    (hB : ∀ imm C' ctx,
      B ≤ prob (genStmt (G := SPMF) octx [] imm procs [] C' ctx pctx size k) (TopLevelEvent P)) :
    nameMass * ((1 / ((size : ℝ≥0∞) + 1)) ^ 6 * (B * stmtMassBound k size ^ len))
      ≤ prob (genProcedure (G := SPMF) octx procs C Γ size (len + 1) pctx k)
          {p | ProcTop P p} := by
  rw [nameMass]
  set c : ℝ≥0∞ := 1 / ((size : ℝ≥0∞) + 1)
  have hre : c ^ 6 * (B * stmtMassBound k size ^ len) =
      c * (c * (c * (c * (c * (c * (B * stmtMassBound k size ^ len)))))) := by ring
  rw [hre]
  unfold genProcedure
  refine le_trans (mul_le_mul' prob_genIdentName_univ le_rfl) (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (mul_le_mul' (prob_genTypeArgs_nil size) le_rfl) (prob_bind_ge {[]} fun ta hta => ?_)
  rw [Set.mem_singleton_iff.mp hta]
  refine le_trans (mul_le_mul' (prob_genInputs_nil [] size) le_rfl) (prob_bind_ge {[]} fun _ _ => ?_)
  refine le_trans (mul_le_mul' (prob_genInputs_nil [] size) le_rfl) (prob_bind_ge {[]} fun _ _ => ?_)
  refine le_trans (mul_le_mul' (prob_genInputs_nil [] size) le_rfl) (prob_bind_ge {[]} fun _ _ => ?_)
  refine le_trans (mul_le_mul' (prob_genChecks_univ _ _ _ _ _) le_rfl)
    (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (mul_le_mul' (prob_genChecks_univ _ _ _ _ _) le_rfl)
    (prob_bind_ge Set.univ fun _ _ => ?_)
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul'
    (le_trans (mul_le_mul' (hB _ _ _) le_rfl)
      (prob_genStmtChain_top_ge octx [] pctx P _ procs [] _ _ size len k)) le_rfl)
    (prob_bind_ge (TopLevelEventChain P) fun t ht => ?_))
  obtain ⟨body, _, _⟩ := t
  refine (prob_pure_of_mem ?_).ge
  exact ⟨body, rfl, ht⟩

-- ── Whole programs ──────────────────────────────────────────────────

/-- **The program-level transfer.** Any declaration event that the first declaration step reaches
with probability at least `c` is reached by a program of `m + 1` declarations with probability at
least `c · (1/28)^m`; the second factor pays for the mass of the other `m` steps. -/
theorem prob_genProgram_ge (Q : Decl → Prop) (m : Nat) (b : Bounds) (c : ℝ≥0∞)
    (hstep : c ≤ prob (genDeclStep (G := SPMF) initState b) {r | ∃ d ∈ r.1, Q d}) :
    c * stepMass ^ m ≤ prob (genProgram (G := SPMF) (m + 1) b) {P | ∃ d ∈ P.decls, Q d} := by
  unfold genProgram
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' ?_ le_rfl)
    (prob_bind_ge {t : List Decl × GenState | ∃ d ∈ t.1, Q d} (d := 1) fun t ht => ?_))
  · rw [genDeclsFold]
    refine le_trans (mul_le_mul' hstep le_rfl)
      (prob_bind_ge {r : StepResult | ∃ d ∈ r.1, Q d} fun r hr => ?_)
    refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul'
      (prob_genDeclsFold_univ b m _) le_rfl) (prob_bind_ge Set.univ fun t _ => ?_))
    refine (prob_pure_of_mem ?_).ge
    obtain ⟨d, hd, h⟩ := hr
    exact ⟨d, List.mem_append_left _ hd, h⟩
  · obtain ⟨decls, _⟩ := t
    exact (prob_pure_of_mem (E := {P : Program | ∃ d ∈ P.decls, Q d}) ht).ge

/-- A declaration is a procedure whose body has, at its top level, a statement satisfying `P`. -/
def IsProcWith (P : Statement → Prop) : Decl → Prop
  | .proc p _ => ProcTop P p
  | _ => False

theorem prob_genDeclProcedure_ge (P : Statement → Prop) (s : GenState) (b : Bounds) (len : Nat)
    (hlen : b.procLen = len + 1) (B : ℝ≥0∞)
    (hB : ∀ imm C' ctx, B ≤ prob (genStmt (G := SPMF) s.octx [] imm s.procs [] C' ctx s.derivedPctx
      b.procSize b.maxStmtSeqLen) (TopLevelEvent P)) :
    1 / 2 * ((1 / ((b.procSize : ℝ≥0∞) + 1)) ^ 6 *
        (B * stmtMassBound b.maxStmtSeqLen b.procSize ^ len)) * (1 / 2)
      ≤ prob (genDeclProcedure (G := SPMF) s b) {r | ∃ d ∈ r.1, IsProcWith P d} := by
  unfold genDeclProcedure
  rw [hlen]
  refine le_trans (mul_le_mul' (prob_genProcedure_top_ge P _ _ _ _ _ len _ _ B hB) le_rfl)
    (prob_bind_ge {p | ProcTop P p} fun p hp => ?_)
  refine le_trans (le_of_eq (mul_one _).symm) (le_trans (mul_le_mul' (prob_dtFreshName_univ _) le_rfl)
    (prob_bind_ge Set.univ fun _ _ => ?_))
  refine (prob_pure_of_mem ?_).ge
  exact ⟨_, List.mem_singleton_self _, hp⟩

/-- The bound for a procedure of size `size`, `len + 1` statements and body-length cap `k`, whose
first statement has probability at least `B`, with its fresh name. -/
noncomputable def procBound (size len k : Nat) (B : ℝ≥0∞) : ℝ≥0∞ :=
  nameMass * ((1 / ((size : ℝ≥0∞) + 1)) ^ 6 * (B * stmtMassBound k size ^ len)) * nameMass

/-- **Whole programs, procedure bodies with loops.** With `procSize ≥ 1` and `procLen ≥ 1`, a
program of `m + 1` declarations holds a procedure whose body has a top-level `loop` with
probability at least `1/14 · procBound · (1/28)^m`. -/
theorem prob_genProgram_proc_loop (m n len : Nat) (b : Bounds) (hs : b.procSize = n + 1)
    (hl : b.procLen = len + 1) :
    stepShare * procBound (n + 1) len b.maxStmtSeqLen (loopAtSize b.maxStmtSeqLen) * stepMass ^ m ≤
      prob (genProgram (G := SPMF) (m + 1) b) {P | ∃ d ∈ P.decls, IsProcWith IsLoop d} := by
  refine prob_genProgram_ge _ m b _ ?_
  refine le_trans ?_ (prob_genDeclStep_proc_ge initState b _)
  refine mul_le_mul' le_rfl ?_
  have h := prob_genDeclProcedure_ge IsLoop initState b len hl (loopAtSize b.maxStmtSeqLen) (by
    intro imm C' ctx; rw [hs]
    exact prob_genStmt_loop_ge _ [] _ imm _ [] C' ctx n _)
  rw [hs] at h
  exact h


-- ── The zero side: `procSize = 0` ───────────────────────────────────

theorem sound_true {α} (g : SPMF α) : IsSoundFor g (fun _ => True) := fun _ _ => trivial

/-- **At `procSize = 0` no procedure body has a nesting statement at its top level.** -/
theorem genProcedure_zero_flat (octx : OpCtx) (procs : ProcSigCtx) (C : LContext CoreLParams)
    (Γ : TContext Unit) (len : Nat) (pctx : PolyOpCtx) (k : Nat) :
    IsSoundFor (genProcedure (G := SPMF) octx procs C Γ 0 len pctx k)
      (fun p => ¬ ProcTop IsNesting p) := by
  rw [IsSoundFor.iff_obs]
  unfold genProcedure
  walk [(sound_true genIdentName).obs, (sound_true (genTypeArgs _)).obs,
    (sound_true (genInputs _ _)).obs, (sound_true (genChecks _ _ _ _ _)).obs,
    (genStmtChain_zero_flat octx _ pctx _ procs _ _ k _ _).obs]
  rename_i hb
  rintro ⟨ss, hss, st, hst, hn⟩
  injection hss with h
  subst h
  exact hb st hst hn

/-- No declaration in the list is a procedure with a top-level nesting statement. -/
def NoNestingProc (ds : List Decl) : Prop := ∀ d ∈ ds, ¬ IsProcWith IsNesting d

theorem addConstants_noNestingProc (τ : LMonoTy) :
    ∀ (cs : List String) (C C' : LContext CoreLParams) (ds : List Decl),
      addConstants C τ cs = some (C', ds) → NoNestingProc ds := by
  intro cs
  induction cs with
  | nil => intro C C' ds h; simp [addConstants] at h; obtain ⟨-, rfl⟩ := h; simp [NoNestingProc]
  | cons c cs ih =>
    intro C C' ds h
    simp only [addConstants] at h
    split at h
    · split at h
      · rename_i C₁ _ C'' ds' hrec
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · simp [mkConstantDecl, IsProcWith]
        · exact ih _ _ _ hrec d hd
      · simp at h
    · simp at h

theorem genDeclStep_zero_flat (s : GenState) (b : Bounds) (hs : b.procSize = 0) :
    IsSoundFor (genDeclStep (G := SPMF) s b) (fun r => NoNestingProc r.1) := by
  have hp : IsSoundFor (genProcedure (G := SPMF) s.octx s.procs s.C s.Γ b.procSize b.procLen
      s.derivedPctx b.maxStmtSeqLen) (fun p => ¬ ProcTop IsNesting p) := by
    rw [hs]; exact genProcedure_zero_flat _ _ _ _ _ _ _
  rw [IsSoundFor.iff_obs]
  unfold genDeclStep genDeclAbstract genAbstractType genDeclAlias genAlias genDeclAxiom genAxiom
    genDeclDistinct genDistinctAssertion genDeclDatatype genDeclFunction genDeclProcedure
  walk [(sound_true (DatatypeGen.genFreshName _)).obs, (sound_true (DatatypeGen.genFreshNames _ _)).obs,
    (sound_true (chooseNat _ _ _)).obs, (sound_true (genNonRecursiveArgTy _ _ _ _)).obs,
    (sound_true (genLExpr _ _ _ _ _ _ _ _ _)).obs, (sound_true (genFunction _ _ _ _)).obs,
    (sound_true (DatatypeGen.genMutuallyRecursiveDatatypes _ _ _ _ _ _ _ _ _)).obs, hp.obs]
  all_goals first
    | (simp [NoNestingProc, IsProcWith, mkAbstractTypeDecl, mkAliasDecl, mkAxiomDecl,
        mkDistinctDecl]; done)
    | (rename_i heq
       intro d hd
       rcases List.mem_append.mp hd with hd | hd
       · exact addConstants_noNestingProc _ _ _ _ _ heq d hd
       · simp only [List.mem_singleton] at hd; subst hd; simp [mkDistinctDecl, IsProcWith])
    | (rename_i hproc _ _
       intro d hd
       simp only [List.mem_singleton] at hd; subst hd
       exact hproc)

theorem genDeclsFold_zero_flat (b : Bounds) (hs : b.procSize = 0) :
    ∀ (m : Nat) (s : GenState), IsSoundFor (genDeclsFold (G := SPMF) s b m)
      (fun t => NoNestingProc t.1) := by
  intro m
  induction m with
  | zero =>
    intro s t ht
    rw [genDeclsFold, mem_support_pure_iff] at ht
    subst ht; simp [NoNestingProc]
  | succ m ih =>
    intro s t ht
    rw [genDeclsFold] at ht
    simp only [mem_support_bind_iff, mem_support_pure_iff] at ht
    obtain ⟨⟨ds, s'⟩, hr, ⟨rest, s''⟩, hrest, rfl⟩ := ht
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact genDeclStep_zero_flat s b hs _ hr d hd
    · exact ih s' _ hrest d hd

/-- **The program-level statement threshold.** With `procSize = 0` no generated program holds a
procedure whose body has a top-level `block`, `ite` or `loop`; with `procSize ≥ 1` (and a body of
at least one statement) a program of `m + 1` declarations holds one with a top-level `loop` with
probability at least `1/14 · procBound · (1/28)^m > 0`. -/
theorem genProgram_nesting_threshold (b : Bounds) :
    (b.procSize = 0 → ∀ numDecls,
      prob (genProgram (G := SPMF) numDecls b) {P | ∃ d ∈ P.decls, IsProcWith IsNesting d} = 0) ∧
    (∀ m n len, b.procSize = n + 1 → b.procLen = len + 1 →
      stepShare * procBound (n + 1) len b.maxStmtSeqLen (loopAtSize b.maxStmtSeqLen) *
          stepMass ^ m ≤
        prob (genProgram (G := SPMF) (m + 1) b) {P | ∃ d ∈ P.decls, IsProcWith IsNesting d}) := by
  refine ⟨fun hs numDecls => ?_, fun m n len hs hl => ?_⟩
  · refine (prob_eq_zero_iff _ _).mpr fun P hP hn => ?_
    unfold genProgram at hP
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hP
    obtain ⟨⟨decls, s'⟩, ht, rfl⟩ := hP
    obtain ⟨d, hd, hdn⟩ := hn
    exact genDeclsFold_zero_flat b hs numDecls initState _ ht d hd hdn
  · refine le_trans (prob_genProgram_proc_loop m n len b hs hl) (prob_mono ?_)
    rintro P ⟨d, hd, hdl⟩
    refine ⟨d, hd, ?_⟩
    cases d with
    | proc p md =>
      obtain ⟨ss, hss, st, hst, hl⟩ := hdl
      refine ⟨ss, hss, st, hst, ?_⟩
      cases st <;> simp_all [IsLoop, IsNesting]
    | _ => exact hdl.elim

end StrataGenerators.SizeDistributionProgram
