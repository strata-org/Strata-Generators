import StrataGenerators.StmtHasTypeAGenComplete

open Lambda LExpr RandomChoice Core Imperative TypeSpec ArbString
open StrataGenerators.Stmt StrataGenerators.Procedure StrataGenerators.Function

/-!
# Completeness of `genStmt` with an existential size and body-length cap

`spec_complete_at` is stated at a fixed size `n` and a fixed body-length cap `k`: its side conditions
`AlphabetOk`, `CallOk` and `ExprOk` mention both. This module removes them from the statement.
`spec_complete`, the main completeness statement for `genStmt`, says that a well-typed statement that meets the *size-free* forms of the
side conditions is reachable by `genStmt … n k` for *some* `n` and `k`.

The size-free forms are `AlphabetOkE`, `CallOkE` and `ExprOkE`. They keep every clause about a
name, a shape or a call recipe, drop every clause about a length, and replace "reachable by
`genLExpr` at depth `n`" by `ExprReach`, "reachable by `genLExpr` at every large enough depth".
`exprReach_of_syntactic` discharges `ExprReach` from the syntactic side conditions of
`genLExpr_complete`, which do not mention a depth.

The proof needs no lemma about the monotonicity of a support in the size. Each `*.eventually`
lemma shows that a size-free condition gives the original condition at every large enough `n`
(and `k`), and `spec_complete_at` is applied at the largest of the thresholds.
-/

namespace StrataGenerators.Stmt.SpecComplete
variable {octx : OpCtx} {tvars : List TyIdentifier}


-- ── "Eventually" ─────────────────────────────────────────────────────────────

/-- `P n` holds at every `n` from some threshold on. -/
def Eventually (P : Nat → Prop) : Prop := ∃ N, ∀ n, N ≤ n → P n

theorem Eventually.and {P Q : Nat → Prop} (hP : Eventually P) (hQ : Eventually Q) :
    Eventually fun n => P n ∧ Q n := by
  obtain ⟨N, hN⟩ := hP; obtain ⟨M, hM⟩ := hQ
  exact ⟨max N M, fun n h => ⟨hN n (by omega), hM n (by omega)⟩⟩

theorem Eventually.of_forall {P : Nat → Prop} (h : ∀ n, P n) : Eventually P := ⟨0, fun n _ => h n⟩

theorem Eventually.mono {P Q : Nat → Prop} (hP : Eventually P) (h : ∀ n, P n → Q n) :
    Eventually Q := by
  obtain ⟨N, hN⟩ := hP; exact ⟨N, fun n hn => h n (hN n hn)⟩

/-- A condition that holds eventually also holds eventually one level up, at `n - 1`. -/
theorem Eventually.pred {P : Nat → Prop} (hP : Eventually P) : Eventually fun n => P (n - 1) := by
  obtain ⟨N, hN⟩ := hP; exact ⟨N + 1, fun n h => hN (n - 1) (by omega)⟩

theorem Eventually.forall_mem {α : Type} {P : α → Nat → Prop} :
    ∀ (l : List α), (∀ a ∈ l, Eventually (P a)) → Eventually fun n => ∀ a ∈ l, P a n
  | [], _ => .of_forall fun _ _ h => nomatch h
  | a :: l, h =>
    ((h a (by simp)).and (Eventually.forall_mem l fun b hb => h b (by simp [hb]))).mono
      fun _ ⟨ha, hl⟩ b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hl b hb

theorem Eventually.forall₂ {α β : Type} {R : α → β → Nat → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ (fun a b => Eventually (R a b)) l₁ l₂ →
      Eventually fun n => List.Forall₂ (fun a b => R a b n) l₁ l₂
  | _, _, .nil => .of_forall fun _ => .nil
  | _, _, .cons h hs => (h.and (Eventually.forall₂ hs)).mono fun _ ⟨h₁, h₂⟩ => .cons h₁ h₂

-- ── Expressions reachable at every large enough depth ───────────────────────

/-- `e` is in `genLExpr`'s support at the type `τ`, in the scope `ctx`, at every large enough
    depth. -/
def ExprReach (ctx : VarCtx) (τ : LMonoTy) (e : Expression.Expr) : Prop :=
  Eventually fun d => e ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx [] tvars [] d τ)

/-- `ExprReach` from the syntactic side conditions of `genLExpr_complete`, none of which mentions
    a depth. -/
theorem exprReach_of_syntactic (ctx : VarCtx) (τ : LMonoTy) (e : Expression.Expr)
    (hτ : ∃ m, τ ∈ SPMF.support (genLMonoTy (G := SPMF) tvars m))
    (hwt : HasTypeA' [] e τ) (hnames : emptyNames e) (hvars : allVarsInCtx ctx.toFVarCtx octx e)
    (hats : ∃ m, AllTypesSimple tvars m [] e) :
    ExprReach (octx := octx) (tvars := tvars) ctx τ e := by
  obtain ⟨m, hm⟩ := hats
  exact ⟨max m (termDepth [] e), fun d hd => genLExpr_complete _ _ _ _ _ d τ hτ 3 e
    (.inl ⟨hwt, hnames, hvars, allTypesSimple_mono_le tvars m d [] e (by omega) hm, by omega⟩)⟩

-- ── The size-free alphabet condition ────────────────────────────────────────

mutual
/-- `AlphabetOk` without its size and length clauses: the name clauses, and an `init` type that
    `genLMonoTy` reaches at *some* depth. -/
def AlphabetOkE (tvars : List TyIdentifier) : Statement → Prop
  | .cmd (CmdExt.cmd (.init x (.forAll [] mty) _ _)) =>
      x.name ∈ SPMF.support (genIdentName (G := SPMF)) ∧
      ∃ m, mty ∈ SPMF.support (genLMonoTy (G := SPMF) tvars m)
  | .cmd (CmdExt.cmd (.init _ _ _ _)) => True
  | .cmd (CmdExt.cmd (.set _ _ _)) => True
  | .cmd (CmdExt.cmd (.assert l _ _)) => l ∈ SPMF.support (genIdentName (G := SPMF))
  | .cmd (CmdExt.cmd (.assume l _ _)) => l ∈ SPMF.support (genIdentName (G := SPMF))
  | .cmd (CmdExt.cmd (.cover l _ _)) => l ∈ SPMF.support (genIdentName (G := SPMF))
  | .cmd (CmdExt.call _ _ _) => True
  | .block label body _ =>
      label ∈ SPMF.support (genIdentName (G := SPMF)) ∧ AlphabetOkEList tvars body
  | .ite _ t e _ => AlphabetOkEList tvars t ∧ AlphabetOkEList tvars e
  | .loop _ _ invs body _ =>
      (∀ p ∈ invs, p.1 ∈ SPMF.support (genIdentName (G := SPMF))) ∧ AlphabetOkEList tvars body
  | .exit _ _ => True
  | .typeDecl tc _ =>
      isLocalTypeName tc.name = true ∧ tc.name ∈ SPMF.support (genIdentName (G := SPMF)) ∧
      (∀ s ∈ tc.params, s ∈ SPMF.support (genIdentName (G := SPMF)))

/-- `AlphabetOkE` lifted to a statement list. -/
def AlphabetOkEList (tvars : List TyIdentifier) : List Statement → Prop
  | [] => True
  | s :: ss => AlphabetOkE tvars s ∧ AlphabetOkEList tvars ss
end

/-- `AlphabetOk` holds at every large enough cap `k` and size `n`. -/
def AlphabetOkEv (tvars : List TyIdentifier) (s : Statement) : Prop :=
  ∃ K, Eventually fun n => ∀ k, K ≤ k → AlphabetOk tvars k n s

/-- `AlphabetOkList` holds at every large enough cap `k` and size `n`. -/
def AlphabetOkListEv (tvars : List TyIdentifier) (ss : List Statement) : Prop :=
  ∃ K, Eventually fun n => ∀ k, K ≤ k → AlphabetOkList tvars k n ss

theorem AlphabetOkListEv.cons {s : Statement} {ss : List Statement}
    (hs : AlphabetOkEv tvars s) (hss : AlphabetOkListEv tvars ss) :
    AlphabetOkListEv tvars (s :: ss) := by
  obtain ⟨K₁, h₁⟩ := hs; obtain ⟨K₂, h₂⟩ := hss
  exact ⟨max K₁ K₂, (h₁.and h₂).mono fun _ ⟨a, b⟩ k hk =>
    ⟨a k (by omega), b k (by omega)⟩⟩

/-- A nested body: the body's condition one size smaller, and its length below the cap. -/
theorem AlphabetOkListEv.nested {ss : List Statement} (h : AlphabetOkListEv tvars ss) :
    ∃ K, Eventually fun n => ∀ k, K ≤ k →
      ss.length ≤ k ∧ AlphabetOkList tvars k (n - 1) ss := by
  obtain ⟨K, hK⟩ := h
  exact ⟨max K ss.length, hK.pred.mono fun _ h k hk => ⟨by omega, h k (by omega)⟩⟩

mutual
theorem alphabetOkE_eventually : ∀ (s : Statement), AlphabetOkE tvars s → AlphabetOkEv tvars s
  | .cmd (CmdExt.cmd (.init x (.forAll [] mty) _ _)), ⟨hx, m, hm⟩ =>
    ⟨0, ⟨m, fun n hn _ _ => ⟨hx, (genLMonoTy_support tvars n mty).mpr
      (inGenLMonoTySupport_mono tvars m n mty hn ((genLMonoTy_support tvars m mty).mp hm))⟩⟩⟩
  | .cmd (CmdExt.cmd (.init _ (.forAll (_ :: _) _) _ _)), _ =>
    ⟨0, .of_forall fun _ _ _ => by simp [AlphabetOk]⟩
  | .cmd (CmdExt.cmd (.set _ _ _)), _ => ⟨0, .of_forall fun _ _ _ => by simp [AlphabetOk]⟩
  | .cmd (CmdExt.cmd (.assert _ _ _)), h => ⟨0, .of_forall fun _ _ _ => by simpa [AlphabetOk, AlphabetOkE] using h⟩
  | .cmd (CmdExt.cmd (.assume _ _ _)), h => ⟨0, .of_forall fun _ _ _ => by simpa [AlphabetOk, AlphabetOkE] using h⟩
  | .cmd (CmdExt.cmd (.cover _ _ _)), h => ⟨0, .of_forall fun _ _ _ => by simpa [AlphabetOk, AlphabetOkE] using h⟩
  | .cmd (CmdExt.call _ _ _), _ => ⟨0, .of_forall fun _ _ _ => by simp [AlphabetOk]⟩
  | .block _ body _, ⟨hl, hb⟩ => by
    obtain ⟨K, N, h⟩ := (alphabetOkEList_eventually body hb).nested
    refine ⟨K, N + 1, fun n hn k hk => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simpa [AlphabetOk, hl] using h (n + 1) (by omega) k hk
  | .ite _ t e _, ⟨ht, he⟩ => by
    obtain ⟨K₁, h₁⟩ := (alphabetOkEList_eventually t ht).nested
    obtain ⟨K₂, h₂⟩ := (alphabetOkEList_eventually e he).nested
    obtain ⟨N, h⟩ := h₁.and h₂
    refine ⟨max K₁ K₂, N + 1, fun n hn k hk => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := (h (n + 1) (by omega)).imp (· k (by omega)) (· k (by omega))
    simpa [AlphabetOk] using ⟨a, c, b, d⟩
  | .loop _ _ invs body _, ⟨hi, hb⟩ => by
    obtain ⟨K, N, h⟩ := (alphabetOkEList_eventually body hb).nested
    refine ⟨max K invs.length, N + 1, fun n hn k hk => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨a, b⟩ := h (n + 1) (by omega) k (by omega)
    simp only [AlphabetOk]
    exact ⟨by omega, hi, a, b⟩
  | .exit _ _, _ => ⟨0, .of_forall fun _ _ _ => by simp [AlphabetOk]⟩
  | .typeDecl tc _, ⟨h₁, h₂, h₃⟩ =>
    ⟨0, ⟨tc.params.length, fun n hn _ _ => by simpa [AlphabetOk] using ⟨h₁, h₂, hn, h₃⟩⟩⟩

theorem alphabetOkEList_eventually :
    ∀ (ss : List Statement), AlphabetOkEList tvars ss → AlphabetOkListEv tvars ss
  | [], _ => ⟨0, .of_forall fun _ _ _ => by simp [AlphabetOkList]⟩
  | s :: ss, ⟨hs, hss⟩ =>
    AlphabetOkListEv.cons (alphabetOkE_eventually s hs) (alphabetOkEList_eventually ss hss)
end

-- ── The size-free expression condition ──────────────────────────────────────

/-- `CmdExprOk` with `ExprReach` in place of reachability at one depth. -/
def CmdExprOkE (ctx : VarCtx) : Cmd Expression → Prop
  | .init _ (.forAll [] mty) (.det e) _ => ExprReach (octx := octx) (tvars := tvars) ctx mty e
  | .init _ _ _ _ => True
  | .set x (.det e) _ =>
      ∀ mty, Map.find? ctx x = some mty → ExprReach (octx := octx) (tvars := tvars) ctx mty e
  | .set _ _ _ => True
  | .assert _ e _ => ExprReach (octx := octx) (tvars := tvars) ctx .bool e
  | .assume _ e _ => ExprReach (octx := octx) (tvars := tvars) ctx .bool e
  | .cover _ e _ => ExprReach (octx := octx) (tvars := tvars) ctx .bool e

mutual
/-- `ExprOk` with `ExprReach` in place of reachability at one depth. It needs no size, so a
    nested body is checked in its own scope only. -/
def ExprOkE (ctx : VarCtx) : Statement → Prop
  | .cmd (CmdExt.cmd c) => CmdExprOkE (octx := octx) (tvars := tvars) ctx c
  | .cmd (CmdExt.call _ _ _) => True
  | .block _ body _ => ExprOkEList ctx body
  | .ite cond t e _ =>
      (∀ g, cond = .det g → ExprReach (octx := octx) (tvars := tvars) ctx .bool g) ∧
      ExprOkEList ctx t ∧ ExprOkEList ctx e
  | .loop guard measure invs body _ =>
      (∀ g, guard = .det g → ExprReach (octx := octx) (tvars := tvars) ctx .bool g) ∧
      (∀ m, measure = some m → ExprReach (octx := octx) (tvars := tvars) ctx .int m) ∧
      (∀ p ∈ invs, ExprReach (octx := octx) (tvars := tvars) ctx .bool p.2) ∧
      ExprOkEList ctx body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- `ExprOkE` lifted to a statement chain, threading the scope with `stepCtx`. -/
def ExprOkEList (ctx : VarCtx) : List Statement → Prop
  | [] => True
  | s :: ss => ExprOkE ctx s ∧ ExprOkEList (stepCtx ctx s) ss
end

theorem cmdExprOkE_eventually (ctx : VarCtx) :
    ∀ (c : Cmd Expression), CmdExprOkE (octx := octx) (tvars := tvars) ctx c →
      Eventually fun n => CmdExprOk (octx := octx) (tvars := tvars) ctx n c
  | .init _ (.forAll [] _) (.det _) _, h => h
  | .init _ (.forAll [] _) .nondet _, _ => .of_forall fun _ => trivial
  | .init _ (.forAll (_ :: _) _) _ _, _ => .of_forall fun _ => trivial
  | .set x (.det _) _, h => by
    cases hf : Map.find? ctx x with
    | none => exact .of_forall fun _ mty hm => by simp [hf] at hm
    | some mty =>
      exact (h mty hf).mono fun _ hn mty' hm => by rw [hf] at hm; cases hm; exact hn
  | .set _ .nondet _, _ => .of_forall fun _ => trivial
  | .assert _ _ _, h => h
  | .assume _ _ _, h => h
  | .cover _ _ _, h => h

/-- A guard that is reachable whenever it is deterministic. -/
private theorem guard_eventually {ctx : VarCtx} {τ : LMonoTy} :
    ∀ (g : ExprOrNondet Expression),
      (∀ e, g = .det e → ExprReach (octx := octx) (tvars := tvars) ctx τ e) →
      Eventually fun n => ∀ e, g = .det e →
        e ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx [] tvars [] n τ)
  | .det e, h => (h e rfl).mono fun _ hn _ he => by cases he; exact hn
  | .nondet, _ => .of_forall fun _ _ he => nomatch he

/-- A measure that is reachable whenever it is present. -/
private theorem measure_eventually {ctx : VarCtx} :
    ∀ (m : Option Expression.Expr),
      (∀ e, m = some e → ExprReach (octx := octx) (tvars := tvars) ctx .int e) →
      Eventually fun n => ∀ e, m = some e →
        e ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx [] tvars [] n .int)
  | some e, h => (h e rfl).mono fun _ hn _ he => by cases he; exact hn
  | none, _ => .of_forall fun _ _ he => nomatch he

mutual
theorem exprOkE_eventually : ∀ (ctx : VarCtx) (s : Statement),
    ExprOkE (octx := octx) (tvars := tvars) ctx s →
      Eventually fun n => ExprOk (octx := octx) (tvars := tvars) ctx n s
  | ctx, .cmd (CmdExt.cmd c), h => cmdExprOkE_eventually ctx c h
  | _, .cmd (CmdExt.call _ _ _), _ => .of_forall fun _ => trivial
  | ctx, .block _ body _, h => (exprOkEList_eventually ctx body h).pred
  | ctx, .ite cond t e _, ⟨hg, ht, he⟩ =>
    ((guard_eventually cond hg).and ((exprOkEList_eventually ctx t ht).pred.and
      (exprOkEList_eventually ctx e he).pred)).mono fun _ h => h
  | ctx, .loop guard measure invs body _, ⟨hg, hm, hi, hb⟩ =>
    ((guard_eventually guard hg).and ((measure_eventually measure hm).and
      ((Eventually.forall_mem invs hi).and (exprOkEList_eventually ctx body hb).pred))).mono
      fun _ h => h
  | _, .exit _ _, _ => .of_forall fun _ => trivial
  | _, .typeDecl _ _, _ => .of_forall fun _ => trivial

theorem exprOkEList_eventually : ∀ (ctx : VarCtx) (ss : List Statement),
    ExprOkEList (octx := octx) (tvars := tvars) ctx ss →
      Eventually fun n => ExprOkList (octx := octx) (tvars := tvars) ctx n ss
  | _, [], _ => .of_forall fun _ => trivial
  | ctx, s :: ss, ⟨hs, hss⟩ =>
    (exprOkE_eventually ctx s hs).and (exprOkEList_eventually (stepCtx ctx s) ss hss)
end

-- ── The size-free call condition ────────────────────────────────────────────

mutual
/-- `CallOk` with `ExprReach` in place of reachability at one depth for the by-value inputs. Every
    other clause of the call recipe is unchanged. -/
def CallOkE (procs : ProcSigCtx) (ctx : VarCtx) : Statement → Prop
  | .cmd (CmdExt.call pname args _) =>
      ∃ (s : ProcSig) (σvals : List LMonoTy) (exprs : List Expression.Expr)
        (mask : List Bool),
        s ∈ procs ∧
        s.pname = pname ∧
        σvals ∈ SPMF.support
          (s.typeArgs.mapM (fun _ =>
            if hg : (generableTypesFromCtx ctx.values [] octx).length > 0 then
              elements (generableTypesFromCtx ctx.values [] octx)
                (by apply List.ne_nil_of_length_pos; assumption)
            else pure (.bool : LMonoTy)) : SPMF (List LMonoTy)) ∧
        args = StrataGenerators.Stmt.mkArgs s.M
          (outTargets [] ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O))
          exprs mask ∧
        (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).all (usableName [] ctx) = true ∧
        (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M
          ++ outTargets [] ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)).keys.Nodup ∧
        List.Forall₂ (fun e τ => ExprReach (octx := octx) (tvars := tvars) ctx τ e)
          exprs (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.I).values ∧
        (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).filter (needsInit ctx)
          ++ (outTargets [] ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)).filter
                (needsInit ctx) = []
  | .cmd (CmdExt.cmd _) => True
  | .block _ body _ => CallOkEList procs ctx body
  | .ite _ t e _ => CallOkEList procs ctx t ∧ CallOkEList procs ctx e
  | .loop _ _ _ body _ => CallOkEList procs ctx body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- `CallOkE` lifted to a statement chain, threading the scope with `stepCtx`. -/
def CallOkEList (procs : ProcSigCtx) (ctx : VarCtx) : List Statement → Prop
  | [] => True
  | s :: ss => CallOkE procs ctx s ∧ CallOkEList procs (stepCtx ctx s) ss
end

mutual
theorem callOkE_eventually (procs : ProcSigCtx) : ∀ (ctx : VarCtx) (s : Statement),
    CallOkE (octx := octx) (tvars := tvars) procs ctx s →
      Eventually fun n => CallOk (octx := octx) (tvars := tvars) procs ctx n s
  | _, .cmd (CmdExt.call _ _ _), ⟨sg, σvals, exprs, mask, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ =>
    (Eventually.forall₂ h₇).mono fun _ h => ⟨sg, σvals, exprs, mask, h₁, h₂, h₃, h₄, h₅, h₆, h, h₈⟩
  | _, .cmd (CmdExt.cmd _), _ => .of_forall fun _ => trivial
  | ctx, .block _ body _, h => (callOkEList_eventually procs ctx body h).pred
  | ctx, .ite _ t e _, ⟨ht, he⟩ =>
    ((callOkEList_eventually procs ctx t ht).pred.and (callOkEList_eventually procs ctx e he).pred)
  | ctx, .loop _ _ _ body _, h => (callOkEList_eventually procs ctx body h).pred
  | _, .exit _ _, _ => .of_forall fun _ => trivial
  | _, .typeDecl _ _, _ => .of_forall fun _ => trivial

theorem callOkEList_eventually (procs : ProcSigCtx) : ∀ (ctx : VarCtx) (ss : List Statement),
    CallOkEList (octx := octx) (tvars := tvars) procs ctx ss →
      Eventually fun n => CallOkList (octx := octx) (tvars := tvars) procs ctx n ss
  | _, [], _ => .of_forall fun _ => trivial
  | ctx, s :: ss, ⟨hs, hss⟩ =>
    (callOkE_eventually procs ctx s hs).and (callOkEList_eventually procs (stepCtx ctx s) ss hss)
end

-- ── Completeness with an existential size and cap ───────────────────────────

/-- **Completeness of `genStmt`, for some size and some body-length cap.** Every well-typed
    statement in generator shape (`InGenShape`) whose names, `init` types, call recipes and
    expressions meet the size-free conditions `AlphabetOkE`, `CallOkE` and `ExprOkE` is in the
    support of `genStmt … n k` for some size `n` and some cap `k`, with an output scope equivalent
    to the typing's. None of the side conditions mentions a size or a cap. -/
theorem spec_complete (P : Program) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ts : TypeScopes) (labels : List String)
    (s : Statement) (C' : LContext CoreLParams) (ts' : TypeScopes)
    (h : StatementWellTyped P C ts labels s C' ts') (ctx : VarCtx)
    (hΓ : Strata.Util.HMaps.Equiv ts (procToTCtx ctx).types)
    (hshape : InGenShape s) (hok : AlphabetOkE tvars s)
    (hcall : CallOkE (octx := octx) (tvars := tvars) procs ctx s)
    (hexpr : ExprOkE (octx := octx) (tvars := tvars) ctx s) :
    ∃ k n ctx', Strata.Util.HMaps.Equiv ts' (procToTCtx ctx').types ∧
      ctx' = stepCtx ctx s ∧
      (⟨[s], C', ctx'⟩ : GenStmtResult) ∈
        SPMF.support (genStmt (G := SPMF) octx tvars [] procs labels C ctx [] n k) := by
  obtain ⟨K, ha⟩ := alphabetOkE_eventually s hok
  obtain ⟨N, hN⟩ := (ha.and ((callOkE_eventually procs ctx s hcall).and
    (exprOkE_eventually ctx s hexpr)))
  obtain ⟨hA, hC, hE⟩ := hN N le_rfl
  exact ⟨K, N, spec_complete_at (maxStmtSeqLen := K) P procs C ts labels s C' ts' h ctx N hΓ hshape
    (hA K le_rfl) hC hE⟩

end StrataGenerators.Stmt.SpecComplete
