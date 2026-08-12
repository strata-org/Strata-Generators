import StrataGenerators.ProcedureHasTypeAGen.Support

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Stmt StrataGenerators.Procedure StrataGenerators.Function

/-!
# Completeness of `genStmt` / `genStmtChain`, indexed directly by `StatementHasTypeA`

`spec_complete` proves that every well-typed statement (per the declarative
`StatementHasTypeA` relation of `Strata.Languages.Core.StatementTypeSpec`) is in
`genStmt`'s support — **without** an auxiliary, generator-mirroring `StmtReachable`
relation. The proof runs by induction on the *typing derivation* itself, via the
two mutually recursive theorems `genStmt_spec_complete` / `genStmtChain_spec_complete`
(emulating `LMonoTy.resolveAliases_context` / `LMonoTys.resolveAliases_context`).

## The side conditions (recursive `Prop`-valued `def`s, not inductive relations)

A bounded random generator cannot reach *every* well-typed statement; its support
is strictly narrower than the spec's acceptance. The residual gaps are captured by
three recursive predicates over the statement tree — deliberately **functions**
returning `Prop`, not inductive relations:

* **`InGenShape`** — the two shape facts the generator fixes and the spec leaves
  free: metadata at `default`, and an `init`'s annotation monomorphic (`.forAll []`).
  (The empty-`assert`/`assume`/`cover`-label condition is *gone*: the generator now
  samples labels via `String.arbitrary`. The `typeDecl` `.bound` condition is *gone*:
  the generator now samples both `Boundedness` values. The `init` groundness
  condition is *gone*: procedure bodies are generated under a context that marks the
  type parameters rigid, so `RigidAnnotCompat` pins the stored type to the
  annotation — see `hRigid`.)
* **`AlphabetOk`** — the identifier-alphabet kernel: every generated *name*
  (block/invariant labels, `init` variable, type-constructor name and params) lies
  in the appropriate generator's support and, where relevant, dodges reserved
  keywords; `assert`/`assume`/`cover` labels lie in `String.arbitrary`'s support;
  and each generated *list* is within the size budget available at its depth.
* **`CallOk`** — the call recipe shape: a `.cmd (.call …)` statement is reachable
  only when its argument list is exactly the generator's `mkArgs`/`outTargets`
  recipe over some callee `s`, at the identity type-instantiation `σ = []`
  (the generator instantiates no type arguments). `True` on every non-call node,
  recursing into nested bodies.

Expression- and function-level side conditions are **bundled**, exactly as in the
soundness proof, into `GenLExprComplete` / a `genFunction`-reachability hypothesis,
taken here as environment hypotheses at every depth.

The procedure-call *correspondence* is a top-level hypothesis `ProcSigComplete procs P`
(the converse of `ProcSigCorresponds`): the callee a well-typed call resolves in `P`
is listed in the generator's `procs`. The `immutableVars` parameter is fixed to `[]`
(a procedure-level notion, vacuous at the statement level: `ctx.writable [] = ctx`).
-/

namespace StrataGenerators.Stmt.SpecComplete
variable {octx : OpCtx} {tvars : List TyIdentifier}

-- ── bridge lemmas ──
theorem procToTCtx_find_rev (ctx : VarCtx) (x : Identifier Unit) (mty : LMonoTy)
    (h : (procToTCtx ctx).types.find? x = some (.forAll [] mty)) : Map.find? ctx x = some mty := by
  rw [procToTCtx_find] at h
  cases hc : Map.find? ctx x with
  | none => rw [hc] at h; simp at h
  | some m => rw [hc] at h; simp only [Option.map_some] at h; injection h with h; injection h with _ h; rw [h]

theorem procToTCtx_fresh_rev (ctx : VarCtx) (x : Identifier Unit)
    (h : (procToTCtx ctx).types.find? x = none) : Map.find? ctx x = none := by
  rw [procToTCtx_find] at h
  cases hc : Map.find? ctx x with
  | none => rfl
  | some m => rw [hc] at h; simp at h

theorem freshName_reach (ctx : VarCtx) (x : Identifier Unit)
    (hname : x.name ∈ SetGen.support (NonEmptyString.arbitrary (G := SetGen.Set)))
    (hdodge : dodgeKeyword x.name = x.name) (hfresh : Map.find? ctx x = none) :
    x.name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) := by
  simp only [genFreshName, mem_support_bind_iff]
  refine ⟨x.name, hname, ?_⟩
  rw [hdodge]; simp only [mem_support_ite_iff, mem_support_pure_iff]
  refine Or.inl ⟨?_, trivial⟩
  unfold VarCtx.isFresh VarCtx.find?; obtain ⟨nm, u⟩ := x; cases u; rw [hfresh]; rfl

theorem aliasEquiv_nil_eq {a b : LMonoTy} (h : AliasEquiv [] a b) : a = b := by
  induction h using AliasEquiv.rec (motive_2 := fun as bs _ => as = bs) with
  | refl => rfl
  | expand hexp => simp [TypeAlias.expandsTo] at hexp
  | collapse hexp => simp [TypeAlias.expandsTo] at hexp
  | cong_tcons hl ih => rw [ih]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | nil => rfl
  | cons h1 h2 ih1 ih2 => rw [ih1, ih2]

theorem subst_ground {S : Subst} {ann : LMonoTy} (hg : ann.freeVars = []) :
    LMonoTy.subst S ann = ann := by
  have h : LMonoTy.subst S ann = LMonoTy.subst [] ann :=
    agree_on_freeVars_implies_subst_eq (fun v hv => by rw [hg] at hv; simp at hv)
  rw [h, LMonoTy.subst_of_hasEmptyScopes (by simp [Subst.hasEmptyScopes]) _]

theorem openFull_forAll_nil (mty : LMonoTy) (tys : List LMonoTy) :
    (LTy.forAll [] mty).openFull tys = mty := by
  simp only [LTy.openFull, LTy.boundVars, List.zip_nil_left]
  -- `ofScopes [[]]` is the one-element stack holding the empty scope.
  rw [show Strata.Util.HMaps.ofScopes [([] : List (TyIdentifier × LMonoTy))]
        = [Strata.Util.HMap.empty] from rfl, LMonoTy.subst_single_empty]
  rfl

theorem init_stored_eq {rigid : List TyIdentifier} {mty mtyS : LMonoTy} {tys : List LMonoTy}
    (hground : mty.freeVars = [])
    (h : RigidAnnotCompat [] rigid ((LTy.forAll [] mty).openFull tys) mtyS) : mtyS = mty := by
  obtain ⟨σ, _, hae⟩ := h
  rw [openFull_forAll_nil] at hae; rw [← aliasEquiv_nil_eq hae, subst_ground hground]

theorem writable_nil_eq (ctx : VarCtx) : ctx.writable [] = ctx := by
  rw [VarCtx.writable]; exact List.filter_eq_self.mpr (fun _ _ => rfl)

/-- Statement typing preserves the ambient `rigidTypeVars`: `funcDecl` extends only
    the factory functions and `typeDecl` only the known types, neither touching the
    rigid set; every other constructor leaves `C` unchanged. (Local copy of Strata's
    `StatementHasType'_rigid_eq`, whose file is not imported here.) -/
theorem stmtHasType_rigid_eq {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {L : List String} {s : Statement}
    (h : StatementHasTypeA P C Γ L s C' Γ') : C'.rigidTypeVars = C.rigidTypeVars := by
  cases h with
  | cmd => rfl
  | block => rfl
  | ite_det => rfl
  | ite_nondet => rfl
  | loop => rfl
  | exit => rfl
  | funcDecl _ _ _ decl func md _ h_nrec h_func _ =>
    simp only [LContext.addFactoryFunction]; split <;> rfl
  | typeDecl _ C0' _ _ tc md _ h_add _ =>
    simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at h_add
    split at h_add
    · simp only [reduceCtorEq] at h_add
    · injection h_add with h_add_eq; rw [← h_add_eq]

/-- Every free variable of a `genLMonoTy tvars`-reachable type lies in `tvars`:
    from `genLMonoTy_support` we get `allFtvarsIn tvars mty`, and `allFtvarsIn_freeVars`
    turns that into a `freeVars ⊆ tvars` statement. -/
theorem freeVars_subset_of_reachable {mty : LMonoTy} {tvars : List TyIdentifier} {n : Nat}
    (h : mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n)) :
    ∀ v ∈ mty.freeVars, v ∈ tvars :=
  allFtvarsIn_freeVars ((genLMonoTy_support tvars n mty).mp h).2.2

/-- **The rigid pin (init case).** When every free variable of the (monomorphic)
    annotation `mty` is rigid, `RigidAnnotCompat` forces the stored type `mtyS` to
    equal `mty` — no groundness needed. The witnessing `σ` is the identity on rigid
    variables, so it fixes `mty` (all of whose free vars are rigid), and the residual
    `AliasEquiv [] (subst σ mty) mtyS` collapses to `mtyS = mty`. -/
theorem init_stored_eq_rigid {rigid : List TyIdentifier} {mty mtyS : LMonoTy} {tys : List LMonoTy}
    (hrigid : ∀ v ∈ mty.freeVars, v ∈ rigid)
    (h : RigidAnnotCompat [] rigid ((LTy.forAll [] mty).openFull tys) mtyS) : mtyS = mty := by
  obtain ⟨σ, hσrigid, hae⟩ := h
  rw [openFull_forAll_nil] at hae
  -- `σ` is identity on rigid vars, hence on every free var of `mty`.
  have hfix : LMonoTy.subst [σ] mty = mty := by
    have hpt : LMonoTy.subst [σ] mty = LMonoTy.subst [] mty :=
      agree_on_freeVars_implies_subst_eq (fun v hv => by
        rw [hσrigid v (hrigid v hv), LMonoTy.subst_of_hasEmptyScopes (by simp [Subst.hasEmptyScopes]) _])
    rw [hpt, LMonoTy.subst_of_hasEmptyScopes (by simp [Subst.hasEmptyScopes]) _]
  rw [hfix] at hae
  exact (aliasEquiv_nil_eq hae).symm

-- ── Residual shape side condition (`InGenShape`) ────────────────────────────
-- Recursive `Prop`-valued functions (NOT inductive relations). Two facts the
-- generator fixes and the spec leaves free: metadata `default`, and monomorphic
-- `init` annotations. Everything else the generator now reaches (labels via
-- `String.arbitrary`, `typeDecl` bounds via sampling, `init` stored type via the
-- rigid context). Procedure `call` is admissible here (its extra recipe/σ
-- conditions live in `CallOk`).

mutual
/-- The metadata/annotation shape the generator emits, recursively over the tree. -/
def InGenShape : Statement → Prop
  | .cmd (CmdExt.cmd (.init _ (.forAll [] _) _ md)) => md = default
  | .cmd (CmdExt.cmd (.init _ _ _ _)) => False          -- polymorphic annotation: unreachable
  | .cmd (CmdExt.cmd (.set _ _ md)) => md = default
  | .cmd (CmdExt.cmd (.assert _ _ md)) => md = default
  | .cmd (CmdExt.cmd (.assume _ _ md)) => md = default
  | .cmd (CmdExt.cmd (.cover _ _ md)) => md = default
  | .cmd (CmdExt.call _ _ md) => md = default
  | .block _ body md => md = default ∧ InGenShapeList body
  | .ite _ t e md => md = default ∧ InGenShapeList t ∧ InGenShapeList e
  | .loop _ _ _ body md => md = default ∧ InGenShapeList body
  | .exit _ md => md = default
  | .funcDecl _ md => md = default
  | .typeDecl _ md => md = default

/-- `InGenShape` lifted to a statement list. -/
def InGenShapeList : List Statement → Prop
  | [] => True
  | s :: ss => InGenShape s ∧ InGenShapeList ss
end

-- ── Residual alphabet/size side condition (`AlphabetOk`) at size `n` ─────────

mutual
/-- The identifier-alphabet + size kernel, recursively over the tree, at size `n`.
    Names lie in their generator's support (dodging keywords where relevant), and
    each generated list is within the budget available at its nesting depth. -/
def AlphabetOk (tvars : List TyIdentifier) : Nat → Statement → Prop
  | n, .cmd (CmdExt.cmd (.init x (.forAll [] mty) _ _)) =>
      x.name ∈ SetGen.support (NonEmptyString.arbitrary (G := SetGen.Set)) ∧
      dodgeKeyword x.name = x.name ∧
      mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n)
  | _, .cmd (CmdExt.cmd (.init _ _ _ _)) => True
  | _, .cmd (CmdExt.cmd (.set _ _ _)) => True
  | _, .cmd (CmdExt.cmd (.assert l _ _)) =>
      l ∈ SetGen.support (String.arbitrary (G := SetGen.Set))
  | _, .cmd (CmdExt.cmd (.assume l _ _)) =>
      l ∈ SetGen.support (String.arbitrary (G := SetGen.Set))
  | _, .cmd (CmdExt.cmd (.cover l _ _)) =>
      l ∈ SetGen.support (String.arbitrary (G := SetGen.Set))
  | _, .cmd (CmdExt.call _ _ _) => True
  | 0, .block .. => False
  | (n+1), .block label body _ =>
      label ∈ SetGen.support (genIdentName (G := SetGen.Set)) ∧
      body.length ≤ n + 1 ∧ AlphabetOkList tvars n body
  | 0, .ite .. => False
  | (n+1), .ite _ t e _ =>
      t.length ≤ n + 1 ∧ e.length ≤ n + 1 ∧
      AlphabetOkList tvars n t ∧ AlphabetOkList tvars n e
  | 0, .loop .. => False
  | (n+1), .loop _ _ invs body _ =>
      invs.length ≤ n + 1 ∧ (∀ p ∈ invs, p.1 ∈ SetGen.support (genIdentName (G := SetGen.Set))) ∧
      body.length ≤ n + 1 ∧ AlphabetOkList tvars n body
  | _, .exit _ _ => True
  | n, .funcDecl decl _ => decl ∈ SetGen.support (genDecl (G := SetGen.Set) octx n)
  | n, .typeDecl tc _ =>
      tc.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) ∧ tc.params.length ≤ n ∧
      (∀ s ∈ tc.params, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))

/-- `AlphabetOk` lifted to a statement list at size `n`. -/
def AlphabetOkList (tvars : List TyIdentifier) : Nat → List Statement → Prop
  | _, [] => True
  | n, s :: ss => AlphabetOk tvars n s ∧ AlphabetOkList tvars n ss
end

-- ── Scope threading for the call recipe ─────────────────────────────────────

/-- The output variable scope of a statement, as the generator threads it. Only
    `init` extends the scope (with its fresh variable); every other constructor —
    including a *well-typed* `call`, whose arguments are all already in scope, so its
    `init` chain is empty — leaves the scope unchanged. This mirrors the `ctx'` the
    completeness proof produces at each node, and is what `CallOkList` threads so a
    nested `call`'s `outTargets` are evaluated at the scope reached there. -/
def stepCtx (ctx : VarCtx) : Statement → VarCtx
  | .cmd (CmdExt.cmd (.init x (.forAll [] mty) _ _)) => ctx.insert ⟨x.name, ()⟩ mty
  | _ => ctx

/-- The output scope of a whole chain: fold `stepCtx` left-to-right. -/
def stepCtxList (ctx : VarCtx) : List Statement → VarCtx
  | [] => ctx
  | s :: ss => stepCtxList (stepCtx ctx s) ss

-- ── Residual call-recipe side condition (`CallOk`), scope-threaded ──────────

mutual
/-- The call-recipe side condition, threaded through the evolving scope `ctx` and at
    size `n`. A `.cmd (.call …)` is admissible only when its argument list is exactly
    the generator's recipe for *some* sampled type-instantiation `σvals` (with
    `σ := s.typeArgs.zip σvals`): `mkArgs s.M (outTargets [] ctx (substSig σ s.O)) exprs`
    for some callee `s` and by-value inputs `exprs` — with the generator's guard (usable
    instantiated in-out block, distinct write keys), the inputs reachable by `genLExpr`
    at the callee's *instantiated* input types, and no fresh `init`s required (a
    well-typed call has all names in scope, so the emitted group is the bare call and
    the output scope is `ctx`). `hσvals` places `σvals` in the sampling step's support.
    `True` on every non-call leaf; nested bodies recurse with the body's own scope. -/
def CallOk (procs : ProcSigCtx) (ctx : VarCtx) (n : Nat) : Statement → Prop
  | .cmd (CmdExt.call pname args _) =>
      ∃ (s : ProcSig) (σvals : List LMonoTy) (exprs : List Expression.Expr),
        s ∈ procs ∧
        s.pname = pname ∧
        σvals ∈ SetGen.support
          (s.typeArgs.mapM (fun _ =>
            if hg : (generableTypesFromCtx ctx.values [] octx).length > 0 then
              elements (generableTypesFromCtx ctx.values [] octx)
                (by apply List.ne_nil_of_length_pos; assumption)
            else pure (.bool : LMonoTy)) : SetGen.Set (List LMonoTy)) ∧
        args = StrataGenerators.Stmt.mkArgs s.M
          (outTargets [] ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)) exprs ∧
        (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).all (usableName [] ctx) = true ∧
        (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M
          ++ outTargets [] ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)).keys.Nodup ∧
        List.Forall₂
          (fun e τ => e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n τ))
          exprs (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.I).values ∧
        (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).filter (needsInit ctx)
          ++ (outTargets [] ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)).filter
                (needsInit ctx) = []
  | .cmd (CmdExt.cmd _) => True
  -- Nested bodies are generated one size smaller, so their calls' inputs are
  -- reachable at `n-1` (mirroring `AlphabetOk` and `genStmt (size+1)` → `size`).
  | .block _ body _ => CallOkList procs ctx (n - 1) body
  | .ite _ t e _ => CallOkList procs ctx (n - 1) t ∧ CallOkList procs ctx (n - 1) e
  | .loop _ _ _ body _ => CallOkList procs ctx (n - 1) body
  | .exit _ _ => True
  | .funcDecl _ _ => True
  | .typeDecl _ _ => True

/-- `CallOk` lifted to a statement chain, threading the scope with `stepCtx`. -/
def CallOkList (procs : ProcSigCtx) (ctx : VarCtx) (n : Nat) : List Statement → Prop
  | [] => True
  | s :: ss => CallOk procs ctx n s ∧ CallOkList procs (stepCtx ctx s) n ss
end

-- ── Structural size witness ─────────────────────────────────────────────────

mutual
/-- A size at which `genStmt` can reach `s` (given the alphabet/shape conditions):
    large enough to bound this node's own generated lists and, one smaller, its
    nested bodies. This is the `∃ n` witness discharged at the top level, so the
    theorem carries no explicit `≤ n` budget premise. -/
def stmtDepth : Statement → Nat
  | .cmd _ => 0
  | .block _ body _ => stmtListDepth body + 1
  | .ite _ t e _ => max (stmtListDepth t) (stmtListDepth e) + 1
  | .loop _ _ invs body _ => max invs.length (stmtListDepth body) + 1
  | .exit _ _ => 0
  | .funcDecl _ _ => 0
  | .typeDecl tc _ => tc.params.length

/-- The size witness for a chain: bounds both the list length and each element. -/
def stmtListDepth : List Statement → Nat
  | [] => 0
  | s :: ss => max (max (stmtDepth s) (stmtListDepth ss)) ((s :: ss).length)
end

-- ── Command-statement completeness ──────────────────────────────────────────

/-- **Completeness for a single `.cmd (CmdExt.cmd c)` statement.** A well-typed
    command in generator shape (`InGenShape`) satisfying the alphabet kernel
    (`AlphabetOk`) is produced by `genStmt … n` at the exact statement and output
    scope. The rigid context (`hRigid : C.rigidTypeVars = tvars`) pins an `init`'s
    stored type to its annotation via `init_stored_eq_rigid`, so no groundness
    premise is needed. Expressions are covered by `hExprC`. -/
theorem genCmdStmt_complete_spec (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (Γ' : TContext Unit)
    (c : Cmd Expression)
    (hRigid : C.rigidTypeVars = tvars)
    (hwt : CmdHasTypeA C (procToTCtx ctx) c Γ')
    (hshape : InGenShape (.cmd (CmdExt.cmd c)))
    (hok : AlphabetOk (octx := octx) tvars n (.cmd (CmdExt.cmd c)))
    (hExprC : GenLExprComplete ctx.toFVarCtx octx tvars n) :
    ∃ ctx', TContext.Equiv (T := CoreLParams) (procToTCtx ctx') Γ' ∧
      ctx' = stepCtx ctx (.cmd (CmdExt.cmd c)) ∧
      (⟨[Stmt.cmd (CmdExt.cmd c)], C, ctx'⟩ : GenStmtResult) ∈
        SetGen.support (genStmt (G := SetGen.Set) octx tvars [] procs labels C ctx [] n) := by
  -- Reduce the goal to membership in `genCmd`'s support via the `genCmdStmt` wrapper
  -- and the `genCmdStmt_mem` lifting into `genStmt`.
  have hlift : ∀ (r : GenCmdResult),
      r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars [] ctx n) →
      (⟨[Stmt.cmd (CmdExt.cmd r.cmd)], C, r.outCtx⟩ : GenStmtResult) ∈
        SetGen.support (genStmt (G := SetGen.Set) octx tvars [] procs labels C ctx [] n) := by
    intro r hr
    refine genCmdStmt_mem procs C ctx n _ ?_
    simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨r, hr, rfl⟩
  cases hwt with
  | init_det x xty e mty tys md Δ hfresh hnovar hlen hcompat hwk hexpr hequiv =>
    -- Shape: annotation `.forAll [] mtyA`; Alphabet: name reachable + dodges keyword + mty reachable.
    obtain ⟨mtyA, rfl, hmdc⟩ : ∃ m, xty = .forAll [] m ∧ md = default := by
      cases xty with
      | forAll bs body =>
        cases bs with
        | nil => exact ⟨body, rfl, hshape⟩
        | cons _ _ => exact absurd hshape (by simp [InGenShape])
    obtain ⟨hname, hdodge, hmtyReach⟩ := hok
    -- `hRigid` + reachability pin the stored type to the annotation.
    have hrigidfv : ∀ v ∈ mtyA.freeVars, v ∈ C.rigidTypeVars := by
      rw [hRigid]; exact freeVars_subset_of_reachable hmtyReach
    have hstored : mty = mtyA := init_stored_eq_rigid hrigidfv hcompat
    subst hstored; subst hmdc
    obtain ⟨nm, u⟩ := x; cases u
    refine ⟨ctx.insert ⟨nm, ()⟩ mty,
      (procToTCtx_insert ctx ⟨nm, ()⟩ mty).trans hequiv.symm, rfl, ?_⟩
    exact hlift ⟨.init ⟨nm,()⟩ (.forAll [] mty) (.det e) default, ctx.insert ⟨nm,()⟩ mty⟩ (by
      rw [genCmd_support_iff]; refine Or.inl ?_
      simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨nm, freshName_reach ctx ⟨nm,()⟩ hname hdodge (procToTCtx_fresh_rev ctx ⟨nm,()⟩ hfresh),
        mty, hmtyReach, e, hExprC mty e hexpr, rfl⟩)
  | init_nondet x xty mty tys md Δ hfresh hlen hcompat hwk hequiv =>
    obtain ⟨mtyA, rfl, hmdc⟩ : ∃ m, xty = .forAll [] m ∧ md = default := by
      cases xty with
      | forAll bs body =>
        cases bs with
        | nil => exact ⟨body, rfl, hshape⟩
        | cons _ _ => exact absurd hshape (by simp [InGenShape])
    obtain ⟨hname, hdodge, hmtyReach⟩ := hok
    have hrigidfv : ∀ v ∈ mtyA.freeVars, v ∈ C.rigidTypeVars := by
      rw [hRigid]; exact freeVars_subset_of_reachable hmtyReach
    have hstored : mty = mtyA := init_stored_eq_rigid hrigidfv hcompat
    subst hstored; subst hmdc
    obtain ⟨nm, u⟩ := x; cases u
    refine ⟨ctx.insert ⟨nm, ()⟩ mty,
      (procToTCtx_insert ctx ⟨nm, ()⟩ mty).trans hequiv.symm, rfl, ?_⟩
    exact hlift ⟨.init ⟨nm,()⟩ (.forAll [] mty) .nondet default, ctx.insert ⟨nm,()⟩ mty⟩ (by
      rw [genCmd_support_iff]; refine Or.inr (Or.inl ?_)
      simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨nm, freshName_reach ctx ⟨nm,()⟩ hname hdodge (procToTCtx_fresh_rev ctx ⟨nm,()⟩ hfresh),
        mty, hmtyReach, rfl⟩)
  | set_det x mty e md Δ hfind hexpr hequiv =>
    have hmdc : md = default := hshape
    have hmem : List.Mem (x, mty) (ctx.writable []) := by
      rw [writable_nil_eq]; exact Map.find?_mem ctx x mty (procToTCtx_find_rev ctx x mty hfind)
    refine ⟨ctx, hequiv.symm, rfl, ?_⟩
    have := hlift ⟨.set x (.det e) default, ctx⟩ ?_
    · subst hmdc; exact this
    · rw [genCmd_support_iff]; refine Or.inr (Or.inr (Or.inl ⟨List.length_pos_of_mem hmem, ?_⟩))
      simp only [genSetDet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff]
      refine ⟨(x, mty), ?_, e, hExprC mty e hexpr, rfl⟩
      rw [show List.filter (fun p => !([].contains p.1)) ctx = ctx from List.filter_eq_self.mpr (fun _ _ => rfl)]
      exact Map.find?_mem ctx x mty (procToTCtx_find_rev ctx x mty hfind)
  | set_nondet x mty md Δ hfind hequiv =>
    have hmdc : md = default := hshape
    have hmem : List.Mem (x, mty) (ctx.writable []) := by
      rw [writable_nil_eq]; exact Map.find?_mem ctx x mty (procToTCtx_find_rev ctx x mty hfind)
    refine ⟨ctx, hequiv.symm, rfl, ?_⟩
    have := hlift ⟨.set x .nondet default, ctx⟩ ?_
    · subst hmdc; exact this
    · rw [genCmd_support_iff]; refine Or.inr (Or.inr (Or.inr (Or.inl ⟨List.length_pos_of_mem hmem, ?_⟩)))
      simp only [genSetNondet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff]
      refine ⟨(x, mty), ?_, rfl⟩
      rw [show List.filter (fun p => !([].contains p.1)) ctx = ctx from List.filter_eq_self.mpr (fun _ _ => rfl)]
      exact Map.find?_mem ctx x mty (procToTCtx_find_rev ctx x mty hfind)
  | assert l e md Δ hexpr hequiv =>
    have hmdc : md = default := hshape
    have hlreach : l ∈ SetGen.support (String.arbitrary (G := SetGen.Set)) := hok
    refine ⟨ctx, hequiv.symm, rfl, ?_⟩
    have := hlift ⟨.assert l e default, ctx⟩ ?_
    · subst hmdc; exact this
    · rw [genCmd_support_iff]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨l, hlreach, e, hExprC .bool e hexpr, rfl⟩
  | assume l e md Δ hexpr hequiv =>
    have hmdc : md = default := hshape
    have hlreach : l ∈ SetGen.support (String.arbitrary (G := SetGen.Set)) := hok
    refine ⟨ctx, hequiv.symm, rfl, ?_⟩
    have := hlift ⟨.assume l e default, ctx⟩ ?_
    · subst hmdc; exact this
    · rw [genCmd_support_iff]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
      simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨l, hlreach, e, hExprC .bool e hexpr, rfl⟩
  | cover l e md Δ hexpr hequiv =>
    have hmdc : md = default := hshape
    have hlreach : l ∈ SetGen.support (String.arbitrary (G := SetGen.Set)) := hok
    refine ⟨ctx, hequiv.symm, rfl, ?_⟩
    have := hlift ⟨.cover l e default, ctx⟩ ?_
    · subst hmdc; exact this
    · rw [genCmd_support_iff]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
      simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨l, hlreach, e, hExprC .bool e hexpr, rfl⟩

/-- A reachable, non-enclosing label is in `genFreshLabel`'s support (discharges the
    `block` rule's `label ∉ L` premise against the generator's freshness filter). -/
theorem genFreshLabel_complete (labels : List String) (label : String)
    (hreach : label ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hfresh : label ∉ labels) :
    label ∈ SetGen.support (genFreshLabel (G := SetGen.Set) labels) := by
  simp only [genFreshLabel, mem_support_bind_iff]
  exact ⟨label, hreach, by simp only [mem_support_ite_iff, mem_support_pure_iff]; exact Or.inr ⟨hfresh, trivial⟩⟩

/-- `genFreshLabel_complete`, and `mem_support_genIdentName_iff` discharges its hypothesis on
    reachability from syntax. All three hypotheses are then decidable conditions on `label`. It is
    a bare Core identifier. It is not a reserved keyword. It is different from each label that
    encloses it. -/
theorem genFreshLabel_complete_of_syntactic (labels : List String) (label : String)
    (hsyn : StrataGenerators.Function.IsGenIdentName label)
    (hnotkw : isReservedKeyword label = false)
    (hfresh : label ∉ labels) :
    label ∈ SetGen.support (genFreshLabel (G := SetGen.Set) labels) :=
  genFreshLabel_complete labels label
    (StrataGenerators.Function.mem_support_genIdentName_of_syntactic hsyn hnotkw) hfresh

-- ── Mutual statement / statement-chain completeness ─────────────────────────

/-- **Completeness of `genStmt` / `genStmtChain`, indexed by the typing derivation.**
    Every well-typed statement in generator shape (`InGenShape`), satisfying the
    alphabet kernel (`AlphabetOk` at some size `n`) and the call recipe (`CallOk`),
    is in `genStmt`'s support at the exact statement and (via `procToTCtx`) the exact
    output scope. Procedure calls are *included*: `CallOk` carries the callee's
    membership `s ∈ procs` (the concrete form of the `ProcSigComplete` reverse
    correspondence) together with its recipe shape, guard, and input reachability.
    `immutableVars` is fixed to `[]` (vacuous at the statement level). -/
theorem spec_complete (P : Program) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (labels : List String)
    (s : Statement) (C' : LContext CoreLParams) (Γ' : TContext Unit)
    (h : StatementHasTypeA P C Γ labels s C' Γ')
    (hExprC : ∀ d (ctx : VarCtx), GenLExprComplete ctx.toFVarCtx octx tvars d)
    (hFuncReach : ∀ d C Γ (func : Function), FuncHasTypeA C Γ func →
      func ∈ SetGen.support (genFunction (G := SetGen.Set) [] octx d)) :
    ∀ (ctx : VarCtx) (n : Nat), C.rigidTypeVars = tvars →
      TContext.Equiv (T := CoreLParams) Γ (procToTCtx ctx) →
      InGenShape s → AlphabetOk (octx := octx) tvars n s → CallOk (octx := octx) (tvars := tvars) procs ctx n s →
      ∃ ctx', TContext.Equiv (T := CoreLParams) Γ' (procToTCtx ctx') ∧
        ctx' = stepCtx ctx s ∧
        (⟨[s], C', ctx'⟩ : GenStmtResult) ∈
          SetGen.support (genStmt (G := SetGen.Set) octx tvars [] procs labels C ctx [] n) := by
  induction h using StatementHasType'.rec (motive_2 := fun C Γ L ss C' Γ' _ =>
    ∀ (ctx : VarCtx) (n : Nat), C.rigidTypeVars = tvars →
      TContext.Equiv (T := CoreLParams) Γ (procToTCtx ctx) →
      InGenShapeList ss → AlphabetOkList (octx := octx) tvars n ss → CallOkList (octx := octx) (tvars := tvars) procs ctx n ss →
      ∃ ctx', TContext.Equiv (T := CoreLParams) Γ' (procToTCtx ctx') ∧
        ctx' = stepCtxList ctx ss ∧
        ((ss, C', ctx') : List Statement × LContext CoreLParams × VarCtx) ∈
          SetGen.support (genStmtChain (G := SetGen.Set) octx tvars [] procs L C ctx [] n ss.length)) with
  | cmd C Γ Γ2 L c Δ hc hequiv =>
    intro ctx n hRig hΓ hnf hok hcall
    cases cmdExtHasTypeA_equiv_congr hc hΓ.symm with
    | cmd Γ3 c2 hcmd =>
      obtain ⟨ctx', hctx', hstep, hmem⟩ :=
        genCmdStmt_complete_spec procs L C ctx n _ c2 hRig hcmd hnf hok (hExprC n ctx)
      exact ⟨ctx', hequiv.trans hctx'.symm, hstep, hmem⟩
    | call pname callArgs proc md σ Δ2 hfind hInLen hOutLen hLhs hIn hOut hInout hequiv2 =>
      -- Shape gives `md = default`; `CallOk` gives membership + recipe + guard + empty chain.
      have hmdc : md = default := hnf
      subst hmdc
      obtain ⟨s, σvals, exprs, hsmem, hpname, hσvals, hargs, hMusable, hNodup, hForall, hEmpty⟩ := hcall
      refine ⟨ctx, hequiv.trans hequiv2, rfl, ?_⟩
      -- The emitted group is `initChain (…) ++ [call]`; the chain is empty (`hEmpty`),
      -- and the output scope `insertAllCtx ctx [] = ctx`.
      refine genCallStmt_mem procs C ctx n _ ?_
      have hmem := genCallStmt_mem_complete (octx := octx) (tvars := tvars)
        (immutableVars := []) procs C ctx n s hsmem σvals hσvals exprs hMusable hNodup hForall
      rw [hEmpty] at hmem
      simpa [hargs, StrataGenerators.Stmt.initChain, StrataGenerators.Stmt.insertAllCtx, hpname] using hmem
  | exit C Γ L label md Δ hmem hequiv =>
    intro ctx n hRig hΓ hnf hok hcall
    have hmdc : md = default := hnf
    subst hmdc
    refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
    refine genExitStmt_mem procs C ctx n _ ?_
    simp only [genExitStmt]
    cases L with
    | nil => exact absurd hmem (by simp)
    | cons hd tl =>
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff]
      exact ⟨label, hmem, rfl⟩
  | funcDecl C Γ L decl func md Δ hrec hfunc hequiv =>
    intro ctx n hRig hΓ hnf hok hcall
    have hmdc : md = default := hnf
    subst hmdc
    have hdecl : decl ∈ SetGen.support (genDecl (G := SetGen.Set) octx n) := hok
    refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
    refine genFuncDeclStmt_mem procs C ctx n _ ?_
    simp only [genFuncDeclStmt, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨decl, hdecl, func, hFuncReach n C (procToTCtx ctx) func (funcHasTypeA_ctx_irrel hfunc), rfl⟩
  | typeDecl C C' Γ L tc md Δ hoktc hequiv =>
    intro ctx n hRig hΓ hnf hok hcall
    have hmdc : md = default := hnf
    subst hmdc
    obtain ⟨hname_tc, hlen, hparams⟩ := hok
    refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
    refine genTypeDeclStmt_mem procs C ctx n _ ?_
    simp only [genTypeDeclStmt, mem_support_bind_iff]
    refine ⟨tc, genTypeConstructor_complete n tc hname_tc hlen hparams, ?_⟩
    rw [hoktc]; simp only [mem_support_pure_iff]
  | block C Γ Cb Γb L label body md Δ hlabel hbody hequiv ihbody =>
    intro ctx n hRig hΓ hnf hok hcall
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨hlabelname, hlen, hokbody⟩ := hok
      obtain ⟨hmdc, hnfbody⟩ := hnf
      subst hmdc
      obtain ⟨ctxb, hctxb, _, hbodymem⟩ := ihbody ctx m hRig hΓ hnfbody hokbody hcall
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact block_mem procs C ctx m label body Cb ctxb body.length hlen hbodymem
        (genFreshLabel_complete L label hlabelname hlabel)
  | ite_det C Γ Ct Γt Ce Γe L cond thenb elseb md Δ hcond hthen helse hequiv iht ihe =>
    intro ctx n hRig hΓ hnf hok hcall
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨htlen, helen, hokt, hoke⟩ := hok
      obtain ⟨hmdc, hnft, hnfe⟩ := hnf
      subst hmdc
      obtain ⟨hcallt, hcalle⟩ := hcall
      obtain ⟨ctxt, hctxt, _, htmem⟩ := iht ctx m hRig hΓ hnft hokt hcallt
      obtain ⟨ctxe, hctxe, _, hemem⟩ := ihe ctx m hRig hΓ hnfe hoke hcalle
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact ite_det_mem procs C ctx m cond thenb elseb Ct ctxt Ce ctxe thenb.length elseb.length
        htlen helen (hExprC (m+1) ctx .bool cond hcond) htmem hemem
  | ite_nondet C Γ Ct Γt Ce Γe L thenb elseb md Δ hthen helse hequiv iht ihe =>
    intro ctx n hRig hΓ hnf hok hcall
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨htlen, helen, hokt, hoke⟩ := hok
      obtain ⟨hmdc, hnft, hnfe⟩ := hnf
      subst hmdc
      obtain ⟨hcallt, hcalle⟩ := hcall
      obtain ⟨ctxt, hctxt, _, htmem⟩ := iht ctx m hRig hΓ hnft hokt hcallt
      obtain ⟨ctxe, hctxe, _, hemem⟩ := ihe ctx m hRig hΓ hnfe hoke hcalle
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact ite_nondet_mem procs C ctx m thenb elseb Ct ctxt Ce ctxe thenb.length elseb.length
        htlen helen htmem hemem
  | loop C Γ Cb Γb L guard measure invs body md Δ hg hm hi hbody hequiv ihbody =>
    intro ctx n hRig hΓ hnf hok hcall
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ mm =>
      obtain ⟨hinvlen, hinvname, hblen, hokbody⟩ := hok
      obtain ⟨hmdc, hnfbody⟩ := hnf
      subst hmdc
      obtain ⟨ctxb, hctxb, _, hbodymem⟩ := ihbody ctx mm hRig hΓ hnfbody hokbody hcall
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      refine loop_mem procs C ctx mm guard measure invs body Cb ctxb body.length hblen ?_ ?_ ?_ hbodymem
      · exact genCondOrNondet_complete (mm+1) ctx guard (fun g hgd => hExprC (mm+1) ctx .bool g (hg g hgd))
      · exact genOptMeasure_complete (mm+1) ctx measure (fun mmm hmm => hExprC (mm+1) ctx .int mmm (hm mmm hmm))
      · exact genInvariants_complete (mm+1) ctx invs hinvlen
          (fun p hp => ⟨hinvname p hp, hExprC (mm+1) ctx .bool p.2 (hi p hp)⟩)
  | nil C Γ L Δ hequiv =>
    rename_i ctx n hRig hΓ _ _ _
    exact ⟨ctx, hequiv.trans hΓ, rfl, genStmtChain_nil_mem procs C ctx n⟩
  | cons C C1 C2 Γ Γ1 Γ2 L s ss hs hss ihs ihss =>
    rename_i ctx n hRig hΓ hnf hok hcall
    obtain ⟨hnfs, hnfss⟩ := hnf
    obtain ⟨hoks, hokss⟩ := hok
    obtain ⟨hcalls, hcallss⟩ := hcall
    -- The head produces `[s]` at scope `ctx1 = stepCtx ctx s` (pinned by `ihs`); the
    -- tail continues from there, so its threaded `CallOkList`/scope line up exactly.
    obtain ⟨ctx1, hctx1, hstep1, hsmem⟩ := ihs ctx n hRig hΓ hnfs hoks hcalls
    subst hstep1
    -- `hRig` transfers to `C1`: statement typing preserves `rigidTypeVars`
    -- (`funcDecl`/`typeDecl` extend only the factory/known-types).
    have hRig1 : C1.rigidTypeVars = tvars := (stmtHasType_rigid_eq hs).trans hRig
    obtain ⟨ctx2, hctx2, hstep2, hssmem⟩ := ihss (stepCtx ctx s) n hRig1 hctx1 hnfss hokss hcallss
    refine ⟨ctx2, hctx2, ?_, ?_⟩
    · show ctx2 = stepCtxList ctx (s :: ss); rw [hstep2]; rfl
    · have := genStmtChain_cons_mem procs C ctx n ss.length ⟨[s], C1, stepCtx ctx s⟩ ss C2 ctx2 hsmem hssmem
      simpa using this

end StrataGenerators.Stmt.SpecComplete
