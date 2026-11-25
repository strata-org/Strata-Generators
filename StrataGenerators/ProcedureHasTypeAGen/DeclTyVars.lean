import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.CmdHasTypeAGenSound
import Strata.Languages.Core.Procedure

open Lambda LExpr RandomChoice Core Imperative TypeSpec
open StrataGenerators.Stmt StrataGenerators.Function

/-!
# The type variables of the declarations in a generated body

`ProcWellTyped.declTyVarsBound` asks that the declared type of each local and each type argument of
each call in a body use only the type parameters of the procedure. `genStmtChain` builds the body
over the type parameters `tvars` of the procedure. This file shows, by recursion on the generated
statements, that every declared type and every call type argument has its type variables in `tvars`.
The recursion carries two facts. Every type in the scope has its type variables in `tvars`, and
every callable procedure mentions only its own type parameters in its in-out and out-only blocks.
-/

namespace StrataGenerators.Procedure

variable {octx : OpCtx} {tvars : List TyIdentifier} {pctx : PolyOpCtx}
  {immutableVars : List (Identifier Unit)} {maxStmtSeqLen : Nat}

-- ── Types over bounded type variables ────────────────────────────────────

/-- Instantiating the types of a block over the callee's type parameters by values within `tvars`
    gives types within `tvars`. -/
theorem substSig_values_tyVarsWithin (typeArgs : List TyIdentifier) (σvals : List LMonoTy)
    (hlen : typeArgs.length ≤ σvals.length) (hσ : ∀ t ∈ σvals, tyVarsWithin tvars t = true)
    (block : @LMonoTySignature Unit)
    (hblock : ∀ ty ∈ block.values, ∀ v ∈ ty.freeVars, v ∈ typeArgs) :
    ∀ ty ∈ (substSig (typeArgs.zip σvals) block).values, tyVarsWithin tvars ty = true := by
  intro ty hty
  rw [substSig_values, List.mem_map] at hty
  obtain ⟨ty0, hty0, rfl⟩ := hty
  exact subst_zip_tyVarsWithin typeArgs σvals hlen hσ ty0 (hblock ty0 hty0)

/-- A call that instantiates the callee's type parameters by values within `tvars` stores type
    arguments within `tvars`. -/
theorem callTyArgs_tyVarsWithin (typeArgs : List TyIdentifier) (σvals : List LMonoTy)
    (hlen : typeArgs.length ≤ σvals.length) (hσ : ∀ t ∈ σvals, tyVarsWithin tvars t = true) :
    ∀ lty ∈ (callTyArgs typeArgs (typeArgs.zip σvals)).getD [],
      tyVarsWithin tvars lty.toMonoTypeUnsafe = true := by
  intro lty hlty
  simp only [callTyArgs, Option.getD_some, List.mem_map] at hlty
  obtain ⟨a, ha, rfl⟩ := hlty
  have hvars : ∀ v ∈ (LMonoTy.ftvar a).freeVars, v ∈ typeArgs := by
    intro v hv
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    exact hv ▸ ha
  exact subst_zip_tyVarsWithin typeArgs σvals hlen hσ (.ftvar a) hvars

-- ── Statement lists whose declarations stay within `tvars` ───────────────

/-- Every declared type and every call type argument of the commands of the statements `ss` has its
    type variables in `tvars`. -/
def StmtsTyVarsWithin (tvars : List TyIdentifier) (ss : List Statement) : Prop :=
  ∀ c ∈ stmtsCmds ss, ∀ v ∈ cmdCollect (fun _ => []) LMonoTy.freeVars c, v ∈ tvars

/-- A generated group declares only within `tvars`, and it leaves a scope whose types have their
    type variables in `tvars`. -/
def DeclsWithin (tvars : List TyIdentifier) (stmts : List Statement) (outCtx : VarCtx) : Prop :=
  StmtsTyVarsWithin tvars stmts ∧ ∀ ty ∈ outCtx.values, tyVarsWithin tvars ty = true

/-- The empty statement list declares nothing. -/
theorem StmtsTyVarsWithin.nil : StmtsTyVarsWithin tvars [] := by
  intro c hc
  simp only [stmtsCmds, List.not_mem_nil] at hc

/-- A concatenation of statement lists declares only within `tvars` when each part does. -/
theorem StmtsTyVarsWithin.append {xs ys : List Statement} (hx : StmtsTyVarsWithin tvars xs)
    (hy : StmtsTyVarsWithin tvars ys) : StmtsTyVarsWithin tvars (xs ++ ys) := by
  intro c hc
  rw [stmtsCmds_append, List.mem_append] at hc
  rcases hc with h | h
  · exact hx c h
  · exact hy c h

/-- A command statement declares only within `tvars` when its command does. -/
theorem StmtsTyVarsWithin.cmd {c : Command}
    (h : ∀ v ∈ cmdCollect (fun _ => []) LMonoTy.freeVars c, v ∈ tvars) :
    StmtsTyVarsWithin tvars [Stmt.cmd c] := by
  intro c' hc'
  simp only [stmtsCmds, stmtCmds, List.append_nil, List.mem_singleton] at hc'
  subst hc'
  exact h

/-- A block declares only within `tvars` when its body does. -/
theorem StmtsTyVarsWithin.block {l : String} {body : List Statement}
    {md : MetaData Expression} (h : StmtsTyVarsWithin tvars body) :
    StmtsTyVarsWithin tvars [Stmt.block l body md] := by
  intro c hc
  simp only [stmtsCmds, stmtCmds, List.append_nil] at hc
  exact h c hc

/-- A conditional declares only within `tvars` when both of its branches do. -/
theorem StmtsTyVarsWithin.ite {cond : ExprOrNondet Expression} {thenb elseb : List Statement}
    {md : MetaData Expression} (ht : StmtsTyVarsWithin tvars thenb)
    (he : StmtsTyVarsWithin tvars elseb) :
    StmtsTyVarsWithin tvars [Stmt.ite cond thenb elseb md] := by
  intro c hc
  simp only [stmtsCmds, stmtCmds, List.append_nil, List.mem_append] at hc
  rcases hc with h | h
  · exact ht c h
  · exact he c h

/-- A loop declares only within `tvars` when its body does. -/
theorem StmtsTyVarsWithin.loop {guard : ExprOrNondet Expression} {measure : Option Expression.Expr}
    {invs : List (String × Expression.Expr)} {body : List Statement} {md : MetaData Expression}
    (h : StmtsTyVarsWithin tvars body) :
    StmtsTyVarsWithin tvars [Stmt.loop guard measure invs body md] := by
  intro c hc
  simp only [stmtsCmds, stmtCmds, List.append_nil] at hc
  exact h c hc

/-- An `exit` declares nothing. -/
theorem StmtsTyVarsWithin.exit {l : String} {md : MetaData Expression} :
    StmtsTyVarsWithin tvars [Stmt.exit l md] := by
  intro c hc
  simp only [stmtsCmds, stmtCmds, List.append_nil, List.not_mem_nil] at hc

/-- A type declaration declares no local variable. -/
theorem StmtsTyVarsWithin.typeDecl {tc : TypeConstructor} {md : MetaData Expression} :
    StmtsTyVarsWithin tvars [Stmt.typeDecl tc md] := by
  intro c hc
  simp only [stmtsCmds, stmtCmds, List.append_nil, List.not_mem_nil] at hc

/-- What a command of the core language, other than a call, collects when no expressions count. -/
theorem cmdCollect_noExprs_cmd (c : Cmd Expression) :
    cmdCollect (fun _ => []) LMonoTy.freeVars (CmdExt.cmd c) =
      (Cmd.initTypes c).flatMap (fun ty => ty.toMonoTypeUnsafe.freeVars) := by
  simp only [cmdCollect, CmdExt.initTypes, Statement.cmdTyArgs, List.flatMap_nil, List.append_nil,
    flatMap_const_nil]

/-- A call declares only within `tvars` when its type arguments are within `tvars`. -/
theorem StmtsTyVarsWithin.call {pname : String} {tyArgs : Option (List LTy)}
    {args : List (CallArg Expression)} {md : MetaData Expression}
    (h : ∀ lty ∈ tyArgs.getD [], tyVarsWithin tvars lty.toMonoTypeUnsafe = true) :
    StmtsTyVarsWithin tvars [Statement.call pname tyArgs args md] := by
  refine StmtsTyVarsWithin.cmd fun v hv => ?_
  simp only [cmdCollect, CmdExt.initTypes, Statement.cmdTyArgs, Statement.cmdExprs,
    List.flatMap_nil, List.nil_append, flatMap_const_nil, List.append_nil,
    List.mem_flatMap] at hv
  obtain ⟨lty, hlty, hvl⟩ := hv
  exact mem_of_tyVarsWithin (h lty hlty) hvl

/-- A chain of `init` statements declares only within `tvars` when each declared type is. -/
theorem initChain_tyVarsWithin (news : List (Identifier Unit × LMonoTy))
    (h : ∀ ty ∈ news.map Prod.snd, tyVarsWithin tvars ty = true) :
    StmtsTyVarsWithin tvars (initChain news) := by
  induction news with
  | nil => exact StmtsTyVarsWithin.nil
  | cons p rest ih =>
    have hp : tyVarsWithin tvars p.2 = true := h p.2 (List.mem_cons_self ..)
    have hrest : ∀ ty ∈ rest.map Prod.snd, tyVarsWithin tvars ty = true :=
      fun ty hty => h ty (List.mem_cons_of_mem _ hty)
    have hhead : StmtsTyVarsWithin tvars [Statement.init p.1 (.forAll [] p.2) .nondet default] := by
      refine StmtsTyVarsWithin.cmd fun v hv => ?_
      simp only [cmdCollect_noExprs_cmd, Cmd.initTypes, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, LTy.toMonoTypeUnsafe] at hv
      exact mem_of_tyVarsWithin hp hv
    exact StmtsTyVarsWithin.append hhead (ih hrest)

-- ── The leaf generators ──────────────────────────────────────────────────

/-- A generated command declares only within `tvars`: the type of an `init` comes from
    `genLMonoTy tvars`. -/
theorem genCmd_tyVars (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) {avoid : List String}
    {kt : Lambda.KnownTypes} (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true)
    (r : GenCmdResult)
    (hr : r ∈ SPMF.support
      (genCmd (G := SPMF) octx tvars immutableVars ctx depth pctx avoid kt)) :
    DeclsWithin tvars [Stmt.cmd (CmdExt.cmd r.cmd)] r.outCtx := by
  revert r; show IsSoundFor _ _; walk_genCmd
  all_goals refine And.intro (StmtsTyVarsWithin.cmd ?_) ?_
  all_goals (try split_ifs)
  all_goals first
    | (intro v hv
       simp only [cmdCollect_noExprs_cmd, Cmd.initTypes, List.flatMap_cons, List.flatMap_nil,
         List.append_nil, LTy.toMonoTypeUnsafe, List.not_mem_nil] at hv <;>
         exact mem_of_tyVarsWithin (tyVarsWithin_of_genLMonoTy ‹_›) hv)
    | exact hctx
    | (intro ty hty
       rcases mem_values_insert ctx _ _ hty with rfl | hold
       · exact tyVarsWithin_of_genLMonoTy ‹_›
       · exact hctx ty hold)

/-- A call group declares only within `tvars`: its `init`s and its call use the callee's types
    instantiated at values within `tvars`. -/
theorem genCallTail_tyVars {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} {s : ProcSig}
    {σvals : List LMonoTy} {T : @LMonoTySignature Unit}
    (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true)
    (hsig : ∀ ty ∈ (s.M ++ s.O).values, ∀ v ∈ ty.freeVars, v ∈ s.typeArgs)
    (hlen : s.typeArgs.length ≤ σvals.length) (hσ : ∀ t ∈ σvals, tyVarsWithin tvars t = true)
    (hT : T.values = (substSig (s.typeArgs.zip σvals) s.O).values)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallTail (G := SPMF) octx tvars immutableVars C ctx d pctx s (s.typeArgs.zip σvals) T)) :
    DeclsWithin tvars r.stmts r.outCtx := by
  have hM : ∀ ty ∈ s.M.values, ∀ v ∈ ty.freeVars, v ∈ s.typeArgs := by
    intro ty hty
    have hmem : ty ∈ (s.M ++ s.O).values := by
      rw [lm_values_append]
      exact List.mem_append_left _ hty
    exact hsig ty hmem
  have hO : ∀ ty ∈ s.O.values, ∀ v ∈ ty.freeVars, v ∈ s.typeArgs := by
    intro ty hty
    have hmem : ty ∈ (s.M ++ s.O).values := by
      rw [lm_values_append]
      exact List.mem_append_right _ hty
    exact hsig ty hmem
  have hMσ := substSig_values_tyVarsWithin s.typeArgs σvals hlen hσ s.M hM
  have hOσ := substSig_values_tyVarsWithin s.typeArgs σvals hlen hσ s.O hO
  -- A filtered signature block's values are among the block's values.
  have hfilt : ∀ (L : @LMonoTySignature Unit) (p : Identifier Unit × LMonoTy → Bool)
      (v : LMonoTy), v ∈ (L.filter p).map Prod.snd → v ∈ L.values := by
    intro L p v hv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    rw [ListMap.values_eq_map_snd]
    exact List.mem_map_of_mem (List.mem_filter.mp hq).1
  obtain ⟨_, exprs, mask, _, _, rfl⟩ := genCallTail_support hr
  have hnew : ∀ ty ∈ ((substSig (s.typeArgs.zip σvals) s.M).filter (needsInit ctx)
      ++ T.filter (needsInit ctx)).map Prod.snd, tyVarsWithin tvars ty = true := by
    intro ty hty
    rw [List.map_append] at hty
    rcases List.mem_append.mp hty with hin | hout
    · exact hMσ ty (hfilt _ _ ty hin)
    · have hmem := hfilt _ _ ty hout
      rw [hT] at hmem
      exact hOσ ty hmem
  refine And.intro ?_ ?_
  · exact StmtsTyVarsWithin.append (initChain_tyVarsWithin _ hnew)
      (StmtsTyVarsWithin.call (callTyArgs_tyVarsWithin s.typeArgs σvals hlen hσ))
  · intro ty hty
    rcases mem_values_insertAllCtx _ ctx hty with hnewty | hold
    · exact hnew ty hnewty
    · exact hctx ty hold

/-- A `genCallStmt` group declares only within `tvars`, when each callee mentions only its own
    type parameters in its in-out and out-only types. -/
theorem genCallStmt_tyVars (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx)
    (d : Nat) (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true)
    (hsigs : ∀ s ∈ procs, ∀ ty ∈ (s.M ++ s.O).values, ∀ v ∈ ty.freeVars, v ∈ s.typeArgs)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    DeclsWithin tvars r.stmts r.outCtx := by
  cases procs with
  | nil => simp only [genCallStmt, mem_support_bot_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff] at hr
    obtain ⟨s, hs, σvals, hσvals, hr⟩ := hr
    have hs' := (mem_support_elements_iff (by simp)).mp hs
    have hmapM := (mem_support_mapM_iff _ _ σvals).mp hσvals
    have hlen : s.typeArgs.length ≤ σvals.length := Nat.le_of_eq hmapM.length_eq.symm
    have hσ : ∀ t ∈ σvals, tyVarsWithin tvars t = true := by
      intro t ht
      obtain ⟨_, _, hmem⟩ := forall₂_mem_left hmapM t ht
      exact sampleTyArg_tyVarsWithin _ _ _ t hmem
    exact genCallTail_tyVars hctx (hsigs s hs') hlen hσ (outTargets_values _ _ _ _) r hr

/-- A `genCallStmtMatch` group declares only within `tvars`, when each callee mentions only its
    own type parameters in its in-out and out-only types. -/
theorem genCallStmtMatch_tyVars (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx)
    (d : Nat) (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true)
    (hsigs : ∀ s ∈ procs, ∀ ty ∈ (s.M ++ s.O).values, ∀ v ∈ ty.freeVars, v ∈ s.typeArgs)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmtMatch (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    DeclsWithin tvars r.stmts r.outCtx := by
  obtain ⟨s, chosen, σvals, hs, hlen, _, hσlen, hσ, _, _, hr⟩ :=
    genCallStmtMatch_cases (octx := octx) (tvars := tvars) (pctx := pctx) r hr
  exact genCallTail_tyVars hctx (hsigs s hs) (Nat.le_of_eq hσlen.symm) hσ
    (matchOutTargets_values _ _ _ hlen) r hr

/-- A generated command statement declares only within `tvars`. -/
theorem genCmdStmt_tyVars (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)
    (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true) (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genCmdStmt (G := SPMF) octx tvars immutableVars C ctx d pctx)) :
    DeclsWithin tvars r.stmts r.outCtx := by
  revert r; show IsSoundFor _ _; rw [IsSoundFor.iff_obs, genCmdStmt]
  walk [(isSoundFor_self_support (genCmd _ _ _ _ _ _ _ _)).obs]
  exact genCmd_tyVars octx pctx tvars immutableVars ctx d hctx _ ‹_›

/-- A generated `exit` declares nothing and keeps the scope. -/
theorem genExitStmt_tyVars (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
    (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true) (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genExitStmt (G := SPMF) labels C ctx)) :
    DeclsWithin tvars r.stmts r.outCtx := by
  revert r; show IsSoundFor _ _; rw [IsSoundFor.iff_obs]; unfold genExitStmt; walk
  exact And.intro StmtsTyVarsWithin.exit hctx

/-- A generated type declaration declares no local variable and keeps the scope. -/
theorem genTypeDeclStmt_tyVars (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)
    (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true) (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genTypeDeclStmt (G := SPMF) C ctx d)) :
    DeclsWithin tvars r.stmts r.outCtx := by
  revert r; show IsSoundFor _ _; rw [IsSoundFor.iff_obs, genTypeDeclStmt]
  walk [(isSoundFor_self_support (genTypeConstructor _)).obs]
  exact And.intro StmtsTyVarsWithin.typeDecl hctx

-- ── The statement-level invariant (mutual over genStmt / genStmtChain) ────────

mutual

/-- A generated statement list declares only within `tvars` and leaves a scope within `tvars`,
    from a scope within `tvars` and callees that mention only their own type parameters. -/
theorem genStmt_tyVars (procs : ProcSigCtx) (labels : List String) (C : LContext CoreLParams)
    (ctx : VarCtx) (n : Nat) (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true)
    (hsigs : ∀ s ∈ procs, ∀ ty ∈ (s.M ++ s.O).values, ∀ v ∈ ty.freeVars, v ∈ s.typeArgs)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen)) :
    DeclsWithin tvars r.stmts r.outCtx := by
  revert r; show IsSoundFor _ _; rw [IsSoundFor.iff_obs]
  cases n <;> rw [genStmt] <;>
    walk [(isSoundFor_self_support (genCmdStmt _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genExitStmt _ _ _)).obs,
      (isSoundFor_self_support (genTypeDeclStmt _ _ _)).obs,
      (isSoundFor_self_support (genCallStmt _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCallStmtMatch _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genFreshLabel _)).obs,
      (isSoundFor_self_support (genStmtChain _ _ _ _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genLExpr _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCondOrNondet _ _ _ _ _)).obs,
      (isSoundFor_self_support (genOptMeasure _ _ _ _ _)).obs,
      (isSoundFor_self_support (genInvariants _ _ _ _ _ _)).obs]
  all_goals first
    | exact genCmdStmt_tyVars C ctx _ hctx _ ‹_›
    | exact genExitStmt_tyVars labels C ctx hctx _ ‹_›
    | exact genTypeDeclStmt_tyVars C ctx _ hctx _ ‹_›
    | exact genCallStmt_tyVars procs C ctx _ hctx hsigs _ ‹_›
    | exact genCallStmtMatch_tyVars procs C ctx _ hctx hsigs _ ‹_›
    | exact And.intro (StmtsTyVarsWithin.block
        (genStmtChain_tyVars procs _ C ctx _ _ hctx hsigs _ ‹_›).1) hctx
    | exact And.intro (StmtsTyVarsWithin.ite
        (genStmtChain_tyVars procs labels C ctx _ _ hctx hsigs _ ‹_›).1
        (genStmtChain_tyVars procs labels C ctx _ _ hctx hsigs _ ‹_›).1) hctx
    | exact And.intro (StmtsTyVarsWithin.loop
        (genStmtChain_tyVars procs labels C ctx _ _ hctx hsigs _ ‹_›).1) hctx
termination_by (n, 0, 0)

/-- A generated statement chain declares only within `tvars` and leaves a scope within `tvars`,
    under the same conditions as `genStmt_tyVars`. -/
theorem genStmtChain_tyVars (procs : ProcSigCtx) (labels : List String) (C : LContext CoreLParams)
    (ctx : VarCtx) (size len : Nat) (hctx : ∀ ty ∈ ctx.values, tyVarsWithin tvars ty = true)
    (hsigs : ∀ s ∈ procs, ∀ ty ∈ (s.M ++ s.O).values, ∀ v ∈ ty.freeVars, v ∈ s.typeArgs)
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SPMF.support
      (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size len
        maxStmtSeqLen)) :
    DeclsWithin tvars result.1 result.2.2 := by
  revert result; show IsSoundFor _ _; rw [IsSoundFor.iff_obs]
  cases len <;> rw [genStmtChain] <;>
    walk [(isSoundFor_self_support (genStmt _ _ _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genStmtChain _ _ _ _ _ _ _ _ _ _ _)).obs]
  · exact And.intro StmtsTyVarsWithin.nil hctx
  · have hhead := genStmt_tyVars procs labels C ctx size hctx hsigs _ ‹_›
    have htail := genStmtChain_tyVars procs labels _ _ size _ hhead.2 hsigs _ ‹_›
    exact And.intro (StmtsTyVarsWithin.append hhead.1 htail.1) htail.2
termination_by (size, 1, len)

end

end StrataGenerators.Procedure
