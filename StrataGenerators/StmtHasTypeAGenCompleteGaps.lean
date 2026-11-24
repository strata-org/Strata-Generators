import StrataGenerators.StmtHasTypeAGenComplete

open Lambda LExpr RandomChoice Core Imperative TypeSpec ArbString
open StrataGenerators.Stmt StrataGenerators.Procedure StrataGenerators.Function

/-!
# The side conditions of `spec_complete_at` are necessary

`spec_complete_at` in `StmtHasTypeAGenComplete.lean` carries five side conditions: `InGenShape`,
`WritesOk`, `AlphabetOk`, `CallOk` and `ExprOk`. This file shows that two of them, `InGenShape` and
`AlphabetOk`, cannot be removed. For each of the two, it gives a statement that is well-typed under
`StatementWellTyped` but is not in the support of `genStmt`. Therefore no
completeness theorem holds for `genStmt` without a side condition of this kind.

## The two gaps

| Predicate     | Clause that survives      | Gap theorem      | In Core source? |
| ------------- | ------------------------- | ---------------- | --------------- |
| `InGenShape`  | `md = default`            | `metadata_gap`   | yes             |
| `AlphabetOk`  | name in `genIdentName`    | `label_gap`      | no              |

The docstring of each gap theorem gives the Strata Core source text of its
counterexample. `Core.formatProgram` produced that text from the statement in the
theorem.

## Two conditions that the generators satisfy

Two further shapes could be a counterexample in the source of Core, and the generators reach both of them:

* Each label of an `assert`, of an `assume` and of a `cover`, and each variable name of an `init`, comes from
  `genIdentName`, whose support holds exactly the legal identifiers of Core that are not a keyword. A generator
  that draws a name from `String.arbitrary` or from `NonEmptyString.arbitrary` reaches an alphanumeric name
  only, so a name with an underscore is then out of reach. One such name is `assert_0`, which the parser itself
  builds for an `assert` with no label. `label_gap` therefore survives for one reason only: a `Statement` holds
  a bare `String`. `emptyLabel_not_reachable` gives a witness.
* `mkArgs` takes a mask for an interleaving, so a call such as `call p(out y, 1);` is in the image of the
  recipe. `mkArgs_out_then_in` shows that. A recipe that fixes the order as the in-out block, then each
  by-value input, then each out target, cannot reach such a call.

## Upstream predicates that do not fit

Three upstream predicates look close to the side conditions, but none of them
discharges one:

* `Imperative.Stmt.stripMetaData` erases the metadata of a `block`, an `ite`, a
  `loop`, an `exit` and a `typeDecl`. It leaves a `.cmd` node
  untouched. The gap of `metadata_gap` is at a `.cmd` node, so this function
  cannot close it.
* The call rule's own premise `Core.WF.WFcallProp` gives the `Nodup` fact for the
  write keys of a call (`lhsWF`), and its in-scope premise gives that no write key needs
  an `init`. `call_written_nodup` and `call_no_init` derive both inside `spec_complete_at`, so
  `CallOk` asks for neither.
* `LContext.WellKindedTy` bounds the type constructors of an `init` annotation.
  `genLMonoTy`'s support also bounds the depth of the type and the free type
  variables (`genLMonoTy_support`), so `WellKindedTy` is too weak.

## The clauses with no source-level counterexample

`InGenShape` also demands that an `init` annotation is monomorphic
(`.forAll [] mty`). The Core front end builds only `.forAll []` local
annotations (`translateInitStatement` and `translateVarStatement` in
`Strata/Languages/Core/DDMTransform/Translate.lean`). So this clause is
necessary at the level of the abstract syntax tree, but no parsed program can
break it. Each clause of `AlphabetOk` about a name is in the same position.
-/
namespace StrataGenerators.Stmt.SpecComplete.Gaps

variable {octx : OpCtx} {tvars : List TyIdentifier}
variable {maxStmtSeqLen : Nat}

-- ── Shape of a call group ────────────────────────────────────────────────

/-- A one-statement call group has an empty `init` chain. Then the statement is
    the call itself. -/
theorem initChain_append_call_singleton {L : List (Identifier Unit × LMonoTy)}
    {pn : String} {tys : Option (List LTy)} {args : List (CallArg Expression)}
    {md : Imperative.MetaData Expression} {s : Statement}
    (h : [s] = StrataGenerators.Stmt.initChain L ++ [Statement.call pn tys args md]) :
    s = Statement.call pn tys args md := by
  cases L with
  | nil => simpa [StrataGenerators.Stmt.initChain] using h
  | cons hd tl => simp [StrataGenerators.Stmt.initChain] at h

-- ── Inversion of `genStmt` at a one-statement `.cmd` group ───────────────

/-- A one-statement `.cmd` group that `genCallTail` produces is a call whose argument list is a
    `mkArgs` recipe over the callee's in-out block and the out arguments. -/
theorem genCallTail_cmd_inv {C : LContext CoreLParams} {ctx : VarCtx} {n : Nat} {s : ProcSig}
    {σ : List (TyIdentifier × LMonoTy)} {T : @LMonoTySignature Unit} {C' : LContext CoreLParams}
    {ctx' : VarCtx} {ce : Command} {r : GenStmtResult} {pctx : PolyOpCtx}
    (hr : r ∈ SPMF.support
      (genCallTail (G := SPMF) octx tvars immutableVars C ctx n pctx s σ T))
    (heq : r = ⟨[Stmt.cmd ce], C', ctx'⟩) :
    ∃ (exprs : List Expression.Expr) (mask : List Bool),
      ce = CmdExt.call s.pname
        (callTyArgs s.typeArgs σ)
        (StrataGenerators.Stmt.mkArgs s.M T exprs mask) default := by
  obtain ⟨_, exprs, mask, _, _, rfl⟩ := genCallTail_support hr
  simp only [GenStmtResult.mk.injEq] at heq
  have hcall := initChain_append_call_singleton heq.1.symm
  simp only [Statement.call, Stmt.cmd.injEq] at hcall
  exact ⟨exprs, mask, hcall⟩

/-- A one-statement `.cmd` group that `genCallStmtMatch` produces is a call whose argument list is
    a `mkArgs` recipe over the callee's in-out block. -/
theorem genCallStmtMatch_cmd_inv (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (C C' : LContext CoreLParams) (ctx ctx' : VarCtx) (n : Nat) (ce : Command)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmtMatch (G := SPMF) octx tvars immutableVars procs C ctx n []))
    (heq : r = ⟨[Stmt.cmd ce], C', ctx'⟩) :
    ∃ (s : ProcSig) (targets : @LMonoTySignature Unit) (σvals : List LMonoTy)
        (exprs : List Expression.Expr) (mask : List Bool),
        s ∈ procs ∧
        ce = CmdExt.call s.pname
          (callTyArgs s.typeArgs (s.typeArgs.zip σvals))
          (StrataGenerators.Stmt.mkArgs s.M targets exprs mask) default := by
  obtain ⟨s, _, σvals, hs, _, _, _, _, hr⟩ := genCallStmtMatch_cases r hr
  obtain ⟨exprs, mask, hce⟩ := genCallTail_cmd_inv hr heq
  exact ⟨s, _, σvals, exprs, mask, hs, hce⟩

/-- **Inversion at a `.cmd` group.** `genStmt` reaches a one-statement group
    `[.cmd ce]` in exactly three ways. Either `genCmd` produced an imperative
    command, or `genCallStmt` produced a call whose argument list is a `mkArgs`
    recipe, or `genCallStmtMatch` produced a call whose argument list is a `mkArgs`
    recipe with some targets. The other six branches produce a `block`, an `ite`, a `loop`, an
    `exit` or a `typeDecl`, so they cannot produce a `.cmd`. -/
theorem mem_genStmt_cmd_inv (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C C' : LContext CoreLParams) (ctx ctx' : VarCtx) (n : Nat)
    (ce : Command)
    (h : (⟨[Stmt.cmd ce], C', ctx'⟩ : GenStmtResult) ∈
      SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx [] n maxStmtSeqLen)) :
    (∃ c, ce = CmdExt.cmd c ∧ (⟨c, ctx'⟩ : GenCmdResult) ∈
        SPMF.support
          (genCmd (G := SPMF) octx tvars immutableVars ctx n [] [] C.knownTypes)) ∨
    (∃ (s : ProcSig) (σvals : List LMonoTy) (exprs : List Expression.Expr) (mask : List Bool),
        s ∈ procs ∧
        ce = CmdExt.call s.pname
          (callTyArgs s.typeArgs (s.typeArgs.zip σvals))
          (StrataGenerators.Stmt.mkArgs s.M
            (outTargets immutableVars ctx
              (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O) (functionNames C))
            exprs mask) default) ∨
    (∃ (s : ProcSig) (targets : @LMonoTySignature Unit) (σvals : List LMonoTy)
        (exprs : List Expression.Expr) (mask : List Bool),
        s ∈ procs ∧
        ce = CmdExt.call s.pname
          (callTyArgs s.typeArgs (s.typeArgs.zip σvals))
          (StrataGenerators.Stmt.mkArgs s.M targets exprs mask) default) := by
  refine (?_ : IsSoundFor _ (fun (r : GenStmtResult) => r = ⟨[Stmt.cmd ce], C', ctx'⟩ → _)) _ h rfl
  rw [IsSoundFor.iff_obs]
  cases n <;> rw [genStmt] <;>
    unfold genCmdStmt genExitStmt genTypeDeclStmt genCallStmt <;>
    walk [(isSoundFor_self_support (genCmd _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (List.mapM (m := SPMF) _ _)).obs,
      (isSoundFor_self_support (listOf (elements [true, false] _))).obs,
      (isSoundFor_self_support (genCallStmtMatch _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genTypeConstructor _)).obs,
      (isSoundFor_self_support (genFreshLabel _)).obs,
      (isSoundFor_self_support (genStmtChain _ _ _ _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genLExpr _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCondOrNondet _ _ _ _ _)).obs,
      (isSoundFor_self_support (genOptMeasure _ _ _ _ _)).obs,
      (isSoundFor_self_support (genInvariants _ _ _ _ _ _)).obs]
  all_goals (rename_i heq; try simp only [GenStmtResult.mk.injEq, List.cons.injEq, Stmt.cmd.injEq,
    reduceCtorEq, false_and, and_true] at heq)
  all_goals first
    | (obtain ⟨rfl, -, rfl⟩ := heq; exact Or.inl ⟨_, rfl, ‹_›⟩)
    | (have hcall := initChain_append_call_singleton heq.1.symm
       simp only [Statement.call, Stmt.cmd.injEq] at hcall
       exact Or.inr (Or.inl ⟨_, _, _, _, ‹_›, hcall⟩))
    | exact Or.inr (Or.inr (genCallStmtMatch_cmd_inv _ _ _ _ _ _ _ _ _ ‹_› ‹_›))

/-- **Inversion at an `assert` command.** `genAssertCmd` is the only branch of
    `genCmd` that produces an `assert`. It emits `default` metadata, and it draws
    the label from `genIdentName`. -/
theorem mem_genCmd_assert_inv (immutableVars : List (Identifier Unit)) (ctx ctx' : VarCtx)
    (n : Nat) (l : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    {avoid : List String} {kt : Lambda.KnownTypes}
    (h : (⟨.assert l e md, ctx'⟩ : GenCmdResult) ∈
      SPMF.support (genCmd (G := SPMF) octx tvars immutableVars ctx n [] avoid kt)) :
    md = default ∧ l ∈ SPMF.support (genIdentName (G := SPMF)) := by
  refine (?_ : IsSoundFor _ (fun (r : GenCmdResult) => r = ⟨.assert l e md, ctx'⟩ → _)) _ h rfl
  walk_genCmd
  all_goals (rename_i heq; (try split_ifs at heq) <;> simp only [GenCmdResult.mk.injEq,
    Cmd.assert.injEq, reduceCtorEq, false_and] at heq)
  all_goals (obtain ⟨⟨rfl, -, rfl⟩, -⟩ := heq; first | rfl | assumption)

-- ── Well-typedness of an `assert` ────────────────────────────────────────

/-- An `assert` of a well-typed `bool` expression is well-typed at every label and at every
    metadata value. -/
theorem assert_wt (P : Program) (C : LContext CoreLParams) (ts : TypeScopes) (L : List String)
    (l : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (he : ExprWellTyped C ts e .bool) :
    StatementWellTyped P C ts L (Statement.assert l e md) C ts :=
  .cmd _ _ _ _ _ (.cmd _ _ _ (.assert _ _ _ _ _ he (Strata.Util.HMaps.Equiv.refl _)))

-- ── Gap 1: the metadata clause of `InGenShape` ───────────────────────────

/-- One metadata element, for the counterexample of `metadata_gap`. -/
def mdKey : Imperative.MetaDataElem Expression :=
  { fld := .label "myKey", value := .switch true }

/-- **Gap 1: metadata.** `genStmt` always emits `default` metadata. The spec
    leaves the metadata free. So a statement with any other metadata is
    well-typed and out of reach.

    The Core grammar has an annotation prefix for every statement
    (`MetadataAnn` in `Grammar.lean`), so the gap is visible in the source:

    ```
    program Core;

    procedure caller ()
    {
      @[myKey] assert [lbl]: true;
    };
    ```

    `assert_wt` gives the well-typedness of the body statement. -/
theorem metadata_gap (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C C' : LContext CoreLParams) (ctx ctx' : VarCtx) (n : Nat)
    (l : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (hmd : md ≠ default) :
    (⟨[Statement.assert l e md], C', ctx'⟩ : GenStmtResult) ∉
      SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx [] n maxStmtSeqLen) := by
  intro h
  rcases mem_genStmt_cmd_inv immutableVars procs labels C C' ctx ctx' n _ h with
    ⟨c, hce, hc⟩ | ⟨s, σvals, exprs, mask, _, hce⟩ | ⟨s, targets, σvals, exprs, mask, _, hce⟩
  · rw [CmdExt.cmd.injEq] at hce; subst hce
    exact hmd (mem_genCmd_assert_inv immutableVars ctx ctx' n l e md hc).1
  · exact absurd hce (by simp)
  · exact absurd hce (by simp)

/-- The metadata of `mdKey` is not `default`, so `metadata_gap` applies to it. -/
example : (#[mdKey] : Imperative.MetaData Expression) ≠ default := by decide

-- ── Gap 2: the alphabet clause of `AlphabetOk` ───────────────────────────

/-- **Gap 2: the label alphabet.** `genAssertCmd` draws an `assert` label from
    `genIdentName`, whose support is exactly the legal Core bare identifiers that
    are not reserved keywords. The `assert` rule accepts *every* `String`, and a
    `Statement` holds a bare `String`, so a statement with any other label is
    well-typed and out of reach.

    **This gap has no source-level counterexample.** Every label a Core program can
    hold is a legal identifier, so the Core parser cannot produce a statement that
    breaks the clause. The earlier source of labels was `String.arbitrary`, whose
    support holds the alphanumeric strings only. Under it a plain parsed program was
    a counterexample, because the parser mints `assert_0` for an unlabelled `assert`
    and an underscore is not alphanumeric.

    `""` is a witness that lives in the abstract syntax tree alone. See
    `emptyLabel_not_reachable`. `Core.formatProgram` renders it as the degenerate
    `assert [||]: true;`. `assert_wt` gives the well-typedness of the statement.

    The same gap applies to the label of an `assume`, of a `cover`, of an invariant and of a `block`, to the
    variable name of an `init`, and to the name of a type constructor. Each of those also comes from
    `genIdentName`. -/
theorem label_gap (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C C' : LContext CoreLParams) (ctx ctx' : VarCtx) (n : Nat)
    (l : String) (e : Expression.Expr)
    (hl : l ∉ SPMF.support (genIdentName (G := SPMF))) :
    (⟨[Statement.assert l e default], C', ctx'⟩ : GenStmtResult) ∉
      SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx [] n maxStmtSeqLen) := by
  intro h
  rcases mem_genStmt_cmd_inv immutableVars procs labels C C' ctx ctx' n _ h with
    ⟨c, hce, hc⟩ | ⟨s, σvals, exprs, mask, _, hce⟩ | ⟨s, targets, σvals, exprs, mask, _, hce⟩
  · rw [CmdExt.cmd.injEq] at hce; subst hce
    exact hl (mem_genCmd_assert_inv immutableVars ctx ctx' n l e default hc).2
  · exact absurd hce (by simp)
  · exact absurd hce (by simp)

/-- The empty label is not a legal identifier, so `label_gap` applies to it. An
    identifier needs a first character. -/
theorem emptyLabel_not_reachable :
    "" ∉ SPMF.support (genIdentName (G := SPMF)) := by
  rw [StrataGenerators.Function.mem_support_genIdentName_iff]
  rintro ⟨⟨c, cs, hsplit, _, _⟩, _⟩
  exact absurd hsplit (by simp)

-- ── The order of the arguments is free ───────────────────────────────

/-- **The order of the arguments needs no side condition.** `mkArgs` takes a mask for an interleaving, so an
    `out` argument before a by-value input is in the image of the recipe. The mask `[false]` puts the one out
    target first.

    Before the mask, `mkArgs` fixed the order as in-out, then by-value input, then
    out target. The call `call p(out y, 1);` below was well-typed and out of reach.
    Now it is the recipe at `mask = [false]`:

    ```
    program Core;

    procedure p (x : int, out r : int)
    {

    };
    procedure caller ()
    {
      var y : int := 0;
      call p(out y, 1);
    };
    ``` -/
theorem mkArgs_out_then_in (y : Identifier Unit)
    (ty : LMonoTy) (e : Expression.Expr) :
    StrataGenerators.Stmt.mkArgs [] [(y, ty)] [e] [false]
      = [CallArg.outArg y, CallArg.inArg e] := by
  simp [StrataGenerators.Stmt.mkArgs, StrataGenerators.Stmt.mergeBy]

-- ── Why `ExprOk` is per expression ──────────────────────────────────────────

/-! ### A hypothesis over each environment is unsatisfiable, at each depth

A hypothesis of the form `∀ d (ctx : VarCtx), GenLExprComplete ctx.toFVarCtx octx tvars d` is unsatisfiable.
`GenLExprComplete fctx octx tvars d` asks that *each* expression that `HasTypeA` accepts at a type is in the
support of `genLExpr` at the depth `d` and at that type.
That is false, and the reason has nothing to do with the depth: with an empty `fctx`
nothing in the support has a free variable, while `HasTypeA.fvar` accepts an
*annotated* free variable against the empty context, since it reads the type off the
annotation. The two sides already disagree at a leaf.

The depth is a second obstruction, and it is independent of the first. `genLExpr` recurses structurally on the
depth, so its support at a fixed depth has a bounded depth, and `HasTypeA` accepts a term of each depth. Each
obstruction alone is enough, and that is why an existential in place of the `∀ d`
`∃ d` does not help. -/

/-- **`GenLExprComplete` is false at every depth.** An annotated free variable is
    well-typed against the empty context, and with `fctx = []` nothing in
    `genLExpr`'s support has a free variable (`genLExpr_no_fvars`). -/
theorem not_GenLExprComplete (d : Nat) :
    ¬ GenLExprComplete [] octx tvars d := by
  intro h
  have hmem := h .int (LExpr.fvar genLoc ⟨"zzz", ()⟩ (some .int)) HasTypeA.fvar
  have := Lambda.LExpr.genLExpr_no_fvars octx [] tvars [] d .int _ hmem
  simp [LExpr.getVars] at this

/-- **An existential over the depth does not help.** The predicate fails at each depth, so
    `∃ d, GenLExprComplete …` is false too. Only a form with the quantifier *inside* can be satisfiable, which
    means the reachability of one expression at a time, in a scope that holds the free variables of that
    expression. `ExprOk` has that form. -/
theorem not_exists_depth_GenLExprComplete :
    ¬ ∃ d, GenLExprComplete [] octx tvars d := by
  rintro ⟨d, hd⟩; exact not_GenLExprComplete d hd

/-- The empty scope really is the empty `fctx`, so the refutation applies to
    `hExprC`'s `ctx = []` instance. -/
theorem toFVarCtx_nil : VarCtx.toFVarCtx [] = [] := rfl

/-- **A hypothesis `hExprC` over each environment is unsatisfiable**, so a completeness theorem that
    took it would be vacuous. Instantiate at `ctx = []`. -/
theorem hExprC_unsatisfiable :
    ¬ (∀ d (ctx : VarCtx), GenLExprComplete ctx.toFVarCtx octx tvars d) := by
  intro h; exact not_GenLExprComplete 0 (h 0 [])

-- ── A call that receives its result into another variable ──────────────────

/-- The callee `procedure p (x : int, out r : int)`: no in-out block, one by-value input, and one
    output-only parameter. -/
def sigP : ProcSig :=
  { pname := "p", typeArgs := [], M := [], I := [(⟨"x", ()⟩, .int)],
    O := [(⟨"r", ()⟩, .int)] }

/-- A scope with two integer variables, `r` and `z`. -/
def callerCtx : VarCtx := [(⟨"r", ()⟩, .int), (⟨"z", ()⟩, .int)]

/-- The call `call p(1, out z);`, which receives the result in `z` and not in the variable `r` that
    the callee declares. -/
def otherTargetCall : Statement :=
  Statement.call "p" (some [])
    [CallArg.inArg (LExpr.const genLoc (.intConst 1)), CallArg.outArg ⟨"z", ()⟩] default

/-- The call `call p(1, out z);` is in the support of `genCallStmtMatch`, at some depth, when no
    function of the context is named `z`. The generator draws `z` as the target of the one
    output-only formal, and the type of `z` matches the type of the formal. The call receives the
    result in a variable other than the callee's own parameter `r`, which `genCallStmt` cannot
    produce. -/
theorem otherTargetCall_mem_genCallStmtMatch (C : LContext CoreLParams) (pctx : PolyOpCtx)
    (hz : "z" ∉ functionNames C) :
    ∃ d, (⟨[otherTargetCall], C, callerCtx⟩ : GenStmtResult) ∈
      SPMF.support (genCallStmtMatch (G := SPMF) octx tvars [] [sigP] C callerCtx d pctx) := by
  have hone : ∃ d, (LExpr.const genLoc (.intConst 1) : LExpr') ∈ SPMF.support
      (genLExpr (G := SPMF) callerCtx.toFVarCtx octx pctx tvars [] d .int) :=
    genLExpr_complete_exists _ _ _ _ _ _ genLMonoTy_mem_int _ _ (by exact .const rfl)
      trivial trivial
      ⟨0, .intConst⟩
  obtain ⟨d, hd⟩ := hone
  refine ⟨d, ?_⟩
  unfold genCallStmtMatch
  simp only [mem_support_bind_iff]
  have hne : ([sigP] : List ProcSig) ≠ [] := by simp
  refine ⟨sigP, (mem_support_elements_iff hne).mpr (List.mem_singleton_self _),
    [some (⟨"z", ()⟩, .int)], ?_, ?_⟩
  · have hO : sigP.O = [(⟨"r", ()⟩, LMonoTy.int)] := rfl
    rw [hO]
    simp only [pickOutTargets, mem_support_bind_iff, mem_support_pure_iff]
    refine ⟨some (⟨"z", ()⟩, .int), ?_, [], by simp, rfl⟩
    rw [mem_support_elements_iff]
    refine List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨(⟨"z", ()⟩, .int), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩)
    · simp [callerCtx]
    · simp [hz]
  · have hren : matchRenaming octx tvars callerCtx sigP = [] := by
      simp [matchRenaming, sigP]
    have hfresh : matchFreshArgs octx tvars callerCtx sigP = [] := by
      simp [matchFreshArgs, freshTyArgs, sigP]
    obtain ⟨substs, hsubsts⟩ : ∃ substs, matchTargets
        (StrataGenerators.Stmt.substSig (matchRenaming octx tvars callerCtx sigP) sigP.O)
        [some (⟨"z", ()⟩, LMonoTy.int)] = some substs := by
      rw [hren, StrataGenerators.Stmt.substSig_nil]
      have hfv : LMonoTy.int.freeVars = [] := rfl
      obtain ⟨Su, hSu, -⟩ := unifyTypes_matching_complete LMonoTy.int LMonoTy.int []
        (fun v hv => absurd hv (by rw [hfv]; exact List.not_mem_nil)) rfl
      refine ⟨[Su], ?_⟩
      simp [matchTargets, sigP, hSu, hfv]
    rw [hsubsts]
    simp only [hfresh, List.mapM_nil, mem_support_bind_iff, mem_support_pure_iff]
    refine ⟨[], rfl, ?_⟩
    have hzipNil : sigP.typeArgs.zip ([] : List LMonoTy) = [] := rfl
    rw [hzipNil, StrataGenerators.Stmt.substSig_nil]
    have hmatched : targetsMatched sigP.O [some (⟨"z", ()⟩, LMonoTy.int)] = true := by decide
    rw [ite_eq_left hmatched]
    have hT : matchOutTargets (outNameBase callerCtx (functionNames C)) sigP.O
        [some (⟨"z", ()⟩, LMonoTy.int)] = [(⟨"z", ()⟩, LMonoTy.int)] := rfl
    rw [hT]
    have hMusable : (StrataGenerators.Stmt.substSig [] sigP.M).all
        (usableName [] callerCtx) = true := by
      simp [sigP, StrataGenerators.Stmt.substSig]
    have hNodup : (StrataGenerators.Stmt.substSig [] sigP.M ++
        (show @LMonoTySignature Unit from [(⟨"z", ()⟩, LMonoTy.int)])).keys.Nodup := by decide
    have hMnotFn : ((StrataGenerators.Stmt.substSig [] sigP.M).filter (needsInit callerCtx)).all
        (fun q => !(functionNames C).contains q.1.name) = true := by
      simp [sigP, StrataGenerators.Stmt.substSig]
    have hannots : ([LExpr.const genLoc (.intConst 1)] : List LExpr').all
        (binderAnnotsKnownIn C.knownTypes) = true := by
      simp [binderAnnotsKnownIn, LExpr.binderAnnotations]
    exact genCallTail_mem (octx := octx) (tvars := tvars) (immutableVars := [])
      (pctx := pctx) (C := C) (ctx := callerCtx) (d := d) (s := sigP) (σ := [])
      (T := [(⟨"z", ()⟩, LMonoTy.int)]) hMusable hNodup hMnotFn
      [LExpr.const genLoc (.intConst 1)] [true] (.cons hd .nil) hannots

end StrataGenerators.Stmt.SpecComplete.Gaps
