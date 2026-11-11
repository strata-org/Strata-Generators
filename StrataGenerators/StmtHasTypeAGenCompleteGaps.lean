import StrataGenerators.StmtHasTypeAGenComplete

open Lambda LExpr RandomChoice Core Imperative TypeSpec ArbString
open StrataGenerators.Stmt StrataGenerators.Procedure StrataGenerators.Function

/-!
# The side conditions of `spec_complete_at` are necessary

`spec_complete_at` in `StmtHasTypeAGenComplete.lean` carries five side conditions: `InGenShape`,
`WritesOk`, `AlphabetOk`, `CallOk` and `ExprOk`. This file shows that three of them, `InGenShape`,
`AlphabetOk` and `CallOk`, cannot be removed. For each of the three, it gives a statement that is well-typed under
`StatementWellTyped` but is not in the support of `genStmt`. Therefore no
completeness theorem holds for `genStmt` without a side condition of this kind.

## The three gaps

| Predicate     | Clause that survives      | Gap theorem      | In Core source? |
| ------------- | ------------------------- | ---------------- | --------------- |
| `InGenShape`  | `md = default`            | `metadata_gap`   | yes             |
| `AlphabetOk`  | name in `genIdentName`    | `label_gap`      | no              |
| `CallOk`      | out target is `outTargets`| `outTarget_gap`  | yes             |

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
    {pn : String} {args : List (CallArg Expression)} {md : Imperative.MetaData Expression}
    {s : Statement}
    (h : [s] = StrataGenerators.Stmt.initChain L ++ [Statement.call pn args md]) :
    s = Statement.call pn args md := by
  cases L with
  | nil => simpa [StrataGenerators.Stmt.initChain] using h
  | cons hd tl => simp [StrataGenerators.Stmt.initChain] at h

-- ── Inversion of `genStmt` at a one-statement `.cmd` group ───────────────

/-- **Inversion at a `.cmd` group.** `genStmt` reaches a one-statement group
    `[.cmd ce]` in exactly two ways. Either `genCmd` produced an imperative
    command, or `genCallStmt` produced a call whose argument list is a `mkArgs`
    recipe. The other six branches produce a `block`, an `ite`, a `loop`, an
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
          (StrataGenerators.Stmt.mkArgs s.M
            (outTargets immutableVars ctx
              (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O) (functionNames C))
            exprs mask) default) := by
  refine (?_ : IsSoundFor _ (fun (r : GenStmtResult) => r = ⟨[Stmt.cmd ce], C', ctx'⟩ → _)) _ h rfl
  rw [IsSoundFor.iff_obs]
  cases n <;> rw [genStmt] <;>
    unfold genCmdStmt genExitStmt genTypeDeclStmt genCallStmt <;>
    walk [(isSoundFor_self_support (genCmd _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (List.mapM (m := SPMF) _ _)).obs,
      (isSoundFor_self_support (listOf (elements [true, false] _))).obs,
      (isSoundFor_self_support (genTypeConstructor _)).obs,
      (isSoundFor_self_support (genFreshLabel _)).obs,
      (isSoundFor_self_support (genStmtChain _ _ _ _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genLExpr _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCondOrNondet _ _ _ _ _)).obs,
      (isSoundFor_self_support (genOptMeasure _ _ _ _ _)).obs,
      (isSoundFor_self_support (genInvariants _ _ _ _ _ _)).obs]
  all_goals (rename_i heq; simp only [GenStmtResult.mk.injEq, List.cons.injEq, Stmt.cmd.injEq,
    reduceCtorEq, false_and, and_true] at heq)
  all_goals first
    | (obtain ⟨rfl, -, rfl⟩ := heq; exact Or.inl ⟨_, rfl, ‹_›⟩)
    | (have hcall := initChain_append_call_singleton heq.1.symm
       simp only [Statement.call, Stmt.cmd.injEq] at hcall
       exact Or.inr ⟨_, _, _, _, ‹_›, hcall⟩)

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
    ⟨c, hce, hc⟩ | ⟨s, σvals, exprs, mask, _, hce⟩
  · rw [CmdExt.cmd.injEq] at hce; subst hce
    exact hmd (mem_genCmd_assert_inv immutableVars ctx ctx' n l e md hc).1
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
    ⟨c, hce, hc⟩ | ⟨s, σvals, exprs, mask, _, hce⟩
  · rw [CmdExt.cmd.injEq] at hce; subst hce
    exact hl (mem_genCmd_assert_inv immutableVars ctx ctx' n l e default hc).2
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

-- ── Gap 3: the out-target name choice of `CallOk` ─────────────────────────

/-- The callee of the counterexample: `procedure p (x : int, out r : int)`. -/
def procP : Procedure :=
  { header := { name := ⟨"p", ()⟩, typeArgs := [],
                inputs := [(⟨"x", ()⟩, .int)], outputs := [(⟨"r", ()⟩, .int)] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] }

/-- The program that declares `procP`. -/
def progP : Program := { decls := [.proc procP .empty] }

/-- The generator-side signature of `procP`: no in-out block, one input-only
    parameter `x`, one output-only parameter `r`. -/
def sigP : ProcSig :=
  { pname := "p", typeArgs := [], M := [], I := [(⟨"x", ()⟩, .int)],
    O := [(⟨"r", ()⟩, .int)] }

/-- The scope of the caller: `r : int` and `z : int`. Both have the type of the
    `out` parameter, so either one can receive the result. -/
def callerCtx : VarCtx := [(⟨"r", ()⟩, .int), (⟨"z", ()⟩, .int)]

/-- The call `call p(1, out z);`. It receives the result into `z`, not into the
    name `r` that the callee declares. -/
def otherTargetCall : Statement :=
  Statement.call "p"
    [CallArg.inArg (LExpr.const () (.intConst 1)), CallArg.outArg ⟨"z", ()⟩] default

/-- With `r : int` in scope, the generator's out target for `procP` is `r`, whatever names it
    avoids. -/
theorem outTargets_sigP (avoid : List String) :
    outTargets [] callerCtx (StrataGenerators.Stmt.substSig [] sigP.O) avoid
      = [(⟨"r", ()⟩, (.int : LMonoTy))] := by
  rw [outTargets_eq_of_reused [] callerCtx _ avoid (by decide)]
  rfl

/-- **Gap 3: the out-target name choice.** The `call` rule constrains an `out`
    argument's existence, its type and its writability. It says nothing about its
    *name*. `outTargets` fixes the name: it reuses the name the callee declares
    when that name is in scope at the declared type, and otherwise it invents a
    fresh one. So a call that receives the result into another in-scope variable of
    the same type is well-typed and out of reach.

    ```
    program Core;

    procedure p (x : int, out r : int)
    {

    };
    procedure caller ()
    {
      var r : int := 0;
      var z : int := 0;
      call p(1, out z);
    };
    ```

    `otherTargetCall_wt` gives the well-typedness of the call. -/
theorem outTarget_gap (labels : List String)
    (C C' : LContext CoreLParams) (ctx' : VarCtx) (n : Nat) :
    (⟨[otherTargetCall], C', ctx'⟩ : GenStmtResult) ∉
      SPMF.support (genStmt (G := SPMF) octx tvars [] [sigP] labels C callerCtx [] n maxStmtSeqLen) := by
  intro h
  rcases mem_genStmt_cmd_inv [] [sigP] labels C C' callerCtx ctx' n _ h with
    ⟨c, hce, hc⟩ | ⟨s, σvals, exprs, mask, hs, hce⟩
  · exact absurd hce (by simp)
  · -- `procs = [sigP]`, so the callee is `sigP` and its instantiation is empty.
    rw [List.mem_singleton] at hs
    subst hs
    rw [show sigP.typeArgs.zip σvals = [] from by simp [sigP]] at hce
    -- Compare the write positions: the recipe writes to `r`, the call writes to `z`.
    rw [CmdExt.call.injEq] at hce
    obtain ⟨-, hargs, -⟩ := hce
    have hlhs := congrArg CallArg.getLhs hargs
    rw [StrataGenerators.Stmt.getLhs_mkArgs, outTargets_sigP] at hlhs
    exact absurd hlhs (by decide)

/-- **`otherTargetCall` is well-typed.** The type instantiation is empty. The one input
    position holds the literal `1` at type `int`. The one write position holds `z`, which the
    scope binds at type `int`. -/
theorem otherTargetCall_wt (C : LContext CoreLParams) (L : List String) :
    StatementWellTyped progP C (procToTCtx callerCtx).types L otherTargetCall C
      (procToTCtx callerCtx).types := by
  have hfind : Program.Procedure.find? progP "p" = some procP := by decide
  refine .cmd _ _ _ _ _ (.call _ "p" _ procP _ [] _ hfind ?_ ?_ ?_ ?_
    (Strata.Util.HMaps.Equiv.refl _))
  · refine ⟨by rw [hfind]; rfl, ?_, by decide, ?_⟩
    · intro proc hproc
      rw [hfind] at hproc
      cases hproc
      exact ⟨by decide, by decide, by decide, by decide⟩
    · simp only [CallArg.getInputExprs, Calls.getInputExprs, List.filterMap_cons,
        List.filterMap_nil, Forall]
      exact ⟨⟩
  · intro v hv
    simp only [CallArg.getLhs, List.filterMap_cons, List.filterMap_nil,
      List.mem_singleton] at hv
    subst hv
    rw [procToTCtx_find]
    decide
  · intro i hi hj
    have hi' : i < 1 := by simpa only [CallArg.getInputExprs, Calls.getInputExprs,
      List.filterMap_cons, List.filterMap_nil, List.length_cons, List.length_nil] using hi
    have hzero : i = 0 := by omega
    subst hzero
    show ExprWellTyped C _ (LExpr.const () (.intConst 1))
      (LMonoTy.subst (Strata.Util.HMaps.ofScopes [[]]) .int)
    rw [Lambda.subst_ofScopes_nilScope]
    refine ⟨.const, ?_, ⟨?_, ?_, ?_⟩⟩
    · intro t ht
      simp [LExpr.binderAnnotations] at ht
    · intro x ann hx
      simp [LExpr.freeVars] at hx
    · intro o ty ho
      simp [LExpr.opAnnots] at ho
    · intro o ho
      simp [LExpr.getOps] at ho
  · intro i hi hj
    have hi' : i < 1 := by simpa only [CallArg.getLhs, List.filterMap_cons,
      List.filterMap_nil, List.length_cons, List.length_nil] using hi
    have hzero : i = 0 := by omega
    subst hzero
    rw [show (ListMap.values procP.header.outputs)[0] = (.int : LMonoTy) from rfl,
      Lambda.subst_ofScopes_nilScope]
    simp only [CallArg.getLhs, List.filterMap_cons, List.filterMap_nil,
      List.getElem_cons_zero]
    rw [procToTCtx_find]
    decide

/-- **The full counterexample for `CallOk`.** `otherTargetCall` is well-typed, and
    `genStmt` cannot reach it at any size. -/
theorem otherTargetCall_gap (labels : List String)
    (C C' : LContext CoreLParams) (ctx' : VarCtx) (n : Nat) :
    StatementWellTyped progP C (procToTCtx callerCtx).types labels otherTargetCall C
        (procToTCtx callerCtx).types ∧
    (⟨[otherTargetCall], C', ctx'⟩ : GenStmtResult) ∉
      SPMF.support (genStmt (G := SPMF) octx tvars [] [sigP] labels C callerCtx [] n maxStmtSeqLen) :=
  ⟨otherTargetCall_wt C labels, outTarget_gap labels C C' ctx' n⟩

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
  have hmem := h .int (LExpr.fvar () ⟨"zzz", ()⟩ (some .int)) HasTypeA.fvar
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

end StrataGenerators.Stmt.SpecComplete.Gaps
