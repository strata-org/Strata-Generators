import StrataGenerators.StmtHasTypeAGenComplete

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Stmt StrataGenerators.Procedure StrataGenerators.Function

/-!
# The side conditions of `spec_complete` are necessary

`spec_complete` in `StmtHasTypeAGenComplete.lean` carries three side conditions:
`InGenShape`, `AlphabetOk` and `CallOk`. This file shows that you cannot remove
them. For each of the three, it gives a statement that is well-typed under
`StatementHasTypeA` but is not in the support of `genStmt`. Therefore no
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
  `loop`, an `exit`, a `funcDecl` and a `typeDecl`. It leaves a `.cmd` node
  untouched. The gap of `metadata_gap` is at a `.cmd` node, so this function
  cannot close it.
* `Core.WF.WFcallProp.lhsWF` gives the `Nodup` fact that `CallOk` needs for the
  write keys of a call. Its parent `Core.WF.WFStatementProp` is not recursive:
  the `block`, `ite` and `loop` cases are empty structures. So it says nothing
  about a call inside a body.
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
    recipe. The other seven branches produce a `block`, an `ite`, a `loop`, an
    `exit`, a `funcDecl` or a `typeDecl`, so they cannot produce a `.cmd`. -/
theorem mem_genStmt_cmd_inv (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C C' : LContext CoreLParams) (ctx ctx' : VarCtx) (n : Nat)
    (ce : Command)
    (h : (⟨[Stmt.cmd ce], C', ctx'⟩ : GenStmtResult) ∈
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n)) :
    (∃ c, ce = CmdExt.cmd c ∧ (⟨c, ctx'⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx n [])) ∨
    (∃ (s : ProcSig) (σvals : List LMonoTy) (exprs : List Expression.Expr) (mask : List Bool),
        s ∈ procs ∧
        ce = CmdExt.call s.pname
          (StrataGenerators.Stmt.mkArgs s.M
            (outTargets immutableVars ctx
              (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O))
            exprs mask) default) := by
  have hcall : ∀ (d : Nat),
      (⟨[Stmt.cmd ce], C', ctx'⟩ : GenStmtResult) ∈
        SetGen.support (genCallStmt (G := SetGen.Set) octx tvars immutableVars procs C ctx d []) →
      (∃ (s : ProcSig) (σvals : List LMonoTy) (exprs : List Expression.Expr) (mask : List Bool),
        s ∈ procs ∧
        ce = CmdExt.call s.pname
          (StrataGenerators.Stmt.mkArgs s.M
            (outTargets immutableVars ctx
              (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O))
            exprs mask) default) := by
    intro d hmem
    cases procs with
    | nil => exact ((SetGen.bot_mem_iff _).mp hmem).elim
    | cons p0 ps =>
      simp only [genCallStmt, mem_support_bind_iff] at hmem
      obtain ⟨s, hs, σvals, _, hmem⟩ := hmem
      split at hmem
      · simp only [mem_support_bind_iff, mem_support_pure_iff] at hmem
        obtain ⟨exprs, _, mask, _, heq⟩ := hmem
        simp only [GenStmtResult.mk.injEq] at heq
        have := initChain_append_call_singleton heq.1
        exact ⟨s, σvals, exprs, mask, (mem_support_elements_iff (by simp)).mp hs, by
          simpa only [Statement.call, Stmt.cmd.injEq] using this⟩
      · exact ((SetGen.bot_mem_iff _).mp hmem).elim
  have hcmdstmt : ∀ (d : Nat),
      (⟨[Stmt.cmd ce], C', ctx'⟩ : GenStmtResult) ∈
        SetGen.support (genCmdStmt (G := SetGen.Set) octx tvars immutableVars C ctx d []) →
      (∃ c, ce = CmdExt.cmd c ∧ (⟨c, ctx'⟩ : GenCmdResult) ∈
        SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx d [])) := by
    intro d hmem
    simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hmem
    obtain ⟨r, hr, heq⟩ := hmem
    simp only [GenStmtResult.mk.injEq, List.cons.injEq, and_true, Stmt.cmd.injEq] at heq
    obtain ⟨rfl, _, rfl⟩ := heq
    exact ⟨r.cmd, rfl, hr⟩
  have hexit :
      (⟨[Stmt.cmd ce], C', ctx'⟩ : GenStmtResult) ∈
        SetGen.support (genExitStmt (G := SetGen.Set) labels C ctx) → False := by
    intro hmem
    cases labels with
    | nil => exact (SetGen.bot_mem_iff _).mp hmem
    | cons hd tl =>
      simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff,
        GenStmtResult.mk.injEq, List.cons.injEq, reduceCtorEq, false_and,
        and_false, exists_false] at hmem
  have hfunc : ∀ (d : Nat),
      (⟨[Stmt.cmd ce], C', ctx'⟩ : GenStmtResult) ∈
        SetGen.support (genFuncDeclStmt (G := SetGen.Set) octx C ctx d []) → False := by
    intro d hmem
    simp only [genFuncDeclStmt, mem_support_bind_iff, mem_support_pure_iff,
      GenStmtResult.mk.injEq, List.cons.injEq, reduceCtorEq, false_and,
      and_false, exists_false] at hmem
  have htype : ∀ (d : Nat),
      (⟨[Stmt.cmd ce], C', ctx'⟩ : GenStmtResult) ∈
        SetGen.support (genTypeDeclStmt (G := SetGen.Set) C ctx d) → False := by
    intro d hmem
    simp only [genTypeDeclStmt, mem_support_bind_iff] at hmem
    obtain ⟨tc, _, hmem⟩ := hmem
    split at hmem
    · simp only [mem_support_pure_iff, GenStmtResult.mk.injEq, List.cons.injEq,
        reduceCtorEq, false_and] at hmem
    · exact (SetGen.bot_mem_iff _).mp hmem
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff] at h
    obtain ⟨w, g, hg, hw, hmem⟩ := h
    simp only [List.mem_cons, Prod.mk.injEq] at hg
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hg
    · exact Or.inl (hcmdstmt 0 hmem)
    · exact (hexit hmem).elim
    · exact (hfunc 0 hmem).elim
    · exact (htype 0 hmem).elim
    · exact Or.inr (hcall 0 hmem)
    · simp at hg
  | succ m =>
    rw [genStmt, mem_support_frequency_iff] at h
    obtain ⟨w, g, hg, hw, hmem⟩ := h
    simp only [List.mem_cons, Prod.mk.injEq] at hg
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hg
    · exact Or.inl (hcmdstmt (m+1) hmem)
    · exact (hexit hmem).elim
    · exact (hfunc (m+1) hmem).elim
    · exact (htype (m+1) hmem).elim
    · exact Or.inr (hcall (m+1) hmem)
    · exact absurd hmem (by
        simp only [mem_support_bind_iff, mem_support_pure_iff, GenStmtResult.mk.injEq,
          List.cons.injEq, reduceCtorEq, false_and, and_false, exists_false, not_false_eq_true])
    · exact absurd hmem (by
        simp only [mem_support_bind_iff, mem_support_pure_iff, GenStmtResult.mk.injEq,
          List.cons.injEq, reduceCtorEq, false_and, and_false, exists_false, not_false_eq_true])
    · exact absurd hmem (by
        simp only [mem_support_bind_iff, mem_support_pure_iff, GenStmtResult.mk.injEq,
          List.cons.injEq, reduceCtorEq, false_and, and_false, exists_false, not_false_eq_true])
    · exact absurd hmem (by
        simp only [mem_support_bind_iff, mem_support_pure_iff, GenStmtResult.mk.injEq,
          List.cons.injEq, reduceCtorEq, false_and, and_false, exists_false, not_false_eq_true])
    · simp at hg

/-- **Inversion at an `assert` command.** `genAssertCmd` is the only branch of
    `genCmd` that produces an `assert`. It emits `default` metadata, and it draws
    the label from `genIdentName`. -/
theorem mem_genCmd_assert_inv (immutableVars : List (Identifier Unit)) (ctx ctx' : VarCtx)
    (n : Nat) (l : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (h : (⟨.assert l e md, ctx'⟩ : GenCmdResult) ∈
      SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx n [])) :
    md = default ∧ l ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  rw [genCmd_support_iff] at h
  rcases h with h | h | ⟨_, h⟩ | ⟨_, h⟩ | h | h | h
  · simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff,
      GenCmdResult.mk.injEq, reduceCtorEq, false_and, exists_false, and_false] at h
  · simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff,
      GenCmdResult.mk.injEq, reduceCtorEq, false_and, exists_false, and_false] at h
  · simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff,
      GenCmdResult.mk.injEq, reduceCtorEq, false_and, exists_false, and_false] at h
  · simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff,
      GenCmdResult.mk.injEq, reduceCtorEq, false_and, exists_false, and_false] at h
  · simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff,
      GenCmdResult.mk.injEq, Cmd.assert.injEq] at h
    obtain ⟨l', hl', e', _, ⟨rfl, _, rfl⟩, _⟩ := h
    exact ⟨rfl, hl'⟩
  · simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff,
      GenCmdResult.mk.injEq, reduceCtorEq, false_and, exists_false, and_false] at h
  · simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff,
      GenCmdResult.mk.injEq, reduceCtorEq, false_and, exists_false, and_false] at h

-- ── Well-typedness of an `assert` ────────────────────────────────────────

/-- An `assert` with a `bool` expression is well-typed at every label and at
    every metadata value. The `assert` rule constrains only the expression. -/
theorem assert_wt (P : Program) (C : LContext CoreLParams) (Γ : TContext Unit) (L : List String)
    (l : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (he : LExpr.HasTypeA [] e (.bool)) :
    StatementHasTypeA P C Γ L (Statement.assert l e md) C Γ :=
  .cmd _ _ _ _ _ _ (.cmd _ _ _ (.assert _ _ _ _ _ he (TContext.Equiv.refl _)))
    (TContext.Equiv.refl _)

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
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
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
    (hl : l ∉ SetGen.support (genIdentName (G := SetGen.Set))) :
    (⟨[Statement.assert l e default], C', ctx'⟩ : GenStmtResult) ∉
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
  intro h
  rcases mem_genStmt_cmd_inv immutableVars procs labels C C' ctx ctx' n _ h with
    ⟨c, hce, hc⟩ | ⟨s, σvals, exprs, mask, _, hce⟩
  · rw [CmdExt.cmd.injEq] at hce; subst hce
    exact hl (mem_genCmd_assert_inv immutableVars ctx ctx' n l e default hc).2
  · exact absurd hce (by simp)

/-- The empty label is not a legal identifier, so `label_gap` applies to it. An
    identifier needs a first character. -/
theorem emptyLabel_not_reachable :
    "" ∉ SetGen.support (genIdentName (G := SetGen.Set)) := by
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

/-- With `r : int` in scope, the generator's out target for `procP` is `r`. -/
theorem outTargets_sigP :
    outTargets [] callerCtx (StrataGenerators.Stmt.substSig [] sigP.O)
      = [(⟨"r", ()⟩, (.int : LMonoTy))] := by
  decide

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
      SetGen.support (genStmt (G := SetGen.Set) octx tvars [] [sigP] labels C callerCtx [] n) := by
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

/-- **`otherTargetCall` is well-typed.** The type instantiation is empty. The one
    input position holds the literal `1` at type `int`. The one write position holds
    `z`, which the scope binds at type `int`. The input parameter `x` is not an
    output parameter, so the in-out premise is vacuous. -/
theorem otherTargetCall_wt (C : LContext CoreLParams) (L : List String) :
    StatementHasTypeA progP C (procToTCtx callerCtx) L otherTargetCall C
      (procToTCtx callerCtx) := by
  refine .cmd _ _ _ _ _ _ (.call _ "p" _ procP _ [] _ (by decide) ?_ ?_ ?_ ?_ ?_ ?_
    (TContext.Equiv.refl _)) (TContext.Equiv.refl _)
  · decide
  · decide
  · intro v hv
    simp only [CallArg.getLhs, List.filterMap_cons, List.filterMap_nil,
      List.mem_singleton] at hv
    subst hv
    rw [procToTCtx_find]
    decide
  · intro i hi hj
    have hi' : i < 1 := by simpa only [CallArg.getInputExprs, List.filterMap_cons,
      List.filterMap_nil, List.length_cons, List.length_nil] using hi
    have : i = 0 := by omega
    subst this
    refine ⟨.int, ?_, ?_⟩
    · show AliasEquiv _ _ (LMonoTy.subst (Strata.Util.HMaps.ofScopes [[]]) _)
      rw [show (ListMap.values procP.header.inputs)[0] = (.int : LMonoTy) from rfl,
        show Strata.Util.HMaps.ofScopes [([] : List (TyIdentifier × LMonoTy))]
          = [Strata.Util.HMap.empty] from rfl, LMonoTy.subst_single_empty]
      exact .refl
    · exact .const
  · intro i hi hj
    have hi' : i < 1 := by simpa only [CallArg.getLhs, List.filterMap_cons,
      List.filterMap_nil, List.length_cons, List.length_nil] using hi
    have : i = 0 := by omega
    subst this
    refine ⟨.int, ?_, ?_⟩
    · show AliasEquiv _ _ (LMonoTy.subst (Strata.Util.HMaps.ofScopes [[]]) _)
      rw [show (ListMap.values procP.header.outputs)[0] = (.int : LMonoTy) from rfl,
        show Strata.Util.HMaps.ofScopes [([] : List (TyIdentifier × LMonoTy))]
          = [Strata.Util.HMap.empty] from rfl, LMonoTy.subst_single_empty]
      exact .refl
    · simp only [CallArg.getLhs, List.filterMap_cons, List.filterMap_nil,
        List.getElem_cons_zero]
      rw [procToTCtx_find]
      decide
  · intro i hi hcontains
    have hi' : i < 1 := by simpa only [ListMap.keys, procP,
      List.length_cons, List.length_nil] using hi
    have : i = 0 := by omega
    subst this
    simp only [ListMap.keys, procP, List.getElem_cons_zero] at hcontains
    exact absurd hcontains (by decide)

/-- **The full counterexample for `CallOk`.** `otherTargetCall` is well-typed, and
    `genStmt` cannot reach it at any size. -/
theorem otherTargetCall_gap (labels : List String)
    (C C' : LContext CoreLParams) (ctx' : VarCtx) (n : Nat) :
    StatementHasTypeA progP C (procToTCtx callerCtx) labels otherTargetCall C
        (procToTCtx callerCtx) ∧
    (⟨[otherTargetCall], C', ctx'⟩ : GenStmtResult) ∉
      SetGen.support (genStmt (G := SetGen.Set) octx tvars [] [sigP] labels C callerCtx [] n) :=
  ⟨otherTargetCall_wt C labels, outTarget_gap labels C C' ctx' n⟩

-- ── `spec_complete`'s old environment hypotheses were unsatisfiable ──────────

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

/-- **The old `hExprC` was unsatisfiable**, so the old `spec_complete` was vacuous.
    Instantiate at `ctx = []`. -/
theorem hExprC_unsatisfiable :
    ¬ (∀ d (ctx : VarCtx), GenLExprComplete ctx.toFVarCtx octx tvars d) := by
  intro h; exact not_GenLExprComplete 0 (h 0 [])

-- ── The `funcDecl` rule is broken upstream ──────────────────────────────────

/-! ### `StatementHasType'.funcDecl` never checks the function it declares

```
| funcDecl : ∀ C Γ L decl func md Δ,
    ¬ decl.isRecursive →
    FuncHasType' τ C Γ func →
    TContext.Equiv Δ Γ →
    StatementHasType' τ P C Γ L (.funcDecl decl md) (C.addFactoryFunction func.toLFunc) Δ
```

The declaration occurs in one premise only, which says that it is not recursive. The function that the rule
*type checks*, and that goes into the output context, is a separate function. The docstring of the rule says
that the resulting function goes into the context, and it means the function that the declaration gives. No
premise connects the two. The algorithmic checker in `Core.StatementType` does connect them:

```
let (decl', func, Env) ← PureFunc.typeCheck C Env decl   -- func := ofPureFunc decl, checked
let C := C.addFactoryFunction func.toLFunc
```

Two consequences, both witnessed below by `funcDecl_illTyped_accepted`:

1. **The specification accepts a local declaration that is ill typed.** No premise checks the declaration.
   Therefore `function f (x : int) : bool { x };` is well formed under the rule, and the type of its body is
   `int` against a declared result type of `bool`. The real checker rejects it.
2. **The rule puts no condition on the output context.** It adds *each* well-typed function, and the one here
   does not even carry the declared name. `FuncHasType'` is a structure of six fields, and it constrains no
   name, no attribute, no axiom, the recursion of the function and the number of its preconditions.
   `genFunction_complete` needs each of those conditions. Therefore the function that the rule adds can also be
   a function that `genFunction` never gives. That fact is what blocks a completeness theorem with no side
   condition at a `funcDecl` node, and it is why the `.funcDecl` clause of `SpecComplete.ExprOk` is `False`.

The fix is to add the premise the algorithm already computes,
`Function.ofPureFunc decl = .ok func` (or the `tyCompat`-style agreement, if
`Function.typeCheck` annotates a signature field). Then `func` is determined by
`decl`, its reachability follows from the declaration's, and the clause can go. -/

/-- The declaration `function f (x : int) : bool { x };`. The type of its body is `int`, and its declared result
    type is `bool`. Therefore this declaration is not well typed. -/
def illTypedDecl : Imperative.PureFunc Expression :=
  { name := ⟨"f", ()⟩, typeArgs := [], isConstr := false, isRecursive := false,
    inputs := [(⟨"x", ()⟩, (.forAll [] .int : LTy))], output := (.forAll [] .bool : LTy),
    body := some (LExpr.fvar () ⟨"x", ()⟩ (some .int)),
    attr := #[], axioms := [], preconditions := [], measure := none }

/-- A trivial well-typed function, whose name is not even the declared one. -/
def unrelatedFunc : Function :=
  { name := ⟨"g", ()⟩, typeArgs := [], inputs := [], output := .bool }

/-- `unrelatedFunc` is well typed in each context that holds the type `bool`. `FuncHasType'` asks for distinct
    inputs, distinct type arguments, no undeclared type variable, and a well-kinded signature. Its two fields
    about a typed body and a typed measure hold with no content here, because this function has neither. -/
theorem unrelatedFunc_wt (C : LContext CoreLParams) (Γ : TContext Unit)
    (hbool : C.WellKindedTy .bool) :
    FuncHasTypeA C Γ unrelatedFunc := by
  refine { inputsNodup := ?_, typeArgsNodup := ?_, noUndeclaredVars := ?_,
           signatureWellKinded := ?_, bodyTyped := ?_, measureTyped := ?_ }
  · show (ListMap.keys ([] : @LMonoTySignature Unit)).Nodup
    simp [ListMap.keys]
  · show ([] : List TyIdentifier).Nodup
    simp
  · intro v hv
    revert hv
    simp [unrelatedFunc, ListMap.values, LMonoTys.freeVars, LMonoTy.bool, LMonoTy.freeVars]
  · intro ty hty
    simp only [unrelatedFunc, ListMap.values, List.mem_cons, List.not_mem_nil, or_false] at hty
    subst hty
    exact ⟨.bool, (congrArg (LMonoTy.tcons "bool") ∘ fun a => a) rfl, hbool⟩
  · simp [unrelatedFunc]
  · simp [unrelatedFunc]

/-- **The counterexample.** The spec accepts a `funcDecl` of an *ill-typed*
    declaration, and puts an *unrelated* function into the output context:

    ```
    program Core;

    procedure caller ()
    {
      function f (x : int) : bool { x };
    };
    ```

    Under this rule that statement is well-formed, and after it the context holds a
    function called `g`. Both halves are wrong, and each on its own is enough to
    force the spec change described above. -/
theorem funcDecl_illTyped_accepted (P : Program) (C : LContext CoreLParams)
    (Γ : TContext Unit) (L : List String) (hbool : C.WellKindedTy .bool) :
    StatementHasTypeA P C Γ L (.funcDecl illTypedDecl default)
      (C.addFactoryFunction unrelatedFunc.toLFunc) Γ :=
  StatementHasType'.funcDecl C Γ L illTypedDecl unrelatedFunc default Γ
    (by simp [illTypedDecl]) (unrelatedFunc_wt C Γ hbool) (tctxEquivRefl _)

end StrataGenerators.Stmt.SpecComplete.Gaps
