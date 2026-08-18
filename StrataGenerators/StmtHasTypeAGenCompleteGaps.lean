import StrataGenerators.StmtHasTypeAGenComplete

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString ArbChar
open StrataGenerators.Stmt StrataGenerators.Procedure StrataGenerators.Function

/-!
# The side conditions of `spec_complete` are necessary

`spec_complete` in `StmtHasTypeAGenComplete.lean` carries three side conditions:
`InGenShape`, `AlphabetOk` and `CallOk`. This file shows that you cannot remove
them. For each of the three, it gives a statement that is well-typed under
`StatementHasTypeA` but is not in the support of `genStmt`. Therefore no
completeness theorem holds for `genStmt` without a side condition of this kind.

Each counterexample is a real Strata Core program. The docstring of each gap
theorem gives the source text. `Core.formatProgram` produced that text from the
statement in the theorem.

## The three gaps

| Predicate     | Clause that survives            | Gap theorem            |
| ------------- | ------------------------------- | ---------------------- |
| `InGenShape`  | `md = default`                  | `metadata_gap`         |
| `AlphabetOk`  | label in `String.arbitrary`     | `label_gap`            |
| `CallOk`      | `args = mkArgs …`               | `call_argorder_gap`    |

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

## The one clause with no source-level counterexample

`InGenShape` also demands that an `init` annotation is monomorphic
(`.forAll [] mty`). The Core front end builds only `.forAll []` local
annotations (`translateInitStatement` and `translateVarStatement` in
`Strata/Languages/Core/DDMTransform/Translate.lean`). So this clause is
necessary at the level of the abstract syntax tree, but no parsed program can
violate it.
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
    (∃ (pn : String) (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr),
        ce = CmdExt.call pn (StrataGenerators.Stmt.mkArgs M T exprs) default) := by
  have hcall : ∀ (d : Nat),
      (⟨[Stmt.cmd ce], C', ctx'⟩ : GenStmtResult) ∈
        SetGen.support (genCallStmt (G := SetGen.Set) octx tvars immutableVars procs C ctx d []) →
      (∃ (pn : String) (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr),
        ce = CmdExt.call pn (StrataGenerators.Stmt.mkArgs M T exprs) default) := by
    intro d hmem
    cases procs with
    | nil => exact ((SetGen.bot_mem_iff _).mp hmem).elim
    | cons p0 ps =>
      simp only [genCallStmt, mem_support_bind_iff] at hmem
      obtain ⟨s, _, σvals, _, hmem⟩ := hmem
      split at hmem
      · simp only [mem_support_bind_iff, mem_support_pure_iff] at hmem
        obtain ⟨exprs, _, heq⟩ := hmem
        simp only [GenStmtResult.mk.injEq] at heq
        have := initChain_append_call_singleton heq.1
        exact ⟨s.pname, s.M, _, exprs, by
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
    the label from `String.arbitrary`. -/
theorem mem_genCmd_assert_inv (immutableVars : List (Identifier Unit)) (ctx ctx' : VarCtx)
    (n : Nat) (l : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (h : (⟨.assert l e md, ctx'⟩ : GenCmdResult) ∈
      SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx n [])) :
    md = default ∧ l ∈ SetGen.support (String.arbitrary (G := SetGen.Set)) := by
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

/-- A string with one character outside `alphanumChars` is outside the support of
    `String.arbitrary`. -/
theorem not_mem_String_arbitrary {s : String} {c : Char} (hc : c ∈ s.toList)
    (hnc : c ∉ alphanumChars) : s ∉ SetGen.support (String.arbitrary (G := SetGen.Set)) := by
  intro h
  simp only [String.arbitrary, mem_support_map_iff] at h
  obtain ⟨cs, hcs, rfl⟩ := h
  rw [String.toList_ofList] at hc
  have hmem := SetGen.mem_support_listOf hcs c hc
  rw [Char.arbitrary, mem_support_elements_iff
    (show alphanumChars ≠ [] from by decide +kernel)] at hmem
  exact hnc hmem

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
    ⟨c, hce, hc⟩ | ⟨pn, M, T, exprs, hce⟩
  · rw [CmdExt.cmd.injEq] at hce; subst hce
    exact hmd (mem_genCmd_assert_inv immutableVars ctx ctx' n l e md hc).1
  · exact absurd hce (by simp)

/-- The metadata of `mdKey` is not `default`, so `metadata_gap` applies to it. -/
example : (#[mdKey] : Imperative.MetaData Expression) ≠ default := by decide

-- ── Gap 2: the alphabet clause of `AlphabetOk` ───────────────────────────

/-- **Gap 2: the label alphabet.** `genAssertCmd` draws an `assert` label from
    `String.arbitrary`, whose support holds the alphanumeric strings only. A
    label with an underscore is a legal Core label, and the `assert` rule accepts
    every label, so such a statement is well-typed and out of reach.

    ```
    program Core;

    procedure caller ()
    {
      assert [loop_invariant]: true;
    };
    ```

    `assert_wt` gives the well-typedness of the body statement. The same gap
    applies to an `assume` label, to a `cover` label and to an `init` variable
    name. An `init` name comes from `NonEmptyString.arbitrary`, which has the
    same alphabet. -/
theorem label_gap (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C C' : LContext CoreLParams) (ctx ctx' : VarCtx) (n : Nat)
    (l : String) (e : Expression.Expr) {c₀ : Char} (hc₀ : c₀ ∈ l.toList)
    (hnc₀ : c₀ ∉ alphanumChars) :
    (⟨[Statement.assert l e default], C', ctx'⟩ : GenStmtResult) ∉
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
  intro h
  rcases mem_genStmt_cmd_inv immutableVars procs labels C C' ctx ctx' n _ h with
    ⟨c, hce, hc⟩ | ⟨pn, M, T, exprs, hce⟩
  · rw [CmdExt.cmd.injEq] at hce; subst hce
    exact not_mem_String_arbitrary hc₀ hnc₀
      (mem_genCmd_assert_inv immutableVars ctx ctx' n l e default hc).2
  · exact absurd hce (by simp)

/-- The label `loop_invariant` holds an underscore, so `label_gap` applies to
    it. -/
example : '_' ∈ "loop_invariant".toList ∧ '_' ∉ alphanumChars := by decide +kernel

-- ── Gap 3: the recipe clause of `CallOk` ─────────────────────────────────

/-- `mkArgs` puts every `inoutArg` first, then every `inArg`, then every
    `outArg`. So it never puts an `outArg` before an `inArg`. -/
theorem mkArgs_ne_out_then_in (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (y : Identifier Unit) (e : Expression.Expr) :
    StrataGenerators.Stmt.mkArgs M T exprs ≠ [CallArg.outArg y, CallArg.inArg e] := by
  cases M with
  | cons hd tl => simp [StrataGenerators.Stmt.mkArgs]
  | nil =>
    cases exprs with
    | cons hd tl => simp [StrataGenerators.Stmt.mkArgs]
    | nil =>
      cases T with
      | nil => simp [StrataGenerators.Stmt.mkArgs]
      | cons hd tl =>
        cases tl with
        | nil => simp [StrataGenerators.Stmt.mkArgs]
        | cons hd2 tl2 => simp [StrataGenerators.Stmt.mkArgs]

/-- **Gap 3: the order of the call arguments.** The `call` rule constrains the
    input positions and the write positions of a call one by one. It does not
    constrain the order of the `CallArg` nodes. `mkArgs` fixes that order. So a
    call that puts an `out` argument before a by-value input is well-typed and
    out of reach, for every procedure context `procs`.

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
    ```

    `badOrderCall_wt` gives the well-typedness of the call. -/
theorem call_argorder_gap (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C C' : LContext CoreLParams) (ctx ctx' : VarCtx) (n : Nat)
    (pname : String) (y : Identifier Unit) (e : Expression.Expr)
    (md : Imperative.MetaData Expression) :
    (⟨[Statement.call pname [CallArg.outArg y, CallArg.inArg e] md], C', ctx'⟩ : GenStmtResult) ∉
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) := by
  intro h
  rcases mem_genStmt_cmd_inv immutableVars procs labels C C' ctx ctx' n _ h with
    ⟨c, hce, hc⟩ | ⟨pn, M, T, exprs, hce⟩
  · exact absurd hce (by simp)
  · rw [CmdExt.call.injEq] at hce
    exact mkArgs_ne_out_then_in M T exprs y e hce.2.1.symm

/-- The callee of the counterexample: `procedure p (x : int, out r : int)`. -/
def procP : Procedure :=
  { header := { name := ⟨"p", ()⟩, typeArgs := [],
                inputs := [(⟨"x", ()⟩, .int)], outputs := [(⟨"r", ()⟩, .int)] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] }

/-- The program that declares `procP`. -/
def progP : Program := { decls := [.proc procP .empty] }

/-- The scope of the caller: `y : int` and `z : int`. -/
def callerCtx : VarCtx := [(⟨"y", ()⟩, .int), (⟨"z", ()⟩, .int)]

/-- The call `call p(out y, 1);`. The `out` argument comes before the by-value
    input. -/
def badOrderCall : Statement :=
  Statement.call "p" [CallArg.outArg ⟨"y", ()⟩, CallArg.inArg (LExpr.const () (.intConst 1))] default

/-- **`badOrderCall` is well-typed.** The type instantiation is empty. The one
    input position holds the literal `1` at type `int`. The one write position
    holds `y`, which the scope binds at type `int`. The input parameter `x` is
    not an output parameter, so the in-out premise is vacuous. -/
theorem badOrderCall_wt (C : LContext CoreLParams) (L : List String) :
    StatementHasTypeA progP C (procToTCtx callerCtx) L badOrderCall C (procToTCtx callerCtx) := by
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

/-- **The full counterexample for `CallOk`.** `badOrderCall` is well-typed, and
    `genStmt` cannot reach it at any size and at any procedure context. -/
theorem badOrderCall_gap (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (labels : List String) (C C' : LContext CoreLParams) (ctx ctx' : VarCtx) (n : Nat) :
    StatementHasTypeA progP C (procToTCtx callerCtx) labels badOrderCall C
        (procToTCtx callerCtx) ∧
    (⟨[badOrderCall], C', ctx'⟩ : GenStmtResult) ∉
      SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx [] n) :=
  ⟨badOrderCall_wt C labels,
    call_argorder_gap immutableVars procs labels C C' ctx ctx' n _ _ _ _⟩

end StrataGenerators.Stmt.SpecComplete.Gaps
