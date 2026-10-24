import StrataGenerators.ProcedureHasTypeAGen.Support

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Stmt StrataGenerators.Procedure StrataGenerators.Function

/-!
# The completeness of `genStmt` and `genStmtChain`, indexed by `StatementHasTypeW`

`spec_complete` proves that each well-typed statement is in the support of `genStmt`. The declarative
relation `StatementHasTypeW`, in `Strata.Languages.Core.WeakTypeSpec`, decides which statements are
well typed. The proof needs **no** helper relation that follows the shape of the generator. It runs by
induction on the *typing derivation* itself, through the two mutually recursive theorems
`genStmt_spec_complete` and `genStmtChain_spec_complete`.

## The side conditions

A random generator with a bound cannot reach *each* well-typed statement, so its support is strictly
narrower than the set that the specification accepts. Four recursive predicates over the tree of a
statement hold the remaining gaps. Each of them is a **function** that gives a `Prop`, and none of them is
an inductive relation:

* **`InGenShape`** holds the two facts about a shape that the generator fixes and that the specification
  leaves free. Those facts are that the metadata is the default value, and that the annotation of an `init`
  is monomorphic.
* **`AlphabetOk`** holds the conditions about the alphabet of an identifier and about a size. Each
  generated *name* is in the support of `genIdentName`, which holds exactly the legal bare identifiers of
  Core that are not a reserved keyword. That condition covers the label of an `assert`, of an `assume` and
  of a `cover`, the label of a block and of an invariant, the variable of an `init`, and the name of a type
  constructor with its parameters. Each generated *list* is inside the budget for a size at its depth. The
  type of an `init` is in the support of `genLMonoTy`.
* **`CallOk`** holds the shape of a call. A `.cmd (.call …)` statement is reachable only when its argument
  list is the recipe of the generator, which is `mkArgs` over `outTargets`, for some callee, at some
  sampled instantiation of the type parameters and some mask for the order of the arguments. The predicate
  is `True` at each node that is not a call, and it recurses into each nested body.
* **`ExprOk`** holds the reachability of each expression, through the scope and the size at each node. Each
  expression of the statement is in the support of `genLExpr`, at the size of *its own* level of the
  nesting, and in the scope that is available *there*. Each binder annotation of it is a type that the
  generator can make (`binderAnnotsGenerable`), since the generator keeps an expression only then.

## No proof can remove the predicates

`StmtHasTypeAGenCompleteGaps.lean` proves that `InGenShape`, `AlphabetOk` and `CallOk` are
necessary. For each of them, it gives a statement that `StatementHasTypeW` accepts and that the
support of `genStmt` does not hold.
Those theorems are `metadata_gap`, `label_gap` and `outTarget_gap`.

One of the gaps has a counterexample that a person can write in Core:

* `outTargets` picks the receiving variable of each `out` parameter itself, and the specification accepts
  each writable variable of the correct type. Read `outTarget_gap`. `genStmt` also emits the default
  metadata, and the grammar of Core has a prefix for an annotation on each statement. Read `metadata_gap`.

Each other gap needs a witness that lives in the abstract syntax tree alone. `genAssertCmd`,
`genAssumeCmd`, `genCoverCmd` and `genFreshName` each draw from `genIdentName`, so each name of a parsed
program is reachable. `mkArgs` takes a mask for an interleaving, so the order of an `inArg` and an `outArg`
is free, and a call such as `call p(out y, 1);` is reachable.

Three predicates of Strata come close to a condition here, and none of them discharges one:

* `Imperative.Stmt.stripMetaData` erases the metadata of a `block`, an `ite`, a `loop`, an `exit` and a
  `typeDecl`. It leaves a `.cmd` node unchanged, and the gap about the metadata is at a
  `.cmd` node.
* `Core.WF.WFcallProp.lhsWF` states the fact about distinct names that `CallOk` needs for the written-to
  keys of a call. Its parent `Core.WF.WFStatementProp` is not recursive, because its cases for a `block`,
  an `ite` and a `loop` are empty structures. Therefore it says nothing about a call inside a body.
* `LContext.WellKindedTy`, which is a premise of each `init` rule, bounds the type constructors of an
  annotation. The support of `genLMonoTy` also bounds the depth of the type and its free type variables, so
  `WellKindedTy` is too weak for the clause of `AlphabetOk` about an `init`.

The other clause of `InGenShape` asks that the annotation of an `init` is monomorphic. The front end of
Core builds a local annotation of that form only, so no parsed program can break that clause. It is
necessary at the level of the abstract syntax tree only.

The *correspondence* for a procedure call is a top-level hypothesis, `ProcSigComplete procs P`, which is
the converse of `ProcSigCorresponds`. It says that the context `procs` of the generator holds the callee
that a well-typed call resolves in the program. The parameter `immutableVars` is the empty list. That
parameter is a notion at the level of a procedure, and it has no content at the level of a statement,
because the writable part of a context at the empty list is that context itself.

## Why the side conditions are per expression, and not per environment

A hypothesis of the form "each expression that the specification accepts at a type is in the support of
`genLExpr` at a fixed depth" is **unsatisfiable**, and `Gaps.hExprC_unsatisfiable` machine-checks that
fact. It fails twice over, at a leaf:

* **The scope.** The rule `HasTypeA.fvar` accepts an *annotated* free variable against the empty context,
  because it reads the type from the annotation. With an empty context of free variables, nothing in the
  support holds a free variable, which `genLExpr_no_fvars` proves. That obstruction does not depend on the
  depth.
* **The depth.** `genLExpr` recurses structurally on the depth, so its support at a fixed depth has a
  bounded depth, and the specification accepts a term of each depth.

An existential over the depth does **not** help, because the predicate is false at each depth, so the
existential is false too. `Gaps.not_exists_depth_GenLExprComplete` proves that. The quantifier must move
*inside*, to one expression at a time, in a scope that holds the free variables of that expression, and at
a depth that bounds it. `ExprOk` is that predicate. `exprOk_assert_of_syntactic` discharges one clause of
it from exactly the syntactic side conditions of `genLExpr_complete`, and `exprOk_assert_true` gives a
statement that satisfies it.

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

/-- A fresh `genIdentName` name that is not in `avoid` is in `genFreshName`'s support.
    `genFreshName` draws from `genIdentName`, whose support holds no keyword, so this needs no
    separate `dodgeKeyword` premise. -/
theorem freshName_reach (ctx : VarCtx) (x : Identifier Unit) {avoid : List String}
    (hname : x.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hfresh : Map.find? ctx x = none) (havoid : x.name ∉ avoid) :
    x.name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx avoid) := by
  simp only [genFreshName, mem_support_bind_iff]
  refine ⟨x.name, hname, ?_⟩
  simp only [mem_support_ite_iff, mem_support_pure_iff]
  refine Or.inl ⟨?_, trivial⟩
  have hctx : VarCtx.isFresh ctx ⟨x.name, ()⟩ = true := by
    unfold VarCtx.isFresh VarCtx.find?; obtain ⟨nm, u⟩ := x; cases u; rw [hfresh]; rfl
  simp only [hctx, Bool.true_and, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not]
  exact havoid

theorem writable_nil_eq (ctx : VarCtx) : ctx.writable [] = ctx := by
  rw [VarCtx.writable]; exact List.filter_eq_self.mpr (fun _ _ => rfl)

-- ── Residual shape side condition (`InGenShape`) ────────────────────────────
-- Two facts about a shape belong here: the metadata is the default value, and
-- the annotation of an `init` is monomorphic. The generator reaches each other shape. It draws a
-- label from `genIdentName` and both boundedness values for a `typeDecl`. A procedure `call` is
-- admissible here (its further conditions about the recipe and the instantiation live in `CallOk`).
--
-- `metadata_gap` (`StmtHasTypeAGenCompleteGaps.lean`) shows that the metadata
-- clause is necessary.

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
  | .typeDecl _ md => md = default

/-- `InGenShape` lifted to a statement list. -/
def InGenShapeList : List Statement → Prop
  | [] => True
  | s :: ss => InGenShape s ∧ InGenShapeList ss
end

-- ── Residual alphabet/size side condition (`AlphabetOk`) at size `n` ─────────

mutual
/-- The identifier-alphabet + size kernel, recursively over the tree, at size `n`.
    Names lie in their generator's support, and each generated list is within the
    budget available at its nesting depth.

    Each clause about a *name* is one condition: membership in the support of `genIdentName`, which holds
    exactly the legal bare identifiers of Core that are not a reserved keyword, and which
    `mem_support_genIdentName_iff_isId` describes. Therefore no
    program that the Core parser accepts can break a name clause. The clauses
    stay, because a `Statement` holds a bare `String`, which need not be a legal identifier. `label_gap`, in
    `StmtHasTypeAGenCompleteGaps.lean`, is the counterexample, and no program that a person writes in Core has
    that shape.

    The clause for an `init` needs no separate condition about a keyword, because
    `genIdentName`'s support already excludes every keyword. The clause for a `typeDecl` also asks
    for a local type name (`isLocalTypeName`). -/
def AlphabetOk (tvars : List TyIdentifier) : Nat → Statement → Prop
  | n, .cmd (CmdExt.cmd (.init x (.forAll [] mty) _ _)) =>
      x.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) ∧
      mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n)
  | _, .cmd (CmdExt.cmd (.init _ _ _ _)) => True
  | _, .cmd (CmdExt.cmd (.set _ _ _)) => True
  | _, .cmd (CmdExt.cmd (.assert l _ _)) =>
      l ∈ SetGen.support (genIdentName (G := SetGen.Set))
  | _, .cmd (CmdExt.cmd (.assume l _ _)) =>
      l ∈ SetGen.support (genIdentName (G := SetGen.Set))
  | _, .cmd (CmdExt.cmd (.cover l _ _)) =>
      l ∈ SetGen.support (genIdentName (G := SetGen.Set))
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
  | n, .typeDecl tc _ =>
      isLocalTypeName tc.name = true ∧
      tc.name ∈ SetGen.support (genIdentName (G := SetGen.Set)) ∧ tc.params.length ≤ n ∧
      (∀ s ∈ tc.params, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))

/-- `AlphabetOk` lifted to a statement list at size `n`. -/
def AlphabetOkList (tvars : List TyIdentifier) : Nat → List Statement → Prop
  | _, [] => True
  | n, s :: ss => AlphabetOk tvars n s ∧ AlphabetOkList tvars n ss
end

-- ── Scope threading for the call recipe ─────────────────────────────────────

/-- The output scope of the variables of a statement, as the generator threads it. Only an `init` extends the
    scope, with its own fresh variable. Each other constructor leaves the scope unchanged, and that includes a
    *well-typed* `call`, because each argument of such a call is already in scope and its chain of `init`
    statements is therefore empty. This definition gives the same scope as the completeness proof gives at each
    node, and `CallOkList` threads it, so that `outTargets` of a nested `call` reads the scope at that node. -/
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
    `σ := s.typeArgs.zip σvals`) and *some* argument-order mask `mask`:
    `mkArgs s.M (outTargets [] ctx (substSig σ s.O)) exprs mask` for some callee `s`
    and for some by-value inputs. The predicate also holds the guard of the generator, which asks for a usable
    instantiated in-out block and for distinct written-to keys, the reachability of each input by `genLExpr` at
    the *instantiated* input type of the callee, binder annotations of each input that the generator can
    make, and the absence of a necessary fresh `init` statement (a
    well-typed call has all names in scope, so the emitted group is the bare call and
    the output scope is `ctx`). `hσvals` places `σvals` in the sampling step's support.
    `True` on every non-call leaf; nested bodies recurse with the body's own scope.

    The `mask` existential is what makes the argument *order* free. `mkArgs` used to
    fix it as in-out, then by-value input, then out target, and a well-typed call in
    any other order was out of reach. The in-out block must still lead, because `M`
    heads both the input signature and the output signature.

    The existential costs nothing: `mkArgs_surjective` shows that some mask reaches
    *every* order-preserving interleaving of the by-value inputs with the out
    targets, and `exists_mask_mkArgs_iff` shows it reaches no more than those. So
    this clause admits exactly the argument orders the `call` rule leaves free. -/
def CallOk (procs : ProcSigCtx) (ctx : VarCtx) (n : Nat) : Statement → Prop
  | .cmd (CmdExt.call pname args _) =>
      ∃ (s : ProcSig) (σvals : List LMonoTy) (exprs : List Expression.Expr)
        (mask : List Bool),
        s ∈ procs ∧
        s.pname = pname ∧
        σvals ∈ SetGen.support
          (s.typeArgs.mapM (fun _ =>
            if hg : (generableTypesFromCtx ctx.values [] octx).length > 0 then
              elements (generableTypesFromCtx ctx.values [] octx)
                (by apply List.ne_nil_of_length_pos; assumption)
            else pure (.bool : LMonoTy)) : SetGen.Set (List LMonoTy)) ∧
        args = StrataGenerators.Stmt.mkArgs s.M
          (outTargets [] ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O))
          exprs mask ∧
        exprs.all binderAnnotsGenerable = true ∧
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
  | .typeDecl _ _ => True

/-- `CallOk` lifted to a statement chain, threading the scope with `stepCtx`. -/
def CallOkList (procs : ProcSigCtx) (ctx : VarCtx) (n : Nat) : List Statement → Prop
  | [] => True
  | s :: ss => CallOk procs ctx n s ∧ CallOkList procs (stepCtx ctx s) n ss
end

-- ── Residual expression-reachability side condition (`ExprOk`) ──────────────

/-- The expressions of one command, reachable by `genLExpr` at size `n` in the scope
    `ctx`, each with binder annotations that the generator can make, since the generator keeps
    an expression only then. This is the per-command half of `ExprOk`.

    `set`'s clause is stated against the type the scope gives its target, because
    that is the type the generator draws the right-hand side at. -/
def CmdExprOk (ctx : VarCtx) (n : Nat) : Cmd Expression → Prop
  | .init _ (.forAll [] mty) (.det e) _ =>
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n mty) ∧
      binderAnnotsGenerable e = true
  | .init _ _ _ _ => True
  | .set x (.det e) _ =>
      (∀ mty, Map.find? ctx x = some mty →
        e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n mty)) ∧
      binderAnnotsGenerable e = true
  | .set _ _ _ => True
  | .assert _ e _ =>
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool) ∧
      binderAnnotsGenerable e = true
  | .assume _ e _ =>
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool) ∧
      binderAnnotsGenerable e = true
  | .cover _ e _ =>
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool) ∧
      binderAnnotsGenerable e = true

mutual
/-- **Expression reachability, threaded through the evolving scope and size.** Every
    expression the statement holds is in `genLExpr`'s support at the size of *its own*
    nesting level and in the scope available *there*.

    A hypothesis of the form `∀ d ctx, GenLExprComplete ctx.toFVarCtx octx tvars d` is **unsatisfiable**, which
    `Gaps.hExprC_unsatisfiable` proves. `GenLExprComplete` asks for *each* well-typed expression at a *fixed*
    depth, and that fails twice over. An annotated free
    variable is well-typed in the empty context but unreachable when the scope is
    empty, and the support of `genLExpr` at a fixed depth has a bounded depth, and the specification accepts a
    term of each depth. An existential over the depth repairs neither obstruction, which
    `Gaps.not_exists_depth_GenLExprComplete` proves. The quantifier must move *inside*, to one expression at a
    time, and this predicate does that.

    It is satisfiable, and `exprOk_assert_of_syntactic` discharges a clause of it from
    the syntactic side conditions of `genLExpr_complete`. Nested bodies drop to `n - 1`
    and re-thread the scope, exactly as `AlphabetOk` and `CallOk` do. -/
def ExprOk (ctx : VarCtx) (n : Nat) : Statement → Prop
  | .cmd (CmdExt.cmd c) => CmdExprOk (octx := octx) (tvars := tvars) ctx n c
  -- A call's by-value inputs are `CallOk`'s business, not this predicate's.
  | .cmd (CmdExt.call _ _ _) => True
  | .block _ body _ => ExprOkList ctx (n - 1) body
  | .ite cond t e _ =>
      (∀ g, cond = .det g →
        g ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool) ∧
        binderAnnotsGenerable g = true) ∧
      ExprOkList ctx (n - 1) t ∧ ExprOkList ctx (n - 1) e
  | .loop guard measure invs body _ =>
      (∀ g, guard = .det g →
        g ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool) ∧
        binderAnnotsGenerable g = true) ∧
      (∀ m, measure = some m →
        m ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .int) ∧
        binderAnnotsGenerable m = true) ∧
      (∀ p ∈ invs, p.2 ∈
        SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool) ∧
        binderAnnotsGenerable p.2 = true) ∧
      ExprOkList ctx (n - 1) body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- `ExprOk` lifted to a statement chain, threading the scope with `stepCtx`. -/
def ExprOkList (ctx : VarCtx) (n : Nat) : List Statement → Prop
  | [] => True
  | s :: ss => ExprOk ctx n s ∧ ExprOkList (stepCtx ctx s) n ss
end

/-- **`ExprOk` is satisfiable.** Its `assert` clause follows from exactly the
    syntactic side conditions of `genLExpr_complete`: the expression is well-typed,
    holds no bound-variable names, has its free variables and operators in the
    ambient contexts, has simple types, and fits the depth budget. The same
    derivation discharges the `assume`/`cover`/`ite`/`loop` clauses, which are the
    same membership at `.bool`, and the `init`/`set` clauses at their own type.

    This is what the old `hExprC` could never have: reachability is claimed for *one*
    expression, in a scope that holds its free variables, at a depth that bounds it. -/
theorem exprOk_assert_of_syntactic (ctx : VarCtx) (n : Nat) (l : String)
    (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (hwt : HasTypeA' [] e .bool)
    (hnames : emptyNames e)
    (hvars : allVarsInCtx ctx.toFVarCtx octx e)
    (hats : AllTypesSimple tvars n [] e)
    (hdepth : termDepth [] e ≤ n)
    (hgen : binderAnnotsGenerable e = true) :
    CmdExprOk (octx := octx) (tvars := tvars) ctx n (.assert l e md) :=
  ⟨genLExpr_complete ctx.toFVarCtx octx [] tvars [] n .bool
    genLMonoTy_mem_bool 3 e (Or.inl ⟨hwt, hnames, hvars, hats, hdepth⟩), hgen⟩

/-- **`ExprOk` holds of one concrete statement**, at each size and in the empty scope. That statement is
    `assert [l]: true;`. This witness is what gives `spec_complete` real content, and
    `Gaps.hExprC_unsatisfiable` proves that a hypothesis over each environment has no such witness. -/
theorem exprOk_assert_true (n : Nat) :
    ExprOk (octx := octx) (tvars := tvars) []  n
      (.cmd (CmdExt.cmd (.assert "l" (LExpr.const () (LConst.boolConst true)) default))) := by
  simp only [ExprOk]
  exact exprOk_assert_of_syntactic [] n "l" _ default
    ((HasTypeA_iff_typeCheck (T := LExprParams') []
      (LExpr.const () (LConst.boolConst true)) LMonoTy.bool).mpr rfl)
    (by simp [emptyNames]) (by simp [allVarsInCtx]) AllTypesSimple.boolConst
    (by simp [termDepth]) rfl

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
  | .typeDecl tc _ => tc.params.length

/-- The size witness for a chain: bounds both the list length and each element. -/
def stmtListDepth : List Statement → Nat
  | [] => 0
  | s :: ss => max (max (stmtDepth s) (stmtListDepth ss)) ((s :: ss).length)
end

-- ── Command-statement completeness ──────────────────────────────────────────

/-- **Completeness for a single `.cmd (CmdExt.cmd c)` statement.** A weakly typed command in
    generator shape (`InGenShape`), whose names and types the generator reaches (`AlphabetOk`) and
    whose expressions it reaches (`CmdExprOk`), is produced by `genStmt … n`, with an output scope
    equivalent to the output scopes of the typing. -/
theorem genCmdStmt_complete_spec (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (ts ts' : TypeScopes)
    (c : Cmd Expression)
    (hΓ : Strata.Util.HMaps.Equiv ts (procToTCtx ctx).types)
    (hwt : CmdHasTypeW C ts c ts')
    (hshape : InGenShape (.cmd (CmdExt.cmd c)))
    (hok : AlphabetOk tvars n (.cmd (CmdExt.cmd c)))
    (hExprC : CmdExprOk (octx := octx) (tvars := tvars) ctx n c) :
    ∃ ctx', Strata.Util.HMaps.Equiv ts' (procToTCtx ctx').types ∧
      ctx' = stepCtx ctx (.cmd (CmdExt.cmd c)) ∧
      (⟨[Stmt.cmd (CmdExt.cmd c)], C, ctx'⟩ : GenStmtResult) ∈
        SetGen.support (genStmt (G := SetGen.Set) octx tvars [] procs labels C ctx [] n) := by
  -- Reduce the goal to membership in `genCmd`'s support via the `genCmdStmt` wrapper
  -- and the `genCmdStmt_mem` lifting into `genStmt`.
  have hlift : ∀ (r : GenCmdResult),
      r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars [] ctx n []) →
      (⟨[Stmt.cmd (CmdExt.cmd r.cmd)], C, r.outCtx⟩ : GenStmtResult) ∈
        SetGen.support (genStmt (G := SetGen.Set) octx tvars [] procs labels C ctx [] n) := by
    intro r hr
    refine genCmdStmt_mem procs C ctx n _ ?_
    simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨r, hr, rfl⟩
  have hctxFind : ∀ x mty, ts.find? x = some (.forAll [] mty) → Map.find? ctx x = some mty :=
    fun x mty hfind => procToTCtx_find_rev ctx x mty ((hΓ.find? x).symm.trans hfind)
  have hctxFresh : ∀ x, ts.find? x = none → Map.find? ctx x = none :=
    fun x hfresh => procToTCtx_fresh_rev ctx x ((hΓ.find? x).symm.trans hfresh)
  have hinsertEquiv : ∀ x mty, Strata.Util.HMaps.Equiv (ts.insert x (.forAll [] mty))
      (procToTCtx (ctx.insert x mty)).types :=
    fun x mty => (Strata.Util.HMaps.insert_equiv hΓ _ _).trans (procToTCtx_insert ctx x mty).1.symm
  -- A declared variable of the typing is a writable variable of `ctx`.
  have hwritable : ∀ x mty, ts.find? x = some (.forAll [] mty) →
      List.Mem (x, mty) (ctx.writable []) := by
    intro x mty hfind
    rw [writable_nil_eq]
    exact Map.find?_mem ctx x mty (hctxFind x mty hfind)
  cases hwt with
  | init_det x xty e mty md _ hfresh hnovar hxty hwk hexpr hequiv =>
    subst hxty
    have hmdc : md = default := hshape
    subst hmdc
    obtain ⟨hname, hmtyReach⟩ := hok
    have hE := hExprC
    simp only [CmdExprOk] at hE
    obtain ⟨hreach, hgen⟩ := hE
    obtain ⟨nm, u⟩ := x; cases u
    have hfresh' : Map.find? ctx ⟨nm, ()⟩ = none := hctxFresh ⟨nm, ()⟩ hfresh
    refine ⟨ctx.insert ⟨nm, ()⟩ mty, hequiv.trans (hinsertEquiv ⟨nm, ()⟩ mty), rfl, ?_⟩
    exact hlift ⟨.init ⟨nm,()⟩ (.forAll [] mty) (.det e) default, ctx.insert ⟨nm,()⟩ mty⟩ (by
      rw [genCmd_support_iff octx tvars [] ctx n _ [] []]; refine Or.inl ?_
      simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨nm, freshName_reach ctx ⟨nm,()⟩ hname hfresh' List.not_mem_nil,
        mty, hmtyReach, e, hreach, by rw [if_pos hgen]⟩)
  | init_nondet x xty mty md _ hfresh hxty hwk hequiv =>
    subst hxty
    have hmdc : md = default := hshape
    subst hmdc
    obtain ⟨hname, hmtyReach⟩ := hok
    obtain ⟨nm, u⟩ := x; cases u
    have hfresh' : Map.find? ctx ⟨nm, ()⟩ = none := hctxFresh ⟨nm, ()⟩ hfresh
    refine ⟨ctx.insert ⟨nm, ()⟩ mty, hequiv.trans (hinsertEquiv ⟨nm, ()⟩ mty), rfl, ?_⟩
    exact hlift ⟨.init ⟨nm,()⟩ (.forAll [] mty) .nondet default, ctx.insert ⟨nm,()⟩ mty⟩ (by
      rw [genCmd_support_iff octx tvars [] ctx n _ [] []]; refine Or.inr (Or.inl ?_)
      simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨nm, freshName_reach ctx ⟨nm,()⟩ hname hfresh' List.not_mem_nil, mty, hmtyReach, rfl⟩)
  | set_det x mty e md _ hfind hexpr hequiv =>
    have hmdc : md = default := hshape
    subst hmdc
    have hE := hExprC
    simp only [CmdExprOk] at hE
    have hmem := hwritable x mty hfind
    refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
    refine hlift ⟨.set x (.det e) default, ctx⟩ ?_
    rw [genCmd_support_iff octx tvars [] ctx n _ [] []]
    refine Or.inr (Or.inr (Or.inl ⟨List.length_pos_of_mem hmem, ?_⟩))
    simp only [genSetDet, mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff]
    exact ⟨(x, mty), hmem, e, hE.1 mty (hctxFind x mty hfind), by rw [if_pos hE.2]⟩
  | set_nondet x mty md _ hfind hequiv =>
    have hmdc : md = default := hshape
    subst hmdc
    have hmem := hwritable x mty hfind
    refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
    refine hlift ⟨.set x .nondet default, ctx⟩ ?_
    rw [genCmd_support_iff octx tvars [] ctx n _ [] []]
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨List.length_pos_of_mem hmem, ?_⟩)))
    simp only [genSetNondet, mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff]
    exact ⟨(x, mty), hmem, rfl⟩
  | assert l e md _ hexpr hequiv =>
    have hmdc : md = default := hshape
    subst hmdc
    have hlreach : l ∈ SetGen.support (genIdentName (G := SetGen.Set)) := hok
    have hE := hExprC
    simp only [CmdExprOk] at hE
    refine ⟨ctx, hequiv.trans hΓ, rfl, hlift ⟨.assert l e default, ctx⟩ ?_⟩
    rw [genCmd_support_iff octx tvars [] ctx n _ [] []]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨l, hlreach, e, hE.1, by rw [generableOrTrue_of_generable hE.2]⟩
  | assume l e md _ hexpr hequiv =>
    have hmdc : md = default := hshape
    subst hmdc
    have hlreach : l ∈ SetGen.support (genIdentName (G := SetGen.Set)) := hok
    have hE := hExprC
    simp only [CmdExprOk] at hE
    refine ⟨ctx, hequiv.trans hΓ, rfl, hlift ⟨.assume l e default, ctx⟩ ?_⟩
    rw [genCmd_support_iff octx tvars [] ctx n _ [] []]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨l, hlreach, e, hE.1, by rw [generableOrTrue_of_generable hE.2]⟩
  | cover l e md _ hexpr hequiv =>
    have hmdc : md = default := hshape
    subst hmdc
    have hlreach : l ∈ SetGen.support (genIdentName (G := SetGen.Set)) := hok
    have hE := hExprC
    simp only [CmdExprOk] at hE
    refine ⟨ctx, hequiv.trans hΓ, rfl, hlift ⟨.cover l e default, ctx⟩ ?_⟩
    rw [genCmd_support_iff octx tvars [] ctx n _ [] []]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨l, hlreach, e, hE.1, by rw [generableOrTrue_of_generable hE.2]⟩

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
    Every weakly typed statement in generator shape (`InGenShape`), satisfying the
    alphabet kernel (`AlphabetOk` at some size `n`), the call recipe (`CallOk`) and expression
    reachability (`ExprOk`), is in `genStmt`'s support at the exact statement, with an output
    scope (through `procToTCtx`) equivalent to the output scopes of the typing. `immutableVars`
    is fixed to `[]`. -/
theorem spec_complete (P : Program) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ts : TypeScopes) (labels : List String)
    (s : Statement) (C' : LContext CoreLParams) (ts' : TypeScopes)
    (h : StatementHasTypeW P C ts labels s C' ts') :
    ∀ (ctx : VarCtx) (n : Nat),
      Strata.Util.HMaps.Equiv ts (procToTCtx ctx).types →
      InGenShape s → AlphabetOk tvars n s → CallOk (octx := octx) (tvars := tvars) procs ctx n s →
      ExprOk (octx := octx) (tvars := tvars) ctx n s →
      ∃ ctx', Strata.Util.HMaps.Equiv ts' (procToTCtx ctx').types ∧
        ctx' = stepCtx ctx s ∧
        (⟨[s], C', ctx'⟩ : GenStmtResult) ∈
          SetGen.support (genStmt (G := SetGen.Set) octx tvars [] procs labels C ctx [] n) := by
  induction h using StatementHasTypeW.rec (motive_2 := fun C ts L ss C' ts' _ =>
    ∀ (ctx : VarCtx) (n : Nat),
      Strata.Util.HMaps.Equiv ts (procToTCtx ctx).types →
      InGenShapeList ss → AlphabetOkList tvars n ss →
      CallOkList (octx := octx) (tvars := tvars) procs ctx n ss →
      ExprOkList (octx := octx) (tvars := tvars) ctx n ss →
      ∃ ctx', Strata.Util.HMaps.Equiv ts' (procToTCtx ctx').types ∧
        ctx' = stepCtxList ctx ss ∧
        ((ss, C', ctx') : List Statement × LContext CoreLParams × VarCtx) ∈
          SetGen.support
            (genStmtChain (G := SetGen.Set) octx tvars [] procs L C ctx [] n ss.length)) with
  | cmd C ts tsc L c ts' hc hequiv =>
    intro ctx n hΓ hnf hok hcall hexpr
    cases hc with
    | cmd c2 _ hcmd =>
      obtain ⟨ctx', hctx', hstep, hmem⟩ :=
        genCmdStmt_complete_spec procs L C ctx n ts tsc c2 hΓ hcmd hnf hok
          (by simpa [ExprOk] using hexpr)
      exact ⟨ctx', hequiv.trans hctx', hstep, hmem⟩
    | call pname callArgs proc md σ _ hfind hwf hlhs hin hout hequiv2 =>
      -- Shape gives `md = default`; `CallOk` gives membership + recipe + guard + empty chain.
      have hmdc : md = default := hnf
      subst hmdc
      obtain ⟨s, σvals, exprs, mask, hsmem, hpname, hσvals, hargs, hgen, hMusable, hNodup,
        hForall, hEmpty⟩ := hcall
      refine ⟨ctx, (hequiv.trans hequiv2).trans hΓ, rfl, ?_⟩
      -- The emitted group is `initChain (…) ++ [call]`; the chain is empty (`hEmpty`),
      -- and the output scope `insertAllCtx ctx [] = ctx`.
      refine genCallStmt_mem procs C ctx n _ ?_
      have hEmpty' := List.append_eq_nil_iff.mp hEmpty
      -- No out target has to be declared, so the generator's names to avoid change no target.
      have hT := outTargets_eq_of_reused [] ctx
        (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O) (functionNames C) hEmpty'.2
      have hMnotFn : ((StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).filter
          (needsInit ctx)).all (fun q => !(functionNames C).contains q.1.name) = true := by
        rw [hEmpty'.1]; rfl
      have hmem := genCallStmt_mem_complete (octx := octx) (tvars := tvars)
        (immutableVars := []) procs C ctx n s hsmem σvals hσvals exprs mask hMusable
        (by rw [hT]; exact hNodup) hMnotFn hForall hgen
      rw [hT, hEmpty] at hmem
      simpa [hargs, StrataGenerators.Stmt.initChain, StrataGenerators.Stmt.insertAllCtx, hpname]
        using hmem
  | exit C ts L label md ts' hmem hequiv =>
    intro ctx n hΓ hnf hok hcall hexpr
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
  | typeDecl C C' Γ L tc md Δ _ hoktc hequiv =>
    intro ctx n hΓ hnf hok hcall hexpr
    have hmdc : md = default := hnf
    subst hmdc
    obtain ⟨hlocal, hname_tc, hlen, hparams⟩ := hok
    refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
    refine genTypeDeclStmt_mem procs C ctx n _ ?_
    simp only [genTypeDeclStmt, mem_support_bind_iff]
    refine ⟨tc, genTypeConstructor_complete n tc hlocal hname_tc hlen hparams, ?_⟩
    rw [hoktc]; simp only [mem_support_pure_iff]
  | block C ts Cb tsb L label body md ts' hlabel hbody hequiv ihbody =>
    intro ctx n hΓ hnf hok hcall hexpr
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨hlabelname, hlen, hokbody⟩ := hok
      obtain ⟨hmdc, hnfbody⟩ := hnf
      subst hmdc
      obtain ⟨ctxb, hctxb, _, hbodymem⟩ := ihbody ctx m hΓ hnfbody hokbody hcall hexpr
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact block_mem procs C ctx m label body Cb ctxb body.length hlen hbodymem
        (genFreshLabel_complete L label hlabelname hlabel)
  | ite_det C ts Ct tst Ce tse L cond thenb elseb md ts' hcond hthen helse hequiv iht ihe =>
    intro ctx n hΓ hnf hok hcall hexpr
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨htlen, helen, hokt, hoke⟩ := hok
      obtain ⟨hmdc, hnft, hnfe⟩ := hnf
      subst hmdc
      obtain ⟨hcallt, hcalle⟩ := hcall
      obtain ⟨ctxt, hctxt, _, htmem⟩ := iht ctx m hΓ hnft hokt hcallt hexpr.2.1
      obtain ⟨ctxe, hctxe, _, hemem⟩ := ihe ctx m hΓ hnfe hoke hcalle hexpr.2.2
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact ite_det_mem procs C ctx m cond thenb elseb Ct ctxt Ce ctxe thenb.length elseb.length
        htlen helen (hexpr.1 cond rfl).1 (hexpr.1 cond rfl).2 htmem hemem
  | ite_nondet C ts Ct tst Ce tse L thenb elseb md ts' hthen helse hequiv iht ihe =>
    intro ctx n hΓ hnf hok hcall hexpr
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨htlen, helen, hokt, hoke⟩ := hok
      obtain ⟨hmdc, hnft, hnfe⟩ := hnf
      subst hmdc
      obtain ⟨hcallt, hcalle⟩ := hcall
      obtain ⟨ctxt, hctxt, _, htmem⟩ := iht ctx m hΓ hnft hokt hcallt hexpr.2.1
      obtain ⟨ctxe, hctxe, _, hemem⟩ := ihe ctx m hΓ hnfe hoke hcalle hexpr.2.2
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact ite_nondet_mem procs C ctx m thenb elseb Ct ctxt Ce ctxe thenb.length elseb.length
        htlen helen htmem hemem
  | loop C ts Cb tsb L guard measure invs body md ts' hg hm hi hbody hequiv ihbody =>
    intro ctx n hΓ hnf hok hcall hexpr
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ mm =>
      obtain ⟨hinvlen, hinvname, hblen, hokbody⟩ := hok
      obtain ⟨hmdc, hnfbody⟩ := hnf
      subst hmdc
      obtain ⟨ctxb, hctxb, _, hbodymem⟩ :=
        ihbody ctx mm hΓ hnfbody hokbody hcall hexpr.2.2.2
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      refine loop_mem procs C ctx mm guard measure invs body Cb ctxb body.length hblen
        ?_ ?_ ?_ hbodymem
      · exact genCondOrNondet_complete (mm+1) ctx guard (fun g hg => (hexpr.1 g hg).1)
          (fun g hg => (hexpr.1 g hg).2)
      · exact genOptMeasure_complete (mm+1) ctx measure (fun m hm => (hexpr.2.1 m hm).1)
          (fun m hm => (hexpr.2.1 m hm).2)
      · exact genInvariants_complete (mm+1) ctx invs hinvlen
          (fun p hp => ⟨hinvname p hp, (hexpr.2.2.1 p hp).1⟩) (fun p hp => (hexpr.2.2.1 p hp).2)
  | nil C ts L ts' hequiv =>
    rename_i ctx n hΓ _ _ _ _
    exact ⟨ctx, hequiv.trans hΓ, rfl, genStmtChain_nil_mem procs C ctx n⟩
  | cons C C1 C2 ts ts1 ts2 L s ss hs hss ihs ihss =>
    rename_i ctx n hΓ hnf hok hcall hexpr
    obtain ⟨hnfs, hnfss⟩ := hnf
    obtain ⟨hoks, hokss⟩ := hok
    obtain ⟨hcalls, hcallss⟩ := hcall
    -- The head produces `[s]` at scope `ctx1 = stepCtx ctx s` (pinned by `ihs`); the
    -- tail continues from there, so its threaded `CallOkList`/scope line up exactly.
    obtain ⟨ctx1, hctx1, hstep1, hsmem⟩ := ihs ctx n hΓ hnfs hoks hcalls hexpr.1
    subst hstep1
    obtain ⟨ctx2, hctx2, hstep2, hssmem⟩ :=
      ihss (stepCtx ctx s) n hctx1 hnfss hokss hcallss hexpr.2
    refine ⟨ctx2, hctx2, ?_, ?_⟩
    · show ctx2 = stepCtxList ctx (s :: ss); rw [hstep2]; rfl
    · have hcons := genStmtChain_cons_mem procs C ctx n ss.length ⟨[s], C1, stepCtx ctx s⟩ ss C2
        ctx2 hsmem hssmem
      simpa using hcons

end StrataGenerators.Stmt.SpecComplete
