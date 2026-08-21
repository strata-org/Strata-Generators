import StrataGenerators.ProcedureHasTypeAGen.Support

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen ArbString
open StrataGenerators.Stmt StrataGenerators.Procedure StrataGenerators.Function

/-!
# The completeness of `genStmt` and `genStmtChain`, indexed by `StatementHasTypeA`

`spec_complete` proves that each well-typed statement is in the support of `genStmt`. The declarative
relation `StatementHasTypeA`, in `Strata.Languages.Core.StatementTypeSpec`, decides which statements are
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
  type of an `init` is in the support of `genLMonoTy`, and the declaration of a `funcDecl` is in the support
  of `genDecl`.
* **`CallOk`** holds the shape of a call. A `.cmd (.call …)` statement is reachable only when its argument
  list is the recipe of the generator, which is `mkArgs` over `outTargets`, for some callee, at some
  sampled instantiation of the type parameters and some mask for the order of the arguments. The predicate
  is `True` at each node that is not a call, and it recurses into each nested body.
* **`ExprOk`** holds the reachability of each expression, through the scope and the size at each node. Each
  expression of the statement is in the support of `genLExpr`, at the size of *its own* level of the
  nesting, and in the scope that is available *there*.

## No proof can remove the predicates

`StmtHasTypeAGenCompleteGaps.lean` proves that each predicate is necessary. For each of them, it gives a
statement that `StatementHasTypeA` accepts and that the support of `genStmt` does not hold. Those theorems
are `metadata_gap`, `label_gap` and `outTarget_gap`.

One of the gaps has a counterexample that a person can write in Core:

* `outTargets` picks the receiving variable of each `out` parameter itself, and the specification accepts
  each writable variable of the correct type. Read `outTarget_gap`. `genStmt` also emits the default
  metadata, and the grammar of Core has a prefix for an annotation on each statement. Read `metadata_gap`.

Each other gap needs a witness that lives in the abstract syntax tree alone. `genAssertCmd`,
`genAssumeCmd`, `genCoverCmd` and `genFreshName` each draw from `genIdentName`, so each name of a parsed
program is reachable. `mkArgs` takes a mask for an interleaving, so the order of an `inArg` and an `outArg`
is free, and a call such as `call p(out y, 1);` is reachable.

Three predicates of Strata come close to a condition here, and none of them discharges one:

* `Imperative.Stmt.stripMetaData` erases the metadata of a `block`, an `ite`, a `loop`, an `exit`, a
  `funcDecl` and a `typeDecl`. It leaves a `.cmd` node unchanged, and the gap about the metadata is at a
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

A hypothesis about the reachability of a function fails for the same kind of reason, and no side condition
on the *statement* can repair it. The rule `StatementHasType'.funcDecl` of Strata adds an **arbitrary**
well-typed function to the context, and that function has no relation to the declaration of the statement.
Therefore the statement does not determine the function whose reachability a proof needs. The two sides
also disagree: `genFunction_complete` needs the name to be in the support of `genIdentName`, at most one
precondition, no recursion, no attribute and no axiom, and `FuncHasType'`, which is a structure of six
fields, constrains none of them. Therefore the `.funcDecl` clause of `ExprOk` is `False`, and **this
theorem covers each statement except a local `funcDecl`**. That is a real restriction, and the
specification must tie the function of the rule to the declaration of the statement to remove it.
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

/-- A fresh `genIdentName` name is in `genFreshName`'s support. `genFreshName`
    draws from `genIdentName`, whose support holds no keyword, so this needs no
    separate `dodgeKeyword` premise. -/
theorem freshName_reach (ctx : VarCtx) (x : Identifier Unit)
    (hname : x.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hfresh : Map.find? ctx x = none) :
    x.name ∈ SetGen.support (genFreshName (G := SetGen.Set) ctx) := by
  simp only [genFreshName, mem_support_bind_iff]
  refine ⟨x.name, hname, ?_⟩
  simp only [mem_support_ite_iff, mem_support_pure_iff]
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
    `genLMonoTy_mem_ftvars` gives `allFtvarsIn tvars mty`, and `allFtvarsIn_freeVars`
    turns that into a `freeVars ⊆ tvars` statement. -/
theorem freeVars_subset_of_reachable {mty : LMonoTy} {tvars : List TyIdentifier} {n : Nat}
    (h : mty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars n)) :
    ∀ v ∈ mty.freeVars, v ∈ tvars :=
  allFtvarsIn_freeVars (genLMonoTy_mem_ftvars h)

/-- **The pin from a rigid variable, for the `init` case.** When each free variable of the monomorphic
    annotation is rigid, `RigidAnnotCompat` forces the stored type to equal the annotation, and it needs no
    ground type. The witnessing substitution is the identity on a rigid variable, so it fixes the annotation,
    because each free variable of the annotation is rigid. The remaining condition about the equivalence of the
    two types then becomes the equality of the two types. -/
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
-- Each predicate below is a recursive function that gives a `Prop`, and none of them is an inductive
-- relation. Two facts about a shape belong here: the metadata is the default value, and the annotation of an
-- `init` is monomorphic. The generator reaches each other shape. It draws a label from `genIdentName`, it
-- draws both boundedness values for a `typeDecl`, and a rigid context pins the stored type of an `init`. A
-- procedure `call` is admissible here (its further conditions about the recipe and the instantiation
-- conditions live in `CallOk`).
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
    `genIdentName`'s support already excludes every keyword. -/
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
    the *instantiated* input type of the callee, and the absence of a necessary fresh `init` statement (a
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

-- ── Residual expression-reachability side condition (`ExprOk`) ──────────────

/-- The expressions of one command, reachable by `genLExpr` at size `n` in the scope
    `ctx`. This is the per-command half of `ExprOk`.

    `set`'s clause is stated against the type the scope gives its target, because
    that is the type the generator draws the right-hand side at. -/
def CmdExprOk (ctx : VarCtx) (n : Nat) : Cmd Expression → Prop
  | .init _ (.forAll [] mty) (.det e) _ =>
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n mty)
  | .init _ _ _ _ => True
  | .set x (.det e) _ =>
      ∀ mty, Map.find? ctx x = some mty →
        e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n mty)
  | .set _ _ _ => True
  | .assert _ e _ =>
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool)
  | .assume _ e _ =>
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool)
  | .cover _ e _ =>
      e ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool)

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
        g ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool)) ∧
      ExprOkList ctx (n - 1) t ∧ ExprOkList ctx (n - 1) e
  | .loop guard measure invs body _ =>
      (∀ g, guard = .det g →
        g ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool)) ∧
      (∀ m, measure = some m →
        m ∈ SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .int)) ∧
      (∀ p ∈ invs, p.2 ∈
        SetGen.support (genLExpr (G := SetGen.Set) ctx.toFVarCtx octx [] tvars [] n .bool)) ∧
      ExprOkList ctx (n - 1) body
  | .exit _ _ => True
  -- **A local `funcDecl` is out of scope, and that is forced.** The old
  -- `hFuncReach : ∀ d C Γ func, FuncHasTypeA C Γ func → func ∈ support (genFunction … d)`
  -- was unsatisfiable, for a reason no side condition on the *statement* can repair:
  -- upstream's `StatementHasType'.funcDecl` adds an **arbitrary** well-typed `func` to
  -- the context, unrelated to the `decl` the statement declares, so the statement does
  -- not even determine the function whose reachability is needed. The two sides also
  -- disagree outright: `genFunction_complete` requires the name to be in
  -- `genIdentName`'s support, `preconditions.length ≤ 1`, `isRecursive = false`,
  -- no attribute and no axiom, and `FuncHasType'`, which is a structure of six fields, constrains none of
  -- them. To remove this restriction, the *specification* must tie the function of the rule to the declaration
  -- of the statement.
  | .funcDecl _ _ => False
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
    (hdepth : termDepth [] e ≤ n) :
    CmdExprOk (octx := octx) (tvars := tvars) ctx n (.assert l e md) :=
  genLExpr_complete ctx.toFVarCtx octx [] tvars [] n .bool
    genLMonoTy_mem_bool 3 e (Or.inl ⟨hwt, hnames, hvars, hats, hdepth⟩)

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
    (by simp [termDepth])

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
    (hExprC : CmdExprOk (octx := octx) (tvars := tvars) ctx n c) :
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
    obtain ⟨hname, hmtyReach⟩ := hok
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
      exact ⟨nm, freshName_reach ctx ⟨nm,()⟩ hname (procToTCtx_fresh_rev ctx ⟨nm,()⟩ hfresh),
        mty, hmtyReach, e, (by simpa [CmdExprOk] using hExprC), rfl⟩)
  | init_nondet x xty mty tys md Δ hfresh hlen hcompat hwk hequiv =>
    obtain ⟨mtyA, rfl, hmdc⟩ : ∃ m, xty = .forAll [] m ∧ md = default := by
      cases xty with
      | forAll bs body =>
        cases bs with
        | nil => exact ⟨body, rfl, hshape⟩
        | cons _ _ => exact absurd hshape (by simp [InGenShape])
    obtain ⟨hname, hmtyReach⟩ := hok
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
      exact ⟨nm, freshName_reach ctx ⟨nm,()⟩ hname (procToTCtx_fresh_rev ctx ⟨nm,()⟩ hfresh),
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
      refine ⟨(x, mty), ?_, e,
        (by simpa [CmdExprOk] using hExprC mty (procToTCtx_find_rev ctx x mty hfind)), rfl⟩
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
    have hlreach : l ∈ SetGen.support (genIdentName (G := SetGen.Set)) := hok
    refine ⟨ctx, hequiv.symm, rfl, ?_⟩
    have := hlift ⟨.assert l e default, ctx⟩ ?_
    · subst hmdc; exact this
    · rw [genCmd_support_iff]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨l, hlreach, e, (by simpa [CmdExprOk] using hExprC), rfl⟩
  | assume l e md Δ hexpr hequiv =>
    have hmdc : md = default := hshape
    have hlreach : l ∈ SetGen.support (genIdentName (G := SetGen.Set)) := hok
    refine ⟨ctx, hequiv.symm, rfl, ?_⟩
    have := hlift ⟨.assume l e default, ctx⟩ ?_
    · subst hmdc; exact this
    · rw [genCmd_support_iff]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
      simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨l, hlreach, e, (by simpa [CmdExprOk] using hExprC), rfl⟩
  | cover l e md Δ hexpr hequiv =>
    have hmdc : md = default := hshape
    have hlreach : l ∈ SetGen.support (genIdentName (G := SetGen.Set)) := hok
    refine ⟨ctx, hequiv.symm, rfl, ?_⟩
    have := hlift ⟨.cover l e default, ctx⟩ ?_
    · subst hmdc; exact this
    · rw [genCmd_support_iff]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
      simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨l, hlreach, e, (by simpa [CmdExprOk] using hExprC), rfl⟩

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
    :
    ∀ (ctx : VarCtx) (n : Nat), C.rigidTypeVars = tvars →
      TContext.Equiv (T := CoreLParams) Γ (procToTCtx ctx) →
      InGenShape s → AlphabetOk (octx := octx) tvars n s → CallOk (octx := octx) (tvars := tvars) procs ctx n s →
      ExprOk (octx := octx) (tvars := tvars) ctx n s →
      ∃ ctx', TContext.Equiv (T := CoreLParams) Γ' (procToTCtx ctx') ∧
        ctx' = stepCtx ctx s ∧
        (⟨[s], C', ctx'⟩ : GenStmtResult) ∈
          SetGen.support (genStmt (G := SetGen.Set) octx tvars [] procs labels C ctx [] n) := by
  induction h using StatementHasType'.rec (motive_2 := fun C Γ L ss C' Γ' _ =>
    ∀ (ctx : VarCtx) (n : Nat), C.rigidTypeVars = tvars →
      TContext.Equiv (T := CoreLParams) Γ (procToTCtx ctx) →
      InGenShapeList ss → AlphabetOkList (octx := octx) tvars n ss → CallOkList (octx := octx) (tvars := tvars) procs ctx n ss →
      ExprOkList (octx := octx) (tvars := tvars) ctx n ss →
      ∃ ctx', TContext.Equiv (T := CoreLParams) Γ' (procToTCtx ctx') ∧
        ctx' = stepCtxList ctx ss ∧
        ((ss, C', ctx') : List Statement × LContext CoreLParams × VarCtx) ∈
          SetGen.support (genStmtChain (G := SetGen.Set) octx tvars [] procs L C ctx [] n ss.length)) with
  | cmd C Γ Γ2 L c Δ hc hequiv =>
    intro ctx n hRig hΓ hnf hok hcall hexpr
    cases cmdExtHasTypeA_equiv_congr hc hΓ.symm with
    | cmd Γ3 c2 hcmd =>
      obtain ⟨ctx', hctx', hstep, hmem⟩ :=
        genCmdStmt_complete_spec procs L C ctx n _ c2 hRig hcmd hnf hok
          (by simpa [ExprOk] using hexpr)
      exact ⟨ctx', hequiv.trans hctx'.symm, hstep, hmem⟩
    | call pname callArgs proc md σ Δ2 hfind hInLen hOutLen hLhs hIn hOut hInout hequiv2 =>
      -- Shape gives `md = default`; `CallOk` gives membership + recipe + guard + empty chain.
      have hmdc : md = default := hnf
      subst hmdc
      obtain ⟨s, σvals, exprs, mask, hsmem, hpname, hσvals, hargs, hMusable, hNodup,
        hForall, hEmpty⟩ := hcall
      refine ⟨ctx, hequiv.trans hequiv2, rfl, ?_⟩
      -- The emitted group is `initChain (…) ++ [call]`; the chain is empty (`hEmpty`),
      -- and the output scope `insertAllCtx ctx [] = ctx`.
      refine genCallStmt_mem procs C ctx n _ ?_
      have hmem := genCallStmt_mem_complete (octx := octx) (tvars := tvars)
        (immutableVars := []) procs C ctx n s hsmem σvals hσvals exprs mask hMusable hNodup
        hForall
      rw [hEmpty] at hmem
      simpa [hargs, StrataGenerators.Stmt.initChain, StrataGenerators.Stmt.insertAllCtx, hpname] using hmem
  | exit C Γ L label md Δ hmem hequiv =>
    intro ctx n hRig hΓ hnf hok hcall hexpr
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
    intro ctx n hRig hΓ hnf hok hcall hexpr
    have hmdc : md = default := hnf
    subst hmdc
    -- Out of scope: see the `.funcDecl` clause of `ExprOk` for why no side condition
    -- on the statement can make this case work.
    exact absurd hexpr (by simp [ExprOk])
  | typeDecl C C' Γ L tc md Δ hoktc hequiv =>
    intro ctx n hRig hΓ hnf hok hcall hexpr
    have hmdc : md = default := hnf
    subst hmdc
    obtain ⟨hname_tc, hlen, hparams⟩ := hok
    refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
    refine genTypeDeclStmt_mem procs C ctx n _ ?_
    simp only [genTypeDeclStmt, mem_support_bind_iff]
    refine ⟨tc, genTypeConstructor_complete n tc hname_tc hlen hparams, ?_⟩
    rw [hoktc]; simp only [mem_support_pure_iff]
  | block C Γ Cb Γb L label body md Δ hlabel hbody hequiv ihbody =>
    intro ctx n hRig hΓ hnf hok hcall hexpr
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨hlabelname, hlen, hokbody⟩ := hok
      obtain ⟨hmdc, hnfbody⟩ := hnf
      subst hmdc
      obtain ⟨ctxb, hctxb, _, hbodymem⟩ := ihbody ctx m hRig hΓ hnfbody hokbody hcall hexpr
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact block_mem procs C ctx m label body Cb ctxb body.length hlen hbodymem
        (genFreshLabel_complete L label hlabelname hlabel)
  | ite_det C Γ Ct Γt Ce Γe L cond thenb elseb md Δ hcond hthen helse hequiv iht ihe =>
    intro ctx n hRig hΓ hnf hok hcall hexpr
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨htlen, helen, hokt, hoke⟩ := hok
      obtain ⟨hmdc, hnft, hnfe⟩ := hnf
      subst hmdc
      obtain ⟨hcallt, hcalle⟩ := hcall
      obtain ⟨ctxt, hctxt, _, htmem⟩ := iht ctx m hRig hΓ hnft hokt hcallt hexpr.2.1
      obtain ⟨ctxe, hctxe, _, hemem⟩ := ihe ctx m hRig hΓ hnfe hoke hcalle hexpr.2.2
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact ite_det_mem procs C ctx m cond thenb elseb Ct ctxt Ce ctxe thenb.length elseb.length
        htlen helen (hexpr.1 cond rfl) htmem hemem
  | ite_nondet C Γ Ct Γt Ce Γe L thenb elseb md Δ hthen helse hequiv iht ihe =>
    intro ctx n hRig hΓ hnf hok hcall hexpr
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ m =>
      obtain ⟨htlen, helen, hokt, hoke⟩ := hok
      obtain ⟨hmdc, hnft, hnfe⟩ := hnf
      subst hmdc
      obtain ⟨hcallt, hcalle⟩ := hcall
      obtain ⟨ctxt, hctxt, _, htmem⟩ := iht ctx m hRig hΓ hnft hokt hcallt hexpr.2.1
      obtain ⟨ctxe, hctxe, _, hemem⟩ := ihe ctx m hRig hΓ hnfe hoke hcalle hexpr.2.2
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      exact ite_nondet_mem procs C ctx m thenb elseb Ct ctxt Ce ctxe thenb.length elseb.length
        htlen helen htmem hemem
  | loop C Γ Cb Γb L guard measure invs body md Δ hg hm hi hbody hequiv ihbody =>
    intro ctx n hRig hΓ hnf hok hcall hexpr
    cases n with
    | zero => exact absurd hok (by simp [AlphabetOk])
    | succ mm =>
      obtain ⟨hinvlen, hinvname, hblen, hokbody⟩ := hok
      obtain ⟨hmdc, hnfbody⟩ := hnf
      subst hmdc
      obtain ⟨ctxb, hctxb, _, hbodymem⟩ := ihbody ctx mm hRig hΓ hnfbody hokbody hcall hexpr.2.2.2
      refine ⟨ctx, hequiv.trans hΓ, rfl, ?_⟩
      refine loop_mem procs C ctx mm guard measure invs body Cb ctxb body.length hblen ?_ ?_ ?_ hbodymem
      · exact genCondOrNondet_complete (mm+1) ctx guard hexpr.1
      · exact genOptMeasure_complete (mm+1) ctx measure hexpr.2.1
      · exact genInvariants_complete (mm+1) ctx invs hinvlen
          (fun p hp => ⟨hinvname p hp, hexpr.2.2.1 p hp⟩)
  | nil C Γ L Δ hequiv =>
    rename_i ctx n hRig hΓ _ _ _ _
    exact ⟨ctx, hequiv.trans hΓ, rfl, genStmtChain_nil_mem procs C ctx n⟩
  | cons C C1 C2 Γ Γ1 Γ2 L s ss hs hss ihs ihss =>
    rename_i ctx n hRig hΓ hnf hok hcall hexpr
    obtain ⟨hnfs, hnfss⟩ := hnf
    obtain ⟨hoks, hokss⟩ := hok
    obtain ⟨hcalls, hcallss⟩ := hcall
    -- The head produces `[s]` at scope `ctx1 = stepCtx ctx s` (pinned by `ihs`); the
    -- tail continues from there, so its threaded `CallOkList`/scope line up exactly.
    obtain ⟨ctx1, hctx1, hstep1, hsmem⟩ := ihs ctx n hRig hΓ hnfs hoks hcalls hexpr.1
    subst hstep1
    -- `hRig` transfers to `C1`: statement typing preserves `rigidTypeVars`
    -- (`funcDecl`/`typeDecl` extend only the factory/known-types).
    have hRig1 : C1.rigidTypeVars = tvars := (stmtHasType_rigid_eq hs).trans hRig
    obtain ⟨ctx2, hctx2, hstep2, hssmem⟩ := ihss (stepCtx ctx s) n hRig1 hctx1 hnfss hokss hcallss hexpr.2
    refine ⟨ctx2, hctx2, ?_, ?_⟩
    · show ctx2 = stepCtxList ctx (s :: ss); rw [hstep2]; rfl
    · have := genStmtChain_cons_mem procs C ctx n ss.length ⟨[s], C1, stepCtx ctx s⟩ ss C2 ctx2 hsmem hssmem
      simpa using this

end StrataGenerators.Stmt.SpecComplete
