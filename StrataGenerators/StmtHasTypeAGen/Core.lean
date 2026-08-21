import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import Basalt.Tuning.Attr
import BasaltExamples.ArbString.Def
import Strata.Languages.Core.StatementTypeSpec
import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.StmtHasTypeAGen.GenCallStmtSound

open Lambda RandomChoice Core Imperative ArbString

/-!
# Core generator definitions for well-typed Strata Core `Statement`s

This file contains the canonical definition of `genStmt` / `genStmtChain`, mutually
recursive generators of well-typed Strata Core statements
(`Statement = Imperative.Stmt Core.Expression Core.Command`) satisfying the
`StatementHasTypeA` / `StatementsHasTypeA` relations of
`Strata.Languages.Core.StatementTypeSpec`.

## Reuse of existing generators

The statement generator delegates to the already-proven-sound-and-complete
component generators:

- `genCmd` (from `CmdHasTypeAGen/Core.lean`) for the `cmd` constructor. A
  generated `Cmd Expression` is wrapped as `CmdExt.cmd`, whose typing
  (`CmdExtHasType'.cmd`) delegates straight back to `CmdHasType'`.
- `genFunction` (from `FunctionHasTypeAGen/Core.lean`) for the well-typed
  function witness of the `funcDecl` constructor.
- `genLExpr` (from `HasTypeAGen/Core.lean`) for the `bool`/`int` expressions
  appearing in `ite`/`loop` guards, loop measures, and loop invariants.

## The three threaded contexts

`StatementHasType'` is a 6-place relation `C Γ L s C' Γ'` (the spec tracks the set
`L` of enclosing-block labels). The generator threads a
representation of all three:

- `Γ` (variable type-scope) is threaded via the flat `VarCtx` from
  `CmdHasTypeAGen/Core.lean`, exactly as `genCmd`/`genCmds` do.
- `C` (the ambient `LContext`) is threaded as an honest `LContext CoreLParams`.
- `L` (the enclosing-block labels) is threaded as a `List String`, extended by a
  fresh label whenever the generator descends into a `block` body.

The **annotated** spec `instHasTypeA` ignores both `C` and `Γ` when typing
expressions, so `C` never influences *which expression* is produced. The only
constructor whose well-typedness depends on the context is `typeDecl`, whose premise is
`C.addKnownTypeWithError … = .ok C'`. The generator handles that case: it generates a `TypeConstructor`, and it
then **matches** on the result of `addKnownTypeWithError`. Therefore the output context of the `.ok` branch is
definitionally the context that the premise needs. After a clash of two names, the generator gives the empty
generator, which is `default`, and its support at `SetGen.Set` is empty. A constructor whose name clashes
therefore gives nothing.

## Labels

Under the new spec `exit label` requires `label ∈ L` and `block label` requires
`label ∉ L` (no shadowing), with the body typed under `label :: L`. Accordingly:

- `genExitStmt` samples its target from the *enclosing* labels `L` (via
  `elements`), so the generated `exit` genuinely targets a live enclosing block.
  When the list of the labels is empty, so no block encloses the point, no valid `exit` exists. The generator
  then gives the empty generator, and the `exit` branch gives nothing there.
- The `block` generator draws its label from `genFreshLabel L`, guaranteeing
  `label ∉ L`, and generates the body under `label :: L`.

## Lexical scoping

`block`, and each branch of `ite`, and the body of `loop`, are lexically scoped:
their output context is the *input* `C, Γ`. Accordingly, the generator discards
the output context of a nested block/branch/body and returns the input `C, Γ`.
-/

namespace StrataGenerators.Stmt

open TypeSpec

-- ── Result of generating a statement ─────────────────────────────────────

/-- The result of the generation of **one statement**, as a statement *list*, together with the output context
    `C'` and the output scope of the variables, as a `VarCtx`.

    Almost every constructor yields a singleton `[s]`. The list is there for the
    one shape that genuinely spans several statements: a procedure `call` whose
    in-out/out arguments are not all in scope must be preceded by `init`s in the
    **ambient** scope (see `genCallStmt`), so its group is `init … ; init … ; call`
    and its output scope is strictly larger than its input. Rather than give calls
    a layer of their own, `genStmt` returns a list uniformly and `genStmtChain`
    splices whatever comes back. -/
structure GenStmtResult where
  /-- The generated statement, as a list. That list holds one statement, except for a group of a call. -/
  stmts : List Statement
  /-- The output ambient `LContext` after the statement. -/
  outC : LContext CoreLParams
  /-- The output variable type-scope after the statement. -/
  outCtx : VarCtx

-- ── Fresh label generation ───────────────────────────────────────────────

/-- A fallback label guaranteed to be absent from `labels`: a string of `x`
    characters strictly longer than any label in the list. Mirrors
    `fallbackFreshName` for variable contexts. -/
def fallbackFreshLabel (labels : List String) : String :=
  String.ofList (List.replicate (labels.foldl (fun acc l => max acc l.length) 0 + 1) 'x')

/-- Generate a fresh label for a block that is not in `labels`. The function draws from `genIdentName`, so the
    label is an identifier that is not empty and is not a keyword. A label of a `block` appears at the position
    of an identifier, so it must not be empty and must not be a reserved word. After a collision, the function
    falls back to a name whose length gives freshness. Therefore the result is never a member of `labels`, which
    is the premise of the `block` rule. This function follows `genFreshName`, which gives the name of a
    variable. -/
def genFreshLabel [Gen G] (labels : List String) : G String := do
  let s ← genIdentName
  if s ∈ labels then
    pure (fallbackFreshLabel labels)
  else
    pure s

-- ── TypeConstructor / declaration sub-generators ─────────────────────────

/-- `Boundedness` is `Inhabited` (default `.Infinite`), needed by `elements` and its
    support-inversion lemma `mem_support_elements_iff` when sampling `bound`. -/
instance : Inhabited Boundedness := ⟨.Infinite⟩

/-- Generate a random `TypeConstructor`: a name and a list of (up to `depth`)
    parameter names, all produced by `genIdentName` so each is a non-empty,
    non-keyword identifier (constructor and type-parameter names both appear in
    identifier position). The `bound` field is sampled over both `Boundedness`
    values: it is typing-irrelevant (the `typeDecl` rule's `addKnownTypeWithError`
    keys only off `name`/`numargs`), so either choice is well-typed. -/
def genTypeConstructor [Gen G] (depth : Nat) : G TypeConstructor := do
  let name ← genIdentName
  let params ← listOfMaxLength depth genIdentName
  let bound ← elements [Boundedness.Infinite, Boundedness.Finite] (by simp)
  pure { bound := bound, name := name, params := params }

/-- Lift a monomorphic `Function` to a non-recursive `PureFunc Expression` (the
    syntactic declaration node stored in a `funcDecl` statement). Each monotype
    field is wrapped as the trivial polytype `∀ []. mty`. The `isRecursive` flag
    is forced to `false` (the `funcDecl` typing rule requires a non-recursive
    declaration). -/
def Function.toPureFuncDecl (f : Function) : Imperative.PureFunc Expression :=
  { name := f.name,
    typeArgs := f.typeArgs,
    isConstr := f.isConstr,
    isRecursive := false,
    inputs := f.inputs.map (fun (id, mty) => (id, (.forAll [] mty : LTy))),
    output := (.forAll [] f.output : LTy),
    body := f.body,
    attr := f.attr,
    axioms := f.axioms,
    preconditions := f.preconditions,
    measure := f.measure }

/-- Generate a syntactic (non-recursive) function-declaration node by generating
    a well-typed `Function` via `genFunction` and lifting it to a `PureFunc`.

    In the declarative `funcDecl` rule, the syntactic declaration and the well-typed witness function that the
    rule adds to the context are *independent*. The rule asks only that the declaration is not recursive and
    that the function is well typed. Therefore the generator draws them independently. Read `genStmt`. This
    helper only
    supplies non-recursive `decl` nodes. -/
def genDecl [Gen G] (octx : OpCtx) (depth : Nat) (pctx : PolyOpCtx := []) :
    G (Imperative.PureFunc Expression) :=
  Function.toPureFuncDecl <$> genFunction [] octx depth pctx

-- ── Guard / measure / invariant sub-generators ───────────────────────────

/-- Generate an `ExprOrNondet` used as an `ite` condition or a `loop` guard:
    either `.nondet`, or `.det e` for a boolean expression `e`. Biased 80% toward a
    *deterministic* guard, at the weights 1 and 4. Therefore a generated `ite` and a generated `loop` more often
    carry a real boolean condition, and not a `*`. Both branches keep a positive weight, so the support does not
    change, and each statement of soundness and of completeness therefore does not change either. Read
    `genCondOrNondet_det_sound` and `genCondOrNondet_complete`. -/
def genCondOrNondet [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G (ExprOrNondet Expression) :=
  frequency
    [ (1, fun () => pure .nondet),
      (4, fun () => (fun e => ExprOrNondet.det e) <$> genLExpr ctx.toFVarCtx octx pctx tvars [] depth .bool) ]
    (by simp)

/-- Generate an optional loop measure: either `none`, or `some m` for an
    integer expression `m`. Biased to produce a measure 75% of the time (weights
    `1` for `none` versus `3` for `some`), so generated loops usually carry a
    measure. -/
def genOptMeasure [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G (Option Expression.Expr) :=
  biasedOptionGen (3 / 4) (genLExpr ctx.toFVarCtx octx pctx tvars [] depth .int)

/-- Generate a single loop invariant: a label (a non-empty, non-keyword
    identifier via `genIdentName`, since an invariant label appears in identifier
    position) paired with a boolean expression. -/
def genInvariant [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G (String × Expression.Expr) := do
  let l ← genIdentName
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth .bool
  pure (l, e)

/-- Generate a list of (up to `depth`) loop invariants, each a
    `(label, boolean expression)` pair. -/
def genInvariants [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) :
    G (List (String × Expression.Expr)) :=
  listOfMaxLength depth (genInvariant octx tvars ctx depth pctx)

-- ── Non-nesting (leaf) statement sub-generators ──────────────────────────

/-- Generate a `cmd` statement by delegating to `genCmd`. The imperative command
    is wrapped as `CmdExt.cmd`; `C` is unchanged. -/
def genCmdStmt [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : G GenStmtResult := do
  let r ← genCmd octx tvars immutableVars ctx depth pctx
  pure ⟨[Stmt.cmd (CmdExt.cmd r.cmd)], C, r.outCtx⟩

/-- Generate an `exit` statement that targets a block around it. The typing rule
    `StatementHasType'.exit` needs the label to be a member of the list of the labels, so `elements` draws the
    target label from that list. Therefore the generated `exit` leaves a block that truly encloses it. When no
    block encloses the point, so the list of the labels is empty, *no* well-typed `exit`
    exists, so this produces the empty generator (`default`, whose `SetGen.Set`
    support is `∅`): the `exit` branch simply contributes nothing there. Context
    is unchanged. -/
def genExitStmt [Gen G] (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) : G GenStmtResult :=
  match labels with
  | [] => default
  | l :: ls => do
      let lbl ← elements (l :: ls) (by simp)
      pure ⟨[Stmt.exit lbl default], C, ctx⟩

/-- Generate a `funcDecl` statement. The syntactic declaration `decl` (a
    non-recursive `PureFunc`) and the well-typed witness `func` (added to `C`)
    are sampled independently, mirroring the declarative rule's decoupling of the
    two. `Γ` is unchanged; `C` becomes `C.addFactoryFunction func`. -/
def genFuncDeclStmt [Gen G] (octx : OpCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : G GenStmtResult := do
  let decl ← genDecl octx depth pctx
  let func ← genFunction [] octx depth pctx
  pure ⟨[Stmt.funcDecl decl default], C.addFactoryFunction func.toLFunc, ctx⟩

/-- Generate a `typeDecl` statement. The function draws a random `TypeConstructor`, and it checks that
    constructor against the context through `addKnownTypeWithError`. On a success, the output context is the
    extended context. After a clash of two names, the function gives the empty generator, whose support is
    empty, so a constructor whose name clashes gives nothing. Therefore the generator is total and sound. -/
def genTypeDeclStmt [Gen G] (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) :
    G GenStmtResult := do
  let tc ← genTypeConstructor depth
  match C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default with
  | .ok C' => pure ⟨[Stmt.typeDecl tc default], C', ctx⟩
  | .error _ => default

-- ── Procedure-call statement sub-generator ────────────────────────────────

/-- Whether the name `x : τ` declared by the callee can be *reused* from the ambient
    scope: `ctx` must bind `x` at exactly `τ`, and `x` must not be immutable (the
    callee writes back through its in-out/out arguments, and writing an immutable
    variable would violate the enclosing procedure's `modRights`). -/
def reusable (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (q : Identifier Unit × LMonoTy) : Bool :=
  ctx.find? q.1 == some q.2 && !immutableVars.contains q.1

/-- Whether the name `x : τ` must be **`init`ed** before the call: `x` is absent
    from the ambient scope, so there is nothing to reuse. -/
def needsInit (ctx : VarCtx) (q : Identifier Unit × LMonoTy) : Bool :=
  ctx.isFresh q.1

/-- A name that the callee fixes is *usable* exactly when the call site can reuse it, or can declare it with an
    `init` statement. Two other cases make the callee uncallable at this site: the scope binds the name at a
    **conflicting** type, or it binds the name at the correct type and the name is **immutable**. The call rule
    gives the generator no freedom over such a name.

    This predicate applies to an **in-out** argument only. The last premise of the call rule fixes an in-out
    argument to exactly the name that the callee declares for it. The rule puts no condition on the name of an
    output-only argument. Read `outTarget`. -/
def usableName (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (q : Identifier Unit × LMonoTy) : Bool :=
  reusable immutableVars ctx q || needsInit ctx q

/-- **Choose the caller's variable that will receive one `out` result.** A call's
    `out` arguments are not expressions but *variables the callee assigns to*, so
    for each `out` parameter the call site has to name one such variable. This picks
    it for the `out` parameter the callee declares as `q = (x, τ)` at position `i` of
    its output-only block; `base` is a length past which invented names are fresh.

    The caller chooses that name. The specification of Core asks that an `out` argument exists, that it has the
    declared type, and that it is writable. It says **nothing about its name**. The call rule does fix the name
    of an in-out argument to the name that the callee declares. Therefore this function does two things:

    * When the scope already binds the name of the callee at exactly that type, and that name is writable, which
      `reusable` decides, the function receives the result in that variable. Real Strata code most often has that
      shape.
    * Otherwise it picks the new name `indexedFreshName base i`, which the caller
      brings into scope with an `init` just before the call.

    A new name is *always* available, so an output-only parameter can never make a callee uncallable. Therefore
    the name of an out argument needs no `usableName` guard, and it admits none. In each case, the type of the
    chosen variable is the declared type, so each argument position still agrees with the declared output type of
    the callee. -/
def outTarget (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (base : Nat)
    (q : Identifier Unit × LMonoTy) (i : Nat) : Identifier Unit × LMonoTy :=
  if reusable immutableVars ctx q then q else (⟨indexedFreshName base i, ()⟩, q.2)

/-- **Choose one receiving variable per `out` parameter**, across the callee's whole
    output-only block `O`: `outTarget` at each position, with the base taken past
    each name of the scope, so that each new name is fresh and two different positions get two different names.
    The result has the same length as the output-only block, and the same types in the same order, which
    `outTargets_length` and `outTargets_values` prove. Only the names can differ. -/
def outTargets (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (O : @LMonoTySignature Unit) : @LMonoTySignature Unit :=
  O.toList.zipIdx.map (fun p => outTarget immutableVars ctx (maxNameLen ctx) p.1 p.2)

/-- Generate a procedure-call statement targeting one of the callable procedures
    in `procs`. This follows the call-site recipe literally, step by step:

    1. **Pick a random callee** `s` from the procedure context (`elements`).
    2. **Examine its type signature for in-out args.** `s`'s signature decomposes as
       `inputs = s.M ++ s.I` and `outputs = s.M ++ s.O` (the shared block `s.M`
       leading both), so the in-out block is
       exactly `s.M` (`getInoutParams = s.M`), the input-only block is `s.I`, and
       the output-only block is `s.O`. The in-out and out args are the ones the
       callee *writes back through*, so each of them needs a variable of the caller, and not an expression. Those
       arguments are the in-out block, together with one receiving variable for each out argument, which
       `inoutNames` and `outTargets` below give. When the in-out block is empty, there is no in-out argument, and
       step 3 covers the out targets only.
    3. **For each in-out arg `x : τ` (then likewise each out arg), check whether
       `ctx` already has `x : τ`.** For an *in-out* arg the call rule forces the
       argument to be named *exactly* as the callee declares it, at exactly the
       declared type, so there is no naming freedom: `reusable` decides the check
       (and additionally requires `x` be writable, since the callee may assign it).
        * **Yes.** Pass the variable of the scope through as the in-out argument, and emit nothing for it.
        * **No.** The variable must be absent, which `needsInit` decides, and the generator emits an `init` for it
          *before* the call. When the scope instead binds that name at a conflicting type, or binds it as an
          immutable name, the generator skips this callee, through the empty generator,
          which keeps the generator total.

       For an *out* arg the same reuse-or-`init` choice is made, but the name is
       **ours** to pick (the Core spec constrains an out argument's existence, type
       and writability, not its name): `outTargets` reuses `x : τ` when it is in scope
       and writable, and otherwise picks a brand-new name to `init`. Since a new name
       is always available, an out arg never makes a callee uncallable, and the guard
       covers `inoutNames` only.
    4. **Generate the call.** The by-value inputs `exprs` (one per `s.I` position, at
       the type declared there) are drawn from `genLExpr`, and the argument list is
       assembled by `mkArgs`: `inout` args for `s.M`, `in` args for `exprs`, `out`
       args for `outTargets`.

    The emitted shape is uniform. It holds the `init` statements for the missing names only, then the `call`, and
    the generator splices that group **inline** into the statement sequence around it, with no block and no
    label. When the call reuses *each* in-out argument and each out target, the list of the `init` statements is
    empty, and the group is the bare call, which is the
    common shape in real Strata code; otherwise the `init`s simply precede the call
    in the ambient scope.

    Because the `init`s are emitted in the *ambient* scope rather than inside a
    block with a lexical scope, they extend the scope of the variables. The output context is
    `insertAllCtx ctx toInit`, and not the input context. That is the price of the inline form, and it is why the
    field `GenStmtResult.stmts` is a statement **list**. The sequence around it, which `genStmtChain` builds,
    splices that list in, and it threads the extended context onward.

    The `init`s use the nondeterministic form `init x τ *` (a havoc), which needs
    no initializer expression and hence no extra expression-typing obligation.

    The remaining `Nodup` guard is genuinely needed: the callee's own signature may
    repeat a key, and a reused out target may coincide with an in-out name, either
    of which would make the `init` chain shadow a name it had already declared.

    Note that no `labels` argument is needed: emitting no block means the
    enclosing-label set plays no role, and the emitted sequence is correspondingly
    well-typed at *every* label set (see `genCallStmt_sound`). -/
def genCallStmt [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : G GenStmtResult :=
  match procs with
  | [] => default
  | p₀ :: ps => do
    -- Step 1: pick a random procedure to call from the procedure context.
    let s ← elements (p₀ :: ps) (by simp)
    -- Step 2. Instantiate the type parameters of the callee. The signature of a polymorphic callee is over its
    -- own type parameters, and the call rule permits each concrete instantiation. The generator therefore samples
    -- one monotype for each type parameter, from the generable types, as `genIndirPoly` samples a type for
    -- polymorphic factory functions), then instantiate the three signature blocks
    -- by `σ`. A monomorphic callee (`s.typeArgs = []`) gives `σ = []`, and
    -- `substSig [] = id`, so this reduces to the previous behaviour verbatim.
    let generableTys := generableTypesFromCtx ctx.values [] octx
    let σvals ← s.typeArgs.mapM (fun _ =>
      if hg : generableTys.length > 0 then
        elements generableTys (by apply List.ne_nil_of_length_pos; assumption)
      else pure .bool)
    let σ : List (TyIdentifier × LMonoTy) := s.typeArgs.zip σvals
    -- The instantiated blocks: types substituted, names untouched.
    let Mσ := StrataGenerators.Stmt.substSig σ s.M
    let Iσ := StrataGenerators.Stmt.substSig σ s.I
    let Oσ := StrataGenerators.Stmt.substSig σ s.O
    -- Step 3: read the in-out args off the callee's (instantiated) signature. Front
    -- alignment (`inputs = M ++ I`, `outputs = M ++ O`) makes `Mσ` exactly the
    -- in-out block, and the second holds the output-only arguments. The callee writes back through both blocks,
    -- so both need a variable of the caller, and the callee fixes the name of an in-out argument only, which step
    -- 4 handles. `substSig` keeps each key, so the in-out names are still exactly the names of the declared
    -- block. The callee fixes each name, and the instantiation fixes each type.
    let inoutNames : List (Identifier Unit × LMonoTy) := Mσ
    let outTargets : @LMonoTySignature Unit := outTargets immutableVars ctx Oσ
    -- Step 4. For each in-out argument, reuse the variable of the scope when the scope holds it at the correct
    -- type, and otherwise plan an `init` for it. A name that the call can neither reuse nor declare makes this
    -- callee uncallable here. Each out target is usable by construction, which `outTargets_all_usableName`
    -- proves.
    if inoutNames.all (usableName immutableVars ctx) = true
        ∧ (Mσ ++ outTargets).keys.Nodup then
      -- The in-out arguments that the group must declare first, and then the out targets that it must declare.
      let inoutToInit := inoutNames.filter (needsInit ctx)
      let outToInit := outTargets.filter (needsInit ctx)
      let toInit := inoutToInit ++ outToInit
      -- Step 5: generate the by-value inputs (at the *instantiated* input types)
      -- and assemble the call. The `mkArgs` in-out/out names come from key-position
      -- only, and `substSig` preserves keys, so passing `s.M` is the same as `Mσ`.
      let exprs ← Iσ.values.mapM (fun τ => genLExpr ctx.toFVarCtx octx pctx tvars [] depth τ)
      -- Step 6: sample how the by-value inputs and the out targets interleave. The
      -- call rule reads the input positions and the write positions through two
      -- projections that each drop the other kind of node, so their relative order
      -- is free. `mask` picks one order; see `mkArgs`.
      let mask ← listOf (elements [true, false] (by simp))
      let theCall :=
        Statement.call s.pname
          (StrataGenerators.Stmt.mkArgs s.M outTargets exprs mask) default
      -- The `init`s (possibly none) then the call, inline in the ambient scope.
      pure ⟨StrataGenerators.Stmt.initChain toInit ++ [theCall], C,
        StrataGenerators.Stmt.insertAllCtx ctx toInit⟩
    else
      default

-- ── Main mutually-recursive statement / statement-list generators ─────────

mutual

/-- Generate a well-typed `Statement` given the ambient context `C`, the variable
    scope `ctx`, and a single `size` budget.

    The parameter `size` is the knob for the size of a draw. It bounds the depth of the nesting of the statement
    *and* the size of an expression and the length of a generated statement sequence, because the generator passes
    it to each sub-generator for a leaf and for an expression, and to each `choose` for the length of a body.
    There is no separate `fuel` for the nesting: `size` plays both roles, as the one `Nat` argument of
    `genLExprBase` does
    for expressions.

    At `size = 0` only the *leaf* constructors are produced (`cmd`, `exit`,
    `funcDecl`, `typeDecl`), with size-0 expressions. At `size + 1` the nesting
    constructors (`block`, `ite`, `loop`) may additionally be produced, with their
    bodies generated at the smaller `size` (so sub-programs shrink as they nest).

    A procedure `call` is produced at every size. It is the one branch that may
    yield more than one statement: its missing-name `init`s precede it in the
    **ambient** scope, so it returns the list `init … ++ [call]` and an extended
    output scope (see `genCallStmt`). This is why the result type is a statement
    *list*; every other branch returns a singleton.

    Each generated statement satisfies `StatementsHasTypeA P C Γ ss C' Γ'`, at each program. Read
    `genStmt_sound`.

    Tagged `@[tunable]`, so every branch weight is a runtime knob, and `genStmt.tuned θ` reads each
    weight from `θ`. There are two sites: the `size = 0` leaf list has arity 5, and the `size + 1`
    list has arity 9. The second site carries `loop` at flat index 13, which is the knob that a
    loop-transformation test wants turned up.

    The weights are *constant* rather than indexed by `size`, because no `depth` binder is in scope
    and each site therefore reads its schedule at depth 0. This recursion cannot run away, unlike an
    expression generator's: the nesting branches exist only at `size + 1`, and they generate their
    bodies at `size`. A decaying schedule has nothing to protect against.
    `StrataGenerators.TuningProfiles` holds the profiles that the suite uses.

    **Why `exit` and `call` fall back to a command.** An `exit` needs an enclosing block label, and a
    `call` needs a callee. With `labels = []` or with `procs = []` those generators have *empty
    support* and can only throw. The weight `if labels.isEmpty then 0 else 1` used to prune them, and
    `frequency` skips a zero-weight branch. But `@[tunable]` cannot see a weight that an `if`
    computes, and it rejects a literal `0`, which would break support-completeness.

    So the *branch* prunes itself instead of its weight: it defers to `genCmdStmt`, which branch 0
    already offers. Every weight stays a positive literal, and the generator stays throw-free. The
    branch's support is then `genExitStmt`'s support, or a subset of branch 0's, so the union over the
    list is unchanged. `genStmt`'s support is that union, which is why the soundness and completeness
    proofs need only a `cases labels` or a `cases procs`.

    The two distributions differ in one respect. This is not a regression, and it is worth knowing.
    The old generator renormalised over the surviving branches. This one hands the share of a pruned
    branch to `cmd`, which leaves `funcDecl` and `typeDecl` slightly rarer in a scope with no label
    and no callee. -/
@[tunable]
def genStmt [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx := []) :
    Nat → G GenStmtResult
  | 0 =>
    -- An `exit` needs an enclosing block label, and a `call` needs a callee. With
    -- `labels = []` or with `procs = []` those generators have *empty support* and can only
    -- throw, so the branch defers to `genCmdStmt`, which is branch 0's generator. The
    -- docstring says why the pruning moved from the weight into the branch.
    frequency
      [ (4, fun () => genCmdStmt octx tvars immutableVars C ctx 0 pctx),
        (1, fun () =>
          if labels.isEmpty then genCmdStmt octx tvars immutableVars C ctx 0 pctx
          else genExitStmt labels C ctx),
        (1, fun () => genFuncDeclStmt octx C ctx 0 pctx),
        (1, fun () => genTypeDeclStmt C ctx 0),
        (3, fun () =>
          if procs.isEmpty then genCmdStmt octx tvars immutableVars C ctx 0 pctx
          else genCallStmt octx tvars immutableVars procs C ctx 0 pctx) ]
      (by show 0 < 4+1+1+1+3; omega)
  | size + 1 =>
    -- As in the `size = 0` case, `exit` and `call` defer to `genCmdStmt` when their own
    -- support is provably empty, which happens with no enclosing label and with no callee.
    frequency
      [ (4, fun () => genCmdStmt octx tvars immutableVars C ctx (size + 1) pctx),
        (1, fun () =>
          if labels.isEmpty then genCmdStmt octx tvars immutableVars C ctx (size + 1) pctx
          else genExitStmt labels C ctx),
        (1, fun () => genFuncDeclStmt octx C ctx (size + 1) pctx),
        (1, fun () => genTypeDeclStmt C ctx (size + 1)),
        (3, fun () =>
          if procs.isEmpty then genCmdStmt octx tvars immutableVars C ctx (size + 1) pctx
          else genCallStmt octx tvars immutableVars procs C ctx (size + 1) pctx),
        (2, fun () => do
          -- The block's `label` must not shadow an enclosing one (`label ∉ L`,
          -- the new-spec `block` premise), so it is drawn fresh from `labels`.
          let label ← genFreshLabel labels
          let ⟨⟨len, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          -- The block's own `label` becomes an enclosing label for its body, so
          -- an `exit` inside the body can break out of this block. The body is
          -- generated at the smaller `size` (guaranteeing termination).
          let (body, _, _) ← genStmtChain octx tvars immutableVars procs (label :: labels) C ctx pctx size len
          pure ⟨[Stmt.block label body default], C, ctx⟩),
        (2, fun () => do
          let cond ← genLExpr ctx.toFVarCtx octx pctx tvars [] (size + 1) .bool
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (thenb, _, _) ← genStmtChain octx tvars immutableVars procs labels C ctx pctx size tlen
          let (elseb, _, _) ← genStmtChain octx tvars immutableVars procs labels C ctx pctx size elen
          pure ⟨[Stmt.ite (.det cond) thenb elseb default], C, ctx⟩),
        (1, fun () => do
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (thenb, _, _) ← genStmtChain octx tvars immutableVars procs labels C ctx pctx size tlen
          let (elseb, _, _) ← genStmtChain octx tvars immutableVars procs labels C ctx pctx size elen
          pure ⟨[Stmt.ite .nondet thenb elseb default], C, ctx⟩),
        (2, fun () => do
          let guard ← genCondOrNondet octx tvars ctx (size + 1) pctx
          let measure ← genOptMeasure octx tvars ctx (size + 1) pctx
          let invariants ← genInvariants octx tvars ctx (size + 1) pctx
          let ⟨⟨blen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (body, _, _) ← genStmtChain octx tvars immutableVars procs labels C ctx pctx size blen
          pure ⟨[Stmt.loop guard measure invariants body default], C, ctx⟩) ]
      (by show 0 < 4+1+1+1+3+2+2+1+2; omega)
termination_by n => (n, 0, 0)

/-- Generate a chain of up to `len` well-typed statement *groups*, threading both
    the ambient context `C` and the variable scope `ctx` through the chain. Each
    group is generated at the same `size`; `len` is a separate structural
    accumulator (the remaining number of groups).

    Named a *chain* rather than a sequence because it calls `genStmt` up to `len`
    times, and it splices each result. A group is usually one statement, and a procedure call also gives the
    `init` statements for each missing name. Therefore the result can be *longer* than the number of the steps.
    That number bounds the steps of the generation, and not the number of the statements.

    The function gives the statement list together with the final context and scope. The result satisfies the
    chained `StatementsHasTypeA` relation. Read `genStmtChain_sound`. -/
def genStmtChain [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx := []) (size : Nat) :
    Nat → G (List Statement × LContext CoreLParams × VarCtx)
  | 0 => pure ([], C, ctx)
  | len + 1 => do
    let r ← genStmt octx tvars immutableVars procs labels C ctx pctx size
    let (rest, C'', ctx'') ←
      genStmtChain octx tvars immutableVars procs labels r.outC r.outCtx pctx size len
    pure (r.stmts ++ rest, C'', ctx'')
termination_by n => (size, 1, n)

end

-- ── Top-level convenience generator ──────────────────────────────────────

/-- Generate a well-typed statement list of up to `len` statements, each generated
    at element `size`, starting from an empty ambient context and empty variable
    scope. The two knobs are orthogonal: `size` bounds each statement's
    nesting/expression size, `len` bounds the top-level sequence length. -/
def genProgramStmts [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (size len : Nat) (pctx : PolyOpCtx := []) :
    G (List Statement × LContext CoreLParams × VarCtx) :=
  genStmtChain octx tvars [] [] [] (LContext.default) [] pctx size len

-- ── Quick tests ──────────────────────────────────────────────────────────

open Std in
instance instToFormatUnitStmtHasTypeAGen : ToFormat Unit where
  format _ := .nil

-- Smoke test: a handful of individual statements at size 2.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨ss, _, _⟩ ← genStmt [] [] [] [] [] (LContext.default) [] [] 2
  IO.println <| Std.format ss |>.pretty : IO Unit)

-- A quick check: a statement from a scope that holds a variable, so that a `set` command and a guard over an
-- existing variable can appear. An expression of a body can also *read* such a variable, because the context of
-- the free variables comes from the scope.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨ss, _, _⟩ ← genStmt [] [] [] [] (LContext.default)
    [(⟨"x", ()⟩, .int), (⟨"b", ()⟩, .bool)] [] 2
  IO.println <| Std.format ss |>.pretty : IO Unit)

-- Smoke test: a whole statement sequence (size 2, up to 4 statements).
#guard_msgs(drop warning, drop all) in
#eval (do
  let (ss, _, _) ← genProgramStmts [] [] 2 4
  IO.println <| Std.format ss |>.pretty : IO Unit)

-- Smoke test: with enclosing labels in scope, `exit` may target one of them.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨ss, _, _⟩ ← genStmt [] [] [] ["outer", "inner"] (LContext.default) [] [] 2
  IO.println <| Std.format ss |>.pretty : IO Unit)

end StrataGenerators.Stmt
