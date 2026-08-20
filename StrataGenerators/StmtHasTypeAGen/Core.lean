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
`StmtHasTypeA` / `StmtsHasTypeA` relations of
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

`StmtHasType'` is a 6-place relation `C Γ L s C' Γ'` (post-#1392: the spec now
tracks the set `L` of enclosing-block labels). The generator threads a
representation of all three:

- `Γ` (variable type-scope) is threaded via the flat `VarCtx` from
  `CmdHasTypeAGen/Core.lean`, exactly as `genCmd`/`genCmds` do.
- `C` (the ambient `LContext`) is threaded as an honest `LContext CoreLParams`.
- `L` (the enclosing-block labels) is threaded as a `List String`, extended by a
  fresh label whenever the generator descends into a `block` body.

The **annotated** spec `instHasTypeA` ignores both `C` and `Γ` when typing
expressions, so `C` never influences *which expression* is produced. The only
constructor whose well-typedness genuinely depends on `C` is `typeDecl` (its
premise is `C.addKnownTypeWithError … = .ok C'`); we handle it by generating a
`TypeConstructor` and then **matching** on the result of `addKnownTypeWithError`,
so the `.ok` branch's output context is definitionally the required `C'`. On a
name clash we produce the empty generator (`default`, whose `SetGen.Set` support
is `∅`), so a clashing constructor simply contributes nothing.

## Labels

Under the new spec `exit label` requires `label ∈ L` and `block label` requires
`label ∉ L` (no shadowing), with the body typed under `label :: L`. Accordingly:

- `genExitStmt` samples its target from the *enclosing* labels `L` (via
  `elements`), so the generated `exit` genuinely targets a live enclosing block.
  When `L = []` (no enclosing block, e.g. at top level) no valid `exit` exists,
  so it produces the empty generator (`default`) — the `exit` branch contributes
  nothing there.
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

/-- The result of generating **one statement** — as a statement *list* — together
    with the output ambient context `C'` and output variable-scope `Γ'` (as a
    `VarCtx`).

    Almost every constructor yields a singleton `[s]`. The list is there for the
    one shape that genuinely spans several statements: a procedure `call` whose
    in-out/out arguments are not all in scope must be preceded by `init`s in the
    **ambient** scope (see `genCallStmt`), so its group is `init … ; init … ; call`
    and its output scope is strictly larger than its input. Rather than give calls
    a layer of their own, `genStmt` returns a list uniformly and `genStmtChain`
    splices whatever comes back. -/
structure GenStmtResult where
  /-- The generated statement, as a list — a singleton except for a call group. -/
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

/-- Generate a fresh block label not in `labels`. Uses `genIdentName` for
    randomness — so the label is a non-empty, non-keyword identifier (a `block`
    label appears in identifier position, so it must not be empty or a reserved
    word) — and falls back to a length-based guarantee when the random label
    collides. Guarantees `label ∉ labels`, the `block` premise of the new spec.
    Mirrors `genFreshName` for variable names. -/
def genFreshLabel [Gen G] (labels : List String) : G String := do
  let s ← genIdentName
  if s ∈ labels then
    pure (fallbackFreshLabel labels)
  else
    pure s

-- ── TypeConstructor / declaration sub-generators ─────────────────────────

/-- Generate a random `TypeConstructor`: a name and a list of (up to `depth`)
    parameter names, all produced by `genIdentName` so each is a non-empty,
    non-keyword identifier (constructor and type-parameter names both appear in
    identifier position). The `bound` field is left at its default (`.Infinite`). -/
def genTypeConstructor [Gen G] (depth : Nat) : G TypeConstructor := do
  let name ← genIdentName
  let params ← listOfMaxLength depth genIdentName
  pure { name := name, params := params }

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

    Note: per the declarative `funcDecl` rule, the syntactic declaration `decl`
    and the well-typed witness `func` added to `C` are *independent* — the rule
    only requires `¬decl.isRecursive` and `FuncHasType' func`. The generator
    therefore samples them independently (see `genStmt`); this helper just
    supplies non-recursive `decl` nodes. -/
def genDecl [Gen G] (fctx : FVarCtx) (octx : OpCtx) (depth : Nat) :
    G (Imperative.PureFunc Expression) :=
  Function.toPureFuncDecl <$> genFunction fctx octx depth

-- ── Guard / measure / invariant sub-generators ───────────────────────────

/-- Generate an `ExprOrNondet` used as an `ite` condition or a `loop` guard:
    either `.nondet`, or `.det e` for a boolean expression `e`. -/
def genCondOrNondet [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : G (ExprOrNondet Expression) :=
  pick
    (fun () => pure .nondet)
    (fun () => (fun e => ExprOrNondet.det e) <$> genLExpr fctx octx [] tvars [] depth .bool)

/-- Generate an optional loop measure: either `none`, or `some m` for an
    integer expression `m`. Biased to produce a measure 75% of the time (weights
    `1` for `none` versus `3` for `some`), so generated loops usually carry a
    measure. -/
def genOptMeasure [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : G (Option Expression.Expr) :=
  biasedOptionGen (3 / 4) (genLExpr fctx octx [] tvars [] depth .int)

/-- Generate a single loop invariant: a label (a non-empty, non-keyword
    identifier via `genIdentName`, since an invariant label appears in identifier
    position) paired with a boolean expression. -/
def genInvariant [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : G (String × Expression.Expr) := do
  let l ← genIdentName
  let e ← genLExpr fctx octx [] tvars [] depth .bool
  pure (l, e)

/-- Generate a list of (up to `depth`) loop invariants, each a
    `(label, boolean expression)` pair. -/
def genInvariants [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : G (List (String × Expression.Expr)) :=
  listOfMaxLength depth (genInvariant fctx octx tvars depth)

-- ── Non-nesting (leaf) statement sub-generators ──────────────────────────

/-- Generate a `cmd` statement by delegating to `genCmd`. The imperative command
    is wrapped as `CmdExt.cmd`; `C` is unchanged. -/
def genCmdStmt [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) : G GenStmtResult := do
  let r ← genCmd fctx octx tvars immutableVars ctx depth
  pure ⟨[Stmt.cmd (CmdExt.cmd r.cmd)], C, r.outCtx⟩

/-- Generate an `exit` statement targeting an enclosing block. Under the new
    typing spec `StmtHasType'.exit` requires `label ∈ L`, so the target label is
    sampled (via `elements`) from the enclosing-block `labels` — the generated
    `exit` genuinely breaks out of a live enclosing block. When no block encloses
    the current point (`labels = []`, e.g. at top level) *no* well-typed `exit`
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
def genFuncDeclStmt [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) : G GenStmtResult := do
  let decl ← genDecl fctx octx depth
  let func ← genFunction fctx octx depth
  pure ⟨[Stmt.funcDecl decl default], C.addFactoryFunction func.toLFunc, ctx⟩

/-- Generate a `typeDecl` statement. A random `TypeConstructor` is generated and
    checked against `C` via `addKnownTypeWithError`. On success the output context
    is the extended `C'`; on a name clash we produce the empty generator
    (`default`, support `∅`), so a clashing constructor simply contributes nothing.
    This keeps the generator total and sound. -/
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

/-- A name the callee dictates is *usable* exactly when we can either reuse it or
    `init` it. Anything else — bound at a **conflicting** type, or bound at the
    right type but **immutable** — makes that callee genuinely uncallable at this
    site, since the call rule gives the generator no naming freedom.

    This applies to the **in-out** arguments only: the call rule pins an in-out
    argument to the very name the callee declares for it (`CmdExtHasType'.call`'s
    last premise). Output-only arguments are *not* name-constrained — see
    `outTarget`. -/
def usableName (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (q : Identifier Unit × LMonoTy) : Bool :=
  reusable immutableVars ctx q || needsInit ctx q

/-- **Choose the caller's variable that will receive one `out` result.** A call's
    `out` arguments are not expressions but *variables the callee assigns to*, so
    for each `out` parameter the call site has to name one such variable. This picks
    it for the `out` parameter the callee declares as `q = (x, τ)` at position `i` of
    its output-only block; `base` is a length past which invented names are fresh.

    The name is genuinely the caller's to choose. The Core spec (§4.6.4) requires an
    `out` argument to exist, to have the declared type, and to be writable, but says
    **nothing about its name** — unlike an in-out argument, which the call rule pins
    to the name the callee declares. So:

    * if the callee's own name `x` happens to already be in scope at exactly `τ` and
      is writable (`reusable`), receive the result in that `x` — the shape real
      Strata code most often has;
    * otherwise pick the brand-new name `indexedFreshName base i`, which the caller
      brings into scope with an `init` just before the call.

    Because a brand-new name is *always* available, an output-only parameter can
    never make a callee uncallable — so out names need (and admit) no `usableName`
    guard. Either way the type of the chosen variable is `τ = q.2`, so the argument
    positions still line up with the callee's declared output types. -/
def outTarget (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (base : Nat)
    (q : Identifier Unit × LMonoTy) (i : Nat) : Identifier Unit × LMonoTy :=
  if reusable immutableVars ctx q then q else (⟨indexedFreshName base i, ()⟩, q.2)

/-- **Choose one receiving variable per `out` parameter**, across the callee's whole
    output-only block `O`: `outTarget` at each position, with the base taken past
    every name in `ctx` so that every brand-new name is genuinely fresh and distinct
    positions get distinct names. The resulting list has the same length as `O` and
    the same types in the same order — see `outTargets_length`, `outTargets_values` —
    only the names may differ. -/
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
       callee *writes back through*, so each needs a caller variable rather than an
       expression: the in-out args `s.M` together with one receiving variable per out
       arg — `inoutNames` and `outTargets` below. When `s.M = []` there are no in-out
       args and step 3 ranges over the out targets alone.
    3. **For each in-out arg `x : τ` (then likewise each out arg), check whether
       `ctx` already has `x : τ`.** For an *in-out* arg the call rule forces the
       argument to be named *exactly* as the callee declares it, at exactly the
       declared type, so there is no naming freedom: `reusable` decides the check
       (and additionally requires `x` be writable, since the callee may assign it).
        * **Yes** — pass the ambient variable `x` straight through as the in-out
          argument. Nothing is emitted for `x`.
        * **No** — `x` must be absent (`needsInit`); we emit `init x τ *` for it
          *before* the call. If `x` is instead bound at a conflicting type, or is
          immutable, this callee is skipped entirely (empty generator, `default`),
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

    The emitted shape is uniform: the `init`s for just the missing names, followed
    by the `call`, spliced **inline** into the enclosing statement sequence — no
    enclosing block and no label. When *every* in-out arg and out target was reused
    the init list is empty and the sequence degenerates to the bare `[call]`, the
    common shape in real Strata code; otherwise the `init`s simply precede the call
    in the ambient scope.

    Because the `init`s are emitted in the *ambient* scope rather than inside a
    lexically-scoped block, they genuinely extend the variable scope: the output
    context is `insertAllCtx ctx toInit`, not the input `ctx`. That is the price of
    inlining, and it is why `GenStmtResult.stmts` is a statement **list** — the
    enclosing sequence (`genStmtChain`) splices the list in and threads the
    extended context onward.

    The `init`s use the nondeterministic form `init x τ *` (a havoc), which needs
    no initializer expression and hence no extra expression-typing obligation.

    The remaining `Nodup` guard is genuinely needed: the callee's own signature may
    repeat a key, and a reused out target may coincide with an in-out name, either
    of which would make the `init` chain shadow a name it had already declared.

    Note that no `labels` argument is needed: emitting no block means the
    enclosing-label set plays no role, and the emitted sequence is correspondingly
    well-typed at *every* label set (see `genCallStmt_sound`). -/
def genCallStmt [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) : G GenStmtResult :=
  match procs with
  | [] => default
  | p₀ :: ps => do
    -- Step 1: pick a random procedure to call from the procedure context.
    let s ← elements (p₀ :: ps) (by simp)
    -- Step 2: read the in-out args off the callee's signature. Front alignment
    -- (`inputs = M ++ I`, `outputs = M ++ O`) makes `s.M` exactly the in-out
    -- block; `s.O` are the output-only args. Both blocks are written back through,
    -- so both need caller variables, but only the in-out names are dictated to us
    -- (step 3).
    let inoutNames : List (Identifier Unit × LMonoTy) := s.M
    let outTargets : @LMonoTySignature Unit := outTargets immutableVars ctx s.O
    -- Step 3: for each in-out arg, reuse the ambient `x : τ` when we have it,
    -- otherwise plan an `init`. A name that is neither reusable nor absent makes
    -- this callee uncallable here. (The out targets are always usable by
    -- construction — see `outTargets_all_usableName`.)
    if inoutNames.all (usableName immutableVars ctx) = true
        ∧ (s.M ++ outTargets).keys.Nodup then
      -- The in-out args we must `init` first, then the out targets we must `init`.
      let inoutToInit := inoutNames.filter (needsInit ctx)
      let outToInit := outTargets.filter (needsInit ctx)
      let toInit := inoutToInit ++ outToInit
      -- Step 4: generate the by-value inputs and assemble the call.
      let exprs ← s.I.values.mapM (fun σ => genLExpr fctx octx [] tvars [] depth σ)
      let theCall :=
        Statement.call s.pname (StrataGenerators.Stmt.mkArgs s.M outTargets exprs) default
      -- The `init`s (possibly none) then the call, inline in the ambient scope.
      pure ⟨StrataGenerators.Stmt.initChain toInit ++ [theCall], C,
        StrataGenerators.Stmt.insertAllCtx ctx toInit⟩
    else
      default

-- ── Main mutually-recursive statement / statement-list generators ─────────

mutual

/-- Generate a well-typed `Statement` given the ambient context `C`, the variable
    scope `ctx`, and a single `size` budget.

    `size` is the QuickCheck-style `sized` knob: it bounds the statement's nesting
    depth *and* — as it is passed on to the leaf/expression sub-generators and to
    the body-length `choose`s — the size of expressions and the length of
    generated statement sequences. There is no separate nesting `fuel`: `size`
    plays both roles, exactly as the single `Nat` argument of `genLExprBase` does
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

    The generated statements satisfy `StmtsHasTypeA P C Γ ss C' Γ'` (for any
    program `P`) — see `genStmt_sound`.

    Tagged `@[tunable]`, so every branch weight is a runtime knob: `genStmt.tuned θ`
    reads them from `θ` at the current `size`. The two sites are the `size = 0`
    leaf list (arity 5) and the `size + 1` list (arity 9), the latter having `loop`
    at flat index 13 — the knob a loop-transformation test wants turned up. See
    `StrataGenerators.TuningProfiles` for the profiles the test suite uses, and
    `TuningPrototypes.genStmt_mutual_tuned_eq` for the proof that no `θ` changes what is
    reachable.
    The weights are *constant* rather than `size`-indexed (no `depth` binder is in
    scope, so every site reads its schedule at depth 0): unlike an expression
    generator, this recursion cannot run away — the nesting branches exist only at
    `size + 1` and generate their bodies at `size`, so nesting depth is bounded by
    the initial budget whatever the weights are, and a decaying schedule has
    nothing to protect against.

    **Why `exit`/`call` fall back to a command.** `exit` needs an enclosing block
    label and `call` needs a callee, so with `labels = []` / `procs = []` those
    generators have *empty support* and can only throw. They used to be pruned by
    the weight `if labels.isEmpty then 0 else 1`, which `frequency` skips — but a
    weight computed by an `if` is invisible to `@[tunable]`, and a literal `0` is
    rejected outright (it would break support-completeness). Pruning the *branch*
    instead of its weight — deferring to `genCmdStmt`, which branch 0 already
    offers — keeps every weight a positive literal and is equally throw-free. The
    branch's support is then either `genExitStmt`'s or a subset of branch 0's, so
    the union over the list, i.e. `genStmt`'s support, is unchanged; that is why
    the soundness and completeness proofs go through with only a `cases labels` /
    `cases procs` added.

    The distributions differ in one respect, which is not a regression but is
    worth knowing: where the old generator renormalised over the surviving
    branches (`cmd` took 4/6 of a label-free, callee-free leaf draw), this one
    hands the pruned branches' share to `cmd` (4/8 directly plus 2/8 through the
    fallbacks, i.e. 3/4), leaving `funcDecl` and `typeDecl` slightly rarer than
    before. -/
@[tunable]
def genStmt [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) : Nat → G GenStmtResult
  | 0 =>
    frequency
      [ (4, fun () => genCmdStmt fctx octx tvars immutableVars C ctx 0),
        (1, fun () =>
          if labels.isEmpty then genCmdStmt fctx octx tvars immutableVars C ctx 0
          else genExitStmt labels C ctx),
        (1, fun () => genFuncDeclStmt fctx octx C ctx 0),
        (1, fun () => genTypeDeclStmt C ctx 0),
        (1, fun () =>
          if procs.isEmpty then genCmdStmt fctx octx tvars immutableVars C ctx 0
          else genCallStmt fctx octx tvars immutableVars procs C ctx 0) ]
      (by show 0 < 4+1+1+1+1; omega)
  | size + 1 =>
    frequency
      [ (4, fun () => genCmdStmt fctx octx tvars immutableVars C ctx (size + 1)),
        (1, fun () =>
          if labels.isEmpty then genCmdStmt fctx octx tvars immutableVars C ctx (size + 1)
          else genExitStmt labels C ctx),
        (1, fun () => genFuncDeclStmt fctx octx C ctx (size + 1)),
        (1, fun () => genTypeDeclStmt C ctx (size + 1)),
        (1, fun () =>
          if procs.isEmpty then genCmdStmt fctx octx tvars immutableVars C ctx (size + 1)
          else genCallStmt fctx octx tvars immutableVars procs C ctx (size + 1)),
        (2, fun () => do
          -- The block's `label` must not shadow an enclosing one (`label ∉ L`,
          -- the new-spec `block` premise), so it is drawn fresh from `labels`.
          let label ← genFreshLabel labels
          let ⟨⟨len, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          -- The block's own `label` becomes an enclosing label for its body, so
          -- an `exit` inside the body can break out of this block. The body is
          -- generated at the smaller `size` (guaranteeing termination).
          let (body, _, _) ← genStmtChain fctx octx tvars immutableVars procs (label :: labels) C ctx size len
          pure ⟨[Stmt.block label body default], C, ctx⟩),
        (2, fun () => do
          let cond ← genLExpr fctx octx [] tvars [] (size + 1) .bool
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (thenb, _, _) ← genStmtChain fctx octx tvars immutableVars procs labels C ctx size tlen
          let (elseb, _, _) ← genStmtChain fctx octx tvars immutableVars procs labels C ctx size elen
          pure ⟨[Stmt.ite (.det cond) thenb elseb default], C, ctx⟩),
        (1, fun () => do
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (thenb, _, _) ← genStmtChain fctx octx tvars immutableVars procs labels C ctx size tlen
          let (elseb, _, _) ← genStmtChain fctx octx tvars immutableVars procs labels C ctx size elen
          pure ⟨[Stmt.ite .nondet thenb elseb default], C, ctx⟩),
        (2, fun () => do
          let guard ← genCondOrNondet fctx octx tvars (size + 1)
          let measure ← genOptMeasure fctx octx tvars (size + 1)
          let invariants ← genInvariants fctx octx tvars (size + 1)
          let ⟨⟨blen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (body, _, _) ← genStmtChain fctx octx tvars immutableVars procs labels C ctx size blen
          pure ⟨[Stmt.loop guard measure invariants body default], C, ctx⟩) ]
      (by show 0 < 4+1+1+1+1+2+2+1+2; omega)
termination_by n => (n, 0, 0)

/-- Generate a chain of up to `len` well-typed statement *groups*, threading both
    the ambient context `C` and the variable scope `ctx` through the chain. Each
    group is generated at the same `size`; `len` is a separate structural
    accumulator (the remaining number of groups).

    Named a *chain* rather than a sequence because it calls `genStmt` up to `len`
    times and splices each result: a group is normally a single statement, but a
    procedure call contributes its missing-name `init`s alongside it, so the
    returned list may be *longer* than `len` — `len` bounds the number of
    generation steps, not the statement count.

    Returns the statement list together with the final `(C, Γ)`. Satisfies the
    chained `StmtsHasTypeA` relation — see `genStmtChain_sound`. -/
def genStmtChain [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat) :
    Nat → G (List Statement × LContext CoreLParams × VarCtx)
  | 0 => pure ([], C, ctx)
  | len + 1 => do
    let r ← genStmt fctx octx tvars immutableVars procs labels C ctx size
    let (rest, C'', ctx'') ← genStmtChain fctx octx tvars immutableVars procs labels r.outC r.outCtx size len
    pure (r.stmts ++ rest, C'', ctx'')
termination_by n => (size, 1, n)

end

-- ── Top-level convenience generator ──────────────────────────────────────

/-- Generate a well-typed statement list of up to `len` statements, each generated
    at element `size`, starting from an empty ambient context and empty variable
    scope. The two knobs are orthogonal: `size` bounds each statement's
    nesting/expression size, `len` bounds the top-level sequence length. -/
def genProgramStmts [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (size len : Nat) : G (List Statement × LContext CoreLParams × VarCtx) :=
  genStmtChain fctx octx tvars [] [] [] (LContext.default) [] size len

-- ── Quick tests ──────────────────────────────────────────────────────────

open Std in
instance instToFormatUnitStmtHasTypeAGen : ToFormat Unit where
  format _ := .nil

-- Smoke test: a handful of individual statements at size 2.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨ss, _, _⟩ ← genStmt [] [] [] [] [] [] (LContext.default) [] 2
  IO.println <| Std.format ss |>.pretty : IO Unit)

-- Smoke test: a statement started from a non-empty variable scope, so `set`
-- and control-flow guards over existing variables can appear.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨ss, _, _⟩ ← genStmt [] [] [] [] [] [] (LContext.default)
    [(⟨"x", ()⟩, .int), (⟨"b", ()⟩, .bool)] 2
  IO.println <| Std.format ss |>.pretty : IO Unit)

-- Smoke test: a whole statement sequence (size 2, up to 4 statements).
#guard_msgs(drop warning, drop all) in
#eval (do
  let (ss, _, _) ← genProgramStmts [] [] [] 2 4
  IO.println <| Std.format ss |>.pretty : IO Unit)

-- Smoke test: with enclosing labels in scope, `exit` may target one of them.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨ss, _, _⟩ ← genStmt [] [] [] [] [] ["outer", "inner"] (LContext.default) [] 2
  IO.println <| Std.format ss |>.pretty : IO Unit)

end StrataGenerators.Stmt
