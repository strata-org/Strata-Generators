import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import BasaltExamples.ArbString.Def
import Strata.Languages.Core.StatementTypeSpec
import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Core

open Lambda RandomChoice Core Imperative ArbString

/-!
# Core generator definitions for well-typed Strata Core `Statement`s

This file contains the canonical definition of `genStmt` / `genStmts`, mutually
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

/-- The result of generating a statement: the statement itself together with the
    output ambient context `C'` and output variable-scope `Γ'` (as a `VarCtx`). -/
structure GenStmtResult where
  /-- The generated statement. -/
  stmt : Statement
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
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) : G GenStmtResult := do
  let r ← genCmd fctx octx tvars ctx depth
  pure ⟨Stmt.cmd (CmdExt.cmd r.cmd), C, r.outCtx⟩

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
      pure ⟨Stmt.exit lbl default, C, ctx⟩

/-- Generate a `funcDecl` statement. The syntactic declaration `decl` (a
    non-recursive `PureFunc`) and the well-typed witness `func` (added to `C`)
    are sampled independently, mirroring the declarative rule's decoupling of the
    two. `Γ` is unchanged; `C` becomes `C.addFactoryFunction func`. -/
def genFuncDeclStmt [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) : G GenStmtResult := do
  let decl ← genDecl fctx octx depth
  let func ← genFunction fctx octx depth
  pure ⟨Stmt.funcDecl decl default, C.addFactoryFunction func.toLFunc, ctx⟩

/-- Generate a `typeDecl` statement. A random `TypeConstructor` is generated and
    checked against `C` via `addKnownTypeWithError`. On success the output context
    is the extended `C'`; on a name clash we produce the empty generator
    (`default`, support `∅`), so a clashing constructor simply contributes nothing.
    This keeps the generator total and sound. -/
def genTypeDeclStmt [Gen G] (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) :
    G GenStmtResult := do
  let tc ← genTypeConstructor depth
  match C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default with
  | .ok C' => pure ⟨Stmt.typeDecl tc default, C', ctx⟩
  | .error _ => default

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

    The generated statement satisfies `StmtHasTypeA P C Γ s C' Γ'` (for any
    program `P`) — see `genStmt_sound`. -/
def genStmt [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) : Nat → G GenStmtResult
  | 0 =>
    let gs : List (Nat × (Unit → G GenStmtResult)) :=
      [ (4, fun () => genCmdStmt fctx octx tvars C ctx 0),
        (1, fun () => genExitStmt labels C ctx),
        (1, fun () => genFuncDeclStmt fctx octx C ctx 0),
        (1, fun () => genTypeDeclStmt C ctx 0) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+1+1+1; omega
    frequency gs hw
  | size + 1 =>
    let gs : List (Nat × (Unit → G GenStmtResult)) :=
      [ (4, fun () => genCmdStmt fctx octx tvars C ctx (size + 1)),
        (1, fun () => genExitStmt labels C ctx),
        (1, fun () => genFuncDeclStmt fctx octx C ctx (size + 1)),
        (1, fun () => genTypeDeclStmt C ctx (size + 1)),
        (2, fun () => do
          -- The block's `label` must not shadow an enclosing one (`label ∉ L`,
          -- the new-spec `block` premise), so it is drawn fresh from `labels`.
          let label ← genFreshLabel labels
          let ⟨⟨len, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          -- The block's own `label` becomes an enclosing label for its body, so
          -- an `exit` inside the body can break out of this block. The body is
          -- generated at the smaller `size` (guaranteeing termination).
          let (body, _, _) ← genStmts fctx octx tvars (label :: labels) C ctx size len
          pure ⟨Stmt.block label body default, C, ctx⟩),
        (2, fun () => do
          let cond ← genLExpr fctx octx [] tvars [] (size + 1) .bool
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (thenb, _, _) ← genStmts fctx octx tvars labels C ctx size tlen
          let (elseb, _, _) ← genStmts fctx octx tvars labels C ctx size elen
          pure ⟨Stmt.ite (.det cond) thenb elseb default, C, ctx⟩),
        (1, fun () => do
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (thenb, _, _) ← genStmts fctx octx tvars labels C ctx size tlen
          let (elseb, _, _) ← genStmts fctx octx tvars labels C ctx size elen
          pure ⟨Stmt.ite .nondet thenb elseb default, C, ctx⟩),
        (2, fun () => do
          let guard ← genCondOrNondet fctx octx tvars (size + 1)
          let measure ← genOptMeasure fctx octx tvars (size + 1)
          let invariants ← genInvariants fctx octx tvars (size + 1)
          let ⟨⟨blen, _⟩⟩ ← RandomChoice.choose 0 (size + 1) (Nat.zero_le _)
          let (body, _, _) ← genStmts fctx octx tvars labels C ctx size blen
          pure ⟨Stmt.loop guard measure invariants body default, C, ctx⟩) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+1+1+1+2+2+1+2; omega
    frequency gs hw
termination_by n => (n, 0, 0)

/-- Generate a length-`len` sequence of well-typed statements, threading both the
    ambient context `C` and the variable scope `ctx` through the sequence. Each
    statement is generated at the same `size`; `len` is a separate structural
    accumulator (the remaining sequence length).

    Returns the statement list together with the final `(C, Γ)`. Satisfies the
    chained `StmtsHasTypeA` relation — see `genStmts_sound`. -/
def genStmts [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat) :
    Nat → G (List Statement × LContext CoreLParams × VarCtx)
  | 0 => pure ([], C, ctx)
  | len + 1 => do
    let r ← genStmt fctx octx tvars labels C ctx size
    let (rest, C'', ctx'') ← genStmts fctx octx tvars labels r.outC r.outCtx size len
    pure (r.stmt :: rest, C'', ctx'')
termination_by n => (size, 1, n)

end

-- ── Top-level convenience generator ──────────────────────────────────────

/-- Generate a well-typed statement list of up to `len` statements, each generated
    at element `size`, starting from an empty ambient context and empty variable
    scope. The two knobs are orthogonal: `size` bounds each statement's
    nesting/expression size, `len` bounds the top-level sequence length. -/
def genProgramStmts [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (size len : Nat) : G (List Statement × LContext CoreLParams × VarCtx) :=
  genStmts fctx octx tvars [] (LContext.default) [] size len

-- ── Quick tests ──────────────────────────────────────────────────────────

open Std in
instance instToFormatUnitStmtHasTypeAGen : ToFormat Unit where
  format _ := .nil

-- Smoke test: a handful of individual statements at size 2.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨s, _, _⟩ ← genStmt [] [] [] [] (LContext.default) [] 2
  IO.println <| Std.format s |>.pretty : IO Unit)

-- Smoke test: a statement started from a non-empty variable scope, so `set`
-- and control-flow guards over existing variables can appear.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨s, _, _⟩ ← genStmt [] [] [] [] (LContext.default)
    [(⟨"x", ()⟩, .int), (⟨"b", ()⟩, .bool)] 2
  IO.println <| Std.format s |>.pretty : IO Unit)

-- Smoke test: a whole statement sequence (size 2, up to 4 statements).
#guard_msgs(drop warning, drop all) in
#eval (do
  let (ss, _, _) ← genProgramStmts [] [] [] 2 4
  IO.println <| Std.format ss |>.pretty : IO Unit)

-- Smoke test: with enclosing labels in scope, `exit` may target one of them.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨s, _, _⟩ ← genStmt [] [] [] ["outer", "inner"] (LContext.default) [] 2
  IO.println <| Std.format s |>.pretty : IO Unit)

end StrataGenerators.Stmt
