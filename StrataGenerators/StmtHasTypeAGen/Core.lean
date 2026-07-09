import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import Basalt.Examples.ArbString.Def
import Strata.Languages.Core.StatementTypeSpec
import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.Combinators

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

## The two threaded contexts

`StmtHasType'` is a 5-place relation `C Γ s C' Γ'`. The generator threads a
representation of both:

- `Γ` (variable type-scope) is threaded via the flat `VarCtx` from
  `CmdHasTypeAGen/Core.lean`, exactly as `genCmd`/`genCmds` do.
- `C` (the ambient `LContext`) is threaded as an honest `LContext CoreLParams`.

The **annotated** spec `instHasTypeA` ignores both `C` and `Γ` when typing
expressions, so `C` never influences *which expression* is produced. The only
constructor whose well-typedness genuinely depends on `C` is `typeDecl` (its
premise is `C.addKnownTypeWithError … = .ok C'`); we handle it by generating a
`TypeConstructor` and then **matching** on the result of `addKnownTypeWithError`,
so the `.ok` branch's output context is definitionally the required `C'`. On a
name clash we fall back to an (always-well-typed) `exit`.

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

-- ── TypeConstructor / declaration sub-generators ─────────────────────────

/-- Generate a random `TypeConstructor`: an alphanumeric name and a list of
    (up to `depth`) alphanumeric parameter names. The `bound` field is left at
    its default (`.Infinite`). -/
def genTypeConstructor [Gen G] (depth : Nat) : G TypeConstructor := do
  let name ← String.arbitrary
  let params ← listOfMaxLength depth String.arbitrary
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
    concreteEval := none,
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
    integer expression `m`. -/
def genOptMeasure [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : G (Option Expression.Expr) :=
  pick
    (fun () => pure none)
    (fun () => (fun e => some e) <$> genLExpr fctx octx [] tvars [] depth .int)

/-- Generate a single loop invariant: an alphanumeric label paired with a
    boolean expression. -/
def genInvariant [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) : G (String × Expression.Expr) := do
  let l ← String.arbitrary
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

/-- Generate an `exit` statement with a random label. Context is unchanged. -/
def genExitStmt [Gen G] (C : LContext CoreLParams) (ctx : VarCtx) : G GenStmtResult := do
  let l ← String.arbitrary
  pure ⟨Stmt.exit l default, C, ctx⟩

/-- Generate a `funcDecl` statement. The syntactic declaration `decl` (a
    non-recursive `PureFunc`) and the well-typed witness `func` (added to `C`)
    are sampled independently, mirroring the declarative rule's decoupling of the
    two. `Γ` is unchanged; `C` becomes `C.addFactoryFunction func`. -/
def genFuncDeclStmt [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) : G GenStmtResult := do
  let decl ← genDecl fctx octx depth
  let func ← genFunction fctx octx depth
  pure ⟨Stmt.funcDecl decl default, C.addFactoryFunction func, ctx⟩

/-- Generate a `typeDecl` statement. A random `TypeConstructor` is generated and
    checked against `C` via `addKnownTypeWithError`. On success the output context
    is the extended `C'`; on a name clash we fall back to an `exit` (leaving `C`
    unchanged), keeping the generator total and sound. -/
def genTypeDeclStmt [Gen G] (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) :
    G GenStmtResult := do
  let tc ← genTypeConstructor depth
  match C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default with
  | .ok C' => pure ⟨Stmt.typeDecl tc default, C', ctx⟩
  | .error _ => pure ⟨Stmt.exit "" default, C, ctx⟩

-- ── Main mutually-recursive statement / statement-list generators ─────────

mutual

/-- Generate a well-typed `Statement` given the ambient context `C`, the variable
    scope `ctx`, an expression-term `depth`, and a nesting `fuel`.

    At `fuel = 0` only the *leaf* constructors are produced (`cmd`, `exit`,
    `funcDecl`, `typeDecl`). At `fuel + 1` the nesting constructors (`block`,
    `ite`, `loop`) may additionally be produced, with their bodies generated at
    the smaller `fuel`.

    The generated statement satisfies `StmtHasTypeA P C Γ s C' Γ'` (for any
    program `P`) — see `genStmt_sound`. -/
def genStmt [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) : Nat → G GenStmtResult
  | 0 =>
    let gs : List (Nat × (Unit → G GenStmtResult)) :=
      [ (4, fun () => genCmdStmt fctx octx tvars C ctx depth),
        (1, fun () => genExitStmt C ctx),
        (1, fun () => genFuncDeclStmt fctx octx C ctx depth),
        (1, fun () => genTypeDeclStmt C ctx depth) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+1+1+1; omega
    frequency gs hw
  | fuel + 1 =>
    let gs : List (Nat × (Unit → G GenStmtResult)) :=
      [ (4, fun () => genCmdStmt fctx octx tvars C ctx depth),
        (1, fun () => genExitStmt C ctx),
        (1, fun () => genFuncDeclStmt fctx octx C ctx depth),
        (1, fun () => genTypeDeclStmt C ctx depth),
        (2, fun () => do
          let label ← String.arbitrary
          let ⟨⟨len, _⟩⟩ ← RandomChoice.choose 0 depth (Nat.zero_le depth)
          let (body, _, _) ← genStmts fctx octx tvars C ctx depth fuel len
          pure ⟨Stmt.block label body default, C, ctx⟩),
        (2, fun () => do
          let cond ← genLExpr fctx octx [] tvars [] depth .bool
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 depth (Nat.zero_le depth)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 depth (Nat.zero_le depth)
          let (thenb, _, _) ← genStmts fctx octx tvars C ctx depth fuel tlen
          let (elseb, _, _) ← genStmts fctx octx tvars C ctx depth fuel elen
          pure ⟨Stmt.ite (.det cond) thenb elseb default, C, ctx⟩),
        (1, fun () => do
          let ⟨⟨tlen, _⟩⟩ ← RandomChoice.choose 0 depth (Nat.zero_le depth)
          let ⟨⟨elen, _⟩⟩ ← RandomChoice.choose 0 depth (Nat.zero_le depth)
          let (thenb, _, _) ← genStmts fctx octx tvars C ctx depth fuel tlen
          let (elseb, _, _) ← genStmts fctx octx tvars C ctx depth fuel elen
          pure ⟨Stmt.ite .nondet thenb elseb default, C, ctx⟩),
        (2, fun () => do
          let guard ← genCondOrNondet fctx octx tvars depth
          let measure ← genOptMeasure fctx octx tvars depth
          let invariants ← genInvariants fctx octx tvars depth
          let ⟨⟨blen, _⟩⟩ ← RandomChoice.choose 0 depth (Nat.zero_le depth)
          let (body, _, _) ← genStmts fctx octx tvars C ctx depth fuel blen
          pure ⟨Stmt.loop guard measure invariants body default, C, ctx⟩) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+1+1+1+2+2+1+2; omega
    frequency gs hw
termination_by n => (n, 0, 0)

/-- Generate a length-`len` sequence of well-typed statements, threading both the
    ambient context `C` and the variable scope `ctx` through the sequence. Each
    statement is generated at nesting `fuel`.

    Returns the statement list together with the final `(C, Γ)`. Satisfies the
    chained `StmtsHasTypeA` relation — see `genStmts_sound`. -/
def genStmts [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (C : LContext CoreLParams) (ctx : VarCtx) (depth : Nat) (fuel : Nat) :
    Nat → G (List Statement × LContext CoreLParams × VarCtx)
  | 0 => pure ([], C, ctx)
  | len + 1 => do
    let r ← genStmt fctx octx tvars C ctx depth fuel
    let (rest, C'', ctx'') ← genStmts fctx octx tvars r.outC r.outCtx depth fuel len
    pure (r.stmt :: rest, C'', ctx'')
termination_by n => (fuel, 1, n)

end

-- ── Top-level convenience generator ──────────────────────────────────────

/-- Generate a well-typed statement list of length up to `len`, at nesting `fuel`
    and term depth `depth`, starting from an empty ambient context and empty
    variable scope. -/
def genProgramStmts [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth fuel len : Nat) : G (List Statement × LContext CoreLParams × VarCtx) :=
  genStmts fctx octx tvars (LContext.default) [] depth fuel len

-- ── Quick tests ──────────────────────────────────────────────────────────

open Std in
instance instToFormatUnitStmtHasTypeAGen : ToFormat Unit where
  format _ := .nil

-- Smoke test: a handful of individual statements at nesting fuel 2.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨s, _, _⟩ ← genStmt [] [] [] (LContext.default) [] 2 2
  IO.println <| Std.format s |>.pretty : IO Unit)

-- Smoke test: a statement started from a non-empty variable scope, so `set`
-- and control-flow guards over existing variables can appear.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let ⟨s, _, _⟩ ← genStmt [] [] [] (LContext.default)
    [(⟨"x", ()⟩, .int), (⟨"b", ()⟩, .bool)] 2 2
  IO.println <| Std.format s |>.pretty : IO Unit)

-- Smoke test: a whole statement sequence.
#guard_msgs(drop warning, drop all) in
#eval (do
  let (ss, _, _) ← genProgramStmts [] [] [] 2 2 4
  IO.println <| Std.format ss |>.pretty : IO Unit)

end StrataGenerators.Stmt
