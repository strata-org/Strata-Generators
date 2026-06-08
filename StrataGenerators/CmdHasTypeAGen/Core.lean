import Basalt.Gen
import Basalt.IO
import Strata.Languages.Core.CmdTypeSpec
import StrataGenerators.HasTypeAGen.Core

open Lambda RandomChoice Core Imperative

/-!
# Core generator definitions for well-typed `Cmd`s

This file contains the canonical definition of `genCmd`, a generator of
well-typed imperative commands satisfying the `CmdHasTypeA` relation.

The generator produces `Cmd Expression` values along with the output typing
context, using `genLExpr` from `HasTypeAGen/Core.lean` to generate well-typed
expressions for the right-hand sides of commands.
-/

-- ── Typing context representation ──────────────────────────────────────

/-- A flat representation of the typing context suitable for the generator.
    Each entry is a variable name paired with its monotype (we only deal
    with monomorphic contexts, i.e. `forAll [] mty`). -/
abbrev VarCtx := List (String × LMonoTy)

/-- Extract all variable names from a `VarCtx`. -/
def VarCtx.names (ctx : VarCtx) : List String :=
  ctx.map Prod.fst

/-- Look up a variable name in the context. -/
def VarCtx.find? (ctx : VarCtx) (x : String) : Option LMonoTy :=
  match ctx with
  | [] => none
  | (y, ty) :: rest => if x == y then some ty else VarCtx.find? rest x

/-- Check if a variable name is fresh (not in the context). -/
def VarCtx.isFresh (ctx : VarCtx) (x : String) : Bool :=
  ctx.find? x |>.isNone

-- ── Fresh name generation ──────────────────────────────────────────────

/-- Generate a fresh variable name not in `ctx` by appending a numeric suffix. -/
def genFreshName [Gen G] (ctx : VarCtx) : G String := do
  let n ← ArbNat.Nat.arbitrary
  let name := "v" ++ toString n
  if ctx.isFresh name then
    pure name
  else
    pure ("v" ++ toString (ctx.names.length + n))

-- ── Command sub-generators ─────────────────────────────────────────────

/-- The result of generating a command: the command itself and the output context. -/
structure GenCmdResult where
  /-- The generated command. -/
  cmd : Cmd Expression
  /-- The output typing context after executing the command. -/
  outCtx : VarCtx

/-- Generate `init x τ (det e)` with a fresh name and well-typed expression. -/
def genInitDet [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (tyDepth depth : Nat) : G GenCmdResult := do
  let name ← genFreshName ctx
  let mty ← genLMonoTy tvars tyDepth
  let e ← genLExpr fctx octx [] tvars [] depth mty
  let xty : Lambda.LTy := .forAll [] mty
  pure ⟨.init ⟨name, ()⟩ xty (.det e) default, (name, mty) :: ctx⟩

/-- Generate `init x τ nondet` with a fresh name. -/
def genInitNondet [Gen G] (tvars : List TyIdentifier)
    (ctx : VarCtx) (tyDepth : Nat) : G GenCmdResult := do
  let name ← genFreshName ctx
  let mty ← genLMonoTy tvars tyDepth
  let xty : Lambda.LTy := .forAll [] mty
  pure ⟨.init ⟨name, ()⟩ xty .nondet default, (name, mty) :: ctx⟩

/-- Generate `set x (det e)` where `x` is an existing variable. -/
def genSetDet [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (_h : ctx.length > 0) : G GenCmdResult := do
  let idx ← choose 0 (ctx.length - 1) (by omega)
  let (name, mty) := ctx.getD idx.down ("", .bool)
  let e ← genLExpr fctx octx [] tvars [] depth mty
  pure ⟨.set ⟨name, ()⟩ (.det e) default, ctx⟩

/-- Generate `set x nondet` where `x` is an existing variable. -/
def genSetNondet [Gen G] (ctx : VarCtx) (_h : ctx.length > 0) : G GenCmdResult := do
  let idx ← choose 0 (ctx.length - 1) (by omega)
  let (name, _mty) := ctx.getD idx.down ("", .bool)
  pure ⟨.set ⟨name, ()⟩ .nondet default, ctx⟩

/-- Generate `assert l e` with a boolean expression. -/
def genAssertCmd [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) : G GenCmdResult := do
  let e ← genLExpr fctx octx [] tvars [] depth .bool
  pure ⟨.assert "" e default, ctx⟩

/-- Generate `assume l e` with a boolean expression. -/
def genAssumeCmd [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) : G GenCmdResult := do
  let e ← genLExpr fctx octx [] tvars [] depth .bool
  pure ⟨.assume "" e default, ctx⟩

/-- Generate `cover l e` with a boolean expression. -/
def genCoverCmd [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) : G GenCmdResult := do
  let e ← genLExpr fctx octx [] tvars [] depth .bool
  pure ⟨.cover "" e default, ctx⟩

-- ── Main command generator ─────────────────────────────────────────────

/-- Generate a well-typed `Cmd Expression` given an input variable context.
    The generated command satisfies `CmdHasTypeA` when interpreted against
    the appropriate `TContext`.

    Commands generated:
    - `init x τ (det e)` — deterministic variable initialization
    - `init x τ nondet`  — non-deterministic variable initialization
    - `set x (det e)`    — deterministic assignment (if ctx has variables)
    - `set x nondet`     — non-deterministic assignment (if ctx has variables)
    - `assert l e`       — assertion with a boolean expression
    - `assume l e`       — assumption with a boolean expression
    - `cover l e`        — coverage check with a boolean expression
-/
def genCmd [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) : G GenCmdResult :=
  let tyDepth := depth
  if h : ctx.length > 0 then
    pick
      (fun () => genInitDet fctx octx tvars ctx tyDepth depth)
      (fun () =>
        pick
          (fun () => genInitNondet tvars ctx tyDepth)
          (fun () =>
            pick
              (fun () => genSetDet fctx octx tvars ctx depth h)
              (fun () =>
                pick
                  (fun () => genSetNondet ctx h)
                  (fun () =>
                    pick
                      (fun () => genAssertCmd fctx octx tvars ctx depth)
                      (fun () =>
                        pick
                          (fun () => genAssumeCmd fctx octx tvars ctx depth)
                          (fun () => genCoverCmd fctx octx tvars ctx depth))))))
  else
    pick
      (fun () => genInitDet fctx octx tvars ctx tyDepth depth)
      (fun () =>
        pick
          (fun () => genInitNondet tvars ctx tyDepth)
          (fun () =>
            pick
              (fun () => genAssertCmd fctx octx tvars ctx depth)
              (fun () =>
                pick
                  (fun () => genAssumeCmd fctx octx tvars ctx depth)
                  (fun () => genCoverCmd fctx octx tvars ctx depth))))

-- ── Sequence generator ──────────────────────────────────────────────────

/-- Generate a sequence of well-typed commands, threading the context through. -/
def genCmds [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) : Nat → G (List (Cmd Expression) × VarCtx)
  | 0 => pure ([], ctx)
  | n + 1 => do
    let ⟨cmd, ctx'⟩ ← genCmd fctx octx tvars ctx depth
    let (rest, ctx'') ← genCmds fctx octx tvars ctx' depth n
    pure (cmd :: rest, ctx'')
