import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import BasaltExamples.ArbString.Def
import Strata.Languages.Core.CmdTypeSpec
import StrataGenerators.HasTypeAGen.Core

open Lambda RandomChoice Core Imperative ArbString

/-!
# Core generator definitions for well-typed `Cmd`s

This file contains the canonical definition of `genCmd`, a generator of
well-typed imperative commands satisfying the `CmdHasTypeA` relation.

The generator produces `Cmd Expression` values along with the output typing
context, using `genLExpr` from `HasTypeAGen/Core.lean` to generate well-typed
expressions for the right-hand sides of commands.
-/

-- ── Typing context representation ──────────────────────────────────────

/-- A representation of the typing context suitable for the generator, using
    Strata's `Map` keyed by identifier. Each entry maps a variable identifier
    `⟨name, ()⟩` to its monotype (we only deal with monomorphic contexts, i.e.
    `forAll [] mty`), mirroring the `Map` field of the semantic `TContext`. -/
abbrev VarCtx := Map (Identifier Unit) LMonoTy

/-- Extract all variable names from a `VarCtx`. -/
def VarCtx.names (ctx : VarCtx) : List String :=
  ctx.map (fun p => p.1.name)

/-- Look up a variable identifier in the context. -/
def VarCtx.find? (ctx : VarCtx) (x : Identifier Unit) : Option LMonoTy :=
  Map.find? ctx x

/-- Check if a variable identifier is fresh (not in the context). -/
def VarCtx.isFresh (ctx : VarCtx) (x : Identifier Unit) : Bool :=
  ctx.find? x |>.isNone

-- ── Fresh name generation ──────────────────────────────────────────────

/-- A fallback name guaranteed to be fresh: a string of `x` characters longer
    than any name in the context. -/
def fallbackFreshName (ctx : VarCtx) : String :=
  String.ofList (List.replicate (ctx.names.foldl (fun acc nm => max acc nm.length) 0 + 1) 'x')

/-- Generate a fresh variable name not in `ctx`. Uses `NonEmptyString.arbitrary`
    for randomness (a variable identifier must be non-empty) and falls back to a
    length-based guarantee when the random name collides. -/
def genFreshName [Gen G] (ctx : VarCtx) : G String := do
  let s ← NonEmptyString.arbitrary
  if ctx.isFresh ⟨s, ()⟩ then
    pure s
  else
    pure (fallbackFreshName ctx)

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
  pure ⟨.init ⟨name, ()⟩ xty (.det e) default, ctx.insert ⟨name, ()⟩ mty⟩

/-- Generate `init x τ nondet` with a fresh name. -/
def genInitNondet [Gen G] (tvars : List TyIdentifier)
    (ctx : VarCtx) (tyDepth : Nat) : G GenCmdResult := do
  let name ← genFreshName ctx
  let mty ← genLMonoTy tvars tyDepth
  let xty : Lambda.LTy := .forAll [] mty
  pure ⟨.init ⟨name, ()⟩ xty .nondet default, ctx.insert ⟨name, ()⟩ mty⟩

/-- Generate `set x (det e)` where `x` is an existing variable. -/
def genSetDet [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (h : ctx.length > 0) : G GenCmdResult := do
  let (name, mty) ← elements ctx (by apply List.ne_nil_of_length_pos; assumption)
  let e ← genLExpr fctx octx [] tvars [] depth mty
  pure ⟨.set name (.det e) default, ctx⟩

/-- Generate `set x nondet` where `x` is an existing variable. -/
def genSetNondet [Gen G] (ctx : VarCtx) (h : ctx.length > 0) : G GenCmdResult := do
  let (name, _) ← elements ctx (by apply List.ne_nil_of_length_pos; assumption)
  pure ⟨.set name .nondet default, ctx⟩

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

    Uses `frequency` for more uniform distribution across command kinds.
    When the context is non-empty, `set` commands get higher weight to
    compensate for the structural bias toward `init` in sequences. -/
def genCmd [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) : G GenCmdResult :=
  let tyDepth := depth
  if h : ctx.length > 0 then
    let gs : List (Nat × (Unit → G GenCmdResult)) :=
      [ (2, fun () => genInitDet fctx octx tvars ctx tyDepth depth),
        (1, fun () => genInitNondet tvars ctx tyDepth),
        (3, fun () => genSetDet fctx octx tvars ctx depth h),
        (2, fun () => genSetNondet ctx h),
        (2, fun () => genAssertCmd fctx octx tvars ctx depth),
        (2, fun () => genAssumeCmd fctx octx tvars ctx depth),
        (2, fun () => genCoverCmd fctx octx tvars ctx depth) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 2+1+3+2+2+2+2; omega
    frequency gs hw
  else
    let gs : List (Nat × (Unit → G GenCmdResult)) :=
      [ (3, fun () => genInitDet fctx octx tvars ctx tyDepth depth),
        (1, fun () => genInitNondet tvars ctx tyDepth),
        (2, fun () => genAssertCmd fctx octx tvars ctx depth),
        (2, fun () => genAssumeCmd fctx octx tvars ctx depth),
        (2, fun () => genCoverCmd fctx octx tvars ctx depth) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 3+1+2+2+2; omega
    frequency gs hw

-- ── Sequence generator ──────────────────────────────────────────────────

/-- `genCmds n` generates a length-n sequence of well-typed commands,
    threading the context through. -/
def genCmds [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) : Nat → G (List (Cmd Expression) × VarCtx)
  | 0 => pure ([], ctx)
  | n + 1 => do
    let ⟨cmd, ctx'⟩ ← genCmd fctx octx tvars ctx depth
    let (rest, ctx'') ← genCmds fctx octx tvars ctx' depth n
    pure (cmd :: rest, ctx'')
