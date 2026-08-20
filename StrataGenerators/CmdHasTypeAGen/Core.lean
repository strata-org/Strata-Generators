import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import Basalt.Tuning.Attr
import BasaltExamples.ArbString.Def
import Strata.Languages.Core.CmdTypeSpec
import StrataGenerators.HasTypeAGen.Core
import StrataGenerators.FunctionHasTypeAGen.Core

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

/-- The *mutable* sub-context: the entries of `ctx` whose key is **not** among the
    immutable names `immutableVars`. Assignment (`set`) targets are drawn from here, so a
    generated body may freely *read* the immutable names (e.g. a procedure's input
    parameters, which live in the threaded `ctx` for freshness and expression
    typing) but can never *assign* to them — exactly the `modRights` obligation.
    When `immutableVars = []` the mutable context is the whole `ctx`. -/
def VarCtx.writable (immutableVars : List (Identifier Unit)) (ctx : VarCtx) : VarCtx :=
  List.filter (fun p => !immutableVars.contains p.1) ctx

-- ── Fresh name generation ──────────────────────────────────────────────

/-- The length of the longest name occurring in a list of `(identifier, type)`
    pairs (`0` for the empty list). A name strictly longer than this is guaranteed
    not to occur in the list — the length-based freshness argument used by
    `fallbackFreshName` and `indexedFreshName`. -/
def maxNameLen (l : List (Identifier Unit × LMonoTy)) : Nat :=
  (l.map (fun p => p.1.name)).foldl (fun acc nm => max acc nm.length) 0

/-- A fallback name guaranteed to be fresh: a string of `x` characters longer
    than any name in the context. -/
def fallbackFreshName (ctx : VarCtx) : String :=
  String.ofList (List.replicate (ctx.names.foldl (fun acc nm => max acc nm.length) 0 + 1) 'x')

/-- A *family* of names, one per index `i`, all strictly longer than `base`: the
    string of `base + 1 + i` `x` characters. Two properties make this family useful
    where several fresh names are needed at once with no randomness involved:

    * taking `base := maxNameLen l` makes every member fresh for `l` (each is
      strictly longer than every name in `l`);
    * distinct indices give names of distinct lengths, hence distinct names.

    See `outTargets`, which names the caller variables receiving a call's `out`
    results — names the Core spec leaves entirely to the caller. -/
def indexedFreshName (base i : Nat) : String :=
  String.ofList (List.replicate (base + 1 + i) 'x')

/-- Generate a fresh variable name not in `ctx`. Uses `NonEmptyString.arbitrary`
    for randomness (a variable identifier must be non-empty), maps it through
    `dodgeKeyword` so the result is never a reserved Core keyword, and falls back
    to a length-based guarantee when the (dodged) random name collides.

    `dodgeKeyword` is applied *before* the freshness check so that the name we
    test for freshness is exactly the name we return; the fallback is dodged too
    (it is all `x`s, hence never a keyword, so `dodgeKeyword` is the identity on
    it — but this keeps keyword-freedom uniform across both branches). -/
def genFreshName [Gen G] (ctx : VarCtx) : G String := do
  let s ← NonEmptyString.arbitrary
  let s := dodgeKeyword s
  if ctx.isFresh ⟨s, ()⟩ then
    pure s
  else
    pure (dodgeKeyword (fallbackFreshName ctx))

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

/-- Generate `set x (det e)` where `x` is an existing *mutable* variable (its key
    is not among the immutable names `immutableVars`). The target is drawn from
    `ctx.writable immutableVars`, so immutable names are never assigned; the output
    context is the full `ctx`. -/
def genSetDet [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (h : (ctx.writable immutableVars).length > 0) : G GenCmdResult := do
  let (name, mty) ← elements (ctx.writable immutableVars) (by apply List.ne_nil_of_length_pos; assumption)
  let e ← genLExpr fctx octx [] tvars [] depth mty
  pure ⟨.set name (.det e) default, ctx⟩

/-- Generate `set x nondet` where `x` is an existing *mutable* variable. -/
def genSetNondet [Gen G] (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (h : (ctx.writable immutableVars).length > 0) : G GenCmdResult := do
  let (name, _) ← elements (ctx.writable immutableVars) (by apply List.ne_nil_of_length_pos; assumption)
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
    compensate for the structural bias toward `init` in sequences.

    Tagged `@[tunable]`, so those weights are a runtime knob: `genCmd.tuned θ`
    reads each branch's weight from `θ` at the current `depth`. There are two
    sites — the writable-context list (arity 7) and the no-writable-variable list
    (arity 5) — because `set` is only offered when there is something to assign
    to; see `StrataGenerators.TuningProfiles` for the profiles the test suite
    uses and `TuningPrototypes.genCmd_tuned_eq` for the proof that tuning changes
    only the distribution. -/
@[tunable]
def genCmd [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) : G GenCmdResult :=
  let tyDepth := depth
  if h : (ctx.writable immutableVars).length > 0 then
    frequency
      [ (2, fun () => genInitDet fctx octx tvars ctx tyDepth depth),
        (1, fun () => genInitNondet tvars ctx tyDepth),
        (3, fun () => genSetDet fctx octx tvars immutableVars ctx depth h),
        (2, fun () => genSetNondet immutableVars ctx h),
        (2, fun () => genAssertCmd fctx octx tvars ctx depth),
        (2, fun () => genAssumeCmd fctx octx tvars ctx depth),
        (2, fun () => genCoverCmd fctx octx tvars ctx depth) ]
      (by show 0 < 2+1+3+2+2+2+2; omega)
  else
    frequency
      [ (3, fun () => genInitDet fctx octx tvars ctx tyDepth depth),
        (1, fun () => genInitNondet tvars ctx tyDepth),
        (2, fun () => genAssertCmd fctx octx tvars ctx depth),
        (2, fun () => genAssumeCmd fctx octx tvars ctx depth),
        (2, fun () => genCoverCmd fctx octx tvars ctx depth) ]
      (by show 0 < 3+1+2+2+2; omega)

-- ── Sequence generator ──────────────────────────────────────────────────

/-- `genCmds n` generates a length-n sequence of well-typed commands,
    threading the context through. -/
def genCmds [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) :
    Nat → G (List (Cmd Expression) × VarCtx)
  | 0 => pure ([], ctx)
  | n + 1 => do
    let ⟨cmd, ctx'⟩ ← genCmd fctx octx tvars immutableVars ctx depth
    let (rest, ctx'') ← genCmds fctx octx tvars immutableVars ctx' depth n
    pure (cmd :: rest, ctx'')
