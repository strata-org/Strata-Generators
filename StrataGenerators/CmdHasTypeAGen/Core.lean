import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
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

/-- Project a statement-level variable scope `VarCtx` (keyed by `Identifier Unit`)
    down to the expression-level free-variable context `FVarCtx` (keyed by `String`)
    that `genLExpr` consumes: each entry `(⟨x, ()⟩, τ)` becomes `(x, τ)`.

    The command/statement generators feed `ctx.toFVarCtx` — *not* a separately
    threaded `fctx` — into every `genLExpr` call, so a generated expression may
    reference exactly the variables currently in scope (procedure parameters,
    earlier-declared locals). Deriving the free-var context from `ctx` at each step
    makes the soundness invariant `fctx.names ⊆ ctx.names` hold *by construction*
    (`toFVarCtx_names`: `ctx.toFVarCtx.names = ctx.names`), which is what discharges
    the `init` rule's freshness premise (`freshNamesDisjointFromExprs_toFVarCtx`)
    once expressions may contain free variables. -/
def VarCtx.toFVarCtx (ctx : VarCtx) : FVarCtx :=
  ctx.map (fun p => (p.1.name, p.2))

/-- The names of `ctx.toFVarCtx` are exactly the names of `ctx`. -/
@[simp] theorem VarCtx.toFVarCtx_names (ctx : VarCtx) :
    ctx.toFVarCtx.map Prod.fst = ctx.names := by
  simp only [VarCtx.toFVarCtx, VarCtx.names, List.map_map, Function.comp_def]

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

-- ── Length-based freshness, shared across generators ────────────────────

/-- The foldl-max accumulator over an arbitrary measure `f` is monotonically
    non-decreasing. The generic core of the length-based freshness argument that
    `fallbackFreshName` / `fallbackName` / `fallbackFreshLabel` all rest on
    (with `f := String.length`): a name strictly longer than every name in a
    list cannot occur in it. -/
theorem foldl_max_ge_init {α : Type _} (f : α → Nat) (xs : List α) (init : Nat) :
    init ≤ xs.foldl (fun acc x => max acc (f x)) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- The foldl-max result is at least `f x` for any member `x`. Specialized to
    `f := String.length` this bounds the length of every member; `maxNameLen`
    lifts it to `(identifier, type)` lists via `length_le_maxNameLen`. -/
theorem foldl_max_ge_of_mem {α : Type _} (f : α → Nat) (xs : List α) (x : α)
    (h : x ∈ xs) (init : Nat) :
    f x ≤ xs.foldl (fun acc y => max acc (f y)) init := by
  induction xs generalizing init with
  | nil => exact absurd h (by exact List.not_mem_nil)
  | cons hd tl ih =>
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge_init f tl _)
    | tail _ hmem => exact ih hmem _

/-- `indexedFreshName base i` has length `base + 1 + i` — the single fact the
    freshness, injectivity, and keyword-freedom lemmas built on the family all
    rest on. -/
theorem indexedFreshName_length (base i : Nat) :
    (indexedFreshName base i).length = base + 1 + i := by
  simp [indexedFreshName, String.length_ofList]

-- ── Command sub-generators ─────────────────────────────────────────────

/-- The result of generating a command: the command itself and the output context. -/
structure GenCmdResult where
  /-- The generated command. -/
  cmd : Cmd Expression
  /-- The output typing context after executing the command. -/
  outCtx : VarCtx

/-- Generate `init x τ (det e)` with a fresh name and well-typed expression. The
    initializer `e` draws its free variables from the current scope
    (`ctx.toFVarCtx`), so it may reference any in-scope variable. -/
def genInitDet [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (tyDepth depth : Nat) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let name ← genFreshName ctx
  let mty ← genLMonoTy tvars tyDepth
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth mty
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
def genSetDet [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (h : (ctx.writable immutableVars).length > 0) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let (name, mty) ← elements (ctx.writable immutableVars) (by apply List.ne_nil_of_length_pos; assumption)
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth mty
  pure ⟨.set name (.det e) default, ctx⟩

/-- Generate `set x nondet` where `x` is an existing *mutable* variable. -/
def genSetNondet [Gen G] (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (h : (ctx.writable immutableVars).length > 0) : G GenCmdResult := do
  let (name, _) ← elements (ctx.writable immutableVars) (by apply List.ne_nil_of_length_pos; assumption)
  pure ⟨.set name .nondet default, ctx⟩

/-- Generate `assert l e` with a boolean expression. The label `l` is sampled via
    `String.arbitrary` (its typing rule constrains only the expression), so the
    generator reaches every alphanumeric label rather than only `""`. -/
def genAssertCmd [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let l ← String.arbitrary
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth .bool
  pure ⟨.assert l e default, ctx⟩

/-- Generate `assume l e` with a boolean expression. The label `l` is sampled via
    `String.arbitrary` (typing-irrelevant, as for `assert`). -/
def genAssumeCmd [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let l ← String.arbitrary
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth .bool
  pure ⟨.assume l e default, ctx⟩

/-- Generate `cover l e` with a boolean expression. The label `l` is sampled via
    `String.arbitrary` (typing-irrelevant, as for `assert`). -/
def genCoverCmd [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let l ← String.arbitrary
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth .bool
  pure ⟨.cover l e default, ctx⟩

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
def genCmd [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : G GenCmdResult :=
  let tyDepth := depth
  if h : (ctx.writable immutableVars).length > 0 then
    let gs : List (Nat × (Unit → G GenCmdResult)) :=
      [ (2, fun () => genInitDet octx tvars ctx tyDepth depth pctx),
        (1, fun () => genInitNondet tvars ctx tyDepth),
        (3, fun () => genSetDet octx tvars immutableVars ctx depth h pctx),
        (2, fun () => genSetNondet immutableVars ctx h),
        (2, fun () => genAssertCmd octx tvars ctx depth pctx),
        (2, fun () => genAssumeCmd octx tvars ctx depth pctx),
        (2, fun () => genCoverCmd octx tvars ctx depth pctx) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 2+1+3+2+2+2+2; omega
    frequency gs hw
  else
    let gs : List (Nat × (Unit → G GenCmdResult)) :=
      [ (3, fun () => genInitDet octx tvars ctx tyDepth depth pctx),
        (1, fun () => genInitNondet tvars ctx tyDepth),
        (2, fun () => genAssertCmd octx tvars ctx depth pctx),
        (2, fun () => genAssumeCmd octx tvars ctx depth pctx),
        (2, fun () => genCoverCmd octx tvars ctx depth pctx) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 3+1+2+2+2; omega
    frequency gs hw

-- ── Sequence generator ──────────────────────────────────────────────────

/-- `genCmds n` generates a length-n sequence of well-typed commands,
    threading the context through. -/
def genCmds [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) :
    Nat → G (List (Cmd Expression) × VarCtx)
  | 0 => pure ([], ctx)
  | n + 1 => do
    let ⟨cmd, ctx'⟩ ← genCmd octx tvars immutableVars ctx depth
    let (rest, ctx'') ← genCmds octx tvars immutableVars ctx' depth n
    pure (cmd :: rest, ctx'')
