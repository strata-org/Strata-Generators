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
# The core definitions of the generator for a well-typed `Cmd`

This file holds the definition of `genCmd`, which is a generator for a well-typed imperative
command that satisfies the relation `CmdHasTypeA`.

The generator gives a `Cmd Expression` value and the output typing context. It uses
`genLExpr` to make a well-typed expression for the right side of a command.
-/

-- ── How the module represents a typing context ─────────────────────────

/-- The form of a typing context that the generator uses. It is a `Map` of Strata whose keys are
    identifiers. Each entry maps a variable identifier `⟨name, ()⟩` to its monotype, because each
    context here is monomorphic and therefore holds only a `forAll [] mty`. The type follows the
    `Map` field of the semantic `TContext`. -/
abbrev VarCtx := Map (Identifier Unit) LMonoTy

/-- The name of each variable in a `VarCtx`. -/
def VarCtx.names (ctx : VarCtx) : List String :=
  ctx.map (fun p => p.1.name)

/-- Maps a `VarCtx`, which is the variable scope of a statement and whose keys are
    `Identifier Unit` values, to the free-variable context `FVarCtx` that `genLExpr` takes and
    whose keys are strings. Each entry `(⟨x, ()⟩, τ)` becomes `(x, τ)`.

    The generators for a command and for a statement give `ctx.toFVarCtx` to each call of
    `genLExpr`, and they do *not* thread a separate `fctx`. A generated expression can therefore
    refer to exactly the variables that are in scope, such as a parameter of the procedure or a
    local variable from an earlier declaration.

    The free-variable context comes from `ctx` at each step, so the invariant for soundness that
    the names of `fctx` are a subset of the names of `ctx` holds *by construction*.
    `toFVarCtx_names` states the equality of the two sets of names. That equality is what
    discharges the freshness premise of the `init` rule, which is
    `freshNamesDisjointFromExprs_toFVarCtx`, when an expression can hold a free variable. -/
def VarCtx.toFVarCtx (ctx : VarCtx) : FVarCtx :=
  ctx.map (fun p => (p.1.name, p.2))

/-- The names of `ctx.toFVarCtx` are the names of `ctx`. -/
@[simp] theorem VarCtx.toFVarCtx_names (ctx : VarCtx) :
    ctx.toFVarCtx.map Prod.fst = ctx.names := by
  simp only [VarCtx.toFVarCtx, VarCtx.names, List.map_map, Function.comp_def]

/-- Looks up a variable identifier in the context. -/
def VarCtx.find? (ctx : VarCtx) (x : Identifier Unit) : Option LMonoTy :=
  Map.find? ctx x

/-- Whether a variable identifier is fresh, which means that the context does not hold it. -/
def VarCtx.isFresh (ctx : VarCtx) (x : Identifier Unit) : Bool :=
  ctx.find? x |>.isNone

/-- The *mutable* part of the context: the entries of `ctx` whose key is **not** in the list of
    immutable names `immutableVars`. The generator draws the target of a `set` from this part. A
    generated body can therefore *read* an immutable name, such as an input parameter of a
    procedure, but it can never *assign* to one. This is the `modRights` obligation. An input
    parameter is in the threaded `ctx` for freshness and for the typing of an expression. When
    `immutableVars` is empty, the mutable part is the whole of `ctx`. -/
def VarCtx.writable (immutableVars : List (Identifier Unit)) (ctx : VarCtx) : VarCtx :=
  List.filter (fun p => !immutableVars.contains p.1) ctx

-- ── How the generator makes a fresh name ───────────────────────────────

/-- The length of the longest name in a list of pairs of an identifier and a type. The result is
    `0` for an empty list. A name that is longer than this length cannot occur in the list, and
    this is the argument from length that `fallbackFreshName` and `indexedFreshName` use. -/
def maxNameLen (l : List (Identifier Unit × LMonoTy)) : Nat :=
  (l.map (fun p => p.1.name)).foldl (fun acc nm => max acc nm.length) 0

/-- A fallback name that is always fresh. It is a string of `x` characters that is longer than each
    name in the context. -/
def fallbackFreshName (ctx : VarCtx) : String :=
  String.ofList (List.replicate (ctx.names.foldl (fun acc nm => max acc nm.length) 0 + 1) 'x')

/-- A *family* of names, one name for each index `i`. Each name is longer than `base`, and it is
    the string of `base + 1 + i` characters `x`. Two properties make this family useful where the
    code needs several fresh names at one time and no randomness:

    * With `base := maxNameLen l`, each member is fresh for `l`, because each member is longer than
      each name in `l`.
    * Two different indices give names of two different lengths, and therefore two different names.

    `outTargets` uses the family. It names the variables of the caller that receive the `out`
    results of a call, and the Core specification leaves those names to the caller. -/
def indexedFreshName (base i : Nat) : String :=
  String.ofList (List.replicate (base + 1 + i) 'x')

/-- Makes a fresh variable name that `ctx` does not hold. The generator draws a random name with
    `genIdentName`, and it falls back to the argument from length when that name is already in the
    context.

    The support of `genIdentName` is exactly the set of legal bare Core identifiers that are not
    reserved keywords, as `mem_support_genIdentName_iff_isId` states. Each name that this generator
    emits is therefore a name that the Core lexer accepts in the position of an identifier, and the
    generator can reach each name that a parsed program can hold.

    The code also applies `dodgeKeyword` to the fallback name. That name holds only the character
    `x`, so it is never a keyword and `dodgeKeyword` is the identity on it. The two branches
    therefore give a name that is not a keyword in the same way. -/
def genFreshName [Gen G] (ctx : VarCtx) : G String := do
  let s ← genIdentName
  if ctx.isFresh ⟨s, ()⟩ then
    pure s
  else
    pure (dodgeKeyword (fallbackFreshName ctx))

-- ── The argument from length, which each generator shares ───────────────

/-- The accumulator of a fold that takes a maximum over a measure `f` never gets smaller. This is
    the general form of the argument from length that `fallbackFreshName`, `fallbackName` and
    `fallbackFreshLabel` all use with `f := String.length`: a name that is longer than each name
    in a list cannot occur in that list. -/
theorem foldl_max_ge_init {α : Type _} (f : α → Nat) (xs : List α) (init : Nat) :
    init ≤ xs.foldl (fun acc x => max acc (f x)) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- The result of a fold that takes a maximum is not less than `f x` for each member `x`. At
    `f := String.length`, this bounds the length of each member. `maxNameLen` carries the bound to
    a list of pairs of an identifier and a type, through `length_le_maxNameLen`. -/
theorem foldl_max_ge_of_mem {α : Type _} (f : α → Nat) (xs : List α) (x : α)
    (h : x ∈ xs) (init : Nat) :
    f x ≤ xs.foldl (fun acc y => max acc (f y)) init := by
  induction xs generalizing init with
  | nil => exact absurd h (by exact List.not_mem_nil)
  | cons hd tl ih =>
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge_init f tl _)
    | tail _ hmem => exact ih hmem _

/-- The length of `indexedFreshName base i` is `base + 1 + i`. This is the one fact that each lemma
    about the family uses: the lemma for freshness, the lemma for injectivity, and the lemma that
    says that no member is a keyword. -/
theorem indexedFreshName_length (base i : Nat) :
    (indexedFreshName base i).length = base + 1 + i := by
  simp [indexedFreshName, String.length_ofList]

-- ── The smaller generators for one command ─────────────────────────────

/-- The result of a draw of one command: the command, and the output context. -/
structure GenCmdResult where
  /-- The generated command. -/
  cmd : Cmd Expression
  /-- The typing context after the command runs. -/
  outCtx : VarCtx

/-- Makes `init x τ (det e)` with a fresh name and a well-typed expression. The initial value `e`
    draws its free variables from the current scope, which is `ctx.toFVarCtx`, so it can refer to
    each variable that is in scope. -/
def genInitDet [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (tyDepth depth : Nat) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let name ← genFreshName ctx
  let mty ← genLMonoTy tvars tyDepth
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth mty
  let xty : Lambda.LTy := .forAll [] mty
  pure ⟨.init ⟨name, ()⟩ xty (.det e) default, ctx.insert ⟨name, ()⟩ mty⟩

/-- Makes `init x τ nondet` with a fresh name. -/
def genInitNondet [Gen G] (tvars : List TyIdentifier)
    (ctx : VarCtx) (tyDepth : Nat) : G GenCmdResult := do
  let name ← genFreshName ctx
  let mty ← genLMonoTy tvars tyDepth
  let xty : Lambda.LTy := .forAll [] mty
  pure ⟨.init ⟨name, ()⟩ xty .nondet default, ctx.insert ⟨name, ()⟩ mty⟩

/-- Makes `set x (det e)`, where `x` is a *mutable* variable that the context holds. The key of
    such a variable is not in the list of immutable names `immutableVars`. The generator draws the
    target from `ctx.writable immutableVars`, so a `set` never assigns to an immutable name. The
    output context is the whole of `ctx`. -/
def genSetDet [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (h : (ctx.writable immutableVars).length > 0) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let (name, mty) ← elements (ctx.writable immutableVars) (by apply List.ne_nil_of_length_pos; assumption)
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth mty
  pure ⟨.set name (.det e) default, ctx⟩

/-- Makes `set x nondet`, where `x` is a *mutable* variable that the context holds. -/
def genSetNondet [Gen G] (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (h : (ctx.writable immutableVars).length > 0) : G GenCmdResult := do
  let (name, _) ← elements (ctx.writable immutableVars) (by apply List.ne_nil_of_length_pos; assumption)
  pure ⟨.set name .nondet default, ctx⟩

/-- Makes `assert l e` with a Boolean expression. The label `l` comes from `genIdentName`, so it is
    a legal Core identifier and not a keyword. The typing rule constrains only the expression.

    `genIdentName` gives the label, and not `String.arbitrary`. The support of `String.arbitrary`
    holds only an alphanumeric string, so it cannot reach the label that the parser makes for an
    `assert` with no label, such as `assert_0`, which `translateLabeledCheck` builds. It also holds
    `""`, and the printer writes an empty label as the degenerate form `[||]`. -/
def genAssertCmd [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let l ← genIdentName
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth .bool
  pure ⟨.assert l e default, ctx⟩

/-- Makes `assume l e` with a Boolean expression. The label `l` comes from `genIdentName`, and the
    typing rule ignores it, as for an `assert`. -/
def genAssumeCmd [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let l ← genIdentName
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth .bool
  pure ⟨.assume l e default, ctx⟩

/-- Makes `cover l e` with a Boolean expression. The label `l` comes from `genIdentName`, and the
    typing rule ignores it, as for an `assert`. -/
def genCoverCmd [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (ctx : VarCtx) (depth : Nat) (pctx : PolyOpCtx := []) : G GenCmdResult := do
  let l ← genIdentName
  let e ← genLExpr ctx.toFVarCtx octx pctx tvars [] depth .bool
  pure ⟨.cover l e default, ctx⟩

-- ── The main generator for a command ───────────────────────────────────

/-- Makes a well-typed `Cmd Expression` from an input variable context. The command satisfies
    `CmdHasTypeA` against the matching `TContext`.

    The generator can make these commands:
    - `init x τ (det e)`, which is a deterministic first value for a variable.
    - `init x τ nondet`, which is a nondeterministic first value for a variable.
    - `set x (det e)`, which is a deterministic assignment. It needs a variable in the context.
    - `set x nondet`, which is a nondeterministic assignment. It needs a variable in the context.
    - `assert l e`, which is an assertion with a Boolean expression.
    - `assume l e`, which is an assumption with a Boolean expression.
    - `cover l e`, which is a check for coverage with a Boolean expression.

    The generator uses `frequency`, so the distribution over the kinds of command is more uniform.
    When the context is not empty, a `set` command gets a higher weight, because the structure of a
    sequence otherwise favours an `init`.

    Tagged `@[tunable]`, so every weight is a runtime knob. `genCmd.tuned θ` reads each branch's
    weight from `θ` at the current `depth`. There are two sites, because the generator offers `set`
    only when the context holds something to assign to. The writable-context list has arity 7, and
    the list for a context with no writable variable has arity 5.
    `StrataGenerators.TuningProfiles` holds the profiles that the suite uses. -/
@[tunable]
def genCmd [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : G GenCmdResult :=
  let tyDepth := depth
  if h : (ctx.writable immutableVars).length > 0 then
    frequency
      [ (2, fun () => genInitDet octx tvars ctx tyDepth depth pctx),
        (1, fun () => genInitNondet tvars ctx tyDepth),
        (3, fun () => genSetDet octx tvars immutableVars ctx depth h pctx),
        (2, fun () => genSetNondet immutableVars ctx h),
        (2, fun () => genAssertCmd octx tvars ctx depth pctx),
        (2, fun () => genAssumeCmd octx tvars ctx depth pctx),
        (2, fun () => genCoverCmd octx tvars ctx depth pctx) ]
      (by show 0 < 2+1+3+2+2+2+2; omega)
  else
    frequency
      [ (3, fun () => genInitDet octx tvars ctx tyDepth depth pctx),
        (1, fun () => genInitNondet tvars ctx tyDepth),
        (2, fun () => genAssertCmd octx tvars ctx depth pctx),
        (2, fun () => genAssumeCmd octx tvars ctx depth pctx),
        (2, fun () => genCoverCmd octx tvars ctx depth pctx) ]
      (by show 0 < 3+1+2+2+2; omega)

-- ── The generator for a sequence of commands ────────────────────────────

/-- `genCmds n` makes a sequence of `n` well-typed commands. It threads the context through the
    sequence. -/
def genCmds [Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) :
    Nat → G (List (Cmd Expression) × VarCtx)
  | 0 => pure ([], ctx)
  | n + 1 => do
    let ⟨cmd, ctx'⟩ ← genCmd octx tvars immutableVars ctx depth
    let (rest, ctx'') ← genCmds octx tvars immutableVars ctx' depth n
    pure (cmd :: rest, ctx'')
