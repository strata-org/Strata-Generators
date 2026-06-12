import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.DL.Lambda.Denote.LExprAnnotated

open Lambda RandomChoice Core Imperative

/-!
# Test support for the `CmdHasTypeAGen` generator

Provides shared utilities for property-based testing of `genCmd` and `genCmds`:
- Pretty-printing for commands and contexts
- Generator wrappers for IO and Plausible.Gen
- Decidable properties about generated commands
-/

-- ── Pretty-printing ────────────────────────────────────────────────────

/-- Pretty-print a `VarCtx` as a comma-separated list of `name : type`. -/
def ppVarCtx (ctx : VarCtx) : String :=
  ctx.map (fun (n, ty) => s!"{n} : {ppType ty}") |> ", ".intercalate |> (s!"[{·}]")

/-- Pretty-print an `LTy` (polytype). Monomorphic types `forAll [] mty` print
    as just the monotype; polymorphic types show the quantifier. -/
private def ppLTy : Lambda.LTy → String
  | .forAll [] mty => ppType mty
  | .forAll tvs mty => s!"∀{tvs}. {ppType mty}"

/-- Pretty-print a command using Strata's layout (init/set/havoc/assert/assume/cover)
    with the human-readable type/expression pretty-printers from `TestSupport`. -/
def ppCmd (cmd : Cmd Expression) : String :=
  match cmd with
  | .init x xty (.det e) _ => s!"init ({x.name} : {ppLTy xty}) := {ppExpr e}"
  | .init x xty .nondet _ => s!"init ({x.name} : {ppLTy xty})"
  | .set x (.det e) _ => s!"{x.name} := {ppExpr e}"
  | .set x .nondet _ => s!"havoc {x.name}"
  | .assert l e _ => s!"assert [{l}] {ppExpr e}"
  | .assume l e _ => s!"assume [{l}] {ppExpr e}"
  | .cover l e _ => s!"cover [{l}] {ppExpr e}"

-- ── Decidable properties ──────────────────────────────────────────────

/-- For `init x τ (det e)`, check that `x ∉ vars(e)`.
    Returns `true` for all non-init commands. -/
def checkInitFreshNotInRhs (cmd : Cmd Expression) : Bool :=
  match cmd with
  | .init x _ (.det e) _ => !(x ∈ HasVarsPure.getVars (P := Expression) e)
  | _ => true

/-- Check that the expression sub-term in a command typechecks.
    For `init` with a declared type, checks expression matches that type.
    For `assert`/`assume`/`cover`, checks expression is boolean.
    For `set`, checks the expression is well-typed (has some type). -/
def checkExprTypechecks (cmd : Cmd Expression) : Bool :=
  match cmd with
  | .init _ (.forAll [] mty) (.det e) _ =>
    LExpr.typeCheck (T := LExprParams') [] e == some mty
  | .set _ (.det e) _ =>
    (LExpr.typeCheck (T := LExprParams') [] e).isSome
  | .assert _ e _ => LExpr.typeCheck (T := LExprParams') [] e == some .bool
  | .assume _ e _ => LExpr.typeCheck (T := LExprParams') [] e == some .bool
  | .cover _ e _ => LExpr.typeCheck (T := LExprParams') [] e == some .bool
  | _ => true


/-- Check that the output context matches input + newly init'd variables. -/
def checkContextGrowth (inCtx outCtx : VarCtx) (cmds : List (Cmd Expression)) : Bool :=
  let definedNames := cmds.filterMap fun
    | .init x (.forAll [] mty) _ _ => some (x.name, mty)
    | _ => none
  outCtx == definedNames.reverse ++ inCtx

-- ── Lightweight command runner ─────────────────────────────────────────
--
-- We redefine a minimal command executor here rather than importing
-- `Strata.Languages.Core.CmdEval` (which provides `Cmd.run`) because:
--
-- 1. `CmdEval` imports `Env`, which imports `Factory.lean`.
-- 2. `Factory.lean` uses `native_decide` to prove that all operator names
--    are unique. This requires the full definition of `CoreLParams` (and
--    its transitive dependencies) to be visible to the native compiler via
--    `public meta import`.
-- 3. Our project (`strata-generators`) uses Lean `v4.30.0-rc2` while the
--    Strata dependency uses `v4.29.1`. Between these versions, `native_decide`
--    became stricter about meta visibility, causing `Factory.lean` to fail
--    to build in our environment.
--
-- Rather than pin our toolchain or fight the meta import chain, we inline
-- the ~30 lines of `Cmd.run`'s logic here, using our already-working
-- expression evaluator (`eval` from `IntBoolFactory` in `TestSupport`).
-- The store is a simple association list mirroring `SemanticStore P`
-- (a function `P.Ident → Option P.Expr`).

/-- A concrete store mapping variable identifiers to expression values.
    Mirrors `Imperative.SemanticStore Expression` but as a simple assoc list. -/
abbrev CmdStore := List (Identifier Unit × Expression.Expr)

/-- Result of running a command: either an updated store, or an error. -/
inductive RunResult where
  | ok (store : CmdStore)
  | error (msg : String)

/-- Look up a variable in the store. -/
def CmdStore.lookup (store : CmdStore) (x : Identifier Unit) : Option Expression.Expr :=
  match store with
  | [] => none
  | (y, e) :: rest => if x == y then some e else CmdStore.lookup rest x

/-- Update an existing variable in the store. Returns `none` if not found. -/
def CmdStore.update (store : CmdStore) (x : Identifier Unit) (e : Expression.Expr) :
    Option CmdStore :=
  match store with
  | [] => none
  | (y, v) :: rest =>
    if x == y then some ((y, e) :: rest)
    else (CmdStore.update rest x e).map ((y, v) :: ·)

/-- Run a single command against a store. Mirrors `Imperative.Cmd.run` from
    `Strata/DL/Imperative/CmdEval.lean` but uses our `IntBoolFactory`-based
    evaluator for expression reduction.
    Note: we don't check freshness for `init` because the generator can produce
    contexts with duplicate variable names (the typing rule `init_det` enforces
    freshness at the type level via `Γ.find? x = none`, but our flat `VarCtx`
    tracks all historical bindings). -/
def runCmd (store : CmdStore) (cmd : Cmd Expression) : RunResult :=
  match cmd with
  | .init x _ eOrNd _ =>
    match eOrNd with
    | .det e =>
      let v := eval 100 e
      .ok ((x, v) :: store)
    | .nondet =>
      .ok ((x, LExpr.intConst () 0) :: store)
  | .set x eOrNd _ =>
    match store.lookup x with
    | none => .error s!"set: variable {x.name} not found"
    | some _ =>
      match eOrNd with
      | .det e =>
        let v := eval 100 e
        match store.update x v with
        | some store' => .ok store'
        | none => .error s!"set: update failed for {x.name}"
      | .nondet =>
        match store.update x (.intConst () 0) with
        | some store' => .ok store'
        | none => .error s!"set: update failed for {x.name}"
  | .assert _ _ _ => .ok store
  | .assume _ _ _ => .ok store
  | .cover _ _ _ => .ok store

/-- Run a sequence of commands, threading the store through. -/
def runCmds (store : CmdStore) : List (Cmd Expression) → RunResult
  | [] => .ok store
  | cmd :: rest =>
    match runCmd store cmd with
    | .ok store' => runCmds store' rest
    | .error msg => .error msg

/-- Build a `CmdStore` from a `VarCtx` by giving each variable a default
    value (integer 0). This ensures all context variables are "defined" so
    that `set` commands can find their targets. -/
def storeFromVarCtx (ctx : VarCtx) : CmdStore :=
  ctx.map fun (name, _) => (⟨name, ()⟩, LExpr.intConst () 0)

-- ── Evaluation-based properties ───────────────────────────────────────

/-- Running a generated command in a well-formed store produces no error. -/
def checkCmdRunNoError (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  match runCmd (storeFromVarCtx ctx) cmd with
  | .ok _ => true
  | .error _ => false

/-- Running a generated command sequence produces no error. -/
def checkCmdsRunNoError (cmds : List (Cmd Expression)) (inCtx : VarCtx) : Bool :=
  match runCmds (storeFromVarCtx inCtx) cmds with
  | .ok _ => true
  | .error _ => false


/-- After running `set x (det e)`, the variable `x` is still in the store. -/
def checkSetPreservesVar (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  match cmd with
  | .set x _ _ =>
    match runCmd (storeFromVarCtx ctx) cmd with
    | .ok store' => (store'.lookup x).isSome
    | .error _ => false
  | _ => true

-- ── Generator wrappers ────────────────────────────────────────────────

/-- Generate a single well-typed command in IO, returning the command, the
    input context, and the output context. -/
def genCmdIO (ctx : VarCtx := []) (depth : Nat := 2) : IO (Cmd Expression × VarCtx × VarCtx) := do
  let tvars : List TyIdentifier := []
  let ⟨cmd, ctx'⟩ ← genCmd (G := IO) [] coreOpCtx tvars ctx depth
  return (cmd, ctx, ctx')

/-- Generate a sequence of well-typed commands in IO. -/
def genCmdsIO (n : Nat := 5) (ctx : VarCtx := []) (depth : Nat := 2) :
    IO (List (Cmd Expression) × VarCtx × VarCtx) := do
  let tvars : List TyIdentifier := []
  let (cmds, ctx') ← genCmds (G := IO) [] coreOpCtx tvars ctx depth n
  return (cmds, ctx, ctx')
