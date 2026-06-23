import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.Languages.Core.CmdEval
import Strata.DL.Imperative.CmdEval

open Lambda RandomChoice Core Core.CmdEval Imperative

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

-- ── Command runner (using Strata's Cmd.run) ──────────────────────────

/-- Build an `Env` from a `VarCtx` by initializing each variable with a
    default value (integer 0). -/
def envFromVarCtx (ctx : VarCtx) : Core.Env :=
  ctx.foldl (fun env (name, mty) =>
    CmdEval.update env ⟨name, ()⟩ (.forAll [] mty) (.intConst () 0))
    Core.Env.init

-- ── Evaluation-based properties ───────────────────────────────────────

/-- Running a generated command in a well-formed store produces no error. -/
def checkCmdRunNoError (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  let env' := Cmd.run (envFromVarCtx ctx) cmd
  env'.error.isNone

/-- Running a generated command sequence produces no error. -/
def checkCmdsRunNoError (cmds : List (Cmd Expression)) (inCtx : VarCtx) : Bool :=
  let env' := Cmds.run (envFromVarCtx inCtx) cmds
  env'.error.isNone

/-- After running `set x (det e)`, the variable `x` is still in the store. -/
def checkSetPreservesVar (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  match cmd with
  | .set x _ _ =>
    let env' := Cmd.run (envFromVarCtx ctx) cmd
    env'.error.isNone && (CmdEval.lookup env' x).isSome
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
