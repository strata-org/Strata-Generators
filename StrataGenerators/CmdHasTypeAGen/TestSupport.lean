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

/-- Build an `Env` from a `VarCtx`, seeding each variable with a *well-typed*
    placeholder value: an annotated free variable `(x : τ)`, which typechecks to
    exactly its declared type `τ`. This contrasts with `envFromVarCtx`, which
    seeds every variable with `intConst 0` regardless of its declared type and
    would therefore start from an ill-typed store for non-`int` variables.
    Used by the store-type-preservation property so that the *starting* store is
    well-typed and any failure is attributable to command evaluation. -/
def envFromVarCtxWellTyped (ctx : VarCtx) : Core.Env :=
  ctx.foldl (fun env (name, mty) =>
    CmdEval.update env ⟨name, ()⟩ (.forAll [] mty) (.fvar () ⟨name, ()⟩ (some mty)))
    Core.Env.init

-- ── Evaluation-based properties ───────────────────────────────────────

/-- After running `set x (det e)`, the variable `x` is still in the store. -/
def checkSetPreservesVar (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  match cmd with
  | .set x _ _ =>
    let env' := Cmd.run (envFromVarCtx ctx) cmd
    env'.error.isNone && (CmdEval.lookup env' x).isSome
  | _ => true

/-- Every variable binding currently in the store typechecks to its declared
    type. Bindings with no declared type are a vacuous pass. -/
def storeWellTyped (E : Core.Env) : Bool :=
  E.exprEnv.state.toSingleMap.all fun (_, (optTy, e)) =>
    match optTy with
    | some τ => LExpr.typeCheck (T := LExprParams') [] e == some τ
    | none => true

/-- **Store type preservation.** Running a command on a well-typed store leaves
    every variable bound to a value that still typechecks at its declared type.
    This is the command-level analogue of expression-level type preservation
    under `eval`.

    We seed the input context with well-typed placeholders (`envFromVarCtxWellTyped`)
    so the starting store is well-typed, then run the command. If the run errors
    (e.g. `cover`, which `Cmd.run` does not support, or a failed `assert`) the
    command never produced a new store, so we treat it as a vacuous pass — this
    deliberately avoids the invalid "commands never error" framing. -/
def checkStoreTypePreservation (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  let env' := Cmd.run (envFromVarCtxWellTyped ctx) cmd
  if env'.error.isNone then storeWellTyped env' else true

/-- **Symbolic/concrete agreement (refinement).** Concrete execution `Cmd.run`
    refines symbolic simulation `Cmd.eval`: whenever the concrete run succeeds
    without error, the symbolic evaluation also succeeds and produces the *same*
    variable store.

    We state the *refinement* direction rather than full equivalence because the
    two evaluators legitimately diverge when concrete execution gets stuck while
    symbolic execution continues:
      • `assert e` with `e` not reducing to a concrete bool: `Cmd.run` errors,
        `Cmd.eval` defers a proof obligation.
      • `assume false`: `Cmd.run` errors, `Cmd.eval` adds a path condition.
      • `cover`: `Cmd.run` errors (unsupported), `Cmd.eval` defers an obligation.
    In every such case concrete *fails*, so the implication is vacuously true and
    we make no false claim. On the agreeing cases (`init`/`set`, `assert`/`assume`
    with a concretely-true condition) both produce identical stores. -/
def checkEvalRunAgreement (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  let σ := envFromVarCtxWellTyped ctx
  let runEnv := Cmd.run σ cmd
  let (_, evalEnv) := Cmd.eval σ cmd
  if runEnv.error.isNone then
    evalEnv.error.isNone &&
      (runEnv.exprEnv.state.toSingleMap == evalEnv.exprEnv.state.toSingleMap)
  else
    true

/-- Classify how a command's condition reduces, for visualization. For
    `assert`/`assume`/`cover` we evaluate the condition in the seeded store and
    report `"true"`, `"false"`, or `"non-concrete"`; other commands are `"n/a"`. -/
def cmdConditionKind (cmd : Cmd Expression) (ctx : VarCtx) : String :=
  match cmd with
  | .assert _ e _ | .assume _ e _ | .cover _ e _ =>
    match CmdEval.denoteBool (CmdEval.eval (envFromVarCtxWellTyped ctx) e) with
    | some true => "true"
    | some false => "false"
    | none => "non-concrete"
  | _ => "n/a"

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
