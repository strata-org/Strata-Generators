import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.Languages.Core.CmdEval
import Strata.DL.Imperative.CmdEval
import Strata.DL.Imperative.CmdType
import Strata.Languages.Core.CmdType

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
  ctx.map (fun (n, ty) => s!"{n.name} : {ppType ty}") |> ", ".intercalate |> (s!"[{·}]")

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


/-- Check that the output context matches input + newly init'd variables.
    `Map.insert` appends a fresh binding to the end of the flat map, so the
    newly-defined variables appear after `inCtx` in definition order. -/
def checkContextGrowth (inCtx outCtx : VarCtx) (cmds : List (Cmd Expression)) : Bool :=
  let definedNames : List (Identifier Unit × LMonoTy) := cmds.filterMap fun
    | .init x (.forAll [] mty) _ _ => some (x, mty)
    | _ => none
  (outCtx : List (Identifier Unit × LMonoTy)) ==
    List.append (inCtx : List (Identifier Unit × LMonoTy)) definedNames

-- ── Command runner (using Strata's Cmd.run) ──────────────────────────

/-- Build an `Env` from a `VarCtx` by initializing each variable with a
    default value (integer 0). -/
def envFromVarCtx (ctx : VarCtx) : Core.Env :=
  ctx.foldl (fun env (name, mty) =>
    CmdEval.update env name (.forAll [] mty) (.intConst () 0))
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
    CmdEval.update env name (.forAll [] mty) (.fvar () name (some mty)))
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

-- ── Structural command shrinker ───────────────────────────────────────
--
-- Mirrors the expression shrinker's structural-shrink + rejection-sample
-- strategy (`shrinkLExpr` from `HasTypeAGen.TestSupport`) at the command level.
-- Every candidate is required to remain well-typed via `checkExprTypechecks`,
-- but — as the expression shrinker already allows — a candidate's *type* may
-- change: shrinking `init (x : bool) := (b && c)` toward `init (x : int) := n`
-- keeps a well-typed command, and the declared type is re-derived so it still
-- matches the shrunk RHS.

/-- Structurally smaller candidates for a command, before well-typedness
    filtering. Two families of reduction:

    * **RHS-expression shrinks** — reduce the expression carried by
      `init`/`set` (deterministic RHS only) or the boolean condition of
      `assert`/`assume`/`cover`, using the shared `shrinkLExpr`. For a
      deterministic `init` we re-derive the declared type from the shrunk RHS so
      the result stays well-typed even when the RHS type changes.
    * **Determinism collapse** — replace a deterministic `init`/`set` RHS by
      `.nondet` (havoc), a strictly simpler, always-well-typed command. -/
def shrinkCmdCandidates (c : Cmd Expression) : List (Cmd Expression) :=
  match c with
  | .init x ty (.det ex) md =>
    ((shrinkLExpr ex).filterMap fun ex' =>
      match LExpr.typeCheck (T := LExprParams') [] ex' with
      | some τ' => some (Cmd.init x (.forAll [] τ') (.det ex') md)
      | none => none)
    ++ [Cmd.init x ty .nondet md]
  | .init _ _ .nondet _ => []
  | .set x (.det ex) md =>
    ((fun ex' => Cmd.set x (.det ex') md) <$> shrinkLExpr ex)
    ++ [Cmd.set x .nondet md]
  | .set _ .nondet _ => []
  | .assert l b md => (Cmd.assert l · md) <$> shrinkLExpr b
  | .assume l b md => (Cmd.assume l · md) <$> shrinkLExpr b
  | .cover l b md => (Cmd.cover l · md) <$> shrinkLExpr b

/-- Well-typed structural shrinks of a command: candidate commands whose
    expression sub-terms still typecheck (bool for `assert`/`assume`/`cover`, the
    re-derived declared type for `init`, any type for `set`). -/
def shrinkCmd (c : Cmd Expression) : List (Cmd Expression) :=
  (shrinkCmdCandidates c).filter checkExprTypechecks

/-- The variables a command adds to the ambient context (only `init` defines a
    new variable). Mirrors the `definedNames` computation in `checkContextGrowth`
    so a shrunk command's recomputed output context stays consistent. -/
def cmdDefinedVars (c : Cmd Expression) : List (Identifier Unit × LMonoTy) :=
  match c with
  | .init x (.forAll [] mty) _ _ => [(x, mty)]
  | _ => []

/-- Recompute the output context of a (shrunk) command from its input context:
    the input context extended with any variable the command defines. -/
def cmdOutCtx (inCtx : VarCtx) (c : Cmd Expression) : VarCtx :=
  Map.ofList (List.append (inCtx : List (Identifier Unit × LMonoTy)) (cmdDefinedVars c))

/-- Recompute the output context of a (shrunk) command *sequence*: the input
    context extended with every variable defined along the sequence, in order.
    Mirrors the `definedNames` fold in `checkContextGrowth`, so a shrunk sequence
    satisfies the context-growth property by construction. -/
def cmdsOutCtx (inCtx : VarCtx) (cmds : List (Cmd Expression)) : VarCtx :=
  Map.ofList (List.append (inCtx : List (Identifier Unit × LMonoTy)) (cmds.flatMap cmdDefinedVars))

/-- The standard Core ambient typing context (built-in `Core.Factory` operators +
    `Core.KnownTypes`), used to type-check a whole command *sequence*. Mirrors the
    statement module's `stmtCheckContext`; duplicated here (rather than imported)
    because that module imports *this* one. -/
def cmdSeqCheckContext : LContext CoreLParams :=
  { LContext.default with
    functions := Core.Factory,
    knownTypes := Core.KnownTypes }

/-- Seed a typing environment from a `VarCtx`: every variable in the input context
    is declared (with its monotype) so a command sequence generated under `inCtx`
    is type-checked with those variables already in scope. -/
def seedTyEnv (inCtx : VarCtx) : TEnv Unit :=
  (inCtx : List (Identifier Unit × LMonoTy)).foldl
    (fun e (x, mty) => Core.CmdType.update e x (LTy.forAll [] mty)) TEnv.default

/-- **Scope-threading well-formedness check** for a command *sequence*. Unlike the
    per-command `checkExprTypechecks` (which type-checks each expression in the
    *empty* context and trusts annotated free variables), this runs Strata's own
    `Imperative.Cmds.typeCheck`, which threads a variable context along the
    sequence: an `init` extends scope, a `set`/reference to an *undeclared*
    variable is rejected. Seeded from `inCtx` so pre-declared variables are in
    scope. This is what makes dropping an `init` whose variable is used later a
    rejected shrink, rather than a dangling reference. -/
def cmdsScopeWellFormed (inCtx : VarCtx) (cmds : List (Cmd Expression)) : Bool :=
  match Imperative.Cmds.typeCheck cmdSeqCheckContext (seedTyEnv inCtx) cmds with
  | .ok _ => true
  | .error _ => false

/-- Structural shrinks of a command sequence: drop one command, or replace one
    command by a smaller one (`shrinkCmd`). Every candidate is filtered by the
    whole-sequence scope-threading check `cmdsScopeWellFormed` (seeded from
    `inCtx`), so a candidate stays not just well-typed but well-*formed*: dropping
    an `init` whose variable a later command references is rejected, never
    yielding a dangling variable. (The per-command `shrinkCmd` already keeps each
    replacement's own expression well-typed; the sequence check adds cross-command
    scoping.) -/
def shrinkCmds (inCtx : VarCtx) (cmds : List (Cmd Expression)) : List (List (Cmd Expression)) :=
  (dropEach cmds
   ++ cmds.zipIdx.flatMap (fun (c, i) => (cmds.set i ·) <$> shrinkCmd c)).filter
    (cmdsScopeWellFormed inCtx)

-- ── Generator wrappers ────────────────────────────────────────────────

/-- Generate a single well-typed command in IO, returning the command, the
    input context, and the output context. -/
def genCmdIO (ctx : VarCtx := []) (depth : Nat := 2) : IO (Cmd Expression × VarCtx × VarCtx) := do
  let tvars : List TyIdentifier := []
  let ⟨cmd, ctx'⟩ ← genCmd (G := IO) [] coreMonoOps tvars [] ctx depth
  return (cmd, ctx, ctx')

/-- Generate a sequence of well-typed commands in IO. -/
def genCmdsIO (n : Nat := 5) (ctx : VarCtx := []) (depth : Nat := 2) :
    IO (List (Cmd Expression) × VarCtx × VarCtx) := do
  let tvars : List TyIdentifier := []
  let (cmds, ctx') ← genCmds (G := IO) [] coreMonoOps tvars [] ctx depth n
  return (cmds, ctx, ctx')
