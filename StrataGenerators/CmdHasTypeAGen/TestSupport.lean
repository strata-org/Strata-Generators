import StrataGenerators.CmdHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.Languages.Core.CmdEval
import Strata.DL.Imperative.CmdEval
import Strata.DL.Imperative.CmdType
import Strata.Languages.Core.CmdType

open Lambda RandomChoice Core Core.CmdEval Imperative

/-!
# The test support for the `CmdHasTypeAGen` generator

This module holds the shared functions for the property-based tests of `genCmd` and
`genCmds`:
- the functions that print a command and a context;
- the wrappers that run a generator in `IO` and in `Plausible.Gen`;
- the decidable properties of a generated command.
-/

-- ── The functions that print ───────────────────────────────────────────

/-- Prints a `VarCtx` as a list of entries of the form `name : type`, with a comma between two
    entries. -/
def ppVarCtx (ctx : VarCtx) : String :=
  ctx.map (fun (n, ty) => s!"{n.name} : {ppType ty}") |> ", ".intercalate |> (s!"[{·}]")

/-- Prints an `LTy`, which is a polytype. A monomorphic type `forAll [] mty` prints as the monotype
    alone, and a polymorphic type prints with its quantifier. -/
private def ppLTy : Lambda.LTy → String
  | .forAll [] mty => ppType mty
  | .forAll tvs mty => s!"∀{tvs}. {ppType mty}"

/-- Prints a command in the layout of Strata, which covers `init`, `set`, `havoc`, `assert`,
    `assume` and `cover`. The function uses the printers for a type and for an expression from
    `TestSupport`, which a person can read. -/
def ppCmd (cmd : Cmd Expression) : String :=
  match cmd with
  | .init x xty (.det e) _ => s!"init ({x.name} : {ppLTy xty}) := {ppExpr e}"
  | .init x xty .nondet _ => s!"init ({x.name} : {ppLTy xty})"
  | .set x (.det e) _ => s!"{x.name} := {ppExpr e}"
  | .set x .nondet _ => s!"havoc {x.name}"
  | .assert l e _ => s!"assert [{l}] {ppExpr e}"
  | .assume l e _ => s!"assume [{l}] {ppExpr e}"
  | .cover l e _ => s!"cover [{l}] {ppExpr e}"

-- ── The decidable properties ──────────────────────────────────────────

/-- For an `init x τ (det e)`, whether `x` is not a variable of `e`. The result is `true` for each
    command that is not an `init`. -/
def checkInitFreshNotInRhs (cmd : Cmd Expression) : Bool :=
  match cmd with
  | .init x _ (.det e) _ => !(x ∈ HasFvars.getFvars (P := Expression) e)
  | _ => true

/-- Whether the expression inside a command typechecks. For an `init` that declares a type, the
    check tests that the expression has that type. For an `assert`, an `assume` and a `cover`, it
    tests that the expression is Boolean. For a `set`, it tests that the expression is well-typed
    and therefore has some type. -/
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


/-- Whether the output context equals the input context and the variables that an `init` added.
    `Map.insert` adds a fresh binding to the end of a flat map, so a new variable comes after the
    entries of `inCtx`, in the order of the declarations. -/
def checkContextGrowth (inCtx outCtx : VarCtx) (cmds : List (Cmd Expression)) : Bool :=
  let definedNames : List (Identifier Unit × LMonoTy) := cmds.filterMap fun
    | .init x (.forAll [] mty) _ _ => some (x, mty)
    | _ => none
  (outCtx : List (Identifier Unit × LMonoTy)) ==
    List.append (inCtx : List (Identifier Unit × LMonoTy)) definedNames

-- ── How the module runs a command, with `Cmd.run` of Strata ───────────

/-- Builds an `Env` from a `VarCtx`. Each variable gets the default value, which is the integer
    0. -/
def envFromVarCtx (ctx : VarCtx) : Core.Env :=
  ctx.foldl (fun env (name, mty) =>
    CmdEval.update env name (.forAll [] mty) (.intConst () 0))
    Core.Env.init

/-- Builds an `Env` from a `VarCtx`. Each variable gets a *well-typed* placeholder value, which is a
    free variable with an annotation, `(x : τ)`, and that value typechecks at the declared type `τ`.

    `envFromVarCtx` is different. It gives each variable the value `intConst 0` whatever its
    declared type is, and the store is therefore ill-typed for a variable whose type is not `int`.

    The property for the preservation of the types in the store uses this function, so the store at
    the *start* is well-typed and a failure therefore comes from the evaluation of the command. -/
def envFromVarCtxWellTyped (ctx : VarCtx) : Core.Env :=
  ctx.foldl (fun env (name, mty) =>
    CmdEval.update env name (.forAll [] mty) (.fvar () name (some mty)))
    Core.Env.init

-- ── The properties that use evaluation ────────────────────────────────

/-- After a run of `set x (det e)`, the store still holds the variable `x`. -/
def checkSetPreservesVar (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  match cmd with
  | .set x _ _ =>
    let env' := Cmd.run (envFromVarCtx ctx) cmd
    env'.error.isNone && (CmdEval.lookup env' x).isSome
  | _ => true

/-- Each variable binding in the store typechecks at its declared type. A binding with no declared
    type is a vacuous pass. -/
def storeWellTyped (E : Core.Env) : Bool :=
  E.exprEnv.state.toSingleMap.all fun (_, (optTy, e)) =>
    match optTy with
    | some τ => LExpr.typeCheck (T := LExprParams') [] e == some τ
    | none => true

/-- **A command keeps the types in the store.** A run of a command on a well-typed store leaves each
    variable bound to a value that still typechecks at its declared type. This claim is the form of
    type preservation under `eval` for a command, and not for an expression.

    The check gives the input context well-typed placeholder values with
    `envFromVarCtxWellTyped`, so the store at the start is well-typed. It then runs the command. If
    the run gives an error, then the command made no new store and the check is a vacuous pass. A
    `cover` gives an error, because `Cmd.run` does not support it, and an `assert` that does not
    hold also gives an error. This form avoids the wrong claim that a command never gives an
    error. -/
def checkStoreTypePreservation (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  let env' := Cmd.run (envFromVarCtxWellTyped ctx) cmd
  if env'.error.isNone then storeWellTyped env' else true

/-- **Symbolic and concrete evaluation agree, as a refinement.** Concrete execution with `Cmd.run`
    refines symbolic simulation with `Cmd.eval`: when the concrete run succeeds with no error, the
    symbolic evaluation also succeeds and it gives the *same* variable store.

    The claim is the *refinement* direction and not full equivalence, because the two evaluators
    correctly differ when concrete execution stops and symbolic execution continues:

    * `assert e`, where `e` does not reduce to a concrete Boolean value. `Cmd.run` gives an error,
      and `Cmd.eval` keeps a proof obligation for later.
    * `assume false`. `Cmd.run` gives an error, and `Cmd.eval` adds a path condition.
    * `cover`. `Cmd.run` gives an error, because it does not support a `cover`, and `Cmd.eval` keeps
      an obligation for later.

    In each of those cases the concrete run *fails*, so the implication is vacuously true and the
    property makes no wrong claim. In each case where the two agree, which is an `init`, a `set`, and
    an `assert` or an `assume` whose condition is concretely true, both evaluators give the same
    store. -/
def checkEvalRunAgreement (cmd : Cmd Expression) (ctx : VarCtx) : Bool :=
  let σ := envFromVarCtxWellTyped ctx
  let runEnv := Cmd.run σ cmd
  let (_, evalEnv) := Cmd.eval σ cmd
  if runEnv.error.isNone then
    evalEnv.error.isNone &&
      (runEnv.exprEnv.state.toSingleMap == evalEnv.exprEnv.state.toSingleMap)
  else
    true

/-- How the condition of a command reduces, for a Tyche panel. For an `assert`, an `assume` and a
    `cover`, the function evaluates the condition in the store that the placeholder values built,
    and it reports `"true"`, `"false"` or `"non-concrete"`. For each other command, it reports
    `"n/a"`. -/
def cmdConditionKind (cmd : Cmd Expression) (ctx : VarCtx) : String :=
  match cmd with
  | .assert _ e _ | .assume _ e _ | .cover _ e _ =>
    match CmdEval.denoteBool (CmdEval.eval (envFromVarCtxWellTyped ctx) e) with
    | some true => "true"
    | some false => "false"
    | none => "non-concrete"
  | _ => "n/a"

-- ── The structural shrinker for a command ─────────────────────────────
--
-- This shrinker follows the strategy of the shrinker for an expression, `shrinkLExpr`: it makes a
-- structural reduction and then rejects a candidate that does not hold. `checkExprTypechecks`
-- requires each candidate to stay well-typed. The *type* of a candidate can change, and the
-- shrinker for an expression already allows this. A reduction from `init (x : bool) := (b && c)`
-- toward `init (x : int) := n` keeps a well-typed command, because the code computes the declared
-- type again and it therefore still matches the smaller right side.

/-- The structurally smaller candidates for a command, before the filter for good typing. There are
    two families of reduction:

    * **A reduction of the expression on the right.** The shrinker reduces the expression of an
      `init` or of a `set`, for a deterministic right side only, or the Boolean condition of an
      `assert`, an `assume` or a `cover`. It uses the shared `shrinkLExpr`. For a deterministic
      `init`, the code computes the declared type again from the smaller right side, so the result
      stays well-typed even when the type of that side changes.
    * **A collapse of the determinism.** The shrinker replaces the deterministic right side of an
      `init` or of a `set` by `.nondet`, which is a `havoc`. Such a command is simpler and it is
      always well-typed. -/
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

/-- The structural reductions of a command that stay well-typed. Each candidate is a command whose
    expressions still typecheck: at `bool` for an `assert`, an `assume` and a `cover`, at the
    declared type that the code computed again for an `init`, and at any type for a `set`. -/
def shrinkCmd (c : Cmd Expression) : List (Cmd Expression) :=
  (shrinkCmdCandidates c).filter checkExprTypechecks

/-- The variables that a command adds to the ambient context. Only an `init` declares a new
    variable. The function follows the computation of `definedNames` in `checkContextGrowth`, so the
    output context that the code computes again for a smaller command stays correct. -/
def cmdDefinedVars (c : Cmd Expression) : List (Identifier Unit × LMonoTy) :=
  match c with
  | .init x (.forAll [] mty) _ _ => [(x, mty)]
  | _ => []

/-- The output context of a command, from its input context. The result is the input context and
    each variable that the command declares. A caller uses this function after a reduction. -/
def cmdOutCtx (inCtx : VarCtx) (c : Cmd Expression) : VarCtx :=
  Map.ofList (List.append (inCtx : List (Identifier Unit × LMonoTy)) (cmdDefinedVars c))

/-- The output context of a *sequence* of commands, from its input context. The result is the input
    context and each variable that the sequence declares, in order. The function follows the fold
    over `definedNames` in `checkContextGrowth`, so a smaller sequence satisfies the property about
    the growth of the context by construction. -/
def cmdsOutCtx (inCtx : VarCtx) (cmds : List (Cmd Expression)) : VarCtx :=
  Map.ofList (List.append (inCtx : List (Identifier Unit × LMonoTy)) (cmds.flatMap cmdDefinedVars))

/-- The standard ambient typing context of Core. It holds the operators of `Core.Factory` and the
    types of `Core.KnownTypes`. The type check of a whole *sequence* of commands uses it. The
    statement module has the same context as `stmtCheckContext`. This module holds its own copy,
    because that module imports *this* module. -/
def cmdSeqCheckContext : LContext CoreLParams :=
  { LContext.default with
    functions := Core.Factory,
    knownTypes := Core.KnownTypes }

/-- Builds a typing environment from a `VarCtx`. The environment declares each variable of the input
    context with its monotype. A type check of a sequence of commands that the generator drew under
    `inCtx` therefore has those variables in scope. -/
def seedTyEnv (inCtx : VarCtx) : TEnv Unit :=
  (inCtx : List (Identifier Unit × LMonoTy)).foldl
    (fun e (x, mty) => Core.CmdType.update e x (LTy.forAll [] mty)) TEnv.default

/-- **The check for good form of a *sequence* of commands, which threads the scope.**
    `checkExprTypechecks` acts on one command. It typechecks each expression in the *empty* context,
    and it trusts the annotation on a free variable. This function is different: it runs
    `Imperative.Cmds.typeCheck` of Strata, which threads a variable context along the sequence. An
    `init` adds to the scope, and the check rejects a `set` or a reference to a variable that no
    declaration introduced. The environment starts from `inCtx`, so each variable that a declaration
    introduced before is in scope.

    This check is what makes the removal of an `init` a rejected reduction when a later command uses
    the variable of that `init`, and the result is therefore never a reference with no
    declaration. -/
def cmdsScopeWellFormed (inCtx : VarCtx) (cmds : List (Cmd Expression)) : Bool :=
  match Imperative.Cmds.typeCheck cmdSeqCheckContext (seedTyEnv inCtx) cmds with
  | .ok _ => true
  | .error _ => false

/-- The structural reductions of a sequence of commands. The shrinker removes one command, or it
    replaces one command by a smaller command from `shrinkCmd`. `cmdsScopeWellFormed` filters each
    candidate, and that check reads the whole sequence and threads the scope from `inCtx`. A
    candidate therefore stays well-typed *and* well-formed. The check rejects the removal of an
    `init` whose variable a later command uses, so the result never holds a variable with no
    declaration. `shrinkCmd` already keeps the expression of each replacement well-typed, and the
    check on the sequence adds the scope across the commands. -/
def shrinkCmds (inCtx : VarCtx) (cmds : List (Cmd Expression)) : List (List (Cmd Expression)) :=
  (dropEach cmds
   ++ cmds.zipIdx.flatMap (fun (c, i) => (cmds.set i ·) <$> shrinkCmd c)).filter
    (cmdsScopeWellFormed inCtx)

-- ── The wrappers around the generators ────────────────────────────────

/-- Makes one well-typed command in `IO`. The result holds the command, the input context and the
    output context. -/
def genCmdIO (ctx : VarCtx := []) (depth : Nat := 2) : IO (Cmd Expression × VarCtx × VarCtx) := do
  let tvars : List TyIdentifier := []
  let ⟨cmd, ctx'⟩ ← genCmd (G := IO) coreMonoOps tvars [] ctx depth
  return (cmd, ctx, ctx')

/-- Makes a sequence of well-typed commands in `IO`. -/
def genCmdsIO (n : Nat := 5) (ctx : VarCtx := []) (depth : Nat := 2) :
    IO (List (Cmd Expression) × VarCtx × VarCtx) := do
  let tvars : List TyIdentifier := []
  let (cmds, ctx') ← genCmds (G := IO) coreMonoOps tvars [] ctx depth n
  return (cmds, ctx, ctx')
