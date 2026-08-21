-- The check predicates that each registered property scores with. Each property pairs its name with its
-- check in one place, in a file under `StrataTests/`.
import StrataGenerators.PhaseChangedFlag
import StrataGenerators.PrinterCoverage
import StrataGenerators.ProcedureHasTypeAGen.TestSupport
import StrataGenerators.ProgramGen.UnprovenTransforms
import StrataGenerators.ProgramGen.LiftFuncDecls
import StrataGenerators.AdtLaws
import StrataGenerators.AliasResolution
import StrataGenerators.MutualBlockShape
import StrataGenerators.RetryGen
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.HasTypeAGen.SmtEval
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.Roundtrip
import StrataGenerators.FunctionHasTypeAGen.Shrink
import StrataGenerators.StmtHasTypeAGen.TestSupport
-- `relabelProcs` and `shrinkProcsList` support the `Shrinkable GenProcs` instance, so that the harness
-- reports a smallest well-typed counterexample for a procedure.
import StrataGenerators.ProcedureHasTypeAGen.Shrink
-- The whole-program generator, and the whole-program shrinker that supports the `Shrinkable GenProgram`
-- instance, together with each `checkProgram*` predicate.
import StrataGenerators.ProgramGen
import StrataGenerators.ProgramGen.Shrink
-- The support for a call to a function that a datatype derives, which each `checkProgramADTCalls*`
-- predicate uses.
import StrataGenerators.ProgramGen.TestSupport
import Basalt.PlausibleGen
import Plausible
import Strata.DL.Lambda.LExprT
-- The imports for the property about `Function.typeCheck`.
import Strata.Languages.Core.FunctionType
import Strata.DL.Lambda.Denote.LExprAnnotated
-- The imports for the property about the round trip from the printer to the parser.
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

/-!
# The wrappers around a generator

This module holds one wrapper structure for each shape that the suite generates, together with the
`Repr`, `Shrinkable` and `Arbitrary` instance of that shape. It also holds each check and each
diagnostic that runs at `IO` and that draws and prints its own samples.

This module is the **one source of truth for how the suite draws, shrinks and prints each shape**.
`TestDecl.property` resolves the `Arbitrary`, `Repr` and `Shrinkable` instance of each wrapper.
`StrataGenerators.Test.Generators` adds the `TycheFeatures` instance, and it makes those four instances
into a `PropertyRunner`, for the rare property that needs a different one.

The properties themselves are **not** here. Each property is a `@[strata_property]` declaration under
`StrataTests/`, and it pairs its name with its check in one place. Read `StrataGenerators.Test` and
`docs/writing-properties.md`. This module holds the generation only.
-/

open Lambda RandomChoice ArbNat Basalt.PlausibleGen Plausible Core Imperative
open Strata Strata.CoreDDM
open StrataDDM (initDialect)

-- ── The generation of a typed expression ─────────────────────────────

/-- A generated expression together with its type. It can hold a free variable from `defaultFCtx`. -/
structure TypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving BEq

instance : Repr TypedExpr where
  reprPrec te _ := s!"({ppExpr te.expr}) : {ppType te.ty}"

-- The structural shrinker for an expression, which is `shrinkLExpr`, and its helper
-- `immediateSubtermsWithoutBinders` are in `StrataGenerators.HasTypeAGen.TestSupport`. Therefore the
-- shrinker for a command, for a statement and for a function each use the same rules of reduction. An
-- import of this file brings both definitions in.

/-- The shrinker for each wrapper that pairs an `LExpr` with its type. Those wrappers are `TypedExpr`,
    `ClosedTypedExpr` and `ResolveTypedExpr`, and they differ only in how the suite generates them.

    The shrunk term must have the correct type. Therefore this shrinker shrinks the `LExpr` with
    `shrinkLExpr`, and it then filters out each candidate that is not well typed. It type checks each
    candidate that stays, to recover the type of the shrunk term. The parameter `mk` builds the concrete
    wrapper from the pair of the expression and the type. This design needs no separate shrinker for a
    type. -/
private def shrinkTypedExpr (mk : LExpr' → LMonoTy → α) (e : LExpr') : List α :=
  (shrinkLExpr e).filterMap fun e' =>
    match LExpr.typeCheck (T := LExprParams') [] e' with
    | some τ' => some (mk e' τ')
    | none => none

instance : Shrinkable TypedExpr where
  shrink te := shrinkTypedExpr (⟨·, ·⟩) te.expr

private def genTypedExprWith (fctx : FVarCtx) : Gen TypedExpr := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := Plausible.Gen) tvars depth
  -- `retryGenArg` is the retry continuation. After a failure at a *subterm*, it draws that subterm again,
  -- and it does not let the failure discard the whole term. It applies at each level of the nesting, and
  -- the outer `retryGen` below cannot reach those levels. Without it, one leaf deep in a term that nothing
  -- can fill costs a full new draw of the term. The outer `retryGen` is still necessary for the draw at
  -- the root.
  let expr ← genLExprWithOps (G := Plausible.Gen) fctx coreMonoOps corePolyOps tvars []
               depth ty 3 (retryGenArg 20)
  pure ⟨expr, ty⟩

-- `genLExpr` can fail through `default` when an arrow case at the depth 0 finds no bound variable, free
-- variable or operator in the context. `Plausible.Gen` does not backtrack, so `retryGen` draws again with
-- new randomness after such a failure.
instance : Arbitrary TypedExpr where
  arbitrary := retryGen 500 (genTypedExprWith defaultFCtx)

/-- A generated closed expression, which holds no free variable. Each property that the suite states for
    the empty typing context uses this wrapper. Those properties are the ones about progress and about
    preservation. -/
structure ClosedTypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving BEq

instance : Repr ClosedTypedExpr where
  reprPrec te _ := s!"({ppExpr te.expr}) : {ppType te.ty}"

instance : Shrinkable ClosedTypedExpr where
  shrink te := shrinkTypedExpr (⟨·, ·⟩) te.expr

instance : Arbitrary ClosedTypedExpr where
  arbitrary := retryGen 500 ((fun te => ⟨te.expr, te.ty⟩) <$> genTypedExprWith [])

-- ── Printing ─────────────────────────────────────────────────────────

instance : Repr LExpr' where
  reprPrec e _ := ppExpr e

instance : Repr LMonoTy where
  reprPrec τ _ := ppType τ

open Std in
instance : ToFormat Unit where
  format _ := .nil

-- ── The properties about the evaluator ───────────────────────────────
--
-- These properties test `LExpr.eval` of `Strata.DL.Lambda.LExprEval`. The first two, which are about the
-- typechecker and about preservation, follow the standard theorems about the safety of a type system.
-- Each other property is about the operational behaviour of the evaluator, which has a bound on its fuel.
-- The theorems of `Strata.DL.Lambda.Semantics` are the model for them.
--
-- Two of those theorems have no property here:
--
--   * One theorem says that the evaluator is sound against the small-step relation `Step`. A direct test
--     of it would have to search for a reachable expression, because the statement holds an existential
--     witness. The properties about idempotence, about growth and about preservation cover that ground
--     instead.
--   * One theorem says that the evaluator gives the same result after a change of the metadata. The
--     metadata type here is `Unit`, so the function that erases the metadata is the identity, and the
--     property holds for that trivial reason.

-- Each property is `@[reducible]`, so that the resolution of a class in Lean can unfold it and find the
-- `Decidable` instance of the proposition inside it. An example of such an instance is a `DecidableEq`
-- for an equality. Without that attribute, the `decidableTestable` instance of the harness sees an opaque
-- `Prop`, and it cannot build a `Testable` instance.

-- ── A resolve after an erasure ───────────────────────────────────────

/-- A closed expression over `coreOpCtx`, which holds the operators of `coreFactory`. The suite sends such
    an expression through `eraseTypes` and then through `resolve`. -/
structure ResolveTypedExpr where
  expr : LExpr'
  ty : LMonoTy
  deriving BEq

instance : Repr ResolveTypedExpr where
  reprPrec te _ := s!"({ppExpr te.expr}) : {ppType te.ty}"

instance : Shrinkable ResolveTypedExpr where
  shrink te := shrinkTypedExpr (⟨·, ·⟩) te.expr

private def genResolveTypedExpr : Gen ResolveTypedExpr := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := Plausible.Gen) tvars depth
  -- Read `genTypedExprWith`. `retryGenArg` draws a failed subterm again, in place.
  let expr ← genLExprWithOps (G := Plausible.Gen) [] coreOpCtx [] tvars [] depth ty 3
               (retryGenArg 20)
  pure ⟨expr, ty⟩

instance : Arbitrary ResolveTypedExpr where
  arbitrary := retryGen 500 genResolveTypedExpr

/-- Run `resolve` on the term after a full erasure, and report the result as a string. The result is `none`
    when the property holds, which means that `resolve` succeeded and inferred a type that is general
    enough. It is `some msg` for a counterexample, and the message is the error of `resolve` itself, or the
    type that `resolve` inferred. -/
def resolveErrorMessage (te : ResolveTypedExpr) : Option String :=
  let erased := eraseAllTypes te.expr
  match LExpr.resolve resolveLContext Lambda.TEnv.default erased with
  | .ok (resolved, _) =>
    if isInstanceOf te.ty resolved.toLMonoTy then none
    else some s!"inferred {ppType resolved.toLMonoTy}, not an instance of {ppType te.ty}"
  | .error e => some s!"{e}"

-- ── The generation of a command ──────────────────────────────────────

/-- A generated command together with the context of its input. -/
structure GenCmdWithCtx where
  cmd : Cmd Expression
  inCtx : VarCtx
  outCtx : VarCtx

instance : Repr GenCmdWithCtx where
  reprPrec gc _ := s!"{ppCmd gc.cmd}  [ctx: {ppVarCtx gc.inCtx}]"

-- This instance shrinks the command with the shared structural shrinker for a command, which keeps the
-- command well typed through `checkExprTypechecks`. It holds the context of the input fixed, and it
-- computes the context of the output again from the shrunk command. Therefore the wrapper stays
-- consistent, and the context of the output is the context of the input together with each variable that
-- the command defines.
instance : Shrinkable GenCmdWithCtx where
  shrink gc := (shrinkCmd gc.cmd).map fun c' =>
    { gc with cmd := c', outCtx := cmdOutCtx gc.inCtx c' }

private def genCmdWith (ctx : VarCtx) : Gen GenCmdWithCtx := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let tvars : List TyIdentifier := []
  let ⟨cmd, ctx'⟩ ← genCmd (G := Plausible.Gen) coreMonoOps tvars [] ctx depth
  pure ⟨cmd, ctx, ctx'⟩

private def genCmdFromBuiltCtx (ctxSize : Nat) : Gen GenCmdWithCtx := do
  let depth := 2
  let tvars : List TyIdentifier := []
  let (_, baseCtx) ← genCmds (G := Plausible.Gen) coreMonoOps tvars [] [] depth ctxSize
  let ⟨cmd, ctx'⟩ ← genCmd (G := Plausible.Gen) coreMonoOps tvars [] baseCtx depth
  pure ⟨cmd, baseCtx, ctx'⟩

instance : Arbitrary GenCmdWithCtx where
  arbitrary := retryGen 1000 (genCmdFromBuiltCtx 3)

/-- A generated sequence of commands together with its context. -/
structure GenCmdsWithCtx where
  cmds : List (Cmd Expression)
  inCtx : VarCtx
  outCtx : VarCtx

instance : Repr GenCmdsWithCtx where
  reprPrec gc _ :=
    let cmdStrs := gc.cmds.map ppCmd |> "; ".intercalate
    s!"{cmdStrs}  [in: {ppVarCtx gc.inCtx}, out: {ppVarCtx gc.outCtx}]"

-- This instance shrinks the sequence of the commands, by a removal of one command or by a shrink of one
-- command. It holds the context of the input fixed, and it computes the context of the output again from
-- the shrunk sequence. Therefore `checkContextGrowth` still relates the two contexts.
instance : Shrinkable GenCmdsWithCtx where
  shrink gc := (shrinkCmds gc.inCtx gc.cmds).map fun cs' =>
    { gc with cmds := cs', outCtx := cmdsOutCtx gc.inCtx cs' }

private def genCmdsWithCtx : Gen GenCmdsWithCtx := do
  let depth := 2
  let n := 4
  let tvars : List TyIdentifier := []
  let (cmds, ctx') ← genCmds (G := Plausible.Gen) coreMonoOps tvars [] [] depth n
  pure ⟨cmds, [], ctx'⟩

instance : Arbitrary GenCmdsWithCtx where
  arbitrary := retryGen 1000 genCmdsWithCtx

-- ── The properties about a command ───────────────────────────────────

-- Each property about a command is in `StrataTests/Cmd.lean`, and it pairs its name with its check in one
-- place. Those properties are about a fresh name in an `init`, the type check of an expression, the
-- preservation of a variable by a `set`, the preservation of the type of the store, the growth of the
-- context, and the agreement between the symbolic evaluator and the concrete evaluator. Their check
-- predicates are in `CmdHasTypeAGen.TestSupport`.

-- ── The generation of a function ─────────────────────────────────────

/-- A `Function` from `genFunction`, together with the context of the free variables that the generator used.
    The property about the annotations of the free variables needs that context, to find the matching type
    map. -/
structure GenFunction where
  func : Function
  fctx : FVarCtx

instance : Repr GenFunction where
  reprPrec gf _ := formatFunc gf.func

-- This instance shrinks the function structurally. It can drop the body, the measure, an input or a type
-- argument, shrink a type, or shrink the expression of the body or of the measure. It holds the context of
-- the free variables fixed. Each candidate satisfies `funcWellFormed`, so it stays well typed.
-- `shrinkLExpr` gives a subterm only, and it adds no free variable with a different annotation. Therefore
-- the property about the annotations of the free variables still holds against the same context.
instance : Shrinkable GenFunction where
  shrink gf := (shrinkFuncWellFormed gf.func).map fun f' => { gf with func := f' }

/-- Generate a function against `defaultFCtx`, and give the context of the free variables, so that a
    property can read the matching type map. The depth grows with the size parameter of the harness, as it
    does in `genCmdWith`. -/
private def genFunctionWith (fctx : FVarCtx) : Gen GenFunction := Gen.sized fun s => do
  let depth := max 1 (s / 20)
  let func ← genFunction (G := Plausible.Gen) fctx coreMonoOps depth
  pure ⟨func, fctx⟩

instance : Arbitrary GenFunction where
  arbitrary := retryGen 1000 (genFunctionWith defaultFCtx)

-- ── The properties about a function ──────────────────────────────────

-- ── The generator of a closed function ───────────────────────────────

/-- A `Function` from a generator with an *empty* context of free variables. Each body is closed and holds no
    free variable, so `Function.typeCheck` can succeed with no context that declares such a variable. -/
structure ClosedGenFunction where
  func : Function

instance : Repr ClosedGenFunction where
  reprPrec gf _ :=
    -- Name the body and the measure. The printer omits an absent body and an absent measure, and that
    -- difference is exactly what the gap in completeness depends on. That gap is a function with a measure
    -- and no body, so a counterexample must show the difference.
    let tag := s!"[body={gf.func.body.isSome}, measure={gf.func.measure.isSome}]"
    s!"{tag}\n{formatFunc gf.func}"

-- This instance uses the same structural shrinker for a function as `GenFunction`. `funcWellFormed`
-- accepts a function with a measure and no body, because the condition on the body then holds with no
-- content. Therefore the shrinker *keeps* that shape, which is the counterexample that the two properties
-- about completeness look for. The shrinker can even reach that shape by a removal of the body that keeps
-- the measure, and it then gives a smallest witness instead of discarding one.
instance : Shrinkable ClosedGenFunction where
  shrink gf := (shrinkFuncWellFormed gf.func).map fun f' => { gf with func := f' }

private def genClosedFunctionWith : Gen ClosedGenFunction := Gen.sized fun s => do
  let depth := max 2 (s / 20)
  let func ← genFunction (G := Plausible.Gen) [] coreMonoOps depth
  pure ⟨func⟩

instance : Arbitrary ClosedGenFunction where
  arbitrary := retryGen 2000 genClosedFunctionWith

-- ── The soundness of `Function.typeCheck` ────────────────────────────
--
-- This property covers a theorem of Strata that has no proof: when `Function.typeCheck` accepts a
-- function, its output satisfies `FuncHasTypeA` at each typing context.
--
-- The decision procedure is `checkTypeCheckAnnotatedSound`. It reflects `FuncHasTypeA` through
-- `checkFuncHasTypeA`, with the context `funcCheckContext`, and it is in
-- `StrataGenerators.FunctionHasTypeAGen.TestSupport`. Both harnesses use it.

-- ── The round trip from the printer to the parser ────────────────────
--
-- This property puts a generated `Function` into a trivial `Program`, prints it with
-- `Core.formatProgram`, parses the output again with DDM, formats the result again, and compares the two
-- strings. A failure of the parse is a true defect of the printer or of the parser, because each name is a
-- legal Core identifier by construction.
--
-- `formatFuncAsProgram`, `parseCoreProgram`, `parseCoreProgramErr`, the structural shrinker and the two
-- predicates for a failure are in `StrataGenerators.FunctionHasTypeAGen.Roundtrip`. Both harnesses use
-- them.

/-- The property about the round trip: the format, the parse and the second format give the same string. The
    result is `true` only when the round trip succeeds. The action runs at `IO`.

    A failure of the parse counts as a **counterexample**, and not as a sample that says nothing.
    `genIdentName` gives a legal Core identifier by construction. Therefore output that the parser cannot
    read is legal and unreadable, which is a true defect of the round trip. -/
def checkPrintParseRoundtrip (func : Function) : IO Bool := do
  let s1 := formatFuncAsProgram func
  match ← parseCoreProgram s1 with
  | some ast2 =>
    let s2 := (Core.formatProgram ast2).pretty
    pure (s1 == s2)
  | none => pure false  -- parse failure = round-trip bug (names are legal by construction)

-- ── The round trip of an identifier with a special character ─────────
--
-- The round trip of a whole function fails on a sample that holds a name, a type argument, a type, a body
-- and more. A reader cannot then assign the failure to one cause. This probe isolates one generated
-- identifier at one syntactic position, inside a function that is trivial in each other part. Therefore a
-- failure gives a smallest reproducer, which says that the identifier at that position does not survive the
-- round trip.
--
-- `genQuotedName` draws each identifier. Each such name is a legal Core identifier, so a failure is a true
-- defect and not an artefact of the generator. Each name holds a special character, which is a character
-- that is not alphanumeric, at an interior position. Those characters are `. ' | \ ? ! @`. This probe
-- therefore reaches the paths for a special character and for an escape with a pipe, and `genIdentName`,
-- which `genFunction` uses, reaches neither of them.
--
-- `IdentPosition` and `minimalFuncWithName` are in `StrataGenerators.FunctionHasTypeAGen.TestSupport`, and
-- both harnesses use them.

/-- Round-trip a single identifier in one position. Returns `none` on success,
    or `some (renderedProgram, reparsedOrMismatch)` describing the failure. -/
def probeIdentRoundtrip (pos : IdentPosition) (name : String) :
    IO (Option (String × String)) := do
  let s1 := formatFuncAsProgram (minimalFuncWithName pos name)
  match ← parseCoreProgramErr s1 with
  | .error e => pure (some (s1, s!"parse-failure: {e.take 140}"))
  | .ok ast2 =>
    let s2 := (Core.formatProgram ast2).pretty
    if s1 == s2 then pure none
    else pure (some (s1, s2))

-- ── The generation of a statement list ───────────────────────────────
--
-- `genProgramStmts` gives a well-typed Strata Core statement list, which satisfies
-- `StatementsHasTypeA`. That generator has a proof of soundness and a proof of completeness against the
-- declarative typing specification. The suite therefore uses it as a certified well-typed input for the
-- typechecker of a statement and for each transform of Strata Core at the level of a statement. Each check
-- predicate is in `StrataGenerators.StmtHasTypeAGen.TestSupport`.

open StrataGenerators.Stmt.TestSupport

/-- A generated well-typed statement list. -/
structure GenStmts where
  stmts : List Statement

instance : Repr GenStmts where
  -- The rendering uses the formatter of Strata, which gives real Core concrete syntax. It appends a summary
  -- of each `funcDecl` shape, because the formatter cannot write a `funcDecl` statement with no body, and it
  -- puts a dummy body there instead. A `funcDecl` with a measure and no body is exactly the counterexample
  -- to the completeness of the typechecker, so the summary records the true shape.
  reprPrec gs _ :=
    let shapes := funcDeclShapesList gs.stmts
    let suffix := if shapes.isEmpty then "" else s!"\n  -- {" ".intercalate shapes}"
    formatStmts gs.stmts ++ suffix

-- This instance shrinks the statement list structurally. It can drop a statement, replace one statement by
-- a smaller one, or put the body of a compound statement in place of that statement. It keeps only a
-- candidate that the algorithmic typechecker accepts, because `shrinkStmts` filters on `checkTypeChecks`.
-- A shrunk list is therefore well typed by construction, because the shrinker checks the whole list again
-- and does not assume that a local change keeps the property.
instance : Shrinkable GenStmts where
  shrink gs := (shrinkStmts gs.stmts).map (⟨·⟩)

/-- Generate a well-typed statement list. The parameter `size`, which is the size of the nesting and of an
    expression, and the length of the sequence both grow with the size parameter of the harness. -/
-- The nesting `size` and the length `len` each stay small, because the properties under test need no large
-- program. A larger `size` also raises the chance that a nested sub-generator reaches its fallback for an
-- empty support. Two examples of such a case are a clash between two `typeDecl` names, and an `exit` with
-- no label around it. Such a failure makes `retryGen` draw the *whole* statement list again, and it can
-- use up the fuel at a large size.
private def genStmtsWith : Gen GenStmts := Gen.sized fun s => do
  let size := max 1 (min 3 (s / 25))
  let len := max 1 (min 4 (s / 20))
  let (ss, _, _) ← StrataGenerators.Stmt.genProgramStmts (G := Plausible.Gen) coreMonoOps [] size len
  pure ⟨ss⟩

-- `genStmt` can reach the empty generator through `default` in a subcase, such as a clash between two
-- `typeDecl` names. Therefore `retryGen` draws again with new randomness, as it does for each other
-- generator here.
instance : Arbitrary GenStmts where
  arbitrary := retryGen 4000 genStmtsWith

-- ── The properties about a statement ─────────────────────────────────

-- Each property about a statement transform and about the typechecker is in `StrataTests/Stmt.lean`, and
-- its check predicate is in `StmtHasTypeAGen.TestSupport`. The property about the definedness of the Kleene
-- transform keeps a panel of its own, because that panel records the definedness *and* the reason for it.

-- ── The generation of a procedure ────────────────────────────────────
--
-- `genProcedure` gives a well-typed Strata Core procedure, which satisfies `ProcHasTypeA`. That generator
-- has a proof of soundness and a proof of completeness against the declarative typing specification. The
-- suite assembles a *list* of such procedures into a `Program` with several declarations, and it uses that
-- program as a certified well-typed input for the three Core transform passes, which are
-- FilterProcedures, PrecondElim and ANFEncoder. Each check predicate is in
-- `StrataGenerators.ProcedureHasTypeAGen.TestSupport`, and each property that scores with one is in
-- `StrataTests/Proc.lean`.

open StrataGenerators.Procedure.TestSupport

/-- A generated list of well-typed procedures, for an assembly into a program. The wrapper renames each
    procedure to `P0`, `P1` and so on, so that no two names collide. The generator draws each name on its
    own, so two procedures could otherwise share a name, and a check that reads a name would then give the
    wrong answer. -/
structure GenProcs where
  procs : List Core.Procedure

instance : Repr GenProcs where
  -- The rendering uses the formatter of Strata, which gives real Core concrete syntax. Therefore a
  -- counterexample shows exactly the program that the pass received.
  reprPrec gp _ :=
    let prog : Core.Program := { decls := gp.procs.map (Core.Decl.proc · .empty) }
    (Core.formatProgram prog).pretty

-- This instance uses the shared shrinker `shrinkProcsList`. That shrinker can drop a whole procedure, and
-- it can also reduce one procedure in place, through `shrinkStmtsList` for the body and `shrinkLExpr` for
-- a precondition or a postcondition. It renames the procedures that stay to `P0` up to `Pk`.
-- `Procedure.typeCheck` of Strata checks each candidate, so a reported counterexample is always a
-- *well-typed* program. That condition matters, because each of these properties has content on well-typed
-- input only. The shrinker holds each header fixed, so each procedure keeps its signature.
instance : Shrinkable GenProcs where
  shrink gp := (shrinkProcsList gp.procs).map (⟨·⟩)

-- The nesting `size` of one procedure stays at 2 or below, the length of a body at 3 or below, and the
-- number of the procedures between 2 and 4. The properties about a transform need no large program. As in
-- `genStmtsWith`, a larger `size` also raises the chance that a nested sub-generator reaches its fallback
-- for an empty support, which makes the harness draw the whole procedure again and can use up the fuel at
-- a large size. The budget of the retries is large enough for each size up to the maximum of 100.
--
-- The generator makes the procedures **from left to right, into an acyclic graph of calls**. It makes the
-- body of the procedure `i` against the signatures of the procedures before it, which the renaming step
-- names `P0` up to `P{i-1}`. Those names are exactly what `relabelProcs` gives each position below, so each
-- `call` and each renamed header agree.
--
-- A body can therefore call a procedure before it, and it can emit a `call P{j}` for a `j` below `i`. The
-- call graph of the assembled program therefore holds real edges, and each dimension of the properties
-- about FilterProcedures and about PrecondElim that reads the call graph has real content. A
-- **polymorphic** procedure is also callable: `headerProcSig` records the type arguments of the callee, and
-- `genCallStmt` samples a concrete instance of them at the call site.
private def genProcsWith : Gen GenProcs := Gen.sized fun s => do
  let n := max 2 (min 4 (2 + s / 30))
  let size := max 1 (min 2 (s / 30))
  let len := max 1 (min 3 (s / 25))
  let (ps, _) ← (List.range n).foldlM
    (fun (acc : List Core.Procedure × StrataGenerators.Stmt.ProcSigCtx) (i : Nat) => do
      let proc ← (retryGen 8000
        (StrataGenerators.Procedure.genProcedure (G := Plausible.Gen)
          corePartialOps acc.2 LContext.default {} size len) : Gen Core.Procedure)
      -- Add this procedure to the context of the callable procedures. Its name after the renaming is `P{i}`,
      -- and the code discards the name of its generated header. A monomorphic procedure and a polymorphic
      -- procedure are both callable, because the call site instantiates the type arguments.
      let sigs := acc.2 ++ [StrataGenerators.Procedure.headerProcSig s!"P{i}" proc.header]
      pure (acc.1 ++ [proc], sigs))
    (([], []) : List Core.Procedure × StrataGenerators.Stmt.ProcSigCtx)
  pure ⟨relabelProcs ps⟩

instance : Arbitrary GenProcs where
  arbitrary := retryGen 8000 genProcsWith

-- Each property about a procedure and a transform pass is in `StrataTests/Proc.lean`. Seven of them are
-- about FilterProcedures, thirteen about PrecondElim and eight about ANFEncoder. Two of them state that the
-- `changed` flag of a pass is `true` if and only if the program changes.

-- ── The generation of a whole program ────────────────────────────────
--
-- `genProgram` gives a whole well-typed Strata Core `Program`. It emits each kind of declaration, and it
-- threads the context across the fold over the declarations. It has a proof of soundness against the
-- declarative specification `ProgramHasTypeA`, in `ProgramGen.SoundProgram`. `GenProcs` assembles a program
-- from procedures only, and this generator also emits an abstract type, an alias, an axiom, a `distinct`
-- declaration, a block of datatypes and a function.
--
-- Most of the suite quantifies over this type. That includes the whole-program checks and the checks about a
-- call to a derived function in `StrataTests/Program.lean`, the properties about a transform with no proof in
-- `StrataTests/Transforms.lean`, the properties about the lifting of a lambda in `StrataTests/Lift.lean`, the
-- properties about an alias in `StrataTests/Alias.lean`, and the property about the coverage of the printer in
-- `StrataTests/Printer.lean`. That last property needs a whole `Program`, because the constructs that the
-- printer cannot write are spread across a type declaration, which can hold a bitvector width in a signature,
-- an expression, which can hold an operator between a bitvector and an integer, and a statement, which can be
-- a `funcDecl` with no body. `genProgram` reaches each of the three.
--
-- This generator is also the only place where a call to a derived function of a datatype is visible from end
-- to end. A block of datatypes extends the vocabulary of the operators, and each *later* function and
-- procedure draws from it. Therefore the body of such a function can call a constructor, a tester, or a safe
-- or unsafe accessor of a field of the block. `derivedCallCoverage` below reports that as a statistic.

open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport

/-- A generated whole program. -/
structure GenProgram where
  prog : Core.Program

instance : Repr GenProgram where
  -- The rendering uses the formatter of Strata, which gives real Core concrete syntax, so a counterexample
  -- shows exactly the program under test. It then appends the shared `programStatusNote`. That note matters,
  -- because the shrinker cannot minimize a program that the typechecker rejects. The oracle of the shrinker
  -- *is* that typechecker. Therefore the note names the gap that caused the rejection, and a reader does not
  -- have to find it in a program of the full size. The note gives the message of the checker itself when the
  -- rejection matches no known gap. The renderer of the Tyche panel uses the same function, so the two views
  -- agree.
  reprPrec gp _ :=
    (Core.formatProgram gp.prog).pretty ++ programStatusNote gp.prog

-- This instance uses the whole-program shrinker `shrinkProgram`. That shrinker can drop a declaration, keep a
-- prefix of the declarations, remove each declaration that holds a known gap at one time, or reduce one
-- declaration in place, through the shrinker for a procedure, a function, a statement or an expression.
-- `Program.typeCheck` of Strata checks each candidate, so a reported counterexample is always a well-typed
-- program. The shrinker keeps the order of the declarations, and it renames nothing.
instance : Shrinkable GenProgram where
  shrink gp := (shrinkProgram gp.prog).map (⟨·⟩)

-- The number of the declarations stays between 2 and 5, and it grows with the size parameter of the harness.
-- As in `genProcsWith`, the budget of the retries must absorb each residual failure of the expression
-- generator, which happens when nothing in scope inhabits a compound argument type. Each declaration is an
-- independent chance of such a failure, so the probability that a whole program succeeds falls quickly with
-- the number of the declarations.
--
-- The fuel is the default value of `ProgramGen.sample`. A large value is necessary, because the body of a
-- function or of a procedure can call a derived function of a datatype. A call to the tester or to an
-- accessor of a *polymorphic* datatype goes through the `IndirPoly` rule, which samples an instance, and a
-- sample that nothing can fill is another failure for the retry loop to absorb. The number of the
-- declarations here is far below the number at which that cost matters, so this fuel is ample.
private def genProgramWith : Gen GenProgram := Gen.sized fun s => do
  let numDecls := max 2 (min 5 (2 + s / 25))
  let prog ← (retryGen 30000 (ProgramGen.genProgram (G := Plausible.Gen) numDecls {})
    : Gen Core.Program)
  pure ⟨prog⟩

instance : Arbitrary GenProgram where
  arbitrary := retryGen 8000 genProgramWith

-- ── The diagnostic for the whole-program shrinker ────────────────────
--
-- No whole-program property shows how well the *shrinker* works. The one property that reliably reports a
-- counterexample does so on a program that holds a known gap, and no shrinker with this oracle can minimize
-- such a program. The one property whose counterexample does shrink reports one rarely, so most runs never
-- see it. On a run that reaches neither, nothing exercises the `Shrinkable GenProgram` instance, and a
-- change to it would stay invisible.
--
-- This diagnostic closes that hole. It minimizes each sampled program against a property that always fails,
-- and it reports how far the shrinker reduced the program, together with the two invariants that matter. It
-- is a diagnostic and not a property behind a gate, because it measures the quality of the shrinker and it
-- asserts no fact about Strata.

/-- Run the whole-program shrinker on fresh samples, and report how far it reduces them. The action also
    checks that each candidate is well typed, and that no reduction leaves a `requires` clause with no
    function.

    The target property is `sizeProgram p ≤ 3`. Almost every generated program fails it, and a program that
    shrinks still fails it. Therefore the minimizer runs to its fixed point, and the ratio in the report
    measures how far the shrinker reaches, and not an early stop.

    The result is the number of the candidates, the number of the candidates that are not well typed, and
    the number of the reductions that leave a `requires` clause with no function. The last two values must
    be 0. -/
def programShrinkDiagnostic (numTrials : Nat) : IO (Nat × Nat × Nat) := do
  let samples := max 1 (min 20 numTrials)
  let mut candidates := 0
  let mut illTyped := 0
  let mut stranded := 0
  let mut sizeBefore := 0
  let mut sizeAfter := 0
  let mut declsBefore := 0
  let mut declsAfter := 0
  for _ in [0:samples] do
    let prog ← ProgramGen.sample 6
    -- Each candidate of one step must be well typed, and none of them may leave a `requires` clause with no
    -- function. That is the one form of ill-formedness that the typechecker does not catch. Read
    -- `funcPreconditionsScoped`.
    let cands := shrinkProgram prog
    candidates := candidates + cands.length
    illTyped := illTyped + (cands.filter (!progTypeChecks ·)).length
    stranded := stranded + (cands.filter (fun c => c.decls.any fun
      | .func f _ => !funcPreconditionsScoped f
      | .recFuncBlock fs _ => fs.any (!funcPreconditionsScoped ·)
      | _ => false)).length
    let minimized := minimizeProgramCounterexample (fun p => sizeProgram p ≤ 3) 400 prog
    sizeBefore := sizeBefore + sizeProgram prog
    sizeAfter := sizeAfter + sizeProgram minimized
    declsBefore := declsBefore + prog.decls.length
    declsAfter := declsAfter + minimized.decls.length
  IO.println s!"    {samples} programs: size {sizeBefore} → {sizeAfter}, \
    decls {declsBefore} → {declsAfter}"
  IO.println s!"    {candidates} candidates emitted; {illTyped} ill-typed, \
    {stranded} with a stranded `requires` (both must be 0)"
  pure (candidates, illTyped, stranded)

-- ── The coverage of a call to a derived function of a datatype ────────

/-- Draw programs, and report how often the body of a generated function, procedure or axiom **calls** a
    derived function of an earlier datatype. The report gives a count for each family, which is a
    constructor, a tester, a safe accessor and an unsafe accessor.

    This is a *statistic about the coverage*, and not a property with a verdict. The generator can draw a
    program whose bodies call nothing. The statistic matters, because the important failure for this part of
    the generator is a silent fall to zero, and no property whose value is always true would catch that.

    The result is the number of the programs, the number that hold a datatype, the number that hold such a
    call, and one count for each of the four families. -/
def derivedCallCoverage (samples maxSize : Nat) (coverageNumDecls : Nat := 10) :
    IO (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
  let mut drawn := 0
  let mut withDt := 0
  let mut withCall := 0
  let mut ctors := 0
  let mut testers := 0
  let mut accs := 0
  let mut uaccs := 0
  -- This action does *not* use the `Arbitrary GenProgram` instance, whose size grows with the harness. Such
  -- a call needs a block of datatypes *and* a later function or procedure in the same program. The small
  -- draws of the property suite therefore almost never hold one. This action measures the coverage at a
  -- fixed and realistic number of declarations.
  for i in [:samples] do
    let r ← (try
      let prog ← Plausible.Gen.run
        (retryGen 30000 (ProgramGen.genProgram (G := Plausible.Gen) coverageNumDecls {})
         : Gen Core.Program) (4 + i % (maxSize + 1))
      pure (some prog)
     catch _ => pure none)
    match r with
    | none => pure ()
    | some prog =>
      drawn := drawn + 1
      unless (datatypeBlocks prog).isEmpty do withDt := withDt + 1
      if mentionsDerivedFunction prog then
        withCall := withCall + 1
        let (c, t, a, u) := calledByFamily prog
        unless c.isEmpty do ctors := ctors + 1
        unless t.isEmpty do testers := testers + 1
        unless a.isEmpty do accs := accs + 1
        unless u.isEmpty do uaccs := uaccs + 1
  pure (drawn, withDt, withCall, ctors, testers, accs, uaccs)

/-- Print the report of `derivedCallCoverage`. The action never changes the exit code, because it gives a
    distribution and asserts nothing. -/
def printDerivedCallCoverage (samples maxSize : Nat) : IO Unit := do
  let (drawn, withDt, withCall, ctors, testers, accs, uaccs) ←
    derivedCallCoverage samples maxSize
  IO.println s!"  programs drawn: {drawn}/{samples} (declaring >= 1 datatype: {withDt})"
  IO.println s!"  bodies calling an ADT-derived function: {withCall}"
  IO.println s!"    constructors {ctors} | testers {testers} \
| safe accessors {accs} | unsafe accessors {uaccs}"
  if withDt > 0 && withCall == 0 then
    IO.println "  NOTE: no derived calls in this run -- if persistent, this is the \
regression the ADT-derived-function work fixed."

-- ── The generation of a block of datatypes ───────────────────────────
--
-- The two wrappers below use the *same* generator, and they differ only in how each one assembles a block,
-- because the properties that they feed ask different questions:
--
--   * `GenAdtBlock` is one draw of `DatatypeGen.genMutuallyRecursiveDatatypes`, which gives an ordinary
--     block whose datatypes usually reference each other. It feeds each `adt:` property of
--     `StrataTests/Adt.lean`. Those properties are the two pure companions of the law properties for SMT,
--     and the property about the scope of an eliminator, which is not about the independent shape.
--   * `GenIndepBlock` joins independent draws of one datatype each, from
--     `MutualBlockShape.genIndependentBlock`, so no field can name another datatype of the block. It feeds
--     each `mutual:` property of `StrataTests/Mutual.lean`.
--
-- Both wrappers draw at `maxSize := 0`. At a larger size, `genArgTy` emits an arrow, and
-- `validateDatatypesForSMT` refuses the whole block for a field of a function type. The share of the blocks
-- with no arrow therefore falls sharply, and most of the budget would go to a block that no solver ever
-- sees. A larger size belongs where the refusals are the point: `AdtLawsSmt.adtSolverAcceptsQueryAction`
-- draws over a schedule of sizes, because it *wants* those refusals.

/-- A generated `mutual … end` block of the ordinary shape. -/
structure GenAdtBlock where
  block : Lambda.MutualDatatype Unit

/-- A generated `mutual … end` block whose datatypes are independent in pairs. -/
structure GenIndepBlock where
  block : Lambda.MutualDatatype Unit

instance : Repr GenAdtBlock where
  reprPrec b _ := StrataGenerators.MutualBlockShape.renderBlock b.block

instance : Repr GenIndepBlock where
  reprPrec b _ := StrataGenerators.MutualBlockShape.renderBlock b.block

/-- Shrink a block by a removal of one datatype. A `MutualDatatype` is a plain `List`, so a removal carries no
    proof obligation, because each datatype holds its own field that says that its list of constructors is not
    empty. The shrinker excludes the empty list, because `validateMutualBlock` rejects an empty block.

    A candidate with fewer than two datatypes makes each `mutual:` property hold with no content, and the
    harness discards a candidate that no longer fails. Therefore the shrinker cannot report a block of one
    datatype as a counterexample. -/
private def shrinkBlock (block : Lambda.MutualDatatype Unit) :
    List (Lambda.MutualDatatype Unit) :=
  if block.length ≤ 1 then []
  else (List.range block.length).map (fun i => block.eraseIdx i)

instance : Shrinkable GenAdtBlock where
  shrink b := (shrinkBlock b.block).map (⟨·⟩)

instance : Shrinkable GenIndepBlock where
  shrink b := (shrinkBlock b.block).map (⟨·⟩)

instance : Arbitrary GenAdtBlock where
  arbitrary := do
    let block ← DatatypeGen.genMutuallyRecursiveDatatypes (G := Plausible.Gen)
      (maxSize := 0)
    pure ⟨block⟩

instance : Arbitrary GenIndepBlock where
  arbitrary := Gen.sized fun s => do
    -- Between two and four datatypes. A `mutual` block of one datatype gives each property no content, and a
    -- property needs two or more datatypes to be about the *block* and not about one datatype.
    let extra := min 2 (s / 30)
    let block ← StrataGenerators.MutualBlockShape.genIndependentBlock
      (G := Plausible.Gen) (extra + 1) (maxSize := 0)
    pure ⟨block⟩

-- ── The diagnostic for the coverage of a block of datatypes ──────────

/-- Report what the suites over a block drew. The report gives the number of the blocks that held two or more
    datatypes, the number whose datatypes had the same type parameters, which is the condition that
    `elimFuncs` assumes, the number that `addMutualBlock` of Strata accepted, the number that passed the
    `blockIsSmtSafe` screen of the law properties behind the `--smt` gate, and the number of the independent
    draws that truly were independent.

    The action prints a diagnostic, and it never changes the exit code. The reason is the reason for each
    other report of coverage in this suite: a property that holds on blocks that each hold one datatype, or
    that Strata rejects, tested nothing. -/
def datatypeBlockCoverage (samples : Nat) : IO (Nat × Nat × Nat × Nat × Nat) := do
  let mut multi := 0
  let mut uniform := 0
  let mut accepted := 0
  let mut smtSafe := 0
  let mut indep := 0
  for i in List.range samples do
    let block ← DatatypeGen.sample (maxSize := i % 3)
    if block.length ≥ 2 then multi := multi + 1
    if StrataGenerators.MutualBlockShape.blockParamsUniform block then
      uniform := uniform + 1
    if StrataGenerators.AdtLaws.blockAccepted block then accepted := accepted + 1
    if StrataGenerators.AdtLaws.blockIsSmtSafe block then smtSafe := smtSafe + 1
    let ind ← StrataGenerators.MutualBlockShape.genIndependentBlock (G := IO) 1
    if StrataGenerators.MutualBlockShape.isIndependentBlock ind then indep := indep + 1
  pure (multi, uniform, accepted, smtSafe, indep)

/-- Print the report about the coverage of the blocks. -/
def printDatatypeBlockCoverage (samples : Nat) : IO Unit := do
  let (multi, uniform, accepted, smtSafe, indep) ← datatypeBlockCoverage samples
  IO.println s!"  ordinary blocks drawn: {samples} \
(>= 2 datatypes: {multi} | uniform type params: {uniform})"
  IO.println s!"    accepted by addMutualBlock: {accepted} | \
SMT-safe (arrow-free, no bitvec 0, bare SMT symbols): {smtSafe}"
  IO.println s!"  independent blocks drawn: {samples} (actually independent: {indep})"
  if accepted < samples then
    IO.println s!"  NOTE: {samples - accepted} block(s) rejected by addMutualBlock -- \
DatatypeGen does not thread reserved names across the datatypes of one block, so two \
of them can declare a constructor of the same name."

-- ── The diagnostics that run at `IO` ─────────────────────────────────

/-- Draw erased terms, and print the error message of `resolve` behind each counterexample to the property
    about a resolve after an erasure. For each failure, the action shows the erased term and the result of
    `resolve` itself. It also gives a count for each different message. The result is the number of the
    counterexamples. -/
def printResolveErrors (numTrials maxSize : Nat) : IO Nat := do
  let attempts := max numTrials 2000
  let mut shown := 0
  let mut msgTally : List (String × Nat) := []
  IO.println "    ── resolve error messages on counterexamples ──"
  for i in List.range attempts do
    let size := i % (maxSize + 1)
    let te ← try Gen.run (Arbitrary.arbitrary (α := ResolveTypedExpr)) size
             catch _ => pure ⟨.const () (.boolConst true), .bool⟩
    match resolveErrorMessage te with
    | none => pure ()
    | some msg =>
      -- Print the first few examples, each as the erased term and the error.
      if shown < 15 then
        IO.println s!"    erased: {ppExpr (eraseAllTypes te.expr)}"
        IO.println s!"      → {msg}"
        shown := shown + 1
      -- Count each different message. The count reads the string of the error, and it ignores the identifier
      -- of a type variable.
      let key := msg
      msgTally := match msgTally.find? (·.1 == key) with
        | some _ => msgTally.map (fun (m, c) => if m == key then (m, c + 1) else (m, c))
        | none => (key, 1) :: msgTally
  IO.println ""
  IO.println s!"    distinct resolve error messages ({msgTally.length}):"
  for (m, c) in msgTally.reverse do
    IO.println s!"      [{c}×] {m}"
  return shown

-- ── The checks of a round trip that run at `IO` ──────────────────────
--
-- These two checks do not fit `checkIO`, because neither of them is a plain `Prop`. Each of them runs at
-- `IO`, shrinks its own counterexample, and prints a smallest reproducer as it goes. Each of them gives the
-- tuple that `checkIO` gives, which is the verdict, the number of the samples, the number of the tests and
-- the message. Therefore a driver can put either of them into a suite as an individual node.

/-- Print each generated function to concrete syntax, and parse the output again, which must give the same
    text. The action shrinks the first few failures of a parse and the first few differences, and it prints a
    smallest reproducer for each of them. This check changes the exit code, because a function that is legal
    by construction and that fails the round trip is a defect of the printer or of the parser. -/
def roundtripFunctionAction (numTrials maxSize : Nat) : IO (Bool × Nat × Nat × Option String) := do
  let total := min numTrials 200
  let mut rtOk := 0
  let mut rtParseFail := 0
  let mut rtMismatch := 0
  for i in List.range total do
    let size := i % (maxSize + 1)
    let gf ← try Gen.run (Arbitrary.arbitrary (α := ClosedGenFunction)) size
             catch _ => pure ⟨default⟩
    let s := formatFuncAsProgram gf.func
    match ← parseCoreProgram s with
    | none =>
      -- A name that is legal by construction and that the parser cannot read is a defect of the printer or
      -- of the parser.
      rtParseFail := rtParseFail + 1
      if rtParseFail ≤ 3 then
        -- Shrink to a smallest witness that the parser cannot read, and show the error of the parser.
        let minF ← shrinkWhile failsRoundtripParseFail 1000 gf.func
        let ms1 := formatFuncAsProgram minF
        let err := match ← parseCoreProgramErr ms1 with
                   | .error e => e | .ok _ => "<parsed unexpectedly>"
        IO.println s!"    FAIL (parse): original: {s.replace "\n" " " |>.take 80}"
        IO.println s!"      shrunk (size {sizeFunc minF}): {ms1.replace "\n" " "}"
        IO.println s!"      parser error:                 {err.take 160}"
    | some ast2 =>
      let s2 := (Core.formatProgram ast2).pretty
      if s == s2 then
        rtOk := rtOk + 1
      else
        rtMismatch := rtMismatch + 1
        if rtMismatch ≤ 3 then
          -- Shrink this difference to a smallest witness that the parser reads and that the round trip
          -- changes.
          let minF ← shrinkWhile failsRoundtripParsed 1000 gf.func
          let ms1 := formatFuncAsProgram minF
          let ms2 ← (do match ← parseCoreProgram ms1 with
                        | some a => pure (Core.formatProgram a).pretty
                        | none => pure "<parse-failed>")
          IO.println s!"    FAIL (mismatch): original: {s.replace "\n" " " |>.take 80}"
          IO.println s!"      shrunk (size {sizeFunc minF}): {ms1.replace "\n" " "}"
          IO.println s!"      re-formatted to:              {ms2.replace "\n" " "}"
  if rtParseFail == 0 && rtMismatch == 0 then
    pure (true, rtOk, total, none)
  else
    pure (false, rtOk, total,
      some s!"{rtParseFail} parse-failures, {rtMismatch} mismatches, {rtOk} ok")

/-- A probe for an identifier that holds a special character. For each position, which is the name of the
    function, a type argument or a binder, the action renders a legal identifier that holds a special
    character, and it checks the round trip. It prints one reproducer for each different triple of a
    position, a result and a class of a character.

    This is a **diagnostic**. It reports how many probes fail, and it does not change the exit code, because
    the round trip of a special character is a known limit. The result is the number of the probes that fail
    and the number that succeed. -/
def specialCharProbeDiagnostic (numTrials maxSize : Nat) : IO (Nat × Nat) := do
  let positions := [IdentPosition.funcName, .typeArg, .binder]
  let mut probeOk := 0
  let mut probeFail := 0
  let mut shownReprs : List String := []
  for i in List.range (min numTrials 200) do
    let size := i % (maxSize + 1)
    let name ← try Gen.run genQuotedName size catch _ => pure "x"
    for pos in positions do
      match ← probeIdentRoundtrip pos name with
      | none => probeOk := probeOk + 1
      | some (rendered, outcome) =>
        probeFail := probeFail + 1
        -- One reproducer for each different triple of a position, a result and the class of the character
        -- that caused the failure. Therefore two different causes stay separate.
        let cls :=
          if name.any (· == '.') then "dot"
          else if name.any (· == '|') then "pipe"
          else if name.any (· == '\\') then "backslash"
          else if name.any (· == '\'') then "apostrophe"
          else if name.toList.head?.map (·.isDigit) == some true then "leading-digit"
          else "other"
        let isParseFail := outcome.startsWith "parse-failure"
        let key := s!"{pos.label}/{if isParseFail then "parse" else "mismatch"}/{cls}"
        if !shownReprs.contains key then
          shownReprs := key :: shownReprs
          IO.println s!"    REPRO [{pos.label}] class={cls} name={name.quote}"
          IO.println s!"           rendered: {rendered.replace "\n" " "}"
          if isParseFail then
            IO.println s!"           {outcome.replace "\n" " "}"
          else
            IO.println s!"           reparsed: {outcome.replace "\n" " "}"
  return (probeFail, probeOk)

/-- A diagnostic about the coverage of the printer. The action draws whole programs, and it counts each
    *different* message about a conversion that `Core.formatProgram` writes, in the order of the counts. It
    also reports, of the programs for which the printer wrote a message, how many the parser still reads.
    Those are the dangerous ones, where a placeholder gave a program that is valid syntax and that is
    **different**, and the property about a round trip over a string cannot find such a case.

    This is a **diagnostic**, and it does not change the exit code. The property behind the gate is the one
    that says that the printer writes no message about a conversion. The task of this action is to name the
    *constructs* that cause a message, over a whole sample, and a view of one counterexample cannot give
    that.

    The whole-program shrinker does minimize the witness of the gated property, and only when the draw type
    checks, because its filter for a candidate is `Program.typeCheck`. On a draw that holds a known gap, the
    harness reports the witness at its full size, and these counts are then the only guide to the cause.

    The result is the number of the programs for which the printer wrote a message, the number of the
    programs that the action drew, and the number that the parser reads although the printer wrote a
    message. -/
def printerErrorDiagnostic (numTrials maxSize : Nat) : IO (Nat × Nat × Nat) := do
  let total := min numTrials 60
  let mut withErrors := 0
  let mut reparsed := 0
  let mut sampled := 0
  let mut tally : List (String × Nat) := []
  for i in List.range total do
    let size := i % (maxSize + 1)
    let gp ← try Gen.run (Arbitrary.arbitrary (α := GenProgram)) size
             catch _ => pure ⟨{ decls := [] }⟩
    -- A draw that used up its retries gives the empty program. The action scores such a draw in neither
    -- direction.
    if gp.prog.decls.isEmpty then continue
    sampled := sampled + 1
    let s := (Core.formatProgram gp.prog).pretty
    let lines := StrataGenerators.PrinterCoverage.strataErrorLines s
    if !lines.isEmpty then
      withErrors := withErrors + 1
      for line in lines.dedup do
        tally := match tally.find? (·.1 == line) with
          | some _ => tally.map (fun (m, c) => if m == line then (m, c + 1) else (m, c))
          | none => (line, 1) :: tally
      -- Does the parser read the text that the printer gave?
      match ← parseCoreProgram (StrataGenerators.PrinterCoverage.printedText s) with
      | some _ => reparsed := reparsed + 1
      | none => pure ()
  IO.println s!"    {withErrors}/{sampled} programs logged a conversion error"
  IO.println s!"    {reparsed} of those still re-parsed (placeholder ⇒ silently different program)"
  IO.println s!"    distinct messages ({tally.length}), most frequent first:"
  for (m, c) in (tally.mergeSort (fun a b => a.2 > b.2)) do
    IO.println s!"      [{c}×] {m}"
  -- The disagreement about the width of a bitvector. The action reports it here too, because several of the
  -- messages above are instances of it. This part is deterministic, so it is a scan and not a draw.
  -- `Function.typeCheck` accepts each width, the printer writes five of them, and those five are *not* the
  -- powers of two.
  let divergent := StrataGenerators.PrinterCoverage.divergentBvWidths 64
  IO.println s!"    bitvec widths 0..63: {64 - divergent.length} printable, {divergent.length} typecheck-but-unprintable"
  IO.println s!"      printable: {StrataGenerators.PrinterCoverage.printableBvWidths}"
  IO.println s!"      first divergent: {divergent.take 12}{if divergent.length > 12 then " …" else ""}"
  return (withErrors, sampled, reparsed)
