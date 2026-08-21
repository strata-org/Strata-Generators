-- The whole-program generator and its shrinker, the program typechecker oracle
-- (`progTypeChecks`) and `sizeProgram`.
import StrataGenerators.ProgramGen.Shrink
-- `programFuncs` / `programBodies` / `declNames` / `nodup` / `evalOver`, and the
-- phase-running plumbing the properties here reuse verbatim rather than re-derive.
import StrataGenerators.ProgramGen.UnprovenTransforms
-- `opNames`, `datatypeBlocks`, and the derived-operator projections.
import StrataGenerators.ProgramGen.TestSupport
-- The pass under test, and the naming convention it renames through.
import Strata.Transform.MonomorphizeFunctions
import Strata.Languages.Core.NameMangling
-- `Core.typeCheck`, which is the only typechecker entry point that accepts a
-- *factory* argument — and the output of this pass can only be checked against
-- the factory the pass itself produced.
import Strata.Languages.Core.Verifier

open Lambda Core Imperative
-- `progTypeChecks`, the whole-program typechecker oracle, and the program shrinker.
open StrataGenerators.Program.TestSupport
-- `runPhaseSt` and `mkState`: a pipeline phase run from a freshly-seeded transform
-- state, returning the `(changed, output)` pair *and* the final state. The final
-- state is what carries the rebuilt factory, which half the properties here read.
open StrataGenerators.Procedure.TestSupport
-- `opNames` (every `.op` name of an expression) and `datatypeBlocks`.
open ProgramGen.TestSupport
-- `programFuncs`, `programBodies`, `declNames`, `nodup`, `evalOver`, `programFactory`.
open StrataGenerators.Program.UnprovenTransforms
-- `mangleFuncName` / `demangleFuncName` / `demangledBaseName` / `mangleTyArgs`.
open Core.NameMangling

/-!
# Check predicates for `MonomorphizeFunctions`

`Strata/Transform/MonomorphizeFunctions.lean` specializes every polymorphic
top-level function (`Decl.func`, `Decl.recFuncBlock`) and every polymorphic
`Factory` function once per distinct ground type instantiation reached from a
non-function context, renames every reference to the specialized copy, and
**drops the polymorphic originals that nothing reached**. It runs immediately
after `typeCheckPhase` in `Core.corePipelinePhases`, so that the SMT encoder, the
symbolic evaluator and the downstream backends can assume monomorphic input.

Upstream tests the pass with fourteen hand-written `#guard_msgs` goldens, each
asserting the same three predicates on one fixed program: no top-level function
keeps its type parameters, no factory entry keeps its type parameters, and the
output typechecks. This module states those claims *over the generator*, and adds
the ones a fixed example set cannot reach.

## Why a generated program is a live input, and why it needs no typechecking first

The pass reads a call's instantiation off the type annotation the typechecker
attaches to the `.op` node, which is why it is ordered after `typeCheckPhase`.
A generated program already carries that annotation: `genIndirPolyCore` builds
`.op () name (some fullArrowTy)` with the instantiation baked in
(`HasTypeAGen/Core.lean`), and `ProgramGen` registers each *declared*
polymorphic function into the `pctx` that feeds body generation, so a generated
body really does call a generated polymorphic function at a ground
instantiation.

The pass can therefore be run on a draw directly. That matters, because
`Program.typeCheck` rejects about 60 percent of generated programs for three
documented pre-existing reasons (see `ProgramGen/Shrink`), and gating every
property on it would throw away most of the signal. Only the properties whose
*claim* presupposes a well-typed input carry the `!progTypeChecks p ||` guard —
`checkMonoOutputTypechecks` and `checkMonoEvalAgreement`.

## Seeding: `Core.Factory`, exactly as upstream does

`runPhaseSt` seeds the transform state with `Core.Factory` (via `mkState`), which
is precisely upstream's own `monoFns` seeding
(`{ CoreTransformState.emp with factory := Core.Factory }`). `runPhaseWithFuncs`,
which additionally pushes the program's own functions into the factory, is
deliberately *not* used: it would put each declared polymorphic function into the
factory as well as into `p.decls`, so `checkMonoFactoryMonomorphic` would then
demand that the pass specialize the same function twice over, under two different
`FuncSource`s, and a red result would say more about the seeding than the pass.

One consequence is worth stating plainly, because it bounds what
`checkMonoDerivedOpsRewritten` can see: `Core.Factory` does **not** hold the
operators a generated datatype block derives (its constructors, testers and field
accessors). Those reach the factory only when a program is run through
`Core.Verifier`. `monoSeedFactoryWithDerived` pushes them in for the one property
that is about them, and that property is self-calibrating — its premise is
"reference to a function that is polymorphic *in the seed factory*", so it goes
vacuous rather than red when the premise is empty.

## Measured: the default draw does not reach the pass

**Read this before trusting a green tick.** Over 40 draws from the default
`Arbitrary GenProgram`, the pass produced **zero** specializations — under
`Core.Factory` seeding *and* under `monoSeedFactoryWithDerived`. Every predicate
below except the two `funcDecl` ones was therefore green vacuously. The cause is
a chain of three facts about the generator, none of them a defect in it:

* A declared polymorphic function is registered into `GenState.pctx`
  (`ProgramGen.funcPolyOpEntry`), and `pctx` is consumed by `genAxiom` **only**.
  Function and procedure bodies see `derivedPctx`, the datatype-derived schemes
  alone. So a generated polymorphic *function* is callable from an axiom and
  nowhere else.
* The default runner draws at most five declarations
  (`numDecls := max 2 (min 5 (2 + s / 25))` in `TestScaffold`), and the axiom
  weight is 1 of six kinds. Across 25 draws, **0** axiom declarations appeared.
* `processTopDecls` seeds the worklist from procedures, axioms, `distinct` and
  *monomorphic* functions. A reference sitting in a polymorphic function's body
  is reached only transitively, so it cannot start a specialization on its own.

Two things follow for whoever wires these up. First, state the coverage: register
`monoSpecializationCount` as a Tyche axis or a `Diagnostic`, so a run says how
often it reached the pass instead of leaving it to be assumed — `monoReachedPass`
is the boolean form. Second, a live draw needs a generator that is *tuned*, not
the default: a larger `numDecls` through `TestDecl.forAll` with an explicit
`PropertyRunner` raises the chance of an axiom-plus-polymorphic-function pair, and
the durable fix is upstream of this module — letting procedure bodies draw from
`pctx` rather than only `derivedPctx` would make a call to a declared polymorphic
function an ordinary event rather than a coincidence.

The two `funcDecl` predicates are the exception, and are reachable today: one of
40 draws carried a polymorphic `funcDecl` statement, and it failed
`checkMonoStmtFuncDeclsMonomorphic` as predicted. Budget trials accordingly —
that is roughly a 2.5 percent hit rate.

## What each group of predicates claims

* `checkMonoAllFuncsMonomorphic`, `checkMonoFactoryMonomorphic`,
  `checkMonoOutputTypechecks`, `checkMonoIdempotent` — upstream's three goldens
  quantified, plus idempotence, which upstream does not state at all.
* `checkMonoStmtFuncDeclsMonomorphic`, `checkMonoStmtFuncDeclRefsRewritten` — the
  statement-level `funcDecl`. `allFuncsMonomorphic` inspects `p.decls` only, and
  the pass's two traversals both ignore a `funcDecl` statement:
  `Command.mapExprM` falls through it on its catch-all, and
  `Statement.collectExprs` returns `[]` for it. So a block-local polymorphic
  function is invisible to the pass, and a block-local body that calls a
  polymorphic top-level function is neither collected (no specialization is
  seeded) nor rewritten (the name is left alone) while the original is dropped as
  unreached. `genFuncDeclStmt` draws exactly this shape, so these two are
  expected to be red; whether that is a defect or a documented scope boundary is
  the upstream conversation, and `Expectation.knownFailure` is where the answer
  belongs.
* `checkMonoTypeDeclsUnchanged`, `checkMonoPolyDatatypesRemain`,
  `checkMonoDerivedOpsRewritten` — the pass monomorphizes a polymorphic
  datatype's *derived functions* but not the datatype *declaration*:
  `processTopDecls` passes a `.type` declaration through on its catch-all. These
  three state that asymmetry as a fact rather than assuming it, so that a future
  upstream change in either direction shows up.
* `checkMonoMangledBaseWasPolymorphic`, `checkMangleRoundtripAt`,
  `checkMangleDistinctAt`, `checkMonoOutputNamesNodup`,
  `checkMonoNoPolyProgramUnchanged`, `checkMonoDeclOrderPreserved` — the naming
  convention. Injectivity of `$__mono#<base>#<tyargs>` is load-bearing for the
  whole scheme (two specializations that mangle alike collapse into one
  declaration), and `mangleTy`'s own docstring concedes that the arity prefix is
  "documentary rather than disambiguating".
* `checkMonoEvalAgreement` — the semantic one. See its docstring for what is and
  is not claimed.
-/

namespace StrataGenerators.Mono

/-! ## Running the pass -/

/-- The pipeline phase under test. -/
def monoPhase : Core.PipelinePhase := Core.monomorphizeFunctionsPipelinePhase

/-- The SMT-trigger meta-operators, which the CST converter matches by name and
    which are therefore left polymorphic on purpose. Kept in step with
    `MonomorphizeFunctions.collectPolymorphicFuncDeclsFromFactory`, which excludes
    exactly these from the set of functions to specialize — so a predicate here
    that failed to exclude them would report the pass's own deliberate exemption
    as a violation. -/
def isTriggerMetaOp (name : String) : Bool :=
  name == "TriggerGroup.addTrigger" || name == "TriggerGroup.empty" ||
  name == "Triggers.addGroup"       || name == "Triggers.empty"

/-- The pass run on `p` from a freshly-seeded state: the `changed` flag, the
    output program, and the final transform state (whose `factory` is the rebuilt
    one — the polymorphic originals dropped and the specialized copies added).

    `none` when the pass raised a diagnostic, which it does on a growing cycle
    (it calls that "non-uniform polymorphic recursion"). Every predicate below
    reads `none` as "no claim to make", so a diagnostic never reads as a
    violation; `checkMonoSucceeds` is the property that scores the diagnostic
    itself. -/
def runMono (p : Program) :
    Option ((Bool × Program) × Transform.CoreTransformState) :=
  runPhaseSt monoPhase p

/-- `runMono` with the seed factory named explicitly, for a property that needs
    the pass to see something `Core.Factory` does not hold — a datatype's derived
    operators, say. `runMono` is this at `Core.Factory`, which is upstream's
    seeding; anything else is a deliberate deviation and should say why. -/
def runMonoWith (F : Lambda.Factory CoreLParams) (p : Program) :
    Option ((Bool × Program) × Transform.CoreTransformState) :=
  match Transform.runWith p monoPhase.transform { mkState p with factory := F } with
  | (.ok r, st) => some (r, st)
  | (.error _, _) => none

/-- The pass run a second time, threaded from the first run's transform state.
    `none` when the second run raised a diagnostic — which, unlike a diagnostic on
    the *first* run, is a violation rather than an absence of claim, so
    `checkMonoIdempotent` asserts this is `some`. -/
def runMonoAgain (r : (Bool × Program) × Transform.CoreTransformState) :
    Option (Bool × Program) :=
  match Transform.runWith r.1.2 monoPhase.transform r.2 with
  | (.ok x, _) => some x
  | (.error _, _) => none

/-- Whether the pass returned at all. Separated from every other predicate so
    that a diagnostic is scored once, by a property that is about the diagnostic,
    instead of silently making the others vacuous. -/
abbrev checkMonoSucceeds (p : Program) : Prop := (runMono p).isSome = true

/-- The output program alone. -/
def monoOut (p : Program) : Option Program := (runMono p).map (·.1.2)

/-! ### Total projections of the output

Every claim below is stated as an *equality at the top level*, and these exist to
make that possible. The obvious phrasing, `∀ p' ∈ monoOut p, f p' = []`, is
decidable but prints `issue: ⋯ does not hold` — Plausible's `PrintableProp` reads
the top-level shape, and a bounded `∀` is not a shape it can render, so such a
property is no more informative than a `Bool`. Projecting through `Option.elim`
with the *vacuous* value as the default keeps the same meaning (a diagnostic is
still no claim) while putting an `=` on top, which prints both sides. -/

/-- `f` applied to the output, or `dflt` when the pass raised a diagnostic. -/
def onOutput (p : Program) (dflt : α) (f : Program → α) : α :=
  ((monoOut p).map f).getD dflt

/-- The `(changed, output)` pair the pass reported, or `(false, p)` on a
    diagnostic — which reads as "unchanged", the vacuous value here. -/
def monoChangedOut (p : Program) : Bool × Program :=
  (((runMono p).map (·.1)).getD (false, p))

/-- The rebuilt factory alone. -/
def monoFactory (p : Program) : Option (Lambda.Factory CoreLParams) :=
  (runMono p).map (·.2.factory)

/-! ## Naming the polymorphic functions the pass can see -/

/-- The polymorphic functions a program declares, by name. These are the
    `Decl.func` and `Decl.recFuncBlock` entries `collectPolymorphicFuncDecls`
    indexes, so this is the set whose originals the pass is entitled to drop. -/
def polyProgramFuncNames (p : Program) : List String :=
  (programFuncs p).filterMap fun f =>
    if f.typeArgs.isEmpty then none else some f.name.name

/-- The polymorphic entries of a factory, minus the trigger meta-operators. -/
def polyFactoryNames (F : Lambda.Factory CoreLParams) : List String :=
  F.toArray.toList.filterMap fun lf =>
    if !lf.typeArgs.isEmpty && !isTriggerMetaOp lf.name.name then some lf.name.name
    else none

/-- Every name the pass will specialize and then drop, for the seed factory `F`.
    A reference to one of these surviving in the output is a dangling reference:
    the declaration it names is gone. -/
def polyNames (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : List String :=
  polyProgramFuncNames p ++ polyFactoryNames F

/-- The references in `ops` that still name one of the `dropped` originals.

    Every "no dangling reference" claim below is `survivingPolyRefs … = []`, and
    that shape is the point: a `Prop`-valued equality against `[]` lets Plausible
    print the *offending names* (`issue: ["f"] = [] does not hold`), where a
    `Bool`-valued `List.all` could only report `false`. -/
def survivingPolyRefs (dropped ops : List String) : List String :=
  (ops.filter dropped.contains).eraseDups

/-- `Core.Factory` with each operator that the program's datatype blocks derive
    pushed in — the constructors, testers and field accessors of a generated
    `mutual … end` block.

    `Core.Factory` holds none of these: they reach a factory only through
    `Core.Verifier`. So without this, a reference to `List..head` is a reference
    to a function the pass has never heard of, and every claim about a *derived*
    operator would be vacuous under the default seeding. `pushIfNew` keeps the
    first entry under a name, so a derived name cannot displace a builtin. -/
def monoSeedFactoryWithDerived (p : Program) : Lambda.Factory CoreLParams :=
  (datatypeBlocks p).foldl (init := Core.Factory) fun F block =>
    match ProgramGen.blockDerivedFactory block with
    | none => F
    | some DF => DF.toArray.foldl (fun F lf => F.pushIfNew lf) F

/-! ## Collecting operator references

`ProgramGen.TestSupport.stmtOpNames` deliberately stops at a `funcDecl` statement
and at a `call`'s arguments. Both matter here: the `funcDecl` statement is the
subject of `checkMonoStmtFuncDeclRefsRewritten`, and a `call`'s `inArg` is an
expression the pass *does* rewrite (`Command.mapExprM` descends into it), so a
predicate that could not see it would miss a whole class of reference. Hence the
deeper traversal below rather than a reuse. -/

/-- The user-facing expressions of a syntactic function declaration — the node a
    `funcDecl` statement carries. Mirrors `MonomorphizeFunctions`'
    `expressionsFromFunction`, which is what the pass reads out of a *top-level*
    function, so the two views of "a function's expressions" cannot drift. -/
def pureFuncExprs (d : Imperative.PureFunc Expression) : List Expression.Expr :=
  d.body.toList ++ d.axioms ++ d.preconditions.map (·.expr) ++ d.measure.toList

/-- Every function a statement list declares through a `funcDecl` statement, at
    any depth. Invisible to `allFuncsMonomorphic`, which reads `p.decls`. -/
partial def funcDeclsOfStmts (ss : List Statement) :
    List (Imperative.PureFunc Expression) :=
  ss.flatMap fun s =>
    match s with
    | .funcDecl d _ => [d]
    | .block _ b _ => funcDeclsOfStmts b
    | .ite _ t e _ => funcDeclsOfStmts t ++ funcDeclsOfStmts e
    | .loop _ _ _ b _ => funcDeclsOfStmts b
    | _ => []

/-- Every `.op` name of a statement list, at any depth, **including** inside a
    `call`'s arguments and inside the declaration a `funcDecl` statement carries. -/
partial def stmtOpNamesDeep (ss : List Statement) : List String :=
  ss.flatMap fun s =>
    match s with
    | .cmd (.cmd c) =>
      match c with
      | .init _ _ (.det e) _ => opNames e
      | .set _ (.det e) _ => opNames e
      | .assert _ e _ => opNames e
      | .assume _ e _ => opNames e
      | .cover _ e _ => opNames e
      | _ => []
    | .cmd (.call _ args _) =>
      args.flatMap fun | .inArg e => opNames e | _ => []
    | .block _ b _ => stmtOpNamesDeep b
    | .ite c t e _ =>
      (match c with | .det x => opNames x | _ => []) ++
        stmtOpNamesDeep t ++ stmtOpNamesDeep e
    | .loop g m invs b _ =>
      (match g with | .det x => opNames x | _ => [])
        ++ (m.map opNames).getD []
        ++ invs.flatMap (fun q => opNames q.2)
        ++ stmtOpNamesDeep b
    | .funcDecl d _ => (pureFuncExprs d).flatMap opNames
    | _ => []

/-- The statements of a procedure body, or `[]` for a `.cfg` body.

    A generated procedure is always `.structured` — `StructuredToUnstructured` is
    a pass, not a shape the generator draws — so nothing here is lost. The `.cfg`
    case is spelled out rather than left to a catch-all so that a future generator
    that *does* draw one shows up as an obviously empty result instead of a
    silently wrong one. -/
def structuredBody (q : Procedure) : List Statement :=
  match q.body with
  | .structured ss => ss
  | .cfg _ => []

/-- The expressions of the declarations the pass treats as **always live** —
    procedures (contract clauses and body), axioms and `distinct`.

    This is the list the pass rewrites *in place*: `processTopDecls` visits these
    three declaration kinds, rewrites each, and pushes it back in the same
    position, adding and removing nothing. So the list has the same length and
    the same order before and after the pass, which is what lets
    `checkMonoEvalAgreement` compare positionally.

    Function bodies are deliberately excluded, and that exclusion is what makes
    the alignment true: the pass *adds* one declaration per specialization and
    drops the polymorphic originals, so any list that included function
    expressions would be a different length on the two sides. -/
def aliveExprs (p : Program) : List Expression.Expr :=
  p.decls.flatMap fun
    | .proc q _ =>
      q.spec.preconditions.values.map (·.expr) ++
      q.spec.postconditions.values.map (·.expr) ++
      Core.Statements.collectExprs (structuredBody q)
    | .ax a _ => [a.e]
    | .distinct _ es _ => es
    | _ => []

/-- Every `.op` name reachable in a program: the always-live declarations, plus
    every function's own expressions, plus the bodies of every function declared
    by a `funcDecl` statement. This is the view a dangling-reference claim needs,
    since a reference the pass failed to rewrite is a reference *somewhere*. -/
def allOpNames (p : Program) : List String :=
  (aliveExprs p).flatMap opNames
    ++ (programFuncs p).flatMap (fun f =>
         (f.body.map opNames).getD [] ++ f.axioms.flatMap opNames ++
         f.preconditions.flatMap (fun c => opNames c.expr) ++
         (f.measure.map opNames).getD [])
    ++ (p.decls.flatMap fun | .proc q _ => stmtOpNamesDeep (structuredBody q) | _ => [])

/-! ## Group A — upstream's goldens, quantified

The three predicates upstream asserts on each of its fourteen examples, plus
idempotence. Each is stated unconditionally except `checkMonoOutputTypechecks`,
whose claim presupposes a well-typed input. -/

/-- **No top-level function declaration keeps its type parameters.** The pass's
    headline postcondition, and the reason the SMT encoder is allowed to assume
    monomorphic input.

    Note the scope: `p.decls` only. A function declared by a `funcDecl`
    *statement* is not covered here — that is `checkMonoStmtFuncDeclsMonomorphic`,
    and the two are separate properties precisely because the pass treats them
    differently.

    Stated as `polyProgramFuncNames p' = []` rather than as a bounded `∀` over the
    declarations, because the two say the same thing and only the equality prints
    the counterexample: a failure reads `issue: ["f"] = [] does not hold`, naming
    the function that kept its type parameters. -/
abbrev checkMonoAllFuncsMonomorphic (p : Program) : Prop :=
  onOutput p [] polyProgramFuncNames = []

/-- **No entry of the rebuilt factory keeps its type parameters**, save the
    trigger meta-operators the pass exempts by name — which is exactly the
    exemption `polyFactoryNames` already applies. -/
abbrev checkMonoFactoryMonomorphic (p : Program) : Prop :=
  ((monoFactory p).map polyFactoryNames).getD [] = []

/-- **The output typechecks**, against the factory the pass itself produced.

    `Core.typeCheck` is the only entry point that takes a factory, and it has to
    be the *rebuilt* one: the output names `$__mono#f#int`, which exists nowhere
    else. Checking the output against `Core.Factory` would therefore fail for a
    reason that has nothing to do with the property.

    Guarded on the input typechecking, since a pass can only be blamed for what
    it does to well-typed input. The guard is an implication rather than a
    disjunction, which is what lets a failure print with the guard discharged. -/
abbrev checkMonoOutputTypechecks (p : Program) : Prop :=
  progTypeChecks p = true →
    ∀ r ∈ runMono p,
      (Core.typeCheck Core.VerifyOptions.quiet r.1.2
        (factory := r.2.factory)).toOption.isSome = true

/-- **The pass is idempotent**, and reports so: after one run every function is
    monomorphic, hence the second run has nothing to specialize, must return the
    same program, and must report `changed = false`.

    The second run is threaded from the *first run's* state, not from a fresh
    one. Re-seeding with `Core.Factory` would hand the second run back the
    polymorphic factory originals the first run dropped, so it would specialize
    them again and the property would be measuring the harness.

    The `isSome` conjunct is load-bearing: a `∀ s ∈ runMonoAgain r` alone would
    read a diagnostic on the *second* run as vacuous, and a second run that fails
    where the first succeeded is precisely a violation of idempotence. -/
abbrev checkMonoIdempotent (p : Program) : Prop :=
  (runMono p).bind runMonoAgain = (monoOut p).map (fun p' => (false, p'))

/-! ## Group B2 — the statement-level `funcDecl`

`allFuncsMonomorphic` reads `p.decls`. But a `funcDecl` *statement* carries an
`Imperative.PureFunc` with its own `typeArgs`, and both of the pass's traversals
skip it: `Command.mapExprM`'s catch-all (`| c => pure c`) returns a `.funcDecl`
unchanged, and `Statement.collectExprs` returns `[]` for it. So a block-local
polymorphic function keeps its type parameters, and a block-local body's call to
a polymorphic top-level function is neither seeded nor renamed — while the
original is dropped as unreached.

`genFuncDeclStmt` draws the declaration from `genFunction`, whose `typeArgs` come
from `genTypeArgs`, and threads `pctx` into the body, so both shapes are
reachable. Read a green tick on either of these as "not reached this draw" until
the Tyche `has_funcDecl` axis says otherwise. -/

/-- Every function a program declares through a `funcDecl` statement, from any
    procedure body. -/
def programStmtFuncDecls (p : Program) : List (Imperative.PureFunc Expression) :=
  p.decls.flatMap fun
    | .proc q _ => funcDeclsOfStmts (structuredBody q)
    | _ => []

/-- The names of the *polymorphic* functions a program declares through a
    `funcDecl` statement. The statement-level analogue of
    `polyProgramFuncNames`, and for the same reason: naming them is what lets the
    property below print which one kept its type parameters. -/
def polyStmtFuncDeclNames (p : Program) : List String :=
  (programStmtFuncDecls p).filterMap fun d =>
    if d.typeArgs.isEmpty then none else some d.name.name

/-- **No function declared by a statement keeps its type parameters** — the
    statement-level counterpart of `checkMonoAllFuncsMonomorphic`.

    Vacuous unless the draw holds a `funcDecl` statement whose declaration is
    polymorphic. -/
abbrev checkMonoStmtFuncDeclsMonomorphic (p : Program) : Prop :=
  onOutput p [] polyStmtFuncDeclNames = []

/-- **A statement-declared body's references are rewritten.** No expression of a
    `funcDecl` statement in the output may still name a function whose
    polymorphic original the pass dropped.

    Vacuous unless the draw holds a `funcDecl` whose body calls a polymorphic
    function; when it is not vacuous, a failure is a dangling reference and not a
    cosmetic one. -/
abbrev checkMonoStmtFuncDeclRefsRewritten
    (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  onOutput p [] (fun p' =>
    survivingPolyRefs (polyNames p F)
      (((programStmtFuncDecls p').flatMap pureFuncExprs).flatMap opNames)) = []

/-- **No reference to a dropped polymorphic original survives anywhere.** The
    unrestricted form of the claim above, over every expression of the output.

    Sharper than "the output typechecks" in one direction and weaker in another:
    it needs no well-typed input, but it checks only the *name*, not the
    instantiation. A reference renamed to a specialization that exists at the
    wrong instantiation passes this and fails the typechecker. -/
abbrev checkMonoNoPolyRefsSurvive
    (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  onOutput p [] (fun p' => survivingPolyRefs (polyNames p F) (allOpNames p')) = []

/-! ## Type declarations: monomorphized only through their derived functions

The pass handles `Decl.func`, `Decl.recFuncBlock` and the factory.
`processTopDecls` passes a `.type` declaration through untouched on its `| _ =>`
catch-all, so a polymorphic datatype declaration survives with its type
parameters intact — while the operators it *derives* are ordinary polymorphic
factory functions and so are specialized like any other.

That asymmetry is stated here as a fact rather than assumed. It is also the one
place where Lutze, Schuster and Brachthäuser's *The Simple Essence of
Monomorphization* (OOPSLA 2025) says Strata is incomplete rather than merely
different: their §2.2 treats type-parametric data types as a kind of polymorphism
in its own right, with constraints raised by the well-formedness judgment, and
specializes `Lazy[Int]` to a declaration `Lazy_Int`. Strata leaves `List a`
declared as `List a` and emits `$__mono#List.cons#int` against it. -/

/-- The type declarations of a program, in declaration order. -/
def typeDecls (p : Program) : List Decl :=
  p.decls.filter fun | .type _ _ => true | _ => false

/-- Each datatype the program declares, paired with its type parameters. The
    projection `checkMonoPolyDatatypesRemain` compares, so that a failure prints
    the datatype whose parameters moved rather than the whole block. -/
def datatypeParams (p : Program) : List (String × List TyIdentifier) :=
  (datatypeBlocks p).flatMap fun b => b.map fun d => (d.name, d.typeArgs)

/-- **Type declarations pass through the pass unchanged** — same declarations, in
    the same order.

    `Decl` derives `DecidableEq`, so this is a genuine equality rather than a
    `BEq` comparison, and a failure prints both declaration lists. They can be
    large; that is the price of the counterexample naming what changed. -/
abbrev checkMonoTypeDeclsUnchanged (p : Program) : Prop :=
  onOutput p (typeDecls p) typeDecls = typeDecls p

/-- **A polymorphic datatype is still polymorphic after the pass**: its type
    parameters are neither dropped nor specialized.

    Stated positively, and expected to hold, because it pins the pass's scope. If
    it ever fails, kind (2) monomorphization has arrived and the properties around
    it need rereading — which is the signal wanted, rather than a silent change of
    meaning under `checkMonoTypeDeclsUnchanged`.

    Vacuous unless the draw declares a datatype with type parameters. -/
abbrev checkMonoPolyDatatypesRemain (p : Program) : Prop :=
  onOutput p (datatypeParams p) datatypeParams = datatypeParams p

/-- The polymorphic operators the program's datatype blocks derive, by name. -/
def derivedPolyNames (p : Program) : List String :=
  (datatypeBlocks p).flatMap fun block =>
    (ProgramGen.adtDerivedPolyOps block).map Prod.fst

/-- **The derived functions of a polymorphic datatype *are* rewritten**, which is
    the other half of the asymmetry: the declaration stays polymorphic, the
    operators it derives do not.

    Seeded with `monoSeedFactoryWithDerived`, because `Core.Factory` holds no
    derived operator and the claim would otherwise be vacuous by construction
    rather than by draw. Self-calibrating: the premise is "a reference to a name
    that is polymorphic in the seed factory", so an empty premise reads as
    vacuous, never as red. -/
abbrev checkMonoDerivedOpsRewritten (p : Program) : Prop :=
  (((runMonoWith (monoSeedFactoryWithDerived p) p).map
    (fun r => survivingPolyRefs (derivedPolyNames p) (allOpNames r.1.2))).getD []) = []

/-! ## Group C — the naming convention

Every specialization is identified by its mangled name
`$__mono#<base>#<mangleTyArgs tys>`, so the convention carries the whole weight of
keeping specializations apart. Two instantiations that mangle alike collapse into
one declaration, silently and at the wrong type — and `mangleTy`'s docstring
concedes that the arity prefix a `.tcons` carries is "documentary rather than
disambiguating". -/

/-- The mangled specialization names the output declares. -/
def monoMangledNames (p : Program) : List String :=
  match monoOut p with
  | none => []
  | some p' =>
    (programFuncs p').filterMap fun f =>
      if (demangleFuncName f.name.name).isSome then some f.name.name else none

/-! ### Coverage

Not properties: a property asserts, and these two measure. They exist because
every predicate in this module reads `none`-or-nothing as "no claim to make", and
the measurement in the module header says that is the *usual* case for a default
draw. Wire at least one of them as a Tyche axis or a `Diagnostic`, so a run
reports how often it reached the pass rather than leaving a reader to assume it
did. -/

/-- How many specializations the pass created — `0` when the draw never reached
    it, which the module header measures as the common case. -/
def monoSpecializationCount (p : Program) : Nat := (monoMangledNames p).length

/-- Whether this draw reached the pass at all. The boolean form of
    `monoSpecializationCount`, for a Tyche nominal axis. -/
def monoReachedPass (p : Program) : Bool := monoSpecializationCount p != 0

/-- **Every specialization's base name was a polymorphic function of the input.**
    A mangled name whose base is not one of the functions the pass set out to
    specialize is a name minted from nowhere. -/
abbrev checkMonoMangledBaseWasPolymorphic
    (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  (monoMangledNames p).filter
    (fun n => !(polyNames p F).contains (demangledBaseName n)) = []

/-- **The output declares no name twice.** The pass adds one declaration per
    specialization, keyed on the instantiation *vector* by
    `FuncSpecialization`'s hand-written `BEq` and `Hashable`. Should those two
    ever disagree, or should two distinct instantiations mangle alike, the output
    holds two declarations under one name — which this catches and the
    typechecker may not.

    Stated as an equality of *lengths* rather than through `nodup`, so a failure
    prints the two counts (`issue: 5 = 6 does not hold`) and thereby how many
    names collapsed. -/
abbrev checkMonoOutputNamesNodup (p : Program) : Prop :=
  (onOutput p [] declNames).eraseDups.length = (onOutput p [] declNames).length

/-- **`demangleFuncName` inverts `mangleFuncName`** at a non-empty instantiation:
    the base name and the type mangling both come back.

    This is where the assumption stated in `demangleFuncName`'s own docstring —
    "`funcname` never contains `#` (not a legal Strata ident char)" — gets tested
    against the names the generator actually mints, rather than trusted. A
    nullary instantiation returns the base name unchanged and so has nothing to
    invert; that case is excluded here and stated by
    `checkMangleNullaryIsIdentity`. -/
abbrev checkMangleRoundtripAt (name : String) (tys : List LMonoTy) : Prop :=
  tys ≠ [] →
    demangleFuncName (mangleFuncName Strata.PtrCache.PtrCache.empty name tys).1.name
      = some (name, mangleTyArgs tys)

/-- **A nullary instantiation is not mangled at all**, per `mangleFuncName`. Worth
    pinning separately: it is the one input on which the round-trip above cannot
    hold, and the reason is a deliberate special case rather than a gap. -/
abbrev checkMangleNullaryIsIdentity (name : String) : Prop :=
  (mangleFuncName Strata.PtrCache.PtrCache.empty name []).1.name = name

/-- **Distinct instantiations of one function get distinct names.** Injectivity of
    the convention, stated pointwise over a pair of instantiation vectors so that
    a failure names the colliding pair. -/
abbrev checkMangleDistinctAt (name : String) (tys₁ tys₂ : List LMonoTy) : Prop :=
  tys₁ ≠ tys₂ →
    (mangleFuncName Strata.PtrCache.PtrCache.empty name tys₁).1.name ≠
      (mangleFuncName Strata.PtrCache.PtrCache.empty name tys₂).1.name

/-- Whether the program refers to any function the pass would specialize. The
    guard for `checkMonoNoPolyProgramUnchanged`: a program that mentions no
    polymorphic function is one the pass has nothing to do to. -/
def refersToPolyFunc (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : Bool :=
  let poly := polyNames p F
  (allOpNames p).any poly.contains || !(polyProgramFuncNames p).isEmpty

/-- **A program with no polymorphic function is returned unchanged**, and reported
    as unchanged.

    The anchor against spurious rewriting: whatever else the pass does, it must
    not touch a program that has nothing to monomorphize. Note what the `changed`
    flag is computed from — `p'.decls != p.decls`, which ignores the rebuilt
    factory entirely, so this property says nothing about a draw whose only
    polymorphic functions are factory entries. -/
abbrev checkMonoNoPolyProgramUnchanged (p : Program) : Prop :=
  refersToPolyFunc p = false → monoChangedOut p = (false, p)

/-- The names of the declarations the pass neither adds nor drops, in order. -/
def nonFuncDeclNames (p : Program) : List String :=
  (p.decls.filter fun | .func _ _ | .recFuncBlock _ _ => false | _ => true).map
    fun d => CoreIdent.toPretty d.name

/-- **The declarations the pass does not add keep their relative order.** A
    specialization is a new declaration, so the output is longer; but every
    declaration that was already there must still be there, in the same order.
    Stated over the non-function declarations, which are the ones the pass neither
    adds nor drops. -/
abbrev checkMonoDeclOrderPreserved (p : Program) : Prop :=
  onOutput p (nonFuncDeclNames p) nonFuncDeclNames = nonFuncDeclNames p

/-! ## Semantics preservation

`monomorphizeFunctionsPipelinePhase` is declared `modelPreserving`: a specialized
copy is a type-instantiated duplicate, so it denotes the same values at that
instantiation. Lutze et al. prove the corresponding result step-for-step
(Theorem 3.10, Corollary 3.11); what is checkable here is the weaker, executable
consequence — that running Strata's own concrete evaluator over an expression
before and after the pass gives the same answer.

**The comparison is modulo the naming convention, and has to be.** Renaming is
the pass's entire purpose, so `f(3)` becomes `$__mono#f#int(3)` and the two terms
are trivially unequal as terms. Both sides are therefore normalized through
`demangledBaseName` before comparison, which is exactly the normalization the CST
printer performs for display. What survives that normalization is a difference in
evaluation *behaviour*, which is the thing worth catching.

**Where the risk actually is.** `LExpr.eval` unfolds only an `.inline`-attributed
function, so neither side unfolds a user function and the property says little
about those. What it does bear on is the *builtins*: the evaluator dispatches on
an operator's literal name, and the pass renames polymorphic builtins
(`select`, `update`, `Sequence.length`, …) to `$__mono#select#…`. If a renamed
builtin stops matching the evaluator's dispatch, folding silently stops — the
program still typechecks, still encodes, and quietly computes less. That is the
failure this property exists to find. -/

/-- Rewrite every `.op` name of an expression through `demangledBaseName`, so a
    specialized reference and its polymorphic original compare equal. -/
partial def demangleOps : Expression.Expr → Expression.Expr
  | .op m o ty => .op m ⟨demangledBaseName o.name, o.metadata⟩ ty
  | .app m f a => .app m (demangleOps f) (demangleOps a)
  | .abs m n ty e => .abs m n ty (demangleOps e)
  | .quant m k n ty tr e => .quant m k n ty (demangleOps tr) (demangleOps e)
  | .ite m c t e => .ite m (demangleOps c) (demangleOps t) (demangleOps e)
  | .eq m a b => .eq m (demangleOps a) (demangleOps b)
  | e => e

/-- The `(before, after)` pairs of always-live expressions whose evaluations
    disagree once names are normalized, plus a self-pairing sentinel when the two
    lists are not the same length.

    The sentinel is what keeps the alignment claim inside the same predicate:
    `List.zip` truncates, so a pass that dropped an always-live declaration would
    otherwise shorten both sides and compare only the surviving prefix. Pairing
    the first input expression with itself is never a real disagreement — the two
    sides are identical — so it cannot fire except through the length check. -/
def evalDisagreements (p : Program) : List (Expression.Expr × Expression.Expr) :=
  match runMono p with
  | none => []
  | some ((_, p'), st) =>
    let es := aliveExprs p
    let es' := aliveExprs p'
    if es.length != es'.length then (es.zip es).take 1
    else (es.zip es').filter fun q =>
      demangleOps (evalOver Core.Factory q.1) != demangleOps (evalOver st.factory q.2)

/-- **Concrete evaluation agrees before and after the pass**, up to the naming
    convention.

    Compares positionally over `aliveExprs`, which the pass rewrites in place and
    neither reorders nor resizes — the length check states that alignment rather
    than assuming it, so a future pass that did add a procedure would fail here
    loudly instead of comparing mismatched pairs.

    Each side is evaluated against the factory that side belongs to: the input
    against `Core.Factory` (what `mkState` seeds, hence what the pass saw), the
    output against the rebuilt factory that holds the specialized copies. Guarded
    on the input typechecking, since evaluation of an ill-typed expression is not
    something either side owes an answer for. -/
abbrev checkMonoEvalAgreement (p : Program) : Prop :=
  progTypeChecks p = true → evalDisagreements p = []

end StrataGenerators.Mono
