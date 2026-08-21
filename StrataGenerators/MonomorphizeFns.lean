-- The whole-program generator and its shrinker, the program typechecker oracle
-- (`progTypeChecks`) and `sizeProgram`.
import StrataGenerators.ProgramGen.Shrink
-- `programFuncs`, `programBodies`, `declNames`, `nodup` and `evalOver`, together with the definitions that
-- run a phase. Each property here uses them, and it writes none of them again.
import StrataGenerators.ProgramGen.UnprovenTransforms
-- `opNames`, `datatypeBlocks`, and the derived-operator projections.
import StrataGenerators.ProgramGen.TestSupport
-- The pass under test, and the naming convention it renames through.
import Strata.Transform.MonomorphizeFunctions
import Strata.Languages.Core.NameMangling
-- `Core.typeCheck`, which is the one entry point of the typechecker that takes a *factory* argument. A check
-- of the output of this pass needs the factory that the pass itself built.
import Strata.Languages.Core.Verifier

open Lambda Core Imperative
-- `progTypeChecks`, the whole-program typechecker oracle, and the program shrinker.
open StrataGenerators.Program.TestSupport
-- `runPhaseSt` and `mkState`. They run a pipeline phase from a fresh transform state, and they give the pair
-- of the flag and the output *and* the final state. That final state holds the factory that the pass built,
-- and many properties here read it.
open StrataGenerators.Procedure.TestSupport
-- `opNames` (every `.op` name of an expression) and `datatypeBlocks`.
open ProgramGen.TestSupport
-- `programFuncs`, `programBodies`, `declNames`, `nodup`, `evalOver`, `programFactory`.
open StrataGenerators.Program.UnprovenTransforms
-- `mangleFuncName` / `demangleFuncName` / `demangledBaseName` / `mangleTyArgs`.
open Core.NameMangling

/-!
# The check predicates for `MonomorphizeFunctions`

`Strata/Transform/MonomorphizeFunctions.lean` specializes each polymorphic top-level function, which is a
`Decl.func` or a `Decl.recFuncBlock`, and each polymorphic function of the `Factory`. It makes one copy for
each different ground instantiation that a context outside a function reaches. It then renames each
reference to the specialized copy, and it **drops each polymorphic original that nothing reaches**. The
pass runs immediately after the phase for the typechecker in `Core.corePipelinePhases`, so that the encoder
for SMT, the symbolic evaluator and each backend can assume a monomorphic input.

Strata tests the pass with fourteen examples that a person wrote, and each of them asserts the same three
claims about one fixed program: no top-level function keeps its type parameters, no entry of the factory
keeps its type parameters, and the output type checks. This module states those claims *over the
generator*, and it adds the claims that a fixed set of examples cannot reach.

## Why a generated program is a real input, and why it needs no type check first

The pass reads the instantiation of a call from the type annotation that the typechecker puts on the `.op`
node, and that is why the pipeline runs it after the phase for the typechecker. A generated program already
carries that annotation. `genIndirPolyCore` builds an `.op` node with the instantiation inside its
annotation, and `ProgramGen` registers each *declared* polymorphic function into the polymorphic context
that the generation of a body uses. Therefore the body of a generated program does call a generated
polymorphic function at a ground instantiation.

The pass therefore runs on a draw directly. That fact matters, because `Program.typeCheck` rejects a large
part of the generated programs, for three reasons that the module docstring of `ProgramGen/Shrink` gives. A
guard on that check for each property would therefore throw most of the signal away. Only a property whose
*claim* needs a well-typed input carries the guard `!progTypeChecks p ||`, and those two properties are
`checkMonoOutputTypechecks` and `checkMonoEvalAgreement`.

## The seed factory is `Core.Factory`, as in the tests of Strata

`runPhaseSt` seeds the transform state with `Core.Factory`, through `mkState`, and that is exactly the seed
of the tests of Strata for this pass. This module does *not* use `runPhaseWithFuncs`, which also pushes
each function of the program into the factory. That seed would put a declared polymorphic function into the
factory *and* into the declarations of the program. `checkMonoFactoryMonomorphic` would then ask the pass
to specialize one function two times, under two different sources, and a counterexample would report the
seed and not the pass.

One consequence bounds what `checkMonoDerivedOpsRewritten` can see. `Core.Factory` holds **none** of the
operators that a generated datatype block derives, which are its constructors, its testers and its
accessors of a field. Those operators reach a factory only when `Core.Verifier` runs a program.
`monoSeedFactoryWithDerived` pushes them in for the one property that is about them, and that property
calibrates itself. Its premise is a reference to a function that is polymorphic *in the seed factory*, so
it says nothing when the premise is empty, and it reports no counterexample there.

## A default draw rarely reaches the pass

A property below says nothing about the pass when the draw reaches no specialization. Three facts about the
generator, and none of them is a defect in it, keep a default draw away from the pass:

* `ProgramGen.funcPolyOpEntry` registers a declared polymorphic function into the polymorphic context of
  the state, and `genAxiom` is the **one** generator that reads that context. The body of a function and of
  a procedure reads the context of the schemes that a datatype derives. Therefore an axiom is the one place
  that can call a generated polymorphic *function*.
* The default runner draws few declarations, and an axiom is one of six kinds of declaration at the weight
  1. Therefore a draw often holds no axiom at all.
* `processTopDecls` seeds its list of the work from each procedure, each axiom, each `distinct` declaration
  and each *monomorphic* function. A reference inside the body of a polymorphic function is reachable only
  through another declaration, so it cannot start a specialization on its own.

Two things follow for a caller that registers these properties. First, report the coverage: register
`monoSpecializationCount` as an axis of a Tyche panel or as a `Diagnostic`, so that a run says how often it
reached the pass. `monoReachedPass` is the same measurement as a `Bool`. Second, a draw that reaches the
pass needs a *tuned* generator, and not the default one. A larger number of declarations, through
`TestDecl.forAll` with an explicit `PropertyRunner`, raises the chance of a draw that holds an axiom and a
polymorphic function together. The durable correction is outside this module: a body of a procedure that
draws from the full polymorphic context, and not from the derived schemes only, would make a call to a
declared polymorphic function an ordinary event.

The two properties about a `funcDecl` statement are the exception, and a draw reaches them. `genFuncDeclStmt`
draws a polymorphic `funcDecl` statement, which `checkMonoStmtFuncDeclsMonomorphic` scores.

## What each group of predicates claims

* `checkMonoAllFuncsMonomorphic`, `checkMonoFactoryMonomorphic`, `checkMonoOutputTypechecks` and
  `checkMonoIdempotent` state the three claims of the tests of Strata over the generator, and they add
  idempotence, which those tests do not state.
* `checkMonoStmtFuncDeclsMonomorphic` and `checkMonoStmtFuncDeclRefsRewritten` are about a `funcDecl`
  *statement*. The field `allFuncsMonomorphic` reads the declarations of the program only, and both
  traversals of the pass skip a `funcDecl` statement. `Command.mapExprM` gives such a statement back
  through its final case, and `Statement.collectExprs` gives the empty list for it. Therefore the pass does
  not see a polymorphic function that a block declares, and it neither seeds a specialization for a
  block-local body that calls a polymorphic top-level function, nor renames that call, and it drops the
  original as unreached. `genFuncDeclStmt` draws exactly that shape. Whether that behaviour is a defect or
  a documented limit of the scope is a question for Strata, and `Expectation.knownFailure` is where the
  answer belongs.
* `checkMonoTypeDeclsUnchanged`, `checkMonoPolyDatatypesRemain` and `checkMonoDerivedOpsRewritten` state one
  asymmetry: the pass specializes the *derived functions* of a polymorphic datatype, and it does not
  specialize the *declaration* of that datatype. `processTopDecls` gives a `.type` declaration back through
  its final case. These three properties state that asymmetry as a fact, so that a later change of Strata
  in either direction becomes visible.
* `checkMonoMangledBaseWasPolymorphic`, `checkMangleRoundtripAt`, `checkMangleDistinctAt`,
  `checkMonoOutputNamesNodup`, `checkMonoNoPolyProgramUnchanged` and `checkMonoDeclOrderPreserved` are
  about the convention for a name. The whole scheme needs the injectivity of that convention, because two
  specializations of one name become one declaration. The docstring of `mangleTy` also records that the
  prefix for an arity is documentary, and that it separates no two names.
* `checkMonoEvalAgreement` is the semantic property. Read its docstring for what it claims and for what it
  does not claim.
-/

namespace StrataGenerators.Mono

/-! ## Running the pass -/

/-- The pipeline phase under test. -/
def monoPhase : Core.PipelinePhase := Core.monomorphizeFunctionsPipelinePhase

/-- The meta-operators for a trigger of SMT. The converter to concrete syntax matches each of them by name,
    so the pass leaves each of them polymorphic on purpose. This list agrees with
    `MonomorphizeFunctions.collectPolymorphicFuncDeclsFromFactory`, which excludes exactly these operators
    from the set to specialize. A predicate here that did not exclude them would report that deliberate
    exemption as a counterexample. -/
def isTriggerMetaOp (name : String) : Bool :=
  name == "TriggerGroup.addTrigger" || name == "TriggerGroup.empty" ||
  name == "Triggers.addGroup"       || name == "Triggers.empty"

/-- The pass, run on the program from a fresh state. The result holds the `changed` flag, the output program,
    and the final transform state. The `factory` field of that state is the factory that the pass built, which
    holds the specialized copies and holds no polymorphic original.

    The result is `none` when the pass raises a diagnostic, which it does on a cycle that grows, and which it
    names a non-uniform polymorphic recursion. Each predicate below reads a `none` as an absence of a claim,
    so a diagnostic is never a counterexample. `checkMonoSucceeds` is the property that scores a
    diagnostic. -/
def runMono (p : Program) :
    Option ((Bool × Program) × Transform.CoreTransformState) :=
  runPhaseSt monoPhase p

/-- `runMono` with an explicit seed factory, for a property that needs the pass to see something that
    `Core.Factory` does not hold, such as an operator that a datatype derives. `runMono` is this function at
    `Core.Factory`, which is the seed of the tests of Strata. Each other seed is a deliberate difference, and
    its call site says why. -/
def runMonoWith (F : Lambda.Factory CoreLParams) (p : Program) :
    Option ((Bool × Program) × Transform.CoreTransformState) :=
  match Transform.runWith p monoPhase.transform { mkState p with factory := F } with
  | (.ok r, st) => some (r, st)
  | (.error _, _) => none

/-- The pass, run a second time, from the transform state of the first run. The result is `none` when the
    second run raises a diagnostic. A diagnostic on the *first* run is an absence of a claim, and a diagnostic
    on the second run is a counterexample. Therefore `checkMonoIdempotent` asks that this result is not
    `none`. -/
def runMonoAgain (r : (Bool × Program) × Transform.CoreTransformState) :
    Option (Bool × Program) :=
  match Transform.runWith r.1.2 monoPhase.transform r.2 with
  | (.ok x, _) => some x
  | (.error _, _) => none

/-- Whether the pass gave a result. This predicate is separate from each other one, so that one property
    scores a diagnostic, and a diagnostic does not silently empty each other property. -/
abbrev checkMonoSucceeds (p : Program) : Prop := (runMono p).isSome = true

/-- The output program alone. -/
def monoOut (p : Program) : Option Program := (runMono p).map (·.1.2)

/-! ### The total projections of the output

Each claim below is an *equality at its top level*, and the definitions here make that form possible. The
direct form, which is `∀ p' ∈ monoOut p, f p' = []`, is decidable, and it prints only a placeholder for the
counterexample. The `PrintableProp` instance of the harness reads the shape at the top level, and it cannot
render a bounded `∀`. Such a property therefore says no more than a `Bool` does. A projection through
`Option.elim`, with the *empty* value as the default, keeps the same meaning, because a diagnostic is still
an absence of a claim, and it puts an equality at the top, which prints both sides. -/

/-- `f` applied to the output, or `dflt` when the pass raised a diagnostic. -/
def onOutput (p : Program) (dflt : α) (f : Program → α) : α :=
  ((monoOut p).map f).getD dflt

/-- The pair of the flag and the output that the pass gives. After a diagnostic, the result is the input
    program together with `false`, which reads as an unchanged program, and which is the empty value here. -/
def monoChangedOut (p : Program) : Bool × Program :=
  (((runMono p).map (·.1)).getD (false, p))

/-- The rebuilt factory alone. -/
def monoFactory (p : Program) : Option (Lambda.Factory CoreLParams) :=
  (runMono p).map (·.2.factory)

/-! ## Naming the polymorphic functions the pass can see -/

/-- The polymorphic functions that a program declares, by name. Those are the `Decl.func` and the
    `Decl.recFuncBlock` entries that `collectPolymorphicFuncDecls` indexes, so this set holds each original
    that the pass can drop. -/
def polyProgramFuncNames (p : Program) : List String :=
  (programFuncs p).filterMap fun f =>
    if f.typeArgs.isEmpty then none else some f.name.name

/-- The polymorphic entries of a factory, minus the trigger meta-operators. -/
def polyFactoryNames (F : Lambda.Factory CoreLParams) : List String :=
  F.toArray.toList.filterMap fun lf =>
    if !lf.typeArgs.isEmpty && !isTriggerMetaOp lf.name.name then some lf.name.name
    else none

/-- Each name that the pass specializes and then drops, at the seed factory `F`. A reference to one of those
    names in the output names a declaration that the pass removed. -/
def polyNames (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : List String :=
  polyProgramFuncNames p ++ polyFactoryNames F

/-- Each reference of `ops` that still names one of the dropped originals.

    Each claim below about such a reference is an equality of this list against the empty list, and that shape
    is the point. An equality that gives a `Prop` lets the harness print the *names* that cause the failure,
    and a `List.all` that gives a `Bool` could report only `false`. -/
def survivingPolyRefs (dropped ops : List String) : List String :=
  (ops.filter dropped.contains).eraseDups

/-- `Core.Factory` together with each operator that a datatype block of the program derives. Those operators
    are the constructors, the testers and the accessors of a field of a generated `mutual … end` block.

    `Core.Factory` holds none of them, because such an operator reaches a factory only through
    `Core.Verifier`. Without this definition, a reference to an accessor names a function that the pass does
    not hold, and each claim about a *derived* operator would then say nothing under the default seed.
    `pushIfNew` keeps the first entry under a name, so a derived name cannot replace a builtin. -/
def monoSeedFactoryWithDerived (p : Program) : Lambda.Factory CoreLParams :=
  (datatypeBlocks p).foldl (init := Core.Factory) fun F block =>
    match ProgramGen.blockDerivedFactory block with
    | none => F
    | some DF => DF.toArray.foldl (fun F lf => F.pushIfNew lf) F

/-! ## The references to an operator

`ProgramGen.TestSupport.stmtOpNames` stops at a `funcDecl` statement and at the arguments of a `call`, on
purpose. Both of those positions matter here. A `funcDecl` statement is the subject of
`checkMonoStmtFuncDeclRefsRewritten`, and an `inArg` of a `call` is an expression that the pass *does*
rewrite, because `Command.mapExprM` goes into it. A predicate that could not read those two positions would
miss a whole class of reference. Therefore this section holds a deeper traversal, and it does not use that
function. -/

/-- Each expression of a syntactic function declaration, which is the node that a `funcDecl` statement holds.
    This definition follows `expressionsFromFunction` of the pass, which is what the pass reads from a
    *top-level* function. Therefore the two views of the expressions of a function cannot differ. -/
def pureFuncExprs (d : Imperative.PureFunc Expression) : List Expression.Expr :=
  d.body.toList ++ d.axioms ++ d.preconditions.map (·.expr) ++ d.measure.toList

/-- Each function that a statement list declares through a `funcDecl` statement, at any depth. The field
    `allFuncsMonomorphic` reads the declarations of the program, so it reads none of these functions. -/
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

    A generated procedure always has a `.structured` body, because a control-flow graph is the output of a
    pass and not a shape that the generator draws. Therefore this function loses nothing. The case for a
    control-flow graph is explicit, and it is not part of a final case, so that a later generator which draws
    one gives an empty result here, and not a wrong one. -/
def structuredBody (q : Procedure) : List Statement :=
  match q.body with
  | .structured ss => ss
  | .cfg _ => []

/-- The expressions of each declaration that the pass treats as **always live**. Those declarations are a
    procedure, with its contract clauses and its body, an axiom, and a `distinct` declaration.

    The pass rewrites that list *in place*. `processTopDecls` visits those three kinds of declaration, it
    rewrites each of them, and it puts each of them back at the same position. It adds and removes nothing.
    Therefore the list has the same length and the same order before and after the pass, and
    `checkMonoEvalAgreement` can compare the two lists by position.

    This definition excludes the body of a function on purpose, and that choice is what makes the two lists
    agree. The pass *adds* one declaration for each specialization, and it drops each polymorphic original.
    Therefore a list that held the expressions of a function would have a different length on the two
    sides. -/
def aliveExprs (p : Program) : List Expression.Expr :=
  p.decls.flatMap fun
    | .proc q _ =>
      q.spec.preconditions.values.map (·.expr) ++
      q.spec.postconditions.values.map (·.expr) ++
      Core.Statements.collectExprs (structuredBody q)
    | .ax a _ => [a.e]
    | .distinct _ es _ => es
    | _ => []

/-- Each `.op` name of a program. The result covers each always-live declaration, the expressions of each
    function, and the body of each function that a `funcDecl` statement declares. A claim about a reference
    that the pass did not rewrite needs that whole view, because such a reference can sit at any position. -/
def allOpNames (p : Program) : List String :=
  (aliveExprs p).flatMap opNames
    ++ (programFuncs p).flatMap (fun f =>
         (f.body.map opNames).getD [] ++ f.axioms.flatMap opNames ++
         f.preconditions.flatMap (fun c => opNames c.expr) ++
         (f.measure.map opNames).getD [])
    ++ (p.decls.flatMap fun | .proc q _ => stmtOpNamesDeep (structuredBody q) | _ => [])

/-! ## The three claims of the tests of Strata, over the generator

The three predicates that the tests of Strata assert on each of their fourteen examples, together with
idempotence. Each of them holds with no guard, except `checkMonoOutputTypechecks`, whose claim needs a
well-typed input. -/

/-- **No top-level function declaration keeps its type parameters.** This is the main postcondition of the
    pass, and it is the reason that the encoder for SMT can assume a monomorphic input.

    The scope is the declarations of the program only. This property does not cover a function that a
    `funcDecl` *statement* declares, and `checkMonoStmtFuncDeclsMonomorphic` covers that case. The two are
    separate properties, because the pass treats the two kinds of declaration differently.

    The claim is an equality of `polyProgramFuncNames p'` against the empty list, and it is not a bounded `∀`
    over the declarations. The two forms say the same thing, and only the equality prints the counterexample,
    which names each function that kept its type parameters. -/
abbrev checkMonoAllFuncsMonomorphic (p : Program) : Prop :=
  onOutput p [] polyProgramFuncNames = []

/-- **No entry of the factory that the pass built keeps its type parameters**, except a meta-operator for a
    trigger, which the pass exempts by name. `polyFactoryNames` applies exactly that exemption. -/
abbrev checkMonoFactoryMonomorphic (p : Program) : Prop :=
  ((monoFactory p).map polyFactoryNames).getD [] = []

/-- **The output type checks**, against the factory that the pass built.

    `Core.typeCheck` is the one entry point that takes a factory, and that factory must be the one that the
    pass built. The output names a specialized function, which exists in no other factory. A check of the
    output against `Core.Factory` would therefore fail for a reason outside this property.

    The property carries a guard on the type check of the input, because a pass is responsible only for what
    it does to a well-typed input. That guard is an implication, and not a disjunction, and that form is what
    lets a counterexample print with the guard already discharged. -/
abbrev checkMonoOutputTypechecks (p : Program) : Prop :=
  progTypeChecks p = true →
    ∀ r ∈ runMono p,
      (Core.typeCheck Core.VerifyOptions.quiet r.1.2
        (factory := r.2.factory)).toOption.isSome = true

/-- **The pass is idempotent, and it reports so.** After one run, each function is monomorphic. Therefore the
    second run has nothing to specialize, it must give the same program, and it must report `changed = false`.

    The second run starts from the state of the *first* run, and not from a fresh state. A second seed of
    `Core.Factory` would give the second run the polymorphic originals of the factory that the first run
    dropped. The second run would then specialize them again, and the property would measure this module and
    not the pass.

    The part of the claim that says the second run gives a result is necessary. A bounded `∀` over that result
    alone would read a diagnostic on the *second* run as an absence of a claim, and a second run that fails
    where the first run succeeded breaks idempotence. -/
abbrev checkMonoIdempotent (p : Program) : Prop :=
  (runMono p).bind runMonoAgain = (monoOut p).map (fun p' => (false, p'))

/-! ## The `funcDecl` statement

The field `allFuncsMonomorphic` reads the declarations of the program. A `funcDecl` *statement* holds an
`Imperative.PureFunc` with its own type parameters, and both traversals of the pass skip it. The final case
of `Command.mapExprM` gives a `.funcDecl` back unchanged, and `Statement.collectExprs` gives the empty list
for it. Therefore a polymorphic function that a block declares keeps its type parameters, and a call from a
block-local body to a polymorphic top-level function gets neither a specialization nor a new name, while the
pass drops the original as unreached.

`genFuncDeclStmt` draws the declaration from `genFunction`, whose type parameters come from `genTypeArgs`,
and it threads the polymorphic context into the body. Therefore a draw can reach both shapes. Read a result
with no counterexample from either property together with the axis of the Tyche panel for a `funcDecl`,
which says whether the draw reached the shape at all. -/

/-- Every function a program declares through a `funcDecl` statement, from any
    procedure body. -/
def programStmtFuncDecls (p : Program) : List (Imperative.PureFunc Expression) :=
  p.decls.flatMap fun
    | .proc q _ => funcDeclsOfStmts (structuredBody q)
    | _ => []

/-- The names of the *polymorphic* functions that a program declares through a `funcDecl` statement. This
    definition is the form of `polyProgramFuncNames` for a statement, and it exists for the same reason: a
    list of the names is what lets the property below print which function kept its type parameters. -/
def polyStmtFuncDeclNames (p : Program) : List String :=
  (programStmtFuncDecls p).filterMap fun d =>
    if d.typeArgs.isEmpty then none else some d.name.name

/-- **No function that a statement declares keeps its type parameters.** This property is the form of
    `checkMonoAllFuncsMonomorphic` for a statement.

    The property says nothing unless the draw holds a `funcDecl` statement whose declaration is
    polymorphic. -/
abbrev checkMonoStmtFuncDeclsMonomorphic (p : Program) : Prop :=
  onOutput p [] polyStmtFuncDeclNames = []

/-- **A statement-declared body's references are rewritten.** No expression of a
    `funcDecl` statement in the output may still name a function whose
    polymorphic original the pass dropped.

    The property says nothing unless the draw holds a `funcDecl` whose body calls a polymorphic function. When
    it does say something, a counterexample is a reference to a declaration that the pass removed, and it is
    not a difference of appearance. -/
abbrev checkMonoStmtFuncDeclRefsRewritten
    (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  onOutput p [] (fun p' =>
    survivingPolyRefs (polyNames p F)
      (((programStmtFuncDecls p').flatMap pureFuncExprs).flatMap opNames)) = []

/-- **No reference to a dropped polymorphic original survives anywhere.** The
    unrestricted form of the claim above, over every expression of the output.

    This property is sharper than the one about the type check of the output in one direction, and weaker in
    another. It needs no well-typed input, and it reads the *name* only, and not the instantiation. A
    reference that the pass renames to a specialization at the wrong instantiation satisfies this property and
    fails the typechecker. -/
abbrev checkMonoNoPolyRefsSurvive
    (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  onOutput p [] (fun p' => survivingPolyRefs (polyNames p F) (allOpNames p')) = []

/-! ## A type declaration changes only through the functions that it derives

The pass handles a `Decl.func`, a `Decl.recFuncBlock` and the factory. `processTopDecls` gives a `.type`
declaration back unchanged, through its final case. Therefore a polymorphic datatype declaration keeps its
type parameters. The operators that such a datatype *derives* are ordinary polymorphic functions of the
factory, and the pass specializes each of them as it specializes each other one.

This section states that asymmetry as a fact, and no property assumes it. It is also the one point where
Lutze, Schuster and Brachthäuser, in *The Simple Essence of Monomorphization* (OOPSLA 2025), call Strata
incomplete, and not merely different. Their section 2.2 treats a datatype with a type parameter as a kind of
polymorphism of its own, with the constraints that the judgement for well-formedness raises, and it
specializes a datatype at a ground instance into a declaration of its own. Strata keeps such a datatype
declared with its type parameters, and it emits a specialized name for each derived operator against it. -/

/-- The type declarations of a program, in declaration order. -/
def typeDecls (p : Program) : List Decl :=
  p.decls.filter fun | .type _ _ => true | _ => false

/-- Each datatype that the program declares, together with its type parameters.
    `checkMonoPolyDatatypesRemain` compares this projection, so that a counterexample prints the datatype
    whose parameters changed, and not the whole block. -/
def datatypeParams (p : Program) : List (String × List TyIdentifier) :=
  (datatypeBlocks p).flatMap fun b => b.map fun d => (d.name, d.typeArgs)

/-- **The pass gives each type declaration back unchanged**, in the same order.

    `Decl` derives `DecidableEq`, so this claim is a true equality, and not a comparison through `BEq`. A
    counterexample therefore prints both lists of the declarations. Such a list can be large, and that size
    is the price of a counterexample that names what changed. -/
abbrev checkMonoTypeDeclsUnchanged (p : Program) : Prop :=
  onOutput p (typeDecls p) typeDecls = typeDecls p

/-- **A polymorphic datatype is still polymorphic after the pass**: its type
    parameters are neither dropped nor specialized.

    The property states the claim positively, because it pins the scope of the pass. A counterexample means
    that the pass also specializes a datatype declaration, and each property around this one then needs a
    second reading. That signal is the point, and it is better than a silent change of the meaning of
    `checkMonoTypeDeclsUnchanged`.

    The property says nothing unless the draw declares a datatype with a type parameter. -/
abbrev checkMonoPolyDatatypesRemain (p : Program) : Prop :=
  onOutput p (datatypeParams p) datatypeParams = datatypeParams p

/-- The polymorphic operators the program's datatype blocks derive, by name. -/
def derivedPolyNames (p : Program) : List String :=
  (datatypeBlocks p).flatMap fun block =>
    (ProgramGen.adtDerivedPolyOps block).map Prod.fst

/-- **The pass rewrites each derived function of a polymorphic datatype.** That is the other half of the
    asymmetry: the declaration keeps its type parameters, and the operators that it derives do not.

    The property uses `monoSeedFactoryWithDerived` as its seed, because `Core.Factory` holds no derived
    operator, and the claim would otherwise say nothing by construction, and not by the draw. The property
    calibrates itself: its premise is a reference to a name that is polymorphic in the seed factory, so an
    empty premise gives no claim, and it gives no counterexample. -/
abbrev checkMonoDerivedOpsRewritten (p : Program) : Prop :=
  (((runMonoWith (monoSeedFactoryWithDerived p) p).map
    (fun r => survivingPolyRefs (derivedPolyNames p) (allOpNames r.1.2))).getD []) = []

/-! ## The convention for a name

The mangled name of a specialization identifies it, and that convention is therefore what keeps two
specializations apart. Two instantiations that give one mangled name become one declaration, in silence and
at the wrong type. The docstring of `mangleTy` also records that the prefix for the arity of a `.tcons` is
documentary, and that it separates no two names. -/

/-- The mangled specialization names the output declares. -/
def monoMangledNames (p : Program) : List String :=
  match monoOut p with
  | none => []
  | some p' =>
    (programFuncs p').filterMap fun f =>
      if (demangleFuncName f.name.name).isSome then some f.name.name else none

/-! ### The coverage

The two definitions below are not properties. A property asserts a claim, and each of these measures a draw.
They exist because each predicate of this module reads an absent result as an absence of a claim, and a
default draw rarely reaches the pass, as the module docstring records. Register at least one of them as an
axis of a Tyche panel or as a `Diagnostic`, so that a run reports how often it reached the pass. -/

/-- The number of the specializations that the pass built. The value is 0 when the draw never reached the
    pass, and the module docstring records that a default draw rarely reaches it. -/
def monoSpecializationCount (p : Program) : Nat := (monoMangledNames p).length

/-- Whether this draw reached the pass. This definition is the `Bool` form of
    `monoSpecializationCount`, for a nominal axis of a Tyche panel. -/
def monoReachedPass (p : Program) : Bool := monoSpecializationCount p != 0

/-- **The base name of each specialization is a polymorphic function of the input.** A mangled name whose base
    is not one of the functions that the pass set out to specialize comes from nowhere. -/
abbrev checkMonoMangledBaseWasPolymorphic
    (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  (monoMangledNames p).filter
    (fun n => !(polyNames p F).contains (demangledBaseName n)) = []

/-- **The output declares no name two times.** The pass adds one declaration for each specialization, and it
    keys each of them on the *list* of the instantiations, through the `BEq` instance and the `Hashable`
    instance of `FuncSpecialization`, which a person wrote. If those two instances disagree, or if two
    different instantiations give one mangled name, then the output holds two declarations under one name.
    This property catches that case, and the typechecker can miss it.

    The claim is an equality of two *lengths*, and it does not use a predicate about duplicates. Therefore a
    counterexample prints the two counts, and it says how many names became one. -/
abbrev checkMonoOutputNamesNodup (p : Program) : Prop :=
  (onOutput p [] declNames).eraseDups.length = (onOutput p [] declNames).length

/-- **`demangleFuncName` inverts `mangleFuncName`** at an instantiation that is not empty. Both the base name
    and the mangled types come back.

    The docstring of `demangleFuncName` states one assumption: the name of a function never holds the
    separator character, because that character is not legal in an identifier of Strata. This property tests
    that assumption against the names that the generator builds, and it does not trust it. An empty
    instantiation gives the base name unchanged, so there is nothing to invert there. This property excludes
    that case, and `checkMangleNullaryIsIdentity` states it. -/
abbrev checkMangleRoundtripAt (name : String) (tys : List LMonoTy) : Prop :=
  tys ≠ [] →
    demangleFuncName (mangleFuncName Strata.PtrCache.PtrCache.empty name tys).1.name
      = some (name, mangleTyArgs tys)

/-- **`mangleFuncName` does not change a name at an empty instantiation.** This case needs a property of its
    own, because it is the one input where the round trip above cannot hold, and the reason is a deliberate
    special case and not a gap. -/
abbrev checkMangleNullaryIsIdentity (name : String) : Prop :=
  (mangleFuncName Strata.PtrCache.PtrCache.empty name []).1.name = name

/-- **Two different instantiations of one function get two different names.** This property is the injectivity
    of the convention, over a pair of lists of the instantiations, so that a counterexample names the pair
    that collides. -/
abbrev checkMangleDistinctAt (name : String) (tys₁ tys₂ : List LMonoTy) : Prop :=
  tys₁ ≠ tys₂ →
    (mangleFuncName Strata.PtrCache.PtrCache.empty name tys₁).1.name ≠
      (mangleFuncName Strata.PtrCache.PtrCache.empty name tys₂).1.name

/-- Whether the program names a function that the pass would specialize. This predicate is the guard of
    `checkMonoNoPolyProgramUnchanged`, because the pass has nothing to do to a program that names no
    polymorphic function. -/
def refersToPolyFunc (p : Program) (F : Lambda.Factory CoreLParams := Core.Factory) : Bool :=
  let poly := polyNames p F
  (allOpNames p).any poly.contains || !(polyProgramFuncNames p).isEmpty

/-- **The pass gives a program with no polymorphic function back unchanged**, and it reports that program as
    unchanged.

    This property is the guard against a rewrite that the pass should not make: whatever else the pass does,
    it must change no program that has nothing to specialize. Read what the `changed` flag comes from: a
    comparison of the two lists of the declarations, which reads no factory. Therefore this property says
    nothing about a draw whose polymorphic functions are entries of the factory only. -/
abbrev checkMonoNoPolyProgramUnchanged (p : Program) : Prop :=
  refersToPolyFunc p = false → monoChangedOut p = (false, p)

/-- The names of the declarations the pass neither adds nor drops, in order. -/
def nonFuncDeclNames (p : Program) : List String :=
  (p.decls.filter fun | .func _ _ | .recFuncBlock _ _ => false | _ => true).map
    fun d => CoreIdent.toPretty d.name

/-- **Each declaration that the pass does not add keeps its relative order.** A specialization is a new
    declaration, so the output is longer. Each declaration of the input must still be present, and in the same
    order. The property covers each declaration that is not a function, because those are the ones that the
    pass neither adds nor drops. -/
abbrev checkMonoDeclOrderPreserved (p : Program) : Prop :=
  onOutput p (nonFuncDeclNames p) nonFuncDeclNames = nonFuncDeclNames p

/-! ## The preservation of the semantics

The pipeline phase of this pass carries the annotation `modelPreserving`. A specialized copy is a duplicate
at one instantiation of the types, so it denotes the same values at that instantiation. Lutze and others
prove the matching result for each step, in their Theorem 3.10 and their Corollary 3.11. The executable
consequence is weaker, and this module can check it: the concrete evaluator of Strata gives the same answer
for an expression before the pass and after it.

**The comparison ignores the convention for a name, and it must do so.** A rename is the whole purpose of
the pass, so a call becomes a call to a specialized name, and the two terms are then different terms. This
module therefore normalizes both sides through `demangledBaseName` before the comparison, and the printer for
concrete syntax performs exactly that normalization for its display. What survives that normalization is a
difference in the *behaviour* of the evaluator, and that difference is the one worth a report.

**Where the risk is.** `LExpr.eval` unfolds a function with the `.inline` attribute only, so neither side
unfolds a function of the program, and this property says little about such a function. It does bear on a
builtin operator. The evaluator dispatches on the literal name of an operator, and the pass renames a
polymorphic builtin, such as the one that selects from a map or the one that gives the length of a sequence.
If a renamed builtin no longer matches the dispatch of the evaluator, then the folding stops in silence. The
program still type checks, it still goes to the encoder, and it computes less. This property exists to find
that failure. -/

/-- Rewrite each `.op` name of an expression through `demangledBaseName`, so that a reference to a
    specialization and a reference to its polymorphic original are equal. -/
partial def demangleOps : Expression.Expr → Expression.Expr
  | .op m o ty => .op m ⟨demangledBaseName o.name, o.metadata⟩ ty
  | .app m f a => .app m (demangleOps f) (demangleOps a)
  | .abs m n ty e => .abs m n ty (demangleOps e)
  | .quant m k n ty tr e => .quant m k n ty (demangleOps tr) (demangleOps e)
  | .ite m c t e => .ite m (demangleOps c) (demangleOps t) (demangleOps e)
  | .eq m a b => .eq m (demangleOps a) (demangleOps b)
  | e => e

/-- Each pair of an always-live expression before the pass and after it whose two evaluations differ, after the
    normalization of the names. The result also holds one pair of the first input expression with itself when
    the two lists have different lengths.

    That extra pair keeps the claim about the alignment inside this one predicate. `List.zip` drops the longer
    tail, so a pass that removed an always-live declaration would otherwise shorten both sides, and the
    comparison would read the common prefix only. A pair of one expression with itself is never a true
    difference, because the two sides are identical, so it can appear only through the check of the two
    lengths. -/
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

    The property compares the two lists by position, over `aliveExprs`. The pass rewrites that list in place,
    and it changes neither its order nor its length. The check of the two lengths states that alignment, and
    the property does not assume it. Therefore a later pass that added a procedure gives a counterexample
    here, and it does not compare two pairs that do not match.

    Each side runs against its own factory. The input runs against `Core.Factory`, which `mkState` seeds and
    which the pass saw. The output runs against the factory that the pass built, which holds each specialized
    copy. The property carries a guard on the type check of the input, because neither side owes an answer for
    an expression that is not well typed. -/
abbrev checkMonoEvalAgreement (p : Program) : Prop :=
  progTypeChecks p = true → evalDisagreements p = []

end StrataGenerators.Mono
