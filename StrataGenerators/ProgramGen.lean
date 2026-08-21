import StrataGenerators.ProgramGen.Core
-- `Basalt.PlausibleGen` supplies the `[Gen Plausible.Gen]` instance used by
-- `sample`, and `RetryGen` the retry wrapper. The direct `G := IO` path is
-- unreliable for procedures (see `sample`'s docstring).
import Basalt.PlausibleGen
import StrataGenerators.RetryGen

open Lambda RandomChoice Core Core.TypeSpec Imperative
open DatatypeGen
open StrataGenerators.Procedure

/-!
# Top-level generator for random well-typed Strata Core programs

Ties the per-declaration generators in `StrataGenerators.ProgramGen.Core`
together into a `Program` generator, threading the real ambient context
(`LContext CoreLParams`), type scope (`TContext Unit`), reserved-name set, and
pool of referenceable type constructors across a declaration fold.

Soundness (every generated program is `ProgramHasTypeA coreContext {} P`) and
completeness live in `StrataGenerators.ProgramGen.Sound` /
`StrataGenerators.ProgramGen.Complete`.
-/

namespace ProgramGen

/-! ## Fold state

The declaration fold threads:

* `C` is the ambient `LContext`. It grows at a declaration of a type constructor, of a datatype and of a
  function.
* `Γ` is the type scope. It grows at a declaration of an alias.
* `reserved` holds each name that a declaration gives so far, together with the reserved set at the start.
  Therefore each new name of a declaration differs from each other name of the program.
* `baseTypes` and `tyCons` hold the pool of the type constructors that a type can reference. A declaration
  of an abstract type grows that pool.
* `octx` and `pctx` hold the vocabularies of the operators that the generation of an expression uses. Each
  declaration of a function grows one of them: `octx` for a monomorphic function, and `pctx` for a
  polymorphic one. Therefore a later body can call each function that the program declares. -/

structure GenState where
  C : LContext CoreLParams
  Γ : TContext Unit
  reserved : List String
  baseTypes : BaseTys
  tyCons : TyCons
  /-- The datatypes that an earlier declaration gives and that a new block can reference, with the arity of
      each of them. This field is separate from `tyCons`, because these names are datatypes of `C` and not
      external known types. They reach
      `TySymInhab` through `.datatype` (carried by
      `Inv.dtPoolOk`) rather than `.external`. Grown by each datatype step. -/
  dtCons : TyCons
  /-- Monomorphic operator context for generated expressions (axiom bodies,
      function bodies, procedure contracts/bodies).

      Seeded with Core's primitives (`coreMonoOps`) and grown from **two** sources,
      which between them are what let a later body call anything the program
      declared earlier:

      * Each **step for a datatype** adds the derived functions of the block that the step declares, at their
        ground types. Those functions are the constructors, the testers, and the safe and unsafe accessors of a
        field, which `adtDerivedOps` gives.
      * each **monomorphic function declaration** (`genDeclFunction`), so a body
        generated later may call a function the program declares. Without it a
        program declared functions none of its own bodies could name, and
        `FunctionInlining` ran as the identity on every draw.

      Soundness is *indifferent* to this list: under the annotated spec an `.op`
      node takes its type from its own annotation, and `genLExpr_sound` quantifies over an arbitrary operator
      context. No field of `Inv` names this field, and that is why it needs no invariant. Therefore growth of
      this field widens the support and changes no obligation of a proof. The field `procs` differs, because its
      threading needs a field of the invariant. -/
  octx : OpCtx
  /-- The context of the polymorphic operators, which the `IndirPoly` rule uses. It grows from the same two
      sources as `octx`. Each step for a datatype adds the derived functions of the block under their full type
      *schemes*, which `adtDerivedPolyOps` gives. That form is what makes the accessors and the testers of a
      *polymorphic* datatype reachable, because `IndirPoly` unifies the result type of a scheme against the
      target, and it does not compare two types for equality. Each **declaration of a polymorphic function**
      also registers here, and not in `octx`, so a later body can call each declared function, and not the
      monomorphic ones only.

      Same soundness remark as `octx`: arbitrary values are sound, because
      `genLExpr_sound` quantifies over `pctx` and `Inv` never mentions it. -/
  pctx : PolyOpCtx
  /-- The polymorphic schemes that a datatype derives, and nothing else. This field is `pctx` without the
      primitives of Core. The generator gives this field, and not `pctx`, to the body of a *function* and of a
      *procedure*.

      The whole of `pctx` would give such a body the primitive schemes of Core, such as `Sequence.map`,
      `select` and `update`. That cost is high against its value. `IndirPoly` renames each bound type variable,
      it unifies at each split point, and it samples an instantiation for each candidate. Therefore a draw of a
      procedure becomes much slower. This field keeps the primitives out and forwards the derived schemes only,
      which gives a body exactly the reach that it needs. That reach is the constructors, the testers and the
      accessors of a datatype that an earlier declaration gives, at a small part of the cost.

      Soundness does not read this field, as it does not read `octx` and `pctx`. -/
  derivedPctx : PolyOpCtx
  /-- The procedures that a declaration gives *so far*, as callable signatures. The fold gives this field to
      `genProcedure`, so that a generated body can `call` one of them. That is what puts a real call between two
      procedures into the emitted program.

      Unlike `octx`/`pctx`, this is **not** soundness-neutral:
      `genProcedure_sound` needs `ProcSigCorresponds procs P`, i.e. every entry must
      resolve in the *enclosing* program. The fold cannot check that condition against a program that it has
      not finished, so the field `Inv.procsResolve` of the invariant carries the obligation, and a theorem
      discharges it at the top level. Read `ProgramGen.ProcSigThread`. -/
  procs : StrataGenerators.Stmt.ProcSigCtx
  deriving Inhabited

/-- The initial fold state: the Strata Core reference context `coreContext`, an
    empty type scope, the reserved seed (`initialReserved` over the default type
    constructors, plus every name Core already knows so generated names dodge
    them), and the default pool of referenceable type constructors. -/
def initState : GenState :=
  { C := coreContext
    Γ := {}
    reserved := initialReserved defaultBaseTypes defaultTyCons Core.KnownTypes.keywords
    baseTypes := defaultBaseTypes
    tyCons := defaultTyCons
    dtCons := []
    octx := coreMonoOps
    pctx := corePolyOps
    derivedPctx := []
    procs := [] }

/-! ## Bounds bundle

The knobs controlling declaration sizes, bundled so the fold and its proofs pass
one argument. -/

structure Bounds where
  /-- Max arity of a generated abstract type. -/
  maxTyConArity : Nat := 2
  /-- Max number of type parameters of an alias. -/
  maxAliasTyParams : Nat := 2
  /-- Size budget for alias bodies / `distinct` element types. -/
  tySize : Nat := 3
  /-- Depth budget for axiom expressions. -/
  exprDepth : Nat := 3
  /-- Depth budget for function bodies. -/
  funcDepth : Nat := 3
  /-- Max number of elements (hence declared constants) in a `distinct`
      assertion. -/
  maxDistinctVars : Nat := 3
  /-- Datatype-block knobs (forwarded to `genMutuallyRecursiveDatatypes`). -/
  maxExtraDatatypes : Nat := 1
  maxTyParams : Nat := 2
  maxExtraBaseConstrs : Nat := 1
  maxRecConstrs : Nat := 2
  maxArgs : Nat := 2
  maxDatatypeSize : Nat := 2
  /-- Element-size budget for a generated procedure (type args, signature types,
      body expression sizes). -/
  procSize : Nat := 3
  /-- Max body statement count for a generated procedure. -/
  procLen : Nat := 3
  /-- Which families of a datatype's auto-generated functions later declarations
      may call: constructors, testers, and safe/unsafe field accessors by default;
      eliminators excluded (see `DerivedOpFamilies`). -/
  derivedFamilies : DerivedOpFamilies := {}
  deriving Inhabited

/-! ## Emitting declarations while threading state

Each `genDecl*` gives a *list* of declarations to append, together with the new state. That list is empty
when an add to the checker fails, and the state then stays the same. It holds one declaration when the add
succeeds. A list makes the case of a skip after a failure a first-class case, and it keeps the soundness
proof a split of `DeclsHasType'` into its two constructors. -/

/-- Result of one declaration step: the declarations to append and the new
    state. -/
abbrev StepResult := List Decl × GenState

/-- Add each of `names` to the reserved set, and grow the referenceable pool by an
    abstract type of the given `arity` (nullary → base type, else applied
    constructor). -/
def GenState.addAbstract (s : GenState) (name : String) (arity : Nat)
    (C' : LContext CoreLParams) : GenState :=
  { s with
    C := C'
    reserved := name :: s.reserved
    baseTypes := if arity = 0 then name :: s.baseTypes else s.baseTypes
    tyCons := if arity = 0 then s.tyCons else (name, arity) :: s.tyCons }

/-- Generate an abstract-type declaration and, if its name does not clash in `C`,
    emit it and grow both the context and the referenceable pool. On a clash (impossible
    for a freshly drawn name, but handled uniformly) the state is unchanged. -/
def genDeclAbstract [Gen G] (s : GenState) (b : Bounds) : G StepResult := do
  let (decl, name, arity) ← genAbstractType s.reserved b.maxTyConArity
  match s.C.addKnownTypeWithError { name := name, metadata := arity } default with
  | .ok C' => pure ([decl], s.addAbstract name arity C')
  | .error _ => pure ([], s)

/-- Generate a type-alias declaration and emit it, extending the type scope with
    the alias (its body is stored verbatim; `mkAliasDecl` keeps it alias-free by
    deriving `typeArgs` from the body). -/
def genDeclAlias [Gen G] (s : GenState) (b : Bounds) : G StepResult := do
  let (decl, name) ← genAlias s.baseTypes s.tyCons s.reserved b.maxAliasTyParams b.tySize
  -- Extend Γ with the alias matching what `DeclHasType'.type_syn` records.
  let Γ' := match decl with
    | .type (.syn ts) _ =>
      { s.Γ with aliases := { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } :: s.Γ.aliases }
    | _ => s.Γ
  pure ([decl], { s with Γ := Γ', reserved := name :: s.reserved })

/-- Generate an axiom declaration (Bool expression) and emit it. Context/scope
    unchanged. -/
def genDeclAxiom [Gen G] (s : GenState) (b : Bounds) : G StepResult := do
  let (decl, name) ← genAxiom s.octx s.pctx s.reserved b.exprDepth
  pure ([decl], { s with reserved := name :: s.reserved })

/-- Declare a group of constants of arity 0 at the type `τ`, one for each name, through the
    `addFactoryFunctionWithError` of the checker, which is the same gate as the step for a function. The
    function gives the grown context and the emitted declarations. It gives `none` when a name clashes in the
    factory, and the whole step for a `distinct` declaration is then
    abandoned, so the group never references an undeclared constant).

    All-or-nothing rather than skip-the-clashing-one: a `distinct` whose elements
    are only *partly* declared would be exactly the bug this replaces. -/
def addConstants (C : LContext CoreLParams) (τ : LMonoTy) :
    List String → Option (LContext CoreLParams × List Decl)
  | [] => some (C, [])
  | c :: cs =>
    match C.addFactoryFunctionWithError (constantFunc c τ).toLFunc with
    | .ok C₁ =>
      match addConstants C₁ τ cs with
      | some (C', ds) => some (C', mkConstantDecl c τ :: ds)
      | none => none
    | .error _ => none

/-- Generate a `distinct` declaration together with the constants it ranges over:
    `function c₀ () : τ; … distinct [d]: [c₀, …];`. The constants precede the
    `distinct` in the emitted list, so every `.op` element refers to a function
    declared earlier in the program.

    This step grows `C` (by the constants' factory entries) and reserves
    `numVars + 1` names; `Γ` and the type vocabulary are unchanged. -/
def genDeclDistinct [Gen G] (s : GenState) (b : Bounds) : G StepResult := do
  let (name, τ, constNames) ←
    genDistinctAssertion s.baseTypes s.tyCons s.reserved b.maxDistinctVars b.tySize
  match addConstants s.C τ constNames with
  | some (C', constDecls) =>
    pure (constDecls ++ [mkDistinctDecl name (distinctElems τ constNames)],
          { s with C := C', reserved := constNames ++ name :: s.reserved })
  | none => pure ([], s)

/-- Generate a datatype block and, if `addMutualBlock` accepts it, emit it and
    grow the context. The block references the *threaded* pool
    (`s.baseTypes`/`s.tyCons`), so it may mention any abstract type declared
    earlier in the program: interleaving direction (2).
    The fold invariant carries `ContextOk` at
    that grown pool (`Inv.ctxOk`), re-established at each abstract-type step
    by `contextOk_addKnownType_grow`.

    Its names are drawn fresh against the whole threaded `reserved` set (which by
    the fold invariant contains every name the program has declared so far, *and*
    every type name `C` knows), so the block's names avoid both `C`'s existing
    types (→ `MutualADTWF`) and every other declaration's name (→
    `getNames.Nodup`). -/
def genDeclDatatype [Gen G] (s : GenState) (b : Bounds) : G StepResult := do
  -- The pool of the applied constructors is the external pool *and* the pool of the datatypes that an earlier
  -- declaration gives. The generator draws such a datatype exactly as it draws each other applied constructor,
  -- at its declared arity, and with no recursive call inside its arguments. Therefore the fields about the
  -- arguments of a constructor need no change. Only the argument about inhabitance differs, and
  -- `DatatypePoolOk` gives it.
  let block ← genMutuallyRecursiveDatatypes s.baseTypes (s.tyCons ++ s.dtCons)
    b.maxExtraDatatypes b.maxTyParams b.maxExtraBaseConstrs b.maxRecConstrs
    b.maxArgs b.maxDatatypeSize s.reserved
  -- Pin the `CoreLParams`-native `Inhabited`/`ToFormat` instances (the ones the
  -- spec's `DeclHasType'.type_data` fixes), rather than the shadowing `ToFormat
  -- Unit` instances the sub-generators bring into scope, so a gated `= .ok C'`
  -- matches the spec constructor with no instance-diamond bridge in the proof.
  match @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams s.C block with
  | .ok C' =>
    let names := block.map (·.name)
    -- Grow the prior-datatype pool by this block's datatypes, so a *later* block may
    -- reference them. Each enters at its own arity (`typeArgs.length`).
    let newPool := block.map (fun d => (d.name, d.typeArgs.length))
    -- Grow the vocabularies of the operators by the *derived* functions of the block, which are the
    -- constructors, the testers and both kinds of accessor. Therefore the expressions of each *later*
    -- declaration can call them. `addMutualBlock` has pushed
    -- these very functions into `C'.functions` (it runs the same
    -- `genBlockFactory` that `adtDerivedOps`/`adtDerivedPolyOps` read), so the
    -- vocabulary and the context stay in step by construction.
    pure ([.type (.data block) .empty],
          { s with C := C', reserved := names ++ s.reserved
                   dtCons := newPool ++ s.dtCons
                   -- Rebuild the context (rather than mutating a list) so the
                   -- by-type index covers the merged vocabulary: `OpCtx` holds a
                   -- hash map from a type to its operators, plus the `agrees` proof
                   -- tying it to the list, and `ofList` is what re-establishes both.
                   octx := OpCtx.ofList (adtDerivedOps block b.derivedFamilies ++ s.octx.ops)
                   pctx := adtDerivedPolyOps block b.derivedFamilies ++ s.pctx
                   derivedPctx :=
                     adtDerivedPolyOps block b.derivedFamilies ++ s.derivedPctx })
  | .error _ => pure ([], s)

/-! ### The generator emits no block that names an earlier *alias*

`genDeclDatatype` draws its block over a pool of type *constructors*, which
never contains an alias name: `genDeclAlias` extends only `Γ.aliases` and
`reserved`, never `baseTypes`/`tyCons`/`dtCons` (the invariant recorded by
`Inv.aliasPoolDisjoint`). So no generated block mentions an alias.

A step that *did* draw over the alias names and then de-aliased with the checker's
own `MutualDatatype.resolveAliases` was prototyped and **removed**, because it
could not be proved sound: generator soundness gives `MutualADTWF s.C block₀` for
the block that it *draws*, and `DeclHasType'.type_data` needs it for the block that the context *stores*,
which is the block after the resolution of the aliases. `MutualADTWF` does **not** survive that resolution.
An alias whose body is an arrow can move a name of the block into the domain of an arrow, and that breaks
strict positivity.

That gap is not reachable by *this* generator (`genArgTy` draws application
arguments at `recCallsAllowed := false`, so a block name never appears inside an
alias application's arguments), so the removed step was unproven rather than
known-unsound. It is parked pending a question to the Strata team about whether
positivity is meant to be checked pre- or post-resolution. -/

/-- How many times a declared function's operator entry is repeated in `octx` /
    `pctx`.

    **Why a repeat rather than a single entry.** `genIndir` and `genIndirPoly` pick an
    operator with `elements`, which is **uniform** over the candidates
    `findOpsInCtx` / `findPolymorphicOps` return for the target type. Those candidate
    lists are large: 105 operators of `Core.Factory` produce `bool` when fully
    applied, and many of them give an `int`. Therefore one entry for a declared function has a very small share
    at a leaf of the type `bool`, and a draw almost never selects it, although the context holds it.

    A list that holds the entry `n` times gives it `n` times its share, because `elements` is uniform over that
    list. That is the same method as a weight in a `frequency` call, through the number of the copies in a list,
    because an `OpCtx` has no field for a weight.

    **Soundness is unaffected**, for the same reason the vocabularies can be grown at
    all: `genLExpr_sound` quantifies over an arbitrary `octx`/`pctx`, and a repeated
    entry changes the distribution only, and not the support. `opsOfTypeList` is a `filterMap`, so a duplicate
    entry gives a duplicate candidate that names the same operator at the same type, and the generator can
    already give that expression.
    `OpCtx.agrees` still holds by construction, since `OpCtx.ofList` recomputes the
    index from the list it is given.

    The value 24 is chosen to put a declared function at roughly 1-in-5 odds at a
    `bool` leaf (24 of 105 + 24) and near even odds at `int`. -/
def declaredFuncWeight : Nat := 24

/-- The curried type of a function: `in₁ → ⋯ → inₙ → out`, built exactly as
    `coreMonoOps` builds it for a `Core.Factory` function. -/
def funcCurriedTy (f : Function) : LMonoTy :=
  LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)

/-- The `OpCtx` entry for a **monomorphic** declared function: its name paired with
    its curried type.

    `none` for a polymorphic function. `OpCtx` holds a monotype per operator, so a
    function with a non-empty `typeArgs` would have to be recorded at a type
    mentioning a free type variable, which `findOpsOfType` would then match by
    accident. A polymorphic function goes to `funcPolyOpEntry` instead. -/
def funcOpEntry (f : Function) : Option (String × LMonoTy) :=
  if f.typeArgs.isEmpty then some (f.name.name, funcCurriedTy f) else none

/-- The `PolyOpCtx` entry for a **polymorphic** declared function: its name paired
    with its type *scheme*, `∀ typeArgs. in₁ → ⋯ → inₙ → out`.

    The function gives `none` for a monomorphic function, which belongs in `octx` instead. An entry with an
    empty list of binders would make `findPolymorphicOps` do the work of `findOpsOfType` with more steps, and
    it would register the operator two times.

    The binder list is the function's own `typeArgs`, which is what makes the entry
    well formed for `findPolymorphicOps`: that function alpha-renames `boundVars`
    away from each type variable that is already in use, it decomposes the arrow, and it unifies the remaining
    result type against the target. Therefore the binders must be exactly the variables of the body that a call
    site can instantiate. For a generated function, those are the type arguments, because `FuncWF` needs each
    free type variable of the signature to be one of them.

    A function whose `typeArgs` contains a variable the signature never mentions is
    still fine here: `findPolymorphicOps` samples an instantiation per bound
    variable and the unused one simply has no effect on the result type. -/
def funcPolyOpEntry (f : Function) : Option (String × LTy) :=
  if f.typeArgs.isEmpty then none
  else some (f.name.name, .forAll f.typeArgs (funcCurriedTy f))

/-- Generate a function that is not recursive, and rename it to a fresh name, so that the names of the program
    stay distinct and no change to `FuncHasType'` is necessary, because that specification puts no condition on
    a name. When `addFactoryFunctionWithError` accepts the function, emit it, grow the factory of the context,
    and register it in the vocabulary of the operators.

    **The `octx` growth is what lets a later body call this function.** Growing `C`
    alone registers the function with the *typechecker*; expression generation draws
    its `.op` nodes from `octx`, so without this a generated program declared
    functions that none of its own bodies could mention, and every pass that needs a
    call to a declared function (`FunctionInlining`, through
    `Factory.callOfLFunc`) ran as the identity. See the `FunctionInlining` notes in
    `StrataGenerators/ProgramGen/UnprovenTransforms.lean`.

    This is **soundness-neutral**, which is what makes it a one-line change rather
    than a proof effort: under the annotated spec an `.op` node is typed from its own
    annotation, so `genLExpr_sound` quantifies over an arbitrary `octx` and the
    `Inv` invariant never mentions the field. Seeding it widens the support without
    touching any obligation. Contrast `procs`, whose threading *did* need a new
    invariant field (`Inv.procsResolve`) because `genProcedure_sound` requires every
    entry to resolve in the enclosing program.

    Registration goes to `octx` for a monomorphic function and to `pctx` for a
    polymorphic one, so **every** declared function becomes callable rather than only
    the monomorphic minority (measured: 44 of 158 declared functions are
    monomorphic, so the `pctx` half covers the other 114). Both are registered only
    on the `.ok` branch: a function the context rejects is not emitted, so recording
    it would offer a call target the program does not declare. -/
def genDeclFunction [Gen G] (s : GenState) (b : Bounds) : G StepResult := do
  let func₀ ← genFunction [] s.octx b.funcDepth s.derivedPctx
  let name ← DatatypeGen.genFreshName s.reserved
  let func := { func₀ with name := ⟨name, ()⟩ }
  match s.C.addFactoryFunctionWithError func.toLFunc with
  | .ok C' =>
    let octx' := match funcOpEntry func with
      | some entry => OpCtx.ofList (s.octx.ops ++ List.replicate declaredFuncWeight entry)
      | none => s.octx
    let pctx' := match funcPolyOpEntry func with
      | some entry => s.pctx ++ List.replicate declaredFuncWeight entry
      | none => s.pctx
    pure ([.func func .empty],
          { s with C := C', reserved := name :: s.reserved,
                   octx := octx', pctx := pctx' })
  | .error _ => pure ([], s)

/-- Generate a procedure and rename it to a globally fresh name (the program's
    names stay distinct without touching `ProcHasType'`, which does not constrain
    the procedure name). The body is generated under the *real* ambient context
    `{ s.C with rigidTypeVars := typeArgs }` and type-scope `s.Γ` (Option B: the
    generator threads `C`/`Γ`), under the *accumulated* callable-procedure context
    `s.procs`, so the body may `call` any procedure declared earlier in the
    program. Procedures leave `C`/`Γ` unchanged (per `DeclHasType'.proc`), so there
    is no gate.

    The emitted procedure is then *registered* in `s.procs` (at its renamed,
    globally fresh name) so later procedures may call it. `M` is recovered as the
    longest common prefix of `inputs`/`outputs`, which is exact for a generated
    procedure (see `commonPrefix` in `ProgramGen.Core`). -/
def genDeclProcedure [Gen G] (s : GenState) (b : Bounds) : G StepResult := do
  let proc₀ ← genProcedure s.octx s.procs s.C s.Γ b.procSize b.procLen s.derivedPctx
  let name ← DatatypeGen.genFreshName s.reserved
  let proc := { proc₀ with header := { proc₀.header with name := ⟨name, ()⟩ } }
  let M := commonPrefix proc.header.inputs proc.header.outputs
  let sig : StrataGenerators.Stmt.ProcSig :=
    { pname := name
      typeArgs := proc.header.typeArgs
      M := M
      I := proc.header.inputs.drop M.length
      O := proc.header.outputs.drop M.length }
  pure ([.proc proc .empty],
        { s with reserved := name :: s.reserved, procs := sig :: s.procs })

/-- Whether the fold has yet declared a function that a later body could call.

    `genDeclFunction` registers each accepted function in `octx` or `pctx`, so the
    combined vocabulary size exceeding the seed's is exactly "some function has been
    declared and accepted". Used only to steer the weights below; nothing about
    correctness depends on it. -/
def hasCallableFunc (s : GenState) : Bool :=
  s.octx.ops.length + s.pctx.length >
    initState.octx.ops.length + initState.pctx.length

/-- The declaration-kind selector: pick one of the seven declaration kinds and run
    its step generator. Every kind here is covered by `genProgram_sound`.

    **Weights.** Procedures, functions and datatype blocks carry the interesting
    structure (bodies, calls, constructor arguments), so they are weighted up;
    abstract types, aliases, axioms and `distinct` are cheap one-liners and are
    weighted down. The procedure weight matters most for *inter-procedure calls*:
    a call needs at least two procedure declarations (the first runs with
    `procs = []`), so the odds of a call scale roughly with the square of this
    weight's share.

    **Order-aware bias toward functions first.** A body can only call a function the
    fold has *already* declared, because `genDeclFunction` registers it in the two operator contexts after the
    step. Under the plain weights, a function with a body rarely comes before the first procedure, and a pass
    that inlines a function then has almost nothing to inline. Therefore, while no function is callable yet,
    which the predicate `hasCallableFunc` decides, the weight of a function rises to 6 and the weight of a
    procedure falls to 1. After one function is callable, the original weights of 3 and 4 return. The effect is
    to put a function early, and it removes no procedure from an early position.

    This is a **distribution-only** change, and that is what keeps it out of the
    proofs. `frequency` and `oneOf` have the same support whenever each weight is positive, because
    `mem_support_frequency_iff` and `mem_support_oneOf_iff` each reduce to the statement that one branch gave
    the value. Therefore no statement of soundness and no statement of completeness changes, and only the
    frequency of each kind changes. Both vectors of the weights keep each entry positive, so the support is the
    same in each phase. `genDeclStep_sound`
    discards the weight it inverts out of the `frequency` (`_hw`) and pins each
    branch by the list's structure, so it is unaffected. The same argument licenses
    the `wExit`/`wCall` weights inside `genStmt`. -/
def genDeclStep [Gen G] (s : GenState) (b : Bounds) : G StepResult :=
  -- `(wFunc, wProc)`: front-load functions until one is callable.
  let (wFunc, wProc) := if hasCallableFunc s then (3, 4) else (6, 1)
  let gs : List (Nat × (Unit → G StepResult)) :=
    [ (1, fun () => genDeclAbstract s b)
    , (1, fun () => genDeclAlias s b)
    , (1, fun () => genDeclAxiom s b)
    , (1, fun () => genDeclDistinct s b)
    , (3, fun () => genDeclDatatype s b)
    , (wFunc, fun () => genDeclFunction s b)
    , (wProc, fun () => genDeclProcedure s b) ]
  frequency gs (by
    -- The four fixed entries of the weight 1, and the weight of the datatype step, already make the sum
    -- positive. Therefore this obligation holds in each phase, and the proof needs no split on the `if`.
    simp only [gs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega)

/-- Fold `n` declaration steps, threading state and accumulating (in order) the
    emitted declarations. -/
def genDeclsFold [Gen G] (s : GenState) (b : Bounds) : Nat → G (List Decl × GenState)
  | 0 => pure ([], s)
  | n + 1 => do
    let (ds, s') ← genDeclStep s b
    let (rest, s'') ← genDeclsFold s' b n
    pure (ds ++ rest, s'')

/-- Generate a whole program: fold `numDecls` declaration steps from `initState`
    and package the emitted declarations into a `Program`. -/
def genProgram [Gen G] (numDecls : Nat := 6) (b : Bounds := {}) : G Program := do
  let (decls, _) ← genDeclsFold initState b numDecls
  pure { decls := decls }

/-! ## Running the generator -/

/-! ### A draw goes through `Plausible.Gen`, and not through `IO`

The direct interpretation at `G := IO` is **not reliable for a procedure**. The `IO` interpretation of
`RandomChoice` in Basalt turns a draw from an empty support in a nested sub-generator into a panic, and the
body of a procedure nests deeply enough to reach one often. Under `G := IO`, a draw of an abstract type, of
an alias, of a `distinct` declaration and of a datatype almost always survives. A draw of an axiom and of a
function survives most of the time. A draw of a procedure survives rarely, and a *longer* body of a procedure
survives even less often. Therefore a larger size for a procedure is worse under `IO`, and not better.

`Plausible.Gen` is the reliable interpretation, because a failed draw is a *catchable exception* there, and
not a panic. Therefore `sample` runs the generator at `G := Plausible.Gen`, under `retryGen`, and it executes
that generator with `Plausible.Gen.run`. Each Tyche panel for a procedure uses the same pattern.

**The fuel for the retries must grow with the number of the declarations.** The remaining cause of a failure
is the `inhabitedWitness` error of the expression generator, which happens when nothing in scope inhabits a
compound argument type, and which is a known gap. Each declaration is an independent chance of that failure.
Therefore the probability that a whole program succeeds falls quickly with the number of the declarations,
and the fuel must absorb that fall.

None of this changes a proof. Each proof is stated over `SetGen.Set`, which is the semantics of a support,
and it does not depend on an interpretation. -/

/-- Draw one random well-typed program, through the `Plausible.Gen` interpretation, with retries.

    The parameter `fuel` bounds the number of the retries for one draw, and it must grow with the number of
    the declarations. The parameter `size` is the size parameter of the harness.

    The default fuel is large, because a body can call a derived function of a datatype. A call to the tester
    or to an accessor of a *polymorphic* datatype goes through the `IndirPoly` rule, which samples an
    instantiation of the candidate, and nothing can often fill that instantiation. That is the same
    `inhabitedWitness` failure as above, and a run reaches it more often when a body has more to reach.

    A value of `false` for each flag of `Bounds.derivedFamilies` removes each call to a derived function, and
    it also removes the need for that fuel. That is the knob for a consumer that needs a cheaper draw more
    than it needs the coverage of a datatype. -/
def sample (numDecls : Nat := 12) (b : Bounds := {})
    (fuel : Nat := 30000) (size : Nat := 10) : IO Program :=
  Plausible.Gen.run (retryGen fuel (genProgram (G := Plausible.Gen) numDecls b)) size

end ProgramGen
