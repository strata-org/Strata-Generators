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

* `C`        — the ambient `LContext` (grows on type-con / datatype / func adds);
* `Γ`        — the type scope (grows on alias adds);
* `reserved` — every name declared so far, plus the seed reserved set, so newly
               drawn declaration names are globally distinct (`getNames.Nodup`);
* `baseTypes` / `tyCons` — the pool of referenceable type constructors, grown
               by abstract-type declarations.

* `octx` / `pctx` — the operator vocabularies feeding expression generation, grown
               by each function declaration (`octx` for a monomorphic function,
               `pctx` for a polymorphic one), so a later body may call any function
               the program declares. -/

structure GenState where
  C : LContext CoreLParams
  Γ : TContext Unit
  reserved : List String
  baseTypes : BaseTys
  tyCons : TyCons
  /-- The *previously declared datatypes* a new block may reference, with their
      arities: interleaving direction (4). Kept separate from `tyCons` because these
      names are datatypes of `C`, not external known types: they reach
      `TySymInhab` through `.datatype` (carried by
      `Inv.dtPoolOk`) rather than `.external`. Grown by each datatype step. -/
  dtCons : TyCons
  /-- Monomorphic operator context for generated expressions (axiom bodies,
      function bodies, procedure contracts/bodies).

      Seeded with Core's primitives (`coreMonoOps`) and grown from **two** sources,
      which between them are what let a later body call anything the program
      declared earlier:

      * each **datatype step**, with the ground-typed derived functions of the block
        just declared — its constructors, testers, and safe/unsafe field accessors
        (`adtDerivedOps`). Before this the list was fixed for the whole fold and no
        body ever mentioned a datatype;
      * each **monomorphic function declaration** (`genDeclFunction`), so a body
        generated later may call a function the program declares. Without it a
        program declared functions none of its own bodies could name, and
        `FunctionInlining` ran as the identity on every draw.

      Soundness is *indifferent* to this list: under the annotated spec an `.op`
      node is typed from its own annotation (`genLExpr_sound` quantifies over an
      arbitrary `octx`), and `Inv` never mentions the field, which is why it needs
      none. So growing it widens the support without touching any proof obligation —
      unlike `procs`, whose threading needed a new invariant field. That is what made
      both growths plumbing changes rather than proof efforts. -/
  octx : OpCtx
  /-- Polymorphic operator context (the `IndirPoly` rule), grown from the same two
      sources as `octx`: each datatype step adds the block's derived functions under
      their full type *schemes* (`adtDerivedPolyOps`) — the projection that makes a
      *polymorphic* datatype's accessors and testers reachable, since `IndirPoly`
      unifies the scheme's return type against the target instead of comparing types
      with `==` — and each **polymorphic function declaration** registers here rather
      than in `octx`, so every declared function becomes callable by a later body
      rather than only the monomorphic minority.

      Same soundness remark as `octx`: arbitrary values are sound, because
      `genLExpr_sound` quantifies over `pctx` and `Inv` never mentions it. -/
  pctx : PolyOpCtx
  /-- The **datatype-derived** polymorphic schemes only — `pctx` minus Core's
      primitives. This, not `pctx`, is what generated *function* and *procedure*
      bodies receive.

      Function and procedure bodies previously ran at `pctx = []` (only axioms saw a
      polymorphic vocabulary). Handing them the whole of `pctx` would newly expose
      Core's 16 primitive schemes (`Sequence.map`, `select`, `update`, …) there, and
      that is expensive out of proportion to its value: `IndirPoly` alpha-renames,
      unifies at every split point, and samples instantiations for each candidate, so
      a procedure draw went from ~60 ms to ~7 s — a change nothing in this task asks
      for. Keeping the primitives where they were and forwarding only the derived
      schemes gives bodies exactly the new reach they need (an earlier datatype's
      testers and accessors) at a fraction of the cost.

      Soundness is indifferent, as for `octx`/`pctx`. -/
  derivedPctx : PolyOpCtx
  /-- The procedures declared *so far*, as callable signatures. Passed to
      `genProcedure` so a generated body may `call` them — this is what makes the
      emitted program contain genuine inter-procedure calls.

      Unlike `octx`/`pctx`, this is **not** soundness-neutral:
      `genProcedure_sound` needs `ProcSigCorresponds procs P`, i.e. every entry must
      resolve in the *enclosing* program. The fold cannot check that against a
      program it has not finished building, so the obligation is carried as the
      invariant field `Inv.procsResolve` and discharged at the top level — see
      `ProgramGen.ProcSigThread`. -/
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

Each `genDecl*` returns a *list* of declarations to append (either `[]` when a
checker add fails — leaving the state unchanged — or `[d]` when it succeeds) plus
the updated state. Returning a list makes the "skip on failure" case first-class
and keeps the soundness proof a clean `DeclsHasType'` cons/nil split. -/

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

/-- Declare a run of 0-ary constants at type `τ`, one per name, using the
    checker's own `addFactoryFunctionWithError` — the same gate as the function
    step. Returns the grown context and the emitted declarations, or `none` if any
    name clashes in the factory (in which case the whole `distinct` step is
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
  -- The applied-constructor pool is the external one *plus* the prior-datatype
  -- pool (direction (4)). A prior datatype is drawn exactly like any other applied
  -- constructor — at its declared arity, with `recCallsAllowed := false` inside its
  -- arguments — so `argsWF`/`argVarsScoped` are unaffected; only the inhabitance
  -- argument differs, and `DatatypePoolOk` supplies it.
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
    -- Grow the operator vocabularies by the block's *derived* functions —
    -- constructors, testers, and both accessor variants — so every *later*
    -- declaration's expressions can call them. `addMutualBlock` has just pushed
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

/-! ### A block that mentions a prior *alias* — deliberately not generated

`genDeclDatatype` draws its block over a pool of type *constructors*, which
never contains an alias name: `genDeclAlias` extends only `Γ.aliases` and
`reserved`, never `baseTypes`/`tyCons`/`dtCons` (the invariant recorded by
`Inv.aliasPoolDisjoint`). So no generated block mentions an alias.

A step that *did* draw over the alias names and then de-aliased with the checker's
own `MutualDatatype.resolveAliases` was prototyped and **removed**, because it
could not be proved sound: generator soundness gives `MutualADTWF s.C block₀` for
the block *drawn*, while `DeclHasType'.type_data` needs it for the block *stored*
(`resolveAliases block₀`), and `MutualADTWF` is **not** preserved by alias
resolution — an arrow-bodied alias can move a block name into an arrow's domain,
breaking strict positivity.

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
    applied, and 27 produce `int`. So a single entry for a declared function gives it
    a ~1% chance at a `bool`-typed leaf, and the measured result was 1 mention across
    200 programs — the function was registered correctly and simply never drawn.

    Repeating the entry `n` times multiplies its share, because `elements` is uniform
    over a list that now holds it `n` times. This is the same trick the weighted
    `frequency` calls use elsewhere, expressed through list multiplicity because
    `OpCtx` has no weight field.

    **Soundness is unaffected**, for the same reason the vocabularies can be grown at
    all: `genLExpr_sound` quantifies over an arbitrary `octx`/`pctx`, and a repeated
    entry changes only the distribution, not the support (`opsOfTypeList` is a
    `filterMap`, so a duplicate contributes a duplicate candidate naming the same
    operator at the same type — an expression the generator could already produce).
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

    `none` for a monomorphic function, which belongs in `octx` instead — an entry
    with an empty binder list would make `findPolymorphicOps` do the work of
    `findOpsOfType` with extra steps, and would double-register the operator.

    The binder list is the function's own `typeArgs`, which is what makes the entry
    well formed for `findPolymorphicOps`: that function alpha-renames `boundVars`
    away from the type variables already in use, decomposes the arrow, and unifies
    the residual result type against the target. So the binders must be exactly the
    variables of the body that are meant to be instantiable — which for a generated
    function is `typeArgs`, since `FuncWF` requires the signature's free type
    variables to be a subset of them.

    A function whose `typeArgs` contains a variable the signature never mentions is
    still fine here: `findPolymorphicOps` samples an instantiation per bound
    variable and the unused one simply has no effect on the result type. -/
def funcPolyOpEntry (f : Function) : Option (String × LTy) :=
  if f.typeArgs.isEmpty then none
  else some (f.name.name, .forAll f.typeArgs (funcCurriedTy f))

/-- Generate a non-recursive function, rename it to a globally fresh name (so the
    program's names stay distinct without touching `FuncHasType'`, which does not
    constrain the name), and — if `addFactoryFunctionWithError` accepts it — emit
    it, grow the context's function factory, and register it in the operator
    vocabulary.

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
    fold has *already* declared, because `genDeclFunction` registers it in
    `octx`/`pctx` after the fact. Under uniform-at-weight selection a bodied function
    preceded the first procedure in only 4 of 200 draws, so `FunctionInlining` had
    almost nothing to inline. While no function is yet callable
    (`hasCallableFunc s = false`) the function weight is therefore raised to 6 and
    the procedure weight dropped to 1; once one exists the original 3-and-4 weights
    resume. The effect is to front-load functions without removing procedures from
    the early positions.

    This is a **distribution-only** change, and that is what keeps it out of the
    proofs: `frequency` and `oneOf` have the same support whenever every weight is
    positive (`mem_support_frequency_iff` / `mem_support_oneOf_iff` both reduce to
    "some branch produced it"), so no soundness or completeness statement changes —
    only how often each kind is drawn. Both weight vectors keep every entry
    positive, so the support is the same in either phase. `genDeclStep_sound`
    discards the weight it inverts out of the `frequency` (`_hw`) and pins each
    branch by the list's structure, so it is unaffected. -/
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
    -- The four fixed weight-1 entries and the datatype weight already make the sum
    -- positive, so this holds whatever phase `(wFunc, wProc)` is in — no case split
    -- on the `if` is needed.
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

/-! ### Sampling: run through `Plausible.Gen`, not `IO`

The direct `G := IO` interpretation is **unreliable for procedures**. Basalt's
`IO` interpretation of `RandomChoice` turns an empty-support draw in a nested
sub-generator into a `panic!`, and procedure bodies nest deeply enough to hit one
often. Measured per-step survival under `G := IO`, 300 draws each:

| step | survival at `procLen = 3` | at `procLen = 6` |
| --- | --- | --- |
| abstract / alias / distinct / datatype | 300/300 | 300/300 |
| axiom | ~176/300 | ~182/300 |
| function | ~205/300 | ~209/300 |
| **procedure** | **~52/300** | **~5/300** |

Note the direction: under `IO`, *longer* procedure bodies are ~10× **less** likely
to survive, so raising `procSize`/`procLen` there is counter-productive.

`Plausible.Gen` is the robust interpretation — a failed draw is a *catchable
exception* rather than a panic — so `sample` runs the generator at
`G := Plausible.Gen` under `retryGen` and executes it with `Plausible.Gen.run`.
This is the same pattern the Tyche procedure panels use
(`StrataGenerators/TycheViz.lean`).

**Retry fuel has to scale with `numDecls`.** The residual failure mode is
`inhabitedWitness` from the expression generator (a compound argument type that
nothing in scope inhabits — a known incompleteness). Each
declaration is an independent chance to hit it, so whole-program success decays
geometrically in `numDecls` and the fuel must absorb it. Measured, default bounds,
`size = 10`:

| `numDecls` | survival at `fuel = 200` |
| --- | --- |
| 2 / 4 / 6 | 40/40 |
| 8 | 4/40 |
| 12 | 0/40 |

| `fuel` (at `numDecls = 12`) | survival |
| --- | --- |
| 200 | 0/20 |
| **2000** | **20/20** |
| 8000 | 20/20 |

Hence the `fuel := 4000` default — comfortably inside the plateau. (For contrast,
under `G := IO` the same failure is an uncatchable `panic!`, which is why that
path is not used here.)

None of this touches the proofs, which are stated over `SetGen.Set` (the support
semantics) and are interpretation-independent. -/

/-- Draw a single random well-typed program, via the `Plausible.Gen`
    interpretation with retries.

    `fuel` bounds the retries per draw — it must grow with `numDecls`, see the
    table above; `size` is Plausible's size parameter.

    **The default rose from 4000 to 30000** when datatype-derived functions became
    callable. A body that calls a *polymorphic* datatype's tester or accessor goes
    through the `IndirPoly` rule, whose candidate instantiation is sampled and so
    is often unfillable — the same `inhabitedWitness` failure mode the table above
    describes, just hit more often now that there is more to reach. Measured at
    `numDecls = 12`, default bounds:

    | configuration | `fuel = 4000` | `fuel = 30000` |
    | --- | --- | --- |
    | `derivedFamilies` all off (no ADT calls) | 8/8 | 8/8 |
    | default (ADT calls enabled) | 1/8 | 8/8 |

    Setting every `Bounds.derivedFamilies` flag to `false` recovers the old
    behaviour *and* the old fuel requirement, which is the knob to reach for if a
    consumer needs the cheaper draw more than it needs ADT coverage. -/
def sample (numDecls : Nat := 12) (b : Bounds := {})
    (fuel : Nat := 30000) (size : Nat := 10) : IO Program :=
  Plausible.Gen.run (retryGen fuel (genProgram (G := Plausible.Gen) numDecls b)) size

end ProgramGen
