import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import StrataGenerators.DatatypeGen
import StrataGenerators.DatatypeGenProofs
import StrataGenerators.FunctionHasTypeAGen
import StrataGenerators.ProcedureHasTypeAGen
import StrataGenerators.HasTypeAGen.Defs
import Strata.Languages.Core.ProgramTypeSpec

open Lambda RandomChoice Core Core.TypeSpec Imperative
open DatatypeGen
open StrataGenerators.Procedure

namespace Lambda

/-- The erroring form of `LContext.addFactoryFunction`.

    Strata gives the *total* `LContext.addFactoryFunction`, which changes nothing after a clash of two names.
    The generator needs the form that gives an error, because that form is the gate that the program checker
    applies, and `FactoryExtendedBy` of `ProgramTypeSpec` describes exactly its successful outcome. This
    definition is a wrapper over `Factory.tryPush`, which Strata does give. -/
def LContext.addFactoryFunctionWithError (C : LContext CoreLParams) (fn : LFunc CoreLParams) :
    Except Strata.Message (LContext CoreLParams) := do
  .ok { C with functions := (← C.functions.tryPush fn) }

end Lambda

/-!
# Generator definitions for random well-typed Strata Core *programs*

This module holds the **code of the generator** for a random Strata Core `Program` that is well typed against
`Core.TypeSpec.ProgramHasType'`, at the annotated specification, which gives `ProgramHasTypeA`. The proofs are
in `StrataGenerators.ProgramGen`.

A `Program` is a list of declarations. This module uses the existing generator for each declaration body that
has one. `DatatypeGen.genMutuallyRecursiveDatatypes` gives a block of algebraic datatypes, and `genFunction`
gives a function. This module adds a generator for the four other kinds of declaration: an **abstract type**,
a **type alias**, an **axiom** and a **`distinct`** assertion.

## Threading the real context

Unlike the sub-generators (which prove soundness for an *arbitrary* ambient
context, exploiting that the annotated spec ignores the context for expression
typing), the program generator threads the *real* `LContext CoreLParams` and
`TContext Unit`. This is forced: the `DeclHasType'` constructors for type
constructors, datatype blocks and functions produce a genuine *output* context
`C'` obtained by running the Strata checker's add operations
(`addKnownTypeWithError` / `addMutualBlock` / `addFactoryFunctionWithError`), and
that only makes sense relative to the real input `C`.

## Generate-and-check gating

For a block of datatypes and for a function, this module does not *prove* that a well-formed value makes the
add of the checker succeed. Strata gives no such bridge, and for `addMutualBlock` such a proof would need an
equivalence between an executable check and an inductive relation about inhabitance, which no proof gives.
This module instead *runs* the add operation, and it emits the declaration on the `.ok` branch only.
Membership in the support of the result then carries the fact that the add succeeded, and that is exactly what
the matching constructor of `DeclHasType'` asks for.

For an abstract type, an alias, an axiom and a `distinct` assertion, the generator draws each name fresh
against a threaded set of the reserved names, so that `addKnownTypeWithError` and each guard of an alias
provably succeed. It also computes the type arguments from the body for
alias well-formedness, so no gating is needed there.

## Global name freshness

`ProgramHasType'` also needs each name of the program to be different from each other name, in one flat
namespace over each kind of declaration. The fold threads one set of the reserved names, and it adds each
declared name as it goes. Therefore the names of a generated program are distinct by construction.
-/

namespace ProgramGen

/-- Working `LExpr` type shared with the expression generator (unit metadata,
    monotype annotations); definitionally `LExpr CoreLParams.mono`. -/
abbrev PExpr := LExpr'

/-! ## Per-kind declaration builders

Small helpers that package generated data into a `Decl`. Kept separate from the
generators so the soundness proofs can talk about the built `Decl` shape
directly. -/

/-- An abstract type declaration of the given arity. The name of a parameter of a type constructor does not
    matter, and only the number of the parameters matters, which `TypeConstructor.numargs` gives. Therefore this
    definition uses an underscore for each parameter name. -/
def mkAbstractTypeDecl (name : String) (arity : Nat) : Decl :=
  .type (.con { name := name, params := List.replicate arity "_" }) .empty

/-- A type-alias declaration whose type arguments are exactly the (deduplicated)
    free type variables of the body `body`.

    The type arguments come from the body, and that choice makes each guard of `TEnv.addTypeAlias` hold by
    construction. Those guards ask that the type arguments are distinct, which the dedup gives, and that the
    free variables of the body and the type arguments are the same set, so the alias has no parameter that its
    body does not name. Read `DeclHasType'.type_syn`. -/
def mkAliasDecl (name : String) (body : LMonoTy) : Decl :=
  .type (.syn { name := name, typeArgs := (LMonoTy.freeVars body).dedup, type := body }) .empty

/-- An axiom declaration `axiom name : e;`. `e` is expected to be a `bool`. -/
def mkAxiomDecl (name : String) (e : PExpr) : Decl :=
  .ax { name := name, e := e } .empty

/-- A `distinct` declaration `distinct[name] es;`. -/
def mkDistinctDecl (name : String) (es : List PExpr) : Decl :=
  .distinct ⟨name, ()⟩ es .empty

/-- A Strata Core **constant**: a 0-ary, body-less function at type `τ`
    because a constant is a function of arity 0 in Core. Core has no form for a declaration of a global variable,
    so this is the one way to name a value at the top level, and a `distinct` group ranges over such names. Read
    `genDistinctAssertion`.

    Body-less and measure-less by construction, so `FuncHasType'`'s `bodyTyped` /
    `measureTyped` obligations are vacuous and `isRecursive` stays at its `false`
    default. -/
def constantFunc (name : String) (τ : LMonoTy) : Function :=
  { name := ⟨name, ()⟩, typeArgs := [], inputs := [], output := τ }

/-- A constant declaration `function name () : τ;`. -/
def mkConstantDecl (name : String) (τ : LMonoTy) : Decl :=
  .func (constantFunc name τ) .empty

/-! ## The pool of referenceable type constructors

As the program grows, a later block of datatypes and a later alias body can reference a type constructor that
an earlier declaration gives. The fold therefore tracks the *applied* constructors that a type can reference,
which are the ones of an arity of 1 or more, as a list of a name and an arity. That list starts with the
parameterized primitives of Strata Core, which are `Sequence` and `Map`, and each abstract
type of arity ≥ 1. Nullary abstract types extend the base-type pool. -/

/-- The base (arity-0) referenceable type names: the datatype generator's
    defaults (`bool`, `int`, `string`, `real`, `regex`). -/
abbrev BaseTys := List String

/-- The applied (arity ≥ 1) referenceable type constructors with their arity. -/
abbrev TyCons := List KnownTyCon

/-! ## Types over the declared type constructors

An alias body is a type over the base types and over the applied type constructors that are in scope. An
argument of a constructor is such a type too. `DatatypeGen.genArgTy` generates such a type. This module calls
it with an empty list of the block references, because an alias body holds no reference to itself. -/

/-- Generate a type that mentions only `baseTypes`, `tyCons`, and the type
    variables `tyParams`. The type has no block references and no self-references.
    This is the argument-type generator of the datatype development with
    `blockRefs := []` and `recCallsAllowed := false`, because there is nothing to
    recurse into. -/
def genNonRecursiveArgTy [Gen G] (baseTypes : BaseTys) (tyCons : TyCons)
    (tyParams : List TyIdentifier) (size : Nat) : G LMonoTy :=
  genArgTy baseTypes tyCons [] tyParams false size

/-! ## Abstract-type generation -/

/-- Generate an abstract type declaration with a fresh name (drawn against
    `reserved`) and an arity in `[0, maxArity]`. Returns the declaration, its
    name, and its arity (the caller uses the arity to extend the pool). -/
def genAbstractType [Gen G] (reserved : List String) (maxArity : Nat) :
    G (Decl × String × Nat) := do
  let name ← DatatypeGen.genFreshName reserved
  let arity ← chooseNat 0 maxArity (by omega)
  pure (mkAbstractTypeDecl name arity, name, arity)

/-! ## Type-alias generation -/

/-- Generate a type-alias declaration. Draws a fresh name and a fresh list of
    type parameters (in `[0, maxTyParams]`), then a body over the type
    constructors in scope *and* those type parameters. The stored `typeArgs` are re-derived
    from the body's free variables (`mkAliasDecl`), so the alias is well-formed by
    construction even though the drawn parameters may not all appear in the body. -/
def genAlias [Gen G] (baseTypes : BaseTys) (tyCons : TyCons)
    (reserved : List String) (maxTyParams size : Nat) : G (Decl × String) := do
  let name ← DatatypeGen.genFreshName reserved
  let numTyParams ← chooseNat 0 maxTyParams (by omega)
  let tyParams ← DatatypeGen.genFreshNames reserved numTyParams
  let body ← genNonRecursiveArgTy baseTypes tyCons tyParams size
  pure (mkAliasDecl name body, name)

/-! ## Axiom generation -/

/-- Generate an axiom declaration: a fresh name and a `bool`-typed expression.
    The expression is generated in an *empty* local context (`bctx = []`,
    `fctx = []`) at type `.bool`, which is exactly what `genLExpr_sound` proves
    well-typed and what `DeclHasType'.ax` (under the annotated spec) requires. -/
def genAxiom [Gen G] (octx : OpCtx) (pctx : PolyOpCtx)
    (reserved : List String) (depth : Nat) : G (Decl × String) := do
  let name ← DatatypeGen.genFreshName reserved
  let e ← genLExpr [] octx pctx [] [] depth .bool
  pure (mkAxiomDecl name e, name)

/-! ## Distinct generation

A `distinct` group ranges over a *named value at the top level*, and in Strata Core such a value is a function
of arity 0, because Core has no form for a declaration of a global variable. Therefore this step emits one
declaration of a constant for each element, and the `distinct` assertion then names each of them through an
`.op` node:

```
function c₀ () : τ;   function c₁ () : τ;   distinct [d]: [c₀, c₁];
```

An annotated *free* variable is also well typed under the annotated specification, because `HasTypeA.fvar`
takes the type of a free variable from its annotation alone and reads no scope. No legal Core program can bind
such a variable at the top level, so `LExpr.resolve` rejects one. `HasTypeA.op` reads only an annotation, as
`HasTypeA.fvar` does, so soundness is
discharged just as cheaply, by a term the checker can also resolve.

The element type `τ` is drawn over `tyParams := []`, hence *ground*, which is also
what each constant's `FuncHasType'.noUndeclaredVars` needs (a constant declares no
type arguments). -/

/-- The elements of a generated `distinct`: one `.op` node per constant name,
    each annotated at the shared monotype `τ`. Well-typed at `τ` by
    `HasTypeA.op`, and resolvable by the checker because `genDeclDistinct`
    declares every `c ∈ names` as a 0-ary function at `τ` first. -/
def distinctElems (τ : LMonoTy) (names : List String) : List PExpr :=
  names.map (fun c => (.op () ⟨c, ()⟩ (some τ) : PExpr))

/-- Draw the ingredients of a `distinct` declaration: a fresh declaration name, a
    ground element type `τ`, and `numVars` fresh constant names.

    The generator draws each name of a constant against the name of the declaration and the reserved set.
    Therefore those names differ from each other *and* from the name of the declaration. Each of them becomes a
    declaration name of the program, so each of them must differ from each other name of the program.

    Turning these parts into declarations needs the ambient `LContext` (each
    constant is added with the checker's own `addFactoryFunctionWithError`), so it
    happens in `genDeclDistinct`. -/
def genDistinctAssertion [Gen G] (baseTypes : BaseTys) (tyCons : TyCons)
    (reserved : List String) (maxVars size : Nat) : G (String × LMonoTy × List String) := do
  let name ← DatatypeGen.genFreshName reserved
  let τ ← genNonRecursiveArgTy baseTypes tyCons [] size
  let numVars ← chooseNat 0 maxVars (by omega)
  let constNames ← DatatypeGen.genFreshNames (name :: reserved) numVars
  pure (name, τ, constNames)

/-! ## Operator vocabulary derived from a datatype block

When a datatype block is declared, `LContext.addMutualBlock` runs Strata's
`genBlockFactory` and pushes the derived functions into `C.functions`:
**eliminators** (`D$Elim`), **constructors** (`c`), **testers** (`c.testerName`,
e.g. `isCons` for a generated block or `List..isCons` for a parsed one),
and an **accessor of a field** in two forms. The *safe* form carries the precondition that the value has the
matching constructor. The *unsafe* form carries no precondition, and its result is an arbitrary value of the
type of the field when a caller applies it to the wrong constructor.

The definitions below build the vocabulary that one block gives, and `ProgramGen.genDeclDatatype` then merges
that vocabulary into the two operator contexts of the fold. Without that merge, no body of a generated function
and of a generated procedure could name a datatype of an earlier declaration.

The vocabulary is read out of `genBlockFactory` rather than re-derived here. That
is deliberate on two counts: it is the *same* function `addMutualBlock` runs, so
the vocabulary cannot drift from what the context actually holds (including the
tester-naming convention, which differs between generated and parsed blocks); and
projecting it with the existing `factoryOps`/`factoryPolyOps` builds each type
with `mkArrow'`, the exact *generic type* form `OpsConsistentR` canonicalizes an
operator to. -/

/-- Which family of derived functions an entry belongs to. Used by
    `DerivedOpFamilies` to select what enters the operator vocabulary. -/
inductive DerivedOpFamily where
  /-- The eliminator `D$Elim`. -/
  | elim
  /-- A constructor (`None`, `Cons`, …). -/
  | constr
  /-- A tester (`isCons` / `List..isCons`). -/
  | tester
  /-- A safe field accessor (`List..head`), which carries a tester precondition. -/
  | accessor
  /-- An unsafe field accessor (`List..head!`), which carries no precondition. -/
  | unsafeAccessor
  deriving DecidableEq, Repr, Inhabited

/-- Classify a derived function name against the block it came from.

    Testers are matched by *name*, against the block's own `testerName` fields,
    rather than by Strata's `isTesterName` predicate: `isTesterName` looks for a
    `..is` prefix after the `..` separator, which recognizes a parsed block's
    `List..isCons` but not a generated block's default `isCons` (the generator
    keeps `LConstr.testerName`'s default, `"is" ++ name`). Matching the block's
    actual fields covers both. -/
def classifyDerivedOp (block : MutualDatatype Unit) (name : String) : DerivedOpFamily :=
  let testerNames := block.flatMap (fun d => d.constrs.map (·.testerName))
  let constrNames := block.flatMap (fun d => d.constrs.map (·.name.name))
  if block.any (fun d => (Lambda.elimFuncName (IDMeta := Unit) d).name == name) then .elim
  else if testerNames.contains name then .tester
  else if constrNames.contains name then .constr
  else if name.endsWith Lambda.unsafeDestructorSuffix then .unsafeAccessor
  else .accessor

/-- Which derived families to admit into the operator vocabulary.

    The eliminator is excluded by default. Its type quantifies over a
    result variable from `freshTypeArgs`, and the target type puts no condition on that variable, so `IndirPoly`
    must *sample* it. Its arguments for the cases are also higher order, because it takes one lambda for each
    constructor of the whole block, and the expression generator can rarely fill such an argument. It is also not
    one of the three families that the documentation of the language describes, and the four families here are
    exactly those. -/
structure DerivedOpFamilies where
  elim : Bool := false
  constr : Bool := true
  tester : Bool := true
  accessor : Bool := true
  unsafeAccessor : Bool := true
  deriving Inhabited

/-- Whether `sel` admits family `f`. -/
def DerivedOpFamilies.admits (sel : DerivedOpFamilies) : DerivedOpFamily → Bool
  | .elim => sel.elim
  | .constr => sel.constr
  | .tester => sel.tester
  | .accessor => sel.accessor
  | .unsafeAccessor => sel.unsafeAccessor

/-- The factory of the derived functions that a block of datatypes gives, as `addMutualBlock` of Strata computes
    it. The result is `none` when `genBlockFactory` rejects the block, which happens after a clash of two names
    among the derived functions. The caller then gives no operator, as it also emits no declaration.

    The instances are pinned explicitly (rather than left to synthesis) to the
    `CoreLParams`-native ones, matching `genDeclDatatype`'s `addMutualBlock` call,
    so the vocabulary is read off the very factory the context received. -/
def blockDerivedFactory (block : MutualDatatype Unit) :
    Option (@Lambda.Factory LExprParams') :=
  (@Lambda.genBlockFactory LExprParams' instInhabitedPUnit instInhabitedPUnit
    instToFormatIDMetaCoreLParams _ block).toOption

/-- The quantified type variables of a type scheme. `[]` exactly when the scheme
    is ground, i.e. when the datatype it came from has no type parameters. -/
def polySchemeVars : Lambda.LTy → List TyIdentifier
  | .forAll vars _ => vars

/-- The **monomorphic** operator entries a datatype block contributes: each
    admitted derived function under its curried generic type.

    For a datatype with no type parameters these types are ground, so the `Indir`
    rule can apply each of them in full, because `findOpsInCtx` compares two result types for equality. For a
    *polymorphic* datatype, each type names a type variable of the datatype, and it therefore matches no concrete
    target. The useful entries of such a block are the ones for the polymorphic context below. This function
    emits an entry in each case. An entry that the monomorphic rule cannot use is inert, and one form for both
    projections needs no special case.

    The result is an `OpList` (the plain (name, curried type) list), not an `OpCtx`:
    the caller *appends* it to the state's existing operators and rebuilds the
    context with `OpCtx.ofList`, so the type index is recomputed over the merged
    vocabulary. Returning an `OpCtx` here would mean building an index that is
    immediately discarded, and `OpCtx` carries an `agrees` proof field, so it is not
    appendable as a list in any case. -/
def adtDerivedOps (block : MutualDatatype Unit)
    (sel : DerivedOpFamilies := {}) : OpList :=
  match blockDerivedFactory block with
  | none => []
  | some F =>
    (factoryOps F).ops.filter (fun e => sel.admits (classifyDerivedOp block e.1))

/-- The **polymorphic** operator entries a datatype block contributes: each
    admitted derived function of a *type-parameterized* datatype, under its full
    type scheme (`∀ d.typeArgs. …`).

    This is the projection that matters for a polymorphic datatype: `IndirPoly`
    unifies the scheme's return type with the target and samples any variable left
    undetermined, so `List..head : ∀α. List<α> → α` is reachable at *any* target
    type, and `List..isCons : ∀α. List<α> → bool` at `bool`.

    **Ground schemes are deliberately excluded** (the `typeArgs`-nonempty filter).
    A datatype with no type parameters yields derived functions whose types are
    already concrete, and those are fully served by the `octx` projection above via
    the monomorphic `Indir` rule, which is much cheaper. An entry here as a scheme with no binder would add no
    reachable term, and it would send each draw through `findPolymorphicOps`, which renames each bound type
    variable, unifies at each split point, and samples an instantiation. That cost is real: the derived operators
    of a *monomorphic* block in the polymorphic context, as well as in the monomorphic one, made a
    procedure draw roughly 30× slower for no gain in coverage. -/
def adtDerivedPolyOps (block : MutualDatatype Unit)
    (sel : DerivedOpFamilies := {}) : PolyOpCtx :=
  match blockDerivedFactory block with
  | none => []
  | some F =>
    (factoryPolyOps F).filter (fun e =>
      sel.admits (classifyDerivedOp block e.1) && !(polySchemeVars e.2).isEmpty)

/-- Every entry of `adtDerivedPolyOps` comes from `factoryPolyOps` of the block's
    own derived factory. This is the membership fact the op-consistency corollary
    needs (`adtDerivedPolyOps_pctxWF` in `ProgramGen.OpsConsistent`, which cannot
    live here: `PCtxWF` is defined in the Mathlib-importing proof module, while
    this file is code-only). -/
theorem mem_adtDerivedPolyOps {block : MutualDatatype Unit}
    {sel : DerivedOpFamilies} {F : @Lambda.Factory LExprParams'}
    (hF : blockDerivedFactory block = some F)
    {e : String × Lambda.LTy} (hmem : e ∈ adtDerivedPolyOps block sel) :
    e ∈ factoryPolyOps F := by
  unfold adtDerivedPolyOps at hmem
  rw [hF] at hmem
  exact (List.mem_filter.mp hmem).1

/-! ## Recovering a procedure's `M`/`I`/`O` split

`genProcedure` builds the inputs as the shared in-out block and then the input-only block, and the outputs as
the shared block and then the output-only block. The shared block comes first in both. To *register* a generated
procedure as a callable signature, the fold must recover that shared block. The state of the fold holds no data
from a proof, so the fold computes that block again, as the longest common prefix of the two signatures.

That is exact: `lcp (M ++ I) (M ++ O) = M ++ lcp I O`, and `I`/`O` have disjoint
keys (the generator filters `O` against `M ++ I`), so `lcp I O = []`. The lemma
`commonPrefix_append_of_disjoint` in `ProgramGen.ProcSigThread` proves it. -/

/-- Longest common prefix, on plain lists. Stated over `List` (rather than
    `LMonoTySignature`, which is a `ListMap` and carries its own `++`) so that
    `List.append` lemmas apply without instance friction. -/
def commonPrefixList {α : Type} [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => if a = b then a :: commonPrefixList as bs else []

/-- Longest common prefix of two signatures. -/
def commonPrefix (A B : @LMonoTySignature Unit) : @LMonoTySignature Unit :=
  commonPrefixList A B

end ProgramGen
