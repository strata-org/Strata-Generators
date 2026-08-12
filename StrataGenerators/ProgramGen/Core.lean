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

/-!
# Generator definitions for random well-typed Strata Core *programs*

This module holds the **generator code** (no proofs — those live in
`StrataGenerators.ProgramGen`) for random Strata Core `Program`s that are
well-typed with respect to `Core.TypeSpec.ProgramHasType'` (instantiated at the
annotated `HasTypeA` spec → `ProgramHasTypeA`).

A `Program` is a list of `Decl`s. We reuse the existing generators for the
"interesting" declaration bodies — `DatatypeGen.genMutuallyRecursiveDatatypes`
for algebraic datatype blocks and `genFunction` for functions — and add
generators for the four declaration kinds those don't already cover: **abstract
types** (`type Foo _ _;`), **type aliases** (`type Bar x = …;`), **axioms**, and
**`distinct`** assertions.

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

For datatype blocks and functions we do not attempt to *prove* "the block/func is
well-formed ⟹ the checker's add succeeds" (that bridge does not exist in Strata,
and for `addMutualBlock` it would require an unproven executable↔inductive
inhabitance equivalence). Instead we *run* the add operation and only emit the
declaration on the `.ok` branch. Support-membership of a produced value then
carries the `= .ok C'` fact for free, which is exactly what the corresponding
`DeclHasType'` constructor asks for.

For abstract types, aliases, axioms and `distinct` we generate names fresh
against a threaded reserved-name set (so `addKnownTypeWithError` / the alias
guards provably succeed) and rely on the derive-typeArgs-from-body trick for
alias well-formedness, so no gating is needed there.

## Global name freshness

`ProgramHasType'` additionally requires `P.getNames.Nodup` — a single flat
namespace across every declaration kind. We thread one global reserved-name set
across the whole fold, adding each declared name as we go, so distinctness of the
generated program's names holds by construction.
-/

namespace ProgramGen

/-- Working `LExpr` type shared with the expression generator (unit metadata,
    monotype annotations); definitionally `LExpr CoreLParams.mono`. -/
abbrev PExpr := LExpr'

/-! ## Per-kind declaration builders

Small helpers that package generated data into a `Decl`. Kept separate from the
generators so the soundness proofs can talk about the built `Decl` shape
directly. -/

/-- An abstract type declaration `type name _ … _;` of the given arity. The
    parameter names are irrelevant for a type constructor (only the count, i.e.
    `numargs`, matters — see `TypeConstructor.numargs`), so we use placeholder
    underscores. -/
def mkAbstractTypeDecl (name : String) (arity : Nat) : Decl :=
  .type (.con { name := name, params := List.replicate arity "_" }) .empty

/-- A type-alias declaration whose type arguments are exactly the (deduplicated)
    free type variables of the body `body`.

    Deriving `typeArgs` from `body` this way makes all of `TEnv.addTypeAlias`'s
    guards hold by construction: `typeArgs.Nodup` (dedup), `freeVars ⊆ typeArgs`
    and `typeArgs ⊆ freeVars` (no phantom args) — see `DeclHasType'.type_syn`. -/
def mkAliasDecl (name : String) (body : LMonoTy) : Decl :=
  .type (.syn { name := name, typeArgs := (LMonoTy.freeVars body).dedup, type := body }) .empty

/-- An axiom declaration `axiom name : e;`. `e` is expected to be a `bool`. -/
def mkAxiomDecl (name : String) (e : PExpr) : Decl :=
  .ax { name := name, e := e } .empty

/-- A `distinct` declaration `distinct[name] es;`. -/
def mkDistinctDecl (name : String) (es : List PExpr) : Decl :=
  .distinct ⟨name, ()⟩ es .empty

/-- A Strata Core **constant**: a 0-ary, body-less function at type `τ`
    ("constants are 0-ary functions", `Core/Program.lean`). Core has no
    global-variable declaration form, so this is the only way to name a top-level
    value — which is what a `distinct` group ranges over (see `genDistinctAssertion`).

    Body-less and measure-less by construction, so `FuncHasType'`'s `bodyTyped` /
    `measureTyped` obligations are vacuous and `isRecursive` stays at its `false`
    default. -/
def constantFunc (name : String) (τ : LMonoTy) : Function :=
  { name := ⟨name, ()⟩, typeArgs := [], inputs := [], output := τ }

/-- A constant declaration `function name () : τ;`. -/
def mkConstantDecl (name : String) (τ : LMonoTy) : Decl :=
  .func (constantFunc name τ) .empty

/-! ## Referenceable type-constructor vocabulary

As the program grows, later ADT blocks and alias bodies may reference the type
constructors declared earlier. We track the referenceable *applied* constructors
(arity ≥ 1) as a `List KnownTyCon = List (String × Nat)`, seeded with Strata
Core's parameterized primitives (`Sequence`, `Map`) and extended by each abstract
type of arity ≥ 1. Nullary abstract types extend the base-type pool. -/

/-- The base (arity-0) referenceable type names: the datatype generator's
    defaults (`bool`, `int`, `string`, `real`, `regex`). -/
abbrev BaseTys := List String

/-- The applied (arity ≥ 1) referenceable type constructors with their arity. -/
abbrev TyCons := List KnownTyCon

/-! ## Generating a type over a vocabulary

Alias bodies and (via the datatype generator) constructor arguments are types
over the current vocabulary. We reuse `DatatypeGen.genArgTy` with an empty
`blockRefs` (an alias body has no recursive self-reference) to produce a type
mentioning only base types, applied constructors, and the supplied type
parameters. -/

/-- Generate a type mentioning only `baseTypes`, `tyCons`, and the type variables
    `tyParams` (no block/self references). Reuses the datatype generator's
    argument-type generator with `blockRefs := []` and `recCallsAllowed := false`
    (there is nothing to recurse into). -/
def genVocabTy [Gen G] (baseTypes : BaseTys) (tyCons : TyCons)
    (tyParams : List TyIdentifier) (size : Nat) : G LMonoTy :=
  genArgTy baseTypes tyCons [] tyParams false size

/-! ## Abstract-type generation -/

/-- Generate an abstract type declaration with a fresh name (drawn against
    `reserved`) and an arity in `[0, maxArity]`. Returns the declaration, its
    name, and its arity (the caller uses the arity to extend the vocabulary). -/
def genAbstractType [Gen G] (reserved : List String) (maxArity : Nat) :
    G (Decl × String × Nat) := do
  let name ← DatatypeGen.genFreshName reserved
  let arity ← chooseNat 0 maxArity (by omega)
  pure (mkAbstractTypeDecl name arity, name, arity)

/-! ## Type-alias generation -/

/-- Generate a type-alias declaration. Draws a fresh name and a fresh list of
    type parameters (in `[0, maxTyParams]`), then a body over the current
    vocabulary *and* those type parameters. The stored `typeArgs` are re-derived
    from the body's free variables (`mkAliasDecl`), so the alias is well-formed by
    construction even though the drawn parameters may not all appear in the body. -/
def genAlias [Gen G] (baseTypes : BaseTys) (tyCons : TyCons)
    (reserved : List String) (maxTyParams size : Nat) : G (Decl × String) := do
  let name ← DatatypeGen.genFreshName reserved
  let numTyParams ← chooseNat 0 maxTyParams (by omega)
  let tyParams ← DatatypeGen.genFreshNames reserved numTyParams
  let body ← genVocabTy baseTypes tyCons tyParams size
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

A `distinct` group ranges over *named top-level values*, and in Strata Core those
are 0-ary functions — Core has no global-variable declaration form. So the step
emits one constant declaration per element and lets the `distinct` reference them
as `.op` nodes:

```
function c₀ () : τ;   function c₁ () : τ;   distinct [d]: [c₀, c₁];
```

Annotated *free* variables (`.fvar () ⟨v, ()⟩ (some τ)`) would also be well-typed
under the annotated spec — `HasTypeA.fvar` types an fvar from its annotation alone,
with no reference to scope — but no legal Core program can bind such a variable at
top level, so `LExpr.resolve` rejects one ("Cannot find this fvar in the context").
`HasTypeA.op` has the same annotation-only shape as `HasTypeA.fvar`, so soundness is
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

    The constant names are drawn against `name :: reserved`, so they are distinct
    from each other *and* from the declaration's own name — all `numVars + 1` names
    become program-level declaration names, so they must all be globally distinct
    (`getNames.Nodup`).

    Turning these parts into declarations needs the ambient `LContext` (each
    constant is added with the checker's own `addFactoryFunctionWithError`), so it
    happens in `genDeclDistinct`. -/
def genDistinctAssertion [Gen G] (baseTypes : BaseTys) (tyCons : TyCons)
    (reserved : List String) (maxVars size : Nat) : G (String × LMonoTy × List String) := do
  let name ← DatatypeGen.genFreshName reserved
  let τ ← genVocabTy baseTypes tyCons [] size
  let numVars ← chooseNat 0 maxVars (by omega)
  let constNames ← DatatypeGen.genFreshNames (name :: reserved) numVars
  pure (name, τ, constNames)


/-! ## Recovering a procedure's `M`/`I`/`O` split

`genProcedure` builds `inputs = M ++ I` and `outputs = M ++ O` with the shared
in-out block `M` leading both. To *register* a generated procedure as a callable
signature the fold must recover `M`, but `GenState` holds no proof data — so it
recomputes `M` as the longest common prefix of the two signatures.

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
