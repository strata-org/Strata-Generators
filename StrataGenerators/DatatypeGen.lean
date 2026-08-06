import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import BasaltExamples.ArbChar.Def
import BasaltExamples.ArbString.Def
import StrataGenerators.HasTypeAGen.Core
import StrataGenerators.CmdHasTypeAGen.Core
import Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.TypeConstructor

open Lambda RandomChoice ArbNat ArbChar ArbString

/-!
# Generator for random well-formed algebraic data types (Strata Core)

A Basalt `Gen`-based random generator for well-formed *mutually recursive*
algebraic data type definitions in Strata Core.

The target of the generator is a `MutualDatatype Unit` — a `List (LDatatype Unit)`
representing the contents of a `mutual … end` block — such that it satisfies the
argument-well-formedness half of `Core.TypeSpec.MutualADTWF`, namely
`argsWF`/`refsKnown`/`argVarsScoped` from
`Strata.Languages.Core.DatatypeTypeSpec`.

## Shape

The heart of the generator is `genArgTy`, which produces a constructor-argument
type. It carries a `recCallsAllowed : Bool` flag that is threaded `false` into
exactly the positions where the spec forbids an occurrence of *any* block
datatype's name — the domain of an arrow, and the arguments of another type
constructor. That single flag is what makes the output well-formed;
`DatatypeGenProofs.lean` turns it into a proof.

Rather than a single self-reference, the recursive-occurrence leaf may emit *any*
member of a supplied `blockRefs : List BlockRef` — the datatypes of the block that
this datatype may legally refer to (see below). This is the one place the move
from single to mutual datatypes shows up in the generator: where the old code
tested equality against a single `selfName`, the well-formedness conditions are
now relaxed to *membership in the set of block names*, and a recursive occurrence
is `n (n's typeArgs)` for any block member `n`.

Around that sit `genConstrArgs` / `genConstrs` (argument lists and constructors),
`genConstructors` / `genConstructorsForAllTypes` (one datatype's / all datatypes' constructors), and
`genMutuallyRecursiveDatatypes` (the whole block). Fuel is a `size` that is halved at each level
of nesting, and alternatives are picked with a uniform `oneOf`.

Base types (arity `0`) and applied type constructors (arity `≥ 1`) are supplied
as two separate parameters, so no arity filtering is needed.

## Type parameters and which datatypes may refer to which

Each datatype in the block declares its *own* `typeArgs` (they are generated
independently, not shared across the block), drawn from a common name-space so
that different datatypes may reuse parameter names. A datatype `dᵢ` may refer to a
block member `dⱼ` — via the uniform occurrence `dⱼ (dⱼ.typeArgs)` — only when
`dⱼ.typeArgs ⊆ dᵢ.typeArgs`. `dᵢ` always qualifies for itself, and a *nullary*
datatype qualifies for everyone.

This subset restriction is exactly what keeps the output `MutualADTWF`: a uniform
occurrence `dⱼ (dⱼ.typeArgs)` introduces `dⱼ`'s type parameters as free variables
of `dᵢ`'s constructor argument, so `MutualADTWF.argVarsScoped` (every free
variable of a constructor argument of `dᵢ` is one of `dᵢ.typeArgs`) forces
`dⱼ.typeArgs ⊆ dᵢ.typeArgs`. `blockRefs` is the pre-filtered list of members that
pass this test for the datatype currently being generated.

## Name generation and the reserved-name set

Every name the generator invents — each datatype's name, its type parameters, its
constructor names, and its field names — is drawn by `genFreshName` from a
threaded list of *reserved* names, and is then itself added to that list where
distinctness matters. So no generated name can collide with:

* a reserved Strata Core keyword (`reservedKeywordsList`), which the parser would
  reject in identifier position;
* a base type or type constructor the generator may reference, nor the reserved
  arrow constructor `"arrow"` — collisions that would make a leaf read as a
  recursive occurrence, or an application read as an arrow;
* any *other datatype's name* in the block — so the block's names are pairwise
  distinct (`namesNodup`) and a base/applied type can never be misread as a
  reference to a block member.

Datatype names are threaded through `reserved` so they stay pairwise distinct;
type parameters are drawn fresh against the reserved set but are *not* added back
to it, so distinct datatypes may reuse the same parameter names (which is what
makes cross-references between parameterized datatypes possible).

This is the same mechanism `genFreshName` uses in `CmdHasTypeAGen/Core.lean` for
variable names: draw a random legal identifier, and fall back to a name that is
*longer than every reserved name* (hence certainly absent) if the draw collides.
Names are otherwise unconstrained — in particular the generator imposes no
prefix or suffix on them.

The reserved set is what discharges the soundness side conditions: see
`NamesOk` and `namesOk_of_fresh` in `DatatypeGenProofs.lean`.

## What "well-formed" means here

For a block `block`, `ConstrArgWF block ty` unfolds to
`NotNested block ty ∧ StrictPosUnif block ty`. Writing `N := block.map (·.name)`
for the set of block names, a constructor-argument type is well-formed exactly
when:

1. **Strict positivity.** No `n ∈ N` appears to the left of an arrow. So in
   `t₁ → t₂`, every block name must be absent from `t₁` and (recursively) `t₂`
   must be strictly positive.
2. **Uniformity.** Every occurrence of an `n ∈ N` is applied to *exactly* that
   datatype's own `typeArgs` (`UniformOccur.self`). A recursive reference must be
   `n τs`, verbatim.
3. **No nesting.** No `n ∈ N` may appear buried inside the arguments of another
   type constructor (`NotNested`); an `n`-headed application is a fine direct
   reference, but `Pair (n τs) …` or `Sequence (n τs)` is rejected.

`refsKnown` additionally requires every referenced type-constructor name to be
either a known primitive, an existing datatype of the ambient context, or a
block name. We satisfy it *by construction*: the generator only ever emits head
symbols drawn from `baseTypes ∪ tyCons`, plus the block names and `"arrow"`.

Each datatype's first constructor is a *witness* that references only the
datatypes generated before it (in particular, the first datatype's witness
references no block name at all). Generating datatypes in order, this makes every
datatype inhabited — either outright or through already-inhabited earlier
datatypes — which is exactly the `MutualADTWF` inhabitance requirement, without
forcing any constructor to be free of all block names.
-/

namespace DatatypeGen

/-! ## Ambient known type constructors

`refsKnown` resolves a referenced name against the ambient `LContext`'s known
types and existing datatypes. Since we are generating a *fresh* datatype with no
proof obligations wired to a concrete context, we take the referenceable type
constructors as explicit parameters. Emitting only these (plus the datatype's own
name, plus `"arrow"`) makes `refsKnown` hold for any context whose
known-type/datatype names are a superset of them. -/

/-- An applied type constructor the generator may reference, together with its
    arity. -/
abbrev KnownTyCon := String × Nat

/-- Ground types the generator may reference: the nullary base type names shared
    with the `LMonoTy` generator in `HasTypeAGen/Core.lean`
    (`nullaryBaseTypeNames` = `bool`, `int`, `string`, `real`, `regex`).
    Bitvectors are drawn separately by `pickBitvecWidth`, as in that generator. -/
def defaultBaseTypes : List String :=
  nullaryBaseTypeNames

/-- Applied type constructors the generator may reference: the parameterized
    primitives Strata Core actually knows (see `Core.KnownLTys`). Note `"arrow"`
    is *not* listed — arrows get their own branch in `genArgTy`. -/
def defaultTyCons : List KnownTyCon :=
  [("Sequence", 1), ("Map", 2)]

/-! ## Name generation

Every generated name goes through `genFreshName`, which draws a legal Core
identifier and guarantees it is absent from a threaded list of reserved names.
`initialReserved` seeds that list, and each generated name is added to it. -/

/-- The names a generated name must avoid before the generator has invented
    anything of its own:

    * `"arrow"`, because `LMonoTy.arrow t1 t2` is *definitionally*
      `LMonoTy.tcons "arrow" [t1, t2]`, so a datatype or constructor named
      `"arrow"` would be indistinguishable from a real arrow;
    * the reserved Strata Core keywords, which the parser rejects in identifier
      position;
    * the referenceable type names `baseTypes` and `tyCons`, so that a leaf like
      `.tcons "bool" []` can never be read as a recursive occurrence of the
      datatype, and an application can never be read as one either;
    * any `extraReserved` names the caller wants avoided — in particular the
      *ambient context's* known-type and datatype names, so that a generated
      datatype name cannot collide with a type the surrounding `LContext` already
      knows (Strata Core knows more type symbols than the generator references,
      e.g. `Triggers` / `bitvec`; reserving them is what makes the generator's
      output `MutualADTWF`-sound against the real Core context). Defaults to `[]`. -/
def initialReserved (baseTypes : List String) (tyCons : List KnownTyCon)
    (extraReserved : List String := []) : List String :=
  "arrow" :: (reservedKeywordsList ++ baseTypes ++ tyCons.map (·.1) ++ extraReserved)

/-- The length of the longest name in a list (`0` for the empty list). A name
    strictly longer than this cannot occur in the list — the length-based
    freshness argument behind `fallbackName`. The `List String` analogue of
    `maxNameLen` in `CmdHasTypeAGen/Core.lean`. -/
def maxNameLength (names : List String) : Nat :=
  names.foldl (fun acc nm => max acc nm.length) 0

/-- A name guaranteed to be absent from `reserved`: the string of
    `maxNameLength reserved + 1` `x` characters, which is strictly longer than
    every reserved name. It is a legal Core identifier (letter-initial and
    alphanumeric) and, being all `x`s, never a reserved keyword.

    Reuses `indexedFreshName` from `CmdHasTypeAGen/Core.lean`, whose index `0`
    member is exactly this string. -/
def fallbackName (reserved : List String) : String :=
  indexedFreshName (maxNameLength reserved) 0

/-- Generate a name that is absent from `reserved`.

    Draws a random legal Core identifier with `genIdentName` (a letter-initial
    run of identifier characters, mapped through `dodgeKeyword` so it is never a
    reserved keyword), and falls back to the length-based `fallbackName` if the
    draw happens to collide with a reserved name. Either way the result is a
    legal identifier that is not in `reserved`, with no prefix or suffix imposed
    on it.

    This is the `List String` counterpart of `genFreshName` in
    `CmdHasTypeAGen/Core.lean`, which does the same against a `VarCtx`. -/
def genFreshName [Gen G] (reserved : List String) : G String := do
  let s ← genIdentName
  if reserved.contains s then pure (fallbackName reserved) else pure s

/-- Generate `n` names that are absent from `reserved` and pairwise distinct, by
    adding each name to the reserved list before drawing the next one. -/
def genFreshNames [Gen G] (reserved : List String) (n : Nat) : G (List String) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let s ← genFreshName reserved
    let rest ← genFreshNames (s :: reserved) n
    pure (s :: rest)

/-! ## Block references

A recursive occurrence in a mutual block may be *any* member of the block that
the datatype under construction is allowed to refer to. Each such member is
recorded as its name together with its own type arguments (as types): a uniform
occurrence of that member is `name args`, verbatim. -/

/-- A block datatype that may be referred to recursively, as its name paired with
    its own type arguments (`d.typeArgs.map .ftvar`). A uniform occurrence is
    `.tcons name args`. -/
abbrev BlockRef := String × LMonoTys

/-! ## The well-formed constructor-argument type generator

`genLeafTy` / `genArgTy` are the heart of the generator. They are parameterized
by:

* `baseTypes : List String` — ground types we may reference;
* `tyCons : List KnownTyCon` — applied type constructors we may reference;
* `blockRefs : List BlockRef` — the block datatypes this datatype may refer to,
  each as its name paired with its own type arguments as types. A uniform
  occurrence of a member is `name args`, verbatim — e.g. for `List α` the
  occurrence must be `List α`, never `List β` or `List (α, α)`. This generalizes
  the old single `selfName`/`selfArgs`: the well-formedness conditions test
  *membership in this set* of names rather than equality with one name;
* `tyParams : List TyIdentifier` — the datatype's type-parameter names, used to
  generate `ftvar` leaves;
* `recCallsAllowed : Bool` — whether a recursive occurrence of a `blockRefs`
  member may be emitted here. This is the one flag that enforces well-formedness:
  it is set to `false` in exactly the positions where the spec forbids an
  occurrence of a block name.
-/

/-- A ground type: a bitvector of an arbitrary width, or one of `baseTypes`
    applied to no arguments.

    Reuses `pickBitvecWidth` from `HasTypeAGen/Core.lean` — the same width
    generator the `LMonoTy` generator uses — which now draws an unconstrained
    width (issue #38). It heads the list so that it is manifestly a `::`, making
    `oneOf`'s non-emptiness obligation provable by `simp`; consequently
    `baseTypes = []` is harmless.

    Unlike `pickBaseType` there, `genBaseTy` is parameterized by the caller's
    `baseTypes` pool (the soundness proof quantifies over it), so it cannot just
    call `pickBaseType`; but the two agree on the default pool
    `defaultBaseTypes = nullaryBaseTypeNames`. -/
def genBaseTy [Gen G] (baseTypes : List String) : G LMonoTy :=
  oneOf ((fun () => pickBitvecWidth) ::
         baseTypes.map (fun b => (fun () => pure (.tcons b [])))) (by simp)

/-- A leaf type: a ground type, one of the datatype's own type parameters, or —
    when `recCallsAllowed` and there is a block member to refer to — a uniform
    recursive occurrence `name args` of some `blockRefs` member.

    Matching on `tyParams` rather than concatenating the available alternatives
    into one flat list is what keeps each *kind* of leaf equally likely, instead
    of letting the many base-type names outvote the recursive occurrence. It is
    also what makes `elements tyParams` legitimate, since `elements` demands a
    non-empty list. Likewise the recursive-occurrence alternative is present only
    when `blockRefs` is non-empty, so `elements blockRefs` is legitimate; when it
    is empty (a datatype allowed to refer to nothing — not even itself) there is
    simply no recursive-occurrence leaf. -/
def genLeafTy [Gen G] (baseTypes : List String)
    (blockRefs : List BlockRef) (tyParams : List TyIdentifier)
    (recCallsAllowed : Bool) : G LMonoTy :=
  match tyParams, recCallsAllowed, blockRefs with
  | [], false, _ => genBaseTy baseTypes
  | [], true, [] => genBaseTy baseTypes
  | [], true, br :: brs =>
    oneOf [ fun () => genBaseTy baseTypes
          , fun () => do let (n, args) ← elements (br :: brs) (by simp)
                         pure (.tcons n args) ] (by simp)
  | v :: vs, false, _ =>
    oneOf [ fun () => genBaseTy baseTypes
          , fun () => LMonoTy.ftvar <$> elements (v :: vs) (by simp) ] (by simp)
  | v :: vs, true, [] =>
    oneOf [ fun () => genBaseTy baseTypes
          , fun () => LMonoTy.ftvar <$> elements (v :: vs) (by simp) ] (by simp)
  | v :: vs, true, br :: brs =>
    oneOf [ fun () => genBaseTy baseTypes
          , fun () => LMonoTy.ftvar <$> elements (v :: vs) (by simp)
          , fun () => do let (n, args) ← elements (br :: brs) (by simp)
                         pure (.tcons n args) ] (by simp)

/-- Generate a well-formed constructor-argument type, at `size` and with
    recursive occurrences allowed iff `recCallsAllowed`. At `size = 0` only a
    leaf; above that, an arrow, a leaf, or an application of a known type
    constructor.

    The two well-formedness-critical `false`s are here:

    * the **arrow** branch generates its domain with `recCallsAllowed := false`
      (strict positivity: `selfName` may not occur left of an arrow) and its
      codomain with the incoming flag (a self-reference is fine there);
    * the **application** branch generates every argument with
      `recCallsAllowed := false` (no nesting: `selfName` may not occur inside
      another type constructor's arguments).

    The `match tyCons` is needed to make `elements tyCons` legitimate. -/
def genArgTy [Gen G] (baseTypes : List String) (tyCons : List KnownTyCon)
    (blockRefs : List BlockRef) (tyParams : List TyIdentifier)
    (recCallsAllowed : Bool) (size : Nat) : G LMonoTy :=
  if size = 0 then
    genLeafTy baseTypes blockRefs tyParams recCallsAllowed
  else
    -- Halved once for every level of nesting, so the recursion terminates.
    let half := size / 2
    let genArrowTy : Unit → G LMonoTy := fun () => do
      let t1 ← genArgTy baseTypes tyCons blockRefs tyParams false half
      let t2 ← genArgTy baseTypes tyCons blockRefs tyParams recCallsAllowed half
      pure (.arrow t1 t2)
    let genSizeZeroArgTy : Unit → G LMonoTy := fun () =>
      genLeafTy baseTypes blockRefs tyParams recCallsAllowed
    match tyCons with
    | [] => oneOf [genArrowTy, genSizeZeroArgTy] (by simp)
    | kc :: kcs =>
      let genTyApp : Unit → G LMonoTy := fun () => do
        let (tyCtor, arity) ← elements (kc :: kcs) (by simp)
        let argTys ← vectorOf arity
          (genArgTy baseTypes tyCons blockRefs tyParams false half)
        pure (.tcons tyCtor argTys)
      oneOf [genArrowTy, genSizeZeroArgTy, genTyApp] (by simp)
  termination_by size
  decreasing_by all_goals omega

/-! ## Constructors and the datatype

`genConstrArgs` and `genConstrs` thread the reserved-name list, returning the
extended list alongside their result so that the caller can keep accumulating.
Every field and constructor name is drawn fresh against that list, so all names
within a generated datatype are pairwise distinct. -/

/-- Generate a constructor's argument list: up to `maxArgs` arguments, each
    generated at an independently chosen size in `[0, maxSize]`, with fresh field
    names. Returns the argument list together with the reserved-name list
    extended by those field names. -/
def genConstrArgs [Gen G] (baseTypes : List String) (tyCons : List KnownTyCon)
    (blockRefs : List BlockRef) (tyParams : List TyIdentifier)
    (recCallsAllowed : Bool) (maxArgs maxSize : Nat) (reserved : List String) :
    G (List (Identifier Unit × LMonoTy) × List String) := do
  let numArgs ← chooseNat 0 maxArgs (by omega)
  let fieldNames ← genFreshNames reserved numArgs
  let argTys ← vectorOf numArgs (do
    let size ← chooseNat 0 maxSize (by omega)
    genArgTy baseTypes tyCons blockRefs tyParams recCallsAllowed size)
  pure ((fieldNames.zip argTys).map
          (fun (nm, ty) => ((⟨nm, ()⟩ : Identifier Unit), ty)),
        fieldNames ++ reserved)

/-- Generate `n` constructors, each with a fresh name and fresh field names.
    Returns the constructors together with the extended reserved-name list. -/
def genConstrs [Gen G] (baseTypes : List String) (tyCons : List KnownTyCon)
    (blockRefs : List BlockRef) (tyParams : List TyIdentifier)
    (recCallsAllowed : Bool) (maxArgs maxSize : Nat) (n : Nat)
    (reserved : List String) : G (List (LConstr Unit) × List String) :=
  match n with
  | 0 => pure ([], reserved)
  | n + 1 => do
    let cname ← genFreshName reserved
    let (args, reserved) ← genConstrArgs baseTypes tyCons blockRefs tyParams
      recCallsAllowed maxArgs maxSize (cname :: reserved)
    let (rest, reserved) ← genConstrs baseTypes tyCons blockRefs tyParams
      recCallsAllowed maxArgs maxSize n reserved
    pure ({ name := ⟨cname, ()⟩, args := args } :: rest, reserved)

/-! ## Headers and the visible-reference set

A generated block is built in two phases. First all *headers* are drawn — each a
datatype name paired with its own type parameters. Then each datatype's body
(constructors) is generated, with a `blockRefs` list computed from the headers.

Names are drawn pairwise distinct (threaded through `reserved`), so the block's
names are distinct (`namesNodup`) and none collides with a base/applied type.
Type parameters, by contrast, are drawn fresh against the reserved set but *not*
added back, so different datatypes may reuse the same parameter names — which is
what lets one parameterized datatype refer to another. -/

/-- A datatype header — its name and its independently generated type parameters —
    is exactly a `Lambda.TypeConstructor` (`name` + `params`, with `bound` left at
    its `.Infinite` default). A block is
    `headers.map (fun h => { name := h.name, typeArgs := h.params, … })`. -/
abbrev Header := TypeConstructor

/-- The block references visible to a datatype whose type parameters are
    `tyParams`: every header `⟨n, ps⟩` with `ps ⊆ tyParams`, recorded as the
    uniform occurrence `(n, ps.map .ftvar)`.

    The `ps ⊆ tyParams` filter is what keeps the output `MutualADTWF`: a uniform
    occurrence `n (ps.map .ftvar)` introduces `ps` as free type variables of the
    referring datatype's constructor argument, and `argVarsScoped` requires those
    to be among the referring datatype's own `tyParams`. A datatype's own header
    always passes (`ps = tyParams ⊆ tyParams`), so self-reference is always
    available; a nullary datatype (`ps = []`) is visible to everyone. -/
def visibleRefs (headers : List Header) (tyParams : List TyIdentifier) :
    List BlockRef :=
  headers.filterMap (fun h =>
    if h.params ⊆ tyParams then some (h.name, h.params.map .ftvar) else none)

/-! ## Shuffling

`genConstructorsForAllTypes` emits datatypes in a fixed inhabitance order (each
datatype's witness constructor references only earlier datatypes), and each
datatype's constructors are emitted witness-first. Since order is semantically
irrelevant — both among the datatypes of a `mutual … end` block and among a
datatype's constructors — we randomly permute both so the generator can reach
every ordering. `permutationOf` produces a random permutation packaged with a proof
that it *is* a permutation of the input (correct by construction), which the proofs
consume via `MutualADTWF`'s permutation-invariance (`MutualADTWF_perm`) and the
membership-based constructor shape lemmas. -/

/-- Generates a random permutation of the list `xs`.  The returned value is
    packaged with a proof that it really is a permutation of `xs`, so the generator
    is *correct by construction*.

    This mirrors `Plausible.Gen.permutationOf`: recurse on the tail to obtain a
    permutation `ys`, then insert the head `x` at a uniformly-random position in
    `ys`.  Note that we sample the insertion index with raw `RandomChoice.choose`
    rather than `chooseNat`, since we need to retain the proof `n ≤ ys.length` in
    order to build the permutation witness (via `List.perm_insertIdx`).

    Unlike `listOf` / `nonEmptyListOf`, this generator recurses structurally on `xs`
    (a decreasing argument), so it needs no `partial_fixpoint`. -/
def permutationOf [Gen G] : (xs : List α) → G { ys // xs.Perm ys }
  | [] => pure ⟨[], List.Perm.nil⟩
  | x :: xs => do
    let ⟨ys, h1⟩ ← permutationOf xs
    let ⟨n, _, h3⟩ ← ULift.down <$> RandomChoice.choose 0 ys.length (Nat.zero_le _)
    return ⟨ys.insertIdx n x, (h1.cons x).trans (List.perm_insertIdx x ys h3).symm⟩

/-! ## Generating the block

`genParamsList` draws one type-parameter list per datatype. `genConstructors` generates a
single datatype's constructors given its header and the block's headers (from
which it computes its visible references). `genConstructorsForAllTypes` folds `genConstructors` over the
headers, and `genMutuallyRecursiveDatatypes` ties phase 1 (headers) to phase 2 (bodies),
then shuffles the resulting block. -/

/-- Draw `n` type-parameter lists, one per datatype, each of independently chosen
    length in `[0, maxTyParams]`. Each list is drawn fresh against `reserved` (the
    block names and reserved keywords) and is internally distinct, but lists for
    different datatypes are drawn independently and may overlap. -/
def genParamsList [Gen G] (reserved : List String) (maxTyParams : Nat) :
    Nat → G (List (List TyIdentifier))
  | 0 => pure []
  | n + 1 => do
    let numTyParams ← chooseNat 0 maxTyParams (by omega)
    let params ← genFreshNames reserved numTyParams
    let rest ← genParamsList reserved maxTyParams n
    pure (params :: rest)

/-- Generate one datatype's constructors, given its header `(nm, params)`, the
    full header list `allHeaders` (for computing visible references), the
    *inhabitance references* `inhabRefs` (block members already known to be
    inhabited — the datatypes generated before this one), and the base
    reserved-name list `reserved` (the block names and reserved keywords).

    The datatype's own type parameters are reserved for its field/constructor
    names. The mandatory first *witness* constructor is generated over `inhabRefs`
    (with `recCallsAllowed := true`): all of its argument types therefore mention
    only already-inhabited block members (or none at all), so the datatype is
    itself inhabited — without requiring the constructor to be free of *all* block
    names. This witness both discharges `constrs_ne` and is what
    `genMutuallyRecursiveDatatypes_inhabited` uses. The remaining constructors are
    generated over the full `blockRefs`. -/
def genConstructors [Gen G] (baseTypes : List String) (tyCons : List KnownTyCon)
    (allHeaders : List Header) (inhabRefs : List BlockRef)
    (nm : String) (params : List TyIdentifier)
    (maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat)
    (reserved : List String) : G (LDatatype Unit) := do
  let blockRefs := visibleRefs allHeaders params
  let reserved := params ++ reserved
  -- The witness constructor may reference already-inhabited datatypes (`inhabRefs`),
  -- which is what makes this datatype inhabited via mutual recursion.
  let cname₀ ← genFreshName reserved
  let (args₀, reserved) ← genConstrArgs baseTypes tyCons inhabRefs params
    true maxArgs maxSize (cname₀ :: reserved)
  let numExtraBase ← chooseNat 0 maxExtraBaseConstrs (by omega)
  let (baseConstrs, reserved) ← genConstrs baseTypes tyCons blockRefs params
    false maxArgs maxSize numExtraBase reserved
  let numRec ← chooseNat 0 maxRecConstrs (by omega)
  let (recConstrs, _) ← genConstrs baseTypes tyCons blockRefs params
    true maxArgs maxSize numRec reserved
  -- The constructors are generated witness-first; permute them, since constructor
  -- order within a datatype is irrelevant. The `Perm` witness discharges
  -- `constrs_ne` (a permutation of a non-empty list is non-empty).
  let orderedConstrs := { name := ⟨cname₀, ()⟩, args := args₀ } :: (baseConstrs ++ recConstrs)
  let ⟨constrs, hperm⟩ ← permutationOf orderedConstrs
  pure { name := nm, typeArgs := params, constrs := constrs,
         constrs_ne := by
           have : constrs ≠ [] := by
             intro h; exact absurd (h ▸ hperm) (by simp)
           simpa [List.length_eq_zero_iff] using this }

/-- Generate the bodies of all datatypes in the block, one per header of the todo
    list, each referring to `allHeaders` for its visible references. The `done`
    accumulator holds the headers already processed; each datatype's witness
    constructor may reference only those already-generated (hence inhabited)
    datatypes, via `visibleRefs done params`. Processing headers in order this way
    gives a well-founded inhabitance order: the first datatype references nothing
    (`done = []`), and each later one may bottom out through earlier ones.

    The base `reserved` list is reset per datatype (constructor/field names of
    distinct datatypes are independent), but the block names it contains keep every
    datatype's references and names disjoint from other datatypes' names. -/
def genConstructorsForAllTypes [Gen G] (baseTypes : List String) (tyCons : List KnownTyCon)
    (allHeaders : List Header) (maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat)
    (reserved : List String) (done : List Header) : List Header → G (MutualDatatype Unit)
  | [] => pure []
  | h :: rest => do
    let d ← genConstructors baseTypes tyCons allHeaders (visibleRefs done h.params)
      h.name h.params maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved
    let ds ← genConstructorsForAllTypes baseTypes tyCons allHeaders
      maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved (done ++ [h]) rest
    pure (d :: ds)

/-- Generate a well-formed *mutually recursive* algebraic data type block.

    Parameters:
    * `baseTypes` / `tyCons` — the referenceable type constructors;
    * `maxExtraDatatypes` — the block gets `1 + [0, maxExtraDatatypes]` datatypes
      (the `1 +` guarantees the block is non-empty, discharging `nonempty`);
    * `maxTyParams` — cap on each datatype's number of type parameters;
    * `maxExtraBaseConstrs` — each datatype gets `1 + [0, maxExtraBaseConstrs]`
      non-recursive constructors (the `1 +` also discharges `constrs_ne`);
    * `maxRecConstrs` — cap on each datatype's number of recursive constructors;
    * `maxArgs` — cap on each constructor's arity;
    * `maxSize` — cap on each argument type's size.

    The datatype names are drawn pairwise distinct and fresh against
    `initialReserved`. Within a datatype, occurrences may reference any block
    member whose type parameters are a subset of this datatype's (`visibleRefs`).
    Each datatype's mandatory first *witness* constructor references only the
    datatypes generated before it (`visibleRefs done`), so — processing datatypes
    in order — every datatype is inhabited (the first bottoms out with no block
    references, and each later one may bottom out through earlier ones), matching
    the `MutualADTWF` inhabitance requirement without forcing any constructor to be
    free of all block names.

    The result satisfies `ConstrArgWF block ty` for every constructor-argument
    type `ty` (`genMutuallyRecursiveDatatypes_argsWF`), references only names in
    `baseTypes ∪ tyCons ∪ (block names) ∪ {"arrow"}`
    (`genMutuallyRecursiveDatatypes_refsKnown`), and — with a suitable ambient context — is
    `MutualADTWF` (`genMutuallyRecursiveDatatypes_MutualADTWF`).

    `extraReserved` additionally forbids every generated datatype name from
    colliding with a caller-supplied name pool — typically the ambient
    `LContext`'s known-type/datatype names, which is what
    `genMutuallyRecursiveDatatypes_MutualADTWF_default` passes so the output is well-formed in
    the real Core context. Defaults to `[]`. -/
def genMutuallyRecursiveDatatypesOrdered [Gen G]
    (baseTypes : List String := defaultBaseTypes)
    (tyCons : List KnownTyCon := defaultTyCons)
    (maxExtraDatatypes : Nat := 2) (maxTyParams : Nat := 2)
    (maxExtraBaseConstrs : Nat := 1) (maxRecConstrs : Nat := 3)
    (maxArgs : Nat := 3) (maxSize : Nat := 3)
    (extraReserved : List String := []) :
    G (MutualDatatype Unit) := do
  let reserved := initialReserved baseTypes tyCons extraReserved
  -- At least one datatype, with pairwise-distinct names fresh against `reserved`.
  let numExtra ← chooseNat 0 maxExtraDatatypes (by omega)
  let names ← genFreshNames reserved (numExtra + 1)
  let reserved := names ++ reserved
  let paramsList ← genParamsList reserved maxTyParams names.length
  let headers : List Header :=
    (names.zip paramsList).map (fun p => { name := p.1, params := p.2 })
  genConstructorsForAllTypes baseTypes tyCons headers maxExtraBaseConstrs maxRecConstrs
    maxArgs maxSize reserved [] headers

/-- Generate a well-formed *mutually recursive* algebraic data type block, with the
    datatypes in random order. `genMutuallyRecursiveDatatypesOrdered` produces the
    block in inhabitance order (each datatype's witness constructor references only
    earlier datatypes); this wrapper `shuffle`s it, since order within a
    `mutual … end` block is semantically irrelevant. `MutualADTWF` is invariant
    under this permutation (`MutualADTWF_perm`), so the shuffled block is still
    well-formed (`genMutuallyRecursiveDatatypes_MutualADTWF`). -/
def genMutuallyRecursiveDatatypes [Gen G]
    (baseTypes : List String := defaultBaseTypes)
    (tyCons : List KnownTyCon := defaultTyCons)
    (maxExtraDatatypes : Nat := 2) (maxTyParams : Nat := 2)
    (maxExtraBaseConstrs : Nat := 1) (maxRecConstrs : Nat := 3)
    (maxArgs : Nat := 3) (maxSize : Nat := 3)
    (extraReserved : List String := []) :
    G (MutualDatatype Unit) := do
  let block ← genMutuallyRecursiveDatatypesOrdered baseTypes tyCons maxExtraDatatypes maxTyParams
    maxExtraBaseConstrs maxRecConstrs maxArgs maxSize extraReserved
  let ⟨block', _⟩ ← permutationOf block
  pure block'

/-! ## Running the generator

`sample` produces one mutually recursive block in `IO`, using Basalt's default
`IO` `RandomChoice` interpretation. Example:

```
#eval do
  let block ← DatatypeGen.sample
  IO.println (repr block)
```
-/

/-- Draw a single random well-formed mutually recursive datatype block in `IO`. -/
def sample (maxSize : Nat := 3) : IO (MutualDatatype Unit) :=
  genMutuallyRecursiveDatatypes (G := IO) (maxSize := maxSize)

end DatatypeGen
