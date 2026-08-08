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
# A generator for random well-formed algebraic data types in Strata Core

This module has a random generator for well-formed *mutually recursive* algebraic
data type definitions in Strata Core. The generator uses Basalt `Gen`.

The generator makes a `MutualDatatype Unit`. That type is a `List (LDatatype Unit)`,
and it holds the contents of one `mutual … end` block. The block obeys the argument
half of `Core.TypeSpec.MutualADTWF`. That half is the `argsWF`, `refsKnown` and
`argVarsScoped` fields from `Strata.Languages.Core.DatatypeTypeSpec`.

A **block datatype** is a datatype that this `mutual … end` block declares. The datatypes
of one block can refer to each other, therefore they are mutually recursive. This module
uses the term *block datatype* for each of them, and also for the datatype that the
generator makes now.

## Shape

`genArgTy` is the heart of the generator. It makes one constructor argument type. It
carries a flag `recCallsAllowed : Bool`. The generator sets this flag to `false` in
exactly the positions where the specification forbids the name of each block
datatype. These positions are the domain of an arrow, and the arguments of another
type constructor.

This one flag makes the output well-formed. `DatatypeGenProofs.lean` changes the flag
into a proof.

A *recursive occurrence* is a reference to a block datatype. The generator emits
more than a single self-reference. It emits any member of the supplied
`blockRefs : List BlockRef`. That list holds the block datatypes that the new
datatype can refer to. Read the section "Type parameters" for the exact rule.

The recursive occurrence is the one part of the generator that shows the change from a
single datatype to a mutual block. The old code compared a head symbol against one
`selfName`, but the conditions are now weaker. The head symbol must be a member of
the set of block names. A recursive occurrence is `n (n's typeArgs)` for each block
datatype `n`.

`genConstrArgs` and `genConstrs` make argument lists and constructors.
`genConstructors` makes the constructors of one datatype, and
`genConstructorsForAllTypes` makes the constructors of all datatypes.
`genMutuallyRecursiveDatatypes` makes the full block. The generator divides the
`size` by 2 at each level of the recursion, therefore the recursion stops. `oneOf`
picks one of the alternatives with equal probability.

The caller supplies the base types of arity `0` and the applied type constructors of
arity `1` or more as two separate parameters. Therefore the generator does not filter
on arity.

## Terms for the parts of an argument type

This module uses three terms for the kinds of type that `genLeafTy` makes. `genArgTy`
does not call itself to make any of these three kinds. Therefore they are the point at
which the recursion on `size` stops, and the name `genLeafTy` comes from this property.

* A **base type** holds no type variable. It is a bitvector `.bitvec w` of one width,
  or a member `b` of `baseTypes` with no arguments, which is `.tcons b []`. `genBaseTy`
  makes a base type.
* A **rigid type variable** is one of the type parameters of the datatype, and
  `tyParams` holds these parameters. The type is `.ftvar v` for a member `v` of
  `tyParams`. The name is rigid because the datatype declares it, therefore the
  generator cannot put another type in its place.
* A **recursive occurrence** is a reference to a block datatype. It is
  `.tcons n args` for a member `(n, args)` of `blockRefs`.

A recursive occurrence is not a leaf of the type. For example, `List α` holds the type
`α`. But `genArgTy` does not recurse to make the arguments of such an occurrence,
because the rule for a uniform occurrence gives those arguments.

## Type parameters, and which datatypes can refer to which

Each datatype in the block declares its *own* `typeArgs`. The generator makes each
list of type parameters independently, and the block does not share one list. The
generator takes all of these names from one common name space, therefore two
different datatypes can use the same parameter names.

A datatype `dᵢ` can refer to a block datatype `dⱼ` only when
`dⱼ.typeArgs ⊆ dᵢ.typeArgs`. The reference is the uniform occurrence
`dⱼ (dⱼ.typeArgs)`. Each `dᵢ` obeys this test for itself. A datatype that has no
type parameters obeys the test for each other datatype.

This subset test is the condition that keeps the output `MutualADTWF`. A uniform
occurrence `dⱼ (dⱼ.typeArgs)` adds the type parameters of `dⱼ` as free variables of a
constructor argument of `dᵢ`. `MutualADTWF.argVarsScoped` says that each free variable
of a constructor argument of `dᵢ` is a member of `dᵢ.typeArgs`. Therefore that field
forces `dⱼ.typeArgs ⊆ dᵢ.typeArgs`. `blockRefs` holds the members that obey this test
for the datatype that the generator makes now.

## How the generator makes names, and the set of reserved names

`genFreshName` makes each name that the generator invents. These names are the name of
each datatype, its type parameters, its constructor names and its field names.
`genFreshName` reads a list of *reserved* names, and the generator threads that list
through the recursion. The generator then adds the new name to the list at each point
where the names must be different. Therefore a generated name cannot be the same as
one of these names:

* A reserved Strata Core keyword from `reservedKeywordsList`. The parser rejects such
  a keyword in the position of an identifier.
* A base type or a type constructor that the generator can refer to, or the reserved
  arrow constructor `"arrow"`. Such a name makes a base type read as a recursive
  occurrence, or makes an application read as an arrow.
* The name of another block datatype. Therefore the names of the block are
  different in pairs, which `namesNodup` needs. A base type or an applied type also
  cannot read as a reference to a block datatype.

The generator threads the datatype names through `reserved`, therefore these names
stay different in pairs. The generator makes each type parameter fresh against the
reserved set, but it does not add the parameter back to that set. Therefore two
different datatypes can use the same parameter names, and one parameterized datatype
can refer to another.

`genFreshName` in `CmdHasTypeAGen/Core.lean` uses the same method for variable names.
It draws a random legal identifier. If that identifier is already in the reserved
list, it falls back to a name that is longer than each reserved name. Such a name is
certainly absent from the list. The generator puts no other limit on a name. In
particular, it adds no prefix and no suffix.

The reserved set discharges the side conditions of the soundness proof. Read
`NamesOk` and `namesOk_of_fresh` in `DatatypeGenProofs.lean`.

## What "well-formed" means here

For a block `block`, `ConstrArgWF block ty` is the conjunction
`NotNested block ty ∧ StrictPosUnif block ty`. Let `N := block.map (·.name)` be the
set of block names. A constructor argument type is well-formed only when it obeys
these three conditions:

1. **Strict positivity.** No `n ∈ N` occurs at the left of an arrow. Therefore, in
   `t₁ → t₂`, each block name is absent from `t₁`, and `t₂` is again strictly
   positive.
2. **Uniformity.** Each occurrence of an `n ∈ N` has exactly the `typeArgs` of that
   datatype as its arguments. `UniformOccur.self` gives this condition. A recursive
   reference must be `n τs`, with no change.
3. **No nested occurrence.** No `n ∈ N` occurs inside the arguments of another type
   constructor. `NotNested` gives this condition. An application with `n` at the head
   is a correct direct reference, but `Pair (n τs) …` and `Sequence (n τs)` are not
   correct.

`refsKnown` also puts a condition on each referenced type constructor name. That name
must be a known primitive, a datatype of the ambient context, or a block name. The
generator obeys this field by construction. It emits only head symbols from
`baseTypes` and `tyCons`, together with the block names and `"arrow"`.

The first constructor that the generator makes for each datatype is *a constructor that
is inhabited*. `ConstrInhab` in `Strata.DL.Lambda.DatatypeWF` gives that condition, and
it holds when each argument type of the constructor is inhabited. Therefore the datatype
is also inhabited, which the inhabitance field of `MutualADTWF` needs.

The generator draws that constructor from a smaller set of references than the other
constructors. That smaller set is *the set of names that the inhabited constructor may
use*. Read the section "Ranks, and not an order" for it. No constructor must be free of
all block names.
-/

namespace DatatypeGen

/-! ## The known type constructors of the ambient context

`refsKnown` resolves a referenced name against the known types and the datatypes of
the ambient `LContext`. This generator makes a *new* datatype, and no proof obligation
connects it to one concrete context. Therefore the caller supplies the type
constructors that the generator can refer to as explicit parameters. The generator
emits only these constructors, the name of the datatype and `"arrow"`. Therefore
`refsKnown` holds for each context that knows all of these names. -/

/-- An applied type constructor that the generator can refer to, with its arity. -/
abbrev KnownTyCon := String × Nat

/-- The names of the base types that the generator can refer to. Each of these base
    types has arity `0`. The `LMonoTy` generator in `HasTypeAGen/Core.lean` uses the same
    names. `nullaryBaseTypeNames` holds `bool`, `int`, `string`, `real` and `regex`.
    `pickBitvecWidth` draws the bitvectors separately, as in that generator. -/
def defaultBaseTypes : List String :=
  nullaryBaseTypeNames

/-- The applied type constructors that the generator can refer to. These are the
    parameterized primitives that Strata Core knows. Read `Core.KnownLTys`. This list
    does not hold `"arrow"`, because `genArgTy` has a separate branch for an arrow. -/
def defaultTyCons : List KnownTyCon :=
  [("Sequence", 1), ("Map", 2)]

/-! ## How the generator makes a name

`genFreshName` makes each name. It draws a legal Core identifier, and the identifier
is always absent from the threaded list of reserved names. `initialReserved` gives the
first value of that list, and the generator adds each new name to it. -/

/-- The names that a new name must not be the same as, before the generator invents a
    name of its own:

    * `"arrow"`. `LMonoTy.arrow t1 t2` is by definition
      `LMonoTy.tcons "arrow" [t1, t2]`, therefore a datatype or a constructor with the
      name `"arrow"` reads as a true arrow.
    * The reserved Strata Core keywords. The parser rejects such a keyword in the
      position of an identifier.
    * The type names in `baseTypes` and `tyCons` that the generator can refer to.
      Therefore a base type such as `.tcons "bool" []` cannot read as a recursive
      occurrence of the datatype, and an application cannot read as one.
    * The `extraReserved` names that the caller wants to keep. These names are usually
      the known types and the datatypes of the *ambient context*. Therefore a new
      datatype name cannot be the same as a type that the `LContext` around it knows.
      Strata Core knows more type symbols than the generator refers to, for example
      `Triggers` and `bitvec`. The reservation of these symbols makes the output of the
      generator sound against the true Core context. The default value is `[]`. -/
def initialReserved (baseTypes : List String) (tyCons : List KnownTyCon)
    (extraReserved : List String := []) : List String :=
  "arrow" :: (reservedKeywordsList ++ baseTypes ++ tyCons.map (·.1) ++ extraReserved)

/-- The length of the longest name in a list. The result is `0` for an empty list. A
    name that is longer than this length cannot be a member of the list. This is the
    argument from length that `fallbackName` uses. `maxNameLen` in
    `CmdHasTypeAGen/Core.lean` does the same for a `VarCtx`. -/
def maxNameLength (names : List String) : Nat :=
  names.foldl (fun acc nm => max acc nm.length) 0

/-- A name that is always absent from `reserved`. The name is a string of
    `maxNameLength reserved + 1` characters `x`, therefore it is longer than each
    reserved name. It is a legal Core identifier, because it starts with a letter and
    holds only letters. It holds only the character `x`, therefore it is never a
    reserved keyword.

    This definition uses `indexedFreshName` from `CmdHasTypeAGen/Core.lean`. The member
    of that family at index `0` is this string. -/
def fallbackName (reserved : List String) : String :=
  indexedFreshName (maxNameLength reserved) 0

/-- Make a name that is absent from `reserved`.

    `genIdentName` draws a random legal Core identifier. That identifier starts with a
    letter, and it continues with identifier characters. `dodgeKeyword` then makes sure
    that it is not a reserved keyword. If the identifier is already in `reserved`, this
    function falls back to `fallbackName`, which uses the argument from length. The
    result is always a legal identifier that is absent from `reserved`. The generator
    adds no prefix and no suffix to it.

    `genFreshName` in `CmdHasTypeAGen/Core.lean` does the same against a `VarCtx`. This
    function does it against a `List String`. -/
def genFreshName [Gen G] (reserved : List String) : G String := do
  let s ← genIdentName
  if reserved.contains s then pure (fallbackName reserved) else pure s

/-- Make `n` names that are absent from `reserved` and different in pairs. This
    function adds each name to the reserved list before it draws the next name. -/
def genFreshNames [Gen G] (reserved : List String) (n : Nat) : G (List String) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let s ← genFreshName reserved
    let rest ← genFreshNames (s :: reserved) n
    pure (s :: rest)

/-! ## Block references

A recursive occurrence in a mutual block can be each block datatype that the new datatype
can refer to. The generator records each such datatype as its name with its own type
arguments as types. A uniform occurrence of that datatype is `name args`, with no
change. -/

/-- A block datatype that a recursive occurrence can refer to. The pair holds the name
    of the datatype and its own type arguments, which are `d.typeArgs.map .ftvar`. A
    uniform occurrence is `.tcons name args`. -/
abbrev BlockRef := String × LMonoTys

/-! ## The generator for a well-formed constructor argument type

`genLeafTy` and `genArgTy` are the heart of the generator. They have these parameters:

* `baseTypes : List String`. These are the names of the base types that the generator
  can refer to. Each of these base types has arity `0`.
* `tyCons : List KnownTyCon`. These are the applied type constructors that the
  generator can refer to.
* `blockRefs : List BlockRef`. These are the block datatypes that the new datatype can
  refer to. Each member is its name with its own type arguments as types. A uniform
  occurrence of a member is `name args`, with no change. For `List α`, the occurrence
  must be `List α`. It cannot be `List β` or `List (α, α)`. This list makes the old
  single pair `selfName` and `selfArgs` more general. The conditions now test for
  membership in this set of names, and not for equality with one name.
* `tyParams : List TyIdentifier`. These are the type parameter names of the datatype.
  The generator uses them to make the rigid type variables, which are the `.ftvar`
  types.
* `recCallsAllowed : Bool`. This flag tells the generator if it can emit a recursive
  occurrence of a `blockRefs` member here. This one flag keeps the output well-formed.
  The generator sets it to `false` in exactly the positions where the specification
  forbids the name of a block datatype.
-/

/-- Make a base type. The result is a bitvector `.bitvec w` of a random width `w`, or a
    member `b` of `baseTypes` with no arguments, which is `.tcons b []`. A base type
    holds no type variable.

    This function uses `pickBitvecWidth` from `HasTypeAGen/Core.lean`. The `LMonoTy`
    generator uses the same width generator, and it now draws a width with no limit.
    Read issue #38. `pickBitvecWidth` is at the head of the list, therefore the list is
    clearly a `::`. Therefore `simp` can prove that `oneOf` gets a list that is not
    empty, and an empty `baseTypes` does no damage.

    `pickBaseType` in that module has no parameter for the pool of base types. But
    `genBaseTy` takes the pool `baseTypes` from the caller, because the soundness proof
    quantifies over it. Therefore `genBaseTy` cannot call `pickBaseType`. The two
    functions agree on the default pool, and `defaultBaseTypes` is
    `nullaryBaseTypeNames`. -/
def genBaseTy [Gen G] (baseTypes : List String) : G LMonoTy :=
  oneOf ((fun () => pickBitvecWidth) ::
         baseTypes.map (fun b => (fun () => pure (.tcons b [])))) (by simp)

/-- Make an argument type of one of the three kinds at which the recursion of `genArgTy`
    stops. `genArgTy` calls this function at `size = 0`, and also as one alternative at a
    larger size. The three kinds are:

    * a **base type** from `genBaseTy`, which is `.bitvec w` or `.tcons b []`;
    * a **rigid type variable** `.ftvar v` for a member `v` of `tyParams`, which is a
      type parameter that the datatype declares;
    * a **recursive occurrence** `.tcons n args` for a member `(n, args)` of
      `blockRefs`. This kind is present only when `recCallsAllowed` is `true` and
      `blockRefs` is not empty.

    This function matches on `tyParams`, and it does not join all of the alternatives
    into one flat list. Therefore each of the three kinds has the same probability, and
    the many base type names cannot outvote the recursive occurrence. The match also
    makes `elements tyParams` correct, because `elements` needs a list that is not empty.
    For the same reason, the alternative for a recursive occurrence is present only when
    `blockRefs` is not empty, therefore `elements blockRefs` is correct. If `blockRefs`
    is empty, this function makes no recursive occurrence. Such a datatype can refer to
    no block datatype, not even to itself. -/
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

/-- Make a well-formed constructor argument type at the given `size`. The generator can
    emit a recursive occurrence only when `recCallsAllowed` is `true`.

    At `size = 0` the result comes from `genLeafTy`, therefore it is a base type, a rigid
    type variable or a recursive occurrence. At a larger size the result is an arrow, an
    application of a known type constructor, or again one of those three kinds.

    This function sets the flag to `false` in the two positions that keep the output
    well-formed:

    * The branch for an **arrow** makes the domain with `recCallsAllowed := false`,
      because strict positivity forbids a block name at the left of an arrow. It makes
      the codomain with the flag from the caller, because a recursive occurrence is
      correct there.
    * The branch for an **application** makes each argument with
      `recCallsAllowed := false`. The rule against a nested occurrence forbids a block
      name inside the arguments of another type constructor.

    The `match tyCons` makes `elements tyCons` correct. -/
def genArgTy [Gen G] (baseTypes : List String) (tyCons : List KnownTyCon)
    (blockRefs : List BlockRef) (tyParams : List TyIdentifier)
    (recCallsAllowed : Bool) (size : Nat) : G LMonoTy :=
  if size = 0 then
    genLeafTy baseTypes blockRefs tyParams recCallsAllowed
  else
    -- Divided by 2 at each level of the recursion, therefore the recursion stops.
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

/-! ## The constructors and the datatype

`genConstrArgs` and `genConstrs` thread the list of reserved names. They return the
longer list with their result, therefore the caller can continue to collect the names.
The generator draws each field name and each constructor name fresh against that list.
Therefore all of the names of one generated datatype are different in pairs. -/

/-- Make the argument list of one constructor. The list has `maxArgs` arguments or less.
    The generator draws the size of each argument independently in the range
    `[0, maxSize]`, and it makes a fresh name for each field. The result holds the
    argument list and the list of reserved names with those field names added. -/
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

/-- Make `n` constructors. Each constructor gets a fresh name and fresh field names. The
    result holds the constructors and the longer list of reserved names. -/
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

/-! ## The headers and the set of visible references

The generator makes a block in two phases. In phase 1 it draws all of the *headers*.
Each header is the name of a datatype with its own type parameters. In phase 2 it makes
the body of each datatype, which is its list of constructors. For phase 2 the generator
calculates a `blockRefs` list from the headers.

A header is a `Lambda.TypeConstructor`. That structure holds a `name` and a list
`params`. The field `bound` keeps its default value `.Infinite`. A block is
`headers.map (fun h => { name := h.name, typeArgs := h.params, … })`.

The generator draws the names different in pairs, because it threads them through
`reserved`. Therefore the names of the block are different, which `namesNodup` needs,
and no name is the same as a base type or an applied type. The generator draws each type
parameter fresh against the reserved set, but it does not add the parameter back.
Therefore two different datatypes can use the same parameter names, and one
parameterized datatype can refer to another. -/

/-- The block references that are visible to a datatype with the type parameters
    `tyParams`. The result holds each header `⟨n, ps⟩` for which `ps ⊆ tyParams`, as the
    uniform occurrence `(n, ps.map .ftvar)`.

    The filter `ps ⊆ tyParams` keeps the output `MutualADTWF`. A uniform occurrence
    `n (ps.map .ftvar)` adds `ps` as free type variables of a constructor argument of the
    datatype that makes the reference. `argVarsScoped` needs those variables to be
    members of the `tyParams` of that datatype. The header of a datatype always obeys
    the filter, because `ps = tyParams ⊆ tyParams`. Therefore a datatype can always refer
    to itself. A datatype that has no type parameters has `ps = []`, therefore it is
    visible to each block datatype. -/
def visibleRefs (headers : List TypeConstructor) (tyParams : List TyIdentifier) :
    List BlockRef :=
  headers.filterMap (fun h =>
    if h.params ⊆ tyParams then some (h.name, h.params.map .ftvar) else none)

/-! ## How the generator mixes the constructors

The generator makes the constructor that is inhabited first, for each datatype. The order
of the constructors in one datatype has no effect on the meaning of the datatype.
Therefore the generator puts the constructors into a random order, and it can make each
order.

`permutationOf` makes a random permutation, and it returns a proof that the result is a
permutation of the input. Therefore it is correct by construction. The proofs use that
permutation through the shape lemmas for the constructors, which speak about membership.

The order of the datatypes in the block needs no such change. The *rank* that each
datatype draws gives the set of names that its inhabited constructor may use, through
`lowerRankHeaders`. The position of the datatype in the list gives nothing. Therefore the
order of the output already has no relation to the inhabitance structure.

This result is the purpose of the design with ranks. The generator makes the block in the
order of the drawn names, and the completeness proof gets each target block directly. The
proof builds no order and inverts no permutation. -/

/-- Make a random permutation of the list `xs`. The result holds a proof that it is a
    permutation of `xs`. Therefore this generator is *correct by construction*.

    This function does the same as `Plausible.Gen.permutationOf`. It first makes a
    permutation `ys` of the tail. It then puts the head `x` at a random position in `ys`,
    and each position has the same probability. This function draws the index with
    `RandomChoice.choose` and not with `chooseNat`, because it must keep the proof
    `n ≤ ys.length`. `List.perm_insertIdx` needs that proof to build the proof of the
    permutation.

    `listOf` and `nonEmptyListOf` need `partial_fixpoint`, but this generator does not.
    Its recursion is on the structure of `xs`, which is a decreasing argument. -/
def permutationOf [Gen G] : (xs : List α) → G { ys // xs.Perm ys }
  | [] => pure ⟨[], List.Perm.nil⟩
  | x :: xs => do
    let ⟨ys, h1⟩ ← permutationOf xs
    let ⟨n, _, h3⟩ ← ULift.down <$> RandomChoice.choose 0 ys.length (Nat.zero_le _)
    return ⟨ys.insertIdx n x, (h1.cons x).trans (List.perm_insertIdx x ys h3).symm⟩

/-! ## How the generator makes the block

`genParamsList` draws one list of type parameters for each datatype. `genRanks` draws one
*inhabitance rank* for each datatype. `genConstructors` makes the constructors of one
datatype. It gets three inputs: the header of that datatype, the headers of the block, and
the set of names that the inhabited constructor may use. It calculates the visible
references from the headers of the block. That set of names holds the block datatypes of a
lower rank. `genConstructorsForAllTypes` applies `genConstructors` to each header with its
rank. `genMutuallyRecursiveDatatypes` connects phase 1, which makes the headers and the
ranks, to phase 2, which makes the bodies.

**The set of names that the inhabited constructor may use.** The generator makes the first
constructor of each datatype from a smaller set of references than the other constructors.
That first constructor is a constructor that is inhabited. For a datatype at rank `r`, the
smaller set is `visibleRefs (lowerRankHeaders rankedHeaders r) params`. It holds each
visible block datatype of a rank less than `r`. The other constructors get the full set
`visibleRefs allHeaders params`, which also holds the datatype itself.

**Ranks, and not an order.** Each datatype draws one rank in the range
`[0, blockSize-1]`. Two datatypes can draw the same rank. The inhabited constructor of a
datatype can refer only to block datatypes of a lower rank.

The proofs use one graph to show that this condition is enough. The nodes of that graph are the
block datatypes. Take two datatypes `d` and `d'`. The graph has one edge from `d` to `d'`
when the argument types of the inhabited constructor of `d` hold the name of `d'`. This module
calls that graph *the graph of name references that the inhabited constructors make*.

Each edge of that graph makes the rank smaller, therefore the graph has no cycle. Therefore each
datatype is inhabited. The inhabited constructor of a datatype at the smallest rank refers to no
block datatype. The reason is that the set of names that it may use is empty.

The old design gave the same guarantee of inhabitance. In that design the generator made
the datatypes in a fixed order, and the inhabited constructor referred only to the
datatypes before it. The new design makes the rank an explicit label, and the position in
the list gives nothing. Therefore the completeness proof does not build a topological
order. It uses the rank that the inhabitance derivation gives it. Read `rankExists` in the
proofs. -/

/-- Draw `n` lists of type parameters, one for each datatype. The generator draws the
    length of each list independently in the range `[0, maxTyParams]`. It draws each list
    fresh against `reserved`, which holds the block names and the reserved keywords. The
    names in one list are different in pairs. The generator draws the lists for two
    different datatypes independently, therefore two lists can hold the same names. -/
def genParamsList [Gen G] (reserved : List String) (maxTyParams : Nat) :
    Nat → G (List (List TyIdentifier))
  | 0 => pure []
  | n + 1 => do
    let numTyParams ← chooseNat 0 maxTyParams (by omega)
    let params ← genFreshNames reserved numTyParams
    let rest ← genParamsList reserved maxTyParams n
    pure (params :: rest)

/-- Draw `n` inhabitance ranks, one for each datatype. The generator draws each rank
    independently in the range `[0, maxRank]`, and two datatypes can draw the same rank.

    The rank is the only condition that makes the datatypes inhabited. The set of names that
    the inhabited constructor may use holds only block datatypes of a lower rank. Therefore
    that constructor can refer only to those datatypes. Therefore the inhabited constructor of
    a datatype at the smallest rank has no block name in it. Each datatype at a higher rank
    is inhabited through the lower ranks.

    `maxRank := blockSize - 1` is large enough, because the rank from the inhabitance
    derivation is never more than `blockSize - 1`. Read `rankExists`. -/
def genRanks [Gen G] (maxRank : Nat) : Nat → G (List Nat)
  | 0 => pure []
  | n + 1 => do
    let r ← chooseNat 0 maxRank (by omega)
    let rest ← genRanks maxRank n
    pure (r :: rest)

/-- Make the constructors of one datatype. This function gets four inputs:

    * `(nm, params)`, the header of the datatype;
    * `allHeaders`, the full list of headers, from which it calculates the visible
      references;
    * `inhabRefs`, the set of names that the inhabited constructor may use. It holds the
      block datatypes that the caller lets that constructor refer to. These datatypes have
      a lower rank.
    * `reserved`, which holds the block names and the reserved keywords.

    This function also reserves the type parameters of the datatype for its field names
    and its constructor names.

    The first constructor is always present, and it is a constructor that is inhabited.
    This function makes it from `inhabRefs`, with `recCallsAllowed := true`. Therefore each
    argument type of that constructor holds only block datatypes of a lower rank, or no block
    datatype at all. Therefore the datatype is inhabited, and no constructor must be free of
    all block names. That first constructor also discharges `constrs_ne`, and
    `genMutuallyRecursiveDatatypes_inhabited` uses it. This function makes the other
    constructors from the full set `blockRefs`. -/
def genConstructors [Gen G] (baseTypes : List String) (tyCons : List KnownTyCon)
    (allHeaders : List TypeConstructor) (inhabRefs : List BlockRef)
    (nm : String) (params : List TyIdentifier)
    (maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat)
    (reserved : List String) : G (LDatatype Unit) := do
  -- `blockRefs` holds each visible block datatype, therefore it also holds this datatype.
  -- `inhabRefs` is different. The caller gives it, and it holds only the visible block
  -- datatypes of a rank less than the rank of this datatype. Read `visibleRefs` and
  -- `lowerRankHeaders`.
  let blockRefs := visibleRefs allHeaders params
  let reserved := params ++ reserved
  -- The inhabited constructor can refer to the members of `inhabRefs`, which all have a
  -- lower rank. This is what makes this datatype inhabited.
  let cname₀ ← genFreshName reserved
  let (args₀, reserved) ← genConstrArgs baseTypes tyCons inhabRefs params
    true maxArgs maxSize (cname₀ :: reserved)
  let numExtraBase ← chooseNat 0 maxExtraBaseConstrs (by omega)
  let (baseConstrs, reserved) ← genConstrs baseTypes tyCons blockRefs params
    false maxArgs maxSize numExtraBase reserved
  let numRec ← chooseNat 0 maxRecConstrs (by omega)
  let (recConstrs, _) ← genConstrs baseTypes tyCons blockRefs params
    true maxArgs maxSize numRec reserved
  -- The inhabited constructor comes first. Then put the constructors into a random order,
  -- because their order in one datatype has no effect. The `Perm` proof discharges
  -- `constrs_ne`, because a permutation of a list that is not empty is not empty.
  let orderedConstrs := { name := ⟨cname₀, ()⟩, args := args₀ } :: (baseConstrs ++ recConstrs)
  let ⟨constrs, hperm⟩ ← permutationOf orderedConstrs
  pure { name := nm, typeArgs := params, constrs := constrs,
         constrs_ne := by
           have : constrs ≠ [] := by
             intro h; exact absurd (h ▸ hperm) (by simp)
           simpa [List.length_eq_zero_iff] using this }

/-- The headers of a rank less than `r`, from a list of headers with their ranks.

    The set of names that the inhabited constructor of a datatype at rank `r` may use is
    `visibleRefs (lowerRankHeaders rankedHeaders r) params`. That set holds the block
    datatypes that this constructor can refer to. The datatype itself is never a member of
    its own set, because `r < r` is false.

    Therefore each edge of the graph of name references that the inhabited constructors make
    goes from rank `r` to a rank less than `r`. Therefore that graph has no cycle, and each
    datatype is inhabited. -/
def lowerRankHeaders (rankedHeaders : List (TypeConstructor × Nat)) (r : Nat) :
    List TypeConstructor :=
  rankedHeaders.filterMap (fun hr => if hr.2 < r then some hr.1 else none)

/-- Make the bodies of all of the block datatypes, one body for each pair
    `(header, rank)` of the list of work. Each datatype gets its visible references from
    `allHeaders`. It gets the set of names that its inhabited constructor may use from
    `rankedHeaders`, which holds all of the headers with their ranks.

    For a datatype at rank `r`, that set is
    `visibleRefs (lowerRankHeaders rankedHeaders r) params`. Therefore that set holds only
    block datatypes of a rank less than `r`. Therefore each edge of the graph of name
    references that the inhabited constructors make gets a smaller rank, and each datatype
    is inhabited. The inhabited constructor of a datatype at the smallest rank refers to no
    block datatype.

    The old function threaded an accumulator `done` for a fixed order, but this function
    threads no such accumulator. The drawn ranks alone give that set of names, therefore
    the order of the declarations has no effect.

    This function gives the same first value of `reserved` to each datatype. The
    constructor names and the field names of two different datatypes are independent. That
    list holds the block names, therefore the names and the references of each datatype
    stay separate from the names of the other datatypes. -/
def genConstructorsForAllTypes [Gen G] (baseTypes : List String) (tyCons : List KnownTyCon)
    (allHeaders : List TypeConstructor) (rankedHeaders : List (TypeConstructor × Nat))
    (maxExtraBaseConstrs maxRecConstrs maxArgs maxSize : Nat)
    (reserved : List String) : List (TypeConstructor × Nat) → G (MutualDatatype Unit)
  | [] => pure []
  | hr :: rest => do
    let d ← genConstructors baseTypes tyCons allHeaders
      (visibleRefs (lowerRankHeaders rankedHeaders hr.2) hr.1.params)
      hr.1.name hr.1.params maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved
    let ds ← genConstructorsForAllTypes baseTypes tyCons allHeaders rankedHeaders
      maxExtraBaseConstrs maxRecConstrs maxArgs maxSize reserved rest
    pure (d :: ds)

/-- Make a well-formed block of *mutually recursive* algebraic data types.

    The parameters are:
    * `baseTypes` and `tyCons`. These are the type constructors that the generator can
      refer to.
    * `maxExtraDatatypes`. The block gets `1 + [0, maxExtraDatatypes]` datatypes. The
      term `1 +` makes sure that the block is not empty, which `nonempty` needs.
    * `maxTyParams`. This is the limit on the number of type parameters of each datatype.
    * `maxExtraBaseConstrs`. Each datatype gets `1 + [0, maxExtraBaseConstrs]`
      constructors that are not recursive. The term `1 +` also discharges `constrs_ne`.
    * `maxRecConstrs`. This is the limit on the number of recursive constructors of each
      datatype.
    * `maxArgs`. This is the limit on the number of arguments of each constructor.
    * `maxSize`. This is the limit on the size of each argument type.

    The generator draws the datatype names different in pairs, and fresh against
    `initialReserved`. In one datatype, an occurrence can refer to each block datatype
    whose type parameters are a subset of the parameters of that datatype. Read
    `visibleRefs`.

    Each datatype draws one *inhabitance rank* in the range `[0, numExtra]`, and two
    datatypes can draw the same rank. The inhabited constructor of each datatype is always
    present, and it refers only to block datatypes of a lower rank. The set of names that it
    may use is `visibleRefs (lowerRankHeaders …)`.

    Therefore each edge of the graph of name references that the inhabited constructors make
    gets a smaller rank. Therefore that graph has no cycle, and each datatype is inhabited.
    The inhabited constructor of a datatype at the smallest rank refers to no block datatype.
    This result gives the inhabitance field of `MutualADTWF`. No constructor must be free of
    all block names, and the generator puts no order on the datatypes of the output.

    The result obeys `ConstrArgWF block ty` for each constructor argument type `ty`. Read
    `genMutuallyRecursiveDatatypes_argsWF`. The result refers only to names in
    `baseTypes ∪ tyCons ∪ (block names) ∪ {"arrow"}`. Read
    `genMutuallyRecursiveDatatypes_refsKnown`. With a correct ambient context, the result
    is `MutualADTWF`. Read `genMutuallyRecursiveDatatypes_MutualADTWF`.

    `extraReserved` holds more names that a new datatype name must not be the same as.
    These names are usually the known types and the datatypes of the ambient `LContext`.
    `genMutuallyRecursiveDatatypes_MutualADTWF_default` gives those names, therefore the
    output is well-formed in the true Core context. The default value is `[]`. -/
def genMutuallyRecursiveDatatypes [Gen G]
    (baseTypes : List String := defaultBaseTypes)
    (tyCons : List KnownTyCon := defaultTyCons)
    (maxExtraDatatypes : Nat := 2) (maxTyParams : Nat := 2)
    (maxExtraBaseConstrs : Nat := 1) (maxRecConstrs : Nat := 3)
    (maxArgs : Nat := 3) (maxSize : Nat := 3)
    (extraReserved : List String := []) :
    G (MutualDatatype Unit) := do
  let reserved := initialReserved baseTypes tyCons extraReserved
  -- One datatype or more. The names are different in pairs, and fresh against `reserved`.
  let numExtra ← chooseNat 0 maxExtraDatatypes (by omega)
  let names ← genFreshNames reserved (numExtra + 1)
  let reserved := names ++ reserved
  let paramsList ← genParamsList reserved maxTyParams names.length
  -- One rank for each datatype, in the range `[0, numExtra]`, which is
  -- `[0, blockSize - 1]`. Two datatypes can draw the same rank.
  let ranks ← genRanks numExtra names.length
  let headers : List TypeConstructor :=
    (names.zip paramsList).map (fun p => { name := p.1, params := p.2 })
  let rankedHeaders : List (TypeConstructor × Nat) := headers.zip ranks
  genConstructorsForAllTypes baseTypes tyCons headers rankedHeaders maxExtraBaseConstrs
    maxRecConstrs maxArgs maxSize reserved rankedHeaders

/-! ## How to run the generator

`sample` makes one mutually recursive block in `IO`. It uses the default `IO`
interpretation of `RandomChoice` from Basalt. This is an example:

```
#eval do
  let block ← DatatypeGen.sample
  IO.println (repr block)
```
-/

/-- Draw one random well-formed block of mutually recursive datatypes in `IO`. -/
def sample (maxSize : Nat := 3) : IO (MutualDatatype Unit) :=
  genMutuallyRecursiveDatatypes (G := IO) (maxSize := maxSize)

end DatatypeGen
