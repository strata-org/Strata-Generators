import StrataGenerators.AdtLaws
import StrataGenerators.PrinterCoverage

/-!
# A `mutual … end` block whose datatypes are *not* mutually recursive

Strata Core declares algebraic datatypes in blocks. A `TypeDecl.data` holds a
`MutualDatatype`, the printer writes it as `mutual d₁ … dₙ end`, and each datatype of the
block can refer to each other datatype. This module answers whether a block *must* use
that freedom. It asks whether Strata accepts a `mutual … end` that holds datatypes which do
not refer to one another, and whether such a block means the same as a separate declaration
for each datatype.

The question matters for two reasons. A front end that emits Core, and a person who writes
Core by hand, have no reason to compute the strongly connected components of a graph of
datatypes before they print a block, so a block of independent datatypes occurs. The proof
of soundness for the generator also uses only `MutualADTWF`, which says nothing about a
block that is *connected*.

## What the properties check

`genIndependentBlock` draws `k` datatypes **independently**. Each draw is a one-datatype
draw of `DatatypeGen.genMutuallyRecursiveDatatypes`, and the generator threads one set of
reserved names through the draws. It then joins the datatypes into one block. Each draw
knows none of the other names, so no constructor field can mention another datatype of the
block. `crossRefs` tests this, so a property cannot become the claim that Strata accepts a
connected block.

A block *keeps* a self-reference. A datatype that refers to itself is recursive and not
*mutually* recursive, and a screen against it loses the interesting shapes, such as a list
and a tree, for no gain.

There are four claims, and each one is stronger than the claim before it:

1. `checkIndependentBlockAccepted`: `LContext.addMutualBlock` accepts the block.
2. `checkIndependentBlockUsable`: a program that declares the block *and calls its
   constructors* typechecks. The property reuses the shape of `AdtLaws.lawProgram`, which
   is a program that uses each constructor of each datatype in the block.
3. `checkSplitBlockAgrees`: Strata also accepts the same datatypes as `k` separate blocks
   of one datatype, and both forms give the **same derived vocabulary**. The names of the
   constructors, the testers, the selectors and the eliminators are the same, and their
   types are the same. This is the half about meaning: a block of independent datatypes and
   the split form are interchangeable.
4. `checkIndependentBlockPrints`: the printer writes the block and it logs no conversion
   error.
-/

open Lambda Core Imperative Strata

namespace StrataGenerators.MutualBlockShape

open StrataGenerators.AdtLaws

/-! ## How the generator draws a block of independent datatypes -/

/-- Draws `k + 1` datatypes independently, and joins them into one block.

    Each draw is `genMutuallyRecursiveDatatypes` with `maxExtraDatatypes := 0`, so each draw
    gives a block of one datatype. The names that the earlier draws used go to the next draw as
    `extraReserved`. This thread of reserved names is what makes the datatypes *independent* in
    the strong sense: a later datatype cannot even name an earlier one, because the vocabulary
    of its draw held no such name.

    The thread also keeps the joined block legal. The checks for a duplicate in
    `addMutualBlock`, and the checks on a name in `genBlockFactory`, both need the names of the
    whole block to be different. `DatatypeGen` does not give that guarantee across two
    datatypes, as `AdtLaws.blockAccepted` describes. -/
def genIndependentBlock [Gen G] (k : Nat) (maxSize : Nat := 0) :
    G (MutualDatatype Unit) := do
  let rec go (n : Nat) (reserved : List String) (acc : MutualDatatype Unit) :
      G (MutualDatatype Unit) := do
    match n with
    | 0 => pure acc
    | n + 1 =>
      let one ← DatatypeGen.genMutuallyRecursiveDatatypes (G := G)
        (maxExtraDatatypes := 0) (maxSize := maxSize) (extraReserved := reserved)
      let names := blockNames one
      go n (names ++ reserved) (acc ++ one)
  go (k + 1) [] []

/-- The pairs `(d, e)` of *different* datatypes of the block where a constructor field of `d`
    mentions `e`. The list is empty exactly when the block holds independent datatypes, and
    such a datatype can still refer to itself.

    Each property below uses this list as its guard against vacuity. A block whose `crossRefs`
    is not empty is *not* the shape under test, and the property then says so and does not
    pass. -/
def crossRefs (block : MutualDatatype Unit) : List (String × String) :=
  let names := block.map (·.name)
  block.flatMap fun d =>
    (d.constrs.flatMap fun c => c.args.flatMap fun (_, τ) => tyHeads τ)
      |>.filter (fun n => n != d.name && names.contains n)
      |>.eraseDups
      |>.map (fun n => (d.name, n))
where
  /-- Each head symbol of a type constructor that occurs in `τ`, at any depth. -/
  tyHeads : LMonoTy → List String
    | .ftvar _ => []
    | .bitvec _ => []
    | .tcons n args => n :: args.attach.flatMap (fun a => tyHeads a.1)
  termination_by τ => SizeOf.sizeOf τ
  decreasing_by cases a; term_by_mem

/-- Whether the block is the shape under test. Two conditions must hold: the block has two or
    more datatypes, and no datatype refers to another datatype of the block. A block of one
    datatype is not the shape under test, because `mutual` is vacuous for such a block. The
    question is about a block that *looks* mutual and is not. -/
def isIndependentBlock (block : MutualDatatype Unit) : Bool :=
  block.length ≥ 2 && (crossRefs block).isEmpty

/-! ## The claims -/

/-- The context that receives the block. It is the real Core context of Strata, and the fold of
    `ProgramGen` starts from the same context. -/
private def baseCtx : LContext CoreLParams := DatatypeGen.coreContext

/-- Adds `block` to the context `C` with `LContext.addMutualBlock`. -/
private def addBlock (C : LContext CoreLParams) (block : MutualDatatype Unit) :
    Except Strata.Message (LContext CoreLParams) :=
  @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
    instToFormatIDMetaCoreLParams C block

/-- Whether Strata accepts each datatype of the block **on its own**, as a block of one
    datatype. This screen keeps the claims below about the *block*. Strata refuses some
    datatypes on their own, such as a datatype that has a field `f` and a field `f!`, which
    `AdtLaws.checkNoDerivedNameCollisions` describes. Without the screen, such a datatype makes
    a claim below fail for a reason that has nothing to do with the shape of the block. -/
def eachDatatypeAccepted (block : MutualDatatype Unit) : Bool :=
  block.all (fun d => (addBlock baseCtx [d]).isOk)

/-- **Strata accepts a `mutual … end` block whose datatypes are not mutually recursive.**
    `addMutualBlock` checks for a name clash, it checks positivity, uniformity and nesting
    through `checkConstructorArgsWF`, and it checks the references to a type and the
    inhabitance. No check mentions a connected block, so the claim must hold, and this property
    says that it does.

    The property states the claim as a *join*, and not as bare acceptance: if Strata accepts
    each datatype alone, then it also accepts the datatypes in one `mutual` block. The property
    is vacuously `true` on a block that is not the shape under test, and on a block that holds a
    datatype which Strata already refuses on its own. -/
def checkIndependentBlockAccepted (block : MutualDatatype Unit) : Bool :=
  !(isIndependentBlock block && eachDatatypeAccepted block)
  || (addBlock baseCtx block).isOk

/-- **A program that declares the block and calls its constructors typechecks.** This claim is
    stronger than acceptance by the context alone. It sends the block through the fold over the
    declarations in `Program.typeCheck`, and it then *uses* each constructor of each datatype,
    through the program for injectivity and disjointness in `AdtLaws.lawProgram`.

    The property screens on `AdtLaws.blockAccepted` and on the shape. A failure is therefore
    about the shape of the block, and not about a name collision that the join of the datatypes
    added. -/
def checkIndependentBlockUsable (block : MutualDatatype Unit) : Bool :=
  !(isIndependentBlock block && blockAccepted block)
  || checkLawProgramTypeChecks block

/-- The derived vocabulary of a context: the name and the type scheme of each function in the
    factory. The list holds **no eliminator**.

    The list holds no eliminator, because an eliminator is the one derived function that the
    code *defines* over the whole block. `elimFuncs` gives `d$Elim` one case-function argument
    for each constructor of each datatype in the block, as in
    `RoseTree$Elim : RoseTree → (Forest → β → α) → …`. The joint form and the split form
    therefore differ there by design, and not by a defect. In both forms, a constructor, a
    tester and a selector belong to one datatype, and the claim of equivalence is about them.
    `checkDerivedFuncsWellScoped` is the property for an eliminator. -/
private def factoryEntries (C : LContext CoreLParams) : List (String × String) :=
  (C.functions.toArray.toList.filter (fun fn => !fn.name.name.endsWith "$Elim")).map
    (fun fn => (fn.name.name, (Std.format fn.type).pretty))

/-- The monotype of a function in the factory: its inputs as arrows onto its output. -/
private def funcMonoTy (fn : LFunc CoreLParams) : LMonoTy :=
  LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)

/-- The derived functions of `block` whose type mentions a type variable that their own
    `typeArgs` does not bind. Each entry is a pair of the name and the free variables. -/
def unboundDerivedTyVars (block : MutualDatatype Unit) : List (String × List String) :=
  match Lambda.genBlockFactory (T := CoreLParams) block with
  | .error _ => []
  | .ok f =>
    f.toArray.toList.filterMap fun fn =>
      let unbound := (funcMonoTy fn).freeVars.filter (fun v => !fn.typeArgs.contains v)
      if unbound.isEmpty then none else some (fn.name.name, unbound)

/-- **The type of each derived function binds each type variable that it mentions.**

    A defect breaks this claim on a block whose datatypes do not all declare the *same* type
    parameters. `addMutualBlock` allows such a block, and an independent block almost always
    has that shape. `elimFuncs` builds the case-function arguments of `d$Elim` from the
    constructors of *each* datatype in the block, but it sets
    `typeArgs := retTyVars ++ d.typeArgs`, which holds only the parameters of `d`. The
    parameters of each other datatype are then free. For `datatype Aa x { mkA(fa : x) }` and
    `datatype Bb y z { mkB(fb : y), nilB() }` in one block:

    ```
    Aa$Elim : ∀[$__ty0, $__ty1, x].    Aa x   → (x → $__ty0) → (y → $__ty1) → $__ty1 → $__ty0
                                                                ^ unbound
    Bb$Elim : ∀[$__ty0, $__ty1, y, z]. Bb y z → (x → $__ty0) → (y → $__ty1) → $__ty1 → $__ty1
                                                 ^ unbound
    ```

    A comment in `elimFuncs` states the assumption next to
    `let typeArgs := block[0].typeArgs`, and it says that each datatype must have the same type
    variables. Nothing enforces the assumption. `validateMutualBlock` checks only for a
    duplicate datatype name, and `checkConstructorArgsWF` constrains an *occurrence* and not a
    list of parameters.

    The result is latent and not immediate. A program that calls such an eliminator still
    typechecks, because a free variable unifies with any type. What the program loses is the
    constraint that a case function has the correct argument type. A fix makes
    `addMutualBlock` reject a block whose parameters differ, or it makes `elimFuncs` bind the
    union of the parameters. -/
def checkDerivedFuncsWellScoped (block : MutualDatatype Unit) : Bool :=
  (unboundDerivedTyVars block).isEmpty

/-- Whether each datatype of the block declares the same type parameters. This is the condition
    that `elimFuncs` assumes and that nothing checks. The suite reports it as the statistic that
    explains the verdict of `checkDerivedFuncsWellScoped`. -/
def blockParamsUniform (block : MutualDatatype Unit) : Bool :=
  match block with
  | [] => true
  | d :: rest => rest.all (fun e => e.typeArgs == d.typeArgs)

/-- **A split of the block into blocks of one datatype changes nothing.** Strata must accept
    `d₁ … dₙ` as one `mutual` block and as `n` separate blocks, and both forms must give the same
    derived vocabulary: the same constructors, testers, selectors and eliminators, at the same
    types.

    This is the claim that a `mutual` block of independent datatypes *means* the same as the
    split form. The claim has content only because the datatypes are independent. For a block
    that is really mutually recursive, the split form is not well formed, because each half
    refers to a type that no declaration has introduced yet, and a reader can then tell the two
    forms apart at once.

    The comparison ignores the order, because the two forms add the same functions in a
    different order. The code therefore sorts both lists before it compares them. -/
def checkSplitBlockAgrees (block : MutualDatatype Unit) : Bool :=
  if !isIndependentBlock block then true
  else
    match addBlock baseCtx block with
    | .error _ => true  -- `checkIndependentBlockAccepted` states the claim about acceptance.
    | .ok cOne =>
      match block.foldlM (fun C d => addBlock C [d]) baseCtx with
      | .error _ => false
      | .ok cSplit =>
        (factoryEntries cOne).mergeSort (fun a b => a.1 ≤ b.1)
          == (factoryEntries cSplit).mergeSort (fun a b => a.1 ≤ b.1)

/-- Whether each field type of the block holds none of the constructs that the printer is
    *already known* to be unable to write. With this screen, a failure to print is about the
    shape of the block, and not about a defect that the suite reports elsewhere. The screen
    rejects these constructs:

    * a `bitvec w` whose width is not one of `1`, `8`, `16`, `32` and `64`. The property
      `printer: every typecheckable bitvec width is printable` covers that width.
    * a `regex`, which has no literal form.
    * an arrow, which is a field with a function type.
    * a `Triggers` field or a `TriggerGroup` field. `lmonoTyToCoreType` lists the types that it
      can write, and these two are not in that list. A field at either type therefore logs
      `unsupported construct in lmonoTyToCoreType: unknown type`. Such a type reaches a *field*
      position only because `defaultBaseTypes` comes from `Core.KnownTypes`, which registers
      both. One datatype with such a field also fails to print, so the gap belongs to the
      printer and not to the block.

    Without this screen, the property fails on many independent blocks for reasons that have
    nothing to do with `mutual`. -/
def blockAvoidsKnownPrinterGaps (block : MutualDatatype Unit) : Bool :=
  block.all fun d => d.constrs.all fun c => c.args.all fun (_, τ) => printableTy τ
where
  printableTy : LMonoTy → Bool
    | .ftvar _ => true
    | .bitvec w => StrataGenerators.PrinterCoverage.printableBvWidths.contains w
    | .tcons n args =>
      n != "regex" && n != "arrow" && n != "Triggers" && n != "TriggerGroup"
        && args.attach.all (fun a => printableTy a.1)
  termination_by τ => SizeOf.sizeOf τ
  decreasing_by cases a; term_by_mem

/-- **The printer writes the block and it logs no conversion error.** `Core.formatProgram` does
    not fail on a construct that it cannot write. It writes a placeholder and it *logs* an error.
    Such a construct can therefore round-trip as a different program. The oracle is that the
    printer logged no error, as `StrataGenerators.PrinterCoverage` describes.

    The property exists because a block of two or more datatypes is where the printer and the
    grammar can disagree. The formatter for a `TypeDecl` emits the keywords `mutual` and `end`,
    and the `command_datatypes` rule of the DDM grammar is a list of `DatatypeDecl` values that
    newlines separate and that holds no such keyword.

    The property screens on `blockAvoidsKnownPrinterGaps`, so it tests the block. -/
def checkIndependentBlockPrints (block : MutualDatatype Unit) : Bool :=
  !(isIndependentBlock block && blockAvoidsKnownPrinterGaps block)
  || StrataGenerators.PrinterCoverage.printsWithoutError
       { decls := [.type (.data block) .empty] }

-- ── The defect in the scope of an eliminator, pinned deterministically ─
--
-- The property above searches for this defect at random. The `#guard` statements below hold the
-- smallest witness, so the build names the defect even on a run whose draws all have uniform
-- type parameters.

/-- Two independent datatypes with *different* type parameters. `addMutualBlock` accepts this
    block, and `elimFuncs` gives its eliminators the wrong scope. -/
def paramMismatchWitness : MutualDatatype Unit :=
  [ { name := "Aa", typeArgs := ["x"]
      constrs := [ { name := ⟨"mkA", ()⟩, args := [(⟨"fa", ()⟩, .ftvar "x")],
                     testerName := "Aa..isMkA" } ]
      constrs_ne := by decide },
    { name := "Bb", typeArgs := ["y", "z"]
      constrs := [ { name := ⟨"mkB", ()⟩, args := [(⟨"fb", ()⟩, .ftvar "y")],
                     testerName := "Bb..isMkB" },
                   { name := ⟨"nilB", ()⟩, args := [], testerName := "Bb..isNilB" } ]
      constrs_ne := by decide } ]

-- The witness is the shape under test, and Strata accepts it.
#guard isIndependentBlock paramMismatchWitness
#guard StrataGenerators.AdtLaws.blockAccepted paramMismatchWitness
#guard !blockParamsUniform paramMismatchWitness

-- Each eliminator leaves the parameter of the *other* datatype free.
#guard unboundDerivedTyVars paramMismatchWitness == [("Aa$Elim", ["y"]), ("Bb$Elim", ["x"])]
#guard !checkDerivedFuncsWellScoped paramMismatchWitness

-- The same shape has the correct scope when the parameters agree, and this shows that the
-- different lists of parameters are the cause.
#guard checkDerivedFuncsWellScoped
  [ { name := "Aa", typeArgs := ["x"],
      constrs := [ { name := ⟨"mkA", ()⟩, args := [(⟨"fa", ()⟩, (.ftvar "x" : LMonoTy))],
                     testerName := "Aa..isMkA" } ],
      constrs_ne := by decide },
    { name := "Bb", typeArgs := ["x"],
      constrs := [ { name := ⟨"mkB", ()⟩, args := [(⟨"fb", ()⟩, (.ftvar "x" : LMonoTy))],
                     testerName := "Bb..isMkB" } ],
      constrs_ne := by decide } ]

-- ── The gap in the printer for `Triggers`, pinned deterministically ────
--
-- These statements say why `blockAvoidsKnownPrinterGaps` screens `Triggers` and
-- `TriggerGroup`. The gap belongs to the printer, and it needs no `mutual` block. One
-- datatype with such a field fails to print, and the same datatype with an `int` field prints.
-- The screen for the two names therefore hides no defect in the shape of a block. If upstream
-- adds these two types to `lmonoTyToCoreType`, then the second guard fails and the screen can
-- drop the two names.

/-- One datatype with one field at the type `Triggers`. No block shape takes part. -/
def triggersFieldWitness : MutualDatatype Unit :=
  [ { name := "Tw", typeArgs := []
      constrs := [ { name := ⟨"mkTw", ()⟩,
                     args := [(⟨"ft", ()⟩, .tcons "Triggers" [])],
                     testerName := "Tw..isMkTw" } ]
      constrs_ne := by decide } ]

/-- The same datatype, but with the field at the type `int`. -/
def intFieldWitness : MutualDatatype Unit :=
  [ { name := "Tw", typeArgs := []
      constrs := [ { name := ⟨"mkTw", ()⟩,
                     args := [(⟨"ft", ()⟩, .tcons "int" [])],
                     testerName := "Tw..isMkTw" } ]
      constrs_ne := by decide } ]

-- A draw can give `Triggers` as a field type only because the vocabulary comes from
-- `Core.KnownTypes`.
#guard DatatypeGen.defaultBaseTypes.contains "Triggers"
#guard DatatypeGen.defaultBaseTypes.contains "TriggerGroup"

-- The gap appears at `Triggers` and it does not appear at `int`. There is one datatype, so the
-- gap is not about `mutual`.
#guard !StrataGenerators.PrinterCoverage.printsWithoutError
  { decls := [.type (.data triggersFieldWitness) .empty] }
#guard StrataGenerators.PrinterCoverage.printsWithoutError
  { decls := [.type (.data intFieldWitness) .empty] }

-- The screen therefore rejects the first datatype and it accepts the second.
#guard !blockAvoidsKnownPrinterGaps triggersFieldWitness
#guard blockAvoidsKnownPrinterGaps intFieldWitness

/-- The printed form of the `mutual … end` declaration, for the report of a counterexample and
    for the Tyche panel. -/
def renderBlock (block : MutualDatatype Unit) : String :=
  (Std.format (Core.TypeDecl.data block)).pretty

/-- The printed form of a program that declares the block, whether or not the printer logged an
    error. The report of `checkIndependentBlockPrints` uses it. -/
def printedBlockProgram (block : MutualDatatype Unit) : String :=
  StrataGenerators.PrinterCoverage.printedText
    (Core.formatProgram { decls := [.type (.data block) .empty] }).pretty

end StrataGenerators.MutualBlockShape
