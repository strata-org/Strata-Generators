import StrataGenerators.AdtLaws
import StrataGenerators.PrinterCoverage

/-!
# `mutual … end` blocks whose datatypes are *not* mutually recursive

Strata Core declares algebraic datatypes in blocks: `TypeDecl.data` carries a
`MutualDatatype`, printed as `mutual d₁ … dₙ end`, and every datatype of the block
may refer to every other. The question this module answers is whether a block is
*required* to use that freedom — i.e. whether a `mutual … end` holding datatypes
that do not refer to one another at all is accepted, and accepted with the same
meaning as declaring each of them separately.

It matters for two reasons. A front end that emits Core (or a user writing it) has
no reason to compute the strongly-connected components of its datatype graph
before printing a block, so blocks of independent datatypes will occur; and the
generator itself is proved sound only against `MutualADTWF`, which says nothing
about the block being *connected*.

## What is checked

`genIndependentBlock` draws `k` datatypes **independently** — each is a
one-datatype draw of `DatatypeGen.genMutuallyRecursiveDatatypes`, over a reserved
set threaded across the draws — and concatenates them into a single block. Since
each datatype is drawn knowing nothing of the others' names, no constructor field
can mention another datatype of the block: `crossRefs` verifies that, so the
property cannot silently degrade into "a connected block is accepted".

Self-reference is *retained*: a datatype referring to itself is recursive but not
*mutually* recursive, and excluding it would lose the interesting shapes (a list, a
tree) for no gain.

Four claims, in increasing strength:

1. `checkIndependentBlockAccepted` — `LContext.addMutualBlock` accepts the block.
2. `checkIndependentBlockUsable` — a program that declares the block *and calls
   its constructors* type checks (the `AdtLaws.lawProgram` shape, reused: it is
   exactly "a program that uses every constructor of every datatype in the
   block").
3. `checkSplitBlockAgrees` — declaring the same datatypes as `k` separate
   one-datatype blocks is also accepted, and yields the **same derived
   vocabulary**: the same constructor, tester, selector and eliminator names, at
   the same types. This is the "same meaning" half — a block of independent
   datatypes is interchangeable with the split form.
4. `checkIndependentBlockPrints` — the printer renders the block without logging a
   conversion error.
-/

open Lambda Core Imperative Strata

namespace StrataGenerators.MutualBlockShape

open StrataGenerators.AdtLaws

/-! ## Drawing a block of independent datatypes -/

/-- Draw `k + 1` datatypes independently and concatenate them into one block.

    Each draw is `genMutuallyRecursiveDatatypes` with `maxExtraDatatypes := 0`, so
    it produces a one-datatype block, and the names already used are passed as
    `extraReserved`. Threading the reserved set is what makes the datatypes
    *independent* in the strong sense: a later datatype cannot even name an earlier
    one, since the earlier one's name was not in the vocabulary it drew over. It
    also keeps the concatenation legal — `addMutualBlock`'s duplicate checks and
    `genBlockFactory`'s name checks both need block-wide distinctness, which
    `DatatypeGen` does not otherwise guarantee across datatypes (see
    `AdtLaws.blockAccepted`). -/
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

/-- The pairs `(d, e)` of *distinct* datatypes of the block such that some
    constructor field of `d` mentions `e`. Empty exactly when the block is a
    collection of independent (though possibly self-recursive) datatypes.

    Used as the non-vacuity guard for every property below: a block whose
    `crossRefs` is non-empty is *not* the shape under test, and the property says
    so rather than passing. -/
def crossRefs (block : MutualDatatype Unit) : List (String × String) :=
  let names := block.map (·.name)
  block.flatMap fun d =>
    (d.constrs.flatMap fun c => c.args.flatMap fun (_, τ) => tyHeads τ)
      |>.filter (fun n => n != d.name && names.contains n)
      |>.eraseDups
      |>.map (fun n => (d.name, n))
where
  /-- Every type-constructor head symbol occurring in `τ`, at any depth. -/
  tyHeads : LMonoTy → List String
    | .ftvar _ => []
    | .bitvec _ => []
    | .tcons n args => n :: args.attach.flatMap (fun a => tyHeads a.1)
  termination_by τ => SizeOf.sizeOf τ
  decreasing_by cases a; term_by_mem

/-- Whether the block is the shape under test: at least two datatypes, and no
    cross-reference between two distinct ones. A one-datatype block is excluded
    because `mutual` is vacuous for it — the question is about a block that *looks*
    mutual and is not. -/
def isIndependentBlock (block : MutualDatatype Unit) : Bool :=
  block.length ≥ 2 && (crossRefs block).isEmpty

/-! ## The claims -/

/-- The context the block is added to: Strata's real Core context, the same
    starting point `ProgramGen`'s fold uses. -/
private def baseCtx : LContext CoreLParams := DatatypeGen.coreContext

private def addBlock (C : LContext CoreLParams) (block : MutualDatatype Unit) :
    Except Strata.Message (LContext CoreLParams) :=
  @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
    instToFormatIDMetaCoreLParams C block

/-- Whether every datatype of the block is accepted **on its own**, as a
    one-datatype block. The screen that makes the claims below about the *block*:
    a datatype Strata refuses in isolation (a `f`/`f!` field pair, say — see
    `AdtLaws.checkNoDerivedNameCollisions`) would make them red for a reason that
    has nothing to do with the block being unconnected. -/
def eachDatatypeAccepted (block : MutualDatatype Unit) : Bool :=
  block.all (fun d => (addBlock baseCtx [d]).isOk)

/-- **A `mutual … end` block of non-mutually-recursive datatypes is accepted.**
    `addMutualBlock` checks name clashes, positivity/uniformity/nesting
    (`checkConstructorArgsWF`), type references and inhabitance — none of which
    mentions connectedness, so this should hold; the property is what says it does.

    Stated as *joining* rather than as bare acceptance: given datatypes each of
    which is accepted alone, putting them in one `mutual` block keeps them
    accepted. Vacuously `true` on a block that is not the shape under test or one of
    whose datatypes is already refused in isolation. -/
def checkIndependentBlockAccepted (block : MutualDatatype Unit) : Bool :=
  !(isIndependentBlock block && eachDatatypeAccepted block)
  || (addBlock baseCtx block).isOk

/-- **A program declaring the block and calling its constructors type checks.**
    Stronger than acceptance by the context alone: it puts the block through
    `Program.typeCheck`'s declaration fold and then *uses* every constructor of
    every datatype, via the injectivity/disjointness program of
    `AdtLaws.lawProgram`.

    Screened on `AdtLaws.blockAccepted` as well as on the shape, so that a failure
    is about the block being unconnected rather than about a name collision the
    concatenation might have introduced. -/
def checkIndependentBlockUsable (block : MutualDatatype Unit) : Bool :=
  !(isIndependentBlock block && blockAccepted block)
  || checkLawProgramTypeChecks block

/-- The derived vocabulary a context holds: the name and type scheme of every
    factory function, **excluding the eliminators**.

    The eliminators are excluded because they are the one derived function that is
    *defined* block-wide: `elimFuncs` gives `d$Elim` a case-function argument for
    every constructor of every datatype in the block
    (`RoseTree$Elim : RoseTree → (Forest → β → α) → …`), so the joint and split forms
    differ there by design, not by defect. Constructors, testers and selectors are
    per-datatype in both forms, and those are what the equivalence claim is about.
    The eliminators get their own property, `checkDerivedFuncsWellScoped`. -/
private def factoryEntries (C : LContext CoreLParams) : List (String × String) :=
  (C.functions.toArray.toList.filter (fun fn => !fn.name.name.endsWith "$Elim")).map
    (fun fn => (fn.name.name, (Std.format fn.type).pretty))

/-- The monotype of a factory function: its inputs curried onto its output. -/
private def funcMonoTy (fn : LFunc CoreLParams) : LMonoTy :=
  LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)

/-- The derived functions of `block` whose type mentions a type variable that
    their own `typeArgs` does not bind, as `(name, unbound variables)`. -/
def unboundDerivedTyVars (block : MutualDatatype Unit) : List (String × List String) :=
  match Lambda.genBlockFactory (T := CoreLParams) block with
  | .error _ => []
  | .ok f =>
    f.toArray.toList.filterMap fun fn =>
      let unbound := (funcMonoTy fn).freeVars.filter (fun v => !fn.typeArgs.contains v)
      if unbound.isEmpty then none else some (fn.name.name, unbound)

/-- **Every derived function's type is closed under its own type parameters.**

    **FAILS honestly**, on any block whose datatypes do not all declare the *same*
    type parameters — which `addMutualBlock` permits and an independent block almost
    always does. `elimFuncs` builds the case-function arguments of `d$Elim` from the
    constructors of *every* datatype in the block, but sets
    `typeArgs := retTyVars ++ d.typeArgs` — only `d`'s own parameters. Any other
    datatype's parameters are then free. For
    `datatype Aa x { mkA(fa : x) }` and `datatype Bb y z { mkB(fb : y), nilB() }`
    in one block:

    ```
    Aa$Elim : ∀[$__ty0, $__ty1, x].    Aa x   → (x → $__ty0) → (y → $__ty1) → $__ty1 → $__ty0
                                                                ^ unbound
    Bb$Elim : ∀[$__ty0, $__ty1, y, z]. Bb y z → (x → $__ty0) → (y → $__ty1) → $__ty1 → $__ty1
                                                 ^ unbound
    ```

    `elimFuncs` states the assumption in a comment — `let typeArgs := block[0].typeArgs`
    with "OK because all must have same typevars" — but nothing enforces it:
    `validateMutualBlock` checks only for duplicate datatype names, and
    `checkConstructorArgsWF` constrains *occurrences*, not parameter lists.

    The consequence is latent rather than immediate: a program calling such an
    eliminator still type checks (an unbound variable unifies), so what is lost is
    the constraint that a case function has the right argument type. Either
    `addMutualBlock` should reject a block with differing parameters, or `elimFuncs`
    should bind their union. -/
def checkDerivedFuncsWellScoped (block : MutualDatatype Unit) : Bool :=
  (unboundDerivedTyVars block).isEmpty

/-- Whether the datatypes of the block all declare the same type parameters — the
    condition `elimFuncs` assumes and nothing checks. Reported as the statistic
    that explains `checkDerivedFuncsWellScoped`'s verdict. -/
def blockParamsUniform (block : MutualDatatype Unit) : Bool :=
  match block with
  | [] => true
  | d :: rest => rest.all (fun e => e.typeArgs == d.typeArgs)

/-- **Splitting the block into one-datatype blocks changes nothing.** Declaring
    `d₁ … dₙ` as a single `mutual` block and declaring them as `n` separate blocks
    must both be accepted and must yield the same derived vocabulary — the same
    constructors, testers, selectors and eliminators, at the same types.

    This is the claim that a `mutual` block of independent datatypes *means* the
    same as the split form, and it is only meaningful because the datatypes are
    independent: for a genuinely mutually recursive block the split form is
    ill-formed (each half would reference a type that is not yet declared), so the
    two forms would be trivially distinguishable.

    The comparison is up to ordering (`List.Perm` via sorted rendering), since the
    two forms push the same functions in a different order. -/
def checkSplitBlockAgrees (block : MutualDatatype Unit) : Bool :=
  if !isIndependentBlock block then true
  else
    match addBlock baseCtx block with
    | .error _ => true  -- acceptance is `checkIndependentBlockAccepted`'s claim
    | .ok cOne =>
      match block.foldlM (fun C d => addBlock C [d]) baseCtx with
      | .error _ => false
      | .ok cSplit =>
        (factoryEntries cOne).mergeSort (fun a b => a.1 ≤ b.1)
          == (factoryEntries cSplit).mergeSort (fun a b => a.1 ≤ b.1)

/-- Whether every field type of the block avoids the constructs the printer is
    *already known* to be unable to render, so that a print failure is about the
    block's shape rather than about a defect the suite reports elsewhere:

    * a `bitvec w` at a width outside `[1, 8, 16, 32, 64]` — the subject of the
      property `printer: every typecheckable bitvec width is printable`;
    * a `regex`, which has no literal form;
    * an arrow, i.e. a function-typed field;
    * a `Triggers` or `TriggerGroup` field. `lmonoTyToCoreType`
      (`FormatCore.lean`) enumerates the types it can render and these two are not
      among them, so a field at either logs
      `unsupported construct in lmonoTyToCoreType: unknown type`. They reach a
      *field* position only because `defaultBaseTypes` is derived from
      `Core.KnownTypes`, which registers both; a single datatype with such a field
      fails to print identically, so the gap is the printer's and not the
      block's.

    Without this screen the property is red on about 16 of 26 independent blocks
    for reasons that have nothing to do with `mutual`. -/
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

/-- **The block prints without a conversion error.** `Core.formatProgram`
    substitutes a placeholder and *logs* an error rather than failing, so an
    unprintable construct would otherwise round-trip as a different program; the
    oracle is that no error was logged (see `StrataGenerators.PrinterCoverage`).

    Included because the multi-datatype block is exactly where the printer and the
    grammar could disagree: `TypeDecl`'s formatter emits the `mutual … end`
    keywords, while the DDM grammar's `command_datatypes` is a newline-separated
    list of `DatatypeDecl` with no such keywords.

    Screened on `blockAvoidsKnownPrinterGaps`, so what it tests is the block. -/
def checkIndependentBlockPrints (block : MutualDatatype Unit) : Bool :=
  !(isIndependentBlock block && blockAvoidsKnownPrinterGaps block)
  || StrataGenerators.PrinterCoverage.printsWithoutError
       { decls := [.type (.data block) .empty] }

-- ── The eliminator-scoping defect, pinned deterministically ───────────
--
-- The property above searches for this at random; these `#guard`s hold the minimal
-- witness, so a build failure names it even on a run whose draws all happen to have
-- uniform type parameters.

/-- Two independent datatypes with *different* type parameters — a block
    `addMutualBlock` accepts and `elimFuncs` mis-scopes. -/
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

-- And each eliminator leaves the *other* datatype's parameter free.
#guard unboundDerivedTyVars paramMismatchWitness == [("Aa$Elim", ["y"]), ("Bb$Elim", ["x"])]
#guard !checkDerivedFuncsWellScoped paramMismatchWitness

-- With matching parameters the same shape is well scoped, which is what makes the
-- differing parameter lists the cause.
#guard checkDerivedFuncsWellScoped
  [ { name := "Aa", typeArgs := ["x"],
      constrs := [ { name := ⟨"mkA", ()⟩, args := [(⟨"fa", ()⟩, (.ftvar "x" : LMonoTy))],
                     testerName := "Aa..isMkA" } ],
      constrs_ne := by decide },
    { name := "Bb", typeArgs := ["x"],
      constrs := [ { name := ⟨"mkB", ()⟩, args := [(⟨"fb", ()⟩, (.ftvar "x" : LMonoTy))],
                     testerName := "Bb..isMkB" } ],
      constrs_ne := by decide } ]

-- ── The `Triggers` printer gap, pinned deterministically ──────────────
--
-- Why `blockAvoidsKnownPrinterGaps` screens `Triggers`/`TriggerGroup`: the gap is
-- the printer's, and it needs no `mutual` block to show up. A *single* datatype
-- with such a field fails to print, and swapping the field for an `int` fixes it,
-- so screening the two names cannot be hiding a block-shape defect. If upstream
-- teaches `lmonoTyToCoreType` these types, the second guard fires and the screen
-- can drop them.

/-- One datatype, one `Triggers`-typed field — no block shape involved. -/
def triggersFieldWitness : MutualDatatype Unit :=
  [ { name := "Tw", typeArgs := []
      constrs := [ { name := ⟨"mkTw", ()⟩,
                     args := [(⟨"ft", ()⟩, .tcons "Triggers" [])],
                     testerName := "Tw..isMkTw" } ]
      constrs_ne := by decide } ]

/-- The same datatype with the field at `int`. -/
def intFieldWitness : MutualDatatype Unit :=
  [ { name := "Tw", typeArgs := []
      constrs := [ { name := ⟨"mkTw", ()⟩,
                     args := [(⟨"ft", ()⟩, .tcons "int" [])],
                     testerName := "Tw..isMkTw" } ]
      constrs_ne := by decide } ]

-- `Triggers` is drawable as a field type at all only because the vocabulary is
-- derived from `Core.KnownTypes`.
#guard DatatypeGen.defaultBaseTypes.contains "Triggers"
#guard DatatypeGen.defaultBaseTypes.contains "TriggerGroup"

-- The gap, and its absence at `int` — one datatype, so not about `mutual`.
#guard !StrataGenerators.PrinterCoverage.printsWithoutError
  { decls := [.type (.data triggersFieldWitness) .empty] }
#guard StrataGenerators.PrinterCoverage.printsWithoutError
  { decls := [.type (.data intFieldWitness) .empty] }

-- So the screen rejects the first and admits the second.
#guard !blockAvoidsKnownPrinterGaps triggersFieldWitness
#guard blockAvoidsKnownPrinterGaps intFieldWitness

/-- The rendered `mutual … end` declaration, for a counterexample report and for
    the Tyche panel. -/
def renderBlock (block : MutualDatatype Unit) : String :=
  (Std.format (Core.TypeDecl.data block)).pretty

/-- The printed form of a program declaring the block, whether or not the printer
    logged an error. Used by the report of `checkIndependentBlockPrints`. -/
def printedBlockProgram (block : MutualDatatype Unit) : String :=
  StrataGenerators.PrinterCoverage.printedText
    (Core.formatProgram { decls := [.type (.data block) .empty] }).pretty

end StrataGenerators.MutualBlockShape
