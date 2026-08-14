import StrataGenerators.ProgramGen
import Strata.Languages.Core.ProgramType

open Lambda Core Imperative

/-!
# Shared check predicates for the whole-program generator

`ProgramGen.genProgram` (in `StrataGenerators.ProgramGen`) generates a random
well-typed Strata Core `Program`, proven sound against
`Core.TypeSpec.ProgramHasTypeA` in `ProgramGen/Sound.lean`. Until now it was the
one generator with **no** presence in either test driver: the suites covered the
expression / command / function / statement / procedure generators directly, so
nothing exercised the whole-program fold or the properties that only make sense
across declarations.

This module holds the harness-independent `check*` predicates, following the
convention of the other `*.TestSupport` modules: each returns a `Bool` so the
LSpec driver, the Plausible-only driver, and (if wired later) a Tyche panel all
share one verdict.

## Why `Core.Program.typeCheck` is *not* used as the oracle here

The obvious property — "every generated program passes Strata's own program
typechecker" — is **false today**, for reasons that predate this generator's
ADT work and are not defects in it:

* `Function 'f': a decreases clause was supplied but the function has no body` —
  `genFunction` draws `body` and `measure` independently, so a bodiless function
  can carry a measure. This is the known function-typechecker-completeness gap
  the function suite already pins (`prop_function_rejection_only_measure`).
* `Cannot find this fvar in the context! v` — `genDistinct` emits fresh
  *variables*, which the declarative spec accepts (it asks only for
  `∃ mty, HasTypeA [] e mty`, and an annotated `fvar` supplies it) but the
  algorithmic checker resolves against a context that never binds them.
* `Cannot infer the type of this operation: churchFalse` — `corePolyOps` lists
  schemes (`churchTrue`/`churchFalse`/`id`) that are *not* in `Core.Factory`, so
  the checker cannot resolve them even though the annotated spec types them from
  their own annotation.

Measured over 25 draws: 1 passed, 24 failed, every failure in one of those three
pre-existing classes. Asserting it would therefore add a red check that says
nothing about this change, so the properties below are the ones that are actually
true of the generator, plus the coverage statistic this PR is about.
-/

namespace ProgramGen.TestSupport

/-! ## Collecting operator names -/

/-- Every `.op` name occurring anywhere in an expression. -/
partial def opNames : LExpr' → List String
  | .op _ o _ => [o.name]
  | .app _ a b => opNames a ++ opNames b
  | .abs _ _ _ e => opNames e
  | .quant _ _ _ _ tr e => opNames tr ++ opNames e
  | .ite _ c t e => opNames c ++ opNames t ++ opNames e
  | .eq _ a b => opNames a ++ opNames b
  | _ => []

/-- Every `.op` name occurring in a statement list, including inside nested
    blocks, `ite` arms, and loop guards/measures/invariants. -/
partial def stmtOpNames (ss : List Statement) : List String :=
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
    | .block _ b _ => stmtOpNames b
    | .ite c t e _ =>
      (match c with | .det x => opNames x | _ => []) ++ stmtOpNames t ++ stmtOpNames e
    | .loop g m invs b _ =>
      (match g with | .det x => opNames x | _ => [])
        ++ (m.map opNames).getD []
        ++ invs.flatMap (fun p => opNames p.2)
        ++ stmtOpNames b
    | _ => []

/-- Every `.op` name occurring in a declaration's *expressions* — a function's
    body / measure / preconditions, a procedure's contract clauses and body, or an
    axiom's proposition. Type-level declarations contribute none. -/
def declOpNames (d : Decl) : List String :=
  match d with
  | .func f _ =>
    (f.body.map opNames).getD [] ++ (f.measure.map opNames).getD []
      ++ f.preconditions.flatMap (fun p => opNames p.expr)
  | .proc p _ =>
    p.spec.preconditions.values.flatMap (fun c => opNames c.expr)
      ++ p.spec.postconditions.values.flatMap (fun c => opNames c.expr)
      ++ (match p.body with | .structured ss => stmtOpNames ss | _ => [])
  | .ax a _ => opNames a.e
  | _ => []

/-- Every datatype block the program declares, in declaration order. -/
def datatypeBlocks (P : Program) : List (MutualDatatype Unit) :=
  P.decls.filterMap fun d =>
    match d with
    | .type (.data block) _ => some block
    | _ => none

/-- The derived-function names the program's datatype blocks contribute — the
    constructors, testers, and safe/unsafe field accessors Strata generates. Read
    through the same `adtDerivedOps`/`adtDerivedPolyOps` the generator feeds into
    its operator vocabulary, so this cannot drift from what is actually callable. -/
def derivedNames (P : Program) : List String :=
  (datatypeBlocks P).flatMap fun block =>
    (ProgramGen.adtDerivedOps block).map Prod.fst
      ++ (ProgramGen.adtDerivedPolyOps block).map Prod.fst

/-- The derived-function names the program's declarations actually *call*. -/
def calledDerivedNames (P : Program) : List String :=
  let derived := derivedNames P
  ((P.decls.flatMap declOpNames).filter derived.contains).eraseDups

/-! ## Checks -/

/-- **Every declared name is globally distinct.** `ProgramHasType'` requires
    `P.getNames.Nodup` — a single flat namespace across every declaration kind —
    and the generator establishes it by construction, threading one reserved-name
    set across the whole fold. This is the executable counterpart. -/
def checkNamesNodup (P : Program) : Bool :=
  (P.getNames.map (·.name)).eraseDups.length == P.getNames.length

/-- **Every datatype block is accepted by Strata's own `addMutualBlock`.** The
    generator gates each block on exactly this call and only emits it on the `.ok`
    branch (that is what makes the emitted declaration match `DeclHasType'
    .type_data`), so replaying the adds in declaration order must succeed. A
    failure would mean the generator emitted a block the checker rejects — i.e.
    the gate leaked.

    The replay starts from `coreContext` (the fold's own starting point, see
    `initState`) and must also thread the program's **abstract type**
    declarations, because a later block may reference one: `genDeclDatatype` draws
    its block over the *threaded* vocabulary, which abstract types extend
    (interleaving direction (2) of `docs/program-gen-interleaving.md`). Replaying
    the blocks alone spuriously fails on exactly those programs — measured 28/40
    without the abstract-type adds versus 40/40 with them. -/
def checkDatatypeBlocksAccepted (P : Program) : Bool :=
  go DatatypeGen.coreContext P.decls
where
  go (C : LContext CoreLParams) : List Decl → Bool
    | [] => true
    | .type (.con tc) _ :: rest =>
      match C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default with
      | .ok C' => go C' rest
      | .error _ => false
    | .type (.data block) _ :: rest =>
      match @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
          instToFormatIDMetaCoreLParams C block with
      | .ok C' => go C' rest
      | .error _ => false
    | _ :: rest => go C rest

/-- **Every called derived function is one the program's datatypes actually
    declare.** Vacuously true when no derived function is called; the point is
    that a body can only name a derived function whose datatype is *already*
    declared, since the vocabulary grows at the datatype step and only later
    declarations draw from it. A failure would mean a body called into a datatype
    that does not exist in the program — an unresolvable name. -/
def checkCalledDerivedAreDeclared (P : Program) : Bool :=
  (calledDerivedNames P).all (derivedNames P).contains

/-- **A called derived function is declared *before* the call site.** Stronger
    than `checkCalledDerivedAreDeclared`: it pins the *ordering* the fold
    establishes. For each declaration, every derived name it calls must come from
    a datatype block appearing strictly earlier in the program.

    This is the property that actually characterizes this feature — "procedures
    and functions refer to algebraic data types that are defined *earlier* in the
    program". If the vocabulary were ever seeded before the corresponding block
    was emitted, this would fail. -/
def checkDerivedCallsFollowDeclaration (P : Program) : Bool :=
  go [] P.decls
where
  /-- `available` accumulates the derived names of blocks seen so far. -/
  go (available : List String) : List Decl → Bool
    | [] => true
    | d :: rest =>
      let derivedHere : List String :=
        match d with
        | .type (.data block) _ =>
          (ProgramGen.adtDerivedOps block).map Prod.fst
            ++ (ProgramGen.adtDerivedPolyOps block).map Prod.fst
        | _ => []
      -- A derived call in `d` must resolve against blocks declared *earlier*.
      -- Names in `derivedHere` do not count: a datatype declaration carries no
      -- expressions, so it cannot call anything anyway.
      let called := (declOpNames d).filter (fun n => (derivedNames P).contains n)
      called.all available.contains && go (available ++ derivedHere) rest

/-! ## Coverage statistic

Not a pass/fail property: the generator is free to draw a program whose bodies
happen to call nothing. Reported as a *rate* so a regression to the old
structurally-zero behaviour is visible. -/

/-- Whether the program both declares a datatype and calls at least one of its
    derived functions. -/
def mentionsDerivedFunction (P : Program) : Bool :=
  !(calledDerivedNames P).isEmpty

/-- Split the called derived names by family, against the program's own blocks:
    `(constructors, testers, safe accessors, unsafe accessors)`. Used by the
    coverage report so a run shows *which* kinds of derived function were
    exercised, not merely that some were. -/
def calledByFamily (P : Program) : List String × List String × List String × List String :=
  let called := calledDerivedNames P
  let classify (n : String) : Option ProgramGen.DerivedOpFamily :=
    (datatypeBlocks P).findSome? fun block =>
      let names := (ProgramGen.adtDerivedOps block).map Prod.fst
        ++ (ProgramGen.adtDerivedPolyOps block).map Prod.fst
      if names.contains n then some (ProgramGen.classifyDerivedOp block n) else none
  ( called.filter (fun n => classify n == some .constr)
  , called.filter (fun n => classify n == some .tester)
  , called.filter (fun n => classify n == some .accessor)
  , called.filter (fun n => classify n == some .unsafeAccessor) )

end ProgramGen.TestSupport
