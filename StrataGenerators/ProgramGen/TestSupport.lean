import StrataGenerators.ProgramGen
import Strata.Languages.Core.ProgramType

open Lambda Core Imperative

/-!
# Shared check predicates for the whole-program generator

`ProgramGen.genProgram`, in `StrataGenerators.ProgramGen`, gives a random well-typed Strata Core `Program`, and
`ProgramGen/Sound.lean` proves it sound against `Core.TypeSpec.ProgramHasTypeW`.

This module holds the `check*` predicates that no harness owns, by the convention of each other `*.TestSupport`
module. Each of them gives a `Bool`, so each driver and each Tyche panel share one verdict.

## Why the oracle here is not `Core.Program.typeCheck`

The checker may reject a generated program that the weak specification accepts: one with a reserved
name or a clash between names of different kinds (`checkerRejectionExpected`). The properties below
hold of every generated program.
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

/-- Each `.op` name that occurs in an *expression* of a declaration. Such an expression is the body, the measure
    or a precondition of a function, a contract clause or the body of a procedure, or the proposition of an
    axiom. A declaration of a type gives no such name. -/
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

/-- The names of the derived functions that each datatype block of the program gives. Those are the constructors,
    the testers, and the safe and unsafe accessors of a field that Strata generates. This definition reads them
    through the same two functions that the generator gives to
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

/-- **Each declared name of the program is distinct.** `ProgramHasType'` needs that fact, in one flat namespace
    over each kind of declaration. The generator establishes it by construction, because it threads one set of
    the reserved names across the whole fold. This predicate is the executable form of that fact. -/
def checkNamesNodup (P : Program) : Bool :=
  (P.getNames.map (·.name)).eraseDups.length == P.getNames.length

/-- **Every datatype block is accepted by Strata's own `addMutualBlock`.** The
    generator gates each block on exactly this call and only emits it on the `.ok`
    branch (that is what makes the emitted declaration match `DeclHasType'
    .type_data`), so replaying the adds in declaration order must succeed. A
    counterexample would mean that the generator emitted a block that the checker rejects, and therefore that the
    gate let a block through.

    The replay starts from `programContext` (`initState.C`) and threads every declaration that
    grows the context as the fold does: an abstract type, which a later block may reference,
    and a function or constant, whose name a later block's derived functions must avoid. -/
def checkDatatypeBlocksAccepted (P : Program) : Bool :=
  go ProgramGen.programContext P.decls
where
  go (C : LContext CoreLParams) : List Decl → Bool
    | [] => true
    | .type (.con tc) _ :: rest =>
      match C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default with
      | .ok C' => go C' rest
      | .error _ => false
    | .func f _ :: rest =>
      match C.addFactoryFunctionWithError f.toLFunc with
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
    declaration draws from it. A counterexample would mean that a body called a datatype that the program does not
    declare, and that name would not resolve. -/
def checkCalledDerivedAreDeclared (P : Program) : Bool :=
  (calledDerivedNames P).all (derivedNames P).contains

/-- **A called derived function is declared *before* the call site.** Stronger
    than `checkCalledDerivedAreDeclared`: it pins the *ordering* the fold
    establishes. For each declaration, every derived name it calls must come from
    a datatype block appearing strictly earlier in the program.

    This property describes the behaviour exactly: a procedure and a function reference an algebraic datatype
    that a declaration *earlier* in the program gives. If the vocabulary held a name before the matching block
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
