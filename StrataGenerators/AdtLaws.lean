import StrataGenerators.DatatypeGen
import StrataGenerators.ProgramGen.TestSupport
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.SMTEncoder

/-!
# The two laws of an algebraic datatype: injectivity and disjointness

`DatatypeGen.genMutuallyRecursiveDatatypes` draws a random and well-formed
`mutual … end` block of algebraic datatypes, which can be mutually recursive. Each
such block denotes an *initial* algebra. Its constructors must therefore obey two
laws, which are the `injection` and `discriminate` tactics of the `Tactics` chapter
of Software Foundations:

* **Injectivity.** For each constructor `C` of arity `k ≥ 1`,
  `C x₁ … x_k = C y₁ … y_k → x₁ = y₁ ∧ … ∧ x_k = y_k`.
* **Disjointness.** For each pair of *different* constructors `C ≠ D` of one
  datatype, `C x_1 ... x_k ≠ D y_1 ... y_k`.

Uniformness has no property here, because `TypeFactory.addMutualBlock` already
checks it syntactically through `checkConstructorArgsWF`.

Neither law is a claim about the generator. Both are claims about **the SMT encoding
of a datatype in Strata**. The generator supplies the datatypes, and the oracle is a
real solver: `cvc5` or `z3` through the whole Core verification pipeline, which is
`Core.verify`. The path under test is therefore the type check, the transforms, the
symbolic evaluation, `SMT.Context.emitDatatypes` and then the solver.

## How a law becomes a proof obligation

The emitted assertion holds no quantifier. Each universally quantified variable
becomes an *uninitialized local*, which is `var x : τ;` and therefore a
`Statement.init … .nondet`. Symbolic evaluation turns such a local into a symbolic
constant with no constraint. For a constructor `C(a : int, b : bool)` with two
fields, the obligation for injectivity is therefore the procedure

```
procedure inj_0_0 () {
  var x0 : int;  var x1 : bool;
  var y0 : int;  var y1 : bool;
  assume [h]: C(x0, x1) == C(y0, y1);
  assert [inj_0_0_f0]: x0 == y0;
  assert [inj_0_0_f1]: x1 == y1;
}
```

and the obligation for disjointness of `C` and `D` is

```
procedure disj_0_0_1 () {
  var x0 : int;  var x1 : bool;  var y0 : …;
  assert [disj_0_0_1]: !(C(x0, x1) == D(y0));
}
```

There is one `assert` for each field, and not one conjunction. A verdict from the
solver then names the field that failed, and not only the constructor.

**The label of an obligation holds indices, and never a generated name.** A generated
datatype name is an arbitrary Core identifier, because `genIdentName` draws a
character that is not alphanumeric, such as `.`, `?` and `@`. A label reaches SMT-LIB
as a symbol, so a label that a generated name builds can turn a failure of a *law*
into a failure of the encoder, and the two must stay separate. The indices are
positions in the block: `inj_{d}_{c}_f{i}` is field `i` of constructor `c` of datatype
`d`. The report also prints the whole block that failed.

## Which blocks are eligible

`validateDatatypesForSMT` rejects a datatype that has a field with a function type. It
reports "Function types cannot be represented in SMT-LIB datatypes", and it throws for
the whole *block* and not for one obligation. A block that holds an arrow anywhere is
therefore skipped before the solver starts, and the suite counts the skip so that it
is visible. `blockIsSmtEligible` is that screen.

A field with an arrow type is common at the default `maxSize` of the generator,
because an arrow is one of three alternatives in `genArgTy` at each size above zero.
The eligible part of the draws is therefore small at that size. A draw at
`maxSize := 0` makes `genArgTy` return `genLeafTy`, whose range holds only a base
type, a type parameter or a recursive occurrence, and never an arrow.
`smtBlockSizeSchedule` mixes both sizes. Size 0 therefore gives the property coverage
that is not vacuous, and the larger sizes still give draws with a `Map` field, a
`Sequence` field, and an arrow field, which the suite counts as a skip.

## Type parameters

A polymorphic datatype has no SMT sort until it receives its parameters.
`groundInstantiation` gives each type parameter the type `int`. This is the cheapest
choice that SMT can encode, and it is enough, because the laws are parametric: an
instance at one ground type is a witness for a failure at each other ground type. The
instantiation applies to the field types only. The *declaration* keeps its parameters,
because that is what the pipeline must handle.
-/

open Lambda Core Imperative

namespace StrataGenerators.AdtLaws

/-! ## How the module instantiates a monotype -/

mutual
/-- Substitutes the type variables of a type, as `σ` gives. This module has its own
    function and it does not use `LMonoTy.subst`, because that function takes the scoped
    `Subst` of Lambda, which is a stack of hash maps with a field for well-formedness. A
    lookup in an association list is all that this module needs. -/
def instTy (σ : List (String × LMonoTy)) : LMonoTy → LMonoTy
  | .ftvar v => (σ.lookup v).getD (.ftvar v)
  | .bitvec n => .bitvec n
  | .tcons n args => .tcons n (instTys σ args)

/-- `instTy` over a list of types. -/
def instTys (σ : List (String × LMonoTy)) : LMonoTys → LMonoTys
  | [] => []
  | t :: ts => instTy σ t :: instTys σ ts
end

/-- Gives each type parameter of `d` the type `int`. This is the ground instance whose
    fields the assertions range over. -/
def groundInstantiation (d : LDatatype Unit) : List (String × LMonoTy) :=
  d.typeArgs.map (fun v => (v, (.int : LMonoTy)))

/-- The ground type of the datatype `d`, which is `d` with `int` at each parameter. The
    constructor applications of an obligation have this type. -/
def groundTy (d : LDatatype Unit) : LMonoTy :=
  .tcons d.name (d.typeArgs.map (fun _ => (.int : LMonoTy)))

/-- The field types of the constructor `c` of `d`, at the ground instance of `d`. A
    recursive occurrence `d αs` in a field also becomes `d int…`, because `αs` are the
    parameters of `d`. `addMutualBlock` enforces that uniformity. -/
def groundFieldTys (d : LDatatype Unit) (c : LConstr Unit) : List LMonoTy :=
  c.args.map (fun (_, τ) => instTy (groundInstantiation d) τ)

/-! ## Which blocks the properties accept -/

/-- Whether the `LContext.addMutualBlock` function of Strata accepts the block, from the
    real Core context. This is a *screen* and not a property. It is the same call that
    `ProgramGen.genDeclDatatype` uses to gate its emission, so no generated program holds a
    block that this call rejects.

    The screen must apply here, because nothing gates
    `DatatypeGen.genMutuallyRecursiveDatatypes`. That generator establishes `MutualADTWF`,
    which is weaker than the condition of `addMutualBlock`. Two causes occur, and only the
    first one is a defect in Strata:

    * **A field `field` and a field `field!`.** The two names collide with the naming scheme
      of Strata for an unsafe destructor, which adds `!` to the end of a name.
      `checkNoDerivedNameCollisions` is the property that states this.
    * **Two datatypes of the block share a constructor name.** This is a gap in the
      *generator*. `genConstructorsForAllTypes` gives the same `reserved` list to each
      datatype of the block, and it does not thread the list through the draws. Two
      datatypes can therefore declare a constructor, a field or a tester with one name, and
      `genBlockFactory` then reports "A function of name f already exists!". This is a
      screen and not an assertion, because the generator of this repository must fix it and
      Strata must not. A change that threads `reserved` through
      `genConstructorsForAllTypes` also changes the shape that the soundness proofs in
      `DatatypeGenProofs` use, so that change is later work. -/
def blockAccepted (block : MutualDatatype Unit) : Bool :=
  match @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams DatatypeGen.coreContext block with
  | .ok _ => true
  | .error _ => false

/-- Whether *each* constructor field of *each* datatype in the block holds no arrow type.
    This is the criterion of `validateDatatypesForSMT`, applied before the pipeline runs.
    That function throws for the whole block, from inside `emitDatatypes` and as an
    `IO.userError`. A block that fails the criterion therefore cannot get a partial test,
    and the suite skips the whole block.

    The check reads the *declared* field types and not the ground instance. `instTy` only
    replaces a type variable by `int`, so it can neither add nor remove an arrow. -/
def blockIsSmtEligible (block : MutualDatatype Unit) : Bool :=
  block.all fun d => d.constrs.all fun c => c.args.all fun (_, τ) => !τ.containsArrow

/-- Each name that the block uses: a datatype name, a constructor name, a tester name and a
    field name. The generator draws the variables of an obligation fresh against this list,
    so a local can never capture the name of a derived function. -/
def blockNames (block : MutualDatatype Unit) : List String :=
  block.flatMap fun d =>
    d.name :: d.constrs.flatMap fun c =>
      c.name.name :: c.testerName :: c.args.map (fun (f, _) => f.name)

/-- Whether `τ` mentions `bitvec 0`.

    **`bitvec 0` is legal in Core and illegal in SMT-LIB.** `pickBitvecWidth` draws a width
    with no bound, so a field of the type `bitvec 0` occurs. `Function.typeCheck` and
    `addMutualBlock` both accept such a field. The encoder then emits `(_ BitVec 0)`, and
    SMT-LIB 2.6 needs a positive index. cvc5 answers
    `Parse Error: Illegal bitvector size: 0`, and z3 answers
    `bit-vector size must be greater than zero`. *Each* obligation that mentions the
    datatype is therefore lost. `adtSolverAcceptsQuery` is the property that pins this
    defect. -/
def mentionsBv0 : LMonoTy → Bool
  | .bitvec w => w == 0
  | .ftvar _ => false
  | .tcons _ args => args.attach.any (fun a => mentionsBv0 a.1)
  termination_by t => SizeOf.sizeOf t
  decreasing_by cases a; term_by_mem

/-- The characters that a *simple symbol* of SMT-LIB 2.6 can hold: a letter, a digit, and
    one of `~ ! @ $ % ^ & * _ - + = < > . ? /`. Section 3.1 of the standard gives this rule.
    Each other character needs the quoted form `|…|`. -/
def smtSymbolExtraChars : List Char :=
  "~!@$%^&*_-+=<>.?/".toList

/-- The reserved words of SMT-LIB 2.6, which a bare symbol must not be. Section 3.1 of the
    standard gives the list. A Core identifier can be any of them. `_` is a legal Core name,
    and the generator gives it when `genIdentName` draws the single start character `_`. cvc5
    then reports `Expected SMT-LIBv2 symbol, got '_' (INDEX_TOK)`. -/
def smtReservedWords : List String :=
  ["_", "!", "as", "let", "exists", "forall", "match", "par",
   "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING"]

/-- Whether the encoder can emit `s` as a bare SMT-LIB symbol.

    **A legal Core identifier is not always such a symbol.** `remainingChars` is the alphabet
    that `genIdentName` draws from, and it is also the alphabet that the lexer of Core
    accepts. It holds `'`, which is *not* a simple-symbol character of SMT-LIB. The emitters
    for a datatype put a name into the output without a change. Therefore
    `datatype Qu { c'x(g'y : int), d() }`, which typechecks, gives

    ```
    (declare-datatype Qu ( (c'x (Qu..g'y Int)) (d)))
    ```

    and cvc5 stops with `Parse Error: … Error finding token`. The same holds for a *type
    parameter*, and there the difference is visible inside one line. Pipes quote a parameter
    where it occurs in a field type, but not in the `par` binder that introduces it:

    ```
    (par (vx' NK) ((b (U..r Int) (U..bz4! (U |vx'| NK))) …))
           ^^^ bare                            ^^^^^ quoted
    ```

    The formatter of the SMT dialect of DDM, `SMTDDM.termTypeToString`, prints a field type
    and it quotes. The datatype name, the list of `par` binders, and the names of a
    constructor and of a selector come from raw string interpolation, which does not quote.

    Of the special characters that `genIdentName` draws, `'` is the only character that breaks
    a bare symbol. The characters `. ? @ ! $ _` all pass *inside* a name. -/
def isSmtSafeSymbol (s : String) : Bool :=
  !s.isEmpty
  && !smtReservedWords.contains s
  && s.all (fun c => c.isAlphanum || smtSymbolExtraChars.contains c)

/-- Each symbol that the block gives to the emitted SMT-LIB: the names in `blockNames`, and
    the **type parameters** of each datatype, which occur in the list of `par` binders. The
    parameters must be in this list, because `genFreshName` draws them in the same way as each
    other name and they therefore hold the same characters. -/
def blockSymbols (block : MutualDatatype Unit) : List String :=
  blockNames block ++ block.flatMap (·.typeArgs)

/-- Whether a solver can receive each obligation of the block. Three conditions must hold: the
    block holds no arrow type, so that `validateDatatypesForSMT` does not throw; the block
    holds no `bitvec 0` field; and each emitted symbol is a bare SMT-LIB symbol.

    This is the screen that the two law properties apply, and it is *not* a claim about
    Strata. The last two conditions are the defects of the encoder that
    `adtSolverAcceptsQuery` reports. The screen keeps the claim about injectivity a claim
    about injectivity, and not a second report of a known defect. Without the screen, the
    solver refuses most of the obligations, and a real counterexample is then hard to see. -/
def blockIsSmtSafe (block : MutualDatatype Unit) : Bool :=
  blockIsSmtEligible block
  && block.all (fun d => d.constrs.all fun c => c.args.all fun (_, τ) => !mentionsBv0 τ)
  && (blockSymbols block).all isSmtSafeSymbol

/-! ## How the module builds the assertion program -/

/-- A free variable at a known type. -/
private def fv (n : String) (τ : LMonoTy) : Expression.Expr := .fvar () ⟨n, ()⟩ (some τ)

/-- `f a₁ … a_n` for an operator `f` that the factory names. Here `f` is always a datatype
    constructor, and `genBlockFactory` inside `addMutualBlock` registered it. The type
    annotation stays `none`: `LExpr.resolve` infers it by unification, and the *binding* that
    receives the application holds the ground result type. `letDecl` builds that binding, and
    the ground type is what gives the type parameters of the constructor their values. -/
private def opApp (name : String) (args : List Expression.Expr) : Expression.Expr :=
  args.foldl (fun acc a => .app () acc a) (.op () ⟨name, ()⟩ none)

/-- `var n : τ;`, which is a local with no initial value. It is the universally quantified
    variable of a law. Symbolic evaluation gives such a local a symbolic value with no
    constraint. -/
private def varDecl (n : String) (τ : LMonoTy) : Statement :=
  Statement.init ⟨n, ()⟩ (.forAll [] τ) .nondet .empty

/-- `var n : τ := e;`, which is a local that has an initial value and an explicit type.

    **The explicit type is what lets the encoder handle a polymorphic constructor.** A
    datatype can declare a type parameter that no constructor field mentions. `genParamsList`
    draws the parameters and the fields independently, and `addMutualBlock` allows such a
    phantom parameter. Unification from the argument types alone can therefore leave a
    parameter without a value. For `datatype D α { C(f : int) }`, the equality `C(x) = C(y)`
    holds at `D ?α`, and the encoder then reports
    `Unimplemented encoding for type var $__ty27` in place of a verdict on the law. A local
    that the code declares at `groundTy d` receives the application, and unification then
    gives each parameter the type `int`. The datatype tests of upstream also use this form, as
    in `var x : Option int; x := None();`. -/
private def letDecl (n : String) (τ : LMonoTy) (e : Expression.Expr) : Statement :=
  Statement.init ⟨n, ()⟩ (.forAll [] τ) (.det e) .empty

/-- `assume [l]: e;`. -/
private def assumeSt (l : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.assume l e .empty))

/-- `assert [l]: e;`. -/
private def assertSt (l : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.assert l e .empty))

/-- A procedure that has a body and no input, no output and no specification. It is the
    container for the obligations of one law. `noFilter := true` stops `FilterProcedures` from
    the removal of the procedure, because nothing calls it. -/
private def lawProc (name : String) (body : List Statement) : Decl :=
  .proc { header := { name := ⟨name, ()⟩, typeArgs := [], inputs := [], outputs := [],
                      noFilter := true }
          spec := { preconditions := [], postconditions := [] }
          body := .structured body } .empty

/-- The variable names for one obligation. There are `n` names. Each name is fresh for the
    block, and the names are pairwise different, because `indexedFreshName` gives a different
    length for each index. The last two names are the names of the two values that the
    obligation *builds*. The other names are the arguments of the constructors. -/
private def lawVarNames (block : MutualDatatype Unit) (n : Nat) : List String :=
  let base := DatatypeGen.maxNameLength (blockNames block)
  (List.range n).map (fun i => indexedFreshName base i)

/-- The obligation for injectivity of the constructor `c`, at index `ci`, of the datatype `d`,
    at index `di`. The result is `none` when `c` has no field, because injectivity is vacuous
    for a nullary constructor and a procedure with no obligation only makes the count of
    attempts larger.

    The result holds the declaration and the labels that it asserts. A caller can therefore
    map a verdict from the solver back to a field, and it does not build the names again. -/
def injObligation (block : MutualDatatype Unit) (di : Nat) (d : LDatatype Unit)
    (ci : Nat) (c : LConstr Unit) : Option (Decl × List String) :=
  let τs := groundFieldTys d c
  if τs.isEmpty then none
  else
    let k := τs.length
    let names := lawVarNames block (2 * k + 2)
    let xs := (names.take k).zip τs
    let ys := ((names.drop k).take k).zip τs
    let u := names[2 * k]!
    let v := names[2 * k + 1]!
    let dτ := groundTy d
    let mkApp := fun (vs : List (String × LMonoTy)) =>
      opApp c.name.name (vs.map (fun (n, τ) => fv n τ))
    let labels := (List.range k).map (fun i => s!"inj_{di}_{ci}_f{i}")
    let decls :=
      (xs ++ ys).map (fun (n, τ) => varDecl n τ)
      ++ [ letDecl u dτ (mkApp xs), letDecl v dτ (mkApp ys),
           assumeSt s!"inj_{di}_{ci}_h" (.eq () (fv u dτ) (fv v dτ)) ]
      ++ (labels.zip (xs.zip ys)).map (fun (l, (x, y)) =>
            assertSt l (.eq () (fv x.1 x.2) (fv y.1 y.2)))
    some (lawProc s!"inj_{di}_{ci}" decls, labels)

/-- The obligation for disjointness of the pair of constructors `(c₁, c₂)`, at the indices
    `(c₁i, c₂i)`, of the datatype `d` at index `di`. Unlike injectivity, this obligation is
    not vacuous for a nullary constructor, so no screen on the arity applies.

    The two constructors receive disjoint blocks of variables, first `x⃗` and then `y⃗`. The
    claim is therefore the strong claim that *no* pair of tuples of arguments makes the two
    applications equal, and not the special case where the two applications share their
    arguments. -/
def disjObligation (block : MutualDatatype Unit) (di : Nat) (d : LDatatype Unit)
    (c1i : Nat) (c1 : LConstr Unit) (c2i : Nat) (c2 : LConstr Unit) : Decl × String :=
  let τ1s := groundFieldTys d c1
  let τ2s := groundFieldTys d c2
  let n1 := τ1s.length
  let n2 := τ2s.length
  let names := lawVarNames block (n1 + n2 + 2)
  let xs := (names.take n1).zip τ1s
  let ys := ((names.drop n1).take n2).zip τ2s
  let u := names[n1 + n2]!
  let v := names[n1 + n2 + 1]!
  let dτ := groundTy d
  let mkApp := fun (nm : String) (vs : List (String × LMonoTy)) =>
    opApp nm (vs.map (fun (n, τ) => fv n τ))
  let label := s!"disj_{di}_{c1i}_{c2i}"
  let body :=
    (xs ++ ys).map (fun (n, τ) => varDecl n τ)
    ++ [ letDecl u dτ (mkApp c1.name.name xs), letDecl v dτ (mkApp c2.name.name ys),
         assertSt label (opApp "Bool.Not" [.eq () (fv u dτ) (fv v dτ)]) ]
  (lawProc s!"disj_{di}_{c1i}_{c2i}" body, label)

/-- The **tester form** of disjointness: for a symbolic `u : d`, no two different testers hold
    of `u`, which is `¬(isC₁ u ∧ isC₂ u)`.

    This form exists because the form with constructor applications **never reaches the
    solver**. The partial evaluator of Strata folds an equality of two applications of
    *different* constructors to `false` by itself. `symbolicEval` therefore turns
    `assert !(C x⃗ == D y⃗)` into the literal `assert true`, and the solver receives no
    question:

    ```
    procedure inj_0_0 () { … } else { assert [disj_0_0_1]: true; }
    ```

    That is a real and useful fact about the evaluator, but it is not a fact about the SMT
    encoding. A report of it as one is exactly the silent vacuity that this suite prevents.
    With a symbolic `u` and only its *testers* in the assertion, there is nothing to fold. The
    query reaches the solver, which must derive the exclusivity from the `declare-datatype`
    that it received. -/
def disjTesterObligation (block : MutualDatatype Unit) (di : Nat) (d : LDatatype Unit)
    (c1i : Nat) (c1 : LConstr Unit) (c2i : Nat) (c2 : LConstr Unit) : Decl × String :=
  let dτ := groundTy d
  let u := (lawVarNames block 1)[0]!
  let label := s!"disjT_{di}_{c1i}_{c2i}"
  let body :=
    [ varDecl u dτ,
      assertSt label
        (opApp "Bool.Not"
          [opApp "Bool.And" [opApp c1.testerName [fv u dτ], opApp c2.testerName [fv u dτ]]]) ]
  (lawProc s!"disjT_{di}_{c1i}_{c2i}" body, label)

/-- The pairs of different positions in a list, in the form `(i, xᵢ, j, xⱼ)` with `i < j`. The
    order inside a pair does not matter. -/
private def indexedPairs (xs : List α) : List (Nat × α × Nat × α) :=
  let ixs := xs.zipIdx
  ixs.flatMap fun (x, i) => ixs.filterMap fun (y, j) =>
    if i < j then some (i, x, j, y) else none

/-- Each obligation for one datatype of the block: injectivity for each constructor, and then
    both forms of disjointness for each pair of constructors. -/
def datatypeObligations (block : MutualDatatype Unit) (di : Nat) (d : LDatatype Unit) :
    List (Decl × List String) :=
  (d.constrs.zipIdx.filterMap (fun (c, ci) => injObligation block di d ci c))
  ++ (indexedPairs d.constrs).flatMap (fun (c1i, c1, c2i, c2) =>
        let (dA, lA) := disjObligation block di d c1i c1 c2i c2
        let (dT, lT) := disjTesterObligation block di d c1i c1 c2i c2
        [(dA, [lA]), (dT, [lT])])

/-- The whole law program for a block: the declaration of the block, and then one procedure for
    each law. The `List String` holds the labels of the `assert` statements, which are the
    proof obligations that a verification run must discharge. The function returns those
    labels, so a block that gives no obligation, such as a block with one nullary constructor,
    is visible as an empty list and not as a silent pass. -/
def lawProgram (block : MutualDatatype Unit) : Program × List String :=
  let obls := block.zipIdx.flatMap (fun (d, di) => datatypeObligations block di d)
  ({ decls := .type (.data block) .empty :: obls.map Prod.fst }, obls.flatMap Prod.snd)

/-- Which law the label of an obligation states. The prefix of the label gives the answer.

    The report keeps the three families separate, because different machinery discharges
    them. `inj` and `disjTester` reach the solver. The partial evaluator folds `disjApp`
    before the solver runs, as `disjTesterObligation` describes. -/
inductive LawKind where
  | inj | disjApp | disjTester
  deriving DecidableEq, Repr, Inhabited

/-- The law that a label states, or `none` when the label belongs to no law family. -/
def LawKind.ofLabel (l : String) : Option LawKind :=
  if l.startsWith "inj_" then some .inj
  else if l.startsWith "disjT_" then some .disjTester
  else if l.startsWith "disj_" then some .disjApp
  else none

/-- The name of a law family, for a report. -/
def LawKind.name : LawKind → String
  | .inj => "injectivity"
  | .disjApp => "disjointness (constructor form)"
  | .disjTester => "disjointness (tester form)"

/-! ## The companion that needs no solver: does the law program typecheck?

The solver property below needs `cvc5` or `z3`, so a flag enables it. This property needs
nothing, it runs in the default suite, and it screens the same programs. If
`Program.typeCheck` rejects an equality between two applications of a generated
constructor, then the solver property receives an ill-typed program and its result says
nothing. The property is also a claim on its own: a *derived* constructor is usable in an
ordinary equality at its ground instance. -/

/-- Whether the law program for `block` typechecks. The property is vacuously `true` for a
    block that gives no obligation. It has *no* screen on `blockIsSmtEligible`, because the
    type checker handles a field with an arrow type and only the SMT encoder does not.

    `blockAccepted` screens the block. A block that `addMutualBlock` refuses cannot give a
    well-typed program, and the reasons for a refusal belong to
    `checkNoDerivedNameCollisions` and to the gap in the generator that the documentation of
    that function names. They do not belong to this property, which is about the *law
    program*. -/
def checkLawProgramTypeChecks (block : MutualDatatype Unit) : Bool :=
  if !blockAccepted block then true
  else
    match Core.typeCheck Core.VerifyOptions.quiet (lawProgram block).fst with
    | .ok _ => true
    | .error _ => false

/-! ## The derived names of one datatype

For each datatype, `genBlockFactory` derives a constructor and a tester for each
constructor, and a *pair* of destructors for each field. `d..f` is the safe destructor,
which the tester guards, and `d..f!` is the unsafe destructor. `mkDestructorFunc` builds
the unsafe name by an added `!` at the end of the safe name, and nothing checks that the
result differs from each other derived name. -/

/-- Each function name that `genBlockFactory` derives from the datatype `d`, in the order of
    emission: the constructors, the testers, the safe destructors, and then the unsafe
    destructors. -/
def derivedNamesOf (d : LDatatype Unit) : List String :=
  d.constrs.map (·.name.name)
  ++ d.constrs.map (·.testerName)
  ++ d.constrs.flatMap (fun c => c.args.map (fun (f, _) => d.name ++ ".." ++ f.name))
  ++ d.constrs.flatMap (fun c => c.args.map (fun (f, _) => d.name ++ ".." ++ f.name ++ "!"))

/-- The derived names that the datatype `d` gives more than one time. -/
def derivedNameCollisions (d : LDatatype Unit) : List String :=
  let names := derivedNamesOf d
  (names.filter (fun n => (names.filter (· == n)).length > 1)).eraseDups

/-- **No datatype derives the same function name two times.**

    A field named `f!` and a field named `f` in one datatype both derive the name `d..f!`. The
    first derives it as its *safe* destructor, and the second as its *unsafe* one.
    `Factory.tryAddAll` then rejects the whole block with the message "A function of name
    `d..f!` already exists!". Both field names are legal Core identifiers, because `!` is in
    the identifier alphabet and the lexer of Core accepts it. This is therefore a legal
    datatype that no one can declare:

    ```
    datatype SZ3z I N { … (Y : …) … (Y! : …) … }
    ⇒ A function of name SZ3z..Y! already exists! Redefinitions are not allowed.
    ```

    The collision is silent at the site of the definition, and it appears as a rejection of
    the whole declaration. This is what makes the defect worth a property: the message names
    the derived function, and not the two fields that caused the collision. A fix builds the
    unsafe name from a character that the identifier alphabet does not hold, or it checks for
    the collision where the code makes the pair.

    The property speaks about one *datatype* and not about a block, so a collision across two
    datatypes cannot make it fail for another reason. `blockAccepted` describes that other
    collision. -/
def checkNoDerivedNameCollisions (block : MutualDatatype Unit) : Bool :=
  block.all (fun d => (derivedNameCollisions d).isEmpty)

/-- The smallest witness for the collision between `f` and `f!`: one datatype, one constructor
    and two fields. A `#guard` holds this constant, and the suite also searches for such a
    block at random. The build therefore pins the defect deterministically, because a random
    draw needs `genConstrArgs` to give both `f` and `f!`, and that is rare. -/
def bangFieldWitness : MutualDatatype Unit :=
  [ { name := "AdtBang"
      typeArgs := []
      constrs :=
        [ { name := ⟨"mkBang", ()⟩,
            args := [(⟨"f", ()⟩, .int), (⟨"f!", ()⟩, .int)],
            testerName := "AdtBang..isMkBang" } ]
      constrs_ne := by decide } ]

-- The two fields derive the name `AdtBang..f!` two times: as the *safe* destructor of `f!`,
-- and as the *unsafe* destructor of `f`.
#guard derivedNameCollisions bangFieldWitness[0]! == ["AdtBang..f!"]
#guard !checkNoDerivedNameCollisions bangFieldWitness

-- That collision is enough for Strata to refuse the whole declaration, so no one can declare
-- this legal Core datatype.
#guard !blockAccepted bangFieldWitness

-- The datatype with the field `f` alone is correct, which shows that the *pair* of fields is
-- the cause.
#guard blockAccepted
  [ { name := "AdtBang", typeArgs := [],
      constrs := [ { name := ⟨"mkBang", ()⟩, args := [(⟨"f", ()⟩, (.int : LMonoTy))],
                     testerName := "AdtBang..isMkBang" } ],
      constrs_ne := by decide } ]

/-! ## The second companion that needs no solver: the evaluator decides disjointness in
constructor form by itself

`disjTesterObligation` says why the form of disjointness that uses constructor applications
never reaches a solver. The partial evaluator of Strata folds `!(C x⃗ == D y⃗)` to `true`
while it evaluates the procedure symbolically. A property *asserts* that fact for two
reasons. The fact is a real guarantee about the evaluator, which knows that two constructors
are disjoint even for symbolic arguments. It also justifies the tester form: if the evaluator
stopped folding the constructor form, then `disjTester` would be the only remaining form and
the `disjApp` obligations would start to cost solver calls. -/

/-- The program of proof obligations that the symbolic evaluator of Strata gives, or `none`
    when the evaluator returns a diagnostic.

    This is the same call as `ProgramGen.UnprovenTransforms.symbolicObligations`. This module
    has its own copy, so that its dependencies stay `DatatypeGen` and Strata. The call uses
    `.quiet`, because the evaluator traces the whole list of obligations at `.normal` and
    above. A law program holds no loop, so the panic of the evaluator on a loop cannot happen
    here. -/
def symbolicObligations (p : Program) : Option Program :=
  match Core.toCoreProofObligationProgram Core.VerifyOptions.quiet p with
  | .ok (out, _) => some out
  | .error _ => none

mutual
/-- Each pair of a label and an expression from an `assert` in a statement, at any depth. -/
def stmtAsserts (s : Statement) : List (String × Expression.Expr) :=
  match s with
  | .cmd (.cmd (.assert l e _)) => [(l, e)]
  | .cmd _ => []
  | .block _ b _ => stmtsAsserts b
  | .ite _ t e _ => stmtsAsserts t ++ stmtsAsserts e
  | .loop _ _ _ b _ => stmtsAsserts b
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []

/-- `stmtAsserts` over a list of statements. -/
def stmtsAsserts (ss : List Statement) : List (String × Expression.Expr) :=
  match ss with
  | [] => []
  | s :: rest => stmtAsserts s ++ stmtsAsserts rest
end

/-- Each pair of a label and an expression from an `assert` in a procedure body of `p`. -/
def programAsserts (p : Program) : List (String × Expression.Expr) :=
  p.decls.flatMap fun d =>
    match d with
    | .proc proc _ =>
      match proc.body with
      | .structured ss => stmtsAsserts ss
      | _ => []
    | _ => []

/-- **Symbolic evaluation folds each disjointness obligation in constructor form to `true`,
    and each obligation in tester form reaches the solver.**

    Both halves matter. The first half is the guarantee about the evaluator. The second half
    guards the solver property against vacuity: if the evaluator also folded the tester form,
    then the solver would receive no question about disjointness and it would still report a
    pass.

    The property is vacuously `true` for a block that holds no pair of constructors, which is
    a block with one constructor. It is also vacuously `true` for a block that Strata refuses,
    and `checkLawProgramTypeChecks` uses the same screen for the same reason. The property is
    `false` when symbolic evaluation fails on a block that Strata *did* accept. -/
def checkDisjFoldsDuringSymEval (block : MutualDatatype Unit) : Bool :=
  if !blockAccepted block then true else
  match symbolicObligations (lawProgram block).fst with
  | none => false
  | some sp =>
    (programAsserts sp).all fun (l, e) =>
      match LawKind.ofLabel l with
      | some .disjApp => e == .const () (.boolConst true)
      | some .disjTester => e != .const () (.boolConst true)
      | _ => true

/-! ## The witness blocks for the two defects of the SMT encoder

These blocks are here and not in `AdtLawsSmt`, so that the `#guard` statements below stay
next to the screen that they exercise. Those statements need no solver. `AdtLawsSmt` runs
the same blocks against a live solver. -/

namespace AdtLawsWitnesses

/-- A block that has a `bitvec 0` field. Core accepts it, and SMT-LIB does not. -/
def bv0Block : MutualDatatype Unit :=
  [ { name := "AdtBv0"
      typeArgs := []
      constrs :=
        [ { name := ⟨"Bv0Zero", ()⟩, args := [(⟨"w", ()⟩, .bitvec 0)],
            testerName := "AdtBv0..isBv0Zero" },
          { name := ⟨"Bv0One", ()⟩, args := [], testerName := "AdtBv0..isBv0One" } ]
      constrs_ne := by decide } ]

/-- A block whose constructor names and field names hold `'`. They are legal Core identifiers,
    and they are not bare SMT-LIB symbols. -/
def quoteBlock : MutualDatatype Unit :=
  [ { name := "AdtQuote"
      typeArgs := []
      constrs :=
        [ { name := ⟨"q'c", ()⟩, args := [(⟨"q'f", ()⟩, .int)],
            testerName := "AdtQuote..isq'c" },
          { name := ⟨"qd", ()⟩, args := [], testerName := "AdtQuote..isqd" } ]
      constrs_ne := by decide } ]

end AdtLawsWitnesses

-- ── The two defects of the SMT encoder, pinned without a solver ───────
--
-- `AdtLawsSmt.adtSolverAcceptsQuery` is the property that reports these two defects, and it
-- needs a live solver. The classification under that property needs no solver, so the
-- statements below pin it. Each `#guard` says that the *screen* sees the defect, and this
-- keeps the screen and the reported cause in agreement.

-- A `bitvec 0` field holds no arrow and its names are correct, so only the screen on the width
-- rejects the block. Core accepts the block, because `Function.typeCheck` and
-- `addMutualBlock` both accept it, and `(_ BitVec 0)` is not legal SMT-LIB.
#guard blockAccepted AdtLawsWitnesses.bv0Block
#guard blockIsSmtEligible AdtLawsWitnesses.bv0Block
#guard !blockIsSmtSafe AdtLawsWitnesses.bv0Block

-- Core also accepts a `'` in a name, and such a name is not a bare SMT-LIB symbol.
#guard blockAccepted AdtLawsWitnesses.quoteBlock
#guard blockIsSmtEligible AdtLawsWitnesses.quoteBlock
#guard !blockIsSmtSafe AdtLawsWitnesses.quoteBlock
#guard !isSmtSafeSymbol "c'x"
-- `_` is a legal Core identifier and a *reserved word* of SMT-LIB.
#guard !isSmtSafeSymbol "_"
-- The other special characters that `genIdentName` draws are all correct.
#guard ["a.b", "a?b", "a@b", "a!b", "a$b", "a_b"].all isSmtSafeSymbol

end StrataGenerators.AdtLaws
