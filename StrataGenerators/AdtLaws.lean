import StrataGenerators.DatatypeGen
import StrataGenerators.ProgramGen.TestSupport
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.SMTEncoder

/-!
# The two laws every algebraic datatype satisfies: injectivity and disjointness

`DatatypeGen.genMutuallyRecursiveDatatypes` draws a random well-formed
`mutual … end` block of (possibly mutually recursive) algebraic datatypes. Any
such block denotes an *initial* algebra, so — exactly as in Software Foundations'
`Tactics` chapter, where the two facts appear as the `injection` and
`discriminate` tactics — its constructors must satisfy:

* **injectivity.** For each constructor `C` of arity `k ≥ 1`,
  `C x₁ … x_k = C y₁ … y_k → x₁ = y₁ ∧ … ∧ x_k = y_k`.
* **disjointness.** For each pair of *distinct* constructors `C ≠ D` of the same
  datatype, `C x_1 ... x_k ≠ D y_1 ... y_k`.

Uniformness is deliberately not covered here (`TypeFactory.addMutualBlock`
already checks it syntactically, via `checkConstructorArgsWF`).

Neither law is a claim about the generator: they are claims about **Strata's SMT
encoding of a datatype**. The generator's job is to supply the datatypes, and the
oracle is a real solver — `cvc5`/`z3` through the whole Core verification
pipeline (`Core.verify`), so the path under test is
typecheck → transform → symbolic eval → `SMT.Context.emitDatatypes` → solver.

## How a law becomes a proof obligation

There is no quantifier in the emitted assertion. Instead each universally
quantified variable becomes an *uninitialised local* — `var x : τ;`, i.e.
`Statement.init … .nondet` — which symbolic evaluation turns into an
unconstrained symbolic constant. So for a two-field constructor `C(a : int, b : bool)`
the injectivity obligation is the procedure

```
procedure inj_0_0 () {
  var x0 : int;  var x1 : bool;
  var y0 : int;  var y1 : bool;
  assume [h]: C(x0, x1) == C(y0, y1);
  assert [inj_0_0_f0]: x0 == y0;
  assert [inj_0_0_f1]: x1 == y1;
}
```

and the disjointness obligation for `C ≠ D` is

```
procedure disj_0_0_1 () {
  var x0 : int;  var x1 : bool;  var y0 : …;
  assert [disj_0_0_1]: !(C(x0, x1) == D(y0));
}
```

One `assert` per field rather than one conjunction, so a solver verdict names the
field that failed rather than only the constructor.

**The obligation labels carry indices, never generated names.** A generated
datatype name is an arbitrary Core identifier (`String.arbitrary` draws
non-alphanumeric characters), and an obligation label reaches SMT-LIB as a
symbol; a label built from a generated name would therefore risk turning a *law*
failure into an encoder failure, and the two must stay distinguishable. The
indices are positions in the block: `inj_{d}_{c}_f{i}` is field `i` of
constructor `c` of datatype `d`. The failing block is printed in full alongside.

## Which blocks are eligible

`validateDatatypesForSMT` rejects a datatype with a function-typed field
outright ("Function types cannot be represented in SMT-LIB datatypes"), and it
throws for the whole *block*, not for one obligation. A block holding an arrow
anywhere is therefore skipped before the solver is ever launched — and counted, so
the skip is visible rather than silent. `blockIsSmtEligible` is that screen.

Arrow-typed fields are common at the generator's default `maxSize` (an arrow is
one of three alternatives in `genArgTy` at every non-zero size), so the eligible
fraction is small there. Drawing at `maxSize := 0` makes `genArgTy` return
`genLeafTy`, whose range is base types / type parameters / recursive occurrences
only — never an arrow. `smtBlockSizeSchedule` mixes both, so the property gets
guaranteed non-vacuous coverage from size 0 while still seeing `Map`/`Sequence`-
and arrow-shaped draws (the latter as counted skips) from the larger sizes.

## Type parameters

A polymorphic datatype has no SMT sort until its parameters are given. Every type
parameter is instantiated with `int` (`groundInstantiation`), which is the
cheapest SMT-encodable choice and is enough: the laws are parametric, so an
instance at one ground type witnesses a failure at every other. The instantiation
is applied to field types only — the *declaration* keeps its parameters, since
that is what the pipeline must handle.
-/

open Lambda Core Imperative

namespace StrataGenerators.AdtLaws

/-! ## Monotype instantiation -/

mutual
/-- Substitute type variables per `σ`. Written here rather than reusing
    `LMonoTy.subst` because the latter takes Lambda's scoped `Subst` (a stack of
    hash maps with a well-formedness field), and all that is needed is a lookup in
    an association list. -/
def instTy (σ : List (String × LMonoTy)) : LMonoTy → LMonoTy
  | .ftvar v => (σ.lookup v).getD (.ftvar v)
  | .bitvec n => .bitvec n
  | .tcons n args => .tcons n (instTys σ args)

/-- `instTy` over a list. -/
def instTys (σ : List (String × LMonoTy)) : LMonoTys → LMonoTys
  | [] => []
  | t :: ts => instTy σ t :: instTys σ ts
end

/-- Instantiate every type parameter of `d` with `int`: the ground instance whose
    fields the assertions range over. -/
def groundInstantiation (d : LDatatype Unit) : List (String × LMonoTy) :=
  d.typeArgs.map (fun v => (v, (.int : LMonoTy)))

/-- The ground type of datatype `d`, i.e. `d` applied to `int` at each parameter —
    the type an obligation's constructor applications live at. -/
def groundTy (d : LDatatype Unit) : LMonoTy :=
  .tcons d.name (d.typeArgs.map (fun _ => (.int : LMonoTy)))

/-- The field types of constructor `c` of `d`, at `d`'s ground instance. A
    recursive occurrence `d αs` in a field becomes `d int…` too, since `αs` are
    exactly `d`'s parameters (uniformity, which `addMutualBlock` enforces). -/
def groundFieldTys (d : LDatatype Unit) (c : LConstr Unit) : List LMonoTy :=
  c.args.map (fun (_, τ) => instTy (groundInstantiation d) τ)

/-! ## Eligibility -/

/-- Whether Strata's own `LContext.addMutualBlock` accepts the block, starting
    from the real Core context. This is a *screen*, not a property: it is the same
    call `ProgramGen.genDeclDatatype` gates its emission on, so a block it rejects
    is one no generated program would ever contain.

    It has to be applied here because `DatatypeGen.genMutuallyRecursiveDatatypes`
    is gated on nothing — it establishes `MutualADTWF`, which is strictly weaker
    than what `addMutualBlock` demands. Two causes show up in practice, and only
    the first is a defect in Strata:

    * **`field` versus `field!`** — the two field names collide with Strata's own
      unsafe-destructor naming scheme, which appends `!`. See
      `checkNoDerivedNameCollisions`, the property that states it.
    * **a constructor name shared by two datatypes of the block** — a *generator*
      gap: `genConstructorsForAllTypes` passes the same `reserved` list to each
      datatype of the block rather than threading it, so two of them can declare a
      constructor (or field, or tester) of the same name, and `genBlockFactory`
      fails with "A function of name f already exists!". Measured at 1–3 of 40
      blocks. Screened rather than asserted, since it is this repo's generator to
      fix, not Strata's; threading `reserved` through
      `genConstructorsForAllTypes` would change the shape the soundness proofs in
      `DatatypeGenProofs` are stated against, so it is left as follow-up work.

    See `docs/adt-laws-alias-mutual-blocks.md`. -/
def blockAccepted (block : MutualDatatype Unit) : Bool :=
  match @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams DatatypeGen.coreContext block with
  | .ok _ => true
  | .error _ => false

/-- Whether *every* constructor field of *every* datatype in the block is
    arrow-free. This is `validateDatatypesForSMT`'s own criterion, applied ahead
    of time: that function throws for the whole block (from inside
    `emitDatatypes`, as an `IO.userError`), so an ineligible block cannot be
    partially tested and is skipped as a whole.

    Checked on the *declared* field types rather than the ground instance: `instTy`
    only replaces type variables with `int`, so it can neither introduce nor remove
    an arrow. -/
def blockIsSmtEligible (block : MutualDatatype Unit) : Bool :=
  block.all fun d => d.constrs.all fun c => c.args.all fun (_, τ) => !τ.containsArrow

/-- Every name the block occupies: datatype names, constructor names, tester
    names and field names. The variables of an obligation are drawn fresh against
    this list, so a local can never capture a derived function's name. -/
def blockNames (block : MutualDatatype Unit) : List String :=
  block.flatMap fun d =>
    d.name :: d.constrs.flatMap fun c =>
      c.name.name :: c.testerName :: c.args.map (fun (f, _) => f.name)

/-- Whether `τ` mentions `bitvec 0` anywhere.

    **`bitvec 0` is legal in Core and illegal in SMT-LIB.** `pickBitvecWidth`
    draws a width with no bound (repo issue #38), so a field of type `bitvec 0`
    occurs; `Function.typeCheck` and `addMutualBlock` both accept it, and the
    encoder emits `(_ BitVec 0)`, whose index SMT-LIB 2.6 requires to be positive.
    cvc5 answers `Parse Error: Illegal bitvector size: 0` and z3
    `bit-vector size must be greater than zero`, so *every* obligation mentioning
    the datatype is lost. See `adtSolverAcceptsQuery` for the property that pins
    this. -/
def mentionsBv0 : LMonoTy → Bool
  | .bitvec w => w == 0
  | .ftvar _ => false
  | .tcons _ args => args.attach.any (fun a => mentionsBv0 a.1)
  termination_by t => SizeOf.sizeOf t
  decreasing_by cases a; term_by_mem

/-- The characters an SMT-LIB 2.6 *simple symbol* may contain: letters, digits and
    `~ ! @ $ % ^ & * _ - + = < > . ? /` (§3.1 of the standard). Anything else has
    to be written in the pipe-quoted form `|…|`. -/
def smtSymbolExtraChars : List Char :=
  "~!@$%^&*_-+=<>.?/".toList

/-- The SMT-LIB 2.6 reserved words that a bare symbol may not be (§3.1). A Core
    identifier may be any of them: `_` in particular is a legal Core name and is
    what the generator produces when `genIdentName` draws the single start
    character `_`. cvc5 then reports
    `Expected SMT-LIBv2 symbol, got '_' (INDEX_TOK)`. -/
def smtReservedWords : List String :=
  ["_", "!", "as", "let", "exists", "forall", "match", "par",
   "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING"]

/-- Whether `s` is emittable as a bare SMT-LIB symbol.

    **A legal Core identifier need not be one.** `remainingChars` (the alphabet
    `genIdentName` draws from, and the one Core's lexer accepts) contains `'`,
    which is *not* an SMT-LIB simple-symbol character, and the datatype emitters
    interpolate a name verbatim — so `datatype Qu { c'x(g'y : int), d() }`, which
    typechecks, produces

    ```
    (declare-datatype Qu ( (c'x (Qu..g'y Int)) (d)))
    ```

    and cvc5 stops at `Parse Error: … Error finding token`. The same holds for a
    *type parameter*, where the inconsistency is visible within a single line: a
    parameter is pipe-quoted where it occurs in a field type but not in the `par`
    binder that introduces it —

    ```
    (par (vx' NK) ((b (U..r Int) (U..bz4! (U |vx'| NK))) …))
           ^^^ bare                            ^^^^^ quoted
    ```

    Field types are rendered through the DDM SMT dialect formatter
    (`SMTDDM.termTypeToString`), which quotes; the datatype name, the `par` binder
    list and the constructor/selector names are raw `s!"…"` interpolations
    (`DL/SMT/Solver.lean:244`, `DL/SMT/IncrementalSolver.lean:254`), which do not.

    Measured over the special characters `genIdentName` draws, `'` is the only
    offending character: `. ? @ ! $ _` all pass *inside* a name. -/
def isSmtSafeSymbol (s : String) : Bool :=
  !s.isEmpty
  && !smtReservedWords.contains s
  && s.all (fun c => c.isAlphanum || smtSymbolExtraChars.contains c)

/-- Every symbol the block contributes to the emitted SMT-LIB: the names of
    `blockNames` plus every datatype's **type parameters**, which appear in the
    `par` binder list. The parameters have to be included: they are drawn by the
    same `genFreshName` as every other name, so they carry the same characters. -/
def blockSymbols (block : MutualDatatype Unit) : List String :=
  blockNames block ++ block.flatMap (·.typeArgs)

/-- Whether every obligation the block generates can even be *put to* a solver:
    arrow-free (so `validateDatatypesForSMT` does not throw), no `bitvec 0` field,
    and every emitted symbol a bare SMT-LIB symbol.

    This is the screen the two law properties apply, and it is *not* a claim about
    Strata: the last two conjuncts are exactly the encoder defects
    `adtSolverAcceptsQuery` reports. Screening them out here is what keeps
    "injectivity holds" a statement about injectivity rather than a re-run of
    already-reported defects — the alternative is a property whose obligations are
    largely refused by the solver, where a real counterexample would be lost in the
    noise. -/
def blockIsSmtSafe (block : MutualDatatype Unit) : Bool :=
  blockIsSmtEligible block
  && block.all (fun d => d.constrs.all fun c => c.args.all fun (_, τ) => !mentionsBv0 τ)
  && (blockSymbols block).all isSmtSafeSymbol

/-! ## Building the assertion program -/

/-- A free variable at a known type. -/
private def fv (n : String) (τ : LMonoTy) : Expression.Expr := .fvar () ⟨n, ()⟩ (some τ)

/-- `f a₁ … a_n` for an operator `f` named in the factory — here always a
    datatype constructor, which `addMutualBlock`'s `genBlockFactory` has
    registered. The type annotation is left `none`: `LExpr.resolve` infers it by
    unification, and the *binding* the application is stored into carries the
    ground result type (see `letDecl`), which is what instantiates the
    constructor's type parameters. -/
private def opApp (name : String) (args : List Expression.Expr) : Expression.Expr :=
  args.foldl (fun acc a => .app () acc a) (.op () ⟨name, ()⟩ none)

/-- `var n : τ;` — an uninitialised local, i.e. the universally quantified
    variable of a law. Symbolic evaluation gives it an unconstrained symbolic
    value; the negative controls at the bottom of this file are what confirm that
    (with `assert x == y` on two such locals *failing*). -/
private def varDecl (n : String) (τ : LMonoTy) : Statement :=
  Statement.init ⟨n, ()⟩ (.forAll [] τ) .nondet .empty

/-- `var n : τ := e;` — a local *with* an initialiser and an explicit type.

    **The explicit type is what makes a polymorphic constructor encodable.** A
    datatype may declare a type parameter that no constructor field mentions
    (`genParamsList` draws the parameters independently of the fields, and
    `addMutualBlock` permits a phantom parameter), so unification from the argument
    types alone can leave a parameter undetermined: for
    `datatype D α { C(f : int) }`, `C(x) = C(y)` is an equality at `D ?α` and the
    encoder then reports `Unimplemented encoding for type var $__ty27` rather than
    a verdict on the law. Binding the application to a local declared at
    `groundTy d` pins every parameter to `int` by unification, which is also how
    upstream's own datatype tests are written (`var x : Option int; x := None();`). -/
private def letDecl (n : String) (τ : LMonoTy) (e : Expression.Expr) : Statement :=
  Statement.init ⟨n, ()⟩ (.forAll [] τ) (.det e) .empty

private def assumeSt (l : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.assume l e .empty))

private def assertSt (l : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.assert l e .empty))

/-- A body-only procedure with no inputs, outputs or spec: the container for one
    law's obligations. `noFilter := true` keeps `FilterProcedures` from pruning it
    (it is reachable from nothing). -/
private def lawProc (name : String) (body : List Statement) : Decl :=
  .proc { header := { name := ⟨name, ()⟩, typeArgs := [], inputs := [], outputs := [],
                      noFilter := true }
          spec := { preconditions := [], postconditions := [] }
          body := .structured body } .empty

/-- The variable names for one obligation: `n` names, all fresh for the block and
    pairwise distinct (distinct indices give distinct lengths — see
    `indexedFreshName`). The last two are the names of the two *constructed*
    values; the rest are the constructor arguments. -/
private def lawVarNames (block : MutualDatatype Unit) (n : Nat) : List String :=
  let base := DatatypeGen.maxNameLength (blockNames block)
  (List.range n).map (fun i => indexedFreshName base i)

/-- The injectivity obligation for constructor `c` (at index `ci`) of datatype `d`
    (at index `di`), or `none` when `c` has no fields — injectivity is vacuous for
    a nullary constructor, and an obligation-free procedure would only inflate the
    "attempted" count.

    Returns the declaration together with the labels it asserts, so the caller can
    map a solver verdict back to a field without re-deriving the naming scheme. -/
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

/-- The disjointness obligation for the constructor pair `(c₁, c₂)` at indices
    `(c₁i, c₂i)` of datatype `d` at index `di`. Unlike injectivity this is
    non-vacuous for nullary constructors, so no arity screen applies.

    The two constructors get disjoint variable blocks (`x⃗` then `y⃗`), so the
    claim is the strong one — *no* pair of argument tuples makes the two
    applications equal — rather than the special case of shared arguments. -/
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

/-- The **tester form** of disjointness: for a symbolic `u : d`, no two distinct
    testers hold of it — `¬(isC₁ u ∧ isC₂ u)`.

    This form exists because the application form above **never reaches the
    solver**. Strata's partial evaluator folds an equality of two applications of
    *distinct* constructors to `false` on its own, so `symbolicEval` turns
    `assert !(C x⃗ == D y⃗)` into the literal `assert true` and the solver is asked
    nothing:

    ```
    procedure inj_0_0 () { … } else { assert [disj_0_0_1]: true; }
    ```

    That is a genuine (and reassuring) fact about the evaluator, but it is not a
    fact about the SMT encoding, and reporting it as one would be exactly the kind
    of silent vacuity this suite exists to avoid. With `u` symbolic and only its
    *testers* mentioned, there is nothing to fold: the query reaches the solver,
    which has to derive exclusivity from the `declare-datatype` it was sent. -/
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

/-- Unordered pairs of distinct positions, as `(i, xᵢ, j, xⱼ)` with `i < j`. -/
private def indexedPairs (xs : List α) : List (Nat × α × Nat × α) :=
  let ixs := xs.zipIdx
  ixs.flatMap fun (x, i) => ixs.filterMap fun (y, j) =>
    if i < j then some (i, x, j, y) else none

/-- Every obligation for one datatype of the block: injectivity per constructor,
    then both disjointness forms per constructor pair. -/
def datatypeObligations (block : MutualDatatype Unit) (di : Nat) (d : LDatatype Unit) :
    List (Decl × List String) :=
  (d.constrs.zipIdx.filterMap (fun (c, ci) => injObligation block di d ci c))
  ++ (indexedPairs d.constrs).flatMap (fun (c1i, c1, c2i, c2) =>
        let (dA, lA) := disjObligation block di d c1i c1 c2i c2
        let (dT, lT) := disjTesterObligation block di d c1i c1 c2i c2
        [(dA, [lA]), (dT, [lT])])

/-- The whole law program for a block: the block's own declaration, then one
    procedure per law. The `List String` is the labels of the `assert`s, i.e. the
    proof obligations a verification run should be asked to discharge — returned so
    that a block contributing none (a block of one nullary constructor, say) is
    visible as an empty list rather than as a silent pass. -/
def lawProgram (block : MutualDatatype Unit) : Program × List String :=
  let obls := block.zipIdx.flatMap (fun (d, di) => datatypeObligations block di d)
  ({ decls := .type (.data block) .empty :: obls.map Prod.fst }, obls.flatMap Prod.snd)

/-- Which law an obligation label states, recovered from the label's prefix. The
    three families are reported separately, because they are discharged by
    different machinery: `inj` and `disjTester` reach the solver, while `disjApp`
    is folded by the partial evaluator before the solver is called (see
    `disjTesterObligation`). -/
inductive LawKind where
  | inj | disjApp | disjTester
  deriving DecidableEq, Repr, Inhabited

def LawKind.ofLabel (l : String) : Option LawKind :=
  if l.startsWith "inj_" then some .inj
  else if l.startsWith "disjT_" then some .disjTester
  else if l.startsWith "disj_" then some .disjApp
  else none

def LawKind.name : LawKind → String
  | .inj => "injectivity"
  | .disjApp => "disjointness (constructor form)"
  | .disjTester => "disjointness (tester form)"

/-! ## The non-solver companion: does the law program typecheck?

The solver property below needs `cvc5`/`z3`, so it is opt-in. This one needs
nothing, runs in the default suite, and screens the exact same programs: if
`Program.typeCheck` rejects an equality between two applications of a generated
constructor, then the solver property is being fed an ill-typed program and its
green result would be worthless. It is also a claim worth making on its own —
that a *derived* constructor is usable in an ordinary equality at its ground
instance. -/

/-- Whether the law program for `block` typechecks. Vacuously `true` for a block
    that contributes no obligation, and *not* screened on
    `blockIsSmtEligible` — the typechecker has no trouble with an arrow-typed
    field, only the SMT encoder does.

    Screened on `blockAccepted`: a block Strata's own `addMutualBlock` refuses
    cannot yield a well-typed program, and the reasons it refuses are the business
    of `checkNoDerivedNameCollisions` and of the generator gap that function's
    docstring names — not of this property, which is about the *law program*.
    Under that screen it held on 40/40 blocks at each of the four block sizes
    measured. -/
def checkLawProgramTypeChecks (block : MutualDatatype Unit) : Bool :=
  if !blockAccepted block then true
  else
    match Core.typeCheck Core.VerifyOptions.quiet (lawProgram block).fst with
    | .ok _ => true
    | .error _ => false

/-! ## The derived names of one datatype

`genBlockFactory` derives, for each datatype, a constructor and a tester per
constructor and a *pair* of destructors per field: `d..f` (safe, guarded by the
tester) and `d..f!` (unsafe). The unsafe name is the safe name with `!` appended
(`mkDestructorFunc`, `TypeFactory.lean:539`), and nothing checks that the result
does not collide with another derived name. -/

/-- Every function name `genBlockFactory` derives from datatype `d`, in emission
    order: constructors, testers, safe destructors, unsafe destructors. -/
def derivedNamesOf (d : LDatatype Unit) : List String :=
  d.constrs.map (·.name.name)
  ++ d.constrs.map (·.testerName)
  ++ d.constrs.flatMap (fun c => c.args.map (fun (f, _) => d.name ++ ".." ++ f.name))
  ++ d.constrs.flatMap (fun c => c.args.map (fun (f, _) => d.name ++ ".." ++ f.name ++ "!"))

/-- The derived names datatype `d` produces more than once. -/
def derivedNameCollisions (d : LDatatype Unit) : List String :=
  let names := derivedNamesOf d
  (names.filter (fun n => (names.filter (· == n)).length > 1)).eraseDups

/-- **No datatype derives the same function name twice.**

    **FAILS honestly.** A field named `f!` and a field named `f` in the same
    datatype both derive the name `d..f!` — the first as its *safe* destructor, the
    second as its *unsafe* one — and `Factory.tryAddAll` then rejects the whole
    block with "A function of name `d..f!` already exists!". Both field names are
    legal Core identifiers (`!` is in the identifier alphabet, and Core's own lexer
    accepts it), so this is a legal datatype that cannot be declared:

    ```
    datatype SZ3z I N { … (Y : …) … (Y! : …) … }
    ⇒ A function of name SZ3z..Y! already exists! Redefinitions are not allowed.
    ```

    The collision is silent at the definition site and surfaces as a
    whole-declaration rejection, which is what makes it worth pinning: the message
    names the derived function, not the two fields responsible. A fix is to mint the
    unsafe name from a character the identifier alphabet excludes, or to check for
    the clash where the pair is generated.

    Stated per *datatype* rather than per block, so that a cross-datatype collision
    — which is this repo's generator to fix, see `blockAccepted` — cannot make it
    red for an unrelated reason. -/
def checkNoDerivedNameCollisions (block : MutualDatatype Unit) : Bool :=
  block.all (fun d => (derivedNameCollisions d).isEmpty)

/-- The minimal witness for the `f`/`f!` collision: one datatype, one constructor,
    two fields. Kept as a `#guard`ed constant as well as being searched for at
    random, so the defect is pinned deterministically at build time — the random
    search needs a draw in which `genConstrArgs` happens to produce both `f` and
    `f!`, which is rare. -/
def bangFieldWitness : MutualDatatype Unit :=
  [ { name := "AdtBang"
      typeArgs := []
      constrs :=
        [ { name := ⟨"mkBang", ()⟩,
            args := [(⟨"f", ()⟩, .int), (⟨"f!", ()⟩, .int)],
            testerName := "AdtBang..isMkBang" } ]
      constrs_ne := by decide } ]

-- The two fields derive the name `AdtBang..f!` twice: as `f!`'s *safe* destructor
-- and as `f`'s *unsafe* one.
#guard derivedNameCollisions bangFieldWitness[0]! == ["AdtBang..f!"]
#guard !checkNoDerivedNameCollisions bangFieldWitness

-- And that is enough for Strata to refuse the whole declaration, so a legal Core
-- datatype cannot be declared at all.
#guard !blockAccepted bangFieldWitness

-- The `f`-only datatype is fine, which is what makes the *pair* the cause.
#guard blockAccepted
  [ { name := "AdtBang", typeArgs := [],
      constrs := [ { name := ⟨"mkBang", ()⟩, args := [(⟨"f", ()⟩, (.int : LMonoTy))],
                     testerName := "AdtBang..isMkBang" } ],
      constrs_ne := by decide } ]

/-! ## The other non-solver companion: the evaluator decides constructor-form
disjointness on its own

`disjTesterObligation` explains why the constructor-application form of
disjointness never reaches a solver: Strata's partial evaluator folds
`!(C x⃗ == D y⃗)` to `true` while symbolically evaluating the procedure. That fact
is worth *asserting* rather than only noting, for two reasons: it is a real
guarantee about the evaluator (it knows constructors are disjoint even with
symbolic arguments), and it is what justifies the tester form's existence — if
this property ever went red, `disjTester` would be the only remaining form and the
`disjApp` obligations would silently start costing solver calls. -/

/-- The proof-obligation program Strata's symbolic evaluator produces, or `none`
    on a diagnostic. Same call as `ProgramGen.UnprovenTransforms.symbolicObligations`
    (inlined rather than imported to keep this module's dependencies to
    `DatatypeGen` plus Strata); `.quiet`, since the evaluator `dbg_trace`s the whole
    obligation list at `.normal` or above. A law program holds no loop, so the
    evaluator's loop panic is unreachable here. -/
def symbolicObligations (p : Program) : Option Program :=
  match Core.toCoreProofObligationProgram Core.VerifyOptions.quiet p with
  | .ok (out, _) => some out
  | .error _ => none

mutual
/-- Every `(label, expression)` of an `assert` in a statement, at any depth. -/
def stmtAsserts (s : Statement) : List (String × Expression.Expr) :=
  match s with
  | .cmd (.cmd (.assert l e _)) => [(l, e)]
  | .cmd _ => []
  | .block _ b _ => stmtsAsserts b
  | .ite _ t e _ => stmtsAsserts t ++ stmtsAsserts e
  | .loop _ _ _ b _ => stmtsAsserts b
  | .exit _ _ | .funcDecl _ _ | .typeDecl _ _ => []

/-- `stmtAsserts` over a statement list. -/
def stmtsAsserts (ss : List Statement) : List (String × Expression.Expr) :=
  match ss with
  | [] => []
  | s :: rest => stmtAsserts s ++ stmtsAsserts rest
end

/-- Every `(label, expression)` of an `assert` in any procedure body of `p`. -/
def programAsserts (p : Program) : List (String × Expression.Expr) :=
  p.decls.flatMap fun d =>
    match d with
    | .proc proc _ =>
      match proc.body with
      | .structured ss => stmtsAsserts ss
      | _ => []
    | _ => []

/-- **Every constructor-form disjointness obligation is folded to `true` by
    symbolic evaluation, and every tester-form one survives it.** Both halves
    matter: the first is the guarantee about the evaluator, the second is the
    non-vacuity guard for the solver property — were the tester form folded too,
    the solver would be asked nothing at all about disjointness and would still
    report green.

    Vacuously `true` for a block with no constructor pair (one constructor) and for
    a block Strata refuses (same screen, and for the same reason, as
    `checkLawProgramTypeChecks`); `false` if symbolic evaluation fails on a block
    that *was* accepted. -/
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

/-! ## Witness blocks for the two SMT-encoder defects

Held here rather than in `AdtLawsSmt` so that the `#guard`s below — which need no
solver — sit next to the screen they exercise. `AdtLawsSmt` runs the same blocks
against a live solver. -/

namespace AdtLawsWitnesses

/-- A block with a `bitvec 0` field: legal Core, illegal SMT-LIB. -/
def bv0Block : MutualDatatype Unit :=
  [ { name := "AdtBv0"
      typeArgs := []
      constrs :=
        [ { name := ⟨"Bv0Zero", ()⟩, args := [(⟨"w", ()⟩, .bitvec 0)],
            testerName := "AdtBv0..isBv0Zero" },
          { name := ⟨"Bv0One", ()⟩, args := [], testerName := "AdtBv0..isBv0One" } ]
      constrs_ne := by decide } ]

/-- A block whose constructor and field names contain `'`: legal Core identifiers
    that are not bare SMT-LIB symbols. -/
def quoteBlock : MutualDatatype Unit :=
  [ { name := "AdtQuote"
      typeArgs := []
      constrs :=
        [ { name := ⟨"q'c", ()⟩, args := [(⟨"q'f", ()⟩, .int)],
            testerName := "AdtQuote..isq'c" },
          { name := ⟨"qd", ()⟩, args := [], testerName := "AdtQuote..isqd" } ]
      constrs_ne := by decide } ]

end AdtLawsWitnesses

-- ── The two SMT-encoder defects, pinned without a solver ──────────────
--
-- `AdtLawsSmt.adtSolverAcceptsQuery` is the property that reports these, and it
-- needs a live solver. The classification they rest on does not, so it is pinned
-- here: each `#guard` says that the *screen* sees the defect, which is what keeps
-- the screen and the reported cause in step.

-- A `bitvec 0` field is arrow-free and its names are fine, so only the width screen
-- rejects it — and it is Core-legal (`Function.typeCheck` and `addMutualBlock` both
-- accept it) while `(_ BitVec 0)` is not SMT-LIB.
#guard blockAccepted AdtLawsWitnesses.bv0Block
#guard blockIsSmtEligible AdtLawsWitnesses.bv0Block
#guard !blockIsSmtSafe AdtLawsWitnesses.bv0Block

-- A `'` in a name is likewise Core-legal and not a bare SMT-LIB symbol.
#guard blockAccepted AdtLawsWitnesses.quoteBlock
#guard blockIsSmtEligible AdtLawsWitnesses.quoteBlock
#guard !blockIsSmtSafe AdtLawsWitnesses.quoteBlock
#guard !isSmtSafeSymbol "c'x"
-- `_` is a legal Core identifier and an SMT-LIB *reserved word*.
#guard !isSmtSafeSymbol "_"
-- The other special characters `genIdentName` draws are all fine.
#guard ["a.b", "a?b", "a@b", "a!b", "a$b", "a_b"].all isSmtSafeSymbol

end StrataGenerators.AdtLaws
