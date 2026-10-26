import StrataGenerators.ProcedureHasTypeAGen.Shrink
import StrataGenerators.FunctionHasTypeAGen.Shrink
import Strata.Languages.Core.ProgramType

open Lambda Core Imperative
-- The statement-level shrinker (`shrinkStmtsList`, recursing into `shrinkCmd` and
-- `shrinkLExpr`), the size measure `sizeStmts`, and the ambient typing context
-- `stmtCheckContext` come from the statement test support (reached transitively via
-- the procedure shrinker).
open StrataGenerators.Stmt.TestSupport
-- The procedure-level shrinker (`shrinkProcCandidates`, `sizeProc`) and the
-- structured-body accessor `bodyStmts`.
open StrataGenerators.Procedure.TestSupport

/-!
# Well-typed shrinker for generated whole programs

The top of the shrinker tower: expression (`shrinkLExpr`) → command (`shrinkCmd`)
→ statement (`shrinkStmtsList`) → function (`shrinkFuncCandidates`) / procedure
(`shrinkProcCandidates`) → **program** (here). Nothing below is re-implemented:
every declaration body is reduced by handing it to the shrinker that already
exists for its kind. The only new reductions are the ones that no such shrinker can express, which are a
removal of a whole declaration, and a reduction of the data at the level of a declaration. That data is the
arity of a type constructor, the body of an alias, the list of the constructors of a datatype block, and the
list of the expressions of a `distinct` declaration.

## The oracle

Candidates are filtered by `progTypeChecks`, i.e. Strata's own whole-program
typechecker `Core.Program.typeCheck`, run in the same standard ambient context
(`stmtCheckContext`: the full `Core.Factory` and `Core.KnownTypes`) every other
harness in this repo uses. So every program this shrinker yields is well-typed by
the algorithm.

Checking the *whole program* rather than tracking per-declaration contexts is what
licenses the wholesale delegation, and it decides several obligations for free:

- **Global name distinctness.** `ProgramHasType'` requires `P.getNames.Nodup`, and
  the checker enforces it incrementally (`C.idents.addListWithError decl.names`).
  This is a case where the filter does real work rather than confirming an
  invariant: `shrinkFunc` renames a function to the canonical `"f"` (see "What is
  preserved, and what is not"), which can collide with a declaration already called
  `f`. Such a candidate is rejected here. The filter also makes distinctness
  unconditional on input that did not have it.
- **Later declarations keep resolving.** Dropping a `type`/`func` declaration can
  orphan a later declaration that referenced it (an alias body mentioning a
  dropped abstract type, a procedure body calling a dropped procedure). That is
  precisely what the whole-program check catches, so such candidates are filtered
  out rather than prevented by local reasoning.
- **Axiom clauses stay Boolean.** `Program.typeCheck`'s `.ax` branch rejects any
  axiom whose resolved type is not `bool`, so an axiom body reduced to a
  non-Boolean subterm is filtered out. Axiom bodies may therefore be shrunk
  freely with `shrinkLExpr`.

## What is preserved, and what is not

The **program's declaration order is preserved**: candidates are sublists or
in-place replacements, never reorderings. So a shrunk program reads against the
original positionally, which is what makes a reduced counterexample legible.

**One declaration kind is renamed.** `shrinkFunc`'s last reduction family
(`FunctionHasTypeAGen/Roundtrip.lean`) rewrites a function's name to the single
canonical `"f"`:

```lean
let shrinkName := if f.name.name.length > 1 then [{ f with name := ⟨"f", ()⟩ }] else []
```

`shrinkDecl` reaches it for a top-level `.func` and for each member of a
`.recFuncBlock`. Therefore those are the only declarations whose name can change, and it can change to `"f"`
only. Each other kind keeps its name. `shrinkTypeDecl` rebuilds a type declaration with a record update,
`shrinkProcCandidates` changes no header, and the case for an `.ax` and for a `.distinct` declaration keeps
the name. A name can still *disappear*, through a removal of a declaration, of a datatype, or of a
constructor with its tester and its accessors, and such a removal is not a rename.

`Nodup` is therefore **not** maintained by an absence of renaming; it is maintained
by the oracle. `progTypeChecks` runs `Core.Program.typeCheck`, which enforces
`P.getNames.Nodup` incrementally, so a rename to `"f"` that collides with a
declaration whose name is already `f` fails that check. So does a rename that leaves a caller of
the old name, since the reference then fails to resolve. Both are rejections rather
than things the candidate generator avoids proposing.

Nothing else is preserved, and per the requirement nothing else needs to be: a
shrunk program need not declare the same names, expose the same procedure
signatures, or have "the same type" in any sense. In particular a declaration may
disappear entirely, a procedure may lose its body and contract, a datatype block
may lose constructors, and the whole program may shrink to `{ decls := [] }` (the
empty program, which typechecks).

-/

namespace StrataGenerators.Program.TestSupport

-- ── Well-typedness oracle ─────────────────────────────────────────────────

/-- Whether Strata's whole-program typechecker accepts `p` in the standard Core
    ambient context (`Core.Factory` + `Core.KnownTypes`). This is the shrinker's
    single invariant: every candidate it emits satisfies it.

    Unlike the procedure-level oracle, no enclosing program has to be threaded in:
    `Program.typeCheck` passes `p` to itself, so a `call` resolves against exactly
    the declaration list the candidate has. Dropping a called procedure therefore
    invalidates its callers *and is caught here*, which is what makes the
    declaration-drop family safe. -/
def progTypeChecks (p : Program) : Bool :=
  match Program.typeCheck stmtCheckContext TEnv.default p with
  | .ok _ => true
  | .error _ => false

/-- The typechecker's diagnostic for a rejected program, newlines flattened
    (`none` when it is accepted). For harness reporting: when a counterexample
    cannot be shrunk because the oracle rejects every candidate, this says why. -/
def progTypeCheckError (p : Program) : Option String :=
  match Program.typeCheck stmtCheckContext TEnv.default p with
  | .ok _ => none
  | .error e => some ((toString e.message).replace "\n" " ")

-- ── Size measure ──────────────────────────────────────────────────────────

/-- Size of a type declaration: an abstract type is its arity, an alias its body's
    type size, a datatype block the sum over its datatypes of (1 per constructor +
    each constructor argument's type size). Every reduction below strictly
    decreases the relevant summand. -/
def sizeTypeDecl : TypeDecl → Nat
  | .con tc => tc.numargs
  | .syn ts => sizeTy ts.type
  | .data block =>
    (block.map fun d =>
      (d.constrs.map fun c => 1 + (c.args.map (fun a => sizeTy a.2)).sum).sum).sum

/-- Size of the parts of one declaration this shrinker can reduce. Names are
    excluded (they are never rewritten), so a candidate that drops or reduces
    *anything* is strictly smaller. -/
def sizeDecl : Decl → Nat
  | .type t _ => sizeTypeDecl t
  | .ax a _ => a.e.sizeOf
  | .lemma l _ => l.e.sizeOf
  | .distinct _ es _ => (es.map (·.sizeOf)).sum
  | .proc p _ => sizeProc p
  | .func f _ => sizeFunc f
  | .recFuncBlock fs _ => (fs.map sizeFunc).sum

/-- Total reducible size of a program: one per declaration (so *dropping* a
    declaration is strictly smaller than emptying it) plus each declaration's own
    reducible size. This is the measure both the one-step shrinker and the greedy
    minimizer strictly decrease, which is what makes the latter terminate. -/
def sizeProgram (p : Program) : Nat :=
  (p.decls.map fun d => 1 + sizeDecl d).sum

-- ── Declaration-level candidate families ──────────────────────────────────
-- One family per declaration kind, each producing *raw* candidates: ill-typed
-- ones are removed by the whole-program filter in `shrinkProgramDecls`.

/-- Replace a datatype's constructor list, discharging `LDatatype.constrs_ne` from
    the decidable non-emptiness check (`none` when the list is empty, which the
    field forbids). Every datatype reduction below goes through this, so no
    candidate can break that side condition. It is an obligation at the level of Lean, and not at the level of
    the checker, so no filter over the oracle could rescue it. -/
private def setConstrs (d : LDatatype Unit) (cs : List (LConstr Unit)) :
    Option (LDatatype Unit) :=
  if h : cs.length != 0 then some { d with constrs := cs, constrs_ne := h } else none

/-- Structurally smaller type declarations.

    * For an **abstract type**, drop one type parameter, which lowers the arity.
      This is a genuine program-level reduction: the arity is what later alias
      bodies and datatype constructor arguments must apply the constructor at, so
      any candidate that leaves such a use behind is rejected by the oracle.
    * For an **alias**, reduce the body with `shrinkTy`, and compute
      `typeArgs` again from the free variables of the reduced body, as
      `ProgramGen.mkAliasDecl` does. That second computation is what keeps
      `TEnv.addTypeAlias`'s guards (`typeArgs.Nodup`, `freeVars ⊆ typeArgs`, no
      phantom args) satisfied by construction; simply keeping the old `typeArgs`
      would strand a phantom argument whenever the reduction dropped a variable.
    * For a **datatype block**, drop one whole datatype from the block, drop
      one constructor from one datatype, or drop one argument from one
      constructor. A block must stay non-empty (`.data []` is not a legal
      declaration) and each datatype must keep at least one constructor
      (`LDatatype.constrs_ne`), so those two drops are guarded rather than
      offered blindly. Dropping the *last* constructor of a datatype is instead
      expressed by dropping that datatype.

      Dropping a constructor can make a datatype uninhabited, and dropping a
      datatype leaves a recursive reference to it from another datatype of the block. `addMutualBlock` inside
      the oracle rejects both cases, so neither of them needs a check here. -/
def shrinkTypeDecl : TypeDecl → List TypeDecl
  | .con tc => (fun ps => .con { tc with params := ps }) <$> dropEach tc.params
  | .syn ts =>
    (fun τ => .syn { ts with type := τ, typeArgs := (LMonoTy.freeVars τ).uniq })
      <$> shrinkTy ts.type
  | .data block =>
    -- Drop one datatype (only when at least two remain, so the block stays non-empty).
    let dropDatatype :=
      if block.length ≤ 1 then []
      else (fun b => TypeDecl.data b) <$> dropEach block
    -- Reduce one datatype in place: drop a constructor, or drop a constructor argument.
    let shrinkOne := block.zipIdx.flatMap fun (d, i) =>
      -- `setConstrs` keeps `constrs_ne`, so dropping the *last* constructor is
      -- silently declined here; that reduction is expressed as a datatype drop.
      let dropConstr : List (LDatatype Unit) :=
        (dropEach d.constrs).filterMap (setConstrs d)
      let dropArg : List (LDatatype Unit) :=
        d.constrs.zipIdx.flatMap fun (c, j) =>
          (dropEach c.args).filterMap fun as =>
            setConstrs d (d.constrs.set j { c with args := as })
      (fun d' => TypeDecl.data (block.set i d')) <$> (dropConstr ++ dropArg)
    dropDatatype ++ shrinkOne

/-- Whether each free variable of each `requires` clause of `f` is a formal parameter of `f`, which is to say
    that the function has no precondition that names a variable outside its own parameters.

    The checker rejects such a clause: `function f0() : bool requires y == 0 { true }`, where `y` is declared
    nowhere, does not type check.

    Such a program is easy to build. The reduction of `shrinkFunc` that drops an input removes the formal
    parameter that a clause names, and `genFunction` often emits a clause that names a formal
    parameter. The shrinkers therefore refuse such a candidate.
    This condition, together with the "each clause is Boolean" half, is enforced by
    `funcWellFormed`, the single filter every function-shrinking family runs.

    It stays a named definition because the whole-program shrinker diagnostic
    (`programShrinkDiagnostic`) asserts it over emitted candidates *independently* of
    the filter that enforces it: should the check ever be absent from
    `funcWellFormed`, the diagnostic catches it rather than silently passing. -/
def funcPreconditionsScoped (f : Function) : Bool :=
  let formals := f.inputs.keys.map (·.name)
  f.preconditions.all fun pc =>
    (LExpr.collectFvarNames pc.expr).all fun x => x.name ∈ formals

/-- Structurally smaller `distinct` expression lists: drop one expression, or
    reduce one with `shrinkLExpr`. A `distinct` over zero or one expression is
    still legal (the spec's `DeclHasType'.distinct` quantifies over the list, so
    the empty list is vacuously fine), which is why dropping is unguarded. -/
def shrinkDistinctExprs (es : List Expression.Expr) : List (List Expression.Expr) :=
  dropEach es
    ++ es.zipIdx.flatMap fun (e, i) => (es.set i ·) <$> shrinkLExpr e

/-- Structurally smaller replacements for one declaration, **largest reduction
    first** (which is what makes the greedy `minimizeProgramWhile` converge
    quickly). Each kind delegates to the shrinker that already exists for its
    contents:

    * `.type` → `shrinkTypeDecl` (above);
    * `.ax` and `.lemma` → `shrinkLExpr` on the proposition;
    * `.distinct` → `shrinkDistinctExprs`;
    * `.proc` → `shrinkProcCandidates` (drop the body, drop/reduce a contract
      clause, or reduce the body with `shrinkStmtsList`, and it holds the header fixed);
    * `.func` → `shrinkFunc`, the *signature-reducing* function reducer (drop the
      body or measure, drop or reduce a `requires` clause, drop an input or type-arg,
      reduce an input/output type, shorten the name), filtered by `funcWellFormed`.
      That filter is what keeps a surviving `requires` clause Boolean and scoped to
      the formal parameters. No check of Strata gives that condition, which
      `funcPreconditionsScoped` records, and the family of `shrinkFunc` that drops an input would otherwise
      break it. The narrower
      signature-preserving `shrinkFuncCandidates` backing the `Shrinkable Function`
      instance is deliberately not used here: at program level there is no reason to
      pin a declared function's signature, and the wider reducer is what lets a
      counterexample shrink to a constant function. Names *are* shortened by
      `shrinkFunc`; a rename that collided with another declaration would break
      `getNames.Nodup` and is rejected by the oracle.
    * `.recFuncBlock` → drop one function from the block (only while two or more
      remain, because `DeclHasType'.recFuncBlock` needs a block that is not empty), or reduce
      one with `shrinkFunc` (same filter).

    Candidates are raw; the whole-program filter in `shrinkProgramDecls` removes
    the ill-typed ones. -/
def shrinkDecl : Decl → List Decl
  | .type t md => (.type · md) <$> shrinkTypeDecl t
  | .ax a md => (fun e => .ax { a with e := e } md) <$> shrinkLExpr a.e
  | .lemma l md => (fun e => .lemma { l with e := e } md) <$> shrinkLExpr l.e
  | .distinct n es md => (.distinct n · md) <$> shrinkDistinctExprs es
  | .proc p md => (.proc · md) <$> shrinkProcCandidates p
  | .func f md => (.func · md) <$> (shrinkFunc f).filter funcWellFormed
  | .recFuncBlock fs md =>
    let dropOne := if fs.length ≤ 1 then [] else (Decl.recFuncBlock · md) <$> dropEach fs
    let shrinkOne := fs.zipIdx.flatMap fun (f, i) =>
      (fun f' => Decl.recFuncBlock (fs.set i f') md) <$> (shrinkFunc f).filter funcWellFormed
    dropOne ++ shrinkOne

-- ── Declarations the checker rejects ──────────────────────────────────────
-- Three shapes of a declaration that the checker rejects in any program: a `distinct` with a free
-- variable, a function with a measure and no body, and an unknown operator. `cutGaps` drops them.

mutual
/-- Whether an expression mentions a free variable. A top-level `distinct` element
    of the form `.fvar () ⟨v, ()⟩ (some τ)` names a variable no legal Core program
    can bind, which is what the algorithm rejects. (`genDistinctAssertion` does not
    produce this shape.) -/
def exprHasFvar : Expression.Expr → Bool
  | .fvar _ _ _ => true
  | .op _ _ _ | .const _ _ | .bvar _ _ => false
  | .app _ a b | .eq _ a b => exprHasFvar a || exprHasFvar b
  | .ite _ a b c => exprHasFvar a || exprHasFvar b || exprHasFvar c
  | .abs _ _ _ b => exprHasFvar b
  | .quant _ _ _ _ t b => exprHasFvar t || exprHasFvar b
/-- Whether an expression applies an operator that neither the ambient factory nor
    the enclosing program defines. `declared` is the program's own function names
    (`programFuncNames`): an `.op` at one of those resolves even though the factory
    does not hold it. That is exactly how a generated `distinct` names the
    constants its step declares, so omitting `declared` would report a
    false `unknown-op` on every such program. -/
def exprHasUnknownOp (declared : List String) : Expression.Expr → Bool
  | .op _ o _ => !(o.name ∈ stmtCheckContext.functions) && !(declared.contains o.name)
  | .const _ _ | .bvar _ _ | .fvar _ _ _ => false
  | .app _ a b | .eq _ a b => exprHasUnknownOp declared a || exprHasUnknownOp declared b
  | .ite _ a b c =>
    exprHasUnknownOp declared a || exprHasUnknownOp declared b || exprHasUnknownOp declared c
  | .abs _ _ _ b => exprHasUnknownOp declared b
  | .quant _ _ _ _ t b => exprHasUnknownOp declared t || exprHasUnknownOp declared b
end

/-- Whether a function has a `decreases` clause and no body. The specification permits that shape, because
    `FuncHasType'` makes each of the two fields optional on its own, and `Function.typeCheck` rejects the
    combination. -/
def funcMeasureNoBody (f : Function) : Bool := f.measure.isSome && f.body.isNone

/-- Whether a declaration carries a measure-without-body function. -/
def declMeasureNoBody : Decl → Bool
  | .func f _ => funcMeasureNoBody f
  | .recFuncBlock fs _ => fs.any funcMeasureNoBody
  | _ => false

/-- Whether a declaration is a `distinct` that names a free variable, which is a global that the program does
    not declare. -/
def declDistinctFvar : Decl → Bool
  | .distinct _ es _ => es.any exprHasFvar
  | _ => false

/-- Whether a declaration's expressions apply an operator outside `Core.Factory`.
    Procedure bodies are *not* inspected: a body's operators are drawn from
    `coreMonoOps` (all of which the factory defines), so there is nothing to find,
    and a full traversal of a procedure body would be dead weight. -/
def declUnknownOp (declared : List String) : Decl → Bool
  | .ax a _ => exprHasUnknownOp declared a.e
  | .distinct _ es _ => es.any (exprHasUnknownOp declared)
  | .func f _ => (f.body.map (exprHasUnknownOp declared)).getD false
  | .recFuncBlock fs _ =>
    fs.any fun f => (f.body.map (exprHasUnknownOp declared)).getD false
  | _ => false

/-- Every function name the program declares itself: top-level functions (including
    the 0-ary constants a `distinct` step emits) and `recFuncBlock` members. -/
def programFuncNames (p : Program) : List String :=
  p.decls.flatMap fun
    | .func f _ => [f.name.name]
    | .recFuncBlock fs _ => fs.map (·.name.name)
    | _ => []

/-- Whether a declaration has one of the three shapes on whose account `Program.typeCheck` rejects
    the whole program. -/
def declHasGap (declared : List String) (d : Decl) : Bool :=
  declDistinctFvar d || declMeasureNoBody d || declUnknownOp declared d

/-- Whether `Program.typeCheck` rejects `p` because a function, an axiom or a `distinct`
    declaration is typed at a generated type variable that nothing declares: a polymorphic
    instance whose type nothing fixes, such as `Sequence.empty` with no annotation. The
    specification accepts such an open instance, and the checker refuses it. The cause is read
    off the checker's message. -/
def hasOpenInstanceRejection (p : Program) : Bool :=
  match progTypeCheckError p with
  | some msg => (msg.splitOn openInstanceRejectionMsg).length > 1
  | none => false

/-- A one-line annotation explaining a program's typechecker status, or `""` when it
    typechecks (so a passing sample renders unadorned). Three cases:

    * accepted → `""`;
    * rejected for an expected reason → the tags of `expectedRejectionCauses`;
    * rejected for any other reason → the verbatim diagnostic, since that rejection is a
      failure.

    Shared by the Plausible `Repr` and the Tyche panel renderer so a counterexample
    reads identically in both views. -/
def programStatusNote (p : Program) : String :=
  if progTypeChecks p then ""
  else match expectedRejectionCauses p with
    | [] =>
      let msg := (progTypeCheckError p).getD "(no diagnostic)"
      s!"\n  -- typechecker-rejected, UNEXPECTED cause: {msg}"
    | cs => s!"\n  -- typechecker-rejected, expected: {" ".intercalate cs}"

-- ── The whole-program check predicates (shared by both harnesses) ─────────

/-- **Whole-program typechecker completeness.** The checker accepts every generated program,
    except one it may reject by `checkerRejectionExpected`. -/
def checkProgramTypeCheckerComplete (p : Program) : Bool :=
  progTypeChecks p || checkerRejectionExpected p

/-! ### Whole-program invariants of a *well-typed* program

The four properties below are all conditional on the input typechecking, so they
are vacuous on a draw the checker rejects and are genuine claims on the rest. Unlike
`checkProgramTypeCheckerComplete`, a counterexample to any of them is
*shrinkable*: the failure does not depend on the oracle rejecting the program, so
smaller candidates are available and the minimizer reports a minimal witness.

`checkProgramTypeCheckIdempotent` is the sharpest of the four: it bears on roughly 1
in 500 single-function draws, and its docstring records the cause. -/

/-- **`getNames` distinctness.** `ProgramHasType'`'s first conjunct is
    `P.getNames.Nodup`, which the checker enforces incrementally via
    `C.idents.addListWithError decl.names`. So a program the checker accepts must
    have distinct names. This property states that fact against `getNames` directly, which is
    the flat namespace the spec quantifies over rather than the checker's
    incremental fold. -/
def checkProgramNamesNodup (p : Program) : Bool :=
  !progTypeChecks p || p.getNames.eraseDups.length == p.getNames.length

/-- **Typechecking is idempotent.** `Program.typeCheck` returns a *rewritten*
    program (each declaration resolved and annotated), so the natural claim is that
    re-checking the output succeeds: the checker's output is in its own input
    language.

    A generated program rarely reaches this property. Each program that does reach it holds a polymorphic
    function whose type parameter appears *only* as the annotation of a binder of a quantifier in the body, as in

        function s<a>() : bool { exists q : a :: false }

    which is accepted, but whose returned form is not: the body's annotation comes
    back freshened to `$__ty1` while `typeArgs` comes back `[]`, so the output trips
    the declaration-level guard ("body contains undeclared type variables") that the
    input passed. The rename-back step (`FunctionType.lean`)
    is driven by the type variables of the *signature*, and a type parameter that
    occurs only in a body binder annotation is invisible to it.

    The property states the claim and does not weaken it, by the same convention as
    `checkProgramTypeCheckerComplete`. Unlike that one, a counterexample here *is*
    shrinkable, since the divergence is in the checker's output rather than in its
    verdict on the input. -/
def checkProgramTypeCheckIdempotent (p : Program) : Bool :=
  match Program.typeCheck stmtCheckContext TEnv.default p with
  | .error _ => true
  | .ok (p', _) => progTypeChecks p'

/-- **`stripMetaData` preserves typeability.** Metadata is source-location and
    annotation bookkeeping, so erasing it cannot change whether a program is
    well-typed. -/
def checkProgramStripMetaPreservesTyping (p : Program) : Bool :=
  !progTypeChecks p || progTypeChecks p.stripMetaData

/-- **`eraseTypes` preserves typeability.** Erasing the type annotations of every
    declaration leaves a program `resolve` must re-infer from scratch; since the
    annotations were derivable in the first place, the erased program should still
    check. The program-level analogue of the expression-level resolve-after-erase
    property (`checkResolveAfterErase`).

    A rejection of the erased program caused by an open polymorphic instance is excused:
    erasing `Sequence.length(Sequence.empty<int>()) == 0` leaves no annotation that fixes the
    element type. -/
def checkProgramEraseTypesPreservesTyping (p : Program) : Bool :=
  !progTypeChecks p || progTypeChecks p.eraseTypes || hasOpenInstanceRejection p.eraseTypes

-- ── Program-level shrinker ────────────────────────────────────────────────

/-- Structurally smaller, **well-typed** candidate programs, largest reduction
    first. Four families:

    1. **Remove every declaration that `declHasGap` flags at once.** Read below.
    2. **Keep a prefix**, and drop the whole suffix of the declarations.
    3. **Drop one declaration**.
    4. **replace one declaration by a smaller one** (`shrinkDecl`).

    Declaration order is preserved throughout (every family is a sublist or an
    in-place replacement, and never a change of the order). `progTypeChecks` filters each candidate, and it
    also filters each candidate of the family that drops a declaration.

    Filtering the drop family too may look redundant, but removing a declaration
    genuinely *can* break the survivors: a later declaration may reference the
    dropped one, and a dropped procedure may still be called. It matters for a
    second reason as well: on ill-typed input, which does occur (the known
    rejection causes), a family that drops a declaration with no filter would emit a smaller
    program that is *not* well typed, and it would break the contract of the shrinker. With the filter, the
    guarantee holds always: each program that this shrinker gives type checks, at each input.

    **Why families 1 and 2 exist.** With only the one-at-a-time families, a program
    carrying *two independent* gap-bearing declarations cannot be reduced at all:
    dropping either one leaves the other, so no single-step candidate passes the
    filter, and the minimizer returns the input untouched even though a much
    smaller well-typed program is one step away. A draw with two different gaps is not rare. The first family,
    which removes each declaration that holds a gap, removes each of
    them in one step, and prefix truncation (family 2) is a cheap generic escape
    from the same class of local minimum, so a program whose *only* obstacle is
    gap-bearing declarations minimizes rather than stalling. -/
def shrinkProgramDecls (p : Program) : List Program :=
  let mk (ds : List Decl) : Program := { decls := ds }
  -- Family 1: drop every gap-bearing declaration in one step (offered only when
  -- that is a genuine reduction, i.e. at least one such declaration exists).
  let cutGaps :=
    let declared := programFuncNames p
    if p.decls.any (declHasGap declared) then
      [mk (p.decls.filter (!declHasGap declared ·))] else []
  -- Family 2: every proper prefix, longest first (so the smallest reduction that
  -- still fails is preferred among prefixes).
  let prefixes :=
    ((List.range p.decls.length).reverse.map fun n => mk (p.decls.take n))
  let candidates :=
    cutGaps ++ prefixes
      ++ (mk <$> dropEach p.decls)
      ++ p.decls.zipIdx.flatMap fun (d, i) => (fun d' => mk (p.decls.set i d')) <$> shrinkDecl d
  candidates.filter progTypeChecks

/-- Well-typed structural shrinks of a program: every candidate that is strictly
    smaller by `sizeProgram` and still accepted by `Program.typeCheck`. This is the
    one-step candidate list the `Shrinkable` typeclass expects; the greedy
    minimizer that reports a *smallest* counterexample is `minimizeProgramWhile`. -/
def shrinkProgram (p : Program) : List Program :=
  (shrinkProgramDecls p).filter fun c => sizeProgram c < sizeProgram p

/-- Greedily minimize `p` while the predicate `fails` still holds, mirroring
    `minimizeProcsWhile`: repeatedly take the first strictly-smaller well-typed
    candidate that still satisfies `fails`, until no candidate does or the fuel
    runs out.

    Because a candidate is kept only when it still fails, the result is always a
    genuine counterexample. Each candidate also passed `progTypeChecks`, so the result is always well typed.
    Read the module docstring for what that guarantee gives and does not give about well-formedness. If the
    failure depends on something that no smaller
    well-typed program reproduces, this returns `p` unchanged: never a wrong answer,
    just an unshrunk one. -/
partial def minimizeProgramWhile (fails : Program → Bool) (fuel : Nat)
    (p : Program) : Program :=
  match fuel with
  | 0 => p
  | fuel + 1 =>
    match (shrinkProgram p).filter fails with
    | [] => p
    | c :: _ => minimizeProgramWhile fails fuel c

/-- Minimize a counterexample to a `Bool` program property: the smallest
    well-typed program this shrinker can reach on which `check` still returns
    `false`. Returns `p` untouched when `check` already holds (nothing to
    minimize). -/
def minimizeProgramCounterexample (check : Program → Bool) (fuel : Nat := 200)
    (p : Program) : Program :=
  if check p then p else minimizeProgramWhile (fun c => !check c) fuel p

-- ── Sanity guards ─────────────────────────────────────────────────────────

section Guards

private def trueExpr : Expression.Expr := .const () (.boolConst true)

/-- An abstract type of arity 2: `type G _ _;`. -/
private def conDecl : Decl :=
  .type (.con { name := "G", params := ["_", "_"] }) .empty

/-- A trivially true axiom. -/
private def axDecl : Decl := .ax { name := "a0", e := trueExpr } .empty

/-- A `distinct` declaration over two closed integer literals. It holds no free variable, so the algorithm
    accepts it, and it does not accept a generated one. -/
private def distinctDecl : Decl :=
  .distinct ⟨"d0", ()⟩ [.const () (.intConst 0), .const () (.intConst 1)] .empty

/-- The alias `type S x := Sequence x;`, whose `typeArgs` field comes from the body, as `mkAliasDecl`
    computes it. -/
private def synDecl : Decl :=
  .type (.syn { name := "S", typeArgs := ["x"], type := .seq (.ftvar "x") }) .empty

/-- A minimal well-typed procedure: no formals, no contract, empty body. -/
private def procDecl : Decl :=
  .proc { header := { name := ⟨"P0", ()⟩, typeArgs := [], inputs := [], outputs := [],
                      lemmas := [] }
          spec := { preconditions := [], postconditions := [] }
          body := .structured [] } .empty

/-- A constant function `function f() : bool { true }`. -/
private def funcDecl : Decl :=
  .func { name := ⟨"f0", ()⟩, typeArgs := [], inputs := [], output := .bool,
          body := some trueExpr } .empty

private def prog (ds : List Decl) : Program := { decls := ds }

-- The oracle accepts the empty program and each hand-built declaration, so it is
-- not vacuously rejecting everything.
#guard progTypeChecks Program.init == true
#guard progTypeChecks (prog [conDecl]) == true
#guard progTypeChecks (prog [synDecl]) == true
#guard progTypeChecks (prog [axDecl]) == true
#guard progTypeChecks (prog [distinctDecl]) == true
#guard progTypeChecks (prog [procDecl]) == true
#guard progTypeChecks (prog [funcDecl]) == true
#guard progTypeChecks (prog [conDecl, synDecl, axDecl, distinctDecl, procDecl, funcDecl]) == true

/-- The alias `type R := $__ty0;`, whose body names a reserved type constructor. -/
private def reservedSynDecl : Decl :=
  .type (.syn { name := "R", typeArgs := [], type := .tcons "$__ty0" [] }) .empty

-- The checker rejects a written type that names a reserved type constructor, and the oracles tag
-- that rejection as a reserved name.
#guard progTypeChecks (prog [reservedSynDecl]) == false
#guard expectedRejectionCauses (prog [reservedSynDecl]) == ["reserved-name"]

/-- A datatype `D` with one constructor `mkD` whose tester is named `$__tyIsMkD`, a reserved
    name. -/
private def reservedTesterBlock : MutualDatatype Unit :=
  [ { name := "D", typeArgs := []
      constrs := [ { name := ⟨"mkD", ()⟩, args := [], testerName := "$__tyIsMkD" } ]
      constrs_ne := by decide } ]

/-- A recursive block of `r0` and `r1`, where `r0` has a parameter named `r1`. -/
private def clashRecBlockDecl : Decl :=
  .recFuncBlock
    [ { name := ⟨"r0", ()⟩, typeArgs := [], isRecursive := true,
        inputs := [(⟨"r1", ()⟩, .int)], output := .bool, body := some trueExpr },
      { name := ⟨"r1", ()⟩, typeArgs := [], isRecursive := true, inputs := [],
        output := .bool, body := some trueExpr } ] .empty

/-- The function `function f1(x : $__ty0) : bool { true }`, whose signature names a reserved
    type constructor. -/
private def reservedSigFuncDecl : Decl :=
  .func { name := ⟨"f1", ()⟩, typeArgs := [], inputs := [(⟨"x", ()⟩, .tcons "$__ty0" [])],
          output := .bool, body := some trueExpr } .empty

-- The checker rejects each of these programs, and the oracles tag the cause.
#guard progTypeChecks (prog [.type (.data reservedTesterBlock) .empty]) == false
#guard expectedRejectionCauses (prog [.type (.data reservedTesterBlock) .empty]) ==
  ["reserved-name"]
#guard progTypeChecks (prog [clashRecBlockDecl]) == false
#guard expectedRejectionCauses (prog [clashRecBlockDecl]) == ["var-function-clash"]
#guard progTypeChecks (prog [reservedSigFuncDecl]) == false
#guard expectedRejectionCauses (prog [reservedSigFuncDecl]) == ["reserved-name"]

-- The empty program is fully minimal: nothing smaller to propose.
#guard sizeProgram Program.init == 0
#guard (shrinkProgram Program.init).isEmpty == true

-- THE HEADLINE INVARIANT: every candidate program typechecks, on a program
-- exercising all six declaration kinds the generator can emit.
private def mixed : Program :=
  prog [conDecl, synDecl, axDecl, distinctDecl, procDecl, funcDecl]
#guard (shrinkProgram mixed).all progTypeChecks == true
-- ...and every candidate is strictly smaller, so the minimizer terminates.
#guard (shrinkProgram mixed).all (fun c => sizeProgram c < sizeProgram mixed) == true
-- Undo `shrinkFunc`'s rename, so a candidate's names can be compared against the
-- input's positionally. `mixed` declares no `f`, so this is unambiguous here.
private def unrenameF (n : String) : String := if n == "f" then "f0" else n

-- **Declaration order is preserved, and `f0 -> f` is the only rewrite.** Both halves
-- in one check: after undoing the rename, every candidate's name list is a *sublist*
-- of the input's. Being a sublist forbids reordering, forbids introducing a name,
-- The input holds one declaration named `f0`, so being a sublist also forbids two declarations that both take
-- the name `f`. A check of the membership in a set tests none of those three conditions, because it accepts
-- both `["f0", "G"]` and `["G", "f", "f"]`.
#guard (shrinkProgram mixed).all
  (fun c => (c.decls.map (fun d => unrenameF d.name.name)).isSublist
              (mixed.decls.map (fun d => d.name.name))) == true

-- The rename is genuinely *reachable*, not merely tolerated by the check above:
-- some candidate rewrites `f0` to `f`. This is the pin the module doc's "one
-- declaration kind is renamed" rests on. Its predecessor ("no declaration is ever
-- renamed") drifted unnoticed precisely because every guard here only *permitted*
-- the rename, so nothing failed when the prose stopped matching the code.
#guard (shrinkProgram mixed).any
  (fun c => (c.decls.map (fun d => d.name.name)).contains "f") == true

-- Dropping a declaration is offered: a property that fails on every program
-- minimizes all the way to the empty program.
#guard minimizeProgramWhile (fun _ => true) 100 mixed == Program.init
-- A property that holds everywhere leaves the input untouched.
#guard minimizeProgramCounterexample (fun _ => true) 100 mixed == mixed
-- Prefix truncation is offered: every proper prefix of `mixed` typechecks, so all
-- six of them, of the lengths 0 up to 5, are candidates. They do not come from that family only, because a
-- removal of the last declaration also gives the prefix of the length 5. Therefore this guard is about
-- reachability, and not about the family that gives each candidate.
#guard (List.range mixed.decls.length).all
  (fun n => (shrinkProgram mixed).any (fun c => c.decls == mixed.decls.take n)) == true

-- Per-kind reductions are all non-empty on the mixed program, i.e. every
-- declaration kind really is reducible (not just droppable).
#guard (shrinkDecl conDecl).isEmpty == false        -- arity 2 → 1
#guard (shrinkDecl synDecl).isEmpty == false        -- Sequence x → x
#guard (shrinkDecl distinctDecl).isEmpty == false   -- drop/reduce an element
#guard (shrinkDecl funcDecl).isEmpty == false       -- drop the body
-- `axDecl`'s body is already a leaf and `procDecl` is already empty, so those two
-- can be dropped and cannot be reduced. These guards therefore give the guard above real content.
#guard (shrinkDecl axDecl).isEmpty == true
#guard (shrinkDecl procDecl).isEmpty == true

-- Abstract-type arity really drops (and `shrinkTypeDecl` keeps the name).
#guard (shrinkTypeDecl (.con { name := "G", params := ["_", "_"] })) ==
  [.con { name := "G", params := ["_"] }, .con { name := "G", params := ["_"] }]

-- An alias reduction re-derives `typeArgs` from the reduced body, so a variable
-- the reduction dropped does not linger as a phantom argument.
#guard (shrinkTypeDecl (.syn { name := "S", typeArgs := ["x"],
                               type := .seq (.ftvar "x") })).any
  (fun | .syn ts => ts.typeArgs == ["x"] && ts.type == .ftvar "x" | _ => false) == true
#guard (shrinkTypeDecl (.syn { name := "S", typeArgs := ["x"],
                               type := .seq .int })).any
  (fun | .syn ts => ts.typeArgs == [] | _ => false) == true

-- A datatype block: a two-constructor enum reduces (constructor drop) but a
-- one-constructor one does not (`constrs_ne` forbids the empty list, and the
-- block cannot become `.data []`).
private def enumDT : LDatatype Unit :=
  { name := "E", typeArgs := [],
    constrs := [{ name := ⟨"C1", ()⟩, args := [] }, { name := ⟨"C2", ()⟩, args := [] }],
    constrs_ne := by simp }
private def unitDT : LDatatype Unit :=
  { name := "U", typeArgs := [], constrs := [{ name := ⟨"C0", ()⟩, args := [] }],
    constrs_ne := by simp }

#guard (shrinkTypeDecl (.data [enumDT])).isEmpty == false
#guard (shrinkTypeDecl (.data [unitDT])).isEmpty == true
-- Every datatype candidate keeps the block non-empty and every datatype's
-- constructor list of each datatype is not empty. Those are the two side conditions about well-formedness
-- that no run of the oracle could rescue, because each of them is at the level of a *type* in Lean, and not at
-- the level of the checker.
#guard (shrinkTypeDecl (.data [enumDT, unitDT])).all
  (fun | .data b => !b.isEmpty && b.all (fun d => !d.constrs.isEmpty) | _ => true) == true
-- A constructor argument is droppable too.
private def argDT : LDatatype Unit :=
  { name := "A", typeArgs := [],
    constrs := [{ name := ⟨"Mk", ()⟩, args := [(⟨"f1", ()⟩, .int), (⟨"f2", ()⟩, .bool)] }],
    constrs_ne := by simp }
#guard (shrinkTypeDecl (.data [argDT])).any
  (fun | .data [d] => d.constrs.any (fun c => c.args.length == 1) | _ => false) == true

-- ── `requires` clauses: reduced, and never stranded ───────────────────────
-- A removal of the input that a `requires` clause names gives a clause that names a variable which nothing
-- declares. The checker rejects that program, and `funcWellFormed`'s precondition conditions keep the
-- shrinker from proposing it. These guards pin both directions: the clause is reducible, and never stranded.

/-- The function `function f0(y : int) : bool requires y == 0 { true }`. Its precondition names the formal
    parameter, which is the shape that `genFunction` gives. -/
private def precondFunc : Function :=
  { name := ⟨"f0", ()⟩, typeArgs := [], inputs := [(⟨"y", ()⟩, .int)], output := .bool,
    body := some trueExpr,
    preconditions := [{ expr := .eq () (.fvar () ⟨"y", ()⟩ (some .int))
                                       (.const () (.intConst 0)), md := () }] }
/-- The same function with the input removed, so its `requires` clause names a variable that nothing
    declares. -/
private def precondFuncDangling : Function := { precondFunc with inputs := [] }

-- The checker rejects that form: a precondition may name no variable outside the formals.
#guard progTypeChecks (prog [.func precondFuncDangling .empty]) == false
-- `funcWellFormed` is what rejects it (its precondition-scoping condition).
#guard funcWellFormed precondFunc == true
#guard funcWellFormed precondFuncDangling == false
#guard funcPreconditionsScoped precondFunc == true
#guard funcPreconditionsScoped precondFuncDangling == false
-- The filter also rejects a clause whose type is not `bool`, which is the other condition that no check of
-- Strata gives.
#guard funcWellFormed { precondFunc with
  preconditions := [{ expr := .const () (.intConst 0), md := () }] } == false

-- THE PRECONDITION REDUCTIONS. Dropping the clause is offered...
#guard (shrinkDecl (.func precondFunc .empty)).any
  (fun | .func f _ => f.preconditions.isEmpty | _ => false) == true

-- ...and reducing it *in place* is offered whenever a subterm is itself Boolean.
-- `requires (y == 0) == true` reduces to `requires y == 0`.
private def nestedPrecondFunc : Function :=
  { precondFunc with
    preconditions := [{ expr := .eq () (.eq () (.fvar () ⟨"y", ()⟩ (some .int))
                                               (.const () (.intConst 0)))
                                       trueExpr, md := () }] }
#guard funcWellFormed nestedPrecondFunc == true
#guard (shrinkDecl (.func nestedPrecondFunc .empty)).any
  (fun | .func f _ => f.preconditions == precondFunc.preconditions | _ => false) == true

-- Conversely, `requires y == 0` offers NO in-place reduction, and that is correct
-- rather than a miss: both subterms of `y == 0` are `int`, so every reduct is
-- non-Boolean and `funcWellFormed` rightly rejects it. Dropping remains available.
#guard (shrinkDecl (.func precondFunc .empty)).all
  (fun | .func f _ => f.preconditions.isEmpty
                        || f.preconditions == precondFunc.preconditions
        | _ => true) == true

-- Every candidate is strictly smaller by `sizeFunc`, which is what lets it past the
-- strict-decrease test in `shrinkWhile` and `shrinkProgram`. This is exactly why
-- `sizeFunc` has to count preconditions: a measure blind to them would rate a
-- clause-reduced candidate equal to its parent, and the test would discard it.
#guard sizeFunc { precondFunc with preconditions := [] } < sizeFunc precondFunc
#guard (shrinkDecl (.func precondFunc .empty)).all
  (fun | .func f _ => sizeFunc f < sizeFunc precondFunc | _ => true) == true

-- ...while stranding the clause is NOT offered: the input-drop reduction is
-- declined for as long as the clause mentions the formal.
#guard (shrinkDecl (.func precondFunc .empty)).any
  (fun | .func f _ => f.inputs.isEmpty && !f.preconditions.isEmpty | _ => false) == false
#guard (shrinkProgram (prog [.func precondFunc .empty])).all
  (fun c => c.decls.all fun | .func f _ => funcPreconditionsScoped f | _ => true) == true
-- Dropping the input IS reachable in two steps (drop the clause, then the input),
-- which is why the drop-clause family is ordered first.
#guard (shrinkDecl (.func { precondFunc with preconditions := [] } .empty)).any
  (fun | .func f _ => f.inputs.isEmpty | _ => false) == true

-- The signature-preserving instance shrinker reduces the clause too, and holds the
-- signature fixed while doing so.
#guard (shrinkFuncWellFormed precondFunc).any (fun f => f.preconditions.isEmpty) == true
#guard (shrinkFuncWellFormed precondFunc).all
  (fun f => f.inputs == precondFunc.inputs && f.output == precondFunc.output
              && f.typeArgs == precondFunc.typeArgs) == true
#guard (shrinkFuncWellFormed precondFunc).all funcWellFormed == true

-- The checker rejects a `decreases` clause on a function that is not recursive, so a non-recursive
-- function with a measure is rejected whatever its inputs.
private def measureFunc : Function :=
  { precondFunc with preconditions := [], measure := some (.fvar () ⟨"y", ()⟩ (some .int)) }
#guard progTypeChecks (prog [.func measureFunc .empty]) == false
#guard progTypeChecks (prog [.func { measureFunc with inputs := [] } .empty]) == false

-- A `recFuncBlock` never shrinks to the empty block (the spec forbids it).
private def recBlock : Decl :=
  .recFuncBlock [{ name := ⟨"g0", ()⟩, typeArgs := [], inputs := [], output := .bool,
                   body := some trueExpr },
                 { name := ⟨"g1", ()⟩, typeArgs := [], inputs := [], output := .bool,
                   body := some trueExpr }] .empty
#guard (shrinkDecl recBlock).all
  (fun | .recFuncBlock fs _ => !fs.isEmpty | _ => true) == true
#guard (shrinkDecl (.recFuncBlock [{ name := ⟨"g0", ()⟩, typeArgs := [], inputs := [],
                                     output := .bool, body := none }] .empty)).all
  (fun | .recFuncBlock fs _ => !fs.isEmpty | _ => true) == true

-- ── The oracle rejects, and the shrinker never emits, rejected declarations ──

/-- A `distinct` mentioning an undeclared global: spec-well-typed but
    algorithm-rejected. Hand-built here, since `genDistinctAssertion` emits `.op`s
    at declared constants instead. -/
private def fvarDistinctDecl : Decl :=
  .distinct ⟨"d1", ()⟩ [.fvar () ⟨"v", ()⟩ (some .int)] .empty

/-- A top-level function with a `decreases` clause and no body, which is the gap about a measure with no
    body. -/
private def measureNoBodyDecl : Decl :=
  .func { name := ⟨"f1", ()⟩, typeArgs := [], inputs := [], output := .bool,
          body := none, measure := some (.const () (.intConst 0)) } .empty

/-- A non-recursive function with a body and the measure `0`. The specification accepts it, and
    the checker rejects a measure on a function that does not call itself. -/
private def measureNonRecDecl : Decl :=
  .func { name := ⟨"f2", ()⟩, typeArgs := [], inputs := [], output := .bool,
          body := some trueExpr, measure := some (.const () (.intConst 0)) } .empty

/-- An axiom that compares `Sequence.length Sequence.empty` with `0`, with no annotation on either
    operator. Nothing fixes the element type of the empty sequence, so the checker types it at a
    generated type variable and rejects the axiom. -/
private def openInstanceDecl : Decl :=
  .ax { name := "a2",
        e := .eq () (.app () (.op () ⟨"Sequence.length", ()⟩ none) (.op () ⟨"Sequence.empty", ()⟩ none))
               (.const () (.intConst 0)) } .empty

/-- An axiom applying `id`, a name `Core.Factory` does not define.

    A person wrote this declaration, and the generator cannot give this shape. Both operator vocabularies come
    from `Core.Factory`, which `coreMonoOps_eq_factoryOps` and `corePolyOps_subset_factoryPolyOps` prove.
    Therefore each operator that a generated term applies resolves. A vocabulary that a person writes can name
    an operator that the factory does not define, and such a name makes this gap reachable. -/
private def unknownOpDecl : Decl :=
  .ax { name := "a1",
        e := .app () (.op () ⟨"id", ()⟩ (some (.arrow .bool .bool))) trueExpr } .empty

/-- The `distinct` shape the generator emits: `.op` elements at 0-ary constants
    (Core's constants) that the same step declares just before the `distinct`.
    Hand-built here in the same style as `fvarDistinctDecl`: this program is
    ACCEPTED where the `.fvar` version is rejected. -/
private def opDistinctDecls : List Decl :=
  [ .func { name := ⟨"c0", ()⟩, typeArgs := [], inputs := [], output := .int } .empty,
    .func { name := ⟨"c1", ()⟩, typeArgs := [], inputs := [], output := .int } .empty,
    .distinct ⟨"d2", ()⟩
      [.op () ⟨"c0", ()⟩ (some .int), .op () ⟨"c1", ()⟩ (some .int)] .empty ]
#guard progTypeChecks (prog opDistinctDecls) == true
-- The constants have to be *there*: the same `distinct` without them is rejected,
-- which is why `genDeclDistinct` emits the two together or not at all.
#guard progTypeChecks (prog [opDistinctDecls[2]!]) == false

-- The checker rejects a `distinct` declaration with a free variable, an unknown operator, a
-- non-recursive function with a measure (with or without a body) and an open instance. None of
-- these rejections is expected, so the completeness oracle fails on each.
#guard [fvarDistinctDecl, measureNoBodyDecl, unknownOpDecl, measureNonRecDecl, openInstanceDecl].all
  (fun d => !progTypeChecks (prog [d]) && !checkProgramTypeCheckerComplete (prog [d])) == true

/-- A procedure `name` with no formals and no contract, and the body `ss`. -/
private def procWithBody (name : String) (ss : List Statement) : Decl :=
  .proc { header := { name := ⟨name, ()⟩, typeArgs := [], inputs := [], outputs := [],
                      lemmas := [] }
          spec := { preconditions := [], postconditions := [] }
          body := .structured ss } .empty

/-- A function with the reserved type parameter `$__ty0`. -/
private def reservedTyArgDecl : Decl :=
  .func { name := ⟨"g0", ()⟩, typeArgs := ["$__ty0"], inputs := [], output := .bool,
          body := some trueExpr } .empty

/-- An axiom named like `funcDecl`. -/
private def axNamedF0 : Decl := .ax { name := "f0", e := trueExpr } .empty

/-- A procedure with a local variable named like the Core function `Int.Add`. -/
private def varFunctionClashDecl : Decl :=
  procWithBody "P1" [.init "Int.Add" (.forAll [] .int) .nondet .empty]

/-- A procedure `P2` that declares a local type `P2`. -/
private def localTypeClashDecl : Decl :=
  procWithBody "P2" [.typeDecl { name := "P2", params := [] } .empty]

-- Each expected cause on its own: the checker rejects the program, and the tag names the cause.
#guard progTypeChecks (prog [reservedTyArgDecl]) == false
#guard expectedRejectionCauses (prog [reservedTyArgDecl]) == ["reserved-name"]
#guard progTypeChecks (prog [funcDecl, axNamedF0]) == false
#guard expectedRejectionCauses (prog [funcDecl, axNamedF0]) == ["decl-kind-clash"]
#guard progTypeChecks (prog [varFunctionClashDecl]) == false
#guard expectedRejectionCauses (prog [varFunctionClashDecl]) == ["var-function-clash"]
#guard progTypeChecks (prog [localTypeClashDecl]) == false
#guard expectedRejectionCauses (prog [localTypeClashDecl]) == ["local-type-clash"]
-- A variable named like a function that is declared only later is accepted, and no cause fires.
#guard progTypeChecks
  (prog [procWithBody "P3" [.init "f0" (.forAll [] .int) .nondet .empty], funcDecl]) == true
#guard expectedRejectionCauses
  (prog [procWithBody "P3" [.init "f0" (.forAll [] .int) .nondet .empty], funcDecl]) == []
#guard expectedRejectionCauses mixed == []
#guard expectedRejectionCauses Program.init == []

-- The shared status note: silent on an accepted program, tagged on an expected rejection.
#guard programStatusNote mixed == ""
#guard programStatusNote Program.init == ""
#guard programStatusNote (prog [reservedTyArgDecl]) ==
  "\n  -- typechecker-rejected, expected: reserved-name"
-- Any other rejection, such as two axioms of one name, is unexpected, and the note gives the
-- checker's message.
#guard progTypeChecks (prog [axDecl, axDecl]) == false
#guard expectedRejectionCauses (prog [axDecl, axDecl]) == []
#guard (programStatusNote (prog [axDecl, axDecl])).startsWith
  "\n  -- typechecker-rejected, UNEXPECTED cause: " == true

-- `declHasGap` fires on exactly the gap-bearing declarations, which is what the
-- `cutGaps` family keys off.
#guard [fvarDistinctDecl, measureNoBodyDecl, unknownOpDecl].all
  (declHasGap (programFuncNames (prog [fvarDistinctDecl, measureNoBodyDecl,
                                       unknownOpDecl]))) == true
#guard [conDecl, synDecl, axDecl, distinctDecl, procDecl, funcDecl].any
  (declHasGap (programFuncNames (prog [conDecl, synDecl, axDecl, distinctDecl,
                                       procDecl, funcDecl]))) == false
-- ...and it does NOT fire on the generator's `distinct` shape, whose `.op`
-- elements resolve at the constants the same program declares.
#guard opDistinctDecls.any (declHasGap (programFuncNames (prog opDistinctDecls))) == false

-- Crucially: shrinking an ill-typed program never *emits* an ill-typed one. The
-- only way past the filter is to remove the offending declarations, so no
-- candidate retains one.
private def illTyped : Program := prog [fvarDistinctDecl, measureNoBodyDecl, axDecl]
#guard progTypeChecks illTyped == false
#guard (shrinkProgram illTyped).all progTypeChecks == true
-- Both rejected declarations have to go, so no candidate keeps either.
#guard (shrinkProgram illTyped).all (fun c => !(c.decls.contains fvarDistinctDecl)) == true
#guard (shrinkProgram illTyped).all (fun c => !(c.decls.contains measureNoBodyDecl)) == true
-- THE `cutGaps` REGRESSION: two *independent* gaps. No single drop can fix this
-- (dropping either leaves the other), so with only the one-at-a-time families the
-- candidate list would be empty and the minimizer would stall on the input. The
-- gap cut yields `[axDecl]` in one step, and the minimizer then reaches the empty
-- program.
#guard (shrinkProgramDecls illTyped).head? == some (prog [axDecl])
#guard minimizeProgramWhile (fun _ => true) 100 illTyped == Program.init
-- The same program with *one* declaration bearing *both* gaps is handled by the
-- plain drop family too, so the guard above really is about independence.
#guard progTypeChecks (prog [fvarDistinctDecl, axDecl]) == false
#guard minimizeProgramWhile (fun _ => true) 100 (prog [fvarDistinctDecl, axDecl])
  == Program.init

-- The limit in the other direction, stated here so that a reader does not read it as a defect. A property that
-- fails *only* on a program that the oracle rejects cannot shrink at all, because the filter removes each
-- candidate, and the input comes back unchanged. `shrinkStmts` and `shrinkProcsList` make the same trade.
#guard minimizeProgramWhile (fun c => !progTypeChecks c) 100 illTyped == illTyped

end Guards

end StrataGenerators.Program.TestSupport
