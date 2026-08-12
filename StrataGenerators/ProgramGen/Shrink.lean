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
exists for its kind, and the only genuinely new reductions are the ones no
sub-shrinker can express — dropping a whole declaration, and reducing the
*declaration-level* data (a type constructor's arity, an alias body, a datatype
block's constructor list, a `distinct`'s expression list).

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
  Since candidates only ever *drop* or *shrink* declarations and never rename or
  duplicate one, distinctness is preserved anyway; the filter makes it
  unconditional even on input that did not have it.
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

The **program's declaration order is preserved** (candidates are sublists /
in-place replacements, never reorderings), and no declaration is ever renamed —
which keeps a counterexample readable against the original and keeps the
`Nodup` obligation trivially maintained.

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
    candidate can violate that side-condition — it is a Lean-level obligation, not
    a checker-level one, so no amount of oracle filtering could rescue it. -/
private def setConstrs (d : LDatatype Unit) (cs : List (LConstr Unit)) :
    Option (LDatatype Unit) :=
  if h : cs.length != 0 then some { d with constrs := cs, constrs_ne := h } else none

/-- Structurally smaller type declarations.

    * **abstract type** (`.con`) — drop one type parameter, lowering the arity.
      This is a genuine program-level reduction: the arity is what later alias
      bodies and datatype constructor arguments must apply the constructor at, so
      any candidate that leaves such a use behind is rejected by the oracle.
    * **alias** (`.syn`) — reduce the body with `shrinkTy` and re-derive
      `typeArgs` from the reduced body's free variables, exactly as
      `ProgramGen.mkAliasDecl` does. Re-deriving is what keeps
      `TEnv.addTypeAlias`'s guards (`typeArgs.Nodup`, `freeVars ⊆ typeArgs`, no
      phantom args) satisfied by construction; simply keeping the old `typeArgs`
      would strand a phantom argument whenever the reduction dropped a variable.
    * **datatype block** (`.data`) — drop one whole datatype from the block, drop
      one constructor from one datatype, or drop one argument from one
      constructor. A block must stay non-empty (`.data []` is not a legal
      declaration) and each datatype must keep at least one constructor
      (`LDatatype.constrs_ne`), so those two drops are guarded rather than
      offered blindly. Dropping the *last* constructor of a datatype is instead
      expressed by dropping that datatype.

      Dropping a constructor can make a datatype uninhabited, and dropping a
      datatype orphans any recursive reference to it from a sibling — both are
      rejected by `addMutualBlock` inside the oracle, so neither needs a local
      check here. -/
def shrinkTypeDecl : TypeDecl → List TypeDecl
  | .con tc => (fun ps => .con { tc with params := ps }) <$> dropEach tc.params
  | .syn ts =>
    (fun τ => .syn { ts with type := τ, typeArgs := (LMonoTy.freeVars τ).dedup })
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

/-- Whether every free variable in each of `f`'s `requires` clauses is one of its
    formals — i.e. the function has no *stranded* precondition.

    **Nothing in Strata enforces this.** `Function.typeCheck` never inspects
    `preconditions` at all: its `freeVarChecks` guard covers the body and the measure
    only (`FunctionType.lean:130`), and no other line of the file mentions the field.
    So `function f0() : bool requires y == 0 { true }`, where `y` is declared
    nowhere, typechecks — as does a non-Boolean clause. `WFFunctionProp` is an empty
    structure, so `WF.lean` does not rule it out either. The consequence reaches
    further than the declaration: `PrecondElim` lifts such a clause into an `assume`
    statement, where the statement typechecker *does* free-var check, so the pass
    turns an accepted program into a rejected one.

    Producing one is easy: `shrinkFunc`'s drop-an-input reduction removes the very
    formal a clause mentions, and `genFunction` emits a clause over the formals on
    roughly half its draws (measured 101/200). The shrinkers therefore refuse to.
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
    * `.ax` → `shrinkLExpr` on the axiom's expression;
    * `.distinct` → `shrinkDistinctExprs`;
    * `.proc` → `shrinkProcCandidates` (drop the body, drop/reduce a contract
      clause, reduce the body via `shrinkStmtsList` — holding the header fixed);
    * `.func` → `shrinkFunc`, the *signature-reducing* function reducer (drop the
      body or measure, drop or reduce a `requires` clause, drop an input or type-arg,
      reduce an input/output type, shorten the name), filtered by `funcWellFormed`.
      That filter is what keeps a surviving `requires` clause Boolean and scoped to
      the formals — a condition no Strata check supplies (see
      `funcPreconditionsScoped`), and one that `shrinkFunc`'s own drop-an-input
      family would otherwise violate. The narrower
      signature-preserving `shrinkFuncCandidates` backing the `Shrinkable Function`
      instance is deliberately not used here: at program level there is no reason to
      pin a declared function's signature, and the wider reducer is what lets a
      counterexample shrink to a constant function. Names *are* shortened by
      `shrinkFunc`; a rename that collided with another declaration would break
      `getNames.Nodup` and is rejected by the oracle.
    * `.recFuncBlock` → drop one function from the block (only while two or more
      remain — `DeclHasType'.recFuncBlock` requires a non-empty block), or reduce
      one with `shrinkFunc` (same filter).

    Candidates are raw; the whole-program filter in `shrinkProgramDecls` removes
    the ill-typed ones. `genProgram` never emits `.recFuncBlock`, so that family
    is exercised only by the `#guard`s below — it is there so the shrinker is total
    on hand-written and future-generated programs rather than silently refusing to
    reduce a declaration kind. -/
def shrinkDecl : Decl → List Decl
  | .type t md => (.type · md) <$> shrinkTypeDecl t
  | .ax a md => (fun e => .ax { a with e := e } md) <$> shrinkLExpr a.e
  | .distinct n es md => (.distinct n · md) <$> shrinkDistinctExprs es
  | .proc p md => (.proc · md) <$> shrinkProcCandidates p
  | .func f md => (.func · md) <$> (shrinkFunc f).filter funcWellFormed
  | .recFuncBlock fs md =>
    let dropOne := if fs.length ≤ 1 then [] else (Decl.recFuncBlock · md) <$> dropEach fs
    let shrinkOne := fs.zipIdx.flatMap fun (f, i) =>
      (fun f' => Decl.recFuncBlock (fs.set i f') md) <$> (shrinkFunc f).filter funcWellFormed
    dropOne ++ shrinkOne

-- ── Classifying an unshrinkable counterexample ────────────────────────────
-- When the oracle rejects the *input* program, no candidate can pass the filter
-- and the counterexample is reported unshrunk. These predicates let a harness say
-- which of the three known rejection causes it hit, instead of leaving the
-- reader to guess from an unreduced program. Each was validated against the
-- typechecker over 100 generated programs: every rejection matched at least one,
-- and no accepted program matched any.
--
-- The `distinct-fvar` class is not *reachable* from `genProgram`:
-- `genDistinctAssertion` emits `.op` nodes at constants the step also declares,
-- never bare `.fvar`s. The predicate is kept because it classifies
-- hand-written and shrunk-from-elsewhere programs correctly, and because
-- `declHasGap`/`cutGaps` treat all three classes uniformly; the `#guard`s below
-- exercise it on a hand-built declaration.

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
    does not know it — which is exactly how a generated `distinct` refers to the
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

/-- Whether a function has a `decreases` clause but no body — the spec-permitted,
    algorithm-rejected shape (`FuncHasType'` makes both fields independently
    optional; `Function.typeCheck` rejects the combination). -/
def funcMeasureNoBody (f : Function) : Bool := f.measure.isSome && f.body.isNone

/-- Whether a declaration carries a measure-without-body function, at top level or
    as an inline `funcDecl` anywhere in a procedure body. -/
def declMeasureNoBody : Decl → Bool
  | .func f _ => funcMeasureNoBody f
  | .recFuncBlock fs _ => fs.any funcMeasureNoBody
  | .proc pr _ => (stmtsFuncDecls (bodyStmts pr.body)).any funcDeclMeasureNoBody
  | _ => false
where
  /-- The same shape on an inline `funcDecl`'s declaration. -/
  funcDeclMeasureNoBody (d : Imperative.PureFunc Expression) : Bool :=
    d.measure.isSome && d.body.isNone

/-- Whether a declaration is a `distinct` mentioning a free variable — a global the
    program never declares. -/
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

/-- Whether a declaration bears any of the three known rejection causes, i.e. is a
    declaration on whose account `Program.typeCheck` will reject the whole program
    (two generator limitations and one Strata gap — see the module doc). Used both
    to classify an unshrinkable counterexample and to drive the `cutGaps` candidate
    family. -/
def declHasGap (declared : List String) (d : Decl) : Bool :=
  declDistinctFvar d || declMeasureNoBody d || declUnknownOp declared d

/-- Whether any declaration of `p` is a `distinct` mentioning an undeclared
    global. -/
def hasUndeclaredDistinctFvar (p : Program) : Bool := p.decls.any declDistinctFvar

/-- Whether any declaration of `p` carries a measure-without-body function. -/
def hasMeasureNoBody (p : Program) : Bool := p.decls.any declMeasureNoBody

/-- Whether any declaration of `p` applies an operator neither `Core.Factory` nor
    `p` itself defines. -/
def hasUnknownOp (p : Program) : Bool :=
  p.decls.any (declUnknownOp (programFuncNames p))

/-- The known rejection causes present in `p`, as short tags, most common first
    (`[]` when none is). A harness reporting an unshrunk counterexample can print
    these to say *why* the oracle refused every candidate; an empty list on a
    rejected program means a new, unclassified gap — worth investigating. -/
def programRejectionCause (p : Program) : List String :=
  (if hasUndeclaredDistinctFvar p then ["distinct-fvar"] else [])
    ++ (if hasMeasureNoBody p then ["measure-no-body"] else [])
    ++ (if hasUnknownOp p then ["unknown-op"] else [])

/-- A one-line annotation explaining a program's typechecker status, or `""` when it
    typechecks (so a passing sample renders unadorned). Three cases:

    * accepted → `""`;
    * rejected, cause known → the gap tags, which is all a reader needs since the
      three gaps are documented;
    * rejected, cause **unknown** → the verbatim diagnostic. This is the interesting
      case: it means `genProgram` produced a spec-well-typed program the algorithm
      rejects for a *new* reason, and it is exactly when the reader needs the
      checker's own message rather than a summary.

    Shared by the Plausible `Repr` and the Tyche panel renderer so a counterexample
    reads identically in both views. -/
def programStatusNote (p : Program) : String :=
  if progTypeChecks p then ""
  else match programRejectionCause p with
    | [] =>
      let msg := (progTypeCheckError p).getD "(no diagnostic)"
      s!"\n  -- typechecker-rejected, UNCLASSIFIED cause: {msg}"
    | cs => s!"\n  -- typechecker-rejected, known gap(s): {" ".intercalate cs}"

-- ── The whole-program check predicates (shared by both harnesses) ─────────

/-- **Whole-program typechecker completeness.** `genProgram` is proven sound (its
    output satisfies `ProgramHasTypeA`), so the algorithmic `Program.typeCheck`
    should accept every generated program. This states that HONESTLY and so FAILS
    on each of the three gaps in the module doc — a genuine spec/algorithm
    divergence, reported as a real failure rather than masked. The program-level
    analogue of `checkTypeCheckerComplete` (statements) and
    `checkFunctionTypeCheckerComplete` (functions). -/
abbrev checkProgramTypeCheckerComplete (p : Program) : Bool := progTypeChecks p

/-- **Characterization of the rejection causes.** "Every rejection of a generated
    program is attributable to a known gap": accepts, OR bears one of the three
    causes. This PINS the list as complete — it should pass, and a failure means
    `genProgram` produced a spec-well-typed program the algorithm rejects for some
    *other* reason: a new, unclassified completeness bug. The program-level analogue
    of `rejectionImpliesFuncDecl` and `funcRejectionImpliesMeasureNoBody`. -/
def checkProgramRejectionIsKnownGap (p : Program) : Bool :=
  progTypeChecks p || !(programRejectionCause p).isEmpty

/-! ### Whole-program invariants of a *well-typed* program

The four properties below are all conditional on the input typechecking, so they
are vacuous on the ~60% of draws the gaps account for and are genuine claims on the
rest. Unlike `checkProgramTypeCheckerComplete`, a counterexample to any of them is
*shrinkable*: the failure does not depend on the oracle rejecting the program, so
smaller candidates are available and the minimizer reports a minimal witness.

Three of the four hold on generated input. `checkProgramTypeCheckIdempotent` **fails
intermittently** — roughly 1 in 500 single-function draws — and its docstring records
the cause. -/

/-- **`getNames` distinctness.** `ProgramHasType'`'s first conjunct is
    `P.getNames.Nodup`, which the checker enforces incrementally via
    `C.idents.addListWithError decl.names`. So a program the checker accepts must
    have distinct names — asserted here directly against `getNames`, i.e. against
    the flat namespace the spec quantifies over rather than the checker's
    incremental fold. -/
def checkProgramNamesNodup (p : Program) : Bool :=
  !progTypeChecks p || p.getNames.eraseDups.length == p.getNames.length

/-- **Typechecking is idempotent.** `Program.typeCheck` returns a *rewritten*
    program (each declaration resolved and annotated), so the natural claim is that
    re-checking the output succeeds: the checker's output is in its own input
    language.

    **FAILS intermittently** — measured at 1 of 482 accepted single-function draws,
    and 0 of 244 accepted multi-declaration programs. Every instance observed is a
    polymorphic function whose type parameter is used *only* as a quantifier binder
    annotation in the body, e.g.

        function s<a>() : bool { exists q : a :: false }

    which is accepted, but whose returned form is not: the body's annotation comes
    back freshened to `$__ty1` while `typeArgs` comes back `[]`, so the output trips
    the declaration-level guard ("body contains undeclared type variables") that the
    input passed. The rename-back step (`FunctionType.lean:91`, `:96-98`, `:184-189`)
    is driven by the type variables of the *signature*, and a type parameter that
    occurs only in a body binder annotation is invisible to it.

    Stated honestly, so it reports the failure rather than masking it — the same
    convention as `checkProgramTypeCheckerComplete`. Unlike that one, a counterexample
    here *is* shrinkable, since the failure is in the checker's output rather than in
    its verdict on the input. -/
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
    property (`checkResolveAfterErase`). -/
def checkProgramEraseTypesPreservesTyping (p : Program) : Bool :=
  !progTypeChecks p || progTypeChecks p.eraseTypes

-- ── Program-level shrinker ────────────────────────────────────────────────

/-- Structurally smaller, **well-typed** candidate programs, largest reduction
    first. Four families:

    1. **cut every gap-bearing declaration at once** (`declHasGap`) — see below;
    2. **truncate to a prefix**, dropping a whole suffix of declarations;
    3. **drop one declaration**;
    4. **replace one declaration by a smaller one** (`shrinkDecl`).

    Declaration order is preserved throughout (every family is a sublist or an
    in-place replacement, never a reordering), and every candidate — drops
    included — is filtered through `progTypeChecks`.

    Filtering the drop family too may look redundant, but removing a declaration
    genuinely *can* break the survivors: a later declaration may reference the
    dropped one, and a dropped procedure may still be called. It matters for a
    second reason as well: on ill-typed input, which does occur (the three
    rejection causes in the module doc), an unfiltered drop family would emit
    smaller *ill-typed* programs and quietly break the shrinker's contract. With
    the filter the guarantee is unconditional — every program this shrinker
    returns typechecks, whatever it was handed.

    **Why families 1 and 2 exist.** With only the one-at-a-time families, a program
    carrying *two independent* gap-bearing declarations cannot be reduced at all:
    dropping either one leaves the other, so no single-step candidate passes the
    filter, and the minimizer returns the input untouched even though a much
    smaller well-typed program is one step away. That is not rare — 13 of 100
    measured draws carry two distinct gaps. The gap cut (family 1) removes all of
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
    minimizer used to report a *minimal* counterexample is `minimizeProgramWhile`. -/
def shrinkProgram (p : Program) : List Program :=
  (shrinkProgramDecls p).filter fun c => sizeProgram c < sizeProgram p

/-- Greedily minimize `p` while the predicate `fails` still holds, mirroring
    `minimizeProcsWhile`: repeatedly take the first strictly-smaller well-typed
    candidate that still satisfies `fails`, until no candidate does or the fuel
    runs out.

    Because a candidate is kept only when it still fails, the result is always a
    genuine counterexample — and because every candidate passed `progTypeChecks`,
    always a well-typed one (see the module doc on what that does and does not buy
    in terms of well-formedness). If the failure hinges on something no smaller
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

/-- A `distinct` over two closed integer literals (no free variables, so the
    algorithm accepts it — unlike a generated one). -/
private def distinctDecl : Decl :=
  .distinct ⟨"d0", ()⟩ [.const () (.intConst 0), .const () (.intConst 1)] .empty

/-- An alias `type S x := Sequence x;` — `typeArgs` derived from the body, as
    `mkAliasDecl` does. -/
private def synDecl : Decl :=
  .type (.syn { name := "S", typeArgs := ["x"], type := .seq (.ftvar "x") }) .empty

/-- A minimal well-typed procedure: no formals, no contract, empty body. -/
private def procDecl : Decl :=
  .proc { header := { name := ⟨"P0", ()⟩, typeArgs := [], inputs := [], outputs := [],
                      noFilter := false }
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
-- Declaration order is preserved: no candidate reorders what it keeps. (Checked
-- via names, which are never rewritten except by `shrinkFunc`'s rename — hence
-- the `f`/`f0` allowance.)
#guard (shrinkProgram mixed).all
  (fun c => (c.decls.map (fun d => d.name.name)).all
    (fun n => n ∈ ["G", "S", "a0", "d0", "P0", "f0", "f"])) == true

-- Dropping a declaration is offered: a property that fails on every program
-- minimizes all the way to the empty program.
#guard minimizeProgramWhile (fun _ => true) 100 mixed == Program.init
-- A property that holds everywhere leaves the input untouched.
#guard minimizeProgramCounterexample (fun _ => true) 100 mixed == mixed
-- Prefix truncation is offered: every proper prefix of `mixed` typechecks, so all
-- six (lengths 0–5) are among the candidates. (They are not *only* from the prefix
-- family — dropping the last declaration yields the length-5 prefix too — so this
-- asserts reachability, not provenance.)
#guard (List.range mixed.decls.length).all
  (fun n => (shrinkProgram mixed).any (fun c => c.decls == mixed.decls.take n)) == true

-- Per-kind reductions are all non-empty on the mixed program, i.e. every
-- declaration kind really is reducible (not just droppable).
#guard (shrinkDecl conDecl).isEmpty == false        -- arity 2 → 1
#guard (shrinkDecl synDecl).isEmpty == false        -- Sequence x → x
#guard (shrinkDecl distinctDecl).isEmpty == false   -- drop/reduce an element
#guard (shrinkDecl funcDecl).isEmpty == false       -- drop the body
-- `axDecl`'s body is already a leaf and `procDecl` is already empty, so those two
-- are droppable but not reducible — asserted so the guard above is honest.
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
-- constructor list non-empty — the two well-formedness side-conditions no oracle
-- run could rescue (they are *type*-level in Lean, not checker-level).
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
-- `Function.typeCheck` ignores `preconditions` entirely — neither type-checking nor
-- free-var-checking them. So dropping the input a `requires` mentions yields a
-- program that typechecks yet references a variable nothing declares, and the *only*
-- thing preventing that is `funcWellFormed`'s precondition conditions. These guards
-- pin both directions: the clause is reducible, and never stranded.

/-- `function f0(y : int) : bool requires y == 0 { true }` — a precondition over
    the formal, the shape `genFunction` produces (on ~half its draws). -/
private def precondFunc : Function :=
  { name := ⟨"f0", ()⟩, typeArgs := [], inputs := [(⟨"y", ()⟩, .int)], output := .bool,
    body := some trueExpr,
    preconditions := [{ expr := .eq () (.fvar () ⟨"y", ()⟩ (some .int))
                                       (.const () (.intConst 0)), md := () }] }
/-- The same function with the input dropped: `requires y == 0` now dangles. -/
private def precondFuncDangling : Function := { precondFunc with inputs := [] }

-- The oracle really does accept the dangling form, so the filter is load-bearing
-- rather than belt-and-braces.
#guard progTypeChecks (prog [.func precondFuncDangling .empty]) == true
-- `funcWellFormed` is what rejects it (its precondition-scoping condition).
#guard funcWellFormed precondFunc == true
#guard funcWellFormed precondFuncDangling == false
#guard funcPreconditionsScoped precondFunc == true
#guard funcPreconditionsScoped precondFuncDangling == false
-- A non-Boolean clause is rejected too — the other half no Strata check supplies.
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

-- The analogous *measure* reduction: dropping the inputs leaves the measure's `y`
-- dangling. `strata-org/Strata` `main` accepts this shape (it used to reject it), so the
-- reduction needs no filter for the opposite reason — the oracle no longer refuses it.
private def measureFunc : Function :=
  { precondFunc with preconditions := [], measure := some (.fvar () ⟨"y", ()⟩ (some .int)) }
#guard progTypeChecks (prog [.func { measureFunc with inputs := [] } .empty]) == true

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

-- ── The oracle really does reject, and the shrinker never emits, the gaps ──

/-- A `distinct` mentioning an undeclared global: spec-well-typed but
    algorithm-rejected. Hand-built here, since `genDistinctAssertion` emits `.op`s
    at declared constants instead. -/
private def fvarDistinctDecl : Decl :=
  .distinct ⟨"d1", ()⟩ [.fvar () ⟨"v", ()⟩ (some .int)] .empty

/-- A top-level function with a `decreases` clause and no body — the
    measure-without-body gap (~28%). -/
private def measureNoBodyDecl : Decl :=
  .func { name := ⟨"f1", ()⟩, typeArgs := [], inputs := [], output := .bool,
          body := none, measure := some (.const () (.intConst 0)) } .empty

/-- An axiom applying `id`, a name `Core.Factory` does not define.

    Hand-built only: the generator can no longer produce this shape. Both operator
    vocabularies are derived from `Core.Factory` (`coreMonoOps_eq_factoryOps`,
    `corePolyOps_subset_factoryPolyOps`), so every operator a generated term applies
    resolves. The old hand-written `corePolyOps` carried a `const` the factory does not
    define, which is what used to make this gap reachable from the generator. -/
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
#guard programRejectionCause (prog opDistinctDecls) == []
-- The constants have to be *there*: the same `distinct` without them is rejected,
-- which is why `genDeclDistinct` emits the two together or not at all.
#guard progTypeChecks (prog [opDistinctDecls[2]!]) == false

-- `distinct-fvar` and `unknown-op` are still genuinely rejected, so the cases below are
-- not vacuous. `measure-no-body` is **accepted on `strata-org/Strata` `main`** — that gap
-- is closed — so the tag below now classifies a shape the checker no longer refuses;
-- `programStatusNote` only consults the classifier on a *rejected* program, so it stays
-- silent on this one.
#guard progTypeChecks (prog [fvarDistinctDecl]) == false
#guard progTypeChecks (prog [measureNoBodyDecl]) == true
#guard progTypeChecks (prog [unknownOpDecl]) == false
-- ...and each is classified, with no false positive on the accepted mixed program.
#guard programRejectionCause (prog [fvarDistinctDecl]) == ["distinct-fvar"]
#guard programRejectionCause (prog [measureNoBodyDecl]) == ["measure-no-body"]
#guard programRejectionCause (prog [unknownOpDecl]) == ["unknown-op"]
#guard programRejectionCause mixed == []
#guard programRejectionCause Program.init == []

-- The shared status note: silent on an accepted program, tagged on a known gap.
#guard programStatusNote mixed == ""
#guard programStatusNote Program.init == ""
-- `measureNoBodyDecl` now typechecks, so the note is silent on it.
#guard programStatusNote (prog [measureNoBodyDecl]) == ""
-- Two gaps at once are both reported.
#guard programStatusNote (prog [fvarDistinctDecl, measureNoBodyDecl]) ==
  "\n  -- typechecker-rejected, known gap(s): distinct-fvar measure-no-body"
-- A rejection matching *no* known gap falls back to the checker's own message —
-- the case worth chasing. Here: two declarations sharing a name, which
-- `getNames.Nodup` forbids and no gap predicate covers.
#guard progTypeChecks (prog [axDecl, axDecl]) == false
#guard programRejectionCause (prog [axDecl, axDecl]) == []
#guard (programStatusNote (prog [axDecl, axDecl])).startsWith
  "\n  -- typechecker-rejected, UNCLASSIFIED cause: " == true

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
-- Only the still-rejected `distinct-fvar` declaration has to go; `measureNoBodyDecl`
-- typechecks on `main`, so a candidate may legitimately keep it.
#guard (shrinkProgram illTyped).all (fun c => !(c.decls.contains fvarDistinctDecl)) == true
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

-- The converse limitation, stated so it is not mistaken for a bug: a property
-- that fails *only* on programs the oracle rejects cannot be minimized at all —
-- every candidate is filtered out, and the input comes back untouched. This is
-- the same trade `shrinkStmts` and `shrinkProcsList` make.
#guard minimizeProgramWhile (fun c => !progTypeChecks c) 100 illTyped == illTyped

end Guards

end StrataGenerators.Program.TestSupport
