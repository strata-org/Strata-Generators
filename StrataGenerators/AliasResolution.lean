import StrataGenerators.DatatypeGen
import StrataGenerators.ProgramGen.UnprovenTransforms

/-!
# Eager versus incremental type-alias resolution

Strata Core resolves a type alias (`type A x := …;`, a `TypeSynonym`) **during**
type checking, one declaration at a time: `Program.typeCheck`'s fold adds each
`.syn` declaration to the type environment (`TEnv.addTypeAlias`) as it reaches it,
and later declarations are de-aliased where the checker happens to need it — a
datatype block through `MutualDatatype.resolveAliases`, an annotation through
`AnnotCompat`/`AliasEquiv`, a signature through `LTy.resolveAliases`.

The property here is that this is *equivalent to* resolving every alias up front:
expanding all aliases before the checker runs must produce a program that type
checks exactly when the original does and that **evaluates the same**. If the two
paths disagree, then an alias is not the transparent abbreviation it is documented
to be — a program's meaning would depend on whether it spells a type by its name or
by its expansion.

Both directions matter and the module states both:

* `checkAliasAcceptanceAgrees` — the two paths agree on acceptance.
* `checkAliasObligationsAgree` — the two paths give the same proof obligations,
  under Strata's own symbolic evaluator (`toCoreProofObligationProgram`, the
  `symbolicEval` phase). This is the "evaluates the same" half.

This is the *semantic* counterpart to the typing-spec gap the repo already
records: `docs/program-gen-interleaving.md` §"Direction (3)" gives a
machine-checked counterexample to `MutualADTWF` being preserved by alias
resolution (repo issue #65). That is about which programs the spec calls
well-formed; this is about whether the two resolution orders *mean* the same
thing.

## Making the property non-vacuous

`ProgramGen.genDeclAlias` emits an alias declaration but nothing ever *uses* it:
the generator's type vocabulary (`baseTypes`/`tyCons`/`dtCons`) is deliberately
kept disjoint from the alias names (invariant `Inv.aliasVocabDisjoint`), precisely
because drawing a block over alias names could not be proved sound. So a generated
program has aliases, and resolving them is the identity — the property would pass
on every draw while testing nothing.

The fix is to *introduce* alias usage rather than to hope for it:
`introduceAlias` picks a ground type `τ` that the program actually mentions, adds
`type A := τ;` as the program's first declaration, and rewrites **every**
occurrence of `τ` to `A`. The result is a program in which the alias is used in
every position a type can appear — signatures, `var` annotations, datatype
constructor fields, expression annotations — and whose eager resolution is the
program we started from. A draw where no ground type occurs at all yields `none`
and is counted as a skip, not a pass.

The rewrite direction is what makes the test sharp. Rewriting `τ` to `A`
*everywhere* means the checker never sees `τ` again and has to do the de-aliasing
itself at each of those positions; and because `A` is nullary and `τ` ground, the
rewrite cannot capture a type variable or change arity.
-/

open Lambda Core Imperative

namespace StrataGenerators.AliasResolution

open StrataGenerators.Program.UnprovenTransforms (symbolicObligations programHasLoop)

/-! ## A type rewrite over a whole program

Core has no generic "map over every type" traversal (`Program.eraseTypes` drops
*expression* annotations but keeps every signature), so this is it. Both
directions of the property need it: `introduceAlias` rewrites `τ ↦ A`, and the
comparison normalises both programs by rewriting `A ↦ τ` so that a difference in
the two obligation programs cannot be a mere difference of spelling. -/

mutual
/-- Apply `f` to `τ` and, recursively, to its arguments (bottom-up: the arguments
    are rewritten first, then `f` sees the rebuilt constructor). -/
def mapTy (f : LMonoTy → LMonoTy) : LMonoTy → LMonoTy
  | .ftvar v => f (.ftvar v)
  | .bitvec n => f (.bitvec n)
  | .tcons n args => f (.tcons n (mapTys f args))

/-- `mapTy` over a list. -/
def mapTys (f : LMonoTy → LMonoTy) : LMonoTys → LMonoTys
  | [] => []
  | t :: ts => mapTy f t :: mapTys f ts
end

/-- `mapTy` under a type scheme. The bound variables are untouched: `f` is only
    ever the ground rewrite `τ ↦ A` or its inverse, so no capture is possible. -/
def mapLTy (f : LMonoTy → LMonoTy) : LTy → LTy
  | .forAll vs mty => .forAll vs (mapTy f mty)

/-- `mapTy` over every type annotation of an expression. -/
def mapExprTys (f : LMonoTy → LMonoTy) : Expression.Expr → Expression.Expr
  | .const m c => .const m c
  | .op m o ty => .op m o (ty.map (mapTy f))
  | .bvar m i => .bvar m i
  | .fvar m x ty => .fvar m x (ty.map (mapTy f))
  | .abs m n ty e => .abs m n (ty.map (mapTy f)) (mapExprTys f e)
  | .quant m k n ty tr e =>
    .quant m k n (ty.map (mapTy f)) (mapExprTys f tr) (mapExprTys f e)
  | .app m e1 e2 => .app m (mapExprTys f e1) (mapExprTys f e2)
  | .ite m c t e => .ite m (mapExprTys f c) (mapExprTys f t) (mapExprTys f e)
  | .eq m e1 e2 => .eq m (mapExprTys f e1) (mapExprTys f e2)

/-- `mapTy` over a signature (a `ListMap` from identifier to monotype). -/
def mapSig (f : LMonoTy → LMonoTy) (s : @LMonoTySignature Unit) : @LMonoTySignature Unit :=
  s.map (fun (n, τ) => (n, mapTy f τ))

/-- `mapTy` over a function declaration: its signature, its body, its axioms, its
    preconditions and its measure. A `Core.Function` is `LFuncDefined CoreLParams`,
    whose signature types are `LMonoTy`. -/
def mapFuncTys (f : LMonoTy → LMonoTy) (fn : Core.Function) : Core.Function :=
  { fn with
    inputs := mapSig f fn.inputs
    output := mapTy f fn.output
    body := fn.body.map (mapExprTys f)
    axioms := fn.axioms.map (mapExprTys f)
    preconditions := fn.preconditions.map (fun p => { p with expr := mapExprTys f p.expr })
    measure := fn.measure.map (mapExprTys f) }

/-- `mapTy` over a statement-level function declaration. Distinct from
    `mapFuncTys` because a `Stmt.funcDecl` carries a `PureFunc Expression`, whose
    signature types are `Expression.Ty = LTy` rather than `LMonoTy`. -/
def mapPureFuncTys (f : LMonoTy → LMonoTy) (fn : PureFunc Expression) :
    PureFunc Expression :=
  { fn with
    inputs := fn.inputs.map (fun (n, τ) => (n, mapLTy f τ))
    output := mapLTy f fn.output
    body := fn.body.map (mapExprTys f)
    axioms := fn.axioms.map (mapExprTys f)
    preconditions := fn.preconditions.map (fun p => { p with expr := mapExprTys f p.expr })
    measure := fn.measure.map (mapExprTys f) }

/-- `mapTy` over a datatype block: every constructor field's type. -/
def mapBlockTys (f : LMonoTy → LMonoTy) (block : MutualDatatype Unit) :
    MutualDatatype Unit :=
  block.map fun d =>
    { d with
      constrs := d.constrs.attach.map (fun c =>
        { c.1 with args := c.1.args.map (fun (n, τ) => (n, mapTy f τ)) })
      constrs_ne := by
        have h := d.constrs_ne
        simpa using h }

/-- `mapTy` over an `ExprOrNondet`. -/
def mapOptExprTys (f : LMonoTy → LMonoTy) : ExprOrNondet Expression → ExprOrNondet Expression
  | .det e => .det (mapExprTys f e)
  | .nondet => .nondet

/-- `mapTy` over a Core command: the `var` type annotation and every expression. -/
def mapCmdTys (f : LMonoTy → LMonoTy) : Command → Command
  | .cmd (.init n ty e md) => .cmd (.init n (mapLTy f ty) (mapOptExprTys f e) md)
  | .cmd (.set n e md) => .cmd (.set n (mapOptExprTys f e) md)
  | .cmd (.assert l e md) => .cmd (.assert l (mapExprTys f e) md)
  | .cmd (.assume l e md) => .cmd (.assume l (mapExprTys f e) md)
  | .cmd (.cover l e md) => .cmd (.cover l (mapExprTys f e) md)
  | .call p args md =>
    .call p (args.map (fun a =>
      match a with
      | .inArg e => .inArg (mapExprTys f e)
      | a => a)) md

mutual
/-- `mapTy` over a statement: its command, and recursively every nested body. A
    `.typeDecl` carries a bare `TypeConstructor` (a name and its parameter count),
    which holds no type to rewrite. -/
def mapStmtTys (f : LMonoTy → LMonoTy) : Statement → Statement
  | .cmd c => .cmd (mapCmdTys f c)
  | .block l b md => .block l (mapStmtsTys f b) md
  | .ite g t e md =>
    .ite (mapOptExprTys f g) (mapStmtsTys f t) (mapStmtsTys f e) md
  | .loop g m inv b md =>
    .loop (mapOptExprTys f g) (m.map (mapExprTys f))
          (inv.map (fun (l, e) => (l, mapExprTys f e)))
          (mapStmtsTys f b) md
  | .exit l md => .exit l md
  | .funcDecl d md => .funcDecl (mapPureFuncTys f d) md
  | .typeDecl tc md => .typeDecl tc md

/-- `mapStmtTys` over a statement list. -/
def mapStmtsTys (f : LMonoTy → LMonoTy) : List Statement → List Statement
  | [] => []
  | s :: rest => mapStmtTys f s :: mapStmtsTys f rest
end

/-- `mapTy` over a procedure: header signatures, spec checks, structured body. A
    `.cfg` body is left alone (the generator produces none; only
    `StructuredToUnstructured` does). -/
def mapProcTys (f : LMonoTy → LMonoTy) (p : Core.Procedure) : Core.Procedure :=
  { p with
    header := { p.header with
                inputs := mapSig f p.header.inputs
                outputs := mapSig f p.header.outputs }
    spec := { preconditions := p.spec.preconditions.map
                (fun (l, c) => (l, { c with expr := mapExprTys f c.expr }))
              postconditions := p.spec.postconditions.map
                (fun (l, c) => (l, { c with expr := mapExprTys f c.expr })) }
    body := match p.body with
            | .structured ss => .structured (mapStmtsTys f ss)
            | b => b }

/-- `mapTy` over one declaration.

    An alias declaration's *body* is rewritten too. That matters for the
    normalising direction (`A ↦ τ`): after it, the program holds `type A := τ;`
    rather than the vacuous `type A := A;` the naive rewrite would give. -/
def mapDeclTys (f : LMonoTy → LMonoTy) : Decl → Decl
  | .type (.con tc) md => .type (.con tc) md
  | .type (.syn ts) md => .type (.syn { ts with type := mapTy f ts.type }) md
  | .type (.data block) md => .type (.data (mapBlockTys f block)) md
  | .ax a md => .ax { a with e := mapExprTys f a.e } md
  | .distinct n es md => .distinct n (es.map (mapExprTys f)) md
  | .proc p md => .proc (mapProcTys f p) md
  | .func fn md => .func (mapFuncTys f fn) md
  | .recFuncBlock fns md => .recFuncBlock (fns.map (mapFuncTys f)) md

/-- `mapTy` over every type in a program. -/
def mapProgramTys (f : LMonoTy → LMonoTy) (p : Program) : Program :=
  { p with decls := p.decls.map (mapDeclTys f) }

/-! ## Introducing an alias -/

/-- The ground types an alias may be introduced for, in the order tried.

    Only *ground* (type-variable-free) types are candidates: an alias for a
    variable-bearing type would need type parameters, `TEnv.addTypeAlias` requires
    `freeVars = typeArgs` exactly, and rewriting a variable-bearing type could
    capture. Base types come first because they occur in the most positions, so
    aliasing one exercises the most of the checker.

    The list is fixed rather than harvested from the program: what matters is that
    the chosen type *occurs* (which `occursIn` decides exactly), and a fixed list
    keeps the choice deterministic per program, which is what lets the shrinker
    reproduce a counterexample. -/
def candidateAliasTys : List LMonoTy :=
  [.bool, .int, .string, .real,
   .bitvec 1, .bitvec 8, .bitvec 16, .bitvec 32, .bitvec 64,
   .tcons "Sequence" [.int], .tcons "Map" [.int, .int]]

/-- A type name no generated program can declare: every generated name is a legal
    bare Core identifier, and this one starts with `$__`, which `genIdentName`'s
    `startChars` can produce only as `$` followed by identifier characters — but
    never the two-character run `__` after a `$`… and in any case
    `mapProgramTys` only ever inserts it transiently, inside `occursIn`. -/
private def probeTy : LMonoTy := .tcons "$__aliasProbe" []

/-- Whether `τ` occurs anywhere in `p`, decided by *rewriting* it: replace every
    occurrence with a sentinel and see whether the program changed. This reuses the
    same traversal the rewrite itself uses, so "occurs" and "is rewritten" cannot
    disagree — the alternative, a separate collector, is a second traversal that
    could drift from the first and silently pick a type that is then rewritten
    nowhere.

    The comparison is on the rendered program, since `Core.Program` carries
    `MetaData` arrays with no `BEq`. -/
def occursIn (τ : LMonoTy) (p : Program) : Bool :=
  (Std.format (mapProgramTys (fun t => if t == τ then probeTy else t) p)).pretty
    != (Std.format p).pretty

/-! ### Why the candidates are *primitive* types only

A program's own declared type names (a monomorphic datatype, a nullary abstract
type) would be attractive candidates — aliasing one puts the alias in front of the
derived-function vocabulary rather than only in front of `int`. They are excluded,
because the alias declaration has to be *positioned*: Core's fold processes
declarations in order, so `type A := T;` for a program-declared `T` may only appear
after `T`'s own declaration, and the rewrite may then only touch the declarations
that follow it. Introducing an alias for a *primitive* type needs no such
reasoning: the alias goes first and the rewrite is total, which is the strongest
form of the test. The narrower coverage is a deliberate trade, and a program
whose types are all program-declared is counted as a skip rather than a pass. -/

/-- A name for the introduced alias, fresh for the program: longer than every
    name the program declares, by the same length argument
    `DatatypeGen.fallbackName` uses. -/
def freshAliasName (p : Program) : String :=
  let names := p.getNames.map (·.name)
  indexedFreshName (DatatypeGen.maxNameLength names) 0

/-- Introduce an alias into `p`: pick the first ground type `τ` it mentions, add
    `type A := τ;` as the first declaration, and rewrite every occurrence of `τ`
    to `A`. Returns `(A, τ, p')`, or `none` when `p` mentions no ground type (a
    fully polymorphic program — counted as a skip).

    The alias declaration comes **first** so that it is in scope at every use:
    Core's fold processes declarations in order, so an alias used before its
    declaration would be an unresolvable name rather than a test of resolution. -/
def introduceAlias (p : Program) : Option (String × LMonoTy × Program) :=
  match candidateAliasTys.find? (occursIn · p) with
  | none => none
  | some τ =>
    let a := freshAliasName p
    let aliasTy : LMonoTy := .tcons a []
    let rewritten := mapProgramTys (fun t => if t == τ then aliasTy else t) p
    let decl : Decl := .type (.syn { name := a, typeArgs := [], type := τ }) .empty
    some (a, τ, { rewritten with decls := decl :: rewritten.decls })

/-- Rewrite `A` back to `τ` everywhere: the *eager* resolution of the alias
    `introduceAlias` added, and also the normaliser the obligation comparison
    applies to both sides so that a difference cannot be one of spelling.

    Expanding by substitution rather than through `LMonoTy.resolveAliases` keeps
    this a claim about *Strata's* behaviour: were the eager path to use the
    checker's own resolver, a defect in that resolver would appear on both sides
    and cancel. `A` is nullary and `τ` ground, so the substitution is exactly what
    the resolver's `tconsAliasSimple` would compute. -/
def expandAlias (a : String) (τ : LMonoTy) (p : Program) : Program :=
  mapProgramTys (fun t => if t == .tcons a [] then τ else t) p

/-! ## The two properties -/

/-- Whether Strata's checker accepts `p`. -/
private def accepts (p : Program) : Bool :=
  match Core.typeCheck Core.VerifyOptions.quiet p with
  | .ok _ => true
  | .error _ => false

/-- The checker's diagnostic on `p`, or `none` when it accepts. Used only for
    reporting a counterexample. -/
def rejectionMessage (p : Program) : Option String :=
  match Core.typeCheck Core.VerifyOptions.quiet p with
  | .ok _ => none
  | .error m => some (toString (m.format none))

/-- **Eager and incremental alias resolution agree on acceptance.**

    Given a generated program `p`, let `p'` be `p` with one of its ground types
    replaced by a fresh alias (`introduceAlias`). Then

    * the *incremental* path is `typeCheck p'` — the checker meets the alias
      declaration in its fold and resolves later uses itself;
    * the *eager* path is `typeCheck (expandAlias … p')` — every alias use is
      expanded first, so the checker never sees the alias in a use position.

    The two must agree. Vacuously `true` when `p` mentions no ground type, and —
    deliberately — **not** conditioned on `p` itself typechecking: about 40% of
    generated programs trip a documented completeness gap, and an alias is
    supposed to be transparent for *those* too. What the property forbids is one
    path accepting where the other rejects. -/
def checkAliasAcceptanceAgrees (p : Program) : Bool :=
  match introduceAlias p with
  | none => true
  | some (a, τ, p') => accepts p' == accepts (expandAlias a τ p')

/-- **Eager and incremental alias resolution give the same proof obligations.**
    The "evaluates the same" half: the oracle is Strata's own symbolic evaluator
    (`toCoreProofObligationProgram`, the `symbolicEval` phase of
    `corePipelinePhases`), so what is compared is the verification conditions a
    real run would receive.

    Both sides are normalised with `expandAlias` before comparison — the
    incremental path's output still spells the alias in its annotations, and a
    difference of spelling is not a difference of meaning.

    Screened three ways, each of which would otherwise make the comparison a
    non-claim rather than a failure:

    * no ground type to alias — nothing to test;
    * `programHasLoop` — the symbolic evaluator **panics** (not `.error`) on a
      loop, so the screen has to precede the call;
    * one of the two paths not typechecking — then it has no obligations to
      compare, and the disagreement is `checkAliasAcceptanceAgrees`' business, not
      this property's. -/
def checkAliasObligationsAgree (p : Program) : Bool :=
  match introduceAlias p with
  | none => true
  | some (a, τ, p') =>
    let pEager := expandAlias a τ p'
    if programHasLoop p' || programHasLoop pEager then true
    else if !(accepts p' && accepts pEager) then true
    else
      match symbolicObligations p', symbolicObligations pEager with
      | some oIncr, some oEager =>
        (Std.format (expandAlias a τ oIncr)).pretty
          == (Std.format (expandAlias a τ oEager)).pretty
      | none, none => true
      | _, _ => false

/-- Whether this program contributes anything to the two properties above: it
    mentions a ground type, so an alias can be introduced. Reported as a coverage
    statistic — a suite where this is rarely true is a suite whose alias
    properties are mostly vacuous. -/
def aliasIntroducible (p : Program) : Bool := (introduceAlias p).isSome

/-- Whether the alias-introduced program is one the *obligation* property actually
    compares (both paths accepted, no loop). The second coverage statistic. -/
def aliasObligationsCompared (p : Program) : Bool :=
  match introduceAlias p with
  | none => false
  | some (a, τ, p') =>
    let pEager := expandAlias a τ p'
    !(programHasLoop p' || programHasLoop pEager)
      && accepts p' && accepts pEager
      && (symbolicObligations p').isSome && (symbolicObligations pEager).isSome

end StrataGenerators.AliasResolution
