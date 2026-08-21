import StrataGenerators.DatatypeGen
import StrataGenerators.ProgramGen.UnprovenTransforms

/-!
# Eager and incremental resolution of a type alias

Strata Core resolves a type alias **during** type checking, one declaration at a
time. An alias is a `TypeSynonym`, and it has the form `type A x := …;`. The fold of
`Program.typeCheck` adds each `.syn` declaration to the type environment with
`TEnv.addTypeAlias` when it reaches that declaration. It then removes an alias from a
later declaration at the places where the checker needs the expansion: from a
datatype block through `MutualDatatype.resolveAliases`, from an annotation through
`AnnotCompat` and `AliasEquiv`, and from a signature through `LTy.resolveAliases`.

The property here says that this order gives the same result as the expansion of every
alias before the checker runs. The expanded program must type check exactly when the
original does, and it must **evaluate the same**. If the two paths disagree, then an
alias is not the transparent abbreviation that the documents describe, and the meaning
of a program depends on whether it writes a type by its name or by its expansion.

Both directions matter, and this module states both:

* `checkAliasAcceptanceAgrees`: the two paths agree on acceptance.
* `checkAliasObligationsAgree`: the two paths give the same proof obligations under the
  symbolic evaluator of Strata, which is `toCoreProofObligationProgram` in the
  `symbolicEval` phase. This is the half about evaluation.

This is the *semantic* companion to a gap in the typing specification that the
repository records elsewhere: there is a machine-checked counterexample to the claim
that alias resolution keeps `MutualADTWF`. That gap is about which programs the
specification calls well-formed. This module is about whether the two orders of
resolution *mean* the same thing.

## How the property stays away from vacuity

`ProgramGen.genDeclAlias` emits an alias declaration, but nothing *uses* it. The type
vocabulary of the generator, which is `baseTypes`, `tyCons` and `dtCons`, stays
disjoint from the alias names. The invariant `Inv.aliasVocabDisjoint` states this, and
the reason is that no proof of soundness exists for a block that draws over alias
names. A generated program therefore has aliases, and resolution of them is the
identity function. The property then holds on each draw and it tests nothing.

The fix is to *add* a use of an alias. `introduceAlias` picks a ground type `τ` that
the program mentions, adds `type A := τ;` as the first declaration of the program, and
rewrites **each** occurrence of `τ` to `A`. The result is a program that uses the alias
in each position where a type can occur: a signature, a `var` annotation, a field of a
datatype constructor, and an annotation on an expression. The eager resolution of that
program is the program at the start. A draw that mentions no ground type gives `none`,
and the suite counts it as a skip and not as a pass.

The direction of the rewrite is what makes the test sharp. The rewrite of `τ` to `A`
happens *everywhere*, so the checker never sees `τ` again and must remove the alias
itself at each of those positions. `A` is nullary and `τ` is ground, so the rewrite
cannot capture a type variable and it cannot change an arity.
-/

open Lambda Core Imperative

namespace StrataGenerators.AliasResolution

open StrataGenerators.Program.UnprovenTransforms (symbolicObligations programHasLoop)

/-! ## A rewrite of the types of a whole program

Core has no traversal that maps a function over each type. `Program.eraseTypes` drops
the annotation of an *expression*, but it keeps each signature. The functions below are
therefore that traversal. Both directions of the property need it. `introduceAlias`
rewrites `τ` to `A`. The comparison then normalizes both programs, and it rewrites `A`
to `τ`, so a difference between the two obligation programs cannot be a difference of
spelling only. -/

mutual
/-- Applies `f` to `τ` and to the arguments of `τ`. The traversal goes from the bottom
    up: it rewrites the arguments first, and `f` then sees the constructor that the
    traversal rebuilt. -/
def mapTy (f : LMonoTy → LMonoTy) : LMonoTy → LMonoTy
  | .ftvar v => f (.ftvar v)
  | .bitvec n => f (.bitvec n)
  | .tcons n args => f (.tcons n (mapTys f args))

/-- `mapTy` over a list of types. -/
def mapTys (f : LMonoTy → LMonoTy) : LMonoTys → LMonoTys
  | [] => []
  | t :: ts => mapTy f t :: mapTys f ts
end

/-- `mapTy` under a type scheme. The function does not change a bound variable. `f` is
    always the ground rewrite from `τ` to `A`, or its inverse, so no capture can
    happen. -/
def mapLTy (f : LMonoTy → LMonoTy) : LTy → LTy
  | .forAll vs mty => .forAll vs (mapTy f mty)

/-- `mapTy` over each type annotation of an expression. -/
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

/-- `mapTy` over a signature, which is a `ListMap` from an identifier to a monotype. -/
def mapSig (f : LMonoTy → LMonoTy) (s : @LMonoTySignature Unit) : @LMonoTySignature Unit :=
  s.map (fun (n, τ) => (n, mapTy f τ))

/-- `mapTy` over a function declaration: the signature, the body, the axioms, the
    preconditions and the measure. A `Core.Function` is an `LFuncDefined CoreLParams`, and
    the types in its signature are `LMonoTy` values. -/
def mapFuncTys (f : LMonoTy → LMonoTy) (fn : Core.Function) : Core.Function :=
  { fn with
    inputs := mapSig f fn.inputs
    output := mapTy f fn.output
    body := fn.body.map (mapExprTys f)
    axioms := fn.axioms.map (mapExprTys f)
    preconditions := fn.preconditions.map (fun p => { p with expr := mapExprTys f p.expr })
    measure := fn.measure.map (mapExprTys f) }

/-- `mapTy` over a function declaration inside a statement. This function is separate from
    `mapFuncTys`, because a `Stmt.funcDecl` holds a `PureFunc Expression`, and the types in
    its signature are `Expression.Ty`, which is `LTy` and not `LMonoTy`. -/
def mapPureFuncTys (f : LMonoTy → LMonoTy) (fn : PureFunc Expression) :
    PureFunc Expression :=
  { fn with
    inputs := fn.inputs.map (fun (n, τ) => (n, mapLTy f τ))
    output := mapLTy f fn.output
    body := fn.body.map (mapExprTys f)
    axioms := fn.axioms.map (mapExprTys f)
    preconditions := fn.preconditions.map (fun p => { p with expr := mapExprTys f p.expr })
    measure := fn.measure.map (mapExprTys f) }

/-- `mapTy` over a datatype block. It rewrites the type of each field of each
    constructor. -/
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

/-- `mapTy` over a Core command. It rewrites the type annotation of a `var` and each
    expression. -/
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
/-- `mapTy` over a statement: its command, and each nested body. A `.typeDecl` holds a
    `TypeConstructor`, which is a name and a number of parameters, and it therefore holds
    no type to rewrite. -/
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

/-- `mapStmtTys` over a list of statements. -/
def mapStmtsTys (f : LMonoTy → LMonoTy) : List Statement → List Statement
  | [] => []
  | s :: rest => mapStmtTys f s :: mapStmtsTys f rest
end

/-- `mapTy` over a procedure: the signatures in the header, the checks in the
    specification, and a structured body. The function does not change a `.cfg` body,
    because the generator makes none and only `StructuredToUnstructured` does. -/
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

    The function also rewrites the *body* of an alias declaration. This matters for the
    direction that normalizes, which rewrites `A` to `τ`. After that rewrite the program
    holds `type A := τ;`, and not the vacuous `type A := A;` that a rewrite of the head
    alone gives. -/
def mapDeclTys (f : LMonoTy → LMonoTy) : Decl → Decl
  | .type (.con tc) md => .type (.con tc) md
  | .type (.syn ts) md => .type (.syn { ts with type := mapTy f ts.type }) md
  | .type (.data block) md => .type (.data (mapBlockTys f block)) md
  | .ax a md => .ax { a with e := mapExprTys f a.e } md
  | .distinct n es md => .distinct n (es.map (mapExprTys f)) md
  | .proc p md => .proc (mapProcTys f p) md
  | .func fn md => .func (mapFuncTys f fn) md
  | .recFuncBlock fns md => .recFuncBlock (fns.map (mapFuncTys f)) md

/-- `mapTy` over each type in a program. -/
def mapProgramTys (f : LMonoTy → LMonoTy) (p : Program) : Program :=
  { p with decls := p.decls.map (mapDeclTys f) }

/-! ## How the module adds an alias -/

/-- The ground types that can receive an alias, in the order that the code tries them.

    Only a *ground* type is a candidate, which is a type with no type variable. An alias
    for a type that holds a variable needs type parameters, `TEnv.addTypeAlias` needs
    `freeVars` to equal `typeArgs`, and a rewrite of such a type can capture a variable. A
    base type comes first, because it occurs in the most positions and an alias for it
    therefore exercises the most of the checker.

    The list is fixed, and the code does not collect it from the program. What matters is
    that the chosen type *occurs*, and `occursIn` decides that exactly. A fixed list also
    keeps the choice deterministic for one program, and that is what lets the shrinker
    reproduce a counterexample. -/
def candidateAliasTys : List LMonoTy :=
  [.bool, .int, .string, .real,
   .bitvec 1, .bitvec 8, .bitvec 16, .bitvec 32, .bitvec 64,
   .tcons "Sequence" [.int], .tcons "Map" [.int, .int]]

/-- A type name that no generated program can declare. Each generated name is a legal bare
    Core identifier. This name starts with `$__`, and the `startChars` set of
    `genIdentName` can give a `$` and then identifier characters, but it cannot give the
    two characters `__` after a `$`. `mapProgramTys` also inserts this name only inside
    `occursIn`, and it removes the name again. -/
private def probeTy : LMonoTy := .tcons "$__aliasProbe" []

/-- Whether `τ` occurs in `p`. The function decides this by a *rewrite*: it replaces each
    occurrence with a probe type, and it then tests whether the program changed. It
    therefore uses the same traversal as the rewrite itself, and the two notions of an
    occurrence and of a rewrite cannot disagree. A separate function that collects the
    types is a second traversal, which can differ from the first and can then pick a type
    that the rewrite touches nowhere.

    The comparison uses the printed program, because a `Core.Program` holds arrays of
    `MetaData` and those arrays have no `BEq` instance. -/
def occursIn (τ : LMonoTy) (p : Program) : Bool :=
  (Std.format (mapProgramTys (fun t => if t == τ then probeTy else t) p)).pretty
    != (Std.format p).pretty

/-! ### Why the candidates are *primitive* types only

A type name that the program declares itself, such as a monomorphic datatype or a nullary
abstract type, is an attractive candidate. An alias for such a name puts the alias in
front of the vocabulary of derived functions, and not only in front of `int`. These
candidates are absent, because the alias declaration then needs a *position*. The fold of
Core reads the declarations in order, so `type A := T;` for a `T` that the program
declares can come only after the declaration of `T`, and the rewrite can then touch only
the declarations after it. An alias for a *primitive* type needs no such argument: the
alias comes first and the rewrite is total, which is the strongest form of the test. The
smaller coverage is a deliberate trade, and the suite counts a program whose types are all
its own declarations as a skip and not as a pass. -/

/-- A name for the new alias that is fresh for the program. The name is longer than each
    name that the program declares, and `DatatypeGen.fallbackName` uses the same argument
    about the length. -/
def freshAliasName (p : Program) : String :=
  let names := p.getNames.map (·.name)
  indexedFreshName (DatatypeGen.maxNameLength names) 0

/-- Adds an alias to `p`. It picks the first ground type `τ` that `p` mentions, it adds
    `type A := τ;` as the first declaration, and it rewrites each occurrence of `τ` to
    `A`. The result is `(A, τ, p')`. The result is `none` when `p` mentions no ground type,
    which means that `p` is fully polymorphic, and the suite counts such a draw as a skip.

    The alias declaration comes **first**, so that it is in scope at each use. The fold of
    Core reads the declarations in order, so an alias that a declaration uses before the
    alias declaration is a name that the checker cannot resolve, and that is not a test of
    resolution. -/
def introduceAlias (p : Program) : Option (String × LMonoTy × Program) :=
  match candidateAliasTys.find? (occursIn · p) with
  | none => none
  | some τ =>
    let a := freshAliasName p
    let aliasTy : LMonoTy := .tcons a []
    let rewritten := mapProgramTys (fun t => if t == τ then aliasTy else t) p
    let decl : Decl := .type (.syn { name := a, typeArgs := [], type := τ }) .empty
    some (a, τ, { rewritten with decls := decl :: rewritten.decls })

/-- Rewrites `A` back to `τ` everywhere. This is the *eager* resolution of the alias that
    `introduceAlias` added. It is also the function that normalizes both sides of the
    comparison of the obligations, so that a difference cannot be a difference of spelling.

    The expansion is a substitution, and it does not call `LMonoTy.resolveAliases`. This
    keeps the claim a claim about the behaviour of *Strata*. If the eager path used the
    resolver of the checker, a defect in that resolver would appear on both sides and the
    two would cancel. `A` is nullary and `τ` is ground, so the substitution gives exactly
    the result that `tconsAliasSimple` in the resolver computes. -/
def expandAlias (a : String) (τ : LMonoTy) (p : Program) : Program :=
  mapProgramTys (fun t => if t == .tcons a [] then τ else t) p

/-! ## The two properties -/

/-- Whether the type checker of Strata accepts `p`. -/
private def accepts (p : Program) : Bool :=
  match Core.typeCheck Core.VerifyOptions.quiet p with
  | .ok _ => true
  | .error _ => false

/-- The message that the type checker gives for `p`, or `none` when the checker accepts `p`.
    Only the report of a counterexample uses it. -/
def rejectionMessage (p : Program) : Option String :=
  match Core.typeCheck Core.VerifyOptions.quiet p with
  | .ok _ => none
  | .error m => some (toString (m.format none))

/-- **Eager and incremental resolution of an alias agree on acceptance.**

    Take a generated program `p`, and let `p'` be `p` with one of its ground types replaced
    by a fresh alias, which is the work of `introduceAlias`. Then:

    * the *incremental* path is `typeCheck p'`. The checker meets the alias declaration in
      its fold, and it resolves each later use itself.
    * the *eager* path is `typeCheck (expandAlias … p')`. Each use of the alias is expanded
      first, so the checker never sees the alias in a use position.

    The two paths must agree. The property is vacuously `true` when `p` mentions no ground
    type. It also does **not** have the type check of `p` itself as a condition, and this is
    deliberate. Many generated programs reach a documented gap in completeness, and an alias
    must be transparent for those programs too. What the property forbids is one path that
    accepts where the other path rejects. -/
def checkAliasAcceptanceAgrees (p : Program) : Bool :=
  match introduceAlias p with
  | none => true
  | some (a, τ, p') => accepts p' == accepts (expandAlias a τ p')

/-- **Eager and incremental resolution of an alias give the same proof obligations.** This is
    the half about evaluation. The oracle is the symbolic evaluator of Strata, which is
    `toCoreProofObligationProgram` in the `symbolicEval` phase of `corePipelinePhases`. The
    comparison therefore covers the verification conditions that a real run receives.

    `expandAlias` normalizes both sides before the comparison. The output of the incremental
    path still writes the alias in its annotations, and a difference of spelling is not a
    difference of meaning.

    Three screens apply. Without them, the comparison gives a failure where it makes no
    claim:

    * `p` mentions no ground type, so there is nothing to test.
    * `programHasLoop` holds. The symbolic evaluator **panics** on a loop and it returns no
      `.error`, so this screen must come before the call.
    * One of the two paths does not type check. It then has no obligations to compare, and
      `checkAliasAcceptanceAgrees` covers that disagreement. -/
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

/-- Whether this program gives anything to the two properties for alias resolution. It does
    so when it mentions a ground type, because an alias for that type can then exist. The
    suite reports this value as a statistic for coverage. If the value is rarely `true`, then
    the properties for an alias are mostly vacuous. -/
def aliasIntroducible (p : Program) : Bool := (introduceAlias p).isSome

/-- Whether the property for the *obligations* compares the program that holds the new alias.
    It does so when both paths accept the program and the program holds no loop. This is the
    second statistic for coverage. -/
def aliasObligationsCompared (p : Program) : Bool :=
  match introduceAlias p with
  | none => false
  | some (a, τ, p') =>
    let pEager := expandAlias a τ p'
    !(programHasLoop p' || programHasLoop pEager)
      && accepts p' && accepts pEager
      && (symbolicObligations p').isSome && (symbolicObligations pEager).isSome

end StrataGenerators.AliasResolution
