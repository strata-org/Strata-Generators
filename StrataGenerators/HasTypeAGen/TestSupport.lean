import StrataGenerators.HasTypeAGen.Defs
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprT
import Strata.Languages.Core.Factory
import Plausible

open Lambda

/-!
# Shared test support for the `HasTypeA` generator

Utilities shared between the LSpec property suite and the Tyche panels (both in
the merged `TestMain` driver): the default free-variable context, the operator
context from Strata's full `Core.Factory`, the evaluator wrapper, and the value
predicate.
-/

-- ── Pretty-printers ────────────────────────────────────────────────────

/-- Pretty-print a monotype with `→` for arrows. Left-hand sides of arrows
    are parenthesized when they are themselves arrow types (standard convention
    for right-associative `→`). -/
partial def ppType : LMonoTy → String
  | .arrow τ₁ τ₂ =>
    let lhs := match τ₁ with
      | .arrow _ _ => s!"({ppType τ₁})"
      | _ => ppType τ₁
    s!"{lhs} -> {ppType τ₂}"
  | .ftvar name => name
  | .bool => "bool"
  | .int => "int"
  | .real => "real"
  | .string => "string"
  | .bitvec n => s!"bv<{n}>"
  | .map k v => s!"Map<{ppType k}, {ppType v}>"
  | .seq a => s!"Sequence<{ppType a}>"
  | .tcons name tys =>
    if tys.isEmpty then name
    else s!"({name} {" ".intercalate (tys.map ppType)})"

/-- Pretty-print an LExpr with minimal parenthesization.
    Precedence levels: 0 = top/binder body, 1 = if/eq, 2 = application fn, 3 = application arg -/
def ppExpr (e : LExpr') (prec : Nat := 0) : String :=
  let wrap (p : Nat) (s : String) := if prec ≥ p then s!"({s})" else s
  match e with
  | .const _ (.boolConst b) => s!"#{b}"
  | .const _ (.intConst i) => s!"#{i}"
  | .const _ (.strConst s) => s!"\"{s}\""
  | .const _ (.realConst r) => s!"#{r}"
  | .const _ (.bitvecConst _ b) => s!"#{b.toNat}"
  | .op _ o _ => s!"{o.name}"
  | .bvar _ i => s!"%{i}"
  | .fvar _ x ty => match ty with
    | some t => s!"{x.name} : {ppType t}"
    | none => s!"{x.name}"
  | .abs _ _ ty body => wrap 1 <| match ty with
    | some t => s!"λ{ppType t}. {ppExpr body 0}"
    | none => s!"λ_. {ppExpr body 0}"
  | .quant _ .all _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∀{ppType t}. {ppExpr body 0}"
    | none => s!"∀_. {ppExpr body 0}"
  | .quant _ .exist _ ty _ body => wrap 1 <| match ty with
    | some t => s!"∃{ppType t}. {ppExpr body 0}"
    | none => s!"∃_. {ppExpr body 0}"
  | .app _ fn arg => wrap 3 <| s!"{ppExpr fn 2} {ppExpr arg 3}"
  | .ite _ c t e => wrap 1 <| s!"if {ppExpr c 0} then {ppExpr t 0} else {ppExpr e 0}"
  | .eq _ e₁ e₂ => wrap 2 <| s!"{ppExpr e₁ 2} == {ppExpr e₂ 2}"

-- ── Default contexts ────────────────────────────────────────────────────

/-- A fixed free-variable context providing variables of common types.
    Used by both the Plausible and Tyche test harnesses to exercise the
    `fvar` generation path. -/
def defaultFCtx : FVarCtx :=
  [ ("x", .bool), ("f", .arrow .int .bool), ("n", .int)
  , ("s", .string), ("r", .regex), ("m", .map .int .bool)
  , ("q", .seq .int) ]

/-- The full `Core.Factory` of Strata, at the parameter types of this package. It is the **one source of
    truth** for the vocabulary of the operators of each harness here.

    Each harness draws its operators from this one factory, through `coreOpCtx`
    below. Therefore a harness cannot drift from the operators that Core truly
    defines, and a new operator in `Core.Factory` reaches each harness with no
    change here.

    This factory replaces `IntBoolFactory`, which held the operators on `int` and
    `bool` only. `IntBoolFactory` gave a vocabulary of 21 operators, against 310
    here, and it excluded every operator on `string`, `real`, `regex` and
    `bitvec`. A generator over `IntBoolFactory` therefore cannot build a term such
    as `Str.Length "é"`, and each property about those types passes vacuously.

    `Core.Factory` lives at `Core.CoreLParams`, which is
    `⟨CoreExprMetadata, Unit⟩ = ⟨Unit, Unit⟩` and therefore definitionally equal to
    `LExprParams'`. Thus the factory needs no instantiation, unlike
    `IntBoolFactory`, which took the two metadata values as arguments. -/
def coreFactory : Factory LExprParams' := Core.Factory

/-- The operators for the procedure generator, including the ones that carry a
    precondition.

    Each `Int.Safe*` operator computes the same value as its total counterpart,
    such as `Int.Div` or `Int.Mod`, but it carries a `y ≠ 0` precondition in
    `Core.Factory`. Therefore a call to one gives a well-formedness obligation for
    `PrecondElim` to discharge, and a generated procedure exercises the pass that
    eliminates a precondition instead of running it as a no-op.

    This context is the same as `coreMonoOps`. `coreMonoOps` comes from `Core.Factory`, which defines each
    `Int.Safe*` operator, so this context needs no separate entry for one of them.

    The definition stays as a separate name, and each call site for procedures
    keeps it. The name records the *intent* that a procedure body must be able to
    reach an operator with a precondition. If a future change narrows
    `coreMonoOps`, this is the definition to widen again. -/
def corePartialOps : OpCtx := coreMonoOps

-- ── Evaluator ───────────────────────────────────────────────────────────

/-- A state for the evaluator, with the full `coreFactory` in it. An operator such as `Int.Add` reduces when it
    has concrete arguments. An operator on a string, on a real number and on a bitvector also reduces. -/
def coreState : LState LExprParams' :=
  { state := [],
    config := { factory := coreFactory,
                fuel := 200,
                usedNames := {} } }

/-- Evaluate an expression with the given fuel over `coreFactory`. An operator
    reduces when it has constant arguments. A free variable is irreducible. -/
def eval (fuel : Nat) (e : LExpr') : LExpr' :=
  (LExpr.evalWithLState fuel coreState e).fst

/-- Report whether an expression is a canonical value over `coreFactory`. -/
def isValue (e : LExpr') : Bool :=
  LExpr.isCanonicalValue coreState.config.factory e

-- ── Expression property checks (shared by both harnesses) ────────────────
-- The pass/fail decision for each expression-generator property lives here so
-- the Plausible assertion and the Tyche panel evaluate the *same* function.

/-- Preservation (closed terms): a well-typed closed term stays well-typed at the
    same type after evaluation. `expectedTy` is the type it was generated at. -/
def checkPreservation (expr : LExpr') (expectedTy : LMonoTy) : Bool :=
  LExpr.typeCheck (T := LExprParams') [] (eval 100 expr) == some expectedTy

/-- Progress (closed terms): a well-typed closed term is either already a value
    or takes a step under evaluation. -/
def checkProgress (expr : LExpr') : Bool :=
  isValue expr || !(expr == eval 100 expr)

/-- Fvar preservation: evaluation introduces no free variables that were not
    already present in the input term. -/
def checkFvarsPreserved (expr : LExpr') : Bool :=
  let inputFvars := LExpr.collectFvarNames expr
  (LExpr.collectFvarNames (eval 100 expr)).all (· ∈ inputFvars)

-- ── Resolve-after-erasure property (shared by both harnesses) ─────────────

/-- Known types covering all base types the generator can produce. Required for
    `LExpr.resolve` to reconstruct arrow/Map/Seq aliases after erasure. -/
def resolveKnownTypes : Lambda.KnownTypes :=
  open Lambda.LTy.Syntax in
  Lambda.makeKnownTypes ([t[∀a b. %a → %b],
    t[bool], t[int], t[string], t[real], t[regex],
    t[∀n. bitvec n],
    t[∀a b. Map %a %b],
    t[∀a. Sequence %a]].map (fun k => k.toKnownType!))

/-- `LContext` with `coreFactory` and each known type that the generator needs. -/
def resolveLContext : Lambda.LContext LExprParams' :=
  { Lambda.LContext.default with
    functions := coreFactory,
    knownTypes := resolveKnownTypes }

/-- The operator context of `coreFactory`: each operator that Strata's Core truly
    defines, as a pair of a name and a curried type.

    This context is the one vocabulary that every harness generates over. It holds
    310 operators, against 21 for the earlier `intBoolOpCtx`, and it adds every
    operator on `string`, `real`, `regex` and `bitvec`.

    `factoryOps` gives each operator its monomorphic type. An operator that is
    polymorphic in the factory therefore appears here with type variables in its
    type. The generator handles such an entry through its `ftvar` cases, and
    `corePolyOps` holds the separate *schemes* for the rules about polymorphism. -/
def coreOpCtx : OpCtx := factoryOps coreFactory

/-- Erase *all* type annotations on an `LExpr`, including the binder-type
    annotations on lambdas (`abs`) and quantifiers (`quant`). After this, no node
    carries a type, so `resolve` must reconstruct every type from scratch via
    unification. -/
def eraseAllTypes : LExpr' → LExpr'
  | .const m c => .const m c
  | .op m o _ => .op m o none
  | .fvar m x _ => .fvar m x none
  | .bvar m i => .bvar m i
  | .abs m name _ e => .abs m name none (eraseAllTypes e)
  | .quant m qk name _ tr e => .quant m qk name none (eraseAllTypes tr) (eraseAllTypes e)
  | .app m e1 e2 => .app m (eraseAllTypes e1) (eraseAllTypes e2)
  | .ite m c t f => .ite m (eraseAllTypes c) (eraseAllTypes t) (eraseAllTypes f)
  | .eq m e1 e2 => .eq m (eraseAllTypes e1) (eraseAllTypes e2)

/-- Whether the ground type `target` is a substitution instance of the (possibly
    more general) inferred type `inferred`. Because `target` has no free type
    variables, unifying the two can only substitute into `inferred`'s variables,
    so success exactly witnesses that `inferred` generalizes `target`. This also
    abstracts over the *names* of the fresh type variables `resolve` introduces,
    so the comparison is up to alpha-equivalence. -/
def isInstanceOf (target inferred : LMonoTy) : Bool :=
  match Lambda.Constraints.unify [(inferred, target)] Lambda.SubstInfo.empty with
  | .ok _ => true
  | .error _ => false

/-- Infer the type of `expr` again, after an erasure of each annotation. The result is `none` when `resolve`
    gives an error. One such case is a quantifier after a full erasure, whose body has the type of the bound
    variable. That case is a gap in the completeness of `resolve`, and not a defect in its soundness. -/
def resolveErasedTy (expr : LExpr') : Option LMonoTy :=
  match LExpr.resolve resolveLContext Lambda.TEnv.default (eraseAllTypes expr) with
  | .ok (resolved, _) => some resolved.toLMonoTy
  | .error _ => none

/-- The property about a resolve after an erasure. After an erasure of each annotation, `resolve` succeeds, and
    it infers a type that the type of the generation is an instance of. A failure of `resolve` counts as a
    counterexample. Read `resolveErasedTy`. -/
def checkResolveAfterErase (expr : LExpr') (expectedTy : LMonoTy) : Bool :=
  match resolveErasedTy expr with
  | some inferred => isInstanceOf expectedTy inferred
  | none => false

-- ── Shared structural expression shrinker ─────────────────────────────────
--
-- The single expression shrinker reused by *every* term-level shrinker in the
-- suite (`TypedExpr`/`ClosedTypedExpr`/`ResolveTypedExpr` in `TestScaffold`, and
-- the command / statement / function shrinkers). It only proposes *structurally
-- smaller* expression. The caller keeps each candidate well typed, usually by a second type check that rejects
-- a failure. Therefore a shrunk expression can change its type. For an example, `(f x) : bool` shrinks toward
-- its subterm `f : int -> bool`.

/-- All ways to drop exactly one element of a list. Shared by every sequence
    shrinker in the suite (command / statement / function). -/
def dropEach {α} : List α → List (List α)
  | [] => []
  | x :: xs => xs :: (x :: ·) <$> dropEach xs

/-- The immediate subterms of a term that holds no binder at its top, such as a lambda or a quantifier. The
    result holds no bare `.op` node, because an operator with no argument is a degenerate result: it is not a
    value, and it cannot reduce with no argument. -/
def immediateSubtermsWithoutBinders (e : LExpr') : List LExpr' :=
  (match e with
  | .app _ fn arg => [fn, arg]
  | .ite _ c t e => [c, t, e]
  | .eq _ e1 e2 => [e1, e2]
  | _ => []).filter fun
    | .op _ _ _ => false
    | _ => true

/-- Shrink an `LExpr'` structurally.
    - For a term with a binder, which is an `abs` or a `quant`, the function shrinks the body and keeps the
      binder, so that the shrunk term stays well scoped.
    - For a term with no binder, the function also gives each subterm at the top.
    - For an integer constant, the function calls the default shrinker for a `Nat` or for an `Int`.

    Each candidate is structurally smaller, and this function type checks none of them. The caller filters
    them. -/
partial def shrinkLExpr (e : LExpr') : List LExpr' :=
  immediateSubtermsWithoutBinders e ++
  match e with
  | .app _ fn arg =>
    (.app () · arg) <$> shrinkLExpr fn ++
    (.app () fn ·) <$> shrinkLExpr arg
  | .ite _ c t el =>
    (.ite () · t el) <$> shrinkLExpr c ++
    (.ite () c · el) <$> shrinkLExpr t ++
    (.ite () c t ·) <$> shrinkLExpr el
  | .eq _ e1 e2 =>
    (.eq () · e2) <$> shrinkLExpr e1 ++
    (.eq () e1 ·) <$> shrinkLExpr e2
  | .abs _ name ty body =>
    (.abs () name ty ·) <$> shrinkLExpr body
  | .quant _ k name ty trigger body =>
    (.quant () k name ty · body) <$> shrinkLExpr trigger ++
    (.quant () k name ty trigger ·) <$> shrinkLExpr body
  | .const _ (.intConst i) =>
    (fun i' => .const () (.intConst i')) <$> Plausible.Shrinkable.shrink i
  | _ => []
