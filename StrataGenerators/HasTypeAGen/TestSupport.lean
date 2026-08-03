import StrataGenerators.HasTypeAGen.Defs
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.IntBoolFactory
import Plausible

open Lambda

/-!
# Shared test support for the `HasTypeA` generator

Utilities shared between the LSpec property suite and the Tyche panels (both in
the merged `TestMain` driver): the default free-variable context, the operator
context from `IntBoolFactory`, the evaluator wrapper, and the value predicate.
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

/-- The `IntBoolFactory` instantiated at our parameter types. Provides
    integer arithmetic (Add, Sub, Mul, ...), comparisons (Lt, Le, ...),
    and boolean operations (And, Or, Not, ...). -/
def intBoolFactory : Factory LExprParams' :=
  @IntBoolFactory (T := LExprParams') ⟨()⟩ ⟨()⟩

/-- Monomorphic operators from Strata's Core.Factory, listed by
    (name, curried type). Used for the Indir generation rule. -/
def coreMonoOps : OpCtx :=
  -- Integer arithmetic
  [ ("Int.Add", .arrow .int (.arrow .int .int))
  , ("Int.Sub", .arrow .int (.arrow .int .int))
  , ("Int.Mul", .arrow .int (.arrow .int .int))
  , ("Int.Div", .arrow .int (.arrow .int .int))
  , ("Int.Mod", .arrow .int (.arrow .int .int))
  , ("Int.Neg", .arrow .int .int)
  -- Integer comparisons
  , ("Int.Lt", .arrow .int (.arrow .int .bool))
  , ("Int.Le", .arrow .int (.arrow .int .bool))
  , ("Int.Gt", .arrow .int (.arrow .int .bool))
  , ("Int.Ge", .arrow .int (.arrow .int .bool))
  -- Real arithmetic
  , ("Real.Add", .arrow .real (.arrow .real .real))
  , ("Real.Sub", .arrow .real (.arrow .real .real))
  , ("Real.Mul", .arrow .real (.arrow .real .real))
  , ("Real.Div", .arrow .real (.arrow .real .real))
  , ("Real.Neg", .arrow .real .real)
  -- Real comparisons
  , ("Real.Lt", .arrow .real (.arrow .real .bool))
  , ("Real.Le", .arrow .real (.arrow .real .bool))
  , ("Real.Gt", .arrow .real (.arrow .real .bool))
  , ("Real.Ge", .arrow .real (.arrow .real .bool))
  -- Boolean operations
  , ("Bool.And", .arrow .bool (.arrow .bool .bool))
  , ("Bool.Or", .arrow .bool (.arrow .bool .bool))
  , ("Bool.Implies", .arrow .bool (.arrow .bool .bool))
  , ("Bool.Equiv", .arrow .bool (.arrow .bool .bool))
  , ("Bool.Not", .arrow .bool .bool)
  -- String operations
  , ("Str.Length", .arrow .string .int)
  , ("Str.Concat", .arrow .string (.arrow .string .string))
  , ("Str.ToRegEx", .arrow .string .regex)
  , ("Str.InRegEx", .arrow .string (.arrow .regex .bool))
  , ("Str.PrefixOf", .arrow .string (.arrow .string .bool))
  , ("Str.SuffixOf", .arrow .string (.arrow .string .bool))
  -- Regex operations
  , ("Re.AllChar", .regex)
  , ("Re.All", .regex)
  , ("Re.None", .regex)
  , ("Re.Star", .arrow .regex .regex)
  , ("Re.Plus", .arrow .regex .regex)
  , ("Re.Comp", .arrow .regex .regex)
  , ("Re.Concat", .arrow .regex (.arrow .regex .regex))
  , ("Re.Union", .arrow .regex (.arrow .regex .regex))
  , ("Re.Inter", .arrow .regex (.arrow .regex .regex))
  , ("Re.Range", .arrow .string (.arrow .string .regex))
  ]

/-- Polymorphic operators from Strata's Core.Factory. Used for the
    IndirPoly generation rule (Pałka et al. 2011, Section 4). -/
def corePolyOps : PolyOpCtx :=
  -- Identity and Church booleans
  [ ("id", .forAll ["a"] (.arrow (.ftvar "a") (.ftvar "a")))
  , ("churchTrue", .forAll ["a", "b"] (.arrow (.ftvar "a") (.arrow (.ftvar "b") (.ftvar "a"))))
  , ("churchFalse", .forAll ["a", "b"] (.arrow (.ftvar "a") (.arrow (.ftvar "b") (.ftvar "b"))))
  -- Map operations
  , ("const", .forAll ["k", "v"] (.arrow (.ftvar "v") (.map (.ftvar "k") (.ftvar "v"))))
  , ("select", .forAll ["k", "v"] (.arrow (.map (.ftvar "k") (.ftvar "v")) (.arrow (.ftvar "k") (.ftvar "v"))))
  , ("update", .forAll ["k", "v"] (.arrow (.map (.ftvar "k") (.ftvar "v")) (.arrow (.ftvar "k") (.arrow (.ftvar "v") (.map (.ftvar "k") (.ftvar "v"))))))
  -- Sequence operations
  , ("Sequence.length", .forAll ["a"] (.arrow (.seq (.ftvar "a")) .int))
  , ("Sequence.empty", .forAll ["a"] (.seq (.ftvar "a")))
  , ("Sequence.append", .forAll ["a"] (.arrow (.seq (.ftvar "a")) (.arrow (.seq (.ftvar "a")) (.seq (.ftvar "a")))))
  , ("Sequence.select", .forAll ["a"] (.arrow (.seq (.ftvar "a")) (.arrow .int (.ftvar "a"))))
  , ("Sequence.build", .forAll ["a"] (.arrow (.ftvar "a") (.seq (.ftvar "a"))))
  , ("Sequence.update", .forAll ["a"] (.arrow (.seq (.ftvar "a")) (.arrow .int (.arrow (.ftvar "a") (.seq (.ftvar "a"))))))
  , ("Sequence.contains", .forAll ["a"] (.arrow (.seq (.ftvar "a")) (.arrow (.ftvar "a") .bool)))
  , ("Sequence.take", .forAll ["a"] (.arrow (.seq (.ftvar "a")) (.arrow .int (.seq (.ftvar "a")))))
  , ("Sequence.drop", .forAll ["a"] (.arrow (.seq (.ftvar "a")) (.arrow .int (.seq (.ftvar "a")))))
  -- `Sequence.map : ∀α β. (α → β) → Sequence<α> → Sequence<β>`. When the target
  -- type is `Sequence<β>`, unification fixes `β` but leaves `α` undetermined, so
  -- the IndirPoly rule must *sample* a concrete type for `α` from the generable
  -- types (Pałka et al. 2011, §4) — the same `map`-style example discussed there.
  , ("Sequence.map", .forAll ["a", "b"]
      (.arrow (.arrow (.ftvar "a") (.ftvar "b"))
        (.arrow (.seq (.ftvar "a")) (.seq (.ftvar "b")))))
  ]

/-- The precondition-bearing ("partial") monomorphic Core operators, layered on
    top of `coreMonoOps`. Each `Int.Safe*` operator computes the same value as its
    total counterpart (`Int.Div`, `Int.Mod`, …) but carries a `y ≠ 0` precondition
    in `Core.Factory` (see `intSafeDivFunc` et al. in Strata's `IntBoolFactory`), so
    a call to one produces a well-formedness obligation for `PrecondElim` to
    discharge. This context is handed to `genProcedure` in place of the total-only
    `coreMonoOps` so that generated procedures actually exercise the
    precondition-elimination pass rather than running it as a no-op. All four names
    resolve in `Core.Factory`, so the obligations are real; the annotation-driven
    typing relation makes generation with these entries sound regardless. -/
def corePartialOps : OpCtx :=
  coreMonoOps ++
  [ ("Int.SafeDiv",  .arrow .int (.arrow .int .int))
  , ("Int.SafeMod",  .arrow .int (.arrow .int .int))
  , ("Int.SafeDivT", .arrow .int (.arrow .int .int))
  , ("Int.SafeModT", .arrow .int (.arrow .int .int)) ]

-- ── Evaluator ───────────────────────────────────────────────────────────

/-- An evaluation state with `IntBoolFactory` loaded. Operators like `Int.Add`
    will reduce when applied to concrete arguments. -/
def intBoolState : LState LExprParams' :=
  { state := [],
    config := { factory := intBoolFactory,
                fuel := 200,
                usedNames := {} } }

/-- Evaluate an expression with the given fuel using `IntBoolFactory`.
    Operators reduce when applied to constants; free variables are irreducible. -/
def eval (fuel : Nat) (e : LExpr') : LExpr' :=
  (LExpr.evalWithLState fuel intBoolState e).fst

/-- Check whether an expression is a canonical value under `IntBoolFactory`. -/
def isValue (e : LExpr') : Bool :=
  LExpr.isCanonicalValue intBoolState.config.factory e

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

/-- `LContext` with `intBoolFactory` and all generator-relevant known types. -/
def resolveLContext : Lambda.LContext LExprParams' :=
  { Lambda.LContext.default with
    functions := intBoolFactory,
    knownTypes := resolveKnownTypes }

/-- The operator context of `intBoolFactory`, used to *generate* the terms whose
    types are erased and re-inferred by the resolve-after-erase property. -/
def intBoolOpCtx : OpCtx := factoryOps intBoolFactory

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

/-- Re-infer the type of `expr` after erasing all annotations. `none` when
    `resolve` errors (e.g. on a fully-erased quantifier whose body type is the
    bound variable — an incompleteness of `resolve`, not a soundness bug). -/
def resolveErasedTy (expr : LExpr') : Option LMonoTy :=
  match LExpr.resolve resolveLContext Lambda.TEnv.default (eraseAllTypes expr) with
  | .ok (resolved, _) => some resolved.toLMonoTy
  | .error _ => none

/-- Resolve-after-erase property: after erasing all annotations, `resolve`
    succeeds and infers a type the generation type `expectedTy` is an instance of.
    (A `resolve` failure is scored as a counterexample — see `resolveErasedTy`.) -/
def checkResolveAfterErase (expr : LExpr') (expectedTy : LMonoTy) : Bool :=
  match resolveErasedTy expr with
  | some inferred => isInstanceOf expectedTy inferred
  | none => false

-- ── Shared structural expression shrinker ─────────────────────────────────
--
-- The single expression shrinker reused by *every* term-level shrinker in the
-- suite (`TypedExpr`/`ClosedTypedExpr`/`ResolveTypedExpr` in `TestScaffold`, and
-- the command / statement / function shrinkers). It only proposes *structurally
-- smaller* expressions; the caller is responsible for keeping candidates
-- well-typed (typically by re-`typeCheck`ing and rejecting failures), so a shrunk
-- expression may legitimately change type — e.g. `(f x) : bool` shrinks toward its
-- subterm `f : int -> bool`.

/-- All ways to drop exactly one element of a list. Shared by every sequence
    shrinker in the suite (command / statement / function). -/
def dropEach {α} : List α → List (List α)
  | [] => []
  | x :: xs => xs :: (x :: ·) <$> dropEach xs

/-- For terms that don't involve top-level binders (e.g. `lam` or `quant`),
    extract their immediate sub-terms. Excludes bare `.op` nodes since
    unapplied operators (interpreted functions) are trivial degenerate results
    (they aren't values and can't reduce without arguments). -/
def immediateSubtermsWithoutBinders (e : LExpr') : List LExpr' :=
  (match e with
  | .app _ fn arg => [fn, arg]
  | .ite _ c t e => [c, t, e]
  | .eq _ e1 e2 => [e1, e2]
  | _ => []).filter fun
    | .op _ _ _ => false
    | _ => true

/-- Structurally shrink an `LExpr'`.
    - For terms involving binders (`abs`/`quant`), we shrink the body but keep the
      binder, so the shrunken term stays well-scoped.
    - For terms without binders, we also extract their top-level subterms.
    - For integer constants we defer to the default `Nat`/`Int` shrinker.
    Candidates are structurally smaller but not re-typechecked here; callers filter. -/
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
