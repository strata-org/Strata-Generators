import StrataGenerators.HasTypeAGen.Defs
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.IntBoolFactory

open Lambda

/-!
# Shared test support for the `HasTypeA` generator

Utilities shared between `PlausibleTestMain` and `TycheMain`: the default
free-variable context, the operator context from `IntBoolFactory`, the
evaluator wrapper, and the value predicate.
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

/-- Combined operator context for generation: monomorphic Core ops. -/
def coreOpCtx : OpCtx := coreMonoOps

/-- Polymorphic operators for exercising the IndirPoly generator rule.
    Includes Map, Sequence, and identity/Church combinator operators. -/
def defaultPolyOps : PolyOpCtx := corePolyOps

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
