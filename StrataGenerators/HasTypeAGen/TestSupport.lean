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
  | .bitvec n => s!"bv{n}"
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
  [("x", .bool), ("f", .arrow .int .bool), ("n", .int)]

/-- The `IntBoolFactory` instantiated at our parameter types. Provides
    integer arithmetic (Add, Sub, Mul, ...), comparisons (Lt, Le, ...),
    and boolean operations (And, Or, Not, ...). -/
def intBoolFactory : Factory LExprParams' :=
  @IntBoolFactory (T := LExprParams') ⟨()⟩ ⟨()⟩

/-- Polymorphic operators for exercising the IndirPoly generator rule.
    - `id : ∀ a. a → a`
    - `churchTrue : ∀ a b. a → b → a`
    - `churchFalse : ∀ a b. b → a → b` -/
def defaultPolyOps : PolyOpCtx :=
  [ ("id", .forAll ["a"] (.arrow (.ftvar "a") (.ftvar "a")))
  , ("churchTrue", .forAll ["a", "b"] (.arrow (.ftvar "a") (.arrow (.ftvar "b") (.ftvar "a"))))
  , ("churchFalse", .forAll ["a", "b"] (.arrow (.ftvar "a") (.arrow (.ftvar "b") (.ftvar "b"))))
  ]

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
  LExpr.eval fuel intBoolState e

/-- Check whether an expression is a canonical value under `IntBoolFactory`. -/
def isValue (e : LExpr') : Bool :=
  LExpr.isCanonicalValue intBoolState.config.factory e
