import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.Languages.Core.FunctionType

open Lambda RandomChoice Core Imperative

/-!
# Test support for the `FunctionHasTypeAGen` generator

Provides shared utilities for property-based testing of `genFunction` (defined
in `FunctionHasTypeAGen/Core.lean`):
- Pretty-printing for generated `Function`s,
- A `Bool` reflection of Strata's `fvars_annotated_by` predicate,
- Generator wrappers for `IO` and `Plausible.Gen`.

## Why we reflect `fvars_annotated_by` locally

The predicate under test is `Lambda.fvars_annotated_by`, defined in
`Strata.DL.Lambda.Denote.Assumptions`:

```
def fvars_annotated_by [DecidableEq T.IDMeta]
    (tyMap : Map T.Identifier LMonoTy) : LExpr T.mono → Prop
  | .fvar _ name (some ty) => ∀ ty', Map.find? tyMap name = some ty' → ty = ty'
  | .fvar _ _ none         => False
  | .const _ _ | .bvar _ _ | .op _ _ _ => True
  | .app _ fn arg          => fvars_annotated_by tyMap fn ∧ fvars_annotated_by tyMap arg
  | .abs _ _ _ body        => fvars_annotated_by tyMap body
  | .ite _ c t e           => fvars_annotated_by tyMap c ∧ … ∧ …
  | .eq _ e1 e2            => fvars_annotated_by tyMap e1 ∧ fvars_annotated_by tyMap e2
  | .quant _ _ _ _ tr body => fvars_annotated_by tyMap tr ∧ fvars_annotated_by tyMap body
```

We cannot import it here. It lives in a Lean *module*-system file
(`import all`-only, no `public section`), whereas this repo's generator files
are non-`module`; Lean rejects importing the symbol into a non-`module` file.
So — exactly as the `Cmd` harness re-implements `storeWellTyped` / typechecking
rather than importing the corresponding Strata `Prop`s — we mirror the
definition as a decidable `Bool` function `fvarsAnnotatedBy`, matching the
`Prop` clause-for-clause. The only clause needing care is the annotated-`fvar`
case: `∀ ty', find? tyMap name = some ty' → ty = ty'` holds iff either
`find? tyMap name = none`, or it is `some ty'` with `ty = ty'`; both are decided
by a single `Map.find?` lookup.
-/

-- ── Bool reflection of `fvars_annotated_by` ──────────────────────────────

/-- A `Bool` reflection of `Lambda.fvars_annotated_by tyMap e` (see the module
    docstring for why this is re-implemented rather than imported).

    Every annotated free variable `(name : ty)` must be consistent with `tyMap`:
    if `name` is bound in `tyMap`, its recorded type must equal `ty`. An
    *unannotated* free variable (`.fvar _ _ none`) is unconditionally rejected
    (mirrors the `Prop`'s `False` clause). All other leaves pass; compound nodes
    recurse into every subexpression. -/
def fvarsAnnotatedBy (tyMap : Map (Identifier Unit) LMonoTy) : LExpr' → Bool
  | .fvar _ name (some ty) =>
    match Map.find? tyMap name with
    | some ty' => ty == ty'
    | none => true
  | .fvar _ _ none => false
  | .const _ _ => true
  | .bvar _ _ => true
  | .op _ _ _ => true
  | .app _ fn arg => fvarsAnnotatedBy tyMap fn && fvarsAnnotatedBy tyMap arg
  | .abs _ _ _ body => fvarsAnnotatedBy tyMap body
  | .ite _ c t e => fvarsAnnotatedBy tyMap c && fvarsAnnotatedBy tyMap t && fvarsAnnotatedBy tyMap e
  | .eq _ e1 e2 => fvarsAnnotatedBy tyMap e1 && fvarsAnnotatedBy tyMap e2
  | .quant _ _ _ _ tr body => fvarsAnnotatedBy tyMap tr && fvarsAnnotatedBy tyMap body

/-- The `FVarCtx` used to *generate* a function, viewed as the type map that its
    fvar annotations should be consistent with. `FVarCtx` is a
    `List (String × LMonoTy)`; the identifiers created by the generator are
    `⟨name, ()⟩`, so we rekey accordingly. -/
def fctxToTyMap (fctx : FVarCtx) : Map (Identifier Unit) LMonoTy :=
  fctx.map (fun (name, ty) => (⟨name, ()⟩, ty))

/-- **The property under test**, applied to a whole function: every fvar in the
    (optional) body and in the (optional) measure is annotated consistently with
    `tyMap`. Absent body/measure are a vacuous pass. -/
def functionFvarsAnnotatedBy (tyMap : Map (Identifier Unit) LMonoTy) (func : Function) : Bool :=
  (match func.body with | some b => fvarsAnnotatedBy tyMap b | none => true) &&
  (match func.measure with | some m => fvarsAnnotatedBy tyMap m | none => true)

-- Function pretty-printing now goes through Strata's own `Core.formatProgram`
-- (see `formatFunc` / `formatFuncAsProgram` in
-- `StrataGenerators.FunctionHasTypeAGen.Roundtrip`), so displays match the real
-- formatter exactly. The former hand-rolled `ppFunction` has been removed.

-- ── Generator wrappers ────────────────────────────────────────────────────

/-- Generate a single well-typed `Function` in `IO`, exercising `genFunction`
    directly. Defaults mirror the other harness wrappers (`defaultFCtx`,
    `coreOpCtx`, depth 3). -/
def genFunctionIO (fctx : FVarCtx := defaultFCtx) (octx : OpCtx := coreOpCtx)
    (depth : Nat := 3) : IO Function :=
  genFunction (G := IO) fctx octx depth

-- ── Known types and context for `Function.typeCheck` ──────────────────────

/-- Known types covering all base types + type constructors the generator can
    produce. Required for `Function.typeCheck` to resolve arrow/Map/Seq aliases. -/
def funcCheckKnownTypes : Lambda.KnownTypes :=
  open Lambda.LTy.Syntax in
  Lambda.makeKnownTypes ([t[∀a b. %a → %b],
    t[bool], t[int], t[string], t[real], t[regex],
    t[∀n. bitvec n],
    t[∀a b. Map %a %b],
    t[∀a. Sequence %a]].map (fun k => k.toKnownType!))

/-- `LContext` with `intBoolFactory` and all generator-relevant known types.
    Matches the `resolveLContext` used for expression-level tests. -/
def funcCheckContext : Lambda.LContext CoreLParams :=
  { Lambda.LContext.default with
    functions := intBoolFactory,
    knownTypes := funcCheckKnownTypes }

-- ── Function property checks (shared by both harnesses) ───────────────────

/-- Reflect `FuncHasTypeA` on a function via `LExpr.typeCheck`: the body (if any)
    types at the declared output, the measure (if any) at `int`, and the input /
    type-argument lists are duplicate-free. -/
def checkFuncHasTypeA (func : Function) : Bool :=
  let bodyOk := match func.body with
    | some b => LExpr.typeCheck (T := CoreLParams) [] b == some func.output
    | none => true
  let measureOk := match func.measure with
    | some m => LExpr.typeCheck (T := CoreLParams) [] m == some .int
    | none => true
  bodyOk && measureOk && decide (func.inputs.keys.Nodup) && decide (func.typeArgs.Nodup)

/-- `Function.typeCheck` soundness (`typeCheck_annotated_sound`): when `typeCheck`
    accepts, its output satisfies the declarative spec `FuncHasTypeA`. When
    `typeCheck` rejects (e.g. measure-without-body, which the spec allows but the
    algorithm forbids), this is a vacuous pass — the property asserts soundness,
    not completeness. -/
def checkTypeCheckAnnotatedSound (func : Function) : Bool :=
  match Function.typeCheck funcCheckContext TEnv.default func with
  | .ok (func', _) => checkFuncHasTypeA func'
  | .error _ => true

/-- Type preservation under evaluation (`Step.type_preserved` /
    `StepStar.type_preserved` / `eval_denote_sound`): if a function has a body,
    evaluating it preserves the declared output type. A bodiless function passes
    vacuously. -/
def checkFunctionBodyPreservation (func : Function) : Bool :=
  match func.body with
  | some body => LExpr.typeCheck (T := CoreLParams) [] (eval 100 body) == some func.output
  | none => true

-- ── Special-character identifier probe (shared by both harnesses) ─────────
-- The full-function round-trip bundles a name, typeargs, types, a body, etc., so
-- a failure can't be attributed to one cause. This probe isolates a single
-- generated identifier in one syntactic position at a time inside an otherwise-
-- trivial function, so a failure yields a minimal reproducer.

/-- The three syntactic positions an identifier can occupy in a `Function`. -/
inductive IdentPosition where
  | funcName
  | typeArg
  | binder
  deriving Repr, DecidableEq

def IdentPosition.label : IdentPosition → String
  | .funcName => "function-name"
  | .typeArg  => "type-arg"
  | .binder   => "binder"

/-- Build a minimal `Function` that places `name` in the given position and is
    otherwise trivial (no body, no measure, `int` output). For `typeArg`, the name
    is also referenced as the output type (`ftvar name`) so it appears in a use
    position, not just its binding. For `binder`, the single input uses the name
    as its parameter identifier at type `int`. -/
def minimalFuncWithName (pos : IdentPosition) (name : String) : Function :=
  let ident : Identifier Unit := ⟨name, ()⟩
  match pos with
  | .funcName => LFunc.mk (name := ident) (inputs := []) (output := .int)
  | .typeArg  => LFunc.mk (name := ⟨"f", ()⟩) (typeArgs := [name]) (inputs := [])
                   (output := .ftvar name)
  | .binder   => LFunc.mk (name := ⟨"f", ()⟩) (inputs := [(ident, .int)]) (output := .int)
