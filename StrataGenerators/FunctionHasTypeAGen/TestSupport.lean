import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.DL.Lambda.Denote.LExprAnnotated

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

-- ── Pretty-printing ──────────────────────────────────────────────────────

/-- Pretty-print a generated `Function` using the human-readable type/expression
    printers from `HasTypeAGen.TestSupport`, in Strata's `func` layout (with
    `∀`-quantified type args, a `decreases` measure clause, and `:=` body). -/
def ppFunction (func : Function) : String :=
  let tyArgs := if func.typeArgs.isEmpty then "" else s!"∀{", ".intercalate func.typeArgs}. "
  let inputs := func.inputs.toList.map (fun (x, ty) => s!"({x.name} : {ppType ty})")
                |> " ".intercalate
  let sig := s!"{tyArgs}{inputs} → {ppType func.output}"
  let measureStr := match func.measure with
    | some m => s!" decreases {ppExpr m}"
    | none => ""
  let bodyStr := match func.body with
    | some b => s!" := {ppExpr b}"
    | none => ";"
  s!"func {func.name.name} : {sig}{measureStr}{bodyStr}"

-- ── Generator wrappers ────────────────────────────────────────────────────

/-- Generate a single well-typed `Function` in `IO`, exercising `genFunction`
    directly. Defaults mirror the other harness wrappers (`defaultFCtx`,
    `coreOpCtx`, depth 3). -/
def genFunctionIO (fctx : FVarCtx := defaultFCtx) (octx : OpCtx := coreOpCtx)
    (depth : Nat := 3) : IO Function :=
  genFunction (G := IO) fctx octx depth
