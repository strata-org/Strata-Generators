import StrataGenerators.HasTypeAGen.Core
import Strata.DL.Lambda.Factory

open Lambda RandomChoice

/-!
# Generator definitions for well-typed `LExpr`s (lightweight, no Mathlib)

This file re-exports the core generator definitions from `Core.lean` and adds
`Factory`-accepting wrappers.

The full `HasTypeAGen` module re-exports everything here plus soundness/completeness proofs.
-/

-- Re-export everything from Core
export ArbNat (Nat.arbitrary)

-- ── Factory conversion ──────────────────────────────────────────────

/-- Extract the flat operator list from a `Factory` by computing the curried
    type of each operation (inputs → output). -/
def factoryOps (F : @Factory LExprParams') : OpCtx :=
  F.toArray.toList.filterMap fun f =>
    let inputTys := f.inputs.values
    let outputTys := LMonoTy.destructArrow f.output
    let ty := match inputTys with
      | [] => f.output
      | ity :: irest => LMonoTy.mkArrow ity (irest ++ outputTys)
    some (f.name.name, ty)

-- ── Factory-accepting wrappers ──────────────────────────────────────

/-- Generate a well-typed `LExpr` using a `Factory` for operators.
    This is a convenience wrapper around `genLExpr` that converts the factory
    to an `OpCtx` via `factoryOps`. Uses the Indir and IndirPoly rules to
    generate fully-applied operator applications. -/
def genLExprWithFactory [Gen G] (fctx : FVarCtx) (F : @Factory LExprParams')
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (pctx : PolyOpCtx := []) : G LExpr' :=
  genLExpr fctx (factoryOps F) pctx tvars bctx depth τ

/-- Generate a well-typed closed expression (no free variables) using the
    given factory for operators. -/
def genClosedLExprWithFactory [Gen G] (F : @Factory LExprParams')
    (tvars : List TyIdentifier) (depth : Nat)
    (pctx : PolyOpCtx := []) : G LExpr' := do
  let τ ← genLMonoTy tvars depth
  genLExprWithFactory [] F tvars [] depth τ pctx

/-- Generate a well-typed `LExpr` using explicit operator and polymorphic
    operator contexts. This is a convenience wrapper around `genLExpr` that
    avoids requiring a `Factory` value. -/
def genLExprWithOps [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx)
    (depth : Nat) (τ : LMonoTy) : G LExpr' :=
  genLExpr fctx octx pctx tvars bctx depth τ
