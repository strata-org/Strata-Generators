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
    type of each operation (inputs → output).

    The curried type is built with `mkArrow'` — exactly the *generic type* form
    `OpsConsistent`/`OpsConsistentR` canonicalize each operator to
    (`mkArrow' fn.output fn.inputs.values`). Using the same builder here means the
    annotation the generator stamps on a `factoryOps`-sourced `.op` node *is*
    definitionally the operator's generic type, so no `destructArrow`/`mkArrow`
    reconciliation (nor an `ArrowSpineOK`/`FactoryOutputWF` side condition) is
    needed to see it is op-consistent. -/
def factoryOps (F : @Factory LExprParams') : OpCtx :=
  F.toArray.toList.filterMap fun f =>
    some (f.name.name, LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))

/-- Extract the polymorphic operator context from a `Factory` by recording each
    operation's full type *scheme*: quantify over the operation's type arguments,
    then curry its inputs to its output.

    This is the polymorphic analogue of `factoryOps`. Where `factoryOps` collapses
    each function to a single `LMonoTy` (losing polymorphism), `factoryPolyOps`
    keeps the `∀ typeArgs. …` scheme that the polymorphic generation rules
    (`genIndirPoly`/`findPolymorphicOps`) need. The scheme is built with the same
    `mkArrow'` builder as `factoryOps`, so an entry here is *by construction* the
    generic type of a real factory function — that is exactly the `PCtxWF F`
    well-formedness condition, discharged as a lemma rather than assumed. -/
def factoryPolyOps (F : @Factory LExprParams') : PolyOpCtx :=
  F.toArray.toList.filterMap fun f =>
    some (f.name.name,
      Lambda.LTy.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))

-- ── Factory-accepting wrappers ──────────────────────────────────────

/-- Generate a well-typed `LExpr` using a `Factory` for operators.
    This is a convenience wrapper around `genLExpr` that converts the factory
    to an `OpCtx` via `factoryOps`. Uses the Indir and IndirPoly rules to
    generate fully-applied operator applications. -/
def genLExprWithFactory [Gen G] (fctx : FVarCtx) (F : @Factory LExprParams')
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (pctx : PolyOpCtx := factoryPolyOps F) : G LExpr' :=
  genLExpr fctx (factoryOps F) pctx tvars bctx depth τ

/-- Generate a well-typed closed expression (no free variables) using the
    given factory for operators. -/
def genClosedLExprWithFactory [Gen G] (F : @Factory LExprParams')
    (tvars : List TyIdentifier) (depth : Nat)
    (pctx : PolyOpCtx := factoryPolyOps F) : G LExpr' := do
  let τ ← genLMonoTy tvars depth
  genLExprWithFactory [] F tvars [] depth τ pctx

/-- Generate a well-typed `LExpr` using explicit operator and polymorphic
    operator contexts. This is a convenience wrapper around `genLExpr` that
    avoids requiring a `Factory` value. -/
def genLExprWithOps [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx)
    (depth : Nat) (τ : LMonoTy) : G LExpr' :=
  genLExpr fctx octx pctx tvars bctx depth τ
