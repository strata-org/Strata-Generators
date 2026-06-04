## Takeaways from getting Claude to synthesize a correct `LExpr` generator

The Claude-synthesized generator inlines the definitions of all sub-generators, so the sub-generator for producing abstractions is repeated several times throughout the body of the parent generator. When we prompt Claude to create helper functions to avoid code duplication (i.e. separate functions for generating Abs, App etc.), it struggles with updating the proofs due to mutual recursion between the different sub-generators, and the solution was to define helpers that take in auxiliary generators as arguments, e.g.:

```lean
-- Generates an application, where the `genTy` and `genExpr` arguments are generators that `genApp` invokes
def genApp [Gen G] (genTy : G LMonoTy) (genExpr : LMonoTy → G LExpr') (τ : LMonoTy) : G LExpr' := do
  let τ' ← genTy
  let arg ← genExpr τ'
  let fn ← genExpr (.arrow τ' τ)
  pure (.app () fn arg)

-- The parent generator (genLExpr) then invokes genApp by passing it a partially-applied recursive call
-- (e.g. the `genLExpr Γ` subterm below)
... genApp genTy (genLExpr Γ) τ
````