# Takeaways from getting Claude to synthesize a correct `LExpr` generator

## Having some knowledge of the PBT literature helps
By default, trying to generate function applications naïvely using the `App` rule is challenging, especially when the function
has multiple (more than one) argument. Consider the `App` rule and the corresponding (simplified) generator:

```
Γ ⊢ e₁ : τ' → τ      Γ ⊢ e₂ : τ'
---------------------------------- (App)
        Γ ⊢ e₁ e₂ : τ 
```

```lean
do 
  let τ' ← genTy  -- We need to generate a random argument type τ' here!
  let e₁ ← genLExpr Γ (.arrow τ' τ)
  let e₂ ← genLExpr Γ τ'
  return (.app e₁ e₂)
```

*A priori*, the generator doesn't know what the argument type `τ'` ought to be, so it needs to generate some random type `τ'`. 
However, if your library functions have multiple arguments, each of which are different type, e.g. 
`take : Int -> String -> String` (function for extracting a prefix from a string, taken from the [Haskell standard library](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Prelude.html#v:take)), then we need to apply the `App` rule twice and hope
that we pick `Int` and `String` as the two random argument types during each application of the `App` rule.

Specifically, in the derivation below, we need to pick `τ'' = Int` and `τ' = String`:
```
Γ ⊢ take : τ'' → τ' → String      Γ ⊢ n : τ''
--------------------------------------------------------------------- (App)
            Γ ⊢ take n : τ' → String                 Γ ⊢ s : τ'
----------------------------------------------------------------------- (App)
                         Γ ⊢ take n s : String 
```

However, in general, the probability of picking both `τ'' = Int` and `τ' = String` is very low, which means we are rarely going to 
generate function applications that actually call factory functions! 




## Avoiding inlining sub-generators
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
```

[^1]: `take n s` . 
