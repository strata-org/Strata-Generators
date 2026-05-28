# Notes for Refactoring HasTypeGen: SHasType → HasType

## Goal

Replace `SHasType` (a local inductive in `HasTypeGen.lean`) with the real
`HasType` from `Strata.DL.Lambda.LExprTypeSpec`. The soundness theorem should
conclude `HasType C Γ e (.forAll [] τ)` directly.

## Current State

- `HasTypeGen.lean` builds successfully (imports `Strata.DL.Lambda.LExprTypeSpec`)
- Soundness is fully proved against `SHasType`
- Completeness has 1 sorry (against `InFragment`)
- The `SHasType` constructors map 1-1 to a subset of `HasType` constructors

## Key Files

- Generator: `/Users/ernestng/Documents/strata-generators/StrataGenerators/HasTypeGen.lean`
- Real HasType: `/Users/ernestng/Documents/strata-generators/.lake/packages/Strata/Strata/DL/Lambda/LExprTypeSpec.lean` (line 87)
- LExprWF (fresh, varOpen, varClose): `/Users/ernestng/Documents/strata-generators/.lake/packages/Strata/Strata/DL/Lambda/LExprWF.lean`
- TContext: `/Users/ernestng/Documents/strata-generators/.lake/packages/Strata/Strata/DL/Lambda/LExprTypeEnv.lean` (line 125)
- LContext: same file (line 440)
- Maps/Map: `/Users/ernestng/Documents/strata-generators/.lake/packages/Strata/Strata/DL/Util/Maps.lean`, `Map.lean`
- LTy.open/openFull: `/Users/ernestng/Documents/strata-generators/.lake/packages/Strata/Strata/DL/Lambda/LTyUnify.lean` (line 739/753)

## Build Command

```bash
cd /Users/ernestng/Documents/strata-generators && lake build StrataGenerators.HasTypeGen
```

Note: `HasTypeGen` and `HasTypeAGen` cannot be built in the same library target
due to a `List.Forall₂` collision between `Strata.DL.Util.List` and Batteries.
The `lakefile.toml` defines them as separate `[[lean_lib]]` targets.

## SHasType → HasType Mapping

Each `SHasType` constructor maps to one (or a chain of) `HasType` constructors:

| SHasType | HasType equivalent | Extra obligations |
|----------|-------------------|-------------------|
| `.tbool_const` | `HasType.tbool_const Γ () b hbool` | Need `C.knownTypes.containsName "bool"` hypothesis |
| `.tint_const` | `HasType.tint_const Γ () k hint` | Need `C.knownTypes.containsName "int"` hypothesis |
| `.tvar hmem hmatch` | `HasType.tinst ... (HasType.tvar Γ () x scheme hlookup) heq` | Need `Γ.types.find? x = some scheme`, then show `LTy.open` produces the target |
| `.top hmem hmatch` | `HasType.tinst ... (HasType.top Γ () f op scheme hlookup htype) heq` | Need `C.functions[op.name]? = some f` and `f.type = .ok scheme` |
| `.tabs hbody` | `HasType.tabs Γ () "" x (.forAll [] τ₁) body (.forAll [] τ₂) none hfresh hx_mono he_mono hbody_typed hannot` | Complex — see below |
| `.tapp hfn harg` | `HasType.tapp Γ () fn arg (.forAll [] τ₁) (.forAll [] τ₂) h1_mono h2_mono hfn_typed harg_typed` | Need `isMonoType` witnesses |
| `.tif hc ht he` | `HasType.tif Γ () c t e ty hc_typed ht_typed he_typed` | Straightforward |
| `.teq he1 he2` | `HasType.teq Γ () e1 e2 ty he1_typed he2_typed` | Straightforward |

## The `tabs` Case (Hardest)

`HasType.tabs` has signature:
```
| tabs : ∀ Γ m name x x_ty e e_ty o,
    LExpr.fresh x e →                          -- x is not free in e
    (hx : LTy.isMonoType x_ty) →               -- x_ty is monomorphic
    (he : LTy.isMonoType e_ty) →               -- e_ty is monomorphic
    HasType C { Γ with types := Γ.types.insert x.fst x_ty}
      (LExpr.varOpen 0 x e) e_ty →             -- body is well-typed in extended ctx
    (o = none ∨ ...) →                          -- annotation compat (we use none)
    HasType C Γ (.abs m name o e) (.forAll [] (.tcons "arrow" [...]))
```

The generator produces: `.abs () "" none (LExpr.varClose 0 (x, none) body)`

So `e = LExpr.varClose 0 (x, none) body`, and we need:
1. `LExpr.fresh (x, none) (LExpr.varClose 0 (x, none) body)` — x is not free after closing
2. `LExpr.varOpen 0 (x, none) (LExpr.varClose 0 (x, none) body) = body` — roundtrip

Key lemma available: `varOpen_of_varClose` (in LExprWF.lean line 283):
```
theorem varOpen_of_varClose (h : LExpr.WF e) :
  varOpen i x (varClose i x e) = e
```

And freshness after close: should follow from the definition of `varClose`
(it replaces all `fvar x` with `bvar`, so x can't be free anymore).

## The `tvar + tinst` Case

The generator produces `.fvar () x none` where `(x, scheme) ∈ vctx` and
`matchScheme scheme τ = some subst`.

Need to construct:
1. `HasType.tvar Γ () x scheme hlookup` — gives `HasType C Γ (.fvar () x none) scheme`
2. Chain of `HasType.tinst` to instantiate `scheme` down to `.forAll [] τ`

For `tinst`:
```
| tinst : ∀ Γ e ty e_ty x x_ty,
    HasType C Γ e ty →
    e_ty = LTy.open x x_ty ty →
    HasType C Γ e e_ty
```

`LTy.open x xty (.forAll [x, ...] body)` removes `x` from the bound vars
and substitutes `xty` for `x` in `body`. So instantiating all vars requires
chaining `tinst` once per bound variable — OR using `openFull` which does them all at once.

Actually there's no `tinstFull` rule — you must chain `tinst` one variable at a time.
So if `scheme = .forAll [α₁, α₂, α₃] body`, you need 3 chained `tinst` applications.

Alternative: prove a helper lemma `HasType.tinst_all` that chains `tinst` for a list.

## The `top + tinst` Case

Similar to `tvar + tinst` but starts with `HasType.top`:
```
| top: ∀ Γ m f op ty,
    C.functions[op.name]? = some f →
    f.type = .ok ty →
    HasType C Γ (.op m op none) ty
```

## New Theorem Signature

```lean
theorem genHTExpr_sound
    (C : LContext HTParams)
    (Γ : TContext Unit)
    (vctx : VarCtx) (octx : OpSchemeCtx)
    (counter : Nat) (size : Nat) (τ : LMonoTy)
    (hτ : SimpleType τ)
    -- Well-formedness hypotheses:
    (hbool : C.knownTypes.containsName "bool")
    (hint : C.knownTypes.containsName "int")
    (hvctx : ∀ x scheme, (x, scheme) ∈ vctx → Γ.types.find? x = some scheme)
    (hoctx : ∀ name scheme, (name, scheme) ∈ octx →
      ∃ f, C.functions[name]? = some f ∧ f.type = .ok scheme)
    (hfresh : ∀ k ≥ counter, Γ.types.find? (freshName k) = none)
    (e : HTExpr)
    (he : e ∈ SetGen.support (genHTExpr (G := SetGen.Set) vctx octx counter size τ)) :
    HasType C Γ e (.forAll [] τ) := by
  ...
```

## Suggested Approach

1. **Start with `tbool_const`/`tint_const`** — these are leaf cases, just need
   the `hbool`/`hint` hypotheses. Get the pattern working.

2. **Do `tif`/`teq`/`tapp`** — structurally similar to `SHasType` proof but
   need to pass `isMonoType` witnesses (which are trivially `.forAll [] _`).

3. **Do `tvar + tinst`** — need a helper that chains `tinst` applications.
   Key: `matchScheme scheme τ = some subst` implies the substitution works.

4. **Do `tabs` last** — hardest, needs freshness + varOpen/varClose roundtrip.

## Helper Lemmas Needed

```lean
-- Chain tinst for all bound variables at once
theorem HasType.tinst_chain (C : LContext T) (Γ : TContext T.IDMeta)
    (e : LExpr T.mono) (scheme : LTy) (subst : List LMonoTy) (τ : LMonoTy)
    (htyped : HasType C Γ e scheme)
    (hmatch : matchScheme scheme τ = some subst) :
    HasType C Γ e (.forAll [] τ)

-- isMonoType for .forAll [] _
theorem forAll_nil_isMonoType (body : LMonoTy) :
    LTy.isMonoType (.forAll [] body) = true

-- freshName is fresh after varClose
theorem fresh_after_varClose (x : HTIdent) (body : HTExpr) :
    LExpr.fresh (x, none) (LExpr.varClose 0 (x, none) body)

-- varOpen roundtrips with varClose (needs WF of body)
-- Already in Strata: varOpen_of_varClose
```

## matchScheme ↔ LTy.open Connection

`matchScheme (.forAll [α₁,...,αₙ] body) τ = some [σ₁,...,σₙ]`

means `body[αᵢ := σᵢ] = τ`.

The `tinst` rule uses `LTy.open x xty ty` which substitutes one variable.
So for `scheme = .forAll [α₁, α₂] body`:
- Start: `HasType C Γ e (.forAll [α₁, α₂] body)`
- `tinst` with `x = α₁, x_ty = σ₁`: `HasType C Γ e (.forAll [α₂] body[α₁:=σ₁])`
- `tinst` with `x = α₂, x_ty = σ₂`: `HasType C Γ e (.forAll [] body[α₁:=σ₁, α₂:=σ₂])`
- Final: `HasType C Γ e (.forAll [] τ)` (since body[all αᵢ:=σᵢ] = τ by matchScheme)

## Import Constraint

`HasTypeGen.lean` imports `Strata.DL.Lambda.LExprTypeSpec` which pulls in
`Strata.DL.Util.List` (defines `List.Forall₂`, `List.dedup`, etc.).
This conflicts with Batteries/Mathlib.

`HasTypeAGen.lean` imports `Basalt.Examples.ArbNat` → `Basalt` → `SPMF` → Mathlib.

They CANNOT be in the same file/library. The `lakefile.toml` defines them as
separate `[[lean_lib]]` targets so `lake build` builds both independently.

## Strata Build Patches (in .lake/packages/Strata/)

Two patches were applied to make Strata build with this Lean version:

1. `Strata/DL/Util/Maps.lean` line 645: `grind` → `simp_all [List.flatten, List.map_append, List.mem_append]`
2. `Strata/DL/Lambda/LExprTypeSpec.lean` line 2107: `sorry` for `Nat.toString` API change
3. `Strata/DL/Lambda/LExprTypeSpec.lean` line 2413: `grind` → explicit `rcases` proof

These are in the lake-fetched package (not version-controlled). If you do
`lake update`, they'll be lost and need to be re-applied.
