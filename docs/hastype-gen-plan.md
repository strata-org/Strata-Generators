# Plan: Generator of Well-Typed Terms Satisfying `HasType`

## Background

Strata has two typing relations for lambda expressions:

- **`HasTypeA`** (`Strata/DL/Lambda/Denote/LExprAnnotated.lean`): A syntax-directed,
  monomorphic, post-annotation relation for fully annotated expressions. Uses de Bruijn
  indices with a `List LMonoTy` context. Already has a proven-correct SetGen generator
  in `HasTypeAGen.lean`.

- **`HasType`** (`Strata/DL/Lambda/LExprTypeSpec.lean`): The full declarative typing
  specification. Based on Hindley-Milner without let-generalization. Uses locally-nameless
  representation with a `TContext` (named free variables) and `LContext` (operators,
  known types). Includes non-syntax-directed rules (`tinst`, `tgen`, `talias`).

## How `HasType` Differs from `HasTypeA`

| Aspect | HasTypeA | HasType |
|--------|----------|---------|
| Types | `LMonoTy` (monomorphic) | `LTy` (polymorphic schemes `∀α₁...αₙ. body`) |
| Binding | De Bruijn indices, `List LMonoTy` context | Locally-nameless, `TContext` with named free vars |
| Variable lookup | Annotation carries the type | `Γ.types.find? x = some ty` |
| Operators | Annotation carries the type | Looked up in `C.functions` with scheme |
| Polymorphism | None | `tinst` (instantiate), `tgen` (generalize) |
| Aliases | None | `talias` (alias equivalence) |
| Annotations | Required on all vars/ops | Optional (annotated and unannotated variants) |

## Type System Structure

The type system is HM without let-generalization:

```
STLC  ⊂  HM without let-gen (Strata HasType)  ⊂  Full HM  ⊂  System F
```

Key properties for a generator:
- If the initial generation target is monomorphic (`.forAll [] monoTy`), **all recursive
  targets remain monomorphic** — `tabs`/`tapp` enforce `isMonoType`, `tif` propagates,
  `teq`/`tquant` have free existential types we choose as mono.
- Polymorphism only enters via `tvar`/`top` (looking up a scheme from context) and must
  be immediately consumed by `tinst`.
- `tgen` is never needed when generating at monomorphic targets.

## Generator Design: Fused Instantiation

The generator should **fuse** `tvar`+`tinst` and `top`+`tinst` into single rules:

- **GenVarInst**: To generate at monomorphic target `τ`, scan `Γ.types` for any variable
  `x : ∀α₁...αₙ. body`. Use `matchScheme` to unify `body` against `τ`, solving for the
  `αᵢ`. If unification succeeds, emit `(.fvar m x none)`.

- **GenOpInst**: Same for operators in `C.functions`. Unify the operator's result type
  against `τ`.

`matchScheme` already exists in `HasTypeGen.lean` — it performs first-order pattern
matching (not full unification, since the target is always ground/monomorphic).

## Scope: Mono Core + Fused Operator Instantiation

Target rules for the generator:

| Rule | Handled by | Notes |
|------|-----------|-------|
| `tbool_const` | Leaf generator | Requires `C.knownTypes.containsName "bool"` |
| `tint_const` | Leaf generator | Requires `C.knownTypes.containsName "int"` |
| `tvar` + `tinst` | GenVarInst (fused) | matchScheme against Γ.types |
| `top` + `tinst` | GenOpInst (fused) | matchScheme against C.functions |
| `tabs` | Recursive | Locally-nameless: must handle `varOpen`/`varClose`, freshness |
| `tapp` | Recursive | Must pick/generate intermediate type (isMonoType) |
| `tif` | Recursive | Condition must be `.forAll [] .bool` |
| `teq` | Recursive | Choose monomorphic intermediate type |
| `tquant` | Recursive | Like `tabs` — binds a variable, body must be bool |

Rules **excluded** from scope:
- `tgen` — not needed for monomorphic targets, creates infinite derivation paths
- `talias` — requires reasoning about `AliasEquiv`
- `tvar_annotated` / `top_annotated` — requires `AnnotCompat`, not needed for unannotated terms
- `treal_const`, `tstr_const`, `tbitvec_const` — can be added later

## Key Implementation Challenges

### 1. Locally-Nameless Binding

Unlike `HasTypeA` (de Bruijn: just prepend to a list), `HasType` uses locally-nameless:
- `tabs` requires `LExpr.fresh x e`, `varOpen 0 x e`, and produces `(.abs m name o e)`
  where `e` has bound variables (via `varClose`)
- The generator must mint fresh variable names and manage open/close
- Proofs must discharge freshness obligations

### 2. matchScheme Correctness

Need a lemma:
```
theorem matchScheme_correct :
    matchScheme (.forAll tyVars body) target = some subst →
    LTy.openFull (.forAll tyVars body) subst = .forAll [] target
```

This is the bridge between the generator (which uses `matchScheme`) and the typing
derivation (which uses `LTy.openFull`).

### 3. Context Parameterization

The generator must be parameterized by:
- `C : LContext T` — provides `C.functions` and `C.knownTypes`
- `Γ : TContext T.IDMeta` — provides `Γ.types` (variable→type scheme mapping)

Guards like `C.knownTypes.containsName "bool"` become runtime checks in the generator
and hypotheses in the proofs.

### 4. isMonoType Proofs

Many rules require `LTy.isMonoType` witnesses. Since the generator only produces
monomorphic types (`SimpleType` ⊂ `LMonoTy` embedded as `.forAll [] _`), these are
always satisfiable, but must be explicitly constructed in the proof.

### 5. Completeness Normalization

For completeness, we need: "any derivation of `HasType C Γ e (.forAll [] τ)` can be
normalized to one that uses `tinst` only immediately above `tvar`/`top`." This is a
metatheorem about the type system. Options:
- Prove it as a separate lemma (hard, ~3-5 hours)
- Restrict completeness to a syntactically characterized fragment (like `AllTypesSimple`
  in `HasTypeAGen`)
- Leave completeness as `sorry` initially

## Relevant Literature

| Paper | Relevance |
|-------|-----------|
| Frank, Quiring, Lampropoulos (POPL 2024) "Not Useless" | Core generation technique. Formalizes Palka et al. as λ□, introduces nonlocal λ⊲ for better argument usage. Directly applicable to mono core. §3.3 sketches polymorphism but leaves it incomplete. |
| Hoang, Trunov, Lampropoulos, Sergey (ICFP 2022) Scilla testing | System F unsubstitution technique (overkill for HM-no-let-gen). Generation-by-execution for imperative statements. Structural parallel: Scilla ≈ Strata (pure core + imperative shell). |
| Fetscher, Claessen, Palka, et al. (ESOP 2015) Random Judgments | Generic solver approach via PLT Redex. Key negative result: completely fails with polymorphism. Confirms: work monomorphically and pre-instantiate schemes. |
| Palka et al. (AST 2011) | Original type-directed generation via rule inversion. GenFunVar heuristic for using polymorphic constants. Frank et al. §2 is a cleaner formalization of this. |

Key insight from the literature: Strata's `HasType` (HM without let-gen) is closer to
"STLC + polymorphic constants" than to System F. The generation strategy is essentially
Palka et al.'s approach: generate monomorphically, instantiate operator schemes at use
sites via unification against the target type. No unsubstitution or backtracking needed.

## Implementation Plan

### Phase 1: matchScheme Correctness (~2-3 hours Claude time)
1. Prove `matchScheme_correct` linking matchScheme to `LTy.openFull`
2. Prove `matchScheme_sound` showing the result is a valid instantiation

### Phase 2: Generator Definition (~4-6 hours Claude time)
1. Define context types (wrap `TContext`/`LContext` or use simplified versions)
2. Define context-scanning helpers (find vars/ops whose schemes match a target)
3. Define `genHasTypeExpr : Nat → LMonoTy → G (LExpr T.mono)` with rules:
   - Base cases: `tbool_const`, `tint_const`, GenVarInst, GenOpInst
   - Recursive: `tabs` (with fresh name + varClose), `tapp`, `tif`, `teq`, `tquant`

### Phase 3: Soundness Proof (~6-8 hours Claude time)
1. Prove helper lemmas for each leaf case
2. Prove the main theorem by structural recursion on size
3. Construct explicit `HasType` derivations including `tinst` for fused rules

### Phase 4: Completeness Proof (~8-12 hours Claude time)
1. Define the fragment predicate (analogous to `AllTypesSimple`)
2. State and prove (or sorry) the normalization metatheorem
3. Prove completeness by case analysis on the fragment predicate

### Recommended Approach
Start with Phase 1 + 2 + 3 (soundness). Leave completeness for later — soundness is
the practically important property (guarantees generated terms are well-typed for testing).

## File Organization

```
StrataGenerators/
  HasTypeGen.lean         -- matchScheme (already exists), generator def, proofs
  HasTypeAGen.lean        -- existing HasTypeA generator (reference)
  SetGen.lean             -- SetGen framework
  SetGen/                 -- SetGen internals
```

Eventually `matchScheme` should move to its own file since it's independent of the
generator infrastructure.
