# Variable Capture Bug in `genIndirPoly`

## Summary

The polymorphic operator instantiation path (`genIndirPoly`) can produce `.op` nodes
whose type annotations violate `OpsConsistent` — the invariant that operator annotations
are valid instantiations of the factory function's generic type scheme. The bug occurs
when a bound type variable in the polymorphic operator's type shares a name with a free
type variable appearing in the target type or context.

## Background: How the Generator Works

`genIndirPoly` (in `HasTypeAGen/Core.lean`) generates fully-applied polymorphic operator
calls. Given a target type `τ`, it:

1. Picks a polymorphic operator from `pctx`, e.g. `id : ∀ α. α → α`
2. Decomposes the monotype body: `argTys = [.ftvar "α"]`, `retTy = .ftvar "α"`
3. Unifies `retTy` with `τ` to determine how the bound type variable should be instantiated
4. Samples concrete types for any remaining undetermined type variables
5. Constructs the annotation: `fullArrowTy = concreteArgTys.foldr arrow τ`
6. Emits `.op "id" (some fullArrowTy)` applied to generated arguments

## The Bug

When the target type is `τ = .ftvar "α"` (a **free** type variable from the typing
context — e.g., the expression is being generated inside a polymorphic function body),
and the operator binds a variable of the **same name** `"α"`:

**Step 3 goes wrong:**

```
unifyTypes (.ftvar "α") (.ftvar "α")
```

The unifier sees two identical terms and returns `subst = []` — "they're already equal,
nothing to do." But semantically these are different: the left `"α"` is a **bound
metavariable** (to be solved) and the right `"α"` is a **rigid free variable** (from
the context). The unifier can't distinguish them because they share a name.

**Consequence:**

- `findFreeTyVars ["α"] []` = `["α"]` — the bound var appears "unsolved"
- A concrete type (say `.int`) is sampled for it
- `fullSubst = [α ↦ .int]`
- `concreteArgTys = [.int]`
- `fullArrowTy = .int → .ftvar "α"` (because `τ = .ftvar "α"` is the target, not substituted)

The annotation `.int → .ftvar "α"` is not a valid instantiation of `α → α`. No single
substitution makes `α → α` equal to `.int → .ftvar "α"` — that would require `α = .int`
and `α = .ftvar "α"` simultaneously.

## What the Correct Annotation Should Be

The annotation on the `.op` node should be `.ftvar "α" → .ftvar "α"` — meaning "`id`
instantiated at the free type variable `α`." Both the argument type and return type are
`.ftvar "α"`, reflecting that the operator's bound `α` was instantiated with the
context's free `α`.

To be clear: this is purely about the **type annotation** carried by the `.op` AST node.
The generated term itself (`id x` for some `x`) is still well-typed under `HasTypeA`
regardless of what annotation it carries — `HasTypeA.op` assigns the type from the
annotation without checking its provenance. The annotation is metadata that the
denotational semantics relies on later to determine how type variables in the operator
body should be instantiated during evaluation.

With the **buggy** annotation `.int → .ftvar "α"`:
- The term type-checks: `HasTypeA` reads the annotation, assigns type `.ftvar "α"` ✓
- But the annotation is incoherent: no instantiation of `∀α. α → α` yields `.int → .ftvar "α"`
- The denotational semantics cannot interpret it (step preservation needs `OpsConsistent`)

With the **correct** annotation `.ftvar "α" → .ftvar "α"`:
- The term type-checks: same as above ✓
- The annotation is coherent: instantiating `α ↦ .ftvar "α"` in `α → α` gives `.ftvar "α" → .ftvar "α"` ✓
- The denotational semantics can interpret it (`OpsConsistent` holds)

## Why This Bug Wasn't Previously Caught

Three independent reasons:

### 1. `HasTypeA` doesn't check `OpsConsistent`

The typing judgement for operators is:
```
| op : HasTypeA Δ (.op m o (some ty)) ty
```

It assigns the expression whatever type the annotation says — no validation against the
factory. So the soundness proof (`genLExpr_sound`) goes through regardless of whether
the annotation is a valid instantiation.

### 2. The test harness only checks `HasTypeA`

Generated terms are validated by `typeCheck`, which implements `HasTypeA` — it reads the
annotation and trusts it. There's no test that runs `OpsConsistent` on generated terms.

### 3. `OpsConsistent` is a downstream assumption, never discharged on generated terms

`OpsConsistent` appears as a hypothesis in Strata's denotational semantics proofs
(step preservation, type soundness). These proofs assume the property holds — they don't
generate terms and check it. The chain of responsibility is:

```
Generator → produces terms satisfying HasTypeA (proven)
                                    ↕ (gap)
Denotational semantics → assumes OpsConsistent holds (never connected)
```

Nobody has attempted to close this gap by proving generated terms satisfy `OpsConsistent`.

### 4. The Haskell prototype didn't have this problem

The original Haskell generator (`GenSTLC.hs`) uses De Bruijn indices (`TVar Int`) for type
variables. Its unification algorithm treats `TVar x == TVar y` as rigid equality (returns
`Nothing` for distinct indices, `[]` for identical indices). And critically, **target types
never contain `TVar`** — the Haskell STLC context only holds ground types (`TBool`,
`TFun TBool TBool`).

So the collision scenario cannot arise: bound variables are integers 0..n-1 in the
polytype body, and target types contain no `TVar` at all.

The Lean port changed two things:
- Type variables became **named strings** (Strata's `LMonoTy.ftvar : String → LMonoTy`)
- The typing context CAN contain free type variables (Strata supports polymorphic contexts)

Both changes are necessary for Strata's richer type system but together create a capture
problem that the simpler STLC setting avoided by construction.

## Consequences

### What goes wrong in practice

1. **Generated terms are still well-typed** per `HasTypeA` — no observable failure in
   type-checking or in the generator's soundness proof.

2. **Generated terms may violate `OpsConsistent`** — specifically when:
   - The target type `τ` contains `.ftvar` names that collide with an operator's bound vars
   - This requires a non-empty `tvars` list (type variables in scope)
   - AND the polymorphic operator binds a variable whose name appears in `tvars`

3. **Denotational semantics proofs cannot be applied** to such terms. If Strata tried to
   inline the operator body using the type substitution derived from `opTypeSubst`, the
   inferred substitution would disagree with the argument types, breaking type preservation.

### Severity

Low-to-moderate for current usage:
- The generator is used for testing, not for producing terms fed into the denotational
  semantics.
- The bug only triggers when `tvars` is non-empty AND shares names with operator bound
  vars — which depends on how `pctx` entries are named.
- Well-typedness (`HasTypeA`) is preserved regardless.

High if the goal is to prove `genLExpr_opsConsistent`:
- The bug makes such a theorem unprovable without a code fix.

## Fix

Alpha-rename the polymorphic operator's bound variables to fresh names before unification.
In `polyOpsForResult`:

```lean
def polyOpsForResult (pctx : PolyOpCtx) (τ : LMonoTy)
    (generableTys : List LMonoTy) (sampledTys : List LMonoTy)
    : List (String × List LMonoTy) :=
  let contextFtvars := collectFtvars τ ++ generableTys.flatMap collectFtvars
  pctx.filterMap fun (name, lty) =>
    match lty with
    | .forAll boundVars monoTy =>
      let (freshBoundVars, freshMonoTy) := freshenBoundVars boundVars monoTy contextFtvars
      let (argTys, retTy) := decomposeArrow freshMonoTy
      ...
      let freeTyVars := findFreeTyVars freshBoundVars subst
      ...
```

After freshening, `unifyTypes retTy' τ` produces a non-trivial substitution (e.g.,
`[α' ↦ .ftvar "α"]`) that correctly records how the operator was instantiated. The
resulting annotation satisfies `OpsConsistent`.

## Verification Plan

After the fix:
1. Add a theorem `genLExpr_opsConsistent` proving generated terms satisfy `OpsConsistent F`
   given a well-formedness condition linking `pctx` entries to factory functions.
2. Add a property test that generates terms via `genIndirPoly` with `tvars` containing
   names that collide with operator bound vars, and asserts `OpsConsistent` holds.
