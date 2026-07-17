# Variable Capture Bug in `genIndirPoly`

> **Scope.** This document covers the *capture bug* and the *freshening fix*
> (`freshenBoundVars`), both of which are live — freshening remains in the
> generator and is essential. The op-consistency proof that consumes it is
> described in `docs/ops-consistent-polymorphic-gap.md` and
> `docs/lean-vs-haskell-generator.md`, which are the authority on the current
> design.

## Summary

The polymorphic operator instantiation path (`genIndirPoly`) can produce `.op` nodes
whose type annotations violate `OpsConsistent` — the invariant that operator annotations
are valid instantiations of the factory function's generic type scheme. The bug occurs
when a bound type variable in the polymorphic operator's type shares a name with a free
type variable appearing in the target type or context.

## What is `OpsConsistent`?

Every `.op` node in Strata's expression AST carries a type annotation — a monotype that
declares the operator's type at that particular use site. For monomorphic operators this
is always the same (e.g., `neg : bool → bool`). For polymorphic operators it varies per
call site (e.g., `id` might be annotated `int → int` at one site and `bool → bool` at
another).

`OpsConsistent F e` checks that every `.op` annotation in `e` is a **valid instantiation**
of the corresponding factory function's generic type scheme. Concretely, for an `.op`
node with name `f` and annotation `ty_op`:

1. Look up `f` in the factory to get its generic type (e.g., `α → α` for `id`)
2. Unify `ty_op` against the generic type to recover a type substitution `S`
3. Check that `ty_op` equals the generic type with `S` applied

This ensures the annotation is coherent: it's the generic type specialized by a single
consistent substitution. An annotation like `.int → .ftvar "α"` for `id` would fail
because no single substitution makes `α → α` equal to `.int → .ftvar "α"`.

The denotational semantics relies on `OpsConsistent` to inline operator bodies correctly:
it uses the substitution recovered from the annotation to instantiate type variables in
the function body. If the annotation is incoherent, the substitution disagrees with the
actual argument types, and type preservation breaks.

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

### 4. The Haskell prototype didn't trigger this problem in practice

The original Haskell generator (`GenSTLC.hs`) uses De Bruijn indices (`TVar Int`) for type
variables. Its unification algorithm treats `TVar x == TVar y` as rigid equality (returns
`Nothing` for distinct indices, `[]` for identical indices). In practice, **target types
never contain `TVar`** because:

- `boolFunctionCtx` is built from `monoFunctions` (only `Forall 0` entries — ground types)
- The `Arbitrary Typ` instance only generates `TBool` and `TFun` (never `TVar`)
- Lambda binders use generated types, so contexts only grow with ground types

This is an invariant maintained by convention, not enforced at the type level. `Ctx = [Typ]`
and `Typ` includes `TVar Int` — nothing prevents a `TVar` from appearing. If someone
manually called `genExactExpr [TVar 0] (TVar 0)`, the same capture issue would surface:
`unify (TVar 0) (TVar 0)` returns `Just []`, and the bound variable appears "unsolved."

The Lean port broke this accidental invariant in two ways:
- Type variables became **named strings** (Strata's `LMonoTy.ftvar : String → LMonoTy`)
- The typing context **routinely** contains free type variables (Strata supports
  polymorphic contexts, and the generator accepts a `tvars` parameter for this purpose)

Both changes are necessary for Strata's richer type system but together make the capture
problem manifest in normal usage rather than only in contrived edge cases.

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

### New Helpers (in `HasTypeAGen/Core.lean`)

```lean
/-- Collect all ftvar names appearing in a monotype. -/
def collectFtvars : LMonoTy → List TyIdentifier
  | .ftvar x => [x]
  | .tcons _ args => args.flatMap collectFtvars
  | .bitvec _ => []

/-- Generate a fresh name not in `used` by appending primes. -/
def freshen (name : TyIdentifier) (used : List TyIdentifier) : TyIdentifier :=
  if name ∉ used then name
  else go (name ++ "'") used
where
  go (candidate : String) (used : List TyIdentifier) : TyIdentifier :=
    if candidate ∉ used then candidate
    else go (candidate ++ "'") used

/-- Alpha-rename bound variables that collide with `contextVars`.
    Returns (freshened bound var names, freshened monotype body). -/
def freshenBoundVars (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (contextVars : List TyIdentifier) : List TyIdentifier × LMonoTy :=
  let allUsed := contextVars ++ boundVars
  let (freshBound, _) := boundVars.foldl (fun (acc, used) v =>
    if v ∈ contextVars then
      let fresh := freshen v used
      (acc ++ [fresh], fresh :: used)
    else
      (acc ++ [v], used))
    ([], allUsed)
  let renaming : Lambda.Subst :=
    [(boundVars.zip freshBound).filterMap (fun (old, new) =>
      if old == new then none else some (old, .ftvar new))]
  let freshMonoTy := LMonoTy.subst renaming monoTy
  (freshBound, freshMonoTy)
```

Note: `LMonoTy.freeVars` already exists in Strata (`Strata/DL/Lambda/LTy.lean:316`)
and could be used instead of `collectFtvars` above.

### Modified `polyOpsForResult`

```lean
def polyOpsForResult (pctx : PolyOpCtx) (τ : LMonoTy)
    (generableTys : List LMonoTy) (sampledTys : List LMonoTy)
    : List (String × List LMonoTy) :=
  let contextVars := (collectFtvars τ ++ generableTys.flatMap collectFtvars).eraseDups
  pctx.filterMap fun (name, lty) =>
    match lty with
    | .forAll boundVars monoTy =>
      let (freshBoundVars, freshMonoTy) := freshenBoundVars boundVars monoTy contextVars
      let (argTys, retTy) := decomposeArrow freshMonoTy
      if argTys.isEmpty || argTys.length > 3 then none
      else match unifyTypes retTy τ with
        | none => none
        | some subst =>
          let freeTyVars := findFreeTyVars freshBoundVars subst
          if !freeTyVars.isEmpty && generableTys.isEmpty then none
          else
            let fullSubst : Lambda.Subst := (freeTyVars.zip sampledTys) :: subst
            let concreteArgTys := argTys.map (LMonoTy.subst fullSubst)
            some (name, concreteArgTys)
```

After freshening, `unifyTypes retTy' τ` produces a non-trivial substitution (e.g.,
`[α' ↦ .ftvar "α"]`) that correctly records how the operator was instantiated,
removing the name capture.

## Current op-consistency proof

Freshening (above) is a *necessary* ingredient but not the whole story, and the
op-consistency proof it feeds into has since been rebuilt against Strata's
declarative `OpsConsistentR`. For the current design — the forward-instance guard
in `findPolymorphicOps`, `PCtxWF`, and the headline
`genLExpr_opsConsistentR_of_PCtxWF` — see `ops-consistent-polymorphic-gap.md` and
`lean-vs-haskell-generator.md`.
