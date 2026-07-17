# Variable Capture Bug in `genIndirPoly`

> **Status note.** The *capture bug* and the *freshening fix* (`freshenBoundVars`)
> described here are still live — freshening remains in the generator and is
> essential. However, this document was written during the **operational
> `OpsConsistent`** era, and its later sections (especially "Two corrections",
> and any mention of `opTypeSubst` orienting a substitution the "wrong direction",
> or `Constraints.unify` being symmetric) describe the operational check that the
> generator is **no longer proven against**. The generator now targets the
> *declarative* `OpsConsistentR`, whose `.op_in` never runs `opTypeSubst`. Treat
> the `opTypeSubst`/symmetric-unifier and ground-only-fix material as historical;
> the current guard and its rationale are in
> `docs/ops-consistent-polymorphic-gap.md` (top note) and
> `docs/lean-vs-haskell-generator.md`.

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
`[α' ↦ .ftvar "α"]`) that correctly records how the operator was instantiated. The
resulting annotation satisfies `OpsConsistent`.

### Why the Fix Works

> **⚠️ SUPERSEDED — this subsection is historically inaccurate.** It claims the
> freshening fix alone makes `id` at target `.ftvar "α"` produce a *consistent*
> `α → α` annotation. It does **not**: `LFunc.opTypeSubst` unifies `(α → α, α → α)`
> and the round-trip does not certify the annotation as a valid instantiation once
> the target type carries free variables — this is the very gap documented in
> `ops-consistent-polymorphic-gap.md`. The actual fix drops such non-ground
> candidates entirely (ground-only instantiation), so `id` at target `.ftvar "α"`
> is **not** generated. Freshening remains necessary (it removes name capture) but
> is not sufficient on its own. The steps below are left only as a record of the
> original — incorrect — reasoning.

With the `id : ∀ α. α → α` example and target `τ = .ftvar "α"`:

1. `contextVars = ["α"]` (from `collectFtvars τ`)
2. `freshenBoundVars ["α"] (α → α) ["α"]` → `(["α'"], .ftvar "α'" → .ftvar "α'")`
3. `unifyTypes (.ftvar "α'") (.ftvar "α")` → `subst = [α' ↦ .ftvar "α"]`
4. `findFreeTyVars ["α'"] [α' ↦ .ftvar "α"]` → `[]` (α' is now solved)
5. `fullSubst = [α' ↦ .ftvar "α"]`
6. `concreteArgTys = [(.ftvar "α'").subst [α' ↦ .ftvar "α"]]` = `[.ftvar "α"]`
7. `fullArrowTy = .ftvar "α" → .ftvar "α"` — **not** `OpsConsistent` (see above),
   so under the ground-only fix this candidate is dropped, not emitted.

## Proving `OpsConsistent` on Generated Terms

> **⚠️ HISTORICAL DESIGN SKETCH — superseded by the actual implementation.** The
> `PCtxWF`, theorem statement, proof strategy, and "Key Lemma" below are the
> *original plan*, and differ from what was built. See the "Implementation status"
> section at the end of this file and `ops-consistent-polymorphic-gap.md` for the
> real design. In particular: (a) `PCtxWF` was strengthened with a
> free-type-variables-⊆-`typeArgs` invariant; (b) the `freshen_subst_eq_generic_subst`
> "Key Lemma" below is **not** how the proof closes — instead the generator was
> restricted to *ground* polymorphic instantiations and the real completeness
> ingredient is `unify_ground_instance` (ground-matching unification completeness);
> (c) the final theorem proves `Lambda.GenOpsConsistent` (a certified copy of
> `OpsConsistent`), not the private `Lambda.OpsConsistent` directly.

### Required Precondition

A well-formedness condition linking `pctx` entries to the factory:

```lean
def PCtxWF (F : @Factory LExprParams') (pctx : PolyOpCtx) : Prop :=
  ∀ (name : String) (lty : Lambda.LTy),
    (name, lty) ∈ pctx →
    ∃ (f : LFunc LExprParams'), f ∈ F.toArray.toList ∧
      f.name.name = name ∧
      lty = .forAll f.typeArgs (LMonoTy.mkArrow' f.output f.inputs.values)
```

### Theorem Statement

```lean
theorem genLExpr_opsConsistent (F : @Factory LExprParams')
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : SimpleType τ)
    (hOctx : octx = factoryOps F)
    (hPctx : PCtxWF F pctx)
    (e : LExpr')
    (he : e ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ)) :
    Lambda.OpsConsistent F e
```

### Proof Strategy

Two cases for `.op` nodes:

1. **From `pickOp`** (via `genLExprBase`): The annotation `τ` is the generic curried type
   from `factoryOps F`. For monomorphic ops, `opTypeSubst` returns `Subst.empty` and
   `genericTy.subst Subst.empty = genericTy = ty_op`. For polymorphic ops in `octx` with
   their full generic type, `opTypeSubst` unifies the annotation against itself.

2. **From `genIndirPoly`**: The annotation is `concreteArgTys.foldr arrow τ`. After
   freshening, this equals `genericTy.subst fullSubst`. Then `opTypeSubst` unifies the
   annotation against `genericTy`, recovering an equivalent substitution.

### Key Lemma

```lean
theorem freshen_subst_eq_generic_subst (boundVars : List TyIdentifier)
    (monoTy : LMonoTy) (contextVars : List TyIdentifier)
    (fullSubst : Lambda.Subst)
    (hAll : ∀ v ∈ (freshenBoundVars boundVars monoTy contextVars).1,
      (Maps.find? fullSubst v).isSome) :
    let (_, freshMonoTy) := freshenBoundVars boundVars monoTy contextVars
    LMonoTy.subst fullSubst freshMonoTy = LMonoTy.subst fullSubst monoTy
```

This states: if all freshened bound vars are mapped by `fullSubst`, then applying
`fullSubst` to the freshened type gives the same result as applying it to the original.
This holds because freshening only renames variables, and if both old and new names map
to the same concrete type under `fullSubst`, the result is identical.

This lemma is non-trivial to prove (requires reasoning about `LMonoTy.subst` and the
renaming substitution). It can be `sorry`'d initially.

### OpsConsistent for Sub-expressions

For compound expressions (`.app`, `.ite`, `.abs`, `.eq`, `.quant`), `OpsConsistent` is
structural (conjunction over sub-expressions). Each sub-expression is generated by
`genLExprBase`, so the proof recurses. The base cases (`.const`, `.bvar`, `.fvar`) are
trivially `True`.

## Files Involved

| File | Role |
|------|------|
| `HasTypeAGen/Core.lean` | Generator definitions (fix goes here) |
| `HasTypeAGen.lean` | Proofs (soundness, completeness, new OpsConsistent theorem) |
| `HasTypeAGen/Defs.lean` | `factoryOps` definition (unchanged) |
| `Strata/.../Assumptions.lean` | `OpsConsistent` definition (unchanged, upstream) |
| `Strata/.../Factory.lean` | `LFunc.opTypeSubst` definition (unchanged, upstream) |
| `Strata/.../LTy.lean` | `LMonoTy.freeVars` (reusable, upstream) |

## Implementation Order

1. Add `collectFtvars`, `freshen`, `freshenBoundVars` to Core.lean
2. Modify `polyOpsForResult` to freshen before unification
3. Verify `lake build` passes (generator compiles)
4. Update `genIndirPoly_sound` if needed
5. Update `genIndirPoly_complete`, `genLExpr_complete`, `IsPolyApp`
6. Add `PCtxWF` and `genLExpr_opsConsistent` (sorry complex sub-goals)
7. Prove what's provable, document remaining sorrys

## Verification

1. `lake build` passes at each step
2. No new `sorry` in previously-proven theorems
3. Property test: generate terms with `tvars = ["α"]` and `pctx` containing operators
   binding `"α"`, verify all generated terms pass a decidable `OpsConsistent` check

## Implementation status (completed)

Done in `StrataGenerators/HasTypeAGen/Core.lean`,
`StrataGenerators/HasTypeAGen/OpsConsistentDef.lean` (new), and
`StrataGenerators/HasTypeAGenOpsConsistent.lean` (new):

1. ✅ `freshen` / `freshenBoundVars` added to `Core.lean`; `polyOpsForResult`
   freshens before unification. (`collectFtvars` not needed — used Strata's
   existing `LMonoTy.freeVars`.)
2. ✅ Generator compiles; `genLExpr_sound`, `genLExpr_complete`, and all existing
   proofs still pass unchanged (they treat `polyOpsForResult` as a black box, so
   the internal freshening change is transparent to them). No new `sorry` in any
   previously-proven theorem.
3. ✅ `OpsConsistent` machinery:
   - `OpsConsistentDef.lean` is a `module` file exposing `Lambda.GenOpsConsistent`,
     an `@[expose] public` copy of Strata's private `Lambda.OpsConsistent`, with a
     build-checked `GenOpsConsistent.faithful : GenOpsConsistent = OpsConsistent`.
     (Necessary because `OpsConsistent` is non-`public` and only nameable from a
     `module` that `import all`s `Assumptions`, which cannot import the non-module
     generator — see `opsconsistent-module-shim.md`.) It also proves the reusable
     Strata bridge lemmas (`unify_self`, `opGeneric_opsConsistent`,
     `opGroundInstance_opsConsistent`, `mkArrow_destructArrow` + `ArrowSpineOK`,
     `mem_get?_eq`).
   - `HasTypeAGenOpsConsistent.lean` proves `GenOpsConsistent` for the full
     generator: `genLExprBase_opsConsistent` (structural induction over the
     generator, all 21 depth/type cases), `mkApps`/`mapM` propagation, the
     monomorphic Indir op node, and the top-level `genLExpr_opsConsistent`.
   - **`genLExpr_opsConsistent_nil`** (and `genIndirPoly_opsConsistent_nil`):
     fully unconditional, `sorry`-free, for `pctx = []` — covering the closed-term
     generators.
   - **`genLExpr_opsConsistent_of_PCtxWF`** (general `pctx`): the headline result,
     **fully proven and unconditional** given `FactoryOutputWF F` + `PCtxWF F pctx`
     (both discharged for any real factory). Depends only on the standard axioms
     (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`. (`genLExpr_opsConsistent`
     is a slightly more general form taking the — now proven — `PolyOpsConsistent`
     assumption directly.)

### Two corrections to this document's original design

**1. The freshening fix alone is not sufficient (the `freshen_subst_eq_generic_subst`
"Key Lemma" plan does not close the proof).** A *second, independent* gap exists:
when the target type carries free type variables, `LFunc.opTypeSubst` can orient
the recovered substitution in the wrong direction, so the annotation
`concreteArgTys.foldr arrow τ` is not a valid factory instantiation even after
freshening. The fix was to restrict `polyOpsForResult` to **ground** instantiations
(drop any candidate whose annotation has free type variables); a ground annotation
is a genuine instance of the generic type and `opTypeSubst` recovers it correctly.
Freshening is still applied (it removes name capture), but groundness is what makes
the annotation consistent. Fully documented, with the `id : ∀α. α → α` at target
`.ftvar "β"` counterexample, in `ops-consistent-polymorphic-gap.md`.

**2. `PolyOpsConsistent` IS proven (not just assumed).** After the ground-only fix
it becomes true, and `PolyOpsConsistent_of_PCtxWF` proves it from `PCtxWF`. This
required (a) proving `unify_ground_instance` — a ground-matching *unification
completeness* result that Strata does not ship (only soundness) — from scratch in
`StrataGenerators/UnifyGroundInstance.lean`, and (b) **strengthening `PCtxWF`** to
require every free type variable of a factory function's generic type to be bound
by its `typeArgs` (`(mkArrow' fn.output fn.inputs.values).freeVars ⊆ fn.typeArgs`),
matching Strata's real `FuncWF` invariant. Without (b), a monomorphic function with
a free type variable would break consistency (machine-checked counterexample; see
`ops-consistent-polymorphic-gap.md`).

### Why `GenOpsConsistent` instead of `OpsConsistent` directly

The proofs are stated in terms of `Lambda.GenOpsConsistent`, an `@[expose] public`
copy of Strata's private `Lambda.OpsConsistent`, certified definitionally equal by
the build-checked `GenOpsConsistent.faithful`. This is forced by Lean's module
system: `OpsConsistent` is only nameable from a `module` file, which cannot import
the non-`module` generator. See `opsconsistent-module-shim.md` for the full
explanation.
