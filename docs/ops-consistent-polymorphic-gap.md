# The `genIndirPoly` forward-instance guard

## Summary

The polymorphic operator path (`genIndirPoly` / `findPolymorphicOps`) instantiates
a factory function's generic type at the target type `τ` and emits an `.op` node
carrying the instantiated annotation. For that annotation to satisfy Strata's
op-consistency relation `OpsConsistentR`, it must be a genuine *substitution
instance* of the operator's generic type. `findPolymorphicOps` guarantees this with
a **forward-instance guard**: it keeps a candidate only when the substitution it
built, applied to the operator's return type, reproduces `τ` exactly.

This is distinct from the variable-capture bug documented in
`ops-consistent-capture-bug.md` (which the bound-variable *freshening* fix
addresses). Freshening removes name collisions; the forward-instance guard ensures
the resulting annotation is a coherent instance. Both are needed, and both are live.

## What `OpsConsistentR` requires

`OpsConsistentR F e` is Strata's *declarative* op-consistency relation: the
inductive specification that every `.op` annotation in `e` is *some* instantiation
of the factory function's generic type. Its `.op_in` constructor requires only the
**existence** of a substitution `S` with

```
annotation = genericTy.subst S
```

where `genericTy = LMonoTy.mkArrow' fn.output fn.inputs.values` is the operator's
declared, uninstantiated arrow type (mentioning the function's own bound type
variables). It does *not* run `LFunc.opTypeSubst` or re-derive `S` by unification —
existence of one witnessing `S` is enough.

## What the generator emits, and why a guard is needed

For a candidate `(name, .forAll boundVars monoTy)` in `pctx` and a target `τ`,
`findPolymorphicOps` (in `HasTypeAGen/Core.lean`):

1. freshens `monoTy`'s bound variables away from the free variables of `τ` and the
   generable-types set (removing capture);
2. decomposes the freshened body into `(argTys, retTy)`;
3. unifies `retTy` with `τ`, obtaining `subst`;
4. extends `subst` to map any still-uninstantiated freshened bound variables to
   freshly sampled types, giving `extendedSubst`;
5. sets `concreteArgTys = argTys.map (subst extendedSubst)`.

`genIndirPoly` then emits `.op name (some (concreteArgTys.foldr arrow τ))` — note
the annotation **hardcodes `τ` in its return position**.

The subtlety: the `op_in` witness available for this annotation is derived from
`extendedSubst` (composed with the freshening renaming), so it reproduces
`subst extendedSubst retTy`, not `τ` directly. The annotation and the witness
therefore agree only when

```
subst extendedSubst retTy = τ.
```

Unification is symmetric, so `unifyTypes retTy τ` can solve the equation in either
direction — it may bind a *free variable of `τ`* to a subterm of `retTy` instead of
the other way around. When it does, `subst extendedSubst retTy ≠ τ`, and the
hardcoded-`τ` annotation is *not* a substitution instance of `genericTy` via the
available witness.

### Concrete example

Take `id : ∀α. α → α` and target `τ = .ftvar "β"` (a free type variable — the normal
polymorphic setting, e.g. when generating the body of `function f<β>(x : β) : β`).
Freshening does not rename here (`α` ∉ {`β`}). Then:

- `decomposeArrow (α → α) = ([α], α)`
- `unifyTypes (retTy = α) (τ = β)` can solve `β ↦ α` — binding the *target's*
  variable `β`, the opposite of the intended `α ↦ β`
- with that orientation, `subst extendedSubst retTy = subst [β ↦ α] α = α ≠ β = τ`

So the annotation `β → β` would not be a coherent instance under the available
witness. The forward-instance guard rejects exactly this candidate.

## The guard

`findPolymorphicOps` keeps a candidate only when the extended substitution, applied
to the freshened return type, yields the target:

```lean
guard (LMonoTy.subst extendedSubst retTy == τ)
```

When this holds, `extendedSubst` (composed with the freshening renaming) is a
witness that `concreteArgTys.foldr arrow τ` is a substitution instance of
`genericTy` — precisely what `OpsConsistentR.op_in` demands. The example above is
dropped because `subst [β ↦ α] α = α ≠ β`.

Note this guard is **strictly more permissive** than requiring ground
instantiations: it *admits* annotations that mention a free (non-quantified) type
variable when the unifier happens to orient the equation the intended way — e.g.
`id` instantiated as `β → β` via `α ↦ β` is a genuine forward instance and is kept.
Only the wrong-orientation candidates are dropped.

For how this guard compares to the Haskell reference generator (which does not need
it, and why), see `lean-vs-haskell-generator.md` (§ "The forward-instance guard").

## How the guard feeds the proof

In `StrataGenerators/HasTypeAGenOpsConsistent.lean`:

- **`findPolymorphicOps_instanceR`** turns membership in `findPolymorphicOps` into
  the `op_in` witness: for every emitted `(name, concreteArgTys)` there is a factory
  function `fn` (`F[name]? = some fn`) and a substitution `S` with
  `concreteArgTys.foldr arrow τ = subst S genericTy`. The guard
  `subst extendedSubst retTy == τ` is exactly the hypothesis this proof needs to
  align the hardcoded-`τ` annotation with the witness. The witness `S` is built
  directly by `composite_instance_subst`, composing the freshening renaming with the
  generator's `extendedSubst` (via `composeWitnessScope`) — needing neither
  groundness nor any well-formedness of the substitution.

- **`PolyOpsConsistentR_of_PCtxWF`** discharges the polymorphic-annotation
  obligation `PolyOpsConsistentR` from `PCtxWF` (the condition that every `pctx`
  entry is a factory function's generic scheme), by feeding each
  `findPolymorphicOps_instanceR` witness into `OpsConsistentR.op_in`. No case split
  on `typeArgs`, no groundness.

- **`genLExpr_opsConsistentR_of_PCtxWF`** is the headline result: every generated
  term satisfies `OpsConsistentR F`, given `PCtxWF F pctx`. For the factory-derived
  context it is unconditional (`genLExpr_opsConsistentR_factory`, via
  `PCtxWF_factoryPolyOps`); for the empty polymorphic context it needs no hypothesis
  at all (`genLExpr_opsConsistentR_nil`). All depend only on the standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

`PCtxWF` records only that each `pctx` entry is the generic scheme of a real factory
function — it does *not* require the annotation to be ground, nor
`freeVars ⊆ typeArgs`. Working against the declarative `OpsConsistentR` (existence
of a substitution) rather than an operational check (re-deriving it by unification)
is what keeps this obligation light.
