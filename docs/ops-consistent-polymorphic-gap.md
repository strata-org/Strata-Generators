# A second `OpsConsistent` gap: wrong-direction unification at free target types

## Summary

While proving that the generator produces `OpsConsistent` terms
(`StrataGenerators/HasTypeAGenOpsConsistent.lean`), a **second, independent**
`OpsConsistent` violation surfaced in the polymorphic operator path
(`genIndirPoly` / `polyOpsForResult`), distinct from the variable-capture bug
documented in `ops-consistent-capture-bug.md`.

The bound-variable *freshening* fix (already applied to `polyOpsForResult`)
correctly removes name collisions between an operator's bound type variables and
the context's free type variables. But it does **not** make the resulting `.op`
annotation `OpsConsistent` when the *target type* itself is (or contains) a free
type variable. In that case `LFunc.opTypeSubst` can recover the type
substitution in the *wrong direction*, and the coherence check fails.

## Concrete counterexample

Take `id : ∀α. α → α` in the factory, and generate a term of type
`τ = .ftvar "β"` (a free type variable — reachable whenever `tvars`/the context
contribute free type variables, which is the normal polymorphic setting).

`polyOpsForResult` (after freshening — here `id`'s bound `α` does *not* collide
with `β`, so nothing is renamed) proceeds:

- `decomposeArrow (α → α) = ([α], α)`
- `unifyTypes (retTy = α) (τ = β) = [α ↦ β]`
- `concreteArgTys = [α].map (subst [α ↦ β]) = [β]`
- annotation `fullArrowTy = β → β`

So `genIndirPoly` emits `.op "id" (some (β → β))`. Now check `OpsConsistent`:

- `F["id"]? = some id`, `id.typeArgs = ["α"]` (non-empty)
- `opTypeSubst id (.op "id" (some (β → β)))` unifies `(β → β, α → α)`
- Strata's unifier returns `[β ↦ α]` — it solves the *target's* variable `β` in
  terms of the operator's bound `α`, the **opposite** of what the generator
  intended.
- The coherence check is `annotation = genericTy.subst tySubst`, i.e.
  `β → β = (α → α).subst [β ↦ α] = α → α`. This is **false**.

Verified in Lean:

```
#eval (match Constraints.unify [(arrow β β, arrow α α)] .empty with
  | .ok si => (repr si.subst, decide (arrow β β = (arrow α α).subst si.subst))
  | .error _ => ("err", false))
-- ("[[(\"β\", ftvar \"α\")]]", false)
```

## Why freshening does not fix this

Freshening renames the operator's **bound** variables away from **context**
variables, so that `unifyTypes retTy τ` treats the bound variable as a solvable
metavariable rather than accidentally seeing it as already-equal to a rigid
context variable. That is necessary but not sufficient here: even with distinct
names (`α` vs `β`), `Constraints.unify` is symmetric and may orient the solved
equation either way. When it solves `β ↦ α` (context var ↦ bound var), applying
that substitution to the generic type does not reproduce the annotation.

For the annotation to be `OpsConsistent`, `opTypeSubst` must recover a
substitution `S` with `annotation = genericTy.subst S`. That holds when the
annotation is a *ground instance* of the generic type (no free vars, e.g.
`int → int`), or more generally when the instantiating substitution maps the
operator's own bound variables (never the context's). It fails precisely when
the target type contributes free variables that the unifier chooses to solve.

## Fix implemented: ground-only instantiation (option 1)

`polyOpsForResult` (in `HasTypeAGen/Core.lean`) now drops any candidate whose
full annotation `concreteArgTys.foldr arrow τ` is **not ground**:

```lean
if LMonoTy.freeVars τ == [] && concreteArgTys.all (fun σ => LMonoTy.freeVars σ == []) then
  some (name, concreteArgTys)
else none
```

A ground annotation `A` is a genuine ground *instance* of the operator's generic
type, so `LFunc.opTypeSubst` (unifying `A` against `genericTy`) can only solve
`genericTy`'s bound variables — mapping them to ground subterms of `A`, the
correct direction — and `A = genericTy.subst tySubst` holds. The counterexample
above is no longer generated: `id` at target `.ftvar "β"` would need annotation
`β → β`, which is non-ground and therefore dropped. Verified computationally:
ground instances such as `int → int` and `(int→bool)→(int→bool)` for `id` unify
to `[α ↦ …]` (correct direction) and satisfy the `OpsConsistent` equation.

This restricts IndirPoly to ground target/argument types. Since the generator is
for property testing, that is an acceptable coverage trade-off (polymorphic
operators are still exercised, just at ground instantiations); free-type-variable
targets are still reachable through the other rules.

## Status in the proof

`StrataGenerators/HasTypeAGenOpsConsistent.lean`:

- **`genLExpr_opsConsistent_nil`** and **`genIndirPoly_opsConsistent_nil`**:
  fully proven, `sorry`-free, for `pctx = []`. These cover the closed-term
  generators (`genClosedLExprWithFactory`, and `genLExprWithFactory` at its
  default `pctx := []`), where `polyOpsForResult` is always empty and no
  polymorphic op is ever emitted.
- **`genLExpr_opsConsistent`** (general `pctx`): proven **given** the assumption
  `PolyOpsConsistent F pctx bctx fctx τ` — which is itself now **fully proven**
  (see next section). Kept as a hypothesis on this theorem only for generality.
- **`genLExpr_opsConsistent_of_PCtxWF`** (general `pctx`, **unconditional**): the
  headline result. Requires only `FactoryOutputWF F` and `PCtxWF F pctx` — both
  factory-well-formedness conditions discharged for any real factory — and
  concludes `GenOpsConsistent F e` (equivalently `OpsConsistent F e`) for every
  generated term. Depends only on the standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`); no `sorry`.

## `PolyOpsConsistent` fully discharged

The completeness ingredient was proven from scratch in
`StrataGenerators/UnifyGroundInstance.lean`:

```lean
theorem unify_ground_instance (A P : LMonoTy) (σ : SubstInfo)
    (hground : A.freeVars = []) (hinst : A = LMonoTy.subst σ.subst P) :
    ∃ R, Constraints.unify [(A, P)] SubstInfo.empty = .ok R ∧ A = LMonoTy.subst R.subst P
```

— a **ground-matching completeness** result for Strata's unifier (which ships
only soundness lemmas), by mutual well-founded induction over
`Constraint.unifyOne`/`Constraints.unifyCore` with a matching invariant
(`Matchesσ`). `PolyOpsConsistent_of_PCtxWF` then derives `PolyOpsConsistent` from
`PCtxWF`: the annotation's groundness comes from the `freeVars … == []` guard, the
"instance of `genericTy`" fact from `polyOpsForResult_instance`, and consistency
from `opGroundInstance_opsConsistent` (poly) / `opGeneric_opsConsistent` (mono).

**A second necessary fix surfaced here:** `PCtxWF` had to be strengthened to
require every free type variable of a factory function's generic type to be bound
by its `typeArgs` (`(mkArrow' fn.output fn.inputs.values).freeVars ⊆ fn.typeArgs`)
— exactly Strata's real `FuncWF` invariant (`output_typevars_in_typeArgs`). Without
it a *monomorphic* function (`typeArgs = []`) carrying a free type variable
(e.g. `g : α → α` with `typeArgs = []`, which no real `FuncWF` factory contains)
would reach `polyOpsForResult`'s success branch with a ground annotation
`A ≠ genericTy`, yet `opTypeSubst` short-circuits to `some Subst.empty` for
monomorphic functions and would demand `A = genericTy` — false. This was found via
a machine-checked counterexample and is the reason the monomorphic case of
`PolyOpsConsistent_of_PCtxWF` needs the invariant (it forces the generic type
ground when `typeArgs = []`, so `A = genericTy`).

## Alternative generator fixes (not taken)

- **Orient the recovered substitution.** Annotate the op with
  `genericTy.subst fullSubst` directly (built from the operator's bound
  variables) rather than reconstructing `concreteArgTys.foldr arrow τ`, forcing
  the `opTypeSubst` round-trip to agree even at free target types. More invasive
  than the ground-only guard.
- **Restrict `pctx`/targets** so free type variables never reach a polymorphic
  operator's return position.
