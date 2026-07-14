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

Here `genericTy` is the operator's declared, *uninstantiated* arrow type built
from the factory signature — `LMonoTy.mkArrow' fn.output fn.inputs.values`, so
`α → α` for `id`, still mentioning `id`'s own **bound** type variable `α`
(`fn.typeArgs = ["α"]`). `tySubst` is the substitution `LFunc.opTypeSubst`
*recovers after the fact* by unifying the annotation against `genericTy`
(`Constraints.unify [(annotation, genericTy)]`) — **not** the substitution the
generator used to build the annotation. The check passes only when that recovered
`tySubst` maps `genericTy`'s bound variables *forward* onto the annotation; the
bug is that `Constraints.unify` is symmetric and here orients the solved equation
the other way (`[β ↦ α]`, solving the target's `β`), so applying it to `α → α`
leaves `α → α` rather than reproducing `β → β`. See `OpsConsistentDef.lean:36-47`
(the check) and `Strata/DL/Lambda/Factory.lean:628-637` (`opTypeSubst`).

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

A type is **ground** when it contains no free type variables — i.e.
`LMonoTy.freeVars τ = []`. `int`, `bool`, and `int → bool` are ground; anything
mentioning a type variable such as `α`, `β`, or `β → β` is not. (In this
codebase there is no separate binder on `LMonoTy`, so "free type variable" just
means "any type variable occurring in the type".) A **ground instance** of a
generic type is a ground type obtained by substituting ground types for the
generic type's variables — e.g. `int → int` and `(int→bool)→(int→bool)` are
ground instances of `id`'s `α → α`, whereas `β → β` is an instance but not a
ground one.

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

### Coverage impact (for future test authors)

The generator is used for property-based testing, where "coverage" means the
variety of well-typed term *shapes* it can produce. The ground-only guard removes
exactly one shape from the space:

> **A polymorphic operator applied at a result type that is (or contains) a free
> type variable.**

Concretely, `genLExpr`/`genIndirPoly` take a `tvars` parameter (type variables in
scope) and a target type `τ`. When you generate the *body* of a polymorphic
function such as

```
function f<β>(x : β) : β { … }
```

the target is `τ = .ftvar "β"` — a free (rigid) type variable. Before this fix,
`genIndirPoly` could instantiate e.g. `id : ∀α. α → α` at `α := β` and emit
`id : β → β` applied to some `x : β`. That term is well-typed under `HasTypeA`,
but its `.op` annotation `β → β` is *not* `OpsConsistent` (the wrong-direction
unification above). The ground-only guard now **drops** such candidates, so
`genIndirPoly` instantiates polymorphic operators only at ground types
(`id : int → int`, `id : bool → bool`, `id : (int → bool) → (int → bool)`, …),
never at `β`.

What this means in practice:

- **No test breaks today.** No existing property test asserts on this shape or on
  the generator's distribution, so nothing starts failing. This is a forward-looking
  note, not a regression.
- **Only non-empty `pctx` is affected.** The `IndirPoly` rule fires only when the
  polymorphic-operator context `pctx` is non-empty. The default/closed-term entry
  points (`genClosedLExpr`, `genLExprWithFactory` at its default `pctx := []`) never
  invoke it, so they are entirely unaffected — as are their fully unconditional
  `…_nil` consistency proofs.
- **The dropped terms are still reachable indirectly.** Polymorphic operators are
  still exercised (at ground instantiations), and a term like `id x` at a
  free-type-variable type can still arise through the other generation rules
  (e.g. a bound/free variable of that type, the `App` rule). Only the specific
  *`IndirPoly`-emitted polymorphic-op-at-free-tyvar* shape is excluded.
- **If you genuinely need that shape covered** (e.g. testing round-tripping or
  denotation of polymorphic-op applications sitting inside polymorphic function
  bodies), do *not* just re-enable non-ground candidates — that reintroduces the
  `OpsConsistent` violation. Instead adopt one of the "Alternative generator
  fixes" below (annotating the op with `genericTy.subst fullSubst` directly is the
  most local), which keeps IndirPoly working at free target types while producing
  a coherent annotation.

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
(`Matchesσ`).

### Why the `unifyCore_success` helper exists (the longest proof in the file)

`unify_ground_instance` is short because it delegates the hard half to
`unifyCore_success`, which is where all the induction lives. The split mirrors
what "completeness" actually requires here:

- **Soundness — already in Strata.** `LExpr.unify_makes_equal` says *if* unify
  succeeds with `R`, then `A.subst R = P.subst R`. Combined with `A` ground
  (`subst_ground`, so `A.subst R = A`), that gives the reconstruction half
  `A = P.subst R` — Part 2 of `unify_ground_instance`, three lines.
- **Termination-with-success — what Strata does *not* provide.** Nothing in
  Strata guarantees that a *solvable* system actually returns `.ok`; its unifier
  could in principle fail or the recursion diverge. That existence obligation
  (`∃ R, Constraints.unify … = .ok R`, Part 1) is the real content, and it can
  only be discharged by following the unifier's own recursion. That is
  `unifyCore_success`.

`unifyCore_success` runs the mutual well-founded induction generated by
`Constraints.unifyCore.induct`, giving **17 subgoals** — one per branch of
`Constraint.unifyOne`/`Constraints.unifyCore` — which is why it is by far the
longest lemma. It carries the invariant `Matchesσ σ S`: every binding already in
the accumulator `S` agrees with the fixed matcher `σ` and is ground. The reason
groundness is doing the heavy lifting is that the branches which would normally
make unification *fail* (an `ftvar` against a mismatched ground type, the occurs
check, name/arity mismatch on `tcons`, bitvec-vs-`tcons`) all become
*contradictory* once `subst_ground` collapses the ground side to a fixed type —
so the "failure" cases are closed by contradiction rather than by producing an
error. The two branches with real work are the `ftvar id` binding steps (on a
find-hit the stored type re-derives the same ground type; on a find-miss we
extend `S` and re-establish `Matchesσ`) and the `tcons` recursion (descend into
the argument lists, transporting the ground-match hypothesis pointwise with
`mem_zip_map`). Isolating this as its own lemma keeps the headline
`unify_ground_instance` statement readable and lets the induction be stated over
arbitrary constraint lists `cs`/accumulators `S` (which the induction needs) while
`unify_ground_instance` only exposes the single-equation `[(A, P)]` case the
generator uses.

`PolyOpsConsistent_of_PCtxWF` then derives `PolyOpsConsistent` from
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
