# Lean vs. Haskell well-typed–term generators: why the Lean body is not a direct translation

There are two closely-related generators of well-typed terms in this project's
orbit:

- the **Lean** generator, `genLExprBase` / `genLExpr` / `genIndirPoly` in
  `StrataGenerators/HasTypeAGen/Core.lean` (this repo), which is *proven* sound
  with respect to Strata's `HasTypeA` and `OpsConsistentR`; and
- the **Haskell** generator, `genExactExpr` / `genIndirPoly` in
  `GenSTLCNamed.hs` (and the hand-written exercise skeleton
  `GenSTLCNamedExercise.hs`) in the sibling `quickcheck-stlc-experiments` repo,
  which is *tested* with QuickCheck (`prop_genSound`, `prop_genOpsConsistent`).

They implement the *same algorithm* — Pałka et al.'s base rules plus the
`Indir`/`IndirPoly` rules — and it is tempting to think of the Lean version as a
line-for-line transliteration of the Haskell one. It isn't, and this document
explains where the bodies differ and *why the differences are forced* rather than
incidental.

The differences fall into three buckets:

1. **Proof-vs-test** — intrinsic and unavoidable.
2. **Totality** — Lean functions must be proven terminating.
3. **Strata-inherited** — Lean must answer to Strata's actual datatypes and
   predicates, which it does not get to redesign.

The single most subtle point — the `genIndirPoly` forward-instance guard — sits
in bucket (1) and gets its own section.

---

## 1. Proof vs. test: the intrinsic gap

The Haskell generator only has to be *right on the samples QuickCheck happens to
draw*. `prop_genSound`/`prop_genOpsConsistent` run a few hundred–thousand random
`(type, term)` pairs and check each. Nothing quantifies over *all* terms the
generator could produce.

The Lean generator has to be *proven correct for its entire support* — every term
reachable with nonzero probability. This is ~85% of the Lean artifact and has no
Haskell counterpart at all:

- Support characterizations like `genLMonoTy_support` (every generated type is a
  `SimpleType` of bounded depth), and the giant 21-case `genLExprBase` traversal
  in `HasTypeAGenOpsConsistent.lean` that walks the generator's `SetGen.Set`
  support and shows each reachable node is consistent.
- Membership lemmas for the random combinators (`frequency`, `pick`, `elements`),
  because reasoning about "what can this `Gen` produce" *is* the proof.

Consequence for the body: the Lean generator is written in a **support-legible**
style. Where Haskell threads failure through `Maybe` and calls `QC.discard`, Lean
must make every branch's support statically characterizable — which drives choices
like the explicit `SimpleType`/`monoTyDepth` predicates and the depth-indexed
recursion, none of which the Haskell version needs.

**This gap cannot be closed by translation.** You cannot turn a test into a proof
by rewriting the generator; the proof obligations exist independently of how the
generator is spelled.

---

## 2. Totality: fuel instead of unbounded recursion

Every Lean `def` must be proven terminating. Two places where the Haskell code
uses unbounded/lazy recursion that Lean cannot copy directly:

### Fresh-name supply

Haskell (`GenSTLCNamed.hs`) filters an **infinite lazy list**:

```haskell
freshNames = filter (`notElem` allUsed) nameSupply
  where nameSupply = [c : s | s <- "" : map show [1..], c <- ['a'..'z']]
```

Lean cannot `filter` an infinite list into a total function, so `freshen`
(`Core.lean`) uses a **fuel-bounded** prime-appending search, with a pigeonhole
argument that the fuel always suffices:

```lean
def freshenGo (fuel) (candidate) (used) : TyIdentifier := ...
def freshen (name) (used) := freshenGo (used.length + 1) name used
```

Same behavior (a name not in `used`), different mechanism — forced purely by
totality.

### Generable-types fixpoint

Both close the context's syntactic subtypes under application. Haskell recurses
"until no new type appears"; Lean bounds the iteration by
`fuel = initial.length`. Again: same result, fuel added for termination.

---

## 3. Strata-inherited constraints

The Lean generator lives against Strata's real definitions and cannot redesign
them:

- **Substitutions.** Strata's `Subst` is a *list of scopes* (`Maps`) with an
  empty-scope fast path, and well-formedness (`SubstWF`) bundled into `SubstInfo`.
  The Haskell `Subst = [(String, Typ)]` is a flat assoc list. This representation
  difference propagates to every substitution operation (`LMonoTy.subst`,
  `composeSubst`, freshening).
- **The consistency predicate is fixed externally.** Haskell's `opsConsistent`
  and its one-directional matcher `matchInstance` are *bespoke to the exercise* —
  invented to make the property meaningful. Lean must discharge Strata's actual
  `OpsConsistentR`, whose `.op_in` demands the existence of a substitution `S`
  with `annotation = genericTy.subst S`. Lean cannot swap in a friendlier check.
- **`HasTypeA` reads annotations; the Haskell checker used to re-infer.** After
  the STLC exercise was aligned to Strata, `getTyp`'s `Const` case trusts the
  annotation (matching `HasTypeA`), but the datatypes and typing rules are still
  Strata's, not a clean-slate design.

---

## 4. The forward-instance guard: the subtle one

This is the difference people most often expect to be eliminable by translation,
and the reason it isn't is worth spelling out precisely. It is **not** because
"Strata's unifier is symmetric" — that was the *operational* `OpsConsistent`
story, which the current generator no longer targets (see the note at the top of
`ops-consistent-polymorphic-gap.md`). `OpsConsistentR` never calls `opTypeSubst`.

### What each generator emits (identical)

Both build the polymorphic-operator annotation the same way — arguments folded
over the **target type** in the return position:

- Lean: `fullArrowTy = concreteArgTys.foldr (fun σ acc => .arrow σ acc) τ`
- Haskell: `annotationTy = foldr TFun resultTy concreteArgTys`

So the annotation *hardcodes* the target (`τ` / `resultTy`) as its return type.
This is deliberate: it makes the term well-typed at the requested target *by
construction* (that is why `prop_genSound` / `HasTypeA` always holds).

### Where they diverge (guard vs. no guard)

Lean has an extra line the Haskell version lacks:

```lean
if LMonoTy.subst fullSubst retTy == τ then some (name, concreteArgTys) else none
```

The reason is about **how the consistency witness is obtained**, and it is a
proof-vs-test manifestation:

- **Haskell searches for the witness at check time.** `opsConsistent` calls
  `matchInstance genericTy annotation`, which walks `genericTy` as a *pattern*,
  one-directionally, and *discovers* whatever substitution makes it match the
  annotation. Because matching is direction-fixed (it can only ever solve the
  scheme's own variables), any annotation that is genuinely a forward instance is
  simply *found* to be consistent. No guard is needed — the checker does the
  existence search per sample.

- **Lean commits to a specific witness in the proof.** To discharge
  `OpsConsistentR.op_in`, `polyOpsForResult_instanceR` must *exhibit* a
  substitution `S` with `annotation = genericTy.subst S`, and it builds that `S`
  from the generator's own `fullSubst` (composed with the freshening renaming, via
  `composeWitnessScope`). That witness reconstructs the annotation's return
  position as `subst fullSubst retTy`. But the annotation *hardcoded* the return
  position as `τ`. The two agree exactly when

  ```
  subst fullSubst retTy = τ
  ```

  which is precisely the guard. When unification oriented the `retTy ~ τ` equation
  against `τ` (e.g. `id : ∀α. α → α` at target `β`, where `unify α β` may solve
  `β ↦ α`), we get `subst fullSubst retTy = α ≠ β = τ`, and the `fullSubst`-derived
  witness does **not** reconstruct the hardcoded annotation — so `op_in` is
  unprovable for that candidate. The guard drops exactly those.

### Is the guard fundamentally required?

No — it is a **cost trade-off, not an impossibility.** Two ways Lean could drop it
and mirror the Haskell shape:

1. **Prove the witness by search, like `matchInstance`.** Instead of reusing
   `fullSubst`, prove a lemma "`concreteArgTys.foldr arrow τ` is always a forward
   instance of `genericTy`" by structural induction, *deriving* the witness. Then
   no guard is needed. This is essentially proving `matchInstance`'s correctness in
   Lean — strictly more proof work, which is why the guard route was taken.
2. **Annotate from the substitution instead of hardcoding `τ`** (i.e.
   `subst fullSubst freshFunTy`). Then the witness matches by construction and no
   guard is needed — but the annotation's return type would no longer be forced to
   `τ`, so the term would not be well-typed at the requested target. That only
   "works" by excluding the same candidates the guard excludes, implicitly. Not a
   real win.

So the guard is the *cheapest* way to make a pre-committed proof witness valid; it
is not logically forced. The genuinely unavoidable part is upstream: Lean must
produce *some* witness for *every* support element (proof), whereas Haskell
re-searches for a witness only on *sampled* terms (test).

---

## Summary table

| Aspect | Haskell (`GenSTLCNamed`) | Lean (`Core.lean`) | Deviation is… |
|---|---|---|---|
| Correctness | QuickCheck properties on samples | proofs over the whole support | intrinsic (proof vs. test) |
| Fresh names | filter infinite lazy list | fuel-bounded `freshenGo` | forced (totality) |
| Generable-types closure | recurse until fixpoint | `fuel = initial.length` | forced (totality) |
| Substitutions | flat `[(String, Typ)]` | scoped `Maps` + `SubstWF` | forced (Strata) |
| Consistency check | bespoke `matchInstance` (matching) | Strata's `OpsConsistentR.op_in` | forced (Strata) |
| Poly-op annotation | `foldr TFun resultTy …` | `concreteArgTys.foldr arrow τ` | **identical** |
| Forward-instance guard | absent (checker searches) | present (proof commits witness) | eliminable in principle, kept for proof cost |

**Bottom line.** The Lean generator's *algorithm* is the same as the Haskell one,
and several pieces are line-for-line equivalent. But it is not a direct syntactic
translation because (a) it carries whole-support proof obligations a test never
states, (b) it must be total, and (c) it must satisfy Strata's fixed datatypes and
`OpsConsistentR`. Only (a) is truly unavoidable; (b) and (c) force *mechanism*
changes (fuel, scoped substitutions, the guard) even where the *behavior* matches.
