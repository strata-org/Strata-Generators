# PRs to make to Strata

This repo (a random-generator soundness/completeness development) sits on top of
Strata, vendored at `.lake/packages/Strata/`. A handful of lemmas defined here are
really general facts about Strata's core datatypes (`LMonoTy`, `Subst`, `Maps`,
`Factory`, `LFunc`) and belong upstream in Strata itself, not in a downstream
generator. This doc lists the upstream PRs, in priority order.

Nothing here mentions generator vocabulary (`genLExpr`/`SetGen`/`SimpleType`/
`HasTypeA'`/`OpsConsistentR`/…); those and the generator-local predicates stay in
this repo. See "Deliberately excluded" at the bottom.

> Note: the copy of Strata under `.lake/packages/Strata/` is a vendored
> dependency, not the upstream repo — any edit there is local until it lands in
> Strata proper through its own review.

---

## PR 1 — `Factory` forward-lookup bridge (`mem_get?_eq`)

**Required to delete the `module` shim `HasTypeAGen/OpsConsistentBridge.lean`.**

### The lemma
`StrataGenerators/HasTypeAGen/OpsConsistentBridge.lean:36` (already `namespace Lambda`, already `public`)

```lean
public theorem mem_get?_eq {T : LExprParams} [DecidableEq T.IDMeta]
    {F : @Factory T} {s : String} {fn : LFunc T}
    (hs : s ∈ F) (hget : F[s]'hs = fn) : F[s]? = some fn
```

Membership plus a total lookup determines the partial lookup. It belongs in
`Strata/DL/Lambda/Factory.lean` beside `mem_name_eq_getElem` (`:384`).

### Why a PR is required (verified empirically)

This proves the *forward* direction `s ∈ F → F[s]'hs = fn → F[s]? = some fn`,
which Strata's current public API does not offer. Strata ships only the *reverse*
bridges — `getElem?_some_implies_mem`, `getElem?_some_getElem`,
`getElem?_is_some_implies_mem` (all `public`, inside `Factory.lean`'s
`public section`). Attempts to re-derive `mem_get?_eq` downstream from the public
API all fail:

- via `getElem?_pos` (the generic `GetElem` law): `Factory` has no
  `LawfulGetElem` instance;
- via unfolding `Factory.get?` (the way the current proof does it): the
  `none`-branch contradiction needs the **private field `F.nameMap`**
  (`error: Field nameMap ... is private`), which is reachable only from a
  `module` file that does `import all Strata.DL.Lambda.Factory`.

That private-field access is the entire reason the lemma is stranded in a
downstream shim. The relevant module-system facts:

- Lean 4's module system makes a `module` file's declarations private by default;
  and a `module` file **cannot import a non-`module` file**.
- The generator is non-`module` (it transitively depends on the vendored Basalt
  library, which has no `module` header), so it cannot `import all Factory` to
  reach `nameMap`.
- `OpsConsistentBridge.lean` therefore exists as a tiny `module` file that *can*
  `import all Factory`, holds only `mem_get?_eq`, and is imported by the
  non-`module` proof file `HasTypeAGenOpsConsistent.lean`. `mem_get?_eq` is the
  only reason the shim exists.

### What it unblocks
Landing `mem_get?_eq` (or a public forward bridge such as `s ∈ F → (F[s]?).isSome`)
in `Factory.lean` lets `OpsConsistentBridge.lean` be deleted entirely and the
`import all` workaround removed. **Until then, that one-lemma shim must stay in
this repo — it cannot be removed downstream.**

---

## PR 2 — substitution / arrow-spine lemmas

General `LMonoTy`/`Subst` facts for a substitution-lemmas file in Strata's Lambda
layer. Unlike PR 1, none of these touches a private field, so no `import all` is
needed (confirmed: the non-`module` file `HasTypeAGenOpsConsistent.lean` already
invokes every primitive they use).

### `LMonoTys_subst_map`
`StrataGenerators/HasTypeAGenOpsConsistent.lean:967`

```lean
theorem LMonoTys_subst_map (S : Lambda.Subst) (args : List LMonoTy) :
    LMonoTys.subst S args = args.map (LMonoTy.subst S)
```

`LMonoTys.subst` is the pointwise `map` of `LMonoTy.subst`. This is a *public
restatement* of a fact Strata already has internally (`LMonoTys_subst_eq_map`) but
which lives in a `module` file and is not `public`. Marking the Strata original
`public` would make this copy unnecessary.

### `subst_foldr_arrow`
`StrataGenerators/HasTypeAGenOpsConsistent.lean:946`

```lean
theorem subst_foldr_arrow (S : Lambda.Subst) (l : List LMonoTy) (t : LMonoTy) :
    LMonoTy.subst S (l.foldr (fun σ acc => LMonoTy.arrow σ acc) t)
      = (l.map (LMonoTy.subst S)).foldr (fun σ acc => LMonoTy.arrow σ acc)
          (LMonoTy.subst S t)
```

Substitution distributes over a right-nested arrow fold (an arrow spine). A
natural companion to Strata's `mkArrow'` API.

### `composeWitnessScope` (+ helpers)
`StrataGenerators/HasTypeAGenOpsConsistent.lean:979, :984, :1011`

```lean
def composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst) : Lambda.SubstOne :=
  (LMonoTy.freeVars P).map (fun v => (v, LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v))))

theorem find?_composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst)
    (v : TyIdentifier) (hv : v ∈ LMonoTy.freeVars P) :
    Maps.find? [composeWitnessScope P T1 T2] v
      = some (LMonoTy.subst T2 (LMonoTy.subst T1 (.ftvar v)))

theorem subst_composeWitnessScope (P : LMonoTy) (T1 T2 : Lambda.Subst) :
    ∀ (mty : LMonoTy), (∀ v, v ∈ LMonoTy.freeVars mty → v ∈ LMonoTy.freeVars P) →
      LMonoTy.subst [composeWitnessScope P T1 T2] mty
        = LMonoTy.subst T2 (LMonoTy.subst T1 mty)
```

The single-scope substitution realizing the composite `subst T2 ∘ subst T1` on the
free variables of `P`, and the two lemmas characterizing it. These support the
composition-instance fact below.

### `composite_instance_subst`
`StrataGenerators/HasTypeAGenOpsConsistent.lean:1055`

```lean
theorem composite_instance_subst (A P : LMonoTy) (T1 T2 : Lambda.Subst)
    (hA : A = LMonoTy.subst T2 (LMonoTy.subst T1 P)) :
    ∃ S : Lambda.Subst, A = LMonoTy.subst S P
```

Any composite substitution instance is a single substitution instance: if
`A = subst T2 (subst T1 P)`, then some raw `S` gives `A = subst S P`. A clean,
generally useful strengthening of Strata's substitution API — no groundness or
`SubstWF` needed.

### `freeVars_mkArrow'`
`StrataGenerators/FunctionHasTypeAGen.lean:71`

```lean
theorem freeVars_mkArrow' (out : LMonoTy) (vals : List LMonoTy) (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' out vals)) :
    v ∈ LMonoTy.freeVars out ∨ ∃ t ∈ vals, v ∈ LMonoTy.freeVars t
```

The free variables of a curried arrow type (`mkArrow' out vals`) are exactly those
of the output or of some input. A natural companion to Strata's `mkArrow'`.

### Proof-dependency closure (verified)

Every candidate in this cluster depends *only* on public Strata primitives —
`LMonoTy.{subst,subst_emptyS,subst_tcons,subst_unfold,subst_no_relevant_keys,
subst_bitvec,freeVars,arrow,tcons,mkArrow'_nil,mkArrow'_cons}`,
`LMonoTys.{subst,subst_eq_substLogic,substLogic,substLogic_emptyS,freeVars,
freeVars_of_cons,freeVars_mem_subset}`, `Subst.hasEmptyScopes`, `Maps.find?`,
`Map.{find?,isEmpty}` — with no repo-local helpers. They form a closed set with an
internal ordering:

```
composite_instance_subst → subst_composeWitnessScope → find?_composeWitnessScope → composeWitnessScope
subst_foldr_arrow → LMonoTys_subst_map
```

Upstream in that dependency order and they compile standalone.

---

## Deliberately excluded (borderline / generator-local)

- `subst_simple`, `SimpleType_arrow_inv` (`HasTypeAGen.lean`): statements mention
  the generator-local `SimpleType`, so they stay here.
- `freshenBoundVars_snd_eq_subst` (`HasTypeAGenOpsConsistent.lean`): mentions the
  generator-local `freshenBoundVars`.
- `norm_arrow` / `norm_arrow'`: trivial `.arrow = .tcons "arrow" [_,_]` defeq
  restatements, not worth upstreaming.
