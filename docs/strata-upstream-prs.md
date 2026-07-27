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

> **Provenance of the delta below.** `main`'s `lakefile.toml` currently pins the
> fork `https://github.com/ngernest/Strata` at rev `7f94d01f` ("Split
> concreteEval out of Func so Stmt DecidableEq compiles on this fork"). Every
> "fork adds X" claim is measured as the diff between that rev and the fork's
> last public-Strata merge base `ee0b2ecb2` (`fix(ci): Missing edits, lake update
> (#1440)`), cross-checked against `strata-org/Strata` `main` to distinguish
> *genuine* fork-only divergence from work the fork merely re-derived while
> upstream landed it independently.

---

## Already reconciled with upstream — no PR needed

Two clusters that earlier drafts of this doc treated as blockers have since
landed in `strata-org/Strata` `main`, and the fork was fast-forwarded onto them.
They are called out here so nobody re-opens PRs for them:

- **Core-AST `DecidableEq`.** Fork commit `7508b62f` ("Add DecidableEq to the
  Strata Core program AST") adds structural `DecidableEq`/`beq`+`beq_eq` to the
  `Imperative` and `Core` ASTs (`Stmt`, `Cmd`, `BasicBlock`, `Statement`,
  `Program`, …). Upstream commit `496bba7` already carries the identical
  machinery — verified an ancestor of `strata-org/Strata` `main`, including
  `Stmt.beq` / `Stmt.beq_eq` and `DecidableEq (Stmt …)`. **No PR.** (This is what
  unblocked issue #23: `stmtsEq` in `StmtHasTypeAGen/TestSupport.lean` now calls
  `decide (ss = ss')` instead of comparing pretty-printed output.)
- **`concreteEval` split off base `Func`.** Fork commit `7f94d01f` ports
  upstream's `76933e8b`: the function-typed `concreteEval` field is moved off the
  `deriving DecidableEq` base `Func` onto `LFunc extends Func`, with `Core.Function`
  aliasing `LFuncDefined`. Upstream `76933e8b` is an ancestor of
  `strata-org/Strata` `main`, and the resulting base `Func` struct is **identical**
  to upstream (same field list, same `deriving DecidableEq`). **No PR.**

One nuance for completeness: `strata-org/Strata` `main` has a *later* commit
`a61d47e5` ("Split closedness conditions out of `FuncWF` into `FuncClosed`") that
the fork did not adopt — the fork still keeps the body/precondition
free-variable clauses inside `FuncWF`. This is inert for this repo (the
generators and their proofs never reference `FuncWF`/`FuncClosed`/`body_freevars`/
`precond_freevars`), so it needs no PR *from this repo's perspective*; the fork
would simply pick it up on the next upstream merge.

---

## Retargeting to `strata-org/Strata`

**Goal:** flip this repo's `lakefile.toml` `require Strata` from
`https://github.com/ngernest/Strata` (a fork) back to the public
`https://github.com/strata-org/Strata`.

**Status:** *still blocked,* but the blocker has narrowed. The fork carries the
Core **typing-specification** work (`LExpr` type-checking soundness, and the
`Cmd`/`Function`/`Statement`/`Procedure` typing relations) that this repo's
generators derive against. Public `strata-org/Strata` does not have it. The
delta below is everything this repo needs on top of the merge base `ee0b2ecb2`
that is *not* already upstream (the two clusters in the section above having been
subtracted out).

Retargeting becomes possible only once these land in public Strata. The clusters
are listed roughly in the order they'd need to go up (each depends on the ones
above it).

### A. New modules to add (fork-only — do not exist upstream at all)

These are imported directly by this repo and pull in the rest of the typing-spec
cluster transitively. All confirmed **missing** in `strata-org/Strata` `main`:

| Module | Lines | Purpose | This repo names |
|---|---|---|---|
| `Strata.Languages.Core.FunctionTypeSpec` | 78 | declarative `FunctionHasType(A)` typing relation | `FunctionHasTypeA`, its constructors |
| `Strata.Languages.Core.CmdTypeSpec` | 108 | declarative `CmdHasType'` / `CmdHasTypeA` typing relations | `CmdHasType'.*`, `CmdHasTypeA` |
| `Strata.Languages.Core.CommandTypeSpec` | 101 | declarative `CmdExtHasType'` (extended-command layer) | `CmdExtHasType'.*` |
| `Strata.Languages.Core.StatementTypeSpec` | 179 | declarative `StmtHasType'` / `StmtsHasType'` (6-place, label-tracking) | `StmtHasTypeA`, `StmtsHasTypeA`, constructors |
| `Strata.Languages.Core.ProcedureTypeSpec` | 157 | declarative procedure typing relation | procedure-generator soundness/completeness |

Each spec module is accompanied in the fork by a large `*Props` companion of
soundness/completeness proofs (not imported by name here, but required for the
specs to be *usable* rather than just stated):
`FunctionTypeSpecProps` (~4.5k lines), `StatementTypeSpecProps` (~3.8k),
`CommandTypeSpecProps` (~3.4k), `CmdTypeSpecProps` (~1.3k).

Their transitive closure also requires the fork-only Lambda-layer theory that
lives *inside* the differing modules below (notably the additive theorems in
`LExprTypeSpec` and `LExprResolveProps`, and the env/unification lemmas —
`genTyVars_prefixed`, `addInNewestContext_stateSubstInfo`, `unify_pred`,
`LTy_instantiateWithCheck_preserves_stateSubstInfo`,
`typeBoundVar_xv_not_in_knownVars`).

### B. Existing upstream modules the fork diverges from

For each: whether the change is **purely additive** (safe, mergeable as-is) or
**behavioral** (upstream would have to accept a typechecker semantics change, or
this repo would have to adapt). Line counts are fork-`7f94d01f`-vs-`ee0b2ecb2`
insertions.

| Module | +lines | Kind | What the fork adds / changes |
|---|---|---|---|
| `DL/Lambda/LExprResolveProps` | ~2274 | additive | new resolve-soundness theorem file underpinning the annotated typing specs |
| `DL/Lambda/LExprTypeSpec` | ~1957 | additive | typing-soundness theorems (superset; no upstream-only decls removed) |
| `Util/Tactics` | ~229 | additive | +9 custom tactics (`elim_err`, `splitIte`, …) used throughout the proofs |
| `DL/Lambda/LTyUnifyProps` | ~167 | additive | unification/substitution lemmas (net; file also drops stale material) |
| `DL/Lambda/LExprTypeEnv` | ~131 | additive | env lemmas (incl. `genTyVars_prefixed`, `addInNewestContext_stateSubstInfo`) |
| `Languages/Core/FunctionType` | ~155 | **behavioral** | `checkAnnotCompat`, monomorphic-annotation & rigid-typevar checks; `freeVarChecks` soundness guard |
| `DL/Lambda/Denote/LExprResolveAnnotated` | ~46 | additive | supporting resolve lemmas |
| `DL/Util/Maps` | ~47 | additive | `find?_append`, `keys_append`, `values_append` |
| `DL/Lambda/Denote/Assumptions` | ~42 | additive (visibility) | marks `OpsConsistent(R)` + `OpsConsistent_OpsConsistentR` `public`/`@[expose]` |
| `DL/Lambda/LTy` | ~17 | additive | `arrowsBinary` and companions |
| `DL/Lambda/LTyUnify` | ~16 | additive | supporting lemmas |
| `DL/Lambda/LExprWF` | ~14 | additive | `freeVars_map_fst_eq_getVars` |
| `DL/Util/Map` | ~12 | additive | `append_nil`, `values_append` |
| `DL/Lambda/Factory` | ~1 guard | **behavioral** | `arrowsBinary` binary-arrow guard in `LFunc.type` (present in fork, absent upstream) |
| `DL/Lambda/LExprT` | ~7 | **behavioral** | `resolveAux` `.quant` case rejects non-`bool` bodies rather than unifying |
| `Languages/Core/Expressions` | ~3 | additive | `HasVarsPure Expression Expression.Expr` instance |

The **behavioral** rows are the only ones that aren't a clean "add these
decls" PR (all three re-verified against `strata-org/Strata` `main`):

- **`LExprT` `.quant`** — upstream's `resolveAux` `.quant` case *unifies* the
  quantifier body with `bool` (`Constraints.unify [(ety, bool)] …`), which is now
  in `strata-org/Strata` `main`. The fork instead *rejects* a non-`bool` body
  (`if ety != bool then .error …`). The fork's typing specs are written against
  the non-unifying behavior, so upstream would need to either offer both, or the
  specs would need re-proving against the unify version.
- **`FunctionType` / `Factory` guards** (`checkAnnotCompat`, monomorphic-
  annotation, `arrowsBinary`) — these change what the typechecker *accepts*, so
  a handful of upstream `#guard_msgs` tests assert different output. The
  `arrowsBinary` guard in `Factory.LFunc.type` and the `freeVarChecks` guard in
  `FunctionType` are both present in the fork and absent upstream. See the fork's
  `MERGE_NOTES.md` for the exact tests affected.

### C. Visibility-only fixes (module-system `public` markers)

Even where the *logic* matches upstream, this repo needs certain symbols exported
across the `module` boundary. Already tracked concretely:

- `Denote/Assumptions`: `OpsConsistent`, `OpsConsistentR`,
  `OpsConsistent_OpsConsistentR` must be `public` (this repo names
  `Lambda.OpsConsistentR` directly). *(Included in row B above.)*
- `Util/List`: upstream's `public section` **exports** `List.Forall₂`, which
  then **collides** with `Batteries`/`Mathlib`'s `List.Forall₂` in this repo. The
  workaround lives here (drop `import Batteries.Data.List.Basic` in
  `HasTypeAGen.lean`); no upstream change is needed for it, but a future upstream
  rename of `List.Forall₂` → a Strata-namespaced name would let this repo import
  Batteries freely again.
- See **PR 1** and **PR 2** below for the `module`-boundary lemma shims
  (`mem_get?_eq`, substitution/arrow-spine facts).

### Retarget checklist

1. Land clusters **A** and the additive rows of **B/C** in `strata-org/Strata`.
2. Resolve the three **behavioral** rows (either upstream accepts the semantics,
   or re-prove the specs against upstream's behavior — the `.quant` unify change
   is the load-bearing one).
3. Land **PR 1 / PR 2** (below) to delete the remaining `module` shims.
4. Flip `lakefile.toml`: `git = "https://github.com/strata-org/Strata"`, pin a
   `rev` that includes the above, then `lake update Strata`.

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
