# Side-Conditions for `genLExpr`, `genCmd`, and `genFunction` Soundness & Completeness

This document catalogs every side-condition (hypothesis beyond the bare
"in support" / "is well-typed" facts) required by the soundness and
completeness theorems for the expression generator (`genLExpr`,
`StrataGenerators/HasTypeAGen.lean`), the command generator (`genCmd`,
`StrataGenerators/CmdHasTypeAGen.lean`), and the function generator
(`genFunction`, `StrataGenerators/FunctionHasTypeAGen.lean`). The
hypothesis-free soundness wrappers at an empty fvar context live in
`StrataGenerators/CmdHasTypeAGenSound.lean` (see §2.1 and §5).

For each theorem we list the hypotheses, give the *reason* each one is needed,
and note whether it is **proved** or **assumed** (taken as a hypothesis to be
discharged by the caller).

> Convention: "support" means `SetGen.support (gen … (G := SetGen.Set))`, the
> set of values the generator can produce. Soundness = `support → property`;
> completeness = `property → support`.

---

## 1. Expression generator (`HasTypeAGen.lean`)

### 1.1 `genLExpr_sound` (line 3497)

```
support (genLExpr fctx octx pctx tvars bctx depth τ) → HasTypeA' bctx e τ
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hτ` | `SimpleType τ` | The result type must be in the image of `genLMonoTy`. The proof recurses by case analysis on the `SimpleType` derivation, not on the raw `LMonoTy`; without it the generator's defining `match` would face type shapes (arbitrary `tcons`, non-generable bitvec widths) it never handles. |
| `hSimpleOps` | `∀ p ∈ octx, SimpleType p.2` | The monomorphic Indir path picks an operator from `octx` and generates its arguments via `genLExprBase`, which requires each argument type to be `SimpleType`. The operator's curried type must therefore decompose into simple types. |
| `hSimplePolyOps` | every entry returned by `polyOpsForResult pctx τ … sampledTys` has `SimpleType` argument types | The polymorphic Indir path (`genIndirPoly`) instantiates a poly-op and generates each argument via `genLExprBase`; the same `SimpleType` requirement on argument types applies. |

**Status:** all proved/discharged at call sites. `hSimpleOps`/`hSimplePolyOps`
are well-formedness conditions on the operator contexts.

### 1.2 `genLExprBase_sound` (line 585)

```
support (genLExprBase fctx octx tvars bctx depth τ) → HasTypeA' bctx e τ
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hτ` | `SimpleType τ` | Same as above — drives the structural recursion (`match depth, τ, hτ`). |

Note: `genLExprBase_sound` needs **no** `AllTypesSimple`, `emptyNames`,
`allVarsInCtx`, or depth hypotheses. Soundness is "free" in those — the
generator only ever emits well-typed, in-context terms, so recovering
`HasTypeA'` requires nothing about the term beyond knowing the target type is
generable.

### 1.3 `genIndirPoly_sound` (line 3425)

```
support (genIndirPoly fctx octx pctx tvars bctx depth τ) → HasTypeA' bctx e τ
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hτ` | `SimpleType τ` | Target type is generable. |
| `hSimplePolyOps` | poly-op entries have `SimpleType` argument types | Each generated argument flows through `genLExprBase`, which requires `SimpleType` on its target type. This is the *only* non-trivial obligation in the proof (see the inline comment at lines 3455–3457). |

### 1.4 `genLExprBase_complete` (line 1833)

```
HasTypeA' bctx e τ ∧ emptyNames e ∧ allVarsInCtx fctx octx e
  ∧ AllTypesSimple tvars depth bctx e ∧ termDepth bctx e ≤ depth
→ support (genLExprBase fctx octx tvars bctx depth τ)
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hτ` | `SimpleType τ` | Drives the recursion and is required to re-derive type-sampling membership. |
| `hwt` | `HasTypeA' bctx e τ` | The term must be well-typed at `τ` — the generator only produces well-typed terms, so this is necessary for reachability. |
| `hnames` | `emptyNames e` | The generator emits binders with the fixed empty name `""` (locally nameless). A term carrying any other binder name is unreachable. |
| `hvars` | `allVarsInCtx fctx octx e` | Free variables come from `pickFVar`/`pickOp`, which draw only from `fctx`/`octx`. Any fvar/op not present in those contexts is unreachable. |
| `hats` | `AllTypesSimple tvars depth bctx e` | At each compound node (`abs`/`app`/`eq`/`quant`) the generator samples an **intermediate** type via `genLMonoTy`. To place the node in the support we must show that sampled type is in `genLMonoTy`'s support, which by `genLMonoTy_support` requires exactly `SimpleType τ' ∧ monoTyDepth τ' ≤ n ∧ allFtvarsIn tvars τ'`. `AllTypesSimple` is the recursive predicate carrying those three witnesses at every node. None of this information is recoverable from `hwt` or `termDepth` (see notes). |
| `hdepth` | `termDepth bctx e ≤ depth` | The generator consumes one unit of fuel per compound level; a term deeper than `depth` cannot be produced. This precondition is *tight* — see `genLExprBase_termDepth_bound` (line 1318), which proves the generator never exceeds the budget. |

**Why `AllTypesSimple` cannot be dropped or derived:**
- `HasTypeA'` allows argument/annotation types that are non-`SimpleType`
  (e.g. a `Map`/`Sequence`, a stray ftvar not in `tvars`, or a `bitvec 7`).
  Such well-typed terms are genuinely unreachable, so the restriction is real.
- `termDepth` (line 1255) ignores annotation-type depth for `abs`/`app`/`eq`
  (only `quant` folds in `monoTyDepth`), so `monoTyDepth τ' ≤ n` cannot be
  derived from the depth budget.
- The `monoTyDepth` component could in principle be absorbed into a richer
  `termDepth`, but `SimpleType` and `allFtvarsIn` are non-numeric and would
  still need a dedicated predicate. So `AllTypesSimple` (or an equivalent) is
  essential.

### 1.5 `genIndirPoly_complete` (line 4292)

Reachability of a polymorphic operator application. The side-conditions are
packaged into the `IsPolyApp` predicate (line 4342) used by
`genLExpr_complete`; they assert the existence of sampled types of the right
length, a matching `polyOpsForResult` entry, and that each argument is in
`genLExprBase`'s support.

### 1.6 `genLExpr_complete` (line 4367)

```
( HasTypeA' bctx e τ ∧ emptyNames e ∧ allVarsInCtx fctx octx e
    ∧ AllTypesSimple tvars depth bctx e ∧ termDepth bctx e ≤ depth )
  ∨ IsPolyApp fctx octx pctx tvars bctx depth τ e
→ support (genLExpr fctx octx pctx tvars bctx depth τ)
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hτ` | `SimpleType τ` | Generable target type. |
| `he` (left disjunct) | the five `genLExprBase_complete` conditions above | Routes through `genLExprBase` (reachable in both `dite` branches). |
| `he` (right disjunct) | `IsPolyApp …` | Routes through `genIndirPoly`. The monomorphic Indir path is subsumed by the App rule of the left disjunct (the Indir rule is a distribution optimization, not a coverage extension). |

---

## 2. Command generator (`CmdHasTypeAGen.lean`)

The command generator delegates expression generation to `genLExpr`, so its
side-conditions split into (a) conditions inherited from the expression layer
and (b) conditions about variable contexts and fresh names.

### Shared helper predicates

| Predicate | Definition (location) | Role |
|---|---|---|
| `VarCtxCorresponds ctx Γ` | line 33 | The `Map`-based `VarCtx` agrees with the semantic `TContext Γ`: every `(x, mty) ∈ ctx` (keyed by `Identifier Unit`) maps to `forAll [] mty` in `Γ`, and fresh identifiers are absent from `Γ`. |
| `GenLExprSound` | line 281 | Assumed expression-soundness: everything in `genLExpr`'s support at `τ` is well-typed at `τ`. Discharged by `genLExpr_sound` (§1.1). |
| `GenLExprComplete` | line 368 | Assumed expression-completeness: every well-typed expression is in `genLExpr`'s support. Discharged by `genLExpr_complete` (§1.6). |
| `FreshNamesDisjointFromExprs` | line 291 | Fresh names from `genFreshName` never occur as free variables in generated expressions. **Now proved for `fctx = []`** as `freshNamesDisjointFromExprs_nil` (`CmdHasTypeAGenSound.lean:25`); it is *false* for nonempty `fctx` (see notes). |

### 2.1 `genCmd_sound` (line 303)

```
support (genCmd fctx octx tvars ctx depth) → ∃ Γ', CmdHasTypeA C Γ r.cmd Γ'
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hCorr` | `VarCtxCorresponds ctx Γ` | Links the generator's flat `ctx` to the typing context `Γ`. Needed so that (a) a freshly generated name is absent from `Γ` (for `init`), and (b) a `set` target found in `ctx` resolves in `Γ`. |
| `hExprSound` | `GenLExprSound fctx octx tvars depth` | The `init_det`/`set_det`/`assert`/`assume`/`cover` cases embed a generated expression; its well-typedness is needed to build the `CmdHasTypeA` derivation. |
| `hDisjoint` | `FreshNamesDisjointFromExprs fctx octx tvars ctx depth` | The `init_det` rule requires the freshly introduced variable not to occur free in the initializer expression. Proved for `fctx = []` (see notes). |

**Status:** all three side-conditions are now discharged for `fctx = []`.
`hCorr` and `hExprSound` come from the caller's setup (`hExprSound` by
`genLExpr_sound`); `hDisjoint` is discharged by `freshNamesDisjointFromExprs_nil`.
The hypothesis-free wrapper is `genCmd_sound_nil` (`CmdHasTypeAGenSound.lean:40`),
which supplies `hDisjoint` internally and leaves only the genuine
context-dependent obligations `hCorr` and `hExprSound`.

### 2.2 `genCmd_sound_env` / `genCmds_sound` (lines 516, 580)

These bundle the soundness side-conditions into a single record
`GenCmdSoundEnv` (line 494) so that the sequence generator can thread an
updated context through an induction on fuel.

`GenCmdSoundEnv` fields:

| Field | Statement | Why it is needed |
|---|---|---|
| `toTCtx` | `VarCtx → TContext Unit` | Semantic interpretation of a flat context. |
| `corr` | `∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)` | Correspondence at *every* reachable context (the sequence generator extends `ctx` as it goes). |
| `exprSound` | `GenLExprSound …` | Same as `hExprSound` above. |
| `freshDisjoint` | `∀ ctx, FreshNamesDisjointFromExprs … ctx …` | Same as `hDisjoint`, but quantified over all contexts reachable during sequence generation. Discharged for `fctx = []` by `freshNamesDisjointFromExprs_nil`. |
| `toTCtx_insert` | `toTCtx (ctx.insert x mty) = insert …` | The output `Γ'` of an `init` matches `toTCtx` applied to the extended `VarCtx`, so the chained `CmdsHasTypeA` relation lines up across steps. |

`genCmds_sound` requires no side-conditions beyond a `GenCmdSoundEnv`; the proof
is an induction on fuel `n` that re-applies `genCmd_sound_env` to each head
command. For `fctx = []`, `genCmdSoundEnv_nil` (`CmdHasTypeAGenSound.lean:56`)
builds the record with `freshDisjoint` pre-filled, and `genCmds_sound_nil`
(line 75) is the hypothesis-free sequence-soundness entry point.

### 2.3 `genCmd_complete` (line 387)

```
CmdHasTypeA C Γ cmd Γ' ∧ (reachability side-conditions)
→ ∃ r, r ∈ support (genCmd …) ∧ CmdHasTypeA C Γ r.cmd Γ'
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hwt` | `CmdHasTypeA C Γ cmd Γ'` | The command must be well-typed; the proof proceeds by inversion on this derivation. |
| `hExprComplete` | `GenLExprComplete fctx octx tvars depth` | The `init_det`/`set_det`/`assert`/`assume`/`cover` cases must show the sub-expression is reachable in `genLExpr`'s support. Discharged by `genLExpr_complete`. |
| `hNameReach` | the name of any `init`/`set` target is in `genFreshName`'s support | The generator picks new variable names from `genFreshName`; a target name it cannot generate is unreachable. |
| `hTyReach` | every `mty` is in `genLMonoTy tvars depth`'s support | An `init` command samples the declared type via `genLMonoTy`; non-generable types are unreachable. |
| `hVarInCtx` | a `set` target found in `Γ` exists at some index of `ctx` | The `set` rule picks the target by index into `ctx` via `choose`; the target must therefore be present in the flat context. |

> Note: the generator fixes labels to `""` and metadata to `default`, so the
> conclusion guarantees the same *expression* and *variable* content, not
> necessarily identical label/metadata.

---

## 3. Function generator (`FunctionHasTypeAGen.lean`)

The function generator produces `Function = LFunc CoreLParams` values and is
proved sound/complete w.r.t. `FuncHasTypeA C Γ` (the annotated instantiation of
`FuncHasType'` from `Strata.Languages.Core.FunctionTypeSpec`). It delegates
type generation to `genLMonoTy` and body/measure generation to `genLExpr`, so
its side-conditions are drawn almost entirely from the expression layer (§1).

### Key simplification: the ambient context is irrelevant

The annotated typing spec used by `FuncHasTypeA` is

```
instance instHasTypeA : ExprTypingSpec LMonoTy where
  embed := id
  exprTyped := fun _C _Γ e mty => LExpr.HasTypeA [] e mty
```

so `exprTyped` **ignores** the ambient context (`_C`, `_Γ`) and `embed = id`.
The `bodyTyped`/`measureTyped` obligations of `FuncHasType'` therefore reduce
*definitionally* to `HasTypeA' [] body output` and `HasTypeA' [] m .int` — exactly
what `genLExpr … [] tvars [] depth τ` produces. **Consequence:** unlike `genCmd`,
the function generator needs **no** `VarCtxCorresponds`-style context
correspondence, no fresh-name disjointness, and the soundness/completeness
theorems hold for *any* ambient `C`/`Γ`.

The generator also fixes `pctx = []` (no polymorphic operators), which makes the
`hSimplePolyOps` obligation of `genLExpr_sound` **vacuous**: `polyOpsForResult []
τ … = []` (proved as `polyOpsForResult_nil`, line 152), so there are no entries
to constrain.

### Shared helper lemmas

| Lemma | Location | Role |
|---|---|---|
| `allFtvarsIn_freeVars` | line 47 | `allFtvarsIn tvars τ → ∀ v ∈ LMonoTy.freeVars τ, v ∈ tvars`. Bridges `genLMonoTy`'s support witness to the spec's `noUndeclaredVars`, which is phrased via `freeVars`. |
| `freeVars_mkArrow'` | line 71 | `freeVars (mkArrow' out vals)` splits into `freeVars out ∨ ∃ t ∈ vals, freeVars t`. Lets `noUndeclaredVars` be discharged component-wise (output + each input type). |
| `genInputs_support` | line 138 | Support of `genInputs`: keys are `Nodup`, every value is in `genLMonoTy tvars depth`'s support. Relies on the local `dedup` facts (`StrataGenerators/FunctionHasTypeAGen/Dedup.lean`). |
| `polyOpsForResult_nil` | line 152 | `polyOpsForResult [] τ … = []` — discharges `hSimplePolyOps` for `pctx = []`. |

### 3.1 `genOptExpr_sound` (line 159)

```
o ∈ support (genOptExpr fctx octx tvars depth τ) ∧ o = some e → HasTypeA' [] e τ
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hτ` | `SimpleType τ` | Passed straight through to `genLExpr_sound` (§1.1) — the body/measure type must be generable. |
| `hSimpleOps` | `∀ p ∈ octx, SimpleType p.2` | Inherited from `genLExpr_sound`: the Indir path over `octx` needs simple operator argument types. |

The `none` case is vacuous; `hSimplePolyOps` is discharged internally via
`polyOpsForResult_nil`, so it does **not** appear as a hypothesis.

### 3.2 `genFunction_sound` (line 187)

```
func ∈ support (genFunction fctx octx depth) → FuncHasTypeA C Γ func
```

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hSimpleOps` | `∀ p ∈ octx, SimpleType p.2` | The **only** side-condition. Required so `genOptExpr_sound` (hence `genLExpr_sound`) applies to the body and measure. |

The four `FuncHasType'` obligations are discharged as follows, needing nothing
beyond `hSimpleOps`:

- `inputsNodup` / `typeArgsNodup` — from the `dedup`-based `genInputs_support` /
  `genTypeArgs_nodup` (the generator dedups both lists).
- `noUndeclaredVars` — `genLMonoTy_support` gives `allFtvarsIn typeArgs τ` for the
  output and each input type; `allFtvarsIn_freeVars` + `freeVars_mkArrow'` convert
  that into the spec's `freeVars ⊆ typeArgs`.
- `bodyTyped` / `measureTyped` — the annotated spec reduces them to `HasTypeA' []
  …`, discharged by `genOptExpr_sound` (`.int` is a `SimpleType` for the measure).

**Status:** proved. `genFunction_sound_nil` (line 224) specializes to `octx = []`,
where `hSimpleOps` is vacuously true — a fully hypothesis-free soundness entry
point (mirroring `genCmd_sound_nil`).

### 3.3 `genFunction_complete` (line 329)

```
FuncHasTypeA C Γ func ∧ (default-field + reachability side-conditions)
→ func ∈ support (genFunction fctx octx depth)
```

The generator only varies six fields (`name`, `typeArgs`, `inputs`, `output`,
`body`, `measure`) and leaves the rest at their `LFunc` defaults, so
completeness requires the target function's remaining fields to *be* those
defaults, plus per-component reachability (mirroring `genCmd_complete`'s
`hExprComplete` / `hNameReach` / `hTyReach`).

| Side-condition | Statement | Why it is needed |
|---|---|---|
| `hwt` | `FuncHasTypeA C Γ func` | The function must be well-typed; `bodyTyped`/`measureTyped` supply the `HasTypeA' []` facts the expression-completeness hypotheses consume, and `*Nodup` feed the `dedup` fixed-point reachability. |
| `hConstr`, `hRec`, `hAttr`, `hEval`, `hAxioms`, `hPre` | `func.isConstr = false`, `func.isRecursive = false`, `func.attr = #[]`, `func.concreteEval = none`, `func.axioms = []`, `func.preconditions = []` | The generator hardcodes these fields to their defaults; a function differing in any of them is unreachable. (The `Unit`-valued name metadata needs no hypothesis — it is definitionally `()`.) |
| `hNameReach` | `func.name.name ∈ support (String.arbitrary)` | The name is drawn from `String.arbitrary`; only its alphanumeric strings are reachable. |
| `hTyArgsReach` | `func.typeArgs ∈ support (genNameList depth)` | `typeArgs` is `dedup` of a `genNameList` draw. Combined with `typeArgsNodup` (from `hwt`), `dedup_eq_self` makes the list a fixed point, hence reachable via `genTypeArgs`. |
| `hInputNamesReach` | `func.inputs.keys.map (·.name) ∈ support (genNameList depth)` | Same reasoning for the input identifier names, which are `dedup`-ed inside `genIdents`. |
| `hInputTyReach` | `∀ ty ∈ func.inputs.values, ty ∈ support (genLMonoTy func.typeArgs depth)` | Each input type is sampled by `genLMonoTy`; non-generable input types are unreachable. |
| `hOutputReach` | `func.output ∈ support (genLMonoTy func.typeArgs depth)` | The output type is sampled by `genLMonoTy`. |
| `hBodyReach` | `∀ b, func.body = some b → b ∈ support (genLExpr fctx octx [] func.typeArgs [] depth func.output)` | If a body exists it must be reachable by `genLExpr` at the output type. This is the function-level analogue of `GenLExprComplete`; the caller discharges it via `genLExpr_complete` (§1.6), whose own side-conditions (`emptyNames`, `allVarsInCtx`, `AllTypesSimple`, `termDepth ≤ depth`) apply to the body. |
| `hMeasureReach` | `∀ m, func.measure = some m → m ∈ support (genLExpr fctx octx [] func.typeArgs [] depth .int)` | Same for the measure, at type `int`. |

**Status:** proved. Note the completeness statement guarantees the same six
generated fields; the fixed-default fields are constrained by hypothesis, and
name metadata is definitionally trivial.

---

## 4. Summary table

| Theorem | Direction | Side-conditions | Assumed (unproved) |
|---|---|---|---|
| `genLExprBase_sound` | sound | `SimpleType τ` | — |
| `genIndirPoly_sound` | sound | `SimpleType τ`, simple poly-op args | — |
| `genLExpr_sound` | sound | `SimpleType τ`, simple op/poly-op args | — |
| `genLExprBase_complete` | complete | `SimpleType τ`, `HasTypeA'`, `emptyNames`, `allVarsInCtx`, `AllTypesSimple`, `termDepth ≤ depth` | — |
| `genLExpr_complete` | complete | base conditions ∨ `IsPolyApp` | — |
| `genCmd_sound` | sound | `VarCtxCorresponds`, `GenLExprSound`, `FreshNamesDisjointFromExprs` | — (all discharged for `fctx = []`) |
| `genCmd_sound_nil` | sound | `VarCtxCorresponds`, `GenLExprSound` (at `fctx = []`) | — |
| `genCmds_sound` | sound | `GenCmdSoundEnv` (bundles the above, quantified over contexts) | — (`freshDisjoint` discharged for `fctx = []`) |
| `genCmds_sound_nil` | sound | `GenCmdSoundEnv` at `fctx = []` (via `genCmdSoundEnv_nil`) | — |
| `genCmd_complete` | complete | `CmdHasTypeA`, `GenLExprComplete`, `hNameReach`, `hTyReach`, `hVarInCtx` | — |
| `genOptExpr_sound` | sound | `SimpleType τ`, simple op args | — (`hSimplePolyOps` vacuous at `pctx = []`) |
| `genFunction_sound` | sound | simple op args (`hSimpleOps`) | — |
| `genFunction_sound_nil` | sound | — (at `octx = []`) | — |
| `genFunction_complete` | complete | `FuncHasTypeA`, default non-typing fields, name/typeArgs/input-name/type/body/measure reachability | — |

## 5. Notes on the (formerly) assumed conditions

- **`FreshNamesDisjointFromExprs`** is no longer an open assumption. It is now
  proved for an empty fvar context as `freshNamesDisjointFromExprs_nil`
  (`CmdHasTypeAGenSound.lean:25`). The proof does *not* reason about name
  collision at all: with `fctx = []`, `pickFVar` is unreachable, so every
  generated expression has *no* free variables (`getVars e = []`, via
  `genLExpr_no_fvars` in `HasTypeAGen.lean:4273`). A fresh name therefore
  trivially fails to occur in the empty variable list, regardless of what the
  name is.

  Crucially, the condition is **false for nonempty `fctx`**: `genLExpr` draws
  free variables from `fctx` via `pickFVar`, and a name fresh with respect to
  the command context `ctx` can still coincide with an `fctx` entry. So this is
  not a general theorem that was merely unproved — it holds *only* at the
  `fctx = []` instantiation, which is exactly what both test harnesses use. (An
  earlier version of this document claimed it was "morally true" in general;
  that was incorrect.)

  The proof is packaged into hypothesis-free entry points in
  `CmdHasTypeAGenSound.lean`: `genCmd_sound_nil` (line 40),
  `genCmdSoundEnv_nil` (line 56), and `genCmds_sound_nil` (line 75). These
  leave only the genuine context-dependent obligations (`hCorr`, `hExprSound` /
  the `toTCtx` fields) to the caller. The file is registered as its own
  `lean_lib` in `lakefile.toml`. All proofs are `sorry`-free.

- **`GenLExprSound` / `GenLExprComplete`** are stated as `def` predicates in
  `CmdHasTypeAGen.lean` and taken as hypotheses there to avoid a Mathlib
  dependency in the command layer; they are *discharged* by the proved
  `genLExpr_sound` / `genLExpr_complete` in `HasTypeAGen.lean`.

- **Function generator has no context-correspondence assumptions.** Because the
  annotated `instHasTypeA` ignores the ambient context (§3), the function
  soundness/completeness theorems carry *none* of the `VarCtxCorresponds` /
  `FreshNamesDisjointFromExprs` baggage of the command layer. The only genuine
  soundness side-condition is `hSimpleOps` (simple operator types), inherited
  from `genLExpr_sound`; it vanishes at `octx = []` (`genFunction_sound_nil`).
  Completeness additionally requires the target's non-generated fields to be at
  their `LFunc` defaults and per-component reachability — the latter delegated to
  `genLExpr_complete` (for the body/measure) and the `dedup` fixed-point argument
  (for the `Nodup` `typeArgs`/inputs), the three local `dedup` facts living in
  `StrataGenerators/FunctionHasTypeAGen/Dedup.lean`. All proofs are `sorry`-free
  and depend only on `propext` / `Classical.choice` / `Quot.sound`.
