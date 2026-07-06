# Refactor Plan: `VarCtx` from `List` to `Map`

**Status:** DONE. `VarCtx` is now `Map (Identifier Unit) LMonoTy` (a bare `Map`,
Option-B-style, not the structure of Option A). Because Strata's
`Map α β := List (α × β)` is an `@[expose] def`, positional `length`/`getD`
indexing survives unchanged, so the `set`-sampling proofs carried over directly
and the `choose`-based distribution is unchanged — the Option-A concern about
positional indexing did not materialize. The only substantive changes were the
key type (`String` → `Identifier Unit`, so context values are threaded as
identifiers and lookups use `Map.find?`) and, in the proofs, using explicit
`List.Mem` / list ascriptions where `Map`'s non-`abbrev`-ness blocks `∈` and
`++` instance synthesis. `genCmd_sound`, `genCmd_complete`, `genCmds_sound`
(and the `_nil` variants) remain axiom-clean. The step-by-step plan below is
retained for historical context.

## Goal

Change the command generator's output context representation from

```lean
abbrev VarCtx := List (String × LMonoTy)   -- CmdHasTypeAGen/Core.lean:26
```

to a `Map` keyed by variable name, mirroring `TContext.types` (the `Map`
field of the semantic typing context). The motivation is to collapse the
`VarCtxCorresponds` bridge (`CmdHasTypeAGen.lean:33`) — which exists *only*
to reconcile the `List` representation with `TContext.types` — toward a
structural/identity correspondence, simplifying `toTCtx` and `toTCtx_cons`
in `GenCmdSoundEnv`.

## Coordination (resolved)

The freshness proof has landed, so the sequencing concern below is now
historical. **What actually changed matters for this refactor:**

- The proof did **not** reshape `VarCtx.isFresh` / `genFreshName`
  (`CmdHasTypeAGen/Core.lean:39, 52`) as originally feared. Those definitions
  are untouched. Instead the proof lives in a *new* file,
  `StrataGenerators/CmdHasTypeAGenSound.lean`, and works by showing generated
  expressions have no free variables at all (`genLExpr_no_fvars`) at
  `fctx = []` — it never reasons about `isFresh` collision.
- Consequence: **step 10 (rebasing the freshness proof) is now lighter than
  planned.** The proof does not depend on the *representation* of `VarCtx`,
  only on `genLExpr_no_fvars` (expression layer, unaffected by this refactor)
  and `HasVarsPure.getVars`. The only `VarCtx`-typed surface in the new file is
  the *parameter* `ctx : VarCtx` threaded through `freshNamesDisjointFromExprs_nil`,
  `genCmd_sound_nil`, `genCmdSoundEnv_nil`, `genCmds_sound_nil`. Update those
  signatures to the new representation; the proof bodies should be unaffected.
- **Add `CmdHasTypeAGenSound.lean` to the surface-area list** (below) — it was
  not present when this plan was first written.

Original sequencing rationale (retained for context): the freshness proof was
small and localized (~25 references, added theorems), while this refactor is
invasive (~80 references, changes a foundational `abbrev`), so the freshness
work was allowed to land first rather than running concurrently and racing on
the same definitions.

## The crux: positional indexing in `set` generators

The single hardest part. `genSetDet`/`genSetNondet`
(`Core.lean:86–97`) pick an existing variable by **position**:

```lean
let idx ← choose 0 (ctx.length - 1) (by omega)
let (name, mty) := ctx.getD idx.down ("", .bool)
```

A `Map` has no canonical positional indexing. Two options:

- **Option A (recommended): keep an ordered key list for sampling, store types in a `Map`.**
  Represent `VarCtx` as a structure `{ names : List String, types : Map String LMonoTy }`
  (or reuse `TContext`'s own `Map` type directly). Sample by indexing into
  `names`; look up the type via the `Map`. This preserves the uniform-over-
  variables sampling distribution the current generator has and keeps the
  `choose`-based proof shape intact.

- **Option B: make `VarCtx` a bare `Map`, derive an ordered key list on demand**
  via `Map.toList`/`keys` inside the `set` generators. Simpler type, but the
  sampling proof must now reason about `Map.toList`'s ordering, and the
  distribution depends on `Map` iteration order. More proof churn, riskier.

Recommend **Option A**: it isolates the `Map` to the type-lookup path (where
the `TContext` correspondence lives) while leaving the sampling path on a
`List` (where positional `choose`/`getD` proofs already work). This minimizes
proof rewrites and keeps the distribution unchanged.

## Surface area

`VarCtx` appears in ~80 sites across:

| File | Role | Impact |
|---|---|---|
| `CmdHasTypeAGen/Core.lean` | `VarCtx` def + `names`/`find?`/`isFresh`, `fallbackFreshName`, `genFreshName`, `GenCmdResult.outCtx`, all sub-generators, `genCmd`, `genCmds` | **High** — the type definition and every consumer |
| `CmdHasTypeAGen.lean` | `VarCtxCorresponds`, `genCmd_support_iff`, `genCmd_sound(_env)`, `genCmd_complete`, `genCmds_sound`, `GenCmdSoundEnv` | **High** — proofs destructure the list |
| `CmdHasTypeAGenSound.lean` (new) | `freshNamesDisjointFromExprs_nil`, `genCmd_sound_nil`, `genCmdSoundEnv_nil`, `genCmds_sound_nil` | **Low** — only `ctx : VarCtx` parameters; proof bodies depend on `genLExpr_no_fvars`, not the representation |
| `HasTypeAGen*.lean`, `HasTypeGen.lean`, `Scratch.lean` | mostly unrelated `FVarCtx`/`OpCtx` (also `List (String × LMonoTy)`) | **Verify only** — do NOT change these; confirm grep hits are not the command `VarCtx` |

> Caution: `FVarCtx` and `OpCtx` (`HasTypeAGen/Core.lean`) are *also*
> `List (String × LMonoTy)`. A blind rename would corrupt them. Scope every
> edit to the command-layer `VarCtx` specifically.

## Step-by-step

1. **Define the new representation** (`CmdHasTypeAGen/Core.lean:26`).
   Per Option A, introduce a structure with an ordered `names : List String`
   and `types : <Map type matching TContext.types>`. Re-implement
   `VarCtx.names`, `VarCtx.find?`, `VarCtx.isFresh` against it. Keep the same
   public signatures so downstream call sites need minimal change.

2. **Update insertion** in `genInitDet`/`genInitNondet` (`Core.lean:75, 83`).
   Replace `(name, mty) :: ctx` with the structure's insert operation
   (append to `names`, insert into `types`). Define a `VarCtx.insert` helper
   so `toTCtx_cons` has a clean lemma target.

3. **Update sampling** in `genSetDet`/`genSetNondet` (`Core.lean:86–97`).
   Index into `ctx.names` for the name; look up its type via `ctx.types`.
   The `choose 0 (ctx.length-1)` shape carries over to `ctx.names.length`.

4. **Update `GenCmdResult.outCtx`** type (`Core.lean:66`) — falls out of step 1.

5. **Rework `VarCtxCorresponds`** (`CmdHasTypeAGen.lean:33`). With `types` now
   a `Map`, the correspondence to `Γ.types` becomes a direct relation between
   two `Map`s (ideally `ctx.types ≈ Γ.types` up to the `forAll []` wrapper),
   instead of the current membership-quantified bridge.

6. **Rework `GenCmdSoundEnv.toTCtx` / `toTCtx_cons`** (`CmdHasTypeAGen.lean:494`).
   `toTCtx` should become near-identity on the `types` field; `toTCtx_cons`
   should reduce to a `Map.insert` lemma rather than list-cons reasoning.

7. **Fix the proofs** that destructure the list:
   - `genCmd_support_iff` (`CmdHasTypeAGen.lean:138`): the `set` branches use
     `ctx.length` and `List.mem_cons` (lines 156, 169) — retarget to `names`.
   - `List.getD_mem_of_lt` (line 201) and its uses in `genCmd_sound(_env)`
     (lines 331–345, 544–560): retarget membership reasoning to `ctx.names`
     plus a `names`↔`types` consistency invariant.
   - `genCmd_complete` `hVarInCtx` (`CmdHasTypeAGen.lean:399`): currently
     "exists an index into `ctx`"; restate as `Map` membership.
   - `genCmds_sound` induction (line 580): threads `ctx'` — verify the new
     insert lemma closes the cons step.

8. **Add a representation invariant** if Option A is used: `names` and `types`
   have the same key set (no dangling/duplicate names). Several `set`-branch
   proofs will need it to go from "index into `names`" to "type found in
   `types`". Bundle it into `VarCtxCorresponds` or carry it as a field.

9. **Update `TestSupport.lean` `#eval`s** and the `#eval` smoke tests at
   `CmdHasTypeAGen.lean:611+` (initial-context literals like
   `[("x", .int), ("y", .bool)]` become the new constructor).

10. **Update `CmdHasTypeAGenSound.lean`.** The freshness proof has landed and
    does *not* depend on the `VarCtx` representation (it goes via
    `genLExpr_no_fvars`, not `isFresh`). Only retarget the `ctx : VarCtx`
    parameters of `freshNamesDisjointFromExprs_nil`, `genCmd_sound_nil`,
    `genCmdSoundEnv_nil`, `genCmds_sound_nil` to the new type; the proof bodies
    should compile unchanged once `VarCtxCorresponds`/`GenCmdSoundEnv` (steps
    5–6) are updated. The `(name, mty) :: ctx` insertion in `genCmdSoundEnv_nil`'s
    `toTCtx_cons` signature must move to the new `VarCtx.insert` (step 2).

## Build / verification checkpoints

Build after each of: step 1–4 (generator compiles, proofs may break), step 5–6
(correspondence layer), step 7–8 (proofs green), step 10 (freshness rebased).
Use the Lean LSP (`lean_build` only when imports change; otherwise
`lean_diagnostic_messages` per file) and confirm no new `sorry`/axioms via
`lean_verify` on `genCmd_sound`, `genCmd_complete`, `genCmds_sound`.

## Risk assessment

- **Distribution change:** Option A preserves uniform-over-variables sampling;
  Option B does not. Prefer A. Note any change in
  `docs/generator-distribution-analysis.md`.
- **`FVarCtx`/`OpCtx` confusion:** highest-likelihood mechanical error. Scope
  edits to the command `VarCtx` only.
- **Scope creep into the expression layer:** none expected — `genLExpr` takes
  `[]` for its fvar/op contexts from the command layer, so the boundary is clean.
- **Decision pending:** whether to introduce a fresh structure (Option A) or
  reuse `TContext` directly as `VarCtx`. Reusing `TContext` maximizes the
  correspondence simplification but couples the generator to the full semantic
  context type; a dedicated structure keeps the generator self-contained.
  Recommend deciding this at step 1 with the current code in front of you.
