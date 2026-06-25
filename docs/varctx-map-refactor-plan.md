# Refactor Plan: `VarCtx` from `List` to `Map`

**Status:** Planned, not started. **Blocked on:** the concurrent
`FreshNamesDisjointFromExprs` proof landing first (see "Coordination" below).

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

## Coordination (read first)

Another agent is proving `FreshNamesDisjointFromExprs`. That proof is
**defined in terms of** `VarCtx.isFresh` and `genFreshName`
(`CmdHasTypeAGen/Core.lean:39, 52`), both of which this refactor reshapes.
The two tasks collide on the *same definitions*, not merely the same files.

**Sequencing decision:** land the freshness proof first, then execute this
refactor on top of the finished code. Do **not** run concurrently. Rationale:
the freshness proof is small and localized (adds a theorem, ~25 references),
while this refactor is invasive (~80 references, changes a foundational
`abbrev`). The merge conflict region is identical either way, so isolating in
a worktree would only defer — not remove — the manual reconciliation, and
would force the just-finished proof to be reworked against a moving type.

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
| `CmdHasTypeAGen/TestSupport.lean` | `#eval` smoke tests | Low — update construction syntax |
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

10. **Rebase the freshness proof.** Once it has landed, update its lemmas
    about `VarCtx.isFresh`/`genFreshName` to the new representation. This is
    the planned point of contact with the other agent's work.

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
