# Handoff: `genStmt` returns a statement *list* (inline call `init`s)

**Branch:** `test_procedure_properties` · **Status:** generator done & green; proofs
~90% done, 1 real blocker + 2 untouched files · **Nothing committed.** Standing
constraint: **do not commit unless explicitly asked.**

## Goal

`genCallStmt` used to wrap its `init`s in a fresh-label `block` whenever some in-out
arg or out target was absent from the ambient scope:

```
block L₀ { init x int *; init y bool *; call p (inout x, in e, out y) }
```

The user asked for those `init`s **inline in the ambient scope**, no block, no label:

```
init x int *
init y bool *
call p (inout x, in e, out y)
```

Core Strata has **no sequencing statement constructor** (`Statement = Imperative.Stmt`
has only `cmd`, `block`, `ite`, `loop`, `exit`, `funcDecl`, `typeDecl`), so "several
statements inline" *must* be a statement **list**. Two knock-on consequences:

1. A call group's output variable scope is genuinely **larger** than its input
   (`insertAllCtx ctx toInit`), where the blocked version returned `ctx` unchanged.
2. Something in the pipeline has to return a list.

## Design chosen (this is the user's explicit call — keep it)

I first built an intermediate `genStmtChunk` layer that kept `genStmt : G GenStmtResult`
single-statement and put the call branch one level up. The user rejected that in favour of:

> "Wouldn't it be easier to make `genStmt` generate a list of statements, where most of
> these lists are just singletons (except the `call` case where we need extra `init`
> statements before the call), and rename `genStmts` to `genStmtChain` or something to
> reflect the fact that it calls `genStmt` multiple times?"

They're right, and it's cheaper: the `_mem` lemmas and the reachability inductives never
inspect the statement field's *shape*, so they survive with only index-type edits.

So, currently implemented:

- `GenStmtResult.stmt : Statement` → **`GenStmtResult.stmts : List Statement`**
- `genStmt` returns `[s]` in all 8 non-call branches; `genCallStmt` returns
  `initChain toInit ++ [theCall]` with `outCtx = insertAllCtx ctx toInit`
- `genCallStmt` is back as a `frequency` branch of `genStmt` (weight 1, **index 4** in
  both the size-0 and size+1 lists) — so the original weights `4+1+1+1+1` and
  `4+1+1+1+1+2+2+1+2` are restored and `stmtChunkStmtWeight` is gone
- `genCallStmt` no longer takes a `labels` argument (no block ⇒ label set is irrelevant;
  the group is well-typed at *every* `labels`)
- `genStmts` → **`genStmtChain`**, which appends: `pure (r.stmts ++ rest, C'', ctx'')`
- `genStmtChunk` deleted entirely
- `StmtsReachable` → **`StmtChainReachable`**

Note `genStmtChain`'s `len` now bounds the number of **generation steps**, not the
statement count — a call step contributes ≥1 statements. Docstrings say so.

## What is DONE and building green

- `StrataGenerators/StmtHasTypeAGen/Core.lean` — **compiles clean** (`lake build
  StrataGenerators.StmtHasTypeAGen.Core`). All generator changes above, docstrings
  updated, `#eval` smoke tests fixed (`⟨ss, _, _⟩`).
- `StrataGenerators/StmtHasTypeAGen/GenCallStmtSound.lean` — **compiles clean.** New
  helpers added (all proved, no `sorry`):
  - `insertAllCtx` (`VarCtx` analogue of the existing semantic `insertAll`) plus
    `insertAllCtx_cons`, `insertAllCtx_find_not_mem`, `insertAllCtx_functional`,
    `insertAllCtx_keys_subset`
  - `StmtsHasTypeA_singleton : StmtHasTypeA … s … → StmtsHasTypeA … [s] …`
  - The pre-existing block-free `call_mixed_body_sound` (~line 830) is now the sole
    soundness engine for the call group. `call_block_sound`, `call_inline_sound`,
    `call_mixed_sound`, `block_wraps` still exist but are **now unused** — candidates
    for deletion once everything is green (check with `lean_references` first).
- `StrataGenerators/StmtHasTypeAGen.lean` — the **entire soundness half is green**:
  - `GenStmtSoundEnv.toTCtx_insertAllCtx` (new; bridges generator-side `insertAllCtx`
    to semantic `insertAll`)
  - `genCallStmt_outCtx` restated over `GenStmtResult` and **relocated** to just above
    `genCallStmt_sound` (it needs `filter_needsInit_append`, declared below its old home).
    The `Map.Functional` obligation is now *real* (outCtx ≠ ctx) and is discharged via
    `insertAllCtx_functional`, whose two side conditions come from the generator's own
    `Nodup` guard (filter-sublist argument) and from `needsInit` itself.
  - `genCallStmt_sound` now concludes `StmtsHasTypeA … r.stmts …` via
    `call_mixed_body_sound`; one uniform shape, no `toInit.isEmpty` split
  - all 4 leaf soundness lemmas conclude `StmtsHasTypeA … r.stmts …`, wrapped in
    `StmtsHasTypeA_singleton`
  - `genStmt_outCtx_functional` and `genStmt_sound` have their call cases restored at
    `rcases` position 5 (arities back to 5 and 9)
  - `genStmtChain_sound`'s `cons` case is now just `exact StmtsHasTypeA_append hh ht`
  - all `_mem` lemma frequency arities/`.tail` chains restored to the original
    `4+1+1+1+1` / `4+1+1+1+1+2+2+1+2`; `genCallStmt_mem` back at index 4
  - `genStmts_cons_mem` concludes over `r.stmts ++ rest`
  - `StmtReachable`'s statement index is `List Statement`; its 4 nesting constructors
    conclude with singletons; `StmtChainReachable.cons` appends (`ss ++ rest`)
  - `genStmt_complete` / `genStmt_complete_sound` signatures take `ss : List Statement`;
    the capstone's second conjunct is now `StmtsHasTypeA`

## THE ONE REAL BLOCKER

```
error: StrataGenerators/StmtHasTypeAGen.lean:1063:8:
  (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) reached
```

Line 1063 is `theorem genStmt_complete`; the timeout is in its `cases h with` (the
`StmtReachable` inversion). The two follow-on errors at 1126/1127 (`Unknown identifier
genStmt_complete`, `unsolved goals`) are **just fallout** — they vanish when this one is
fixed. Nothing else in the file errors.

Diagnosis: widening `StmtReachable`'s statement index from `Statement` to
`List Statement` made the motive/unifier work harder during `cases`; the four nesting
constructors now force `[Stmt.block …] =?= ss` style unification against a `GenStmtResult`
whose `stmts` field is a list expression.

Things to try, cheapest first:

1. `set_option maxHeartbeats 1000000` — **cannot be placed with `… in` inside the
   `mutual` block** (I tried; parse error: `unexpected token 'set_option'`). Put it as a
   *standalone command before* `mutual` and reset after, i.e.
   ```lean
   set_option maxHeartbeats 1000000
   mutual
   …
   end
   set_option maxHeartbeats 200000
   ```
   This is the 30-second fix and may well be all that's needed. Check whether it's a
   genuine size increase or a unification pathology before settling for it.
2. Replace `cases h with` by `induction h with` / `match h with`, or add explicit
   `(motive := …)`. Often the motive is what's blowing up.
3. If a specific constructor is the culprit, split `genStmt_complete` into per-arity
   helper lemmas and dispatch, keeping `cases` small.
4. `set_option diagnostics true` to see which `whnf` is looping.

## STILL TO DO (untouched — will not compile yet)

### `StrataGenerators/ProcedureHasTypeAGen/MutableVars.lean`
Only the mechanical `genStmts`→`genStmtChain` / `StmtsReachable`→`StmtChainReachable`
rename has been applied. Real work:

- `genCallStmt_mutableVars` (~line 311) — restate over the list result. Drop the
  `labels` argument (gone from `genCallStmt`). `r.stmt` → `r.stmts`, and the two
  `HasVarsImp.modifiedVars/definedVars (P := Expression) r.stmt` become
  `Block.modifiedVars`/`Block.definedVars` over the list. Write set is now
  `initChain toInit ++ [call]`, i.e. `modifiedVars = M.keys ++ T.keys` and
  `definedVars = toInit.map Prod.fst`. Its docstring still describes the **old blocked**
  shape ("`init`-defined by the `block`'s chain", "The output scope is the input `ctx`")
  — both claims are now false; rewrite it.
  The output-scope obligation is no longer trivial (outCtx ≠ ctx); discharge it with the
  new `insertAllCtx_keys_subset`.
- `genStmt_mutableVars` (~line 399) — `r.stmt` → `r.stmts`; the call case is back in the
  `frequency` list at index 4, so `rcases` arities stay 5 / 9 (they're already 5 / 9 in
  the file — the earlier chunk-era reduction was never applied here). Non-call branches
  need their singleton `[s]` unfolded (`Block.modifiedVars [s] = modifiedVars s` etc. —
  check whether the existing `block_modifiedVars_*` lemmas give this by `simp`).
- `genStmtChain_mutableVars` (~line 521) — the `cons` case now **appends** the head group
  instead of consing, so use `block_modifiedVars_append` / `block_definedVars_append`
  plus `trans_step` rather than the cons lemmas.
- Available helpers (already proved in that file): `mem_writable_keys_iff`,
  `mem_append_grow_r`, `mem_append_grow_mid`, `trans_step`, `ite_combine`,
  `initChain_modifiedVars` (`= []`), `initChain_definedVars` (`= news.map Prod.fst`),
  `inlineCall_modifiedVars` (`= M.keys ++ T.keys`), `inlineCall_definedVars` (`= []`),
  `mem_keys_append_exists`.

### `StrataGenerators/ProcedureHasTypeAGen.lean`
Renames applied only. It consumes `genStmtChain_sound` (~542), `genStmtChain_mutableVars`
(~550), `StmtChainReachable` (~702), `genStmts_complete` (~733). The `genStmtChain` *type*
is unchanged, so signatures should survive; the `StmtChainReachable.cons` shape change
(`ss ++ rest`) will propagate. Expect small fixes, not a rewrite.

### Naming consistency (cosmetic, do last)
`genStmts_nil_mem`, `genStmts_cons_mem`, `genStmts_complete` kept their old names (the
blanket rename only hit the `genStmts` *generator* identifier). Rename to
`genStmtChain_*` for consistency — `genStmtChain_sound` and
`genStmtChain_mutableVars` already got renamed by the sweep, so the file is currently
mixed.

## Build / verify sequence

```bash
lake build StrataGenerators.StmtHasTypeAGen.Core   # green now
lake build StrataGenerators.StmtHasTypeAGen        # 1 blocker (above)
lake build StrataGenerators                        # then MutableVars + ProcedureHasTypeAGen
lake build test test-plain                         # then re-run both property suites
```

Redirect to `/tmp/*.log` and `grep -n "error:"` — the build output is huge. `timeout` is
unavailable on this macOS shell; use `run_in_background` instead. `#eval` refuses
sorry-dependent code, use `#eval!`.

**After it's green, re-run the property suites and compare against the pre-refactor
numbers** — the shape change alters what gets generated, so a diff in pass rates is
expected and needs interpreting, not just accepting.

## Pre-existing issues NOT part of this work (don't get distracted)

- `genProcedure` (`ProcedureHasTypeAGen/Core.lean:151`) passes `procs := []`, so **calls
  are still unreachable from the procedure suite**. `genCallStmt []` returns the
  *failing* `default` (`throw (.genError "inhabitedWitness")`), which is the cause of the
  `Generation failure: out of fuel` crashes in the proc harness (single-draw success
  13/4000 vs 45/4000 measured pre-refactor). Offered to the user, never approved.
  Note this refactor slightly *worsens* the odds: the call branch is drawn at weight 1/9
  and immediately fails.
- 9 failing ident/position cases (591 ok) in run1 of the stmt harness — pre-existing.
- `FilterProcedures changed-flag` property fails honestly (hardcoded `true` upstream).
- `PrecondElim changed flag is faithful` is **flaky**, not fixed.
- `genInputMentioningPrecond` can emit tautologies like `x == x`.

## Measurements worth keeping

With an *overlapping* ambient scope (`g:int, r:int` in `ctx`) the block was essentially
never needed: inline 1753 / blocked 0 of 2000 draws. With an *empty* scope it was needed
1044/2000. So the inline form is the common case in realistic contexts — this refactor
is not just cosmetic.
