# Function generator (`genFunction`) — progress & handoff

Goal: a generator of random well-typed Strata Core `Function`s
(`Function = LFunc CoreLParams`), proved sound and complete w.r.t. the
`FuncHasTypeA` typing spec in `Strata/Languages/Core/FunctionTypeSpec.lean`.
Mirrors the existing `genCmd` / `genLExpr` machinery in
`StrataGenerators/CmdHasTypeAGen/` and `StrataGenerators/HasTypeAGen/`.

## What's done

### 1. Bumped the Strata dependency (DONE, builds)
- The previously pinned rev `43d90cf40` did **not** contain
  `Strata/Languages/Core/FunctionTypeSpec.lean` (it was added later in commit
  `c3c222aef`, "Working on Function types").
- Updated `lakefile.toml`: `rev = "43d90cf40"` → `rev = "66dcd82d1"` (current
  tip of `origin/main` on https://github.com/ngernest/Strata, which contains
  `FunctionTypeSpec.lean`).
- Ran `lake update Strata`, updating `lake-manifest.json`.
- **Verified** the bump did not break existing proofs: `lake build` succeeds for
  `StrataGenerators.HasTypeAGen`, `StrataGenerators.CmdHasTypeAGen`,
  `StrataGenerators.CmdHasTypeAGenSound` (only the pre-existing 3 `sorry`
  warnings in `Strata.DL.Lambda.LExprTypeSpec`, which are upstream and unrelated).

### 2. Wrote the generator (DONE, builds)
- New file: `StrataGenerators/FunctionHasTypeAGen/Core.lean` (Mathlib-free,
  mirrors `CmdHasTypeAGen/Core.lean`). Builds clean via
  `lake build StrataGenerators.FunctionHasTypeAGen.Core`.
- Added two `lean_lib` entries to `lakefile.toml`:
  `StrataGenerators.FunctionHasTypeAGen.Core` and
  `StrataGenerators.FunctionHasTypeAGen` (the latter file — the proofs — does
  **not exist yet**, so a full `lake build` will fail on it until created; see TODO).
- Generator structure (`genFunction fctx octx depth : G Function`):
  - `name`     ← `String.arbitrary`
  - `typeArgs` ← `genTypeArgs` = `List.dedup <$> genNameList` (so `Nodup`)
  - `inputs`   ← `genInputs typeArgs` = distinct idents (`genIdents`, via
    `List.dedup` on the mapped identifiers) each paired with `genLMonoTy typeArgs`
  - `output`   ← `genLMonoTy typeArgs depth`
  - `body`     ← `genOptExpr … output` (`none`, or `some` of `genLExpr … output`)
  - `measure`  ← `genOptExpr … .int`
  - all other `LFunc` fields left at defaults.

### 3. Key correctness insight (drives both proofs)
The spec is parameterized over the `ExprTypingSpec` typeclass. The **annotated**
instance used by `FuncHasTypeA` is:

```
instance instHasTypeA : ExprTypingSpec LMonoTy where
  embed := id
  exprTyped := fun _C _Γ e mty => LExpr.HasTypeA [] e mty
```

So `exprTyped` **ignores the typing context** (`_C`, `_Γ`) and `embed = id`.
Therefore:
- `bodyTyped`   reduces *definitionally* to `LExpr.HasTypeA [] body output`.
- `measureTyped` reduces to `LExpr.HasTypeA [] m .int`.

Both are exactly what `genLExpr … [] typeArgs [] depth τ` (empty bvar context,
empty pctx) produces. **Confirmed definitionally** (an `Iff.rfl`/`rfl`-style
check passed in a scratch file). This is what makes functions *easier* than
commands: no `VarCtx ↔ TContext` correspondence is needed at all.

The remaining `FuncHasType'` obligations:
- `inputsNodup : func.inputs.keys.Nodup` — from `List.dedup` on the idents.
  Note `inputs.keys` = the identifier list; `genIdents` dedups the *identifiers*
  (`⟨s,()⟩`), and `keys` of the zipped map = that deduped ident list.
- `typeArgsNodup : func.typeArgs.Nodup` — directly from `List.dedup`.
- `noUndeclaredVars : ∀ v ∈ freeVars (mkArrow' output inputs.values), v ∈ typeArgs`
  — because every type came from `genLMonoTy typeArgs`, whose support lemma
  `genLMonoTy_support` gives `allFtvarsIn typeArgs τ`, i.e. all ftvars ⊆ typeArgs.

## Reusable lemmas already proven upstream (in `HasTypeAGen.lean`)
- `genLExpr_sound` — support ⊆ well-typed (needs `SimpleType τ` + op simplicity
  side-conditions; for us `octx`/`pctx` from the caller, `τ` simple by
  `genLMonoTy_simple`).
- `genLExpr_complete` — well-typed (+ side conditions: `emptyNames`,
  `allVarsInCtx`, `AllTypesSimple`, `termDepth ≤ depth`) OR `IsPolyApp` ⊆ support.
- `genLMonoTy_support` : `τ ∈ support (genLMonoTy tvars n) ↔ SimpleType τ ∧
  monoTyDepth τ ≤ n ∧ allFtvarsIn tvars τ`.
- `genLMonoTy_simple`.
- `mem_mapM_iff`, `mem_support_bind_iff`, `mem_support_pick_iff`,
  `mem_support_map_iff`, `mem_support_choose_iff`, `String_arbitrary_support_set`,
  `Nat_arbitrary_support_set` — all in `SetGen`/`HasTypeAGen`.

The command-level analogues to mirror are `genCmd_sound` / `genCmd_complete` in
`StrataGenerators/CmdHasTypeAGen.lean` and the hypothesis-discharging pattern in
`StrataGenerators/CmdHasTypeAGenSound.lean`.

### 4. Proofs completed (DONE, builds clean, no `sorry`)
- `StrataGenerators/FunctionHasTypeAGen/Dedup.lean` — the three local `dedup`
  facts (`nodup_dedup`, `mem_dedup`, `dedup_eq_self`), isolated in their own file
  (as the doc recommended). Own `lean_lib` entry in `lakefile.toml`.
- `StrataGenerators/FunctionHasTypeAGen.lean` — soundness + completeness:
  - Free-var helpers `allFtvarsIn_freeVars`, `freeVars_mkArrow'`.
  - Support lemmas `genTypeArgs_nodup`, `genIdents_nodup`,
    `mapM_genInputs_keys_values`, `genInputs_support`.
  - `genOptExpr_sound` (uses `polyOpsForResult_nil` to discharge the poly side
    condition, since `genFunction` fixes `pctx = []`).
  - **`genFunction_sound`** — every generated function is `FuncHasTypeA C Γ` for
    any `Γ`, given `octx` holds only simple types; plus a hypothesis-free
    `genFunction_sound_nil` at `octx = []`.
  - Completeness helpers `mapM_genInputs_complete`, `genIdents_complete`,
    `genTypeArgs_complete`, `genInputs_complete`, `genOptExpr_complete`.
  - **`genFunction_complete`** — every well-typed function with default
    non-typing fields and per-component reachability (name/typeArgs/input
    names/types/body/measure) is in `genFunction`'s support. Reachability
    hypotheses mirror `genCmd_complete`'s `hExprComplete`/`hNameReach`/`hTyReach`.
- `lake build` is green (only the pre-existing `HasTypeGen.lean` and upstream
  `LExprTypeSpec` `sorry`s remain, both unrelated). `lean_verify` confirms both
  top-level theorems reduce to `propext`/`Classical.choice`/`Quot.sound` only.

## THE BLOCKER (RESOLVED): `List.dedup` import collision

`List.dedup` is **defined twice** and the two definitions collide depending on
imports:

1. **Strata's** `List.dedup` in `.lake/packages/Strata/Strata/DL/Util/List.lean`
   (line 16). Strata uses the **Lean module system**: the *definition* is marked
   `public def dedup`, so it IS exported and is what my `Core.lean` compiles
   against. But its **lemmas are NOT `public`** (`nodup_dedup`, `mem_of_mem_dedup`,
   `mem_dedup_of_mem`, `dedup_eq_self`-style, etc. at lines 42+), so they are
   **not importable** — `List.nodup_dedup` resolves to "unknown constant" even
   after `import Strata.DL.Util.List`.

2. **Mathlib's** `List.dedup` (+ its rich lemma set `List.nodup_dedup`,
   `List.mem_dedup`, `List.dedup_eq_self`, …). But importing a Mathlib file that
   defines it (e.g. `import Mathlib.Data.List.Dedup`) **fails to elaborate**:

   ```
   error: import Mathlib.Data.List.Dedup failed, environment already contains
   'List.dedup' from Strata.DL.Util.List
   ```

   i.e. once anything transitively pulls in Strata's `Util.List`, you can't also
   pull in Mathlib's `dedup` module — the name is already taken.

`HasTypeAGen.lean` already imports Mathlib transitively (via
`Basalt.Examples.ArbNat` → Mathlib) AND Strata's `Util.List` transitively, so the
proof file (which must import `HasTypeAGen` for the reusable `genLExpr` lemmas)
is stuck with **Strata's `dedup` definition but no dedup lemmas from either side**.

### Resolution (DONE): prove the 3 dedup facts locally in `Dedup.lean`
We only need three facts about Strata's `dedup`, and all three are provable in a
few lines by induction directly on `List.dedup`'s definition
(`| a :: as => let as := as.dedup; if a ∈ as then as else a :: as`). Two already
verified in scratch; the third had a trivial typo:

```lean
-- FACT 1 (VERIFIED in scratch): dedup is Nodup
theorem my_nodup_dedup {α} [DecidableEq α] (l : List α) : l.dedup.Nodup := by
  induction l with
  | nil => simp [List.dedup]
  | cons a as ih =>
    simp only [List.dedup]; split
    · exact ih
    · rename_i h; exact List.nodup_cons.mpr ⟨h, ih⟩

-- FACT 3 (VERIFIED in scratch): Nodup → dedup = self  (needed for completeness)
theorem my_dedup_eq_self {α} [DecidableEq α] (l : List α) (h : l.Nodup) :
    l.dedup = l := by
  induction l with
  | nil => simp [List.dedup]
  | cons a as ih =>
    obtain ⟨hnotin, hnd⟩ := List.nodup_cons.mp h
    simp only [List.dedup]; rw [ih hnd]; simp [hnotin]

-- FACT 2 (had a typo; here is the corrected version to verify):
theorem my_mem_dedup {α} [DecidableEq α] (l : List α) (a : α) :
    a ∈ l.dedup ↔ a ∈ l := by
  induction l with
  | nil => simp [List.dedup]
  | cons b bs ih =>
    simp only [List.dedup]; split
    · rename_i h
      rw [ih, List.mem_cons]
      exact ⟨fun hh => Or.inr hh,
             fun hh => hh.elim (fun heq => heq ▸ ih.mp h) id⟩
    · rename_i h; rw [List.mem_cons, List.mem_cons, ih]
```

`List.nodup_cons` and `List.mem_cons` come from core/Batteries and ARE available
(no collision), so these local lemmas compile in the `HasTypeAGen`-importing
environment. Put them near the top of `FunctionHasTypeAGen.lean`.

(Alternative, not recommended: switch the generator to `List.eraseDups` if that
avoids the collision, or ask upstream Strata to mark the dedup lemmas `public`.
Local re-proof is the least invasive and keeps the generator file unchanged.)

## TODO (all done — kept for reference)

1. Create `StrataGenerators/FunctionHasTypeAGen.lean`:
   - `import StrataGenerators.HasTypeAGen`,
     `import StrataGenerators.FunctionHasTypeAGen.Core`,
     `import Strata.Languages.Core.FunctionTypeSpec`.
   - Add the 3 local dedup lemmas above.
   - Helper: `allFtvarsIn tvars τ → ∀ v ∈ LMonoTy.freeVars τ, v ∈ tvars`
     (induction on `τ` via `@[induction_eliminator] LMonoTy.induct`; use
     `LMonoTys.freeVars_subset`). **Drafted & essentially verified in scratch**
     (`/tmp/test_helpers.lean` — the two helpers compiled once the Mathlib-dedup
     import was removed).
   - Helper: `freeVars (mkArrow' out vals)` membership splits into
     `freeVars out ∨ ∃ t ∈ vals, freeVars t` (induction on `vals`, using
     `LMonoTy.mkArrow'_cons`/`_nil`). **Drafted & verified in scratch.**
   - `genFunction_sound`: intro a member of the support, `simp` through the
     `bind`/`pure`/`pick`/`map` support lemmas to expose typeArgs/inputs/output/
     body/measure witnesses, then build the `FuncHasType'` structure:
     - `inputsNodup`/`typeArgsNodup` from the dedup facts,
     - `noUndeclaredVars` from `genLMonoTy_support`'s `allFtvarsIn` + the two
       freeVars helpers,
     - `bodyTyped`/`measureTyped` from `genLExpr_sound` (context ignored — reduce
       `exprTyped … (embed …)` to `HasTypeA [] …` by `rfl`/`change`/`simp
       [instHasTypeA]`). Body/measure `none` cases discharge vacuously.
     - Soundness needs the caller's `octx`/`pctx` simplicity side-conditions,
       exactly like `GenLExprSound` in `CmdHasTypeAGen.lean`. Consider packaging
       them as hypotheses (or specialize to `octx = []`, `pctx = []` for a
       hypothesis-free entry point mirroring `CmdHasTypeAGenSound.lean`).
   - `genFunction_complete`: inversion on `FuncHasTypeA`; show each well-typed
     function is reachable. Will need reachability side-conditions analogous to
     `genCmd_complete` (`hExprComplete`, name/type reachability). Use
     `my_dedup_eq_self` to show a `Nodup` typeArgs/inputs list is a fixed point of
     `dedup`, hence reachable by `genTypeArgs`/`genIdents`.
2. Confirm `inputs.keys` (from `genIdents`-built map) equals the deduped ident
   list — since `genInputs` builds the map by `mapM (fun x => (x, ty))` over the
   deduped idents, `keys` = those idents; prove via a small `mapM`/`keys` lemma
   or `List.map_map`-style reasoning.
3. `lake build StrataGenerators.FunctionHasTypeAGen` until green; then a full
   `lake build`.

## Useful file references
- Spec: `.lake/packages/Strata/Strata/Languages/Core/FunctionTypeSpec.lean`
  (also at `~/Documents/Strata/Strata/Languages/Core/FunctionTypeSpec.lean`).
- `Func` structure fields: `.lake/packages/Strata/Strata/DL/Util/Func.lean`.
- `ExprTypingSpec` / `instHasTypeA`:
  `.lake/packages/Strata/Strata/Languages/Core/CmdTypeSpec.lean` (lines ~33-43).
- `LMonoTy`, `freeVars`, `mkArrow'`, `LMonoTy.induct`:
  `.lake/packages/Strata/Strata/DL/Lambda/LTy.lean`.
- Strata `dedup` + (non-public) lemmas:
  `.lake/packages/Strata/Strata/DL/Util/List.lean`.
- Command-level template proofs: `StrataGenerators/CmdHasTypeAGen.lean`,
  `StrataGenerators/CmdHasTypeAGenSound.lean`.
- Expr-level reusable lemmas: `StrataGenerators/HasTypeAGen.lean`
  (`genLExpr_sound` ~L3497, `genLExpr_complete` ~L4420, `genLMonoTy_support`
  ~L542, `mem_mapM_iff` ~L3242).

## Current build status
- `lake build StrataGenerators.FunctionHasTypeAGen.Core` ✅
- `lake build StrataGenerators.FunctionHasTypeAGen.Dedup` ✅
- `lake build StrataGenerators.FunctionHasTypeAGen` (proofs) ✅ — soundness and
  completeness proven, no `sorry`.
- Full `lake build` ✅ (only pre-existing unrelated `sorry`s in
  `HasTypeGen.lean` and upstream `LExprTypeSpec` remain).
