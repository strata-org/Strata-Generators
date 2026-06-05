# CmdHasTypeA Generator: Architecture and Proof Structure

This document explains the random generator of well-typed imperative commands
in `StrataGenerators/CmdHasTypeAGen/Core.lean` and the accompanying soundness
and completeness proofs in `StrataGenerators/CmdHasTypeAGen.lean`.

## Background: The `CmdHasTypeA` Relation

Strata's `CmdHasTypeA` (defined in `Strata.Languages.Core.CmdTypeSpec`) is the
declarative typing specification for imperative commands, instantiated with
the annotated monomorphic typing relation `HasTypeA`:

```lean
abbrev CmdHasTypeA (C : LContext CoreLParams) :=
  @CmdHasType' LMonoTy C instHasTypeA
```

where `instHasTypeA` sets:
```lean
instance instHasTypeA : ExprTypingSpec LMonoTy where
  embed := id
  exprTyped := fun _C _Γ e mty => LExpr.HasTypeA [] e mty
```

The key insight is that `exprTyped` ignores the `LContext` and `TContext`
parameters and checks the expression against an **empty bound-variable context
`[]`**. This is exactly what `genLExpr fctx octx tvars [] depth τ` produces.

### Typing Rules

| Rule | Command | Input Ctx | Output Ctx | Expression Constraint |
|------|---------|-----------|------------|----------------------|
| `init_det` | `init x τ (det e)` | `Γ.find? x = none`, `x ∉ vars(e)` | `Γ[x ↦ forAll [] mty]` | `HasTypeA [] e mty` |
| `init_nondet` | `init x τ nondet` | `Γ.find? x = none` | `Γ[x ↦ forAll [] mty]` | (none) |
| `set_det` | `set x (det e)` | `Γ.find? x = some (forAll [] mty)` | `Γ` | `HasTypeA [] e mty` |
| `set_nondet` | `set x nondet` | `Γ.find? x = some (forAll [] mty)` | `Γ` | (none) |
| `assert` | `assert l e` | any `Γ` | `Γ` | `HasTypeA [] e bool` |
| `assume` | `assume l e` | any `Γ` | `Γ` | `HasTypeA [] e bool` |
| `cover` | `cover l e` | any `Γ` | `Γ` | `HasTypeA [] e bool` |

## Generator Architecture

### Context Representation: `VarCtx`

The generator uses a flat `VarCtx := List (String × LMonoTy)` to track which
variables are in scope and their monotypes. This is a simplified projection of
Strata's `TContext Unit` (which uses nested `Maps (Identifier Unit) LTy`).

The mapping is: an entry `(x, mty)` in `VarCtx` corresponds to
`Γ.types.find? ⟨x, ()⟩ = some (.forAll [] mty)` in the `TContext`.

### Sub-generators

Each `CmdHasTypeA` constructor has a dedicated sub-generator:

```
genInitDet   : fctx → octx → tvars → ctx → tyDepth → depth → G GenCmdResult
genInitNondet: tvars → ctx → tyDepth → G GenCmdResult
genSetDet    : fctx → octx → tvars → ctx → depth → (ctx.length > 0) → G GenCmdResult
genSetNondet : ctx → (ctx.length > 0) → G GenCmdResult
genAssertCmd : fctx → octx → tvars → ctx → depth → G GenCmdResult
genAssumeCmd : fctx → octx → tvars → ctx → depth → G GenCmdResult
genCoverCmd  : fctx → octx → tvars → ctx → depth → G GenCmdResult
```

Each returns a `GenCmdResult` containing the generated command and the output
context (which is `ctx` for set/assert/assume/cover, and `(name, mty) :: ctx`
for init).

### Top-level Dispatcher: `genCmd`

`genCmd` uses `dite` (decidable if-then-else) on `ctx.length > 0` to determine
which command forms are available:

- **Non-empty context**: all 7 forms (init_det, init_nondet, set_det, set_nondet, assert, assume, cover)
- **Empty context**: 5 forms (init_det, init_nondet, assert, assume, cover)

The `set` commands require at least one variable to exist in the context.
Selection between forms uses nested `pick` (uniform binary choice).

### Expression Generation

All expression sub-terms are generated via `genLExpr fctx octx tvars [] depth τ`
from `HasTypeAGen/Core.lean`. The empty bound-variable context `[]` matches the
`instHasTypeA` specification exactly.

### Fresh Name Generation

`genFreshName` produces names of the form `"v" ++ n` where `n` is drawn from a
geometric distribution (via `Nat.arbitrary`). If the name collides with existing
context entries, a fallback `"v" ++ (ctx.length + n)` is used.

### Sequence Generation: `genCmds`

`genCmds` threads the output context of one command into the input context of
the next, producing a well-typed command sequence:

```lean
def genCmds ... : Nat → G (List (Cmd Expression) × VarCtx)
  | 0     => pure ([], ctx)
  | n + 1 => do
    let ⟨cmd, ctx'⟩ ← genCmd ... ctx ...
    let (rest, ctx'') ← genCmds ... ctx' ... n
    pure (cmd :: rest, ctx'')
```

## Proof Structure

### Import Architecture

The main challenge is the `List.Forall₂` import conflict between
`Strata.DL.Util.List` (imported transitively by `CmdTypeSpec`) and Batteries
(imported by Mathlib). Our solution:

- `CmdHasTypeAGen/Core.lean` imports `CmdTypeSpec` and `HasTypeAGen/Core` (no Mathlib)
- `CmdHasTypeAGen.lean` imports `Core` and `SetGen` (no Mathlib)
- Expression-level soundness (`genLExpr_sound`) lives in `HasTypeAGen.lean` (with Mathlib)

The command-level soundness theorems are stated **parametrically**: they take
an expression well-typing hypothesis `hwt : HasTypeA [] e τ` rather than
deriving it from generator support membership. This cleanly separates concerns
and avoids the import conflict.

### Soundness Proofs

Each soundness theorem has the form:

```lean
theorem genXxx_sound (C Γ ...) (hwt : HasTypeA [] e τ) (preconditions...) :
    CmdHasTypeA C Γ cmd Γ' :=
  CmdHasType'.xxx Γ ... hwt
```

These are direct applications of the `CmdHasType'` constructors — no case
analysis or induction needed. The soundness argument is:

1. `genLExpr` produces expressions satisfying `HasTypeA' [] e τ` (proved in `HasTypeAGen.lean`)
2. `HasTypeA' [] e τ` is definitionally equal to `instHasTypeA.exprTyped _ _ e τ`
3. Therefore the `CmdHasType'` constructor applies directly

The `init_det` case has an additional precondition `x ∉ vars(e)` (the freshly
generated variable name must not appear in the generated expression). This holds
in practice because `genLExpr` with `bctx = []` and `fctx` not containing `x`
cannot produce an expression mentioning `x`.

### Completeness Proofs

Completeness operates at two levels:

**Level 1: Sub-generator completeness** — shows that specific command results
are in the sub-generator's support:

```lean
theorem genAssertCmd_complete (...) (he : e ∈ support (genLExpr ... .bool)) :
    ⟨.assert "" e default, ctx⟩ ∈ support (genAssertCmd ...) := by
  simp [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨e, he, rfl⟩
```

These unfold the monadic definition (`bind` + `pure`) and exhibit the witness.

**Level 2: Embedding into `genCmd`** — shows that sub-generator results are
reachable from the top-level `genCmd`:

```lean
theorem genCmd_reaches_assert (...) (hr : r ∈ support (genAssertCmd ...)) :
    r ∈ support (genCmd ...) := by
  simp [genCmd, mem_support_dite_iff, mem_support_pick_iff]
  by_cases h : ctx.length > 0
  · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))⟩
  · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inl hr))⟩
```

These decompose the `dite` (via `mem_support_dite_iff`) and navigate the nested
`pick` structure (via `mem_support_pick_iff`) to place the result in the correct
disjunct.

### Key Simp Lemmas Used

| Lemma | Purpose |
|-------|---------|
| `mem_support_dite_iff` | Decompose `dite` membership into existential disjunction |
| `mem_support_pick_iff` | Decompose `pick` membership into `∨` |
| `mem_support_bind_iff` | Decompose monadic bind into existential |
| `mem_support_pure_iff` | `a ∈ support (pure b) ↔ a = b` |
| `mem_support_choose_iff` | `a ∈ support (choose lo hi _) ↔ lo ≤ a.down ∧ a.down ≤ hi` |

## Relationship to Expression-Level Proofs

The full soundness story composes two independently-proved results:

```
genLExpr_sound (from HasTypeAGen.lean, uses Mathlib):
  e ∈ support (genLExpr ... τ) → HasTypeA' [] e τ

genAssertCmd_sound (from CmdHasTypeAGen.lean, no Mathlib):
  HasTypeA' [] e .bool → CmdHasTypeA C Γ (.assert "" e default) Γ
```

Composing these gives end-to-end soundness: any command produced by `genCmd`
is well-typed. The composition cannot be stated in a single file due to the
import conflict, but it holds by transitivity at the meta-level (or in a
downstream file that carefully manages imports).

## Possible Extensions

1. **Init freshness proof**: Prove that `genFreshName ctx` always produces a
   name not in `ctx` (requires showing the fallback `"v" ++ (ctx.length + n)`
   is indeed fresh for the generator's naming scheme).

2. **No-variable-capture proof**: Prove that generated expressions from
   `genLExpr fctx octx tvars [] depth τ` (with `fctx` not containing `x`)
   cannot mention `x`, completing the `init_det` soundness for the composed
   system.

3. **Full `genCmd` soundness/completeness**: State and prove a single theorem
   characterizing the exact support of `genCmd` w.r.t. `CmdHasTypeA`.

4. **Sequence soundness**: Prove that `genCmds` produces command sequences
   where successive contexts satisfy the chained `CmdHasTypeA` judgements.
