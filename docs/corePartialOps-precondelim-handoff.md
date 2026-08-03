# `corePartialOps` + making PrecondElim non-vacuous

**Date:** 2026-07-29, completed 2026-07-30
**Status:** Done. Building green; both harnesses re-run. Not committed (standing
constraint: commit only when explicitly asked).

## What was asked

1. Add a separate `corePartialOps` operator context (distinct from the total-only
   `coreMonoOps`) and hand it to the **procedure generator** so that generated
   procedures contain partial-function calls — making the **PrecondElim**
   transform pass actually fire instead of running as a no-op.
2. Remove the two now-unnecessary aliases in
   `StrataGenerators/HasTypeAGen/TestSupport.lean` (`coreOpCtx`,
   `defaultPolyOps`).

Both done, plus the follow-up work the first pass left open (below).

## Background: what "partial" means here

A Strata `Factory` function is **partial** iff its `preconditions` list is
non-empty. Strata ships pairs of operators: a total one and a
precondition-carrying "safe" variant computing the *same* value:

- `.lake/packages/Strata/Strata/DL/Lambda/IntBoolFactory.lean:404,473` —
  `intDivFunc` (`Int.Div`, total) vs. `intSafeDivFunc` (`Int.SafeDiv`,
  precondition `y ≠ 0`). Same for `Mod`/`SafeMod`, `DivT`/`SafeDivT`,
  `ModT`/`SafeModT`.
- Bitvector `Bv{n}.Safe{Add,Sub,Mul,Neg,UAdd,…}` (overflow preconditions);
  `Bv{n}.Safe{SDiv,SMod}` carry **two** preconditions.
- `Sequence.{select,update,take,drop}` are partial (bounds preconditions) — note:
  no `Safe` in the name. These live in `corePolyOps`, not the monomorphic context.

`PrecondElim` works via `Lambda.collectWFObligations`
(`.lake/packages/Strata/.../DL/Lambda/Preconditions.lean:64`): at each call site
it does `if func.preconditions.isEmpty then [] else …`. Total operators
contribute nothing → no `assert` → `changed = false`. That is why the old proc
tests, generating only from `coreMonoOps`, saw PrecondElim as a **no-op**.

`Factory.callOfLFunc` (`.../DL/Lambda/Factory.lean:521`) matches a fully-applied
`.op` node by **name** against the seeded factory. The generator's `pickOp`
(`HasTypeAGen/Core.lean:145`) emits `LExpr.op () ⟨name, ()⟩ (some τ)` verbatim and
`genApp` applies it to arity, so registering a correctly-typed `("Int.SafeDiv", …)`
entry in the `OpCtx` produces call nodes PrecondElim recognizes — the names do
resolve, since `Core.Factory` includes all four `intSafe*Func`
(`.../Languages/Core/Factory.lean:897–903`).

Soundness of generation is unaffected: `HasTypeA.op` types any annotated op node
at its annotation regardless of name (`pickOp_sound`, `HasTypeAGen.lean:213`), so
`genProcedure` stays sound with the new entries.

## Changes

### 1. `HasTypeAGen/TestSupport.lean`
- **Removed** the `coreOpCtx` and `defaultPolyOps` aliases; inlined
  `coreOpCtx → coreMonoOps` across `TycheViz.lean`, `TestScaffold.lean`, and the
  `{Function,Stmt,Cmd}HasTypeAGen/TestSupport.lean` trio. (`defaultPolyOps` was
  dead.)
- **Added** `corePartialOps : OpCtx := coreMonoOps ++ [Int.SafeDiv, Int.SafeMod,
  Int.SafeDivT, Int.SafeModT]` (all `.int → .int → .int`). These are the
  monomorphic partial ops — chosen over the Sequence ops because they need no
  polymorphic type-sampling and `genProcedure` is called monomorphically.

### 2. Procedure generator points at `corePartialOps`
`TestScaffold.lean:609` (`genProcsWith`) and `TycheViz.lean:842`
(`genProcProp`). All other generators still use `coreMonoOps`, so no other
distribution shifts.

### 3. `ProcedureHasTypeAGen/TestSupport.lean`
- **Rewrote `checkPrecondChangedFlagValid`** to full structural equality:
  `changed == decide (out ≠ prog)`. The old decl-name-sequence proxy was stale
  (faithful only while the pass was a no-op).
- **Added obligation-counting oracle** (`obligationCount`, `cmdObligations`,
  `stmtObligations`/`stmtsObligations`, `programObligations`) — computes the
  *expected* assert count independently of the pass, by asking the seeded
  `Core.Factory` via the same `collectWFObligations` the pass uses. Mirrors
  `transformStmt` branch for branch, including that a loop's guard and measure are
  each asserted **twice** (before the loop, and at the end of the body).
- **Added `checkPrecondCallSiteAsserts`** (new live property) and
  `checkPrecondPreconditionsStripped` (defined but at the time deliberately *not*
  wired — see below; a follow-up change to `genFunction` made it non-vacuous and
  it is now live).
- **Added `#guard`s**: the obligation oracle against `Core.Factory`
  (`Int.SafeDiv` ↦ 1, `Int.Div` ↦ 0, nesting, the loop double-count, `nondet`),
  plus two hand-built PrecondElim reproducers (below).
- **Rewrote the module doc**: the "No partial-function calls … runs as a no-op"
  section and the three `coreOpCtx` mentions are gone; added a section on the new
  honest PrecondElim failure and on why metadata-inclusive structural equality is
  the right oracle.

### 4. Property wiring
`Properties.lean` gains `procPrecondCallSiteAsserts`; the bundle is now twelve
properties (thirteen after the `genFunction` follow-up added
`procPrecondStripped`). Both harnesses and Tyche fold `Properties.procTransforms`
automatically, so `TestMain`/`PlainTestMain`/`TycheViz` needed only comment
updates (counts, and the second expected failure). README enumerates no property
names, so it needed no change.

## Findings

### `DecidableEq` was available all along

The previous pass believed `Decl`/`Program`/`Statement` lack `DecidableEq` and
that a metadata-stripped *string* comparison was needed. Not so: `Program` and
`Decl` both `deriving DecidableEq` (`Core/Program.lean:59,170`) and
`Strata.DL.Imperative.Stmt` supplies a hand-rolled `DecidableEq (Stmt P C)`
(`Stmt.lean:194`) that the derived instances use. So `out ≠ prog` decides
directly — no `stripMetaData`, no formatting, no string compare.

This also dissolves the two blockers in the old handoff:
- The **`stripMetaData` panic** is moot — it is never called. (It also did *not*
  panic on any of 600 probe outputs, so whatever the earlier crash was, it was not
  reproducible here.)
- The **`fmtChanged = 20 > fired = 19` gap** was never metadata noise. It is a
  real bug (next section). Including metadata in the comparison is not merely
  harmless but correct: `transformStmt` re-emits unchanged statements with their
  original `md` untouched; only the freshly built asserts carry
  `propertySummary`-stripped metadata.

### PrecondElim's `changed` flag is NOT faithful — a second honest bug

`transformStmt`'s `.funcDecl` branch (`PrecondElim.lean:328–338`) emits a
`{name}$$wf` block holding the asserts collected from the declared function's
**preconditions and body**, but returns `(hasPreconds, …)` — a flag derived
*solely* from `!decl.preconditions.isEmpty`. So a precondition-free function
whose *body* calls a partial function gets a `$$wf` block inserted and is still
reported unchanged.

Minimal reproducer, now a `#guard` in `TestSupport.lean`:

```
procedure P () { function f () : int { Int.SafeDiv(1, 0) } }
```

→ pass returns `changed = false`, output program `≠` input.

`checkPrecondChangedFlagValid` states the faithful contract and therefore
**FAILS**, pinning this the same way `checkFilterChangedFlagValid` pins
FilterProcedures' hardcoded `changed := true`. Note the two failures are
different in kind: FilterProcedures over-reports (false positive), PrecondElim
under-reports (false negative).

Neither is currently *exploitable*: `Core.PipelinePhase`'s runner discards the flag
outright (`PipelinePhase.lean:101`, `let (_, next) ← pp.transform prog`), and
PrecondElim runs once in a flat pass list, so no downstream analysis is skipped
today. Both are latent bugs against a convention other passes rely on —
`runProgramUntil` (`CoreTransform.lean:357–381`) does drive fixpoint iteration off
`changed` (`if !changed then break`), as ANFEncoder and ProcedureInlining use it.

### Empirical profile (3000 generated programs, `GenProcs` config, sizes 0–100)

| quantity | count |
|---|---|
| PrecondElim reports `changed = true` | 159 (5.3%) |
| program actually differs | 174 (5.8%) |
| inputs carrying ≥1 obligation | 174 |
| `checkPrecondChangedFlagValid` failures | 15 (0.5%) |
| `checkPrecondCallSiteAsserts` failures | 0 |
| `checkPrecondProceduresPreserved` / `OrderPreserved` failures | 0 |
| declaration count grew | 0 |
| inputs with a `funcDecl` carrying its own precondition | 0 |

Re-measured after `genFunction` gained `requires`-clause generation (1500 programs,
final 3:1 input-mentioning bias):

| quantity | count |
|---|---|
| PrecondElim reports `changed = true` | 242 |
| program actually differs | 245 |
| inputs carrying ≥1 obligation | 96 |
| inputs with a `funcDecl` carrying its own precondition | **174** (was 0) |
| `checkPrecondChangedFlagValid` failures | 3 |
| `checkPrecondPreconditionsStripped` failures | **0** |
| `callSiteAsserts` / `proceduresPreserved` / `orderPreserved` failures | 0 |
| declaration count grew | 0 |

The accounting identity still holds exactly: `differs − fired = 245 − 242 = 3 =` the
changed-flag failures. Note `differs (245) > inputs-with-obligations (96)` now,
unlike the pre-precondition run where they were equal — because a declared
precondition is itself stripped, so the pass rewrites programs that carry no
partial-call obligation at all. That is precisely the newly-reachable code path.

`differs = 174 = inputs-with-obligations` exactly, and `174 − 159 = 15 =` the
changed-flag failures. So the pass rewrites the program precisely when obligations
exist, and mis-reports in exactly the `funcDecl`-body cases. There is no residual
unexplained discrepancy — the earlier `20 vs 19` gap is fully accounted for.

`declGrew = 0` because generated procs have **empty-of-partial-calls contracts**:
`mkContractWFProc` only emits a top-level `$$wf` *procedure* when a contract clause
calls a partial function, which never occurred. All effect is inside bodies.

### `preconditionsStripped`: was vacuous, now live

At the time of this change the property was vacuous, but for a *different* reason
than "no partial calls": `genFunction` never populated a declaration's
`preconditions` field, so there was never a precondition for the pass to strip —
0 of 3000 generated programs carried one. Per the repo's standard (a property that
cannot fail is not a test) it was defined and `#guard`-tested but not added to the
bundle.

**Resolved in a follow-up.** `genFunction` now draws an optional `requires` clause
(`genPrecondition`, via the `optionGen` combinator) over the function's *own formal
parameters*. Generating over the formals is not merely a taste preference for
interesting preconditions — `FuncWF.precond_freevars` (`DL/Util/Func.lean:120`)
*requires* a precondition's free variables to be a subset of the input names, so
any other context would generate ill-formed functions. `genPrecondition` therefore
passes `inputsAsFVarCtx inputs` as the free-variable context; since
`genLExprBase`'s variable leaves are drawn only from the supplied `fctx`, every
free variable is a formal by construction.

**Passing the formals as `fctx` is necessary but not sufficient** to actually
*mention* them. `genLExprBase`'s `bool` rules can only reach a variable leaf via
`fvarsOfType fctx .bool`, so a formal is reachable only when it is itself
`bool`-typed — and `genInputs` produces a `bool`-typed formal in only ~2% of
signatures (measured; `noInputs` is also 42–87% depending on depth). Passing the
context alone yielded preconditions mentioning a formal just **3% of the time**
(1 of ~40 clauses per depth bucket).

So `genPrecondition` is biased 3:1 toward `genInputMentioningPrecond`, which picks
a formal `(x, τ)` via `elements` and builds `x == e` with `e` drawn at that
formal's *own* type `τ`. The equality node is `bool` whatever `τ` is, so every
formal becomes usable regardless of type. Re-measured: **~71%** of clauses now
mention a formal (26/80, 28/66, 36/65, 30/53 across depths 1/2/3/5, where the
denominators include the no-formals functions that have nothing to mention). The
weight-1 unbiased `.bool` branch is retained so plain boolean preconditions stay
reachable — which is also what keeps `genPreconditions_complete`'s hypothesis
sufficient.

Re-measured over 1500 programs: **184 carried a `funcDecl` precondition** (up from
0), and `checkPrecondPreconditionsStripped` passed on all of them. It is now wired
as `PropertyNames.procPrecondStripped`.

Proof-side consequences: `FuncHasType'` has no precondition field, so
`genFunction_sound` only needed extra destructuring binders. `genFunction_complete`
traded its `hPre : preconditions = []` hypothesis for the honest pair `hPreLen :
length ≤ 1` (the generator emits `Option.toList`, so ≥2 clauses are genuinely
unreachable) plus `hPreReach`, a reachability hypothesis on the formals context —
rather than silently weakening the theorem. A precondition mentioning an ambient
variable is out of reach *by design*: such a function violates
`FuncWF.precond_freevars` anyway.

`genPreconditions_complete` states reachability via the unbiased `.bool` branch
only — deliberately one-directional, since that is all `genFunction_complete` needs.
The proof splits on `inputs.toList ≠ []` (`dif_pos`/`dif_neg`) and, in the non-empty
case, selects the weight-1 thunk via `mem_support_frequency_iff`.

### Does a *full* completeness theorem hit undecidability?

No — and it is worth recording why, since the worry is natural. One might expect an
exact characterization to have to quantify over the "provable" or "valid"
preconditions, which would indeed be undecidable. It does not, for two reasons:

1. **A generator's support is a set of syntax trees, not of truths.** The theorem
   says which `LExpr'` *terms* the generator can emit. Emitting `1 == 0` is a fact
   about reachable syntax; whether `1 == 0` holds is never asked.
2. **`FuncWF.precond_freevars` is purely syntactic** (`Func.lean:120`):
   `getVarNames p.expr ⊆ f.inputs.map (getName ·.1)`. Well-formedness of a
   precondition constrains its *free variables*, not its meaning. Strata never
   requires a declared precondition to be satisfiable, let alone provable — that is
   the verifier's business, downstream, and PrecondElim discharges obligations by
   *emitting asserts* rather than by deciding them.

So the exact theorem is stateable and provable: `mem_support_genPrecondition_iff`
(`FunctionHasTypeAGen.lean`) is a genuine iff whose right-hand side is a finite
disjunction over the two `frequency` branches, each reduced to `genLExpr`
reachability. Axioms: `propext`, `Classical.choice`, `Quot.sound` — no `sorry`.

The residual question is whether *`genLExpr`* reachability is decidable, which is a
separate matter already settled by `genLExprBase_complete` (`HasTypeAGen.lean:1895`):
its hypotheses are `HasTypeA'`, `emptyNames`, `allVarsInCtx`, `AllTypesSimple`, and
`termDepth bctx e ≤ depth` — all syntactic and decidable, and its docstring claims
the depth bound is tight (`genLExprBase_termDepth_bound` gives the converse). The
generator is a finite branching structure over a bounded depth budget; there is no
semantic quantifier anywhere in the chain.

## Verdict set after this change

Thirteen proc/transform properties; **two expected failures**, both honest:

- `proc: FilterProcedures changed flag is faithful` — hardcoded `changed := true`.
- `proc: PrecondElim changed flag is faithful` — **new**, the `.funcDecl` bug above.

The other eleven pass, including the new `proc: PrecondElim asserts every partial
call` and `proc: PrecondElim strips all preconditions`. Note the new failure is *probabilistic*: it needs a generated `funcDecl`
whose body calls a partial function (~0.5% of programs), so it reliably fails at
1000 trials but a much shorter run could miss it. The hand-built `#guard` covers
it deterministically regardless.

## Key gotchas for the next agent

- **Do NOT import `Core.formatProgram` or `StmtHasTypeAGen.TestSupport`** in any
  file that also imports the transform passes / `TestScaffold` — the
  `List.Forall₂` clash (Strata + Batteries) breaks the environment and makes
  identifiers spuriously "unknown". Symptoms come and go erratically.
- **Stale `.olean`s** cause spurious "unknown constant" and noncomputable-cascade
  errors; `lake build <target>` before believing an error.
- The proc generator's `Gen.backtrack` can exhaust and `panic!` at large sizes; the
  8000-replica budget was tuned to avoid this through Plausible size 100, but a
  standalone probe should guard generation.
- Structural `Program` equality is cheap and available — reach for it before
  reaching for formatters.

## Related memory

- `project_proc_transform_tests` — the original proc/transform suite this extends.
  Its "PrecondElim is a NO-OP" claim is **outdated**.
- `project_procedure_gen` — the `genProcedure` generator itself.
