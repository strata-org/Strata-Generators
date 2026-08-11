# #64 + #52 part B — what was done

## Goal

1. **#64**: make monomorphic *and* polymorphic factory applications reachable in
   *every* subterm position — `ite` arms, `abs`/`quant` bodies, `app`
   function/argument — by folding the Indir/IndirPoly rules into
   `genLExprBase`'s own per-type `frequency` lists.
2. **#52 part B**: state completeness for the polymorphic case at *any* subterm
   position, rather than only at the root as `genLExpr_complete`'s
   `base conditions ∨ IsPolyApp` shape allowed.

Both delivered. The whole project builds; no new `sorry` and no new axiom.

## Generator restructuring (`HasTypeAGen/Core.lean`)

### The dependency cycle, and how it is broken

`genIndirPoly` (a) defaulted `genArg` to `genLExprBase … depth` and (b) fell back
to `genLExprBase … depth τ` when `findPolymorphicOps` was empty. Both made it
depend on `genLExprBase`, so it could not be called *from* `genLExprBase`.

Fix: a new **`genIndirPolyCore`** takes both the argument generator and the
fallback as explicit parameters and therefore mentions `genLExprBase` nowhere. It
sits *before* `genLExprBase`. `genIndir` already took `genArg`, so it just moved
earlier verbatim.

`genIndirPoly` survives as a thin wrapper *after* `genLExprBase` holding the old
defaults, so existing call sites and proofs keep their meaning:

```lean
genIndirPoly … depth τ maxNumArgs genArg
  = genIndirPolyCore … τ genArg (genLExprBase … depth τ) maxNumArgs
```

`genIndirPolyCore` needs no `depth`: it was only ever consumed by the default
`genArg` and the fallback, both now explicit.

### Signature change

`genLExprBase` gained `pctx : PolyOpCtx` after `octx` — the ~800-reference
mechanical change. `retryCont` was deliberately **not** moved (see Scope).

### The two new branches

Appended to each of the ten `n + 1` `frequency` lists, weight 4 each: a
monomorphic Indir branch and a polymorphic IndirPoly branch, both drawing
arguments from `genLExprBase … n` and both falling back to
`genLExprBase … n τ`.

Decisions worth recording:

- **Arguments come from the smaller index `n`.** That keeps `genLExprBase`
  structurally recursive — verified: `#print genLExprBase.eq_def` shows
  `Nat.brecOn`, not `WellFounded.fix`, and `rfl` still unfolds it per case. So it
  stays reducible and the ~150 `simp only [genLExprBase]` / `rw [genLExprBase]`
  proof sites survive.
- **Appending, not inserting.** `genLExprBase_complete`'s `frequency` witnesses
  are `.head`/`.tail` chains, so appending leaves every existing index valid.
  Only the ten `hw : 0 < List.sum …` obligations changed — which is why
  `genLExprBase_complete` needed *no* new cases at all, against the issue's
  estimate of it being the riskiest part.
- Depth-0 `oneOf` cases untouched: Indir at the floor would leave no budget for
  arguments.

## Proofs

New module **`HasTypeAGen/IndirSupport.lean`** (`sorry`-free) holds everything
shared. Its lemmas are parametric in `genArg`/`fallback`, taking the property they
need as a hypothesis rather than referring to `genLExprBase`, which is what lets
them sit *upstream* of both proof files — the same trick `Core.lean` uses for the
generators. Each `genLExprBase_*` proof then discharges those hypotheses with its
own recursive call at `n`.

| theorem | outcome |
|---|---|
| `genLExprBase_sound` | 20 new subgoals, all closed |
| `genLExprBase_fvars_subset` | 20 new subgoals, all closed |
| `genLExprBase_opsConsistentR` | 20 new subgoals, all closed; gained a `PolyOpsConsistentR` hypothesis |
| `genLExprBase_complete` | **no new cases** (only the `hw` sums) |
| `genLExprBase_termDepth_bound` | **statement had to change** — see below |

`HasTypeAGenOpsConsistent.lean` also needed a ~370-line block moved *above*
`genLExprBase_opsConsistentR`, since that theorem now consumes it.

### `genLExprBase_termDepth_bound`: the old statement is false, not just unproved

This is the one finding that goes beyond the issue's cost estimate. The issue says
this theorem "needs re-derivation". In fact its **conclusion becomes false**:

`termDepth` charges one level per `app` node, so a fully-applied operator of arity
`k` is a `k`-deep spine and costs `k`. At `depth = 1` the new Indir branch can emit
`Int.Add #1 #2` from two depth-0 leaves, whose `termDepth` is `2 > 1`. Verified by
evaluation before touching the proof.

So the bound was **restated**, not re-proved:

```
termDepth bctx e ≤ depthBudget K depth      -- K = max arity available per level
```

with `depthBudget K n = n * K`, written recursively to keep the proof's arithmetic
linear (`omega` handles `depthBudget K n` as an atom; `n * K` with variable `K` it
cannot). The arity ceilings are genuine theorems, not assumptions:
`findOpsInCtx_length_le` bounds the monomorphic rule by `opCtxArity octx`, and
`findPolymorphicOps_length_le` bounds the polymorphic one by `maxNumArgs`. For
`corePartialOps`/`corePolyOps`, `K = 3`.

Consequence for `genLExprBase_complete`: its `hdepth : termDepth bctx e ≤ depth`
precondition is unchanged and still sufficient, but the old *converse* reading —
that `hdepth` exactly characterizes reachability — no longer holds. The support is
now strictly larger than `{e | termDepth e ≤ depth}`.

It also gained a side condition, `IndirArgTysSimple`, asserting the argument types
the rules request are `SimpleType`. This is a genuine hypothesis, not a provable
fact: `findOpsInCtx` reads argument types off `octx`'s arrow types and
`findPolymorphicOps` substitutes *sampled* types into a scheme, so neither is
constrained to `SimpleType` by anything in the generator. It is cheap to discharge
for the real vocabularies.

## #52 part B

Three new `sorry`-free theorems:

- `genLExprBase_complete_polyApp` — a polymorphic factory application is in
  **`genLExprBase`'s** own support. This is the statement the two-disjunct
  `genLExpr_complete` could not make, and it is what makes the positional claim
  provable at all: since the structural rules recurse into `genLExprBase`, the
  polymorphic case composes into every position they generate.
- `genLExprBase_polyApp_under_ite` — the `ite`-arm instance.
- `genLExprBase_polyApp_under_quant` — the binder-body instance (both quantifier
  kinds), the case #64 calls out specifically.

Stated at the `bool` target, where the branch list is longest. Because the
IndirPoly entry is the *last* element of every per-type list, the other nine
`SimpleType` cases differ only in the `.tail` chain length.

`IsPolyApp`/`SchemeInstAt` and the three `…_specShaped` wrappers from #55 are
retained unchanged — they are still the spec-level route, and #55's ten
unification/freshening lemmas are consumed exactly as before.

## Existential-depth completeness corollaries

`genLExprBase_complete`/`genLExpr_complete` are depth-indexed, and their
`hdepth : termDepth bctx e ≤ depth` premise makes the caller compute the
generator's fuel accounting. Two corollaries quantify the depth existentially
instead:

- `genLExprBase_complete_exists`
- `genLExpr_complete_exists`

plus the lemma they need, `allTypesSimple_mono` / `allTypesSimple_mono_le`
(`AllTypesSimple`'s index is an upper bound, so it is monotone). The witness is
`max m (termDepth bctx e)`. These are strictly weaker than the depth-indexed
originals, so they are corollaries rather than new arguments.

Worth having *because of* the `termDepth_bound` change above: `hdepth` is still
sufficient for reachability but no longer characterizes it, so a statement that
never names a depth is insulated from the `K` constant, including from any future
change to it.

Two things deliberately not claimed:

- **`AllTypesSimple` is existentially quantified, not dropped.** It is not
  derivable from `HasTypeA'` — it additionally pins down bitvector widths, string
  alphabets, and the rational shapes the constant generators emit. Only the *index*
  becomes existential.
- **Only `genLExpr_complete`'s base disjunct is lifted.** `IsPolyApp`'s argument
  clause is stated against the depth-`match` generator, so raising `depth` changes
  *which generator the clause refers to* rather than relaxing a numeric bound;
  monotonicity would need its own support-monotonicity lemma for `genLExpr`. No
  claim is made either way.

### Why the dual direction gets no such treatment

Existentially quantifying `termDepth_bound`'s conclusion would give
`∃ d, termDepth bctx e ≤ d`, which is **vacuous**: it is
`⟨termDepth bctx e, Nat.le_refl _⟩` without inspecting the generator at all (Lean's
linter flags the support hypothesis as unused), and it holds for terms no depth can
produce. Completeness is the backward direction, so weakening its conclusion is
sound; `termDepth_bound` is the forward direction and is the theorem that pins the
generator down, so the quantitative fuel-to-output link has to stay depth-indexed.

## Measured reach (the actual payload)

Polymorphic factory application strictly under an `ite` arm / `abs` body /
`quant` body, 400 draws per cell, `corePartialOps` + `corePolyOps`, same
`retryGenArg 20` / `retryGen 500` the harness uses. Script:
`docs/measurements/issue-64-reach.lean`.

| target | depth | before (`main`) | after |
|---|---|---|---|
| `int` | 2 | 0/400 | 0/400 |
| `int` | 3 | 0/400 | **3/400** |
| `bool` | 2 | 0/400 | 0–1/400 |
| `bool` | 3 | 0/400 | **2–3/400** |
| `Sequence int` | 2 | 0/400 | 0/400 |
| `Sequence int` | 3 | 0/400 | **1–2/400** |

Zero in *every* configuration before; non-zero at depth 3 for every target after.
Depth 2 stays near zero, which is expected: a polymorphic spine plus its arguments
needs the budget. Success rate is unchanged at 400/400.

## Scope: deliberately not done

- **`retryCont` stays on `genLExpr`.** #59 argues that dissolving `genLExpr`
  forces `retryCont` onto `genLExprBase` so retries reach the new inner branches.
  That is a *cost* property, not a reach property, and it would double an
  already-~800-site signature change plus add a `retryCont = id` specialization to
  every proof. The measured success rate above (400/400) shows the current retry
  placement is not currently a bottleneck at these depths.
- **`genLExpr` is not dissolved.** It still applies the root-level 1:9
  base-vs-Indir weighting (versus roughly 8:8 inside the merged branch lists) and
  owns `retryCont`, so all `genLExpr_*` theorems and downstream callers are
  untouched.
- The `sorry` in `unifyTypes_matching_complete` (#55) is unchanged. All-positions
  removes the *positional* restriction on completeness; it does not reduce the
  unification obligation, exactly as #52's own comment predicted.
- Part B's three theorems are stated at the `bool` target rather than for all ten
  `SimpleType` cases (see above for why the others are mechanical).
