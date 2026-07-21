# Property-based testing for the CSE / PtrCache CR

Applying this repo's well-typed Strata Core generators to
[CR-289836082](https://code.amazon.com/reviews/CR-289836082) — *"[Strata] Rename
ANFEncoder to CommonSubexprElim, accelerate with a safe pointer-address hash
cache"*.

> **Status.** This doc lives on `main`; the implementation lives on branch
> **`cse-ptrcache-properties`** (not yet merged). The CR is reconstructed on
> `ngernest/Strata` branch `cse-ptrcache-cr` (full 15-file diff, base `984172d4`;
> builds clean). On the `cse-ptrcache-properties` branch, this repo's
> `lakefile.toml` targets that Strata branch (resolved commit `8a3b26083`) — on
> `main` the Strata dep is still pinned to `1d858fb03`, so the steps in §4 are
> what that branch applied. There, the rename (§4.2) is done and the black-box
> properties **P-CSE-1/2/3/6** are wired into both harnesses and **all pass** at
> 200 trials / size 60:
>
> | Property | Predicate | Result |
> |---|---|---|
> | P-CSE-2 idempotence (#5a) | `checkCseIdempotent` | PASS |
> | P-CSE-1 typing preservation (#5b) | `checkCsePreservesTyping` | PASS |
> | P-CSE-3 capture safety | `checkCseNoFreeBVarInInits` | PASS |
> | P-CSE-6 DAG-size output bound | `checkCseVarCountBounded` | PASS |
>
> P-CSE-4 (eval preservation) and P-CSE-5/7 (hash-quality independence, traversal
> linearity) remain future work — the latter two need the §5 seam. The sections
> below are the design rationale.

The CR rewrites the common-subexpression-elimination (CSE) pass so every
traversal is proportional to the number of *distinct DAG nodes* rather than the
expanded tree size, using the pointer-address cache of §5 of [*Sealing
Pointer-Based Optimizations Behind Pure Functions*](https://arxiv.org/abs/2003.01685)
(Selsam, Hudon, de Moura). This doc says **what to test and why**, in terms of
the machinery already in this repo, and lists the **`lakefile.toml` / import
changes** needed for the generators to build against the CR.

---

## 1. What is already proved — and therefore *not* worth testing

The value of PBT here depends entirely on knowing where the CR's own proofs
stop. The paper's correctness story is: *an accelerated implementation is
functionally indistinguishable from a pure reference implementation*, discharged
either by a dependent-type proof or not at all. In this CR:

| Machinery (`Strata/Util/PtrCache.lean`, `Strata/Transform/CommonSubexprElim.lean`) | Guaranteed by | Test adds? |
|---|---|---|
| `PtrCache` lookup/update, `withPtrEqResult`, `withPtrAddr`, `Squash` wrapper | `run'_output_eq : (m.run' c).output = f x` — any run from any cache returns `f x` on the nose, via the `Result.h` proof each entry carries | **No.** A proof beats any generator. |
| `hashExprCached` / all hashing paths (`hashM`, `withHash`, `RwState.hashM`) | `hashExprCached_eq : hashExprCached = hashExpr` | **No.** |
| `exprEq` via `withPtrEqDecEq` | sound by construction (§3.3) | **No.** |

So do **not** spend generator budget differential-testing the cache against a
naive hash map — `run'_output_eq` already says the cache is a transparent
optimization. Point PBT at the parts the CR does *not* prove.

## 2. What is NOT proved — the real PBT targets

The proofs cover the **cache**. Nothing covers the **CSE algorithm built on top
of it**. Three specific unsealed surfaces, in priority order.

### 2.1 Binder handling (capture safety) — highest value

`collectSubexprs` decides whether a subexpression is eligible for hoisting from a
`Bool` "bvar-free" flag. The `abs` case carries this comment verbatim in the CR:

```lean
| .abs _ _ _ body =>
    -- Report bvar-freeness (may spuriously return true because it doesn't
    -- compare de bruijn index with the depth) ...
    (!body.hasBVar, st)
```

If that flag is ever `true` for a subexpression that actually contains a variable
bound by an enclosing `abs`/`quant`, CSE would hoist that subterm into a `var`
declaration **outside its binder → variable capture → silent semantic change**,
violating the "model-preserving" claim. The `.quant` case *does* recurse
`collectSubexprs` into its body, so this path is live. The author flagged the
approximation themselves — which is exactly the claim PBT exists to falsify.

**Why this repo is the right place:** `genLExpr` generates `abs`/`quant` with de
Bruijn bound variables, and the statement/command generators nest them inside
real Core statements. We can produce binder-rich, *certified well-typed* inputs
that a hand-written test suite would never think to construct.

### 2.2 Collision behaviour of `collectSubexprHashes` / `removeSubsumed`

These are the only two hash-keyed spots left **without** a structural `exprEq`
fallback:

```lean
-- collectSubexprHashes: hash-only early return
if !top && acc.contains he then return acc
-- removeSubsumed: hash-only membership
exprs.filter (fun e => !subHashes.contains ((hashM e).run' memo))
```

(Contrast `recordDup`, `replaceSubexprs`, `tryReplace`, which *are* `exprEq`-
guarded within the bucket.) A `hashExpr` collision here can make `removeSubsumed`
keep a subsumed target or drop a maximal one. It does not break semantics — the
collision-safe `replaceExprs` still rewrites correctly — but it changes *which*
duplicates are extracted, and can affect fixpoint convergence. The invariant to
assert is: **correctness must be independent of hash quality.**

### 2.3 Fuel convergence and idempotence

The old code computed `fuel` as a provable bound (`|S(body)|`) with a written
termination argument. The CR replaces it with a magic constant and silently
returns the partially-processed body on exhaustion:

```lean
def fuel : Nat := 1024
...
| 0 => (body, startIdx)   -- give up, return partial result
```

Semantically safe (partial CSE is still correct), but the fixpoint might not
actually converge, which would break idempotence. Worth an explicit property.

---

## 3. The properties to add

All of these fit the existing pattern: a `Bool` `check*` predicate in
`StmtHasTypeAGen/TestSupport.lean`, a `prop_*` wrapper + `checkProperty` call in
`PlausibleTestMain.lean`, and a `StmtPropResult` tag for a Tyche panel. Property
numbers continue from the existing `#1…#9`.

### P-CSE-1 — Typing preservation (rename of existing #5b; **already wired**)

The existing `checkAnfPreservesTyping` *is* this property; after the rename it
tests CSE. Vacuous when the input is rejected, genuinely FAILS if CSE turns an
accepted statement list into a rejected one. Because a subterm hoisted out of its
binder becomes ill-scoped, **this is already a partial capture detector** (§2.1):
capture that produces an unbound/ill-typed reference shows up as a typing
regression here.

```lean
-- after the rename, this is exactly the existing predicate:
def checkCsePreservesTyping (ss : List Statement) : Bool :=
  !checkTypeChecks ss || checkTypeChecks (cseStmts ss)
```

### P-CSE-2 — Idempotence (rename of existing #5a; **already wired**)

`checkAnfIdempotent` → `checkCseIdempotent`: `cse (cse x) ≈ cse x` under
`stmtsEq`. Directly exercises §2.3: if the 1024-fuel fixpoint fails to converge,
a second pass keeps extracting and this fails.

### P-CSE-3 — No free bound variable in any extracted init (**new; strongest capture detector**)

The sharpest, cheapest oracle for §2.1 — no evaluator needed. CSE only ever
introduces `var $__cse.k := e` declarations; assert that **no such init `e`
contains a free `.bvar`**. A captured bound variable is a `.bvar` that escaped its
binder, so it appears as a free bvar in the hoisted init.

```lean
/-- Every `$__cse.*` init expression introduced by CSE is closed w.r.t. bound
    variables (no `.bvar` escaped its binder). A failure is a capture bug. -/
def checkCseNoFreeBVarInInits (ss : List Statement) : Bool :=
  let out := cseStmts ss
  -- collect the RHS of every `init` whose name starts with `cseVarPrefix`,
  -- then check `!e.hasBVar` on each. (hasBVar is already used by the pass.)
  (cseIntroducedInits out).all (fun e => !e.hasBVar)
```

`cseIntroducedInits` is a small total traversal collecting `Statement.init` RHSs
whose name has prefix `Core.CSE.cseVarPrefix` — mirrors the existing
`funcDeclShapes` traversal style in `TestSupport.lean`.

### P-CSE-4 — Semantic preservation under evaluation (**new; the "model-preserving" claim itself**)

The only property that catches a capture producing a *well-typed but
different-meaning* program, plus the SSA "structurally-equal ⇒ same value"
assumption the pass relies on. Model it on the existing
`prop_cmd_eval_run_agreement` (which already evaluates generated commands): for a
generated *closed, well-typed* statement list, evaluate before and after CSE and
assert equal observable results / final store.

> Note: the repo's eval oracle is currently expression- and command-level
> (`LExpr.eval`, `prop_cmd_eval_run_agreement`). A statement-list evaluator is
> needed to state this at full strength. If one is not readily reachable, a strong
> proxy is: for each generated *expression* `e`, compare `eval e` against `eval e'`
> where `e'` is `e` after `replaceExprs`/the expression-level CSE core — reusing
> the existing `TypedExpr`/`ClosedTypedExpr` generators and `eval` from
> `HasTypeAGen/TestSupport.lean`.

### P-CSE-5 — Correctness is independent of hash quality (**new; needs a CR seam — see §5**)

Targets §2.2. Run CSE with a deliberately weakened hash (e.g.
`fun e => LExpr.hashExpr e % 4`) and assert the result is *semantically* equal to
the strong-hash run (use the P-CSE-4 oracle, **not** structural `stmtsEq` — output
*shape* may legitimately differ under collisions; only meaning must be invariant).
A correct implementation treats hashing purely as a performance hint. **This
cannot be written from `strata-generators` today** because `hx` is a hardcoded
`private abbrev` inside `CommonSubexprElim.lean`; see §5 for the seam to request.

### P-CSE-6 — Output-size bound on the DAG measure (**new**; your reviewer's idea #1, corrected)

Your reviewer suggested "output doesn't grow more than it should." Pin the bound
to the **distinct-DAG-node** measure, *not* tree size — CSE *adds* `var` decls, so
a tree-size bound throws false failures. Compute the structural DAG size with a
memoized traversal (metadata-ignoring key, backed by `BEq` so it is robust to
hash collisions — do **not** count distinct `UInt64` hashes, which undercounts):

```lean
structure ExprKey where expr : Expression.Expr
instance : BEq ExprKey where beq a b := a.expr == b.expr        -- structural
instance : Hashable ExprKey where hash k := LExpr.hashExpr k.expr

/-- Number of distinct subterms up to structural equality (the DAG-node count). -/
partial def structuralDagSize (e : Expression.Expr) : Nat := (go e {}).size
where go (e) (seen : Std.HashSet ExprKey) : Std.HashSet ExprKey :=
  if seen.contains ⟨e⟩ then seen
  else /- insert ⟨e⟩, recurse into children -/ ...
```

Property: number of introduced `var` decls ≤ number of distinct duplicated
subexprs ≤ `structuralDagSize`. Plausible's shrinker then hands you the minimal
offending program if it ever fails — the "shrink to the smallest offending input"
outcome your reviewer wanted.

### P-CSE-7 — Traversal stays linear on shared input (**new**; reviewer's idea #2; needs the §5 seam)

The paper's Fig 3 warns of the trap: a cache scales linearly on maximally-shared
input but reverts to exponential on **structurally-equal-but-pointer-disjoint**
terms *unless* something re-shares them first. `stmtRunCSE` calls
`Lean.ShareCommon.shareCommon` up front precisely to defeat this. To test it,
count how often the underlying `LExpr.hashExpr` *actually runs* (= cache misses =
distinct physical nodes) and assert it stays `≈ structuralDagSize`, across the
paper's four input families:

1. maximally shared (post-`shareCommon`) — the win case
2. near-perfect sharing (shared base, distinct roots — Fig 2)
3. **pointer-disjoint but structurally equal (Fig 3)** — the documented cliff
4. no sharing

A tree-only generator only ever produces family 4 and never exercises the
memoization; family 3 is the one that proves `shareCommon` is doing its job.
Measuring misses requires wrapping `hx` (§5). Without the seam, only P-CSE-6
(output size, black-box) is testable from here.

### Generator angles

- **Binder-heavy mode** for P-CSE-3/4: bias `genLExpr` toward `abs`/`quant` with
  live de Bruijn indices. The generators already produce these; a size/weight
  knob to raise their frequency makes capture bugs far more likely to surface.
- **Sharing modes** for P-CSE-7: post-process a generated term to (2) share a
  common base, (3) duplicate a subterm into two pointer-disjoint copies, or run it
  through `shareCommon` (1). Family 4 is the raw generator output.

### Tyche panels

Each `check*` predicate drops straight into the existing `StmtPropResult`
machinery in `TycheMain.lean` — reuse `stmtListFeatures` and add a `tag`
(`"cse_no_free_bvar"`, `"cse_preserves_typing"`, …). For P-CSE-6/7 add ordinal
features `dag_size = structuralDagSize` and (with the seam) `hash_misses`, so the
scaling relationship is directly eyeballable as a scatter in Tyche.

---

## 4. `lakefile.toml` and import changes

### 4.1 Repoint the Strata dependency at a ref containing the CR

The generators currently depend on **`github.com/ngernest/Strata` @ `1d858fb03`**,
which does **not** contain `Strata/Transform/CommonSubexprElim.lean` or
`Strata/Util/PtrCache.lean` (the CR is on the internal `code.amazon.com` Strata).
Nothing in this repo can `import` the CR code until the Strata dependency points
at a commit that includes it. Steps:

1. Land the CR's commits onto a ref of the Strata your generators depend on —
   e.g. cherry-pick / merge them onto a branch of `ngernest/Strata` and push.
2. Bump the pin in `lakefile.toml`:

   ```toml
   [[require]]
   name = "Strata"
   git = "https://github.com/ngernest/Strata"
   rev = "<commit-with-CSE-and-PtrCache>"   # was "1d858fb03"
   ```

3. Re-resolve and rebuild:

   ```bash
   lake update Strata      # refresh the manifest to the new rev
   lake exe cache get      # Mathlib artifacts
   make build
   ```

**Toolchain:** both repos are `leanprover/lean4:v4.29.1` today. If the CR bumped
the Lean toolchain (its description mentions a `lake update`), copy the new
`lean-toolchain` from Strata into this repo — a mismatch fails the build before
any test runs.

**No new `[[lean_lib]]` entries are required** for the CR code: those entries
declare *this repo's own* modules. `CommonSubexprElim` and `PtrCache` are pulled
in transitively by `import`, once the dependency ref has them.

### 4.2 Update the transform wrapper for the rename (required or it won't compile)

`StrataGenerators/StmtHasTypeAGen/TestSupport.lean` imports the *old* module and
calls the *old* entry point. The CR renames both. Change:

```lean
-- line 8
-import Strata.Transform.ANFEncoder
+import Strata.Transform.CommonSubexprElim

-- lines 215-216
-def anfStmts (ss : List Statement) : List Statement :=
-  (Core.ANFEncoder.anfEncodeBody ss 0).fst
+def cseStmts (ss : List Statement) : List Statement :=
+  (Core.CSE.stmtRunCSE ss 0).fst
```

Rename table (from reading revision 6):

| Old | New |
|---|---|
| `Strata/Transform/ANFEncoder.lean` | `Strata/Transform/CommonSubexprElim.lean` |
| namespace `Core.ANFEncoder` | `Core.CSE` |
| `anfEncodeBody : Statements → Nat → Statements × Nat` | `stmtRunCSE : Statements → Nat → Statements × Nat` (same signature — drop-in) |
| `anfVarPrefix = "$__anf."` | `cseVarPrefix = "$__cse."` |
| `anfEncoderPipelinePhase` | `commonSubexprElimPhase` |
| *(new file)* | `Strata.Util.PtrCache` (namespace `Strata.PtrCache`) |

`stmtRunCSE` now runs `shareCommon` + the fixpoint internally, so `cseStmts`
stays a pure `List Statement → List Statement` wrapper — the existing
`checkAnfIdempotent` / `checkAnfPreservesTyping` predicates work unchanged after
renaming `anfStmts → cseStmts`.

Then rename the harness identifiers to match: `prop_stmt_anf_*` /
`checkAnf*` → `..._cse_*` / `checkCse*` in `PlausibleTestMain.lean` and the
`StmtPropResult` tags in `TycheMain.lean`.

### 4.3 (Optional) build `PtrCache` directly

Only needed if you want to unit/property-test `PtrCache` helpers directly — but
per §1 they are proved, so this is generally unnecessary. If desired, just add the
import where you need it; no lakefile change:

```lean
import Strata.Util.PtrCache   -- exposes Strata.PtrCache.{PtrCache, evalPtrCache, ...}
```

---

## 5. A testability ask for the CR (enables P-CSE-5 and P-CSE-7)

Two of the strongest properties — hash-quality independence (P-CSE-5) and
traversal linearity (P-CSE-7) — need to (a) substitute a weakened hash and
(b) count real `hx` invocations. Today `hx` is a hardcoded `private abbrev` and
the traversal functions are `private`, so **neither is reachable from
`strata-generators`**. Worth requesting on the CR, small and self-contained:

- Parameterize the pass over its hash function (`hx` as an argument, defaulting to
  `LExpr.hashExpr`), **or** expose a test-only entry point that accepts a hash.
  This unlocks the weakened-hash differential (P-CSE-5).
- Expose a miss counter (thread a `Nat` through the existing `StateM`, or a
  test-only variant), so P-CSE-7 can assert `misses ≈ structuralDagSize` and
  validate the CR's own `gen_5…gen_12` scaling table rather than relying on
  flaky wall-clock timing.

If exposing these is undesirable, the alternative is to put P-CSE-5/7 **in-tree**
in the Strata package's `StrataTest/`, where `private` definitions are reachable
via same-namespace / `import all`. Everything else (P-CSE-1…4, P-CSE-6) is
black-box and belongs here in `strata-generators`.

---

## 6. Summary — recommended order

1. **Rebuild path first** (§4.1–4.2): repoint Strata, rename `anfStmts → cseStmts`,
   confirm the suite still builds and the renamed #5a/#5b pass.
2. **P-CSE-3 (no free bvar in inits)** — cheapest, highest-signal capture
   detector; no evaluator needed.
3. **P-CSE-4 (semantic preservation)** — the actual "model-preserving" claim;
   reuse the command-eval oracle pattern.
4. **P-CSE-6 (DAG-size output bound)** — black-box, gives shrunk counterexamples.
5. **P-CSE-1/2 (typing preservation, idempotence)** — already wired; keep as
   regression guards.
6. **P-CSE-5/7** — after the CR adds the §5 seam (or as in-tree `StrataTest`
   properties): hash-quality independence and traversal linearity across the four
   sharing families.

The through-line: **the cache is proved (§1), the transformation is not (§2).**
Aim every property at an unproven line in the diff, and lean on this repo's
sound-and-complete generators to feed it certified well-typed — and, crucially,
binder-rich and share-rich — inputs.
