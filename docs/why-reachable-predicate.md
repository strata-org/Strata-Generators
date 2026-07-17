# Why the statement generator's completeness needs a `Reachable` predicate

**Scope.** This note explains why the completeness proof for the Strata Core
statement generator (`genStmt` / `genStmts` in `StrataGenerators/StmtHasTypeAGen.lean`)
is stated over a bespoke inductive relation `StmtReachable` / `StmtsReachable`,
rather than directly over the declarative typing relation `StmtHasTypeA`. The short
answer: **lexical scoping makes the typing judgment of every nesting constructor
`C Γ ⟶ C Γ`, which discards exactly the structural information a generator's
completeness theorem must pin down** — so a completeness statement phrased over
`StmtHasTypeA` would be *vacuous* for `block` / `ite` / `loop`.

---

## Background: what the relations mean

`StmtHasTypeA P C Γ L s C' Γ'` is a **6-place** relation. Read it as:

> under program `P`, starting in ambient context `C` (built-in/declared functions
> and known types), type-scope `Γ` (variable types), and enclosing-block label set
> `L`, statement `s` is well-typed and *produces output contexts* `C'` and `Γ'`.

The input contexts are `(C, Γ)`; the output contexts are `(C', Γ')`; `L` is the set
of labels of the lexically enclosing blocks (added post-#1392, so `exit` targets an
enclosing block and `block` cannot shadow one). When this note writes `C Γ ⟶ C Γ`, it
means the instance where the **output** equals the **input** — the statement leaves
the contexts unchanged. `L` never appears in an output position; it is a fixed index
across a statement list, extended only when descending into a `block` body.

"Completeness" of the generator should mean: *every statement we care about is
actually produced by the generator* — i.e. is in `genStmt`'s support (`SetGen.Set`
support = the set of values the generator can emit).

---

## The observation: nesting rules are `C Γ ⟶ C Γ`

Here is the `block` rule verbatim (from
`Strata/Languages/Core/StatementTypeSpec.lean`):

```lean
| block : ∀ C Γ C_body Γ_body L label body md,
    label ∉ L →
    StmtsHasType' τ P C Γ (label :: L) body C_body Γ_body →
    StmtHasType' τ P C Γ L (.block label body md) C Γ
--                     ^ input: C Γ                ^^^ output: C Γ  (identical)
```

Two things to notice:

1. The conclusion's **output** contexts (last two arguments) are literally the
   **input** `C Γ`. A block maps `C Γ ⟶ C Γ`.
2. The body's own output contexts `C_body` / `Γ_body` are bound by the `∀` and
   appear **only in the premise**, never in the conclusion.

(The label premises — `label ∉ L` and typing the body under `label :: L` — are new
in the post-#1392 spec. They constrain the *label*, not the contexts, so they don't
change the `C Γ ⟶ C Γ` observation below; they are why the reachability relation's
`block` constructor now draws `label` from `genFreshLabel L`, see the constructor
further down.)

Point (2) is the formal shadow of **lexical scoping**: anything the body declares
— a `funcDecl`/`typeDecl` extending `C`, an `init` extending `Γ` — is block-local
and is discarded when the block closes. So at the `(C, Γ)` level a block is
*context-neutral*. `ite` (both branches) and `loop` (body) route through the same
"discard the inner output" design and are likewise `C Γ ⟶ C Γ`:

```lean
| ite_det : ∀ C Γ C_t Γ_t C_e Γ_e L cond thenb elseb md,
    S.exprTyped C Γ cond (S.embed .bool) →
    StmtsHasType' τ P C Γ L thenb C_t Γ_t →
    StmtsHasType' τ P C Γ L elseb C_e Γ_e →
    StmtHasType' τ P C Γ L (.ite (.det cond) thenb elseb md) C Γ   -- output C Γ

| loop : ∀ C Γ C_body Γ_body L guard measure invariants body md,
    … → StmtsHasType' τ P C Γ L body C_body Γ_body →
    StmtHasType' τ P C Γ L (.loop guard measure invariants body md) C Γ  -- output C Γ
```

(`ite`/`loop` bodies inherit the enclosing `L` unchanged — only `block` introduces a
new label into scope.)

For contrast, the leaf declaration rules are **not** `C Γ ⟶ C Γ` — they genuinely
change the output context, so they *do* pin down content:

```lean
| funcDecl : … → StmtHasType' τ P C Γ L (.funcDecl decl md) (C.addFactoryFunction func) Γ
--                                       output C is EXTENDED ^^^^^^^^^^^^^^^^^^^^^^^^^^
| typeDecl : … C.addKnownTypeWithError … = .ok C' →
             StmtHasType' τ P C Γ L (.typeDecl tc md) C' Γ            -- output C' ≠ C
```

---

## Why this makes `StmtHasTypeA`-based completeness vacuous

Suppose we tried to state completeness directly over the typing relation, in the
natural "re-realization" style (produce *some* reachable statement realizing the
given judgment):

```
given  StmtHasTypeA P C Γ L (block label body md) C Γ
find   r ∈ support (genStmt …)  with  r realizing  StmtHasTypeA P C Γ L r.stmt C Γ
```

The judgment `StmtHasTypeA P C Γ L · C Γ` says **nothing about the body** — only
"input `C Γ`, output `C Γ`." And there is a *much simpler* statement with the
**identical** judgment whenever `L` is non-empty: `exit`.

```lean
| exit : ∀ C Γ L label md, label ∈ L → StmtHasType' τ P C Γ L (.exit label md) C Γ  -- also C Γ ⟶ C Γ
```

So (with any enclosing label in scope) the "completeness" obligation for a `block`
could be discharged by the generator producing an **`exit`**: the theorem would be
*satisfied without the generator ever producing a block*, let alone the intended
body. Technically true, completely useless — it never forces coverage of the nesting
constructors. The typing relation, by design, has thrown away exactly the structural
information (which body, which branches, which guard) that a *generator* completeness
theorem must nail down.

This is the vacuity, stated as a slogan:

> Over `StmtHasTypeA`, "complete for blocks" is provable by emitting an `exit`.
> Any theorem an `exit` can satisfy on behalf of every block is not saying what we
> mean by completeness.

---

## Why other shortcuts don't work either

- **Strengthen to exact recovery over `StmtHasTypeA`** ("produce `r` with
  `r.stmt = block label body md` and the right output contexts"). This is what we
  actually want — but you cannot *state* it as a hypothesis-free consequence of the
  typing derivation, because the derivation for a block does not mention how the
  body was built by the generator. You need a premise that says "the body is
  reachable," and expressing *that* premise for the nesting cases is exactly the
  inductive relation below (its body premise is "the body is reachable"). Trying to
  state it inline is circular: the hypothesis you need for a block is the conclusion
  you're proving, for its sub-terms.

- **Inline the support predicate** (drop the relation; state
  `⟨s, C', ctx'⟩ ∈ support (genStmt …)` with raw side-hypotheses). Same circularity:
  the side-hypothesis for the nesting cases is "the body/branches are in `genStmts`'s
  support," i.e. the very statement you are proving for sub-terms. Structural
  induction over an explicit relation is what breaks the circle.

- **Reuse some existing relation.** The only candidates at statement granularity are
  `StmtHasType'` (vacuous for nesting, as shown) and the generator's own `support`
  (circular). Nothing existing captures "in the generator's normal form with each
  component reachable."

---

## What we use instead: `StmtReachable` / `StmtsReachable`

We define a `size`-indexed, `VarCtx`-threaded mutual inductive that mirrors
`genStmt` / `genStmts` constructor-for-constructor, and **carries the discarded
structure explicitly in its premises**. The `block` constructor:

```lean
| block : ∀ labels C ctx size label body C_body Γ_body len,
    len ≤ size + 1 →
    label ∈ SetGen.support (genFreshLabel (G := SetGen.Set) labels) →
    StmtsReachable fctx octx tvars (label :: labels) C ctx size len body C_body Γ_body →
    StmtReachable  fctx octx tvars labels C ctx (size + 1)
      (Stmt.block label body default) C ctx
```

Contrast with the typing rule: here the premise
`StmtsReachable … body C_body Γ_body` mentions `body` and asserts *the body is
reachable*, so an inhabitant of `StmtReachable … (block label body …) …` genuinely
records "this is a **block** whose **body** is reachable" — not merely "some
statement mapping `C Γ ⟶ C Γ`." An `exit` inhabits a *different* constructor
(`StmtReachable.exit`) and can never masquerade as a block. The vacuity is gone.

The `label ∈ support (genFreshLabel labels)` premise mirrors the generator's fresh
label draw, and (via `genFreshLabel_not_mem`) discharges the spec's `label ∉ L`
premise when the reachable statement is shown well-typed.

Notes:

- The conclusion's output contexts are still `C ctx` for a block — the relation
  *agrees* with the spec that a block is context-neutral. The difference is entirely
  in the **premise**, which keeps the body alive.
- Threading a single `size` (rather than a separate nesting fuel) means the
  sequence `cons` case needs no fuel-monotonicity lemma: head and tail are at the
  same `size`.
- The relation is `VarCtx`-indexed (not `TContext`-indexed), so completeness can
  conclude the *exact* output scope `r.outCtx = ctx'` without a determinism lemma
  for `CmdHasTypeA` (whose output context is in fact **not** deterministic — the
  `init_nondet` rule leaves the stored monotype free up to `RigidAnnotCompat`).

---

## The two theorems, and why the relation is not vacuous *itself*

Completeness is then a one-line-per-constructor induction on the reachability
derivation:

```lean
theorem genStmt_complete  … (h : StmtReachable  … labels C ctx n s C' ctx') :
    (⟨s, C', ctx'⟩ : GenStmtResult) ∈ support (genStmt  … labels C ctx n)
theorem genStmts_complete … (h : StmtsReachable … labels C ctx size len ss C' ctx') :
    ((ss, C', ctx')) ∈ support (genStmts … labels C ctx size len)
```

A fair worry: have we just moved the problem — is `StmtReachable` itself a
meaningful specification, or could *it* be vacuous/wrong? Two facts pin it down from
both sides:

1. **`genStmt_complete` (above): reachable ⇒ in support.** The relation is not
   *stronger* than the generator — everything it deems reachable really is produced.
2. **`genStmt_sound`: in support ⇒ `StmtHasTypeA … labels …`.** Everything in the
   support is well-typed (at the same enclosing label set `labels` threaded by the
   reachability relation).

Composing them (`genStmt_complete_sound`) shows a reachable statement is
simultaneously in the generator's support **and** well-typed — so `StmtReachable`
characterizes exactly *the generator's well-typed support*, which is the honest
target. The relation earns its keep: it is the completeness specification that
`StmtHasTypeA` structurally cannot be.

---

## One-paragraph summary

`StmtHasTypeA` collapses `block` / `ite` / `loop` to the context-neutral judgment
`C Γ ⟶ C Γ`, deliberately forgetting their bodies (lexical scoping). A completeness
theorem stated over `StmtHasTypeA` is therefore vacuous for the nesting
constructors — an `exit` (in any non-empty label scope), which has the same
judgment, would satisfy it. We instead
prove completeness over `StmtReachable` / `StmtsReachable`, inductive relations that
mirror the generator and keep each sub-component's reachability in their premises;
`genStmt_complete` (reachable ⇒ in support) and `genStmt_sound` (support ⇒
well-typed) together confirm the relation captures exactly the generator's
well-typed support, non-vacuously.
