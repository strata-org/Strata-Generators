# Property-Based Testing Plan: `LiftInternalFuncDecls`

**Target:** CR-292807021 — "[Strata] feat(core): Add internal funcDecl lifting pass"
(`https://code.amazon.com/reviews/CR-292807021/revisions/6#/details`, author `lebjuney`, revision 6)

**Goal of this document:** give an implementing agent everything needed to write property-based
tests (Plausible) against the lifting pass, including what the pass actually does, which academic
specifications supply the oracles, the concrete property list, and generator requirements.

**Status of facts here:** the pass mechanics and the API references were read off CR revision 6 and
verified against the local tree at commit `7f94d01ff`. Where the CR introduces a symbol that does
not exist upstream yet, it is marked **(new in CR)**.

---

## 1. What the pass is

It is **lambda lifting**, not closure conversion. This matters for choosing oracles, so the
evidence is recorded here.

Lambda lifting, as implemented in `Strata/Transform/LiftInternalFuncDecls.lean` **(new in CR)**:

1. **Free variables become extra parameters.** `capturedVars` computes free variables of the
   `funcDecl`'s body/axioms/preconditions/measure minus the formals; `toFunction` prepends them as
   *leading* `inputs`, and type variables in their types are appended to `typeArgs`.
2. **The function is hoisted** to a closed top-level `Decl.func`, emitted immediately before its
   enclosing procedure. The `funcDecl` statement is removed from the body.
3. **Call sites pass the extra arguments explicitly** — `substOps` replaces `.op f` with
   `LExpr.mkApp () (.op () newName none) capturedArgs`.
4. **Johnsson's fixpoint** (Phase 2 of `hoistProcedure`):
   `extCaptured(f) = own(f) ∪ ⋃ { extCaptured(g) | g a sibling called by f }`, computed as a least
   fixpoint over the sibling call graph.

There is **no** closure datatype, no environment tuple, no `apply`/unpacking, and no change to how
function values are represented or typed. Function references stay direct `.op` applications.
Closure conversion would allocate a closure value pairing code with a captured environment and make
`f` a first-class value; none of that is present. `funcDecl` is not first-class in Strata, which is
exactly why the call-site rewrite can be purely local to the `.op` node.

### Terminology nit to fix in the CR

Three docstrings say "closure conversion" for what the code does, contradicting the file's own
(correct) section heading "How it works (lambda lifting with declaration-site value capture)":

- `rewritePureFunc` docstring: "Apply the closure-conversion substitutions"
- `LExprWF.lean` `substOps` docstring: "the closure-conversion use in `LiftInternalFuncDecls`"

Worth a review comment so nobody later reads this as introducing closures.

---

## 2. Snapshot variables — the one non-textbook part

A **snapshot var** is a fresh local the pass introduces to freeze a captured value at the point
where the `funcDecl` used to be. The term is the CR's own: `genLiftVar`'s docstring says "Generate a
fresh snapshot-variable identifier," and `LiftingFunc.captured` is documented as
`(originalVar, snapshotVar, type)` triples.

It is an ordinary procedure-local — just a `Statement.init` emitted in place of the deleted
`funcDecl`. It plays two roles at once: it becomes a leading *parameter* of the lifted function
(renamed from the captured variable inside the body), and it is the *argument* passed at every
rewritten call site.

### Why it exists

Textbook lambda lifting would add `c` as a parameter and pass `c` at each call site. That is correct
in a pure language with immutable bindings. Strata is imperative, and its evaluator gives `funcDecl`
**declaration-time** capture semantics: `Core.captureFreevars`
(`Strata/Languages/Core/StatementEval.lean`) substitutes the current values of the body's free
variables into the function when the `funcDecl` statement executes.

So the pass performs that capture *statically*. Passing `c` at the call site would be **wrong**
whenever `c` is reassigned between the `funcDecl` and the call.

**This is the single most important semantic fact for test design.** Both reference papers assume
immutable bindings, so their "insert extraneous parameter, pass it at the call site" formulation is
*not* what this pass does. Take the papers' *shape* of correctness, instantiate the evaluation
relation with Strata's evaluator, and make "reassignment between declaration and call" a
first-class generator feature rather than an accident.

---

## 3. Worked example (CR test example 4) — the transformation in full

This is the example to hold in mind; it is the one that distinguishes snapshot capture from
call-site capture.

### Before → after

```
procedure reassign(a : int)                     function $__liftfncl_addC_1
{                                                   ($__liftfncl_0 : int, x : int) : int {
  var c : int := 10;                              x + $__liftfncl_0
  function addC(x : int) : int { x + c }        }
  c := 999;                          ══>       procedure reassign (a : int)
  var r : int := addC(a);                       {
  assert r == a + 10;                             var c : int := 10;
};                                                var $__liftfncl_0 : int := c;
                                                  c := 999;
                                                  var r : int := $__liftfncl_addC_1($__liftfncl_0, a);
                                                  assert [assert_0]: r == a + 10;
                                                };
```

### The four simultaneous edits to `addC`

`addC` starts as a `PureFunc` with `inputs = [(x, int)]`, `output = int`,
`body = some (x + c)`. Its one free variable, `c`, drives everything.

**1. `capturedVars` finds `c`.** Free vars of the body are `x` and `c`; `x` is a formal, so it is
filtered out. `c`'s type is read off the `fvar` annotation left by type inference. Result:
`[(c, int)]`.

**2. A snapshot var is minted and left behind at the declaration site.** `genLiftVar` produces
`$__liftfncl_0`, and the `funcDecl` statement is *replaced in place* by
`var $__liftfncl_0 : int := c`. "In place" is the whole trick — it lands between `var c := 10` and
`c := 999`, so it captures `10`.

**3. Inside the body, `c` is renamed to the snapshot, which becomes a leading parameter.**

```
  body:      x + c            ──substFvars {c ↦ $__liftfncl_0}──>   x + $__liftfncl_0
  inputs:    [(x, int)]       ──extraInputs ++ inputs──────────>    [($__liftfncl_0, int), (x, int)]
  output:    int              (unchanged)
  name:      addC             ──genLiftFuncName──────────────>      $__liftfncl_addC_1
```

`rewritePureFunc` applies that rename to `body`, `axioms`, `preconditions`, **and** `measure` — all
four, even though only `body` is populated here. The result goes to `toFunction`, which prepends the
captured params, and is emitted as a top-level `Decl.func` placed just before `reassign`.

**4. The call site gains a leading argument.** A Core call `addC(a)` is a curried application of an
`.op`:

```
before:                              after substOps {addC ↦ ($__liftfncl_addC_1 $__liftfncl_0)}:

      app                                        app
     ╱   ╲                                      ╱   ╲
 op addC   fvar a                            app     fvar a
                                            ╱   ╲
                    op $__liftfncl_addC_1    fvar $__liftfncl_0
```

`substOps` only ever rewrites the `.op` **leaf** — it swaps `op addC` for
`op $__liftfncl_addC_1` already applied to `$__liftfncl_0`. Because application associates to the
left, wrapping that leaf *prepends* arguments to the spine, and the tree above is exactly `mkApp` of
`$__liftfncl_addC_1` to `[$__liftfncl_0, a]` (see `LExpr.mkApp`,
`Strata/DL/Lambda/LExpr.lean:535`). **This is why the captured parameters must lead:** trailing
parameters would require finding the outermost application node and appending, which is not a local
rewrite. The op's type annotation is dropped (`none`) so a subsequent type-check re-infers it at the
new arity.

Nothing else in the procedure is touched — `assert r == a + 10` mentions no lifted function.

### Why the assertion still holds

```
  var c : int := 10;                    c = 10
  var $__liftfncl_0 : int := c;         c = 10,  $__liftfncl_0 = 10   ← frozen, never reassigned
  c := 999;                             c = 999, $__liftfncl_0 = 10
  ...$__liftfncl_addC_1($__liftfncl_0, a)        passes 10  ⟹  r = a + 10  ✓
```

Textbook lambda lifting would read `999` and give `r = a + 999`, breaking the assertion.

One-line summary: `addC` is transformed by *turning its captured variable into a parameter*
(lambda lifting), but the argument it receives is *a copy taken at the declaration site*
(closure-capture timing).

---

## 4. Reference papers and exactly what each supplies

Both papers are relevant, in different ways. Both describe a pure call-by-name `letrec` language, so
§2's caveat applies throughout.

### Reading order: Levy–Reeves in full, Fischbach–Hannan as a targeted skim

The question "how do I property test lambda lifting" is a methodology question, not a
correctness-statement question, and on that axis the two are not close.

**Read Levy–Reeves properly, first.** Their §7 *is* this document's experiment, already run: generated
test suite, implementation checked against three independent decidable oracles. That is a harness
architecture to copy rather than derive. Their specs are decidable predicates, so they port to Lean
`Bool`s / `DecOpt` instances directly, whereas Fischbach–Hannan gives theorems about a relation and
leaves the decidability engineering to you. They are in Lean 4 already. And — decisively — one of
their three oracles *is* a translation of the Fischbach–Hannan specification, so reading Levy–Reeves
gets you Fischbach–Hannan's spec in the form actually needed. Their Def 4.6 is exactly what Phase 2
of `hoistProcedure` computes, making it the direct oracle for P8, the algorithmically interesting part
of the pass.

Priority sections: §4 (Def 4.6, §4.1, §4.5) for the oracle and the no-shadowing preprocessing, §7 for
the harness design, Thm 6.10 for minimality.

**Then skim Fischbach–Hannan for the three things Levy–Reeves does not cover** — an afternoon, not a
full pass:

- **Thm 4 + Cor. 1** — *bidirectional* operational correctness, including termination. This is P13,
  and it is the property that catches the dangerous direction (`run p` verifying where `p` does not).
  Levy–Reeves does not give this framing.
- **Fig. 3 side conditions** — `x ∈ dom(Γ)`, `y ∉ dom(Γ)`, `FV(τ) ⊆ dom(Γ)` → properties #6/#7.
  Short enough to lift off the figure without the surrounding development.
- **§2.2 pitfalls, pp. 513–515** — adversarial generator shapes, but see the scope limit below: most
  are out of scope for Strata. Read for the ones that transfer.

**Caveat limiting both.** Per §2, both assume immutable bindings, so neither describes snapshot
variables — the single most important semantic fact about this pass. Their "pass the captured variable
at the call site" formulation is *wrong* for Strata. So **P7** (snapshot definition dominates every
use) and **P16** (snapshot-vs-call-site differential) — the two properties §8 flags as riskiest — have
no oracle in either paper. Those come from instantiating the papers' *shape* of correctness with
Strata's evaluator and `Core.captureFreevars`.

### Fischbach & Hannan, "Specification and correctness of lambda lifting" (JFP 13(3), 2003)

Local copy: `~/Downloads/specification-and-correctness-of-lambda-lifting.pdf`

Supplies **correctness oracles**. Its value for PBT is that it specifies lifting as a *relation*
(Fig. 3, judgment `Γ ▷ e : τ ⇒ e'`), separating "is this a valid lifting" from "is this the lifting
my algorithm produced." That gives a checkable oracle rather than an expected-output string.

| Result | Content | Becomes property |
|---|---|---|
| Thm 1 (Type Completeness) | every typable source term relates to *some* target | #12 (pass is total on well-typed inputs modulo documented restrictions) |
| Thm 2 (Type Correctness) | `‖Γ‖ ▷ e' : ‖τ‖` — output well-typed at erasure of source type | #5 (arity/type shape) + re-typecheck in every test |
| Thm 4 + Cor. 1 (Operational Correctness) | **bidirectional**: `e ↪ v` iff `e' ↪ v'`; explicitly covers termination | #13 |
| §2.2 pitfalls, pp. 513–515 | catalogue of ways naive lifting breaks | adversarial generator shapes |
| Fig. 3 side conditions | `x ∈ dom(Γ)` on `(lift-app)`; `y ∉ dom(Γ)`, `FV(τ) ⊆ dom(Γ)` on `(abs)`/`(letrec)` | #6, #7 |

The bidirectionality of Thm 4 is the part people skip and the part that catches "lifting made the
program stop diverging."

**Scope limit:** all of their hard cases (pp. 513–515) arise from **functions used as first-class
values** — lifted parameter captured by a later `let x`, parameter escaping its scope,
in-scope-but-wrong-scope, and the case where lifting `f` forces a *vacuous* lifting from `g`. Strata's
`funcDecl` is not first-class, so the funarg-flavoured pitfalls are out of scope. The **scope
conditions transfer directly** and become properties #6/#7.

### Levy & Reeves, "Simple Lambda Lifting: Formalisation in Lean and a new efficient algorithm" (FormaliSE '26)

Local copy: `~/Downloads/Simple Lambda Lifting in Lean.pdf`

The closer match, for three reasons:

1. **They already did what we are proposing.** §7: *"We have tested our algorithm implementation on
   examples from the literature and on a large suite of generated test cases; we checked that the
   output of our implementation satisfies the Johnsson-style lifting specification, the translation
   of the Fischbach–Hannan specification, and the specification of complete lifting."* Three
   independent decidable oracles over generated programs — **this is the architecture to copy.**
2. **Their specs are decidable predicates, not just theorems.** Def 4.6 (Solution), Thm 6.10
   (Minimality), Fig. 2 (`SC`, complete lifting) are all directly encodable as Lean `Bool`s.
3. Their §4.1 unused-function example and footnote 3 critique of Danvy–Schultz name the exact bug
   classes a naive fixpoint hits. They are in Lean 4 already, which eases borrowing.

**Where Levy–Reeves lines up with the CR, precisely.** Their Def 4.6 says `EP[f]` is the least
mapping with:

- (1) `v` a referenced non-local of `f` ⟹ `v ∈ EP[f]`
- (2) `v ∈ EP[f]` ∧ `g` references `f` ∧ `g` is not the declaring function of `v` ⟹ `v ∈ EP[g]`
- (3) nothing else is in `EP`

Phase 2 of `hoistProcedure` computes exactly this, specialised to Strata's flat scope structure. A
`funcDecl` carries a `PureFunc` whose body is an expression, so **internal functions cannot nest**.
Two consequences before writing generators:

- All of a procedure's internal functions are siblings, and the declaring function of every captured
  variable is always the enclosing procedure, never a sibling. So **condition (2)'s "not the
  declaring function" guard can never fire** — there is no exclusion case to test.
- With no nesting, `freeVars` of the body coincides with their *referenced non-local*, so their §4.1
  subtlety (`x` non-local in `f` only via nested `g`, hence unneeded after block-floating) **cannot
  arise**. Their minimality theorem still bites in its transitive form — property #8.

---

## 5. Properties, in order of value-per-effort

### Tier 1 — structural postconditions (decidable, no oracle, cheap)

The CR already has these as `#guard`s on fixed examples in
`StrataTest/Transform/LiftInternalFuncDecls.lean` **(new in CR)**; promote them to `∀` over
generated programs. Reuse the CR's own helpers: `funcIsClosed`, `allFuncsClosed`,
`allBodiesNoFuncDecl`, `programTypechecks`, `runLiftAst`, `soleFunc`.

**P1. Closedness.** `allFuncsClosed (run p)` — every emitted `Decl.func` satisfies `funcIsClosed`.
This is the pass's entire stated purpose (it licenses deleting the `LFuncClosed` TODO in
`Strata/DL/Lambda/FactoryWF.lean`), so invest the most generator diversity here. The CR also proves
`funcIsClosed_toLFuncClosed`, so the boolean recovers the real `Lambda.LFuncClosed`.

**P2. No residual `funcDecl`.** `allBodiesNoFuncDecl (run p)`, using
`Imperative.Block.noFuncDecl` (`Strata/DL/Imperative/Stmt.lean:219`).

**P3. Idempotence.** `run (run p) ≡ run p` modulo the fresh-name counter. Follows from P2, so a
violation means the traversal misses a nesting position. Cheap; catches missed `Stmt` constructors
immediately.

**P4. Identity on trivial cases.** `p` has no `funcDecl` ⟹ `run p = p` syntactically. `p` with only
`.cfg` bodies ⟹ `run p = p`. Also `changed = true ↔ p` contained a `funcDecl`:
`liftInternalFuncDecls` infers `changed` from `decls.length != decls.length`, an indirect proxy
worth pinning down (a procedure whose only lifted function is emitted 1-for-1 still changes length,
but confirm the edge cases).

**P5. Arity/type shape.** For each lifted `f`: `inputs = extCap ++ original inputs` (captured params
**lead** — the whole local-rewrite argument depends on it, see §3 step 4), `output` unchanged,
`typeArgs ⊇` original. This is the constructive content of Fischbach–Hannan Thm 2 here.

### Tier 2 — scope conditions (where bugs are most likely)

**P6. Name hygiene / no capture.** Every generated `$__liftfncl…` name is distinct from every
identifier occurring anywhere in `p`; snapshot vars pairwise distinct; lifted function names
pairwise distinct. This is Fischbach–Hannan's `y ∉ dom(Γ)` and Levy–Reeves' no-shadowing
precondition (which they discharge by α-conversion or unique integer IDs, §4.5). Adversarial
generator: emit user identifiers that look like the prefix (`liftPrefix = "$__liftfncl"`).

**P7. Snapshot definition dominates every use.** For each lifted `f` with snapshot vars `s₁…sₖ`,
every rewritten call site of `f` must be dominated by the `var sᵢ := cᵢ` inits.

**Write this one first.** It is the imperative analogue of `(lift-app)`'s `x ∈ dom(Γ)`, and it is the
structural risk the design carries: the pass hoists the *function* to the top level while leaving the
*snapshots* at the original program point. CR example 6 (`funcInIfPgm`) declares `twice` inside a
then-branch; the snapshot inits stay in that branch. Failure modes to generate:

- a `funcDecl` declared in a branch, referenced after the `if`
- referenced in the sibling `else` branch
- a `funcDecl` inside a loop body, called on a later iteration before its init re-executes (stale or
  out-of-scope snapshot)

Check both scope validity and, via re-typecheck, that nothing dangles.

**P8. Minimality, and that the fixpoint is a fixpoint.** Three checks:

- `extMap` satisfies Levy–Reeves Def 4.6 conditions (1) and (2) — directly encodable.
- `extMap` is the *least* such (Thm 6.10): one more iteration of the propagation step changes
  nothing, and no `extCap` strictly contains the least fixpoint from an independent reference
  implementation. The loop bound `for _ in [0 : lfs.length]` is asserted in a comment to suffice;
  verify it with deep sibling chains and mutual recursion (their footnote 3 cycle case) rather than
  trusting the count.
- Corollary: no lifted function has a parameter unused in its body *and* not required by any sibling
  call it makes.

**P9. Captured-type coherence.** `capturedVars` resolves each captured variable's type by `head?` on
the annotations found — first-annotation-wins. Property: all annotations for a given captured name
within one `funcDecl` agree. If a generator can produce a body where the same `fvar` name carries
two different `LMonoTy` annotations (shadowing, or partial annotation after a rewrite), this silently
picks one. Related: it `throw`s when *no* annotation exists, so generators must produce
post-typecheck programs, and separately assert that a well-typed input never reaches that error path.

**P10. No free type variables.** Every lifted `Function` has all type variables occurring in its
`inputs`/`output` present in `typeArgs`. `extraTypeArgs` is computed per function from `extCap`;
inherited captures bring their own type vars, so mutual recursion across a polymorphic procedure's
type parameter (`procedure p<V>`) is the case to generate.

**P11. `substOps` bvar side condition.** Its docstring
(`Strata/DL/Lambda/LExprWF.lean`, **new in CR**) notes it does *not* lift de Bruijn indices under
binders, so it is sound only when replacements are bvar-free. Property: every replacement in
`opSubstList` is closed w.r.t. bvars — and generate `funcDecl` bodies with `abs`/`quant` wrapping the
sibling call so the substitution actually goes under a binder.

**P12. Rejection completeness.** `run` rejects exactly when (a) duplicate internal function names
within a procedure, or (b) a procedure mixes local `typeDecl` with `funcDecl` (uses
`Imperative.Stmt.localTypeDecls`, **new in CR**, `Strata/DL/Imperative/Stmt.lean:~228`). Property:
for well-typed `p`, `run p` errors ⟹ (a) ∨ (b), and conversely. This is Fischbach–Hannan Thm 1
adapted. High value because it converts open-ended "does it crash" into a biconditional, and it will
find *unintended* rejections.

### Tier 3 — semantic oracles

**P13. Operational correctness, both directions** (Fischbach–Hannan Thm 4 / Cor. 1). Under Strata's
evaluator, `p` and `run p` agree on final state / assertion outcomes, and one terminates iff the
other does. Get the bidirectionality — the dangerous failure is `run p` succeeding where `p` fails,
i.e. an unsound verifier. Note `Core.eval` (`Strata/Languages/Core/StatementEval.lean:744`) is a
*symbolic* simulator returning `List Env × Statistics`, and `evalAux` (line 727) is already
fuel-bounded by `Imperative.Block.sizeOf ss`; treat fuel exhaustion as a distinguished outcome that
must match on both sides.

**P14. Verification-outcome preservation.** The pass is registered via
`modelPreservingPipelinePhase` (`Strata/Languages/Core/PipelinePhase.lean:63`), which is a claim:
`p` verifies iff `run p` verifies. Stronger and more diagnostic: the multiset of proof obligations
is the same modulo renaming. The phase sits ahead of `callElim`/`termCheck`/`precondElim`
(`Strata/Languages/Core/Verifier.lean:1502`, **modified by CR**), so also test the composite — with
no `funcDecl` the pipeline output must be bit-identical; with `funcDecl` it must agree on outcome.

**P15. Metamorphic relations** — cheap, no evaluator, surprisingly effective:

- α-renaming commutes with lifting (up to the fresh-name counter).
- Adding an unrelated top-level decl, or permuting independent decls, commutes.
- Lifting a procedure in isolation yields the same functions as lifting it inside a larger program.
- **Differential against `FunctionInlining`**: `inline(p)` and `inline(run p)` should agree.
  `Strata/Transform/FunctionInlining.lean` already exists, so this is a free second implementation of
  "what the functions mean."

**P16. Snapshot-semantics differential.** Explicitly generate reassignment of a captured variable
between the `funcDecl` and each call, and compare against *call-site* lifting (the papers' version).
They must **disagree**, and the pass must match `captureFreevars`. A test that only ever passes is
not testing this; you want the shape where naive lambda lifting is observably wrong. CR example 4
(`reassignPgm`) is the hand-written seed for this.

---

## 6. Generator design

Most of the effort lives here.

`StrataTest/DL/Lambda/TestGen.lean` already has Plausible generators for well-typed `LExpr` via
`ArbitrarySizedSuchThat` (helper classes in `StrataTest/DL/Lambda/PlausibleHelpers.lean`,
including a `DecOpt` partial-decidability class and `checkerBacktrack`). The missing piece is a
`Statement` / `Procedure` / `Program` generator. Requirements, in priority order:

1. **Post-typecheck programs only.** `capturedVars` reads types off `fvar` annotations and errors
   without them. Generate → `Core.typeCheck` → lift, mirroring the CR's `liftOnly` helper.
2. **Capture through non-body fields.** `capturedVars` unions free variables from `body`, `axioms`,
   `preconditions`, **and** `measure`, and `rewritePureFunc` rewrites all four. A generator
   populating only `body` misses three of four — **the most likely coverage gap.**
3. **Sibling call graphs, including cycles.** Phase 2's fixpoint is the algorithmically interesting
   part. Chains longer than 2, mutual recursion (Levy–Reeves fn. 3 / the Danvy–Schultz SCC bug), and
   mixed cases (capturing sibling called by non-capturing sibling).
4. **Nesting positions.** `funcDecl` inside `block` / `ite` / `loop`, at varying depths, with calls
   placed in sibling and enclosing scopes. Drives P2 and P7.
5. **Polymorphism.** Captures of a procedure's type parameter `<V>` so `extraTypeArgs` is
   non-trivial, plus the inherited-capture case for P10.
6. **Unused internal functions** (Levy–Reeves §4.1). Not a soundness bug here given flat scoping, but
   it produces dead snapshot inits and dead top-level functions. If output size matters (their
   Thm 4.8 is an output-size result), make it a property.
7. **Adversarial names.** Identifiers colliding with `$__liftfncl`, shadowed locals, same name at
   different types.
8. **Both rejection triggers** (duplicate internal names; local `typeDecl` + `funcDecl`), so P12 has
   both polarities.

Two smaller things:

- Levy–Reeves convert identifiers to integer IDs in `0..|I|-1` as preprocessing (§4.5) partly to
  guarantee no shadowing. Worth borrowing as a generator invariant, with a separate
  shadowing-generator for the rejection path.
- **Invest in shrinking.** A 40-line procedure with six mutually recursive internal functions is
  unreadable as a counterexample, and the structural properties will hand you exactly that.

---

## 7. Existing infrastructure — verified pointers

| Path | Relevance |
|---|---|
| `Strata/Transform/LiftInternalFuncDecls.lean` | **(new in CR)** the pass, 356 lines |
| `StrataTest/Transform/LiftInternalFuncDecls.lean` | **(new in CR)** 824 lines of `#guard_msgs` examples + helper predicates to reuse |
| `StrataTest/DL/Lambda/TestGen.lean` | Plausible generators for well-typed `LExpr` |
| `StrataTest/DL/Lambda/PlausibleHelpers.lean` | `ArbitrarySizedSuchThat`, `DecOpt`, `checkerBacktrack` |
| `StrataTest/DL/Lambda/TestGenTests.lean` | examples of driving those generators |
| `Strata/DL/Imperative/Stmt.lean:207,219` | `Stmt.noFuncDecl` / `Block.noFuncDecl` |
| `Strata/DL/Imperative/Stmt.lean:~228` | `Stmt.localTypeDecls` / `Block.localTypeDecls` **(new in CR)** |
| `Strata/DL/Imperative/Stmt.lean:237–262` | `Stmt.mapExpr` / `Block.mapExpr` |
| `Strata/DL/Lambda/LExprWF.lean` | `substFvars`, and `substOps` **(new in CR)** |
| `Strata/DL/Lambda/LExpr.lean:535` | `LExpr.mkApp` — left-associating, hence leading params |
| `Strata/DL/Lambda/FactoryWF.lean` | `LFuncClosed`; CR rewrites its TODO comment |
| `Strata/Languages/Core/Statement.lean:552–558` | `Statement.mapExprs` / `Statements.mapExprs` |
| `Strata/Languages/Core/StatementEval.lean:727,744` | `evalAux` (fuel = `Block.sizeOf`), `eval` |
| `Strata/Languages/Core/StatementEval.lean` | `Core.captureFreevars` — the semantics being modelled |
| `Strata/Languages/Core/StatementSemantics.lean:173–182` | funcDecl free-var capture in the semantics |
| `Strata/Transform/CoreTransform.lean:390` | `Core.Transform.run` |
| `Strata/Languages/Core/PipelinePhase.lean:63` | `modelPreservingPipelinePhase` |
| `Strata/Languages/Core/Verifier.lean:1502` | where the phase is inserted **(modified by CR)** |
| `StrataTest/Languages/Core/Examples/SubstFvarsCaptureTests.lean` | existing capture-semantics tests |
| `Strata/Transform/FunctionInlining.lean` | differential oracle for P15 |

### Gotchas found while verifying

- **`Stmt.mapExpr` does not recurse into `funcDecl`.** `Strata/DL/Imperative/Stmt.lean:253` returns
  `.funcDecl decl md` unchanged. Phase 5's `Statements.mapExprs` call-site rewrite therefore only
  works because `collectLiftingFuncsFromBlock` has already stripped every `funcDecl`. Worth an
  explicit property: if a `funcDecl` ever survived stripping, its inner call sites would silently
  go un-rewritten. Test by asserting P2 *before* trusting any call-site property.
- `Command.mapExpr` (`Strata/Languages/Core/Statement.lean:540`) has a catch-all `| c => c`, so
  nondeterministic `init`/`set` and `havoc` carry no expressions to rewrite — fine, but do not assume
  every command was visited.
- `Core.eval` is a *symbolic* simulator returning `List Env`; `evalOne` errors with
  `"More than one result environment"` when the list is not a singleton. For P13, decide up front
  whether to compare `List Env` multisets or restrict generators to deterministic control flow.
- The CR's existing tests use `#guard_msgs` on exact formatted output. That is brittle under any
  change to name generation or parameter ordering. Fischbach–Hannan's specification is
  *non-deterministic* — one source term relates to many valid liftings — which is precisely why
  "output satisfies the spec" beats "output equals a golden string." A spec-satisfaction oracle in
  the Levy–Reeves style keeps the readable examples while making the generated suite robust.

---

## 8. Suggested build order

0. **Read Levy–Reeves §4 and §7** (see §4 above) before writing the harness — it fixes the
   spec-satisfaction architecture and hands you P8's oracle. Fischbach–Hannan Fig. 3 and Thm 4 can
   wait until steps 2 and 4 respectively.
1. **P1, P2, P3, P12** with a generator covering `funcDecl` nesting and sibling call graphs. Smallest
   thing that exercises the traversal and the fixpoint, needs no evaluator, and P12 will likely find
   unintended rejections on the first substantial run.
2. **P7** (scope domination) and **P8** (minimality-as-fixpoint) — the two places where the design
   carries real risk.
3. **P5, P6, P9, P10, P11** — cheap once the generator exists.
4. **P13, P14, P16** — evaluator-based, once the structural layer is trusted.
5. **P15** metamorphic relations — good ongoing regression value, low cost.

If time is short, P1 + P7 + P12 is the highest-value trio: purpose, riskiest structural invariant,
and totality.
