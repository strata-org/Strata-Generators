# Statement generator vs. *Testing Noninterference, Quickly* (ICFP '13)

A comparison of Strata Core's well-typed statement generator (`genStmt`/`genStmts`)
with the random program generators of Hriţcu, Hughes, Pierce, Spector-Zabusky,
Vytiniotis, Azevedo de Amorim, Lampropoulos, *Testing Noninterference, Quickly*
(ICFP 2013), and the insights from that paper that transfer to our setting.

---

## Shared DNA

Both are **property-based random generators for a language with nontrivial
well-formedness constraints**, built from the same QuickCheck-style combinator
vocabulary. Their generators pick an instruction kind, then fill fields; ours uses
Basalt's `frequency` to pick a statement constructor, then fills it via
`genCmd`/`genLExpr`/`listOfMaxLength`/`choose`. Four specific techniques line up
almost one-to-one:

1. **Sequence generation.** Their "generate *sequences* of instructions that make
   sense together" (§4, the `[Push a, Store]` example) is exactly our `genStmts`
   threading `(C, ctx, labels)` through a list so each statement is well-formed in
   the state the previous ones produce.

2. **Weighted distributions.** Their headline early result — weighting
   `Push`/`Halt` up cut MTTF by orders of magnitude (Fig 5, NAIVE→WEIGHTED) — is
   why our `genStmt` uses `frequency` with hand-picked weights (4 for `cmd`, 1 each
   for the leaf decls, 2 for `block`/`ite_det`/`loop`) rather than uniform choice,
   and why `genCmd` up-weights `set` over `init` once the context is non-empty.

3. **"Smart integers" / sample-from-the-valid-pool.** Their smart-integer trick
   (bias raw integers toward in-range memory addresses, §4) is the same move as our
   variable references (`genSetDet` samples an index into `ctx`) and — now — our
   exit labels (`genExitStmt` samples from the enclosing `labels`). This is the
   insight we already adopted.

4. **Valid-by-construction control-flow targets.** Their "generation by execution"
   makes jump targets valid because the machine is *run* during generation; our
   lexical scoping makes exit targets valid because the enclosing labels are
   *statically known*. Same guarantee, cheaper mechanism.

---

## The fundamental difference in goal

Here's what's easy to gloss over: **they test a property and measure MTTF; we
prove the generator correct.** Their generator is a *bug-finding instrument* for
the machine — its quality is judged empirically (discard rate, mean-time-to-failure,
Fig 5–10). Ours is a *verified artifact* — its quality is
`genStmt_sound`/`genStmt_complete`.

This flips several of their concerns:

- They generate crashing/ill-typed programs and either **discard** (their
  preconditions, 59–79% discard rates) or avoid them via execution. We generate
  **only** well-typed statements by construction, with **zero discards** — the
  enviable end state they worked hard to approximate.

- There's a lovely meta-parallel on completeness. When they introduce
  smart/variational generation they explicitly worry "have we compromised
  completeness?" and can only argue *informally* "no — by generating a random
  machine and randomly varying it is possible to generate all pairs." Our
  `genStmt_complete` / `genStmts_complete` **discharge that exact worry by proof**:
  every well-formed (normal-form) statement is in the generator's support. We
  turned their informal side-note into a theorem.

---

## Insights we could still adopt, ranked by relevance

### 1. Measure the distribution — the zero-discard trap

Their single strongest empirical lesson is that naive generation is *nearly
useless* despite being "correct": avg 0.47 execution steps, 74% immediate stack
underflow (Fig 6). Because we generate by construction with no discards, we've lost
their built-in feedback signal (discard rate) that reveals a degenerate
distribution. We could be emitting mostly `exit` statements, empty blocks, and
depth-0 programs and never know.

**Concrete adoption:** collect the analog of their Fig 6–10 statistics over
`genStmt` output — constructor frequencies, average nesting depth, average
block/branch length, fraction of `exit`s that hit a live label, fraction of `set`
vs `init`. Then tune the `frequency` weights against those, treating them as the
measured knob the paper shows they are (rather than the guesses they currently are).

### 2. Generation-by-execution as the blueprint for the out-of-scope `.call` generator

We deliberately skipped procedure calls (no generator; the `cmd` case only wraps
`CmdExt.cmd`). The paper's `Call` handling is exactly the recipe: don't sample a
call and hope it type-checks — **sample a procedure from the program `P`, then
generate arguments matching its signature** (`getInputExprs` typed at
`subst[σ] inputs`, LHS vars from `ctx`). That's "sample from the valid pool"
applied to the whole call node, and it makes the `CmdExtHasType'.call` premises
satisfiable by construction — the same reason our label change works.

### 3. Type-preserving shrinking, with our reachability relation as the invariant

They invest heavily in shrinking (§3, §7) because raw counterexamples are huge. We
have no shrinker — but if this generator is ever pointed at the Strata typechecker
(differential testing spec vs. implementation) or the evaluator, type-preserving
shrinking is the need, and it's the genuinely hard part (their follow-up work and
the later "generating well-typed terms" line). Our `StmtReachable`/`StmtsReachable`
relation is a ready-made **shrinking invariant**: a shrinker may only move between
related statements, and `genStmt_complete` guarantees the shrunk term is still
reachable. That's a cleaner starting point than they had.

### 4. Variational generation for *relational* properties — and we're unusually well-positioned

Their deepest trick is generating one machine and *varying* it to get an
indistinguishable pair satisfying the relational (noninterference) precondition.
Our `StmtHasType'` is parameterized over `ExprTypingSpec` — instantiated to **both**
polymorphic `HasType` and annotated `HasTypeA`. So a natural relational property is
"`genStmt` output is simultaneously well-typed under both instantiations," or "the
annotated and inference typecheckers agree on generated statements." Variational
generation is the technique, and the parameterization hands us the two related
worlds for free.

### 5. Property strengthening, *if* we ever test rather than prove

Their §6 (make intermediate low states observable; quasi-initial states) is a
property-side lesson with no analog while we're proving. But the moment the
generator feeds a *test* of the operational semantics ("well-typed statements never
get stuck"), the same lesson bites: observe intermediate `Config`s, not just the
final one, or most counterexamples become invisible.

---

## Where Strata is genuinely easier

Two of their hardest problems don't exist for us, worth stating so we don't
over-import machinery:

- **No "landing in the middle of code" problem.** Their §5 backward-jump subtlety
  — a jump can land in already-generated instructions, forcing them to re-execute
  rather than regenerate — is a flat-instruction-stream pathology. Strata Core has
  **structured** control flow (tree of blocks), so exits only ever leave enclosing
  blocks; there's no arbitrary landing site.

- **Static, compositional validity.** They must *run* the machine to know what's
  valid because validity is dynamic. Our validity is typing — static and
  compositional — so we thread contexts and *prove* preservation instead of
  executing. That's precisely why we could adopt their valid-by-construction *idea*
  for labels without adopting their execution *mechanism*.

---

## Further influences from the *Haskell source* (beyond the paper)

Reading the actual QuickCheck implementation at `~/Documents/TestingNoninterference`
(both the `stack/` and `register/` machines) surfaces several concrete techniques
that the paper only gestures at. Ranked by fit to our setting:

### 6. Invariant-preserving ("variation") shrinking — our reachability relation is exactly the invariant

`register/Shrinking.hs` is the most directly instructive file. Their ordinary
`shrink` (the `Arbitrary Instr`/`Value`/`Atom` instances) is unremarkable, but
`class ShrinkV` — *shrink a `Variation` and return `Variation`s* — is the real
idea: every shrink step maps a **related pair** of states to a smaller **still-related**
pair (`shrinkV :: Variation a -> [Variation a]`). The `ShrinkV (Frame Atom)`,
`ShrinkV Stack`, and `removeRegisters` cases all carefully preserve the
low-indistinguishability invariant while removing content (delete a register from
*both* machines and renumber all references via `decrRegInstr`; drop synchronized
low stack frames together).

Transfer: if we ever build a shrinker (needed the moment `genStmt` feeds a *test*
of the typechecker or evaluator), the analogue of `ShrinkV`'s invariant is our
`StmtReachable`/`StmtsReachable` relation. A `shrinkStmt` should only produce
statements that remain reachable (and hence, by `genStmt_complete_sound`, remain
well-typed) — e.g. drop a statement from a block body, shrink a `block`/`ite`/`loop`
to one of its sub-blocks, replace a `cmd` by a smaller reachable `cmd`. Their
`decrRegInstr` renumbering has a direct analogue too: dropping a variable from `ctx`
means renaming/removing its `set`/`init` references so the result still threads.
We're better positioned than they were — they had to *hand-maintain* the
indistinguishability invariant with `error` guards for violations, whereas ours is
a Lean inductive we can *prove* the shrinker preserves.

### 7. `SmartGen` with a threaded `Info` record — generalize our `labels` threading

`register/Generation.hs` threads a single `Info = { flags, codeLen, dataLen, noRegs }`
record through *every* generator via a `class SmartGen a where smartGen :: Info -> Gen a`.
`Info` is precisely "the ambient facts needed to generate something valid here":
`codeLen` bounds jump targets, `dataLen` bounds pointer offsets, `noRegs` bounds
register indices. Their `SmartGen Pointer` "will always produce a valid pointer"
because it picks a block from `dataLen` and an offset within that block's length.

Transfer: we just added `labels` as one such ambient fact. The lesson is to
recognize `labels` as the *first member of an `Info`-like bundle* rather than a
one-off. Natural future members: a list of in-scope loop/block labels (done), the
set of declared type names (for `typeDecl`/type-constructor generation), the
procedure table (for the eventual `.call` generator — issue #2 above), the ambient
`C`/`ctx` (already threaded). Bundling them into one `GenStmtInfo` structure —
mirroring `Info` — would keep the generator signature stable as we add
context-sensitivity, instead of growing the positional argument list each time
(we already felt this pain threading `labels` through ~30 lemma signatures).

### 8. `smartInt`: bias operands toward the *valid sub-domain*, with a fallback

`register/Generation.hs`'s `SmartGen Int`/`Value` and the stack machine's
`smartIntWeighted` don't sample raw integers — they `frequency`-mix "a valid code
address (`choose (0,cl-1)`)", "a valid data pointer", and a small residue of
arbitrary values. The residue matters: it keeps the generator *complete* (any value
is still reachable) while making the *common* case valid.

Transfer: this is exactly the shape of our new `genExitStmt` (`elements labels`
mixed with `String.arbitrary`). The same pattern applies wherever we sample a
"reference": e.g. when a future `set`/expression generator picks a variable, prefer
an in-`ctx` variable of the *right type* but keep a low-weight arbitrary branch so
completeness survives. The general rule the source encodes: **bias toward the valid
sub-domain with `frequency`, never restrict to it** — restriction breaks
completeness, biasing doesn't.

### 9. `Reachability.hs` / `generateStamps`: a *repair* pass that post-processes a generated state into a well-formed one

Their `generateStamps` (`register/Reachability.hs`) doesn't generate well-formed
memory directly; it generates freely and then **deterministically repairs** the
result — computing, for each memory block, the meet of all labels that can reach it
and stamping accordingly, so the "no low pointer into a high frame" invariant holds
by construction *after the fact*. `wellFormed`/`reachable` are the checkable
predicate the repair establishes.

Transfer: this "generate-then-canonicalize" split is an alternative to our
"correct-by-construction threading" for any invariant that's painful to maintain
inline. We don't need it now (typing is compositional, so threading works), but if
a future constraint is genuinely global — e.g. "no two `typeDecl`s in the whole
statement tree clash", which currently we sidestep via the `.error` fallback in
`genTypeDeclStmt` — a post-hoc rename/repair pass over the generated tree may be
cleaner than threading a global name set. The proof obligation would then be
"repair produces a reachable statement", a single lemma rather than pervasive
threading.

### 10. The profiling harness (`profileTests`) — make insight #1 concrete

`stack/DriverUtils.hs`'s `profileTests` is the exact instrument behind the paper's
Fig 6–10: it runs 30000 generations, `collect`s the well-formedness verdict of the
final state, and `Average.record`s the execution-step count, then emits a LaTeX
table of the distribution. This is the concrete form of our "insight #1: measure
the distribution". Our analogue needs no execution — a pure fold over `genStmt`
samples recording a constructor histogram, nesting depth, body lengths, and
live-vs-fallback exit-label ratio — but the *shape* (sample a fixed large N,
tabulate, compare against tuned weights) is worth copying directly.

### 11. Mutation testing of the *spec* (`register/Mutate.hs`) — orthogonal but worth noting

`Mutate.hs` systematically weakens the IFC rule table (`mutateRule` drops
conjuncts from side-conditions and label expressions) to produce *buggy* variants,
then measures how fast each generator catches each mutant — this is how the paper
quantifies generator strength. For us this is an evaluation methodology, not a
generator technique: once we have any executable Strata Core property (typechecker
vs. spec, or preservation), we could mutation-test *our* generator by injecting
bugs into a copy of the typing rules and measuring detection — a principled
alternative to eyeballing coverage.

---

## Highest-leverage next steps

- **Insight #1 / #10** (measure the distribution) is still the highest-leverage,
  lowest-risk item: a statistics-collecting harness over `genStmt` (constructor
  histogram, nesting depth, live-label hit rate) so the `frequency` weights become
  measured rather than guessed. `profileTests` is the template.
- **Insight #7** (bundle ambient facts into a `GenStmtInfo`) is the
  lowest-risk *structural* improvement, and pays off immediately given how many
  lemma signatures `labels` touched.
- **Insight #6** (reachability-preserving shrinking) is the highest-value item the
  day this generator drives a real test, and our proven `StmtReachable` relation
  gives us a head start the original authors didn't have.
