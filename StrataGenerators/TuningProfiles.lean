import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.ProcedureHasTypeAGen.Core

open Lambda RandomChoice Core Imperative
open StrataGenerators.Stmt

/-!
# Tuning profiles for the property families in this repo's test suite

`@[tunable]` turns a generator's `frequency` weights into a runtime value (see
`StrataGenerators.SetGen.Tuning`). This module says *which* weights to use: it names one
`Tuning` per job the test suite has to do, and provides the tuned entry points the suite (and
the `dist-report` executable) draw from.

Everything here is `Tuning` values and generator plumbing — no proofs, so it is Mathlib-free and
importable next to Strata's transform passes. The θ-invariance theorems for these generators
(*every* `θ` denotes the same `SetGen.Set`, so no profile can invalidate a soundness or
completeness result) live in `StrataGenerators.SetGen.TuningPrototypes`, one per generator.

## What a profile is for

The generators are proven sound *and* complete, so every sample is a well-typed program and every
well-typed program is reachable. Neither says anything about *how often* a shape appears, and the
properties in the suite are not equally sensitive to all shapes. A property whose interesting
precondition holds on 2% of samples spends 98% of its budget re-checking a trivial case, and one
whose precondition never holds passes vacuously — the failure mode PBT is worst at reporting. A
profile is the fix: it moves probability onto the shapes a given family of properties actually
discriminates on, and (because tuning is θ-invariant at `Set`) it cannot cost coverage — every
shape stays reachable, so a shape a profile makes rare is still eventually drawn.

Concretely, here is the measured baseline against what a profile buys — `lake exe dist-report 250`,
one row per shape the properties discriminate on. (These are one run's figures; nothing here is
seed-deterministic, and rates move a few points run to run — `exit` under `stmtKleeneBalanced` has
been measured anywhere from 13% to 19%. Re-run before reading a small difference as a change.)

| properties | interesting shape | default | tuned | profile |
| --- | --- | --- | --- | --- |
| `stmt: LoopElim …` (#3, #4) | ≥ 1 `loop` | 32% | **78%** | `stmtLoopHeavy` |
| ” | a loop inside a loop | 3% | **32%** | ” |
| ” | an invariant-bearing loop | 19% | **59%** | ” |
| `stmt: typechecker accepts …` | ≥ 1 `funcDecl` | 18% | **68%** | `stmtFuncDeclHeavy` |
| `stmt: DetToKleene …` | ≥ 1 `exit` | 4% | **17%** | `stmtKleeneBalanced` |
| `cmd: set …` (2) | mean `set`s per sample | 1.3 | **2.1** | `cmdSetHeavy` |
| `cmd: context growth …` | variables added by `init` (mean) | 0.9 | **2.1** | `cmdInitHeavy` |
| `cmd: symbolic/concrete eval …` | ≥ 1 `assert`/`assume`/`cover` | 91% | **99%** | `cmdCheckHeavy` |
| `expr: preservation`/`progress` | term is not already a value | 42% | **54%** | `exprEvalHeavy` |
| `expr: progress` | the failure the gap predicts | 22% | **38%** | `exprIndirHeavy` |
| `expr: eval preserves fvars` | term mentions a free variable | 28% | **41%** | `exprFVarHeavy` |
| `proc: PrecondElim …` (13) | the pass rewrites the program | 67% | **78%** | `procPrecondHeavy` |
| ” | ≥ 1 declared function | 40% | **81%** | ” |
| `proc: FilterProcedures …` (7) | ≥ 1 `call` | 57% | **82%** | `procCallHeavy` |

The `proc:` rows are the ones to read sceptically, and they are a good advertisement for measuring
rather than assuming: when these profiles were first written, calls appeared in 15% of generated
programs and PrecondElim fired on 26%. Both numbers are now 57% and 67% *without* any tuning, because
`genProcedure` and `genCallStmt` were improved in the meantime (every sibling is callable, and the
`call` weight is 3 rather than 1). What was a 4× gain is now a sharpener worth about 1.2–2×, and
`stmtLoopHeavy` raises `PrecondElim fires` (78%) just as much as `procPrecondHeavy` does. Keep the
`proc:` profiles for the declared-function rate, which is still 40% → 81%; do not expect them to
rescue a vacuous property, because that family is no longer vacuous.

Two rows are honestly *not* there: `stmt: ANF …` and `proc: ANFEncoder …` (ten properties) run as
identity checks — the encoder changed the program on 0–4% of samples under every profile. The reason
is not a weight that is set wrong but the shape the pass keys on; see the ANF note below the
procedure profiles.

## What the profiles do to the suite's own properties

Coverage of a *shape* is a proxy. `lake exe dist-report --props` measures the thing itself: it runs
every property in `Properties.stmtTransforms` / `Properties.procTransforms` under each profile and
reports how often each one fails. Over 300 samples per profile:

* **No profile introduces a new failure.** Every property that passes under the default weights
  passes under all of them — which is the outcome the θ-invariance theorems predict but do not
  imply (they say no shape becomes unreachable, not that no property breaks).
* **The known defects reproduce several times faster.** `stmt: typechecker accepts generated
  statements` (#1, the `funcDecl` spec/algorithm gap) fails on 5% of default samples and **23%**
  under `stmtFuncDeclHeavy`. `proc: PrecondElim factory strips declared functions` fails on 23% by
  default and **51%** under `procPrecondHeavy`. For a defect you are trying to *keep* pinned, that
  is the difference between a property that needs hundreds of trials to bite and one that bites on
  every run.
* **One known defect stays out of reach**: `proc: PrecondElim changed flag is faithful` fails on
  ~1% of samples under every profile, because it needs a declared function whose *body* calls a
  partial operator — an expression-level shape, and the composition gap below is exactly why no
  weight here reaches it.

## Desirable distributions, family by family

**Expressions** (`expr: …`, 5 properties over `genLExprBase`). Three different jobs pull in
different directions:

* *Generator soundness* (`expr: generated terms typecheck`) wants **breadth** — every rule of
  every type, since the property is only as strong as the set of shapes it visits. That is what
  the default near-uniform weighting already gives, and it is why `exprBreadth` is the defaults.
* *Evaluator properties* (`preservation`, `progress`, `eval preserves fvars`) want terms that
  actually **reduce**. A leaf — a constant, an `fvar`, an `op` — is already a value, so the
  property holds for a reason that has nothing to do with the evaluator. `exprEvalHeavy` raises
  `app`/`ite`/`eq` (the redex-forming rules) and drops the three leaf branches to 1.
* *Known gaps* want the opposite of avoidance. `expr: progress` fails on `∀`/`∃` (`LExpr.eval`
  has no rule for a quantifier, so `if (∀x. e) then …` is stuck) and `resolve after type erasure`
  fails on an erased quantifier whose body type is the bound variable. `exprQuantHeavy` makes a
  quantifier the modal `bool` shape, which turns those two properties from "fails on a small
  fraction of runs" into "fails on almost every run" — the difference between a flaky signal and
  a regression test for the characterization.

**Commands** (`cmd: …`, 6 properties). `cmd: set preserves variable` and `cmd: store type
preservation` only bite on a `set`; `cmd: context growth matches inits` only bites on an `init`.
Those pull apart, so there are two profiles (`cmdSetHeavy`, `cmdInitHeavy`) rather than one
compromise. `cmd: symbolic/concrete eval agreement` bites hardest on `assert`/`assume`/`cover`,
whose guard can be false at run time — `cmdCheckHeavy`.

**Functions** (`function: …`, 7 properties). The decisive shape here is *presence*, not choice of
rule: `function: typeCheck accepts generated functions` fails exactly on a function with a
`measure` and no `body`, and the other six properties are trivial or vacuous when the body is
absent. Body and measure presence are `optionGen` coins rather than `frequency` sites, so they
are **not tunable as written**; `SetGen.TuningPrototypes` shows the `weightedOptionGen` rework
that would make them so (`genPreconditionW`), applied to the precondition coin. What *is* tunable
is the precondition's shape (`genPrecondition`, tagged in `SetGen.TuningPrototypes`):
`precondInputHeavy` makes a `requires` clause mention a formal ~10 times out of 11, which is what
gives PrecondElim's stripping path something to strip.

**Statements** (`stmt: …`, 7 properties). This is the family the tuning machinery pays for
itself on:

* `LoopElim preserves typeability` / `eliminates all loops` are *entirely* vacuous on a
  loop-free program — the transform is the identity and the property degenerates to "the
  typechecker accepts what the generator produced", which property #1 already tests.
  `stmtLoopHeavy` makes the modal statement a loop, and (because tuning threads through the
  whole mutual recursion — see `genStmtChainT`) it also makes *nested* loops common, which is
  where a loop-elimination pass is most likely to be wrong.
* `DetToKleene defined iff supported` is a *biconditional*, so it needs both sides: programs
  with an `exit`/`funcDecl`/`typeDecl` (undefined) and without (defined), plus
  invariant-bearing loops for the documented caveat. A profile that maximises any one
  constructor makes one side of the iff vacuous, so `stmtKleeneBalanced` deliberately
  equalises the leaves instead of maximising them.
* `typechecker accepts generated statements` (#1) fails only on a `funcDecl` — the honest
  spec/algorithm gap — so `stmtFuncDeclHeavy` is the profile that turns it into a fast, reliable
  reproducer.
* `ANF is idempotent` / `ANF preserves typeability` need a **repeated** subexpression, which is a
  harder thing to ask a generator for than it sounds — the encoder is common-subexpression
  elimination, so it fires only when the *same* non-leaf, bvar-free expression occurs twice in one
  body. No weight makes two independently drawn subterms equal; see the ANF note below the procedure
  profiles for what does move the rate and by how little.

**Procedures** (`proc: …`, 28 properties over three transform passes). Everything the passes
need is in the procedure *bodies*, i.e. in the statement weights:

* FilterProcedures' five `FilterCorrect` fields and both call-graph fields need real call-graph
  edges, i.e. `call` statements: `procCallHeavy`.
* PrecondElim needs a partial-function call (measured at ~6% of programs by default) and, for
  the `changed`-flag defect, a *declared function whose body* calls one (~0.5%).
  `procPrecondHeavy` raises `call` and `funcDecl` together, since a `funcDecl` is what carries a
  declared function into the program.
* ANFEncoder needs a repeated subexpression in one procedure body, which no weight reliably buys —
  see the note below.

## Composition: what a knob reaches, and what it does not

`@[tunable]` threads `θ` through the tagged definition and its own recursion. It does **not**
thread it into a *different* definition the body calls by name. Two consequences, both measured:

* `genStmt` and `genStmtChain` are one mutual block, so tagging `genStmt` alone tunes only the
  outermost statement: with the loop weight at 40, top-level loops went 15% → 72% but
  loop-in-loop only 2% → 7.5%. Tagging the block's shared auxiliary `genStmt._mutual` — whose
  recursion is internal, so `θ` is threaded through all of it — gives 3.5% → 66% for
  loop-in-loop. That is what `genStmtT`/`genStmtChainT` below are built on, and why they are
  built on it.
* An **expression** weight set here does not reach the expressions inside generated statements:
  `genStmt` calls `genLExpr` by name, and `genLExpr`/`genIndirPoly` call `genLExprBase` by name.
  So `exprEvalHeavy` shapes the `expr:` family (which draws from `genLExprBase` directly) but
  not the expressions inside a `cmd` or a loop guard. Reaching those needs the sub-generator
  calls to take the tuning — tuning-passing style — which is a Basalt-level change, not a
  weighting. Until then the PrecondElim-partial-call rate is not tunable from here, and neither is
  the one expression-level lever that would move the ANF rate (see the ANF note above).
-/

namespace StrataGenerators.TuningProfiles

/-! Tag the mutual block's shared auxiliary, not `genStmt` itself: `genStmt._mutual` is where the
recursion is internal, so `θ` threads through *all* of it. Tagging `genStmt` (as its definition
site does) tunes only the outermost statement, because its recursion runs through the other member
of the block — see the "Composition" section above for the measured difference. -/
attribute [tunable] StrataGenerators.Stmt.genStmt._mutual

/-! Two more generators need no source change at all: their `frequency` lists are already literal,
so the attribute can be applied from here. `genLMonoTy` is the base-type-versus-compound-type split
that decides how often a generated type is an `arrow`/`Map`/`Sequence`; `genPrecondition` is the
`requires`-clause shape split (`SetGen.TuningPrototypes` explains that one at length).

`genGenerableTy`, `genAppArgTy` and `genLExpr` are tunable as written too — 9:1 context-derived
versus blind type draws, and 1:9 base-rules versus operator-application — but no profile here moves
them, so they are left untagged rather than tagged without evidence. -/
attribute [tunable] genLMonoTy genPrecondition

/-- Rewrite selected flat indices of a `Tuning` to constant weights. The base is always a
generator's own `.defaults`, so a profile is a diff against the shipping distribution and reads
as one. -/
def withWeights (base : Tuning) (edits : List (Nat × Nat)) : Tuning :=
  edits.foldl (fun θ (i, w) => { θ with schedules := θ.schedules.set! i (w, 0) }) base

/-- Set one weight at every index in `idxs` — the shape an expression profile wants, since a role
(`app`, `ite`, a leaf) recurs once per per-type site of `genLExprBase` and moving it at one site
only is diluted by the type distribution. -/
def withWeightsAt (base : Tuning) (idxs : List Nat) (w : Nat) : Tuning :=
  withWeights base (idxs.map (fun i => (i, w)))

-- ══════════════════════════════════════════════════════════════════════════
-- Flat indices
-- ══════════════════════════════════════════════════════════════════════════

/-! `Tuning.weight` addresses a branch by its flat index across all of a generator's sites, so
these are the names a profile is written in. Each block is pinned by an `example : … = rfl` in
this module, so a branch reordering in the generator breaks the build rather
than silently repointing a profile. -/

/-! Flat indices of `genStmt`'s two sites: the `size = 0` leaf list (0–4) and the `size + 1`
list (5–13). -/
namespace StmtIdx
def cmd0      : Nat := 0
def exit0     : Nat := 1
def funcDecl0 : Nat := 2
def typeDecl0 : Nat := 3
def call0     : Nat := 4
def cmd       : Nat := 5
def exit      : Nat := 6
def funcDecl  : Nat := 7
def typeDecl  : Nat := 8
def call      : Nat := 9
def block     : Nat := 10
def iteDet    : Nat := 11
def iteNondet : Nat := 12
def loop      : Nat := 13
end StmtIdx

/-! Flat indices of `genCmd`'s two sites: the writable-context list (0–6, which alone offers
`set`) and the no-writable-variable list (7–11). -/
namespace CmdIdx
def initDet    : Nat := 0
def initNondet : Nat := 1
def setDet     : Nat := 2
def setNondet  : Nat := 3
def assert     : Nat := 4
def assume     : Nat := 5
def cover      : Nat := 6
def initDet'    : Nat := 7
def initNondet' : Nat := 8
def assert'     : Nat := 9
def assume'     : Nat := 10
def cover'      : Nat := 11
end CmdIdx

/-! Flat indices of `genLExprBase`'s ten sites — one per generated type, all at `n + 1` (the
`n = 0` arms are uniform `oneOf`s, with no weights to tune). Every site offers the same *roles*, in
the same order, with three exceptions: `bool` also offers `eq`/`∀`/`∃`, the four sites whose type has
no literal (`ftvar`, `regex`, `Map`, `Sequence`) have no constant branch, and `arrow`'s first branch
is `abs` rather than a constant.

That regularity is what the role lists below capture. A weight is worth setting *per role across
every site*, not per site: a profile that raises `ite` only at `bool` is diluted by the type
distribution, since a base type is drawn uniformly and only one draw in six is `bool` — which is
exactly what the first `dist-report` run of `exprQuantHeavy` showed (a 10× weight moved the
quantifier rate from 3% to 13%, no further, because 5 draws in 6 never reach the `bool` site at the
root at all). -/
namespace ExprIdx

/-- Site offsets, in source order. -/
def arrowSite  : Nat := 0
def boolSite   : Nat := 8
def intSite    : Nat := 19
def ftvarSite  : Nat := 27
def stringSite : Nat := 34
def realSite   : Nat := 42
def bitvecSite : Nat := 50
def regexSite  : Nat := 58
def mapSite    : Nat := 65
def seqSite    : Nat := 72

/-- The `app` branch of every site. -/
def appAll : List Nat := [1, 9, 20, 27, 35, 43, 51, 58, 65, 72]
/-- The `ite` branch of every site. -/
def iteAll : List Nat := [2, 10, 21, 28, 36, 44, 52, 59, 66, 73]
/-- The bound-variable branch of every site (a `bvar` when one of the right type is in scope, and
otherwise the site's own fallback). -/
def bvarAll : List Nat := [3, 14, 22, 29, 37, 45, 53, 60, 67, 74]
/-- The free-variable branch of every site. -/
def fvarAll : List Nat := [4, 15, 23, 30, 38, 46, 54, 61, 68, 75]
/-- The bare-operator branch of every site — an operator whose *type is* the target type, hence a
leaf. Not to be confused with `indirAll`. -/
def opAll : List Nat := [5, 16, 24, 31, 39, 47, 55, 62, 69, 76]
/-- The **Indir** branch of every site: a fully-applied monomorphic operator returning the target
type, with its arguments drawn from this generator. This is where `Int.Add x 2` — and the partial
`Int.Safe*` builtins PrecondElim exists for — come from, so it is the operator knob that matters. -/
def indirAll : List Nat := [6, 17, 25, 32, 40, 48, 56, 63, 70, 77]
/-- The **IndirPoly** branch of every site: the same for a polymorphic library operator. -/
def indirPolyAll : List Nat := [7, 18, 26, 33, 41, 49, 57, 64, 71, 78]
/-- The literal-constant branch of the five sites that have one. -/
def constAll : List Nat := [8, 19, 34, 42, 50]
/-- `abs`, which only the `arrow` site offers. -/
def absArrow : Nat := 0

/-- `bool`-only rules. -/
def boolConst : Nat := 8
def boolApp   : Nat := 9
def boolIte   : Nat := 10
def boolEq    : Nat := 11
def boolAll   : Nat := 12
def boolExist : Nat := 13
/-- Both quantifiers. -/
def quantAll : List Nat := [12, 13]

end ExprIdx

-- ══════════════════════════════════════════════════════════════════════════
-- Profiles
-- ══════════════════════════════════════════════════════════════════════════

/-! ### Statements -/

/-- The shipping statement distribution: 4 : 1 : 1 : 1 : 1 leaves, 2 : 2 : 1 : 2 for
`block` : `ite` : `ite-nondet` : `loop`. -/
def stmtDefault : Tuning := genStmt._mutual.defaults

/-- **Loop-heavy** (`stmt: LoopElim …`, `#3`/`#4`). `loop` outweighs the summed rest, so a loop is
the modal statement at every nesting level and loop-in-loop programs — where a loop-elimination
pass is most likely to be wrong — are common rather than incidental. `cmd` keeps its default weight
so loop *bodies* still hold commands to eliminate around.

24 comes from a sweep (`dist-report`, 250 samples per point, max size 100), reading "has a loop" /
"has a loop inside a loop" / first-try success rate:

| loop weight | 2 (default) | 8 | 16 | 24 | 40 |
| --- | --- | --- | --- | --- | --- |
| ≥ 1 loop | 29% | 61% | 78% | 76% | 87% |
| nested loop | 2% | 10% | 20% | 26% | 28% |
| 1st-try | 67% | 65% | 63% | 60% | 58% |

Nesting is what the weight is really buying, and it saturates: past 24 another 16 points of weight
buy two points of nesting and cost two of generation cost. -/
def stmtLoopHeavy : Tuning :=
  withWeights stmtDefault [(StmtIdx.loop, 24)]

/-- **Loop-heavy but shallower.** As `stmtLoopHeavy`, but the leaf `cmd` branch is raised too, so
a loop body is more often a straight-line block than another loop. Use when the pass under test
is about a loop's *contents* rather than its nesting. -/
def stmtLoopWide : Tuning :=
  withWeights stmtDefault [(StmtIdx.loop, 16), (StmtIdx.cmd, 12), (StmtIdx.cmd0, 12)]

/-- **`funcDecl`-heavy** (`stmt: typechecker accepts generated statements`, `#1`). The honest
spec/algorithm gap is a `funcDecl` statement, so this makes the counterexample the common case.
Also the profile for PrecondElim's declared-function paths. -/
def stmtFuncDeclHeavy : Tuning :=
  withWeights stmtDefault [(StmtIdx.funcDecl, 12), (StmtIdx.funcDecl0, 12)]

/-- **Call-heavy** (`proc: FilterProcedures …`, and every call-graph field). A `call` needs a
callee, so this only bites when the generator is given a non-empty `ProcSigCtx` — which is
exactly the procedure-list harness. -/
def stmtCallHeavy : Tuning :=
  withWeights stmtDefault [(StmtIdx.call, 12), (StmtIdx.call0, 12)]

/-- **Kleene-balanced** (`stmt: DetToKleene defined iff supported`, `#6`). The property is a
biconditional between "the transform is defined" and "no `exit`/`funcDecl`/`typeDecl`, and no
invariant loop", so it needs samples on *both* sides; a profile that maximises any one constructor
makes one side vacuous. Raising the three unsupported leaves to `cmd`'s weight puts the undefined
side at about 60% of samples.

`block` is raised with them, and that is not cosmetic: `exit` needs an enclosing label, so at the
top level (`labels = []`) it is unreachable no matter what its weight is — a `block` is what creates
the scope an `exit` can target. Measured, raising `exit` alone left it at 3–4% of samples (the
default rate); raising `block` to 8 alongside it took it to 15%. -/
def stmtKleeneBalanced : Tuning :=
  withWeights stmtDefault
    [(StmtIdx.exit, 8), (StmtIdx.funcDecl, 4), (StmtIdx.typeDecl, 4), (StmtIdx.loop, 4),
     (StmtIdx.block, 8),
     (StmtIdx.exit0, 8), (StmtIdx.funcDecl0, 4), (StmtIdx.typeDecl0, 4)]

/-- **Everything-at-once** for the statement suite: loops common, and the three
`Kleene`-unsupported leaves and `call` all well represented. A single run then exercises #3/#4,
#6 and #1 together, at the cost of being optimal for none of them. -/
def stmtMixed : Tuning :=
  withWeights stmtDefault
    [(StmtIdx.loop, 8), (StmtIdx.funcDecl, 3), (StmtIdx.exit, 6), (StmtIdx.call, 3),
     (StmtIdx.block, 4),
     (StmtIdx.funcDecl0, 3), (StmtIdx.exit0, 6), (StmtIdx.call0, 3)]

/-! ### Procedures — the same statement knobs, aimed at the three transform passes -/

/-- **FilterProcedures**: call-graph edges are the whole point, so `call` dominates. -/
def procCallHeavy : Tuning := stmtCallHeavy

/-- **PrecondElim**: a declared function (`funcDecl`) is what carries preconditions into the
program, and a `call` is what makes a call site to assert at; both up. -/
def procPrecondHeavy : Tuning :=
  withWeights stmtDefault
    [(StmtIdx.funcDecl, 10), (StmtIdx.call, 6), (StmtIdx.funcDecl0, 10), (StmtIdx.call0, 6)]

/-! **There is deliberately no ANFEncoder profile**, and the reason is about the pass rather than
about the weights. `Core.ANFEncoder` is *common-subexpression elimination*, not expression
flattening: `findANFEncoderTargets` collects the subexpressions of a whole procedure body, keeps the
non-leaf bvar-free ones, and hoists only the **duplicates** (`findDuplicates`) into
`var $__anf.n := …`. So `proc: ANFEncoder …` (eight properties) and `stmt: ANF …` (two) need the same
expression to occur *twice in one body* — a nested expression on its own is not enough, and neither
is any number of distinct ones.

That is not a weight. Every subterm the generator draws is drawn independently, and no weighting of
independent choices makes two of them equal. Two things do move the rate, both weakly:

* **More expressions per body.** Collisions are roughly quadratic in the number of expressions a
  body holds, so the density lever helps a little — and the best one is `stmtLoopHeavy`, not
  anything `cmd`-shaped, because a `loop` carries a guard *and* a measure *and* an invariant list
  while a command carries one expression. Measured: `ANF≠id` 1% at the defaults, 3% under
  `stmtLoopHeavy`, and 0–1% under the `cmd`-heavy, `block`-heavy variant that this note replaces
  (which is why that variant is not a profile). The `cse:` witness in the front-end redesign — a
  body holding `str.le(P(G), P(G))` — is one of those 1%.
* **A degenerate expression distribution**, which would raise the collision probability directly.
  That is a `genLExprBase` knob, so `genStmt` reaches it by name and untunably (see "Composition") —
  and it would trade away exactly the breadth the `expr:` properties need.

The observed firings are collisions of small terms: e.g. `if false then 0 else -1` drawn into two
different loop invariants of one procedure, hoisted into a single `var`. Getting this family off the
floor wants a generator that *shares* subterms — draw a subexpression once and use it in two places —
which is a generator-structure change, and a well-motivated one given what the pass does. -/

/-! ### Commands -/

def cmdDefault : Tuning := genCmd.defaults

/-- **`set`-heavy** (`cmd: set preserves variable`, `cmd: store type preservation`). Both
properties are vacuous on anything but a `set`; the second site (no writable variable) has no
`set` branch to raise, so it is left alone. -/
def cmdSetHeavy : Tuning :=
  withWeights cmdDefault [(CmdIdx.setDet, 8), (CmdIdx.setNondet, 4)]

/-- **`init`-heavy** (`cmd: context growth matches inits`). Only an `init` grows the context, so
a sequence of mostly-`init` commands is what makes the growth equation non-trivial. -/
def cmdInitHeavy : Tuning :=
  withWeights cmdDefault
    [(CmdIdx.initDet, 8), (CmdIdx.initNondet, 4), (CmdIdx.initDet', 8), (CmdIdx.initNondet', 4)]

/-- **Check-heavy** (`cmd: symbolic/concrete eval agreement`). `assert`/`assume`/`cover` are the
commands whose concrete `run` can fail while symbolic `eval` succeeds, so they are where the
agreement property has content. -/
def cmdCheckHeavy : Tuning :=
  withWeights cmdDefault
    [(CmdIdx.assert, 6), (CmdIdx.assume, 6), (CmdIdx.cover, 6),
     (CmdIdx.assert', 6), (CmdIdx.assume', 6), (CmdIdx.cover', 6)]

/-! ### Expressions -/

/-- Breadth: the shipping weights. Every rule of every type stays common, which is what
`expr: generated terms typecheck` — a soundness property — wants. -/
def exprBreadth : Tuning := genLExprBase.defaults

/-- **Redex-heavy** (`expr: preservation`, `progress`, `eval preserves fvars`). The evaluator
properties are trivial on a term that is already a value, so the rules that build a redex — `app`
and `ite`, at *every* type — go up and the leaf rules (`bvar`/`fvar`/`op`) and literals go to the
floor. Quantifiers stay at 1: they are what makes `progress` fail, and this profile is for
exercising the evaluator, not for pinning that gap. -/
def exprEvalHeavy : Tuning :=
  let θ := withWeightsAt exprBreadth ExprIdx.appAll 6
  let θ := withWeightsAt θ ExprIdx.iteAll 8
  let θ := withWeightsAt θ ExprIdx.bvarAll 1
  let θ := withWeightsAt θ ExprIdx.fvarAll 1
  let θ := withWeightsAt θ ExprIdx.opAll 1
  withWeightsAt θ ExprIdx.constAll 1

/-- **Quantifier-heavy** (`expr: progress`, `expr: resolve after type erasure`). Both properties
fail on a quantifier — `LExpr.eval` has no rule for one, and `resolve` rejects an erased `∃x. x` —
and both failures are the documented gap rather than a soundness bug, so what a regression test
wants is for them to fail *reliably*.

Two measurements shaped this one:

* Raising `∀`/`∃` alone is not enough. They live only at the `bool` site, and a uniformly drawn base
  type is `bool` one time in six, so a 10× quantifier weight moved the rate from 3% to 13% and
  stopped. `ite` goes up at every site too — an `ite`'s guard is a `bool` subterm whatever the type
  of the `ite` — which is what carries the quantifier weight into terms of every type.
* Raising them *too* far is also not enough, and for a more interesting reason: a quantifier at the
  root is not stuck, because `LExpr.eval` leaves it alone and the property scores it as a value. It
  is a quantifier in an **eliminator** position — an `ite` guard, an `eq` operand — that gets stuck.
  So the eliminators outweigh the quantifiers here rather than the other way round.

What this profile therefore buys is quantifier *presence*, not `progress` failures: 8% → 27% over
the suite's whole size range, and 10% → 53% at max size 60 (where the depth budget is 3 — at depth
1 the sub-terms of an `ite` are drawn from the `n = 0` arms, which have no quantifier branch at
all, so the depth schedule, not the weight, is the binding constraint). For reproducing the
`progress` gap use `exprIndirHeavy` instead, and see its docstring for why. -/
def exprQuantHeavy : Tuning :=
  let θ := withWeightsAt exprBreadth ExprIdx.quantAll 8
  let θ := withWeightsAt θ ExprIdx.iteAll 14
  let θ := withWeights θ [(ExprIdx.boolEq, 8)]
  let θ := withWeightsAt θ ExprIdx.constAll 1
  let θ := withWeightsAt θ ExprIdx.bvarAll 1
  let θ := withWeightsAt θ ExprIdx.opAll 1
  withWeightsAt θ ExprIdx.fvarAll 1

/-- **fvar-heavy** (`expr: eval preserves fvars`). The property says evaluation introduces no *new*
free variable; on a closed term it holds for want of any free variable at all. Only useful with a
non-empty `fctx` — with `fctx = []` the branch falls back to the site's constant. Measured against
`defaultFCtx`, it takes the fraction of terms that mention a free variable from 31% to 48%. -/
def exprFVarHeavy : Tuning :=
  withWeightsAt exprBreadth ExprIdx.fvarAll 10

/-- **Indir-heavy** (`expr: progress`). This is the profile that reproduces the `progress`
counterexamples, and which knob does it changed when the expression generator did: `genLExprBase`
now offers the **Indir** and **IndirPoly** rules — a fully-applied operator whose result type is the
target — at every type, so an operator application is a branch here rather than something only the
`genLExpr` wrapper added at the root.

Measured (400 draws per row, `dist-report`'s expression sampler):

| | default | `op` leaf ×30 | Indir ×12 | Indir ×24 |
| --- | --- | --- | --- | --- |
| `progress` fails | 22% | 17% | 30% | **38%** |
| term contains an operator | 33% | 24% | 48% | **54%** |
| term is already a value | 64% | 81% | 52% | **47%** |
| 1st-try | 51% | 77% | 35% | **32%** |

Note the middle column, which is why this profile replaced an earlier `exprStuckOpHeavy` that raised
the bare-`op` *leaf* branch instead: raising a leaf **crowds out** Indir, so it lowered the failure
rate and the operator content it was supposed to raise. The `op` branch draws an operator whose
*type is* the target type — a leaf, not an application — and the two are easy to confuse.

The price is the highest in this module: first-try success 51% → 32%, so every sample costs about
1.6× as much to draw. An operator application needs a term per argument, and each is another chance
to fail. -/
def exprIndirHeavy : Tuning :=
  withWeightsAt (withWeightsAt exprBreadth ExprIdx.indirAll 24) ExprIdx.indirPolyAll 24

/-! There is deliberately no profile for the bare-`op` *leaf* branch. It draws an operator whose
*type is* the target type, so raising it makes terms more value-like and, worse, displaces the Indir
branches that carry real operator applications — see the table in `exprIndirHeavy`, whose middle
column is that measurement. -/

/-! ### Types

`genLMonoTy`'s two sites are the same 9:1 base-versus-compound split, once with type variables in
scope (indices 0–1) and once without (2–3). -/

def tyDefault : Tuning := genLMonoTy.defaults

/-- **Compound-type-heavy.** Raises `arrow`/`Map`/`Sequence` types from 1-in-10 to even money.
More compound types means more higher-order and collection-typed terms — and a much lower
first-try success rate, since `genLExprBase` can only inhabit a compound type when something in
the context already has it. The `dist-report` `1st-try` column is there to make that price
visible: this is the one profile in this module whose cost may outweigh what it buys. -/
def tyCompoundHeavy : Tuning := withWeights tyDefault [(1, 9), (3, 9)]

-- ══════════════════════════════════════════════════════════════════════════
-- Tuned entry points
-- ══════════════════════════════════════════════════════════════════════════

/-! Each of these is the shipping generator with `θ` threaded through it, and each is pinned to the
shipping generator at `θ = defaults` by an `example : … = … := rfl` below — so the plumbing cannot
drift away from what it claims to wrap. -/

/-- `genStmt` with every branch weight read from `θ`, threaded through the *whole* mutual recursion
(so the statements nested inside a `block`/`ite`/`loop` body are tuned too). -/
def genStmtT [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx := []) (size : Nat) :
    G GenStmtResult :=
  genStmt._mutual.tuned θ octx tvars immutableVars procs pctx (PSum.inl ⟨labels, C, ctx, size⟩)

/-- `genStmtChain` with every branch weight read from `θ`. -/
def genStmtChainT [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx := []) (size len : Nat) :
    G (List Statement × LContext CoreLParams × VarCtx) :=
  genStmt._mutual.tuned θ octx tvars immutableVars procs pctx
    (PSum.inr ⟨labels, C, ctx, size, len⟩)

/-- `genProgramStmts` with every branch weight read from `θ`: the entry point the statement family's
harness draws from. -/
def genProgramStmtsT [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (size len : Nat) (pctx : PolyOpCtx := []) :
    G (List Statement × LContext CoreLParams × VarCtx) :=
  genStmtChainT θ octx tvars [] [] [] (LContext.default) [] pctx size len

/-- `genCmds` with every branch weight read from `θ`. `genCmds` has no `frequency` site of its own —
it is a plain fold over `genCmd` — so the tuned chain is spelled out here rather than emitted by the
attribute. -/
def genCmdsT [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) :
    Nat → G (List (Cmd Expression) × VarCtx)
  | 0 => pure ([], ctx)
  | n + 1 => do
    let ⟨cmd, ctx'⟩ ← genCmd.tuned θ octx tvars immutableVars ctx depth []
    let (rest, ctx'') ← genCmdsT θ octx tvars immutableVars ctx' depth n
    pure (cmd :: rest, ctx'')

/-- `genProcedure` with the statement weights of its *body* read from `θ`. Identical to
`StrataGenerators.Procedure.genProcedure` except for the `genStmtChainT` call, which is what the
`rfl` pin below records. -/
def genProcedureT [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (_Γ : TContext Unit) (size len : Nat)
    (pctx : PolyOpCtx := []) : G Procedure := do
  let name ← genIdentName
  let typeArgs ← genTypeArgs size
  let inout ← genInputs typeArgs size
  let rawInputOnly ← genInputs typeArgs size
  let inputOnly := StrataGenerators.Procedure.disjointInputs rawInputOnly inout
  let rawOutputOnly ← genInputs typeArgs size
  let outputOnly :=
    StrataGenerators.Procedure.disjointInputs rawOutputOnly (inout ++ inputOnly)
  let inputs := inout ++ inputOnly
  let outputs := inout ++ outputOnly
  let preconditions ←
    StrataGenerators.Procedure.genChecks (StrataGenerators.Procedure.sigFctx inputs)
      octx typeArgs size pctx
  let postconditions ←
    StrataGenerators.Procedure.genChecks
      (StrataGenerators.Procedure.sigFctx
        (inputs ++ outputs ++ StrataGenerators.Procedure.oldVars inout))
      octx typeArgs size pctx
  let (body, _, _) ← genStmtChainT θ octx typeArgs
    (ListMap.keys inputs ++ ListMap.keys (StrataGenerators.Procedure.oldVars inout)) procs []
    ({ C with rigidTypeVars := typeArgs })
    (inputs ++ outputs ++ StrataGenerators.Procedure.oldVars inout) pctx size len
  pure {
    header := {
      name := ⟨name, ()⟩, typeArgs := typeArgs, inputs := inputs, outputs := outputs,
      noFilter := false
    },
    spec := { preconditions := preconditions, postconditions := postconditions },
    body := .structured body
  }

-- ══════════════════════════════════════════════════════════════════════════
-- The plumbing is the shipping generator
-- ══════════════════════════════════════════════════════════════════════════

/-! At `θ = defaults` each wrapper is the shipping generator *definitionally* — `Eq.refl`,
checked by the kernel. That is what keeps `genProcedureT` (the one wrapper that restates a
generator body rather than delegating to one) from drifting: any divergence, in any field, fails
these. `SetGen.TuningPrototypes` states them at `SetGen.Set` for every `θ` rather than just the
defaults. -/

/-! Well-founded recursion makes `genStmt` and `genStmtChain` irreducible, so the pins below need
them unsealed to see that each is a projection of the shared auxiliary the tuning is threaded
through. -/
unseal StrataGenerators.Stmt.genStmt StrataGenerators.Stmt.genStmtChain

@[simp] theorem genStmtT_defaults [_root_.Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size : Nat) :
    genStmtT (G := G) stmtDefault octx tvars immutableVars procs labels C ctx pctx size
      = genStmt octx tvars immutableVars procs labels C ctx pctx size := rfl

@[simp] theorem genStmtChainT_defaults [_root_.Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size len : Nat) :
    genStmtChainT (G := G) stmtDefault octx tvars immutableVars procs labels C ctx pctx size len
      = genStmtChain octx tvars immutableVars procs labels C ctx pctx size len := rfl

@[simp] theorem genProgramStmtsT_defaults [_root_.Gen G] (octx : OpCtx)
    (tvars : List TyIdentifier) (size len : Nat) (pctx : PolyOpCtx) :
    genProgramStmtsT (G := G) stmtDefault octx tvars size len pctx
      = genProgramStmts octx tvars size len pctx := rfl

@[simp] theorem genCmdsT_defaults [_root_.Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth n : Nat) :
    genCmdsT (G := G) cmdDefault octx tvars immutableVars ctx depth n
      = genCmds octx tvars immutableVars ctx depth n := by
  induction n generalizing ctx with
  | zero => rfl
  | succ n ih =>
    simp only [cmdDefault] at ih
    simp only [genCmdsT, genCmds, cmdDefault, genCmd.tuned_defaults, ih]

@[simp] theorem genProcedureT_defaults [_root_.Gen G] (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (size len : Nat) (pctx : PolyOpCtx) :
    genProcedureT (G := G) stmtDefault octx procs C Γ size len pctx
      = StrataGenerators.Procedure.genProcedure octx procs C Γ size len pctx := rfl

/-! The index tables above name the branch each profile means to move; these pin them. A branch
reordering in `genStmt`/`genCmd`/`genLExprBase` changes an arity or an offset and breaks one of
these, rather than silently repointing every profile at the wrong branch. -/

example : genStmt._mutual.sites.size = 2 := rfl
example : (genStmt._mutual.sites[0]!.offset, genStmt._mutual.sites[0]!.arity) = (0, 5) := rfl
example : (genStmt._mutual.sites[1]!.offset, genStmt._mutual.sites[1]!.arity) = (5, 9) := rfl
example : genStmt._mutual.defaults = genStmt.defaults := rfl
example : (genCmd.sites[0]!.offset, genCmd.sites[0]!.arity) = (0, 7) := rfl
example : (genCmd.sites[1]!.offset, genCmd.sites[1]!.arity) = (7, 5) := rfl
example : genLExprBase.sites.size = 10 := rfl
example : genLExprBase.defaults.schedules.size = 79 := rfl
example : (genLExprBase.sites[1]!.offset, genLExprBase.sites[1]!.arity) = (ExprIdx.boolSite, 11) :=
  rfl
example : genLExprBase.sites[9]!.offset = ExprIdx.seqSite := rfl
example : ExprIdx.appAll.length = 10 ∧ ExprIdx.iteAll.length = 10 := ⟨rfl, rfl⟩
example : ExprIdx.appAll.map (· + 1) = ExprIdx.iteAll := rfl
/-- Indir and IndirPoly are the last two branches of every site, so they sit one apart. -/
example : ExprIdx.indirAll.map (· + 1) = ExprIdx.indirPolyAll := rfl
/-- And they are the weight-4 branches the source gives them. -/
example : ExprIdx.indirAll.all (fun i => genLExprBase.defaults.schedules[i]! == (4, 0)) := by
  decide

/-! And that each profile moves the branch it names, leaving its neighbours alone. (The expression
profiles fold over 79 schedule entries, hence the raised recursion depth.) -/

set_option maxRecDepth 8000

example : stmtLoopHeavy.schedules[StmtIdx.loop]! = (24, 0) := rfl
example : stmtLoopHeavy.schedules[StmtIdx.block]! = (2, 0) := rfl
example : stmtCallHeavy.schedules[StmtIdx.call]! = (12, 0) := rfl
example : exprQuantHeavy.schedules[ExprIdx.boolAll]! = (8, 0) := rfl
example : exprQuantHeavy.schedules[ExprIdx.boolEq]! = (8, 0) := rfl
example : exprEvalHeavy.schedules[ExprIdx.absArrow]! = (4, 0) := rfl
example : cmdSetHeavy.schedules[CmdIdx.setDet]! = (8, 0) := rfl
example : genLMonoTy.sites.size = 2 := rfl
example : tyCompoundHeavy.schedules = #[(9, 0), (9, 0), (9, 0), (9, 0)] := rfl
example : tyDefault.schedules = #[(9, 0), (1, 0), (9, 0), (1, 0)] := rfl

end StrataGenerators.TuningProfiles
