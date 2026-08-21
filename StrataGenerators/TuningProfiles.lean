import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.ProcedureHasTypeAGen.Core

open Lambda RandomChoice Core Imperative
open StrataGenerators.Stmt

/-!
# Tuning profiles for the property families in this repo's test suite

`@[tunable]` turns a generator's `frequency` weights into a runtime value. This module says *which*
weights to use. It names one `Tuning` per job the test suite has to do, and it holds the tuned entry
points that the suite and the `dist-report` executable draw from.

This module holds `Tuning` values and generator plumbing, and no proofs. It is therefore Mathlib-free,
and a Strata transform pass can import it. `StrataGenerators.SetGen.TuningPrototypes` holds the
θ-invariance theorems, one per generator. Each says that every `θ` denotes the same `SetGen.Set`, so
no profile can invalidate a soundness or a completeness result.

## What a profile is for

The generators are sound *and* complete, so every sample is a well-typed program, and every
well-typed program is reachable. Neither law says how *often* a shape appears, and the properties in
the suite are not equally sensitive to all shapes. A property whose interesting precondition holds on
2% of samples spends 98% of its budget on a trivial case. A property whose precondition never holds
passes vacuously, and that is the failure a property-based test reports worst.

A profile fixes this. It moves probability onto the shapes that one family of properties
discriminates on. It cannot cost coverage, because tuning is θ-invariant at `Set`: every shape stays
reachable, so a shape that a profile makes rare is still drawn eventually.

The table below gives the measured baseline against what a profile buys. It comes from two runs of
`lake exe dist-report 250 100`, and each cell is the range across the two runs. Nothing here is
seed-deterministic, so re-run the report before you read a small difference as a change. If the range
of a row already spans the gap between the two columns, the profile does nothing.

| properties | interesting shape | default | tuned | profile |
| --- | --- | --- | --- | --- |
| `stmt: LoopElim …` (#3, #4) | ≥ 1 `loop` | 23–26% | **80–82%** | `stmtLoopHeavy` |
| ” | a loop inside a loop | 0–2% | **27–28%** | ” |
| ” | an invariant-bearing loop | 16% | **56–58%** | ” |
| `stmt: typechecker accepts …` | ≥ 1 `funcDecl` | 17–19% | **64–65%** | `stmtFuncDeclHeavy` |
| `stmt: DetToKleene …` | ≥ 1 `exit` | 2% | **13–14%** | `stmtKleeneBalanced` |
| `cmd: set …` (2) | mean `set`s per sample | 0.7 | **1.0–1.2** | `cmdSetHeavy` |
| `cmd: context growth …` | variables added by `init` (mean) | 1.3 | **2.3** | `cmdInitHeavy` |
| `cmd: symbolic and concrete eval …` | ≥ 1 `assert`, `assume` or `cover` | 91–95% | **99%** | `cmdCheckHeavy` |
| `expr: preservation` and `progress` | term is not already a value | 92–93% | 96% | `exprEvalHeavy` |
| `expr: progress` | the failure the gap predicts | 40–45% | 45–49% | `exprIndirHeavy` |
| `expr: eval preserves fvars` | term mentions a free variable | 52–55% | 53–57% | `exprFVarHeavy` |
| `proc: PrecondElim …` (13) | the pass rewrites the program | 60–65% | **75–77%** | `procPrecondHeavy` |
| ” | ≥ 1 declared function | 32–34% | **81–82%** | ” |
| `proc: FilterProcedures …` (7) | ≥ 1 `call` | 58% | **79–81%** | `procCallHeavy` |

**The three `expr:` rows are not bold, and that is the honest result.** Each range covers the gap
between the two columns. Through the generator those properties draw from, these profiles do almost
nothing.

One weight explains it, and `θ` does not reach that weight. `genLExpr` has its own root `frequency`,
a 1 to 9 split in favour of a fully-applied operator. So about 90% of terms are an operator
application at the root, before any of `genLExprBase`'s 79 weights applies. The base rules are
reached only in argument position, and a 24-fold weight on a base-rule branch then moves the
top-level shape by a few points. The *default* distribution is already redex-heavy: 92% of terms are
not a value. An earlier measurement of the bare `genLExprBase` reported 42%, which is why
`exprEvalHeavy` looked like it had more to buy.

The missing knob is that root split. It needs a wider index space than `genLExprBase.defaults`, 81
weights rather than 79, so it changes the arity that every expression profile is checked against. It
is a change to the index space and not a new profile. Until somebody makes it, read the `expr:`
profiles as a statement of intent. They apply, they cannot cost coverage, and they are measurably
weak.

Read the `proc:` rows with the same care, because they show why measurement beats assumption. When
these profiles were first written, a call appeared in 15% of generated programs and PrecondElim fired
on 26%. Those numbers are now 58% and 60–65% *without* any tuning, because `genProcedure` and
`genCallStmt` improved in the meantime. Every sibling is now callable, and the `call` weight is 3
rather than 1. A four-fold gain is now a sharpener worth about 1.2 to 1.4 times, and `stmtLoopHeavy`
raises the PrecondElim rate to 67–69%, about as far as `procPrecondHeavy` does. Keep the `proc:`
profiles for the declared-function rate, which still goes from 32–34% to 81–82%. Do not expect them
to rescue a vacuous property, because that family is no longer vacuous.

Two rows are honestly *absent*. The ten `stmt: ANF …` and `proc: ANFEncoder …` properties run as
identity checks, because the encoder changed the program on 0–2% of samples under every profile. No
weight is set wrong. The cause is the shape the pass keys on, and the ANF note below the procedure
profiles explains it.

## What the profiles do to the suite's own properties

Coverage of a *shape* is a proxy. Measuring the thing itself means running the suite's own
properties under each profile. A registration attribute already does that: tag the statement and
procedure families with `@[strata_properties (tuning := θ)]`, one profile at a time, and read the
per-property verdicts out of `lake test`. `StrataGenerators.DistReport` has no property-outcome table,
and says there why that comparison belongs in the suite. Over 300 trials per profile:

* **No profile introduces a new failure.** Every property that passes under the default weights
  passes under all of them. The θ-invariance theorems predict this outcome but do not imply it: they
  say that no shape becomes unreachable, not that no property breaks.
* **The known defects reproduce several times faster.** `stmt: typechecker accepts generated
  statements` is the `funcDecl` gap between the spec and the algorithm. It fails on 5% of default
  samples and on **23%** under `stmtFuncDeclHeavy`. `proc: PrecondElim factory strips declared
  functions` fails on 23% by default and on **51%** under `procPrecondHeavy`. For a defect you want
  to *keep* pinned, that is the difference between a property that needs hundreds of trials and one
  that bites on every run.
* **One known defect stays out of reach.** `proc: PrecondElim changed flag is faithful` fails on
  about 1% of samples under every profile. It needs a declared function whose *body* calls a partial
  operator, which is an expression-level shape. The composition section below says why no weight
  here reaches one.

## Desirable distributions, family by family

**Expressions**: five properties, drawn through `genLExprT`. Three jobs pull in different
directions. All three currently pull against a root split that they cannot move, so what follows is
the intent of each profile rather than a measured gain.

* *Generator soundness*, `expr: generated terms typecheck`, wants **breadth**: every rule of every
  type, because the property is only as strong as the set of shapes it visits. The default
  near-uniform weighting already gives that, which is why `exprBreadth` is the defaults.
* The *evaluator properties* want terms that **reduce**. A leaf is already a value, so the property
  then holds for a reason that has nothing to do with the evaluator. A constant, an `fvar` and an
  `op` are the leaves. `exprEvalHeavy` raises the redex-forming rules `app`, `ite` and `eq`, and
  drops the three leaf branches to 1. Measured, the *default* distribution already does this job:
  only 7–8% of draws are a value.
* The *known gaps* want the opposite of avoidance. `expr: progress` fails on `∀` and `∃`, because
  `LExpr.eval` has no rule for a quantifier and `if (∀x. e) then …` is therefore stuck.
  `expr: resolve after type erasure` fails on an erased quantifier whose body type is the bound
  variable. `exprQuantHeavy` aims to make a quantifier the modal `bool` shape. It measures 2% of
  terms with a quantifier, against 0% at the defaults. The quantifier branch exists only at the
  `bool` site, and the root is an operator application nine times in ten. So the profile does not make
  either gap a reliable reproducer.

**Commands**: six properties. `cmd: set preserves variable` and `cmd: store type preservation` bite
only on a `set`. `cmd: context growth matches inits` bites only on an `init`. Those pull apart, so
there are two profiles, `cmdSetHeavy` and `cmdInitHeavy`, rather than one compromise.
`cmd: symbolic and concrete eval agreement` bites hardest on `assert`, `assume` and `cover`, whose
guard can be false at run time. `cmdCheckHeavy` raises those three.

**Functions**: seven properties. The decisive shape is the *presence* of a clause, not the choice of
rule. `function: typeCheck accepts generated functions` fails exactly on a function that has a
`measure` and no `body`, and the other six are trivial or vacuous when the body is absent. An
`optionGen` coin decides body and measure presence, and a coin is not a `frequency` site, so neither
is **tunable as written**. `SetGen.TuningPrototypes` shows the rework that would expose them: its
`genPreconditionW` applies `weightedOptionGen` to the precondition coin. The precondition's *shape*
is already tunable through `genPrecondition`. `precondInputHeavy` makes a `requires` clause mention a
formal about ten times out of eleven, which gives the stripping path of PrecondElim something to
strip.

**Statements**: seven properties. This is the family that pays for the tuning machinery.

* `LoopElim preserves typeability` and `LoopElim eliminates all loops` are *entirely* vacuous on a
  loop-free program. The transform is then the identity, and each property degenerates into "the
  typechecker accepts what the generator produced". `stmt: typechecker accepts generated statements`
  already tests that. `stmtLoopHeavy` makes a loop the modal statement, and it also makes *nested*
  loops common, because the tuning threads through the whole mutual recursion. A nested loop is where
  a loop-elimination pass is most likely to be wrong.
* `DetToKleene defined iff supported` is a biconditional, so it needs both sides. It needs programs
  with an `exit`, a `funcDecl` or a `typeDecl`, where the transform is undefined, and programs
  without one, where it is defined. It also needs an invariant-bearing loop for the documented
  caveat. A profile that maximises any one constructor makes one side of the biconditional vacuous.
  `stmtKleeneBalanced` therefore equalises the leaves rather than maximises them.
* `typechecker accepts generated statements` fails only on a `funcDecl`, which is the honest gap
  between the spec and the algorithm. `stmtFuncDeclHeavy` turns it into a fast, reliable reproducer.
* `ANF is idempotent` and `ANF preserves typeability` need a **repeated** subexpression, which is
  harder to ask a generator for than it sounds. The encoder eliminates common subexpressions, so it
  fires only when the *same* non-leaf, bvar-free expression occurs twice in one body. No weight makes
  two independent draws equal. The ANF note below the procedure profiles says what does move the
  rate, and by how little.

**Procedures**: 28 properties over three transform passes. Everything the passes need is in the
procedure *bodies*, which means in the statement weights.

* The five `FilterCorrect` fields of FilterProcedures, and both call-graph fields, need real
  call-graph edges. That means `call` statements, so `procCallHeavy`.
* PrecondElim needs a call to a partial function, measured at about 6% of programs by default. For
  the `changed`-flag defect it needs a *declared function whose body* calls one, at about 0.5%.
  `procPrecondHeavy` raises `call` and `funcDecl` together, because a `funcDecl` is what carries a
  declared function into the program.
* ANFEncoder needs a repeated subexpression in one procedure body, and no weight buys that
  reliably. See the note below.

## Composition: what a knob reaches, and what it does not

`@[tunable]` threads `θ` through the tagged definition and its own recursion. It does **not** thread
`θ` into a *different* definition that the body calls by name. There are two measured consequences.

First, `genStmt` and `genStmtChain` are one mutual block, so a tag on `genStmt` alone tunes only the
outermost statement. With the loop weight at 40, top-level loops went from 15% to 72%, but a loop
inside a loop went only from 2% to 7.5%. The block's members share the auxiliary
`genStmt._mutual`, whose recursion is internal, so a tag there threads `θ` through all of it. That
gives 3.5% to 66% for a loop inside a loop, and it is what `genStmtT` and `genStmtChainT` below are
built on.

Second, an **expression** weight set here does not reach the expressions inside a generated
statement. `genStmt` calls `genLExpr` by name, and `genLExpr` and `genIndirPoly` call `genLExprBase`
by name. Where the by-name call is one hop, a restatement of the caller is cheap, and this module
writes one: `genLExprT` below is `genLExpr`'s body over the tuned callee. That is what lets
`exprEvalHeavy` and the other expression profiles reach the `expr:` family through the entry point
those properties draw from.

The same treatment for `genStmt`'s expressions would mean a restatement of the whole statement
generator, so no profile here shapes the expression inside a `cmd` or a loop guard. That needs the
sub-generator calls to take the tuning, which is a change to Basalt rather than a weighting. Until
somebody makes it, this module cannot tune the rate of a partial call for PrecondElim, and it cannot
reach the one expression-level lever that would move the ANF rate.
-/

namespace StrataGenerators.TuningProfiles

/-! Tag the shared auxiliary of the mutual block rather than `genStmt` itself. The recursion inside
`genStmt._mutual` is internal, so `θ` threads through *all* of it. A tag on `genStmt`, as its
definition site carries, tunes only the outermost statement, because its recursion runs through the
other member of the block. The "Composition" section above gives the measured difference. -/
attribute [tunable] StrataGenerators.Stmt.genStmt._mutual

/-! Two more generators need no change to their source, because their `frequency` lists are already
literal. `genLMonoTy` splits a base type against a compound type, and so decides how often a
generated type is an `arrow`, a `Map` or a `Sequence`. `genPrecondition` splits the shape of a
`requires` clause, and `SetGen.TuningPrototypes` covers that one at length.

`genGenerableTy`, `genAppArgTy` and `genLExpr` are tunable as written too. They split 9 to 1 between
a context-derived and a blind type draw, and 1 to 9 between the base rules and an operator
application. No profile here moves them, so they stay untagged rather than tagged without
evidence. -/
attribute [tunable] genLMonoTy genPrecondition

/-- Rewrite selected flat indices of a `Tuning` to constant weights. The base is always a
generator's own `.defaults`, so a profile is a difference against the shipping distribution, and
reads as one. -/
def withWeights (base : Tuning) (edits : List (Nat × Nat)) : Tuning :=
  edits.foldl (fun θ (i, w) => { θ with schedules := θ.schedules.set! i (w, 0) }) base

/-- Set one weight at every index in `idxs`. An expression profile wants this shape, because each
role recurs once per per-type site of `genLExprBase`. `app`, `ite` and each leaf are such roles, and
the type distribution dilutes a change made at one site only. -/
def withWeightsAt (base : Tuning) (idxs : List Nat) (w : Nat) : Tuning :=
  withWeights base (idxs.map (fun i => (i, w)))

-- ══════════════════════════════════════════════════════════════════════════
-- Flat indices
-- ══════════════════════════════════════════════════════════════════════════

/-! `Tuning.weight` addresses a branch by its flat index across all of a generator's sites, so these
are the names a profile is written in. An `example` in this module pins each block. If somebody
reorders a branch in the generator, the build breaks rather than the profile silently moving to the
wrong branch. -/

/-! Flat indices of `genStmt`'s two sites. The `size = 0` leaf list holds 0 to 4, and the
`size + 1` list holds 5 to 13. -/
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

/-! Flat indices of `genCmd`'s two sites. The writable-context list holds 0 to 6, and it is the only
list that offers `set`. The list for a context with no writable variable holds 7 to 11. -/
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

/-! Flat indices of `genLExprBase`'s ten sites, one per generated type. All ten sit at `n + 1`,
because the `n = 0` arms are uniform `oneOf`s and have no weight to tune.

Every site offers the same *roles*, in the same order, with three exceptions. `bool` also offers
`eq`, `∀` and `∃`. The four sites whose type has no literal have no constant branch, and those are
`ftvar`, `regex`, `Map` and `Sequence`. The first branch at `arrow` is `abs` rather than a constant.

The role lists below capture that regularity. Set a weight *per role across every site*, not per
site. A profile that raises `ite` at `bool` alone is diluted by the type distribution, because a base
type is drawn uniformly and only one draw in six is `bool`. The first `dist-report` run of
`exprQuantHeavy` showed exactly that: a ten-fold weight moved the quantifier rate from 3% to 13% and
no further, because five draws in six never reach the `bool` site at the root. -/
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
/-- The bound-variable branch of every site. It draws a `bvar` when one of the target type is in
scope, and the site's own fallback when none is. -/
def bvarAll : List Nat := [3, 14, 22, 29, 37, 45, 53, 60, 67, 74]
/-- The free-variable branch of every site. -/
def fvarAll : List Nat := [4, 15, 23, 30, 38, 46, 54, 61, 68, 75]
/-- The bare-operator branch of every site. It draws an operator whose *type is* the target type, so
the result is a leaf. Do not confuse it with `indirAll`. -/
def opAll : List Nat := [5, 16, 24, 31, 39, 47, 55, 62, 69, 76]
/-- The **Indir** branch of every site. It draws a fully-applied monomorphic operator that returns
the target type, and takes its arguments from this generator. This branch is where `Int.Add x 2`
comes from, and where the partial `Int.Safe*` builtins come from. Those builtins are why PrecondElim
exists, so this is the operator knob that matters. -/
def indirAll : List Nat := [6, 17, 25, 32, 40, 48, 56, 63, 70, 77]
/-- The **IndirPoly** branch of every site. It does the same for a polymorphic library operator. -/
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

/-- The shipping statement distribution. The leaves stand at 4 to 1 to 1 to 1 to 1, and `block`,
`ite`, `ite-nondet` and `loop` stand at 2 to 2 to 1 to 2. -/
def stmtDefault : Tuning := genStmt._mutual.defaults

/-- **Loop-heavy** (`stmt: LoopElim …`). `loop` outweighs the sum of the rest, so a loop is the modal
statement at every nesting level. A loop inside a loop then becomes common rather than incidental,
and that is where a loop-elimination pass is most likely to be wrong. `cmd` keeps its default weight,
so a loop *body* still holds commands to eliminate around.

The weight 24 comes from a sweep with `dist-report`, at 250 samples per point and max size 100:

| loop weight | 2 (default) | 8 | 16 | 24 | 40 |
| --- | --- | --- | --- | --- | --- |
| has a loop | 29% | 61% | 78% | 76% | 87% |
| has a loop inside a loop | 2% | 10% | 20% | 26% | 28% |
| first-try success | 67% | 65% | 63% | 60% | 58% |

Nesting is what the weight really buys, and it saturates. Above 24, another 16 points of weight buy
two points of nesting and cost two points of generation cost. -/
def stmtLoopHeavy : Tuning :=
  withWeights stmtDefault [(StmtIdx.loop, 24)]

/-- **Loop-heavy but shallower.** As `stmtLoopHeavy`, but it raises the leaf `cmd` branch as well, so
a loop body is more often a straight-line block than another loop. Use it when the pass under test is
about a loop's *contents* rather than its nesting. -/
def stmtLoopWide : Tuning :=
  withWeights stmtDefault [(StmtIdx.loop, 16), (StmtIdx.cmd, 12), (StmtIdx.cmd0, 12)]

/-- **`funcDecl`-heavy** (`stmt: typechecker accepts generated statements`). The honest gap between
the spec and the algorithm is a `funcDecl` statement, so this profile makes the counterexample the
common case. It is also the profile for the declared-function paths of PrecondElim. -/
def stmtFuncDeclHeavy : Tuning :=
  withWeights stmtDefault [(StmtIdx.funcDecl, 12), (StmtIdx.funcDecl0, 12)]

/-- **Call-heavy** (`proc: FilterProcedures …`, and every call-graph field). A `call` needs a callee,
so this profile bites only when the generator has a non-empty `ProcSigCtx`. The procedure-list
harness is the one that supplies one. -/
def stmtCallHeavy : Tuning :=
  withWeights stmtDefault [(StmtIdx.call, 12), (StmtIdx.call0, 12)]

/-- **Kleene-balanced** (`stmt: DetToKleene defined iff supported`). The property is a biconditional,
so it needs samples on *both* sides. One side is "the transform is defined". The other is "the block
holds no `exit`, no `funcDecl` and no `typeDecl`, and no invariant loop". A profile that maximises any
one constructor makes one side vacuous. This profile raises the three unsupported leaves to the weight
of `cmd`, which puts the undefined side at about 60% of samples.

It raises `block` as well, and that is not cosmetic. An `exit` needs an enclosing label, so at the top
level, where `labels = []`, no weight makes an `exit` reachable. A `block` is what creates the scope
that an `exit` can target. Measured, a raise of `exit` alone left it at the default rate of 3–4% of
samples. A raise of `block` to 8 alongside it takes `exit` to 13–15%. -/
def stmtKleeneBalanced : Tuning :=
  withWeights stmtDefault
    [(StmtIdx.exit, 8), (StmtIdx.funcDecl, 4), (StmtIdx.typeDecl, 4), (StmtIdx.loop, 4),
     (StmtIdx.block, 8),
     (StmtIdx.exit0, 8), (StmtIdx.funcDecl0, 4), (StmtIdx.typeDecl0, 4)]

/-- **Everything at once** for the statement suite. Loops are common, and the three leaves that
Kleene does not support and `call` are all well represented. One run then exercises the `LoopElim`,
`DetToKleene` and typechecker properties together. The price is that it is optimal for none of
them. -/
def stmtMixed : Tuning :=
  withWeights stmtDefault
    [(StmtIdx.loop, 8), (StmtIdx.funcDecl, 3), (StmtIdx.exit, 6), (StmtIdx.call, 3),
     (StmtIdx.block, 4),
     (StmtIdx.funcDecl0, 3), (StmtIdx.exit0, 6), (StmtIdx.call0, 3)]

/-! ### Procedures: the same statement knobs, aimed at the three transform passes -/

/-- **FilterProcedures.** Call-graph edges are the whole point, so `call` dominates. -/
def procCallHeavy : Tuning := stmtCallHeavy

/-- **PrecondElim.** A `funcDecl` carries a precondition into the program, and a `call` creates the
call site to assert at. This profile raises both. -/
def procPrecondHeavy : Tuning :=
  withWeights stmtDefault
    [(StmtIdx.funcDecl, 10), (StmtIdx.call, 6), (StmtIdx.funcDecl0, 10), (StmtIdx.call0, 6)]

/-! **There is deliberately no ANFEncoder profile**, and the reason is about the pass rather than
about the weights. `Core.ANFEncoder` eliminates common subexpressions. It does not flatten
expressions. `findANFEncoderTargets` collects the subexpressions of a whole procedure body and keeps
the non-leaf, bvar-free ones. Then `findDuplicates` hoists only the **duplicates** into
`var $__anf.n := …`. So the eight `proc: ANFEncoder …` properties and the two `stmt: ANF …`
properties need the same expression *twice in one body*. One nested expression is not enough, and
neither is any number of distinct ones.

No weight buys that. The generator draws every subterm independently, and no weighting of
independent choices makes two of them equal. Two things do move the rate, and both move it weakly:

* **More expressions per body.** The chance of a collision grows roughly with the square of the
  number of expressions in a body, so density helps a little. The best density lever is
  `stmtLoopHeavy` rather than anything `cmd`-shaped, because a `loop` carries a guard, a measure and
  an invariant list, while a command carries one expression. Measured, the pass changed the program on
  1% of samples at the defaults and on 3% under `stmtLoopHeavy`. A `cmd`-heavy and `block`-heavy
  variant gave 0–1%, which is why no such profile is here.
* **A degenerate expression distribution**, which raises the chance of a collision directly. That is
  a `genLExprBase` knob, and `genStmt` reaches `genLExprBase` by name, so no tuning here reaches it.
  It would also trade away the breadth that the `expr:` properties need.

The firings that were observed are collisions of small terms. In one, the generator drew
`if false then 0 else -1` into two loop invariants of one procedure, and the pass hoisted it into a
single `var`. To get this family off the floor, a generator has to *share* subterms: draw a
subexpression once and use it in two places. That is a change to the structure of the generator, and
what the pass does makes it a well-motivated one. -/

/-! ### Commands -/

def cmdDefault : Tuning := genCmd.defaults

/-- **`set`-heavy** (`cmd: set preserves variable`, `cmd: store type preservation`). Both properties
are vacuous on any command other than a `set`. The second site serves a context with no writable
variable, and it has no `set` branch to raise, so this profile leaves it alone. -/
def cmdSetHeavy : Tuning :=
  withWeights cmdDefault [(CmdIdx.setDet, 8), (CmdIdx.setNondet, 4)]

/-- **`init`-heavy** (`cmd: context growth matches inits`). Only an `init` grows the context, so a
sequence of mostly `init` commands is what gives the growth equation content. -/
def cmdInitHeavy : Tuning :=
  withWeights cmdDefault
    [(CmdIdx.initDet, 8), (CmdIdx.initNondet, 4), (CmdIdx.initDet', 8), (CmdIdx.initNondet', 4)]

/-- **Check-heavy** (`cmd: symbolic and concrete eval agreement`). The concrete `run` of an `assert`,
an `assume` or a `cover` can fail while the symbolic `eval` succeeds. Those three commands are
therefore where the agreement property has content. -/
def cmdCheckHeavy : Tuning :=
  withWeights cmdDefault
    [(CmdIdx.assert, 6), (CmdIdx.assume, 6), (CmdIdx.cover, 6),
     (CmdIdx.assert', 6), (CmdIdx.assume', 6), (CmdIdx.cover', 6)]

/-! ### Expressions -/

/-- Breadth: the shipping weights. Every rule of every type stays common, which is what the soundness
property `expr: generated terms typecheck` wants. -/
def exprBreadth : Tuning := genLExprBase.defaults

/-- **Redex-heavy** (`expr: preservation`, `progress`, `eval preserves fvars`). The evaluator
properties are trivial on a term that is already a value. So this profile raises the two rules that
build a redex, `app` and `ite`, at *every* type. It drops the leaf rules `bvar`, `fvar` and `op`, and
the literals, to the floor. The quantifiers stay at 1: a quantifier is what makes `progress` fail, and
this profile exercises the evaluator rather than pins that gap.

Measured, it takes the already-a-value rate from 7–8% down to 4%. That is the smallest margin of any
profile here, because the default distribution already does the job. `genLExpr`'s root split makes the
modal term an operator application, and an operator application is a redex. -/
def exprEvalHeavy : Tuning :=
  let θ := withWeightsAt exprBreadth ExprIdx.appAll 6
  let θ := withWeightsAt θ ExprIdx.iteAll 8
  let θ := withWeightsAt θ ExprIdx.bvarAll 1
  let θ := withWeightsAt θ ExprIdx.fvarAll 1
  let θ := withWeightsAt θ ExprIdx.opAll 1
  withWeightsAt θ ExprIdx.constAll 1

/-- **Quantifier-heavy** (`expr: progress`, `expr: resolve after type erasure`). Both properties fail
on a quantifier. `LExpr.eval` has no rule for one, and `resolve` rejects an erased `∃x. x`. Both
failures are the documented gap rather than a soundness bug, so a regression test wants them to fail
*reliably*. **This profile does not deliver that.** Measured through `genLExprT`, a quantifier appears
in 2% of terms, against 0% at the defaults.

Three measurements shaped it, and the third says why it does not work.

* A raise of `∀` and `∃` alone is not enough. They live only at the `bool` site, and a uniformly drawn
  base type is `bool` one time in six. A ten-fold quantifier weight moved the rate from 3% to 13% and
  stopped there. So `ite` goes up at every site as well, because the guard of an `ite` is a `bool`
  subterm whatever the type of the `ite` is. That is what carries the quantifier weight into terms of
  every type.
* A raise that goes *too* far is also not enough, for a more interesting reason. A quantifier at the
  root is not stuck: `LExpr.eval` leaves it alone, and the property scores it as a value. A quantifier
  in an **eliminator** position is what gets stuck, and an `ite` guard and an `eq` operand are such
  positions. So the eliminators outweigh the quantifiers here rather than the other way round.
* Both measurements above used `genLExprBase` alone. The properties draw through `genLExpr`, whose
  root `frequency` sends nine draws in ten to a fully-applied operator before any of these weights
  applies. Its subterms bottom out in the `n = 0` arms, and those arms have no quantifier branch at
  all. So the root split and the depth schedule are the binding constraints, and `θ` addresses
  neither. The note under this module's coverage table covers this.

To reproduce the `progress` gap, `exprIndirHeavy` is the better bet, though not by much. -/
def exprQuantHeavy : Tuning :=
  let θ := withWeightsAt exprBreadth ExprIdx.quantAll 8
  let θ := withWeightsAt θ ExprIdx.iteAll 14
  let θ := withWeights θ [(ExprIdx.boolEq, 8)]
  let θ := withWeightsAt θ ExprIdx.constAll 1
  let θ := withWeightsAt θ ExprIdx.bvarAll 1
  let θ := withWeightsAt θ ExprIdx.opAll 1
  withWeightsAt θ ExprIdx.fvarAll 1

/-- **fvar-heavy** (`expr: eval preserves fvars`). The property says that evaluation introduces no
*new* free variable. On a closed term it holds because the term has no free variable at all. The
profile is useful only with a non-empty `fctx`: when `fctx = []` the branch falls back to the site's
constant.

Measured against `defaultFCtx` through `genLExprT`, the share of terms that mention a free variable is
52–55% at the defaults and 53–57% here. That is no effect outside the run-to-run range. An earlier
measurement of 31% against 48% used `genLExprBase` alone, where the root is a base rule rather than an
operator application 90% of the time. The property is *already* non-vacuous on half the samples, so
this profile has little left to buy. -/
def exprFVarHeavy : Tuning :=
  withWeightsAt exprBreadth ExprIdx.fvarAll 10

/-- **Indir-heavy** (`expr: progress`). This is the profile that reproduces the `progress`
counterexamples. `genLExprBase` offers the **Indir** and **IndirPoly** rules at every type, and each
draws a fully-applied operator whose result type is the target. An operator application is therefore a
branch of `genLExprBase`, and not only something that the `genLExpr` wrapper adds at the root.

Measured on `genLExprBase` alone, at 400 draws per row:

| | default | `op` leaf ×30 | Indir ×12 | Indir ×24 |
| --- | --- | --- | --- | --- |
| `progress` fails | 22% | 17% | 30% | **38%** |
| term contains an operator | 33% | 24% | 48% | **54%** |
| term is already a value | 64% | 81% | 52% | **47%** |
| first-try success | 51% | 77% | 35% | **32%** |

Read the middle column carefully. It is why this profile replaced an earlier one that raised the
bare-`op` *leaf* branch: a raise of a leaf **crowds out** Indir, so it lowered both the failure rate
and the operator content that it was supposed to raise. The `op` branch draws an operator whose *type
is* the target type, which is a leaf and not an application. The two are easy to confuse. That lesson
stands, and the numbers do not carry over.

Through `genLExprT`, which is the entry point the property uses, those columns are nearly flat.
`progress` fails on 40–45% of default draws and on 45–49% here. An operator occurs in 90–91% of terms
either way, and first-try success is 78–80% against 80–84%. `genLExpr`'s root split already puts a
fully-applied operator at the root in nine draws out of ten. A raise of Indir *inside* `genLExprBase`
therefore has little left to raise, and costs little. Both the gain and the price were real of a
sampler that no property used. -/
def exprIndirHeavy : Tuning :=
  withWeightsAt (withWeightsAt exprBreadth ExprIdx.indirAll 24) ExprIdx.indirPolyAll 24

/-! There is deliberately no profile for the bare-`op` *leaf* branch. It draws an operator whose
*type is* the target type. A raise therefore makes terms more like values, and it also displaces the
Indir branches that carry a real operator application. The middle column of the table in
`exprIndirHeavy` is that measurement. -/

/-! ### Types

`genLMonoTy` has two sites, and each is the same 9 to 1 split between a base type and a compound type.
Indices 0 and 1 serve the case with type variables in scope, and indices 2 and 3 the case without. -/

def tyDefault : Tuning := genLMonoTy.defaults

/-- **Compound-type-heavy.** Raises an `arrow`, a `Map` or a `Sequence` type from one draw in ten to
even money. More compound types give more higher-order and collection-typed terms. They also give a
much lower first-try success rate, because `genLExprBase` can inhabit a compound type only when
something in the context already has that type. The `1st-try` column of `dist-report` makes that price
visible. This is the one profile in this module whose cost may outweigh what it buys. -/
def tyCompoundHeavy : Tuning := withWeights tyDefault [(1, 9), (3, 9)]

-- ══════════════════════════════════════════════════════════════════════════
-- Tuned entry points
-- ══════════════════════════════════════════════════════════════════════════

/-! Each definition below is the shipping generator with `θ` threaded through it. A theorem below pins
each one to the shipping generator at `θ = defaults`, so the plumbing cannot drift away from what it
claims to wrap. -/

/-- `genStmt` with every branch weight read from `θ`, threaded through the *whole* mutual recursion. A
statement nested inside a `block`, an `ite` or a `loop` body is therefore tuned as well. -/
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

/-- `genProgramStmts` with every branch weight read from `θ`. This is the entry point that the
statement family's harness draws from. -/
def genProgramStmtsT [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (size len : Nat) (pctx : PolyOpCtx := []) :
    G (List Statement × LContext CoreLParams × VarCtx) :=
  genStmtChainT θ octx tvars [] [] [] (LContext.default) [] pctx size len

/-- `genCmds` with every branch weight read from `θ`. `genCmds` is a plain fold over `genCmd` and has
no `frequency` site of its own, so this module writes the tuned chain out rather than let the
attribute emit it. -/
def genCmdsT [_root_.Gen G] (θ : Tuning) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) :
    Nat → G (List (Cmd Expression) × VarCtx)
  | 0 => pure ([], ctx)
  | n + 1 => do
    let ⟨cmd, ctx'⟩ ← genCmd.tuned θ octx tvars immutableVars ctx depth []
    let (rest, ctx'') ← genCmdsT θ octx tvars immutableVars ctx' depth n
    pure (cmd :: rest, ctx'')

/-- `genProcedure` with the statement weights of its *body* read from `θ`. The body is
`StrataGenerators.Procedure.genProcedure`'s body, and the `genStmtChainT` call is the only
difference. -/
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

/-- `genIndirPoly` with the weights of the generator it falls back to read from `θ`. The body is
`StrataGenerators.genIndirPoly`'s body, with both `genLExprBase`-valued defaults tuned. -/
def genIndirPolyT [_root_.Gen G] (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat := 3)
    (genArg : LMonoTy → G LExpr' := genLExprBase.tuned θ fctx octx pctx tvars bctx depth) :
    G LExpr' :=
  genIndirPolyCore fctx octx pctx bctx τ genArg
    (genLExprBase.tuned θ fctx octx pctx tvars bctx depth τ) maxNumArgs

/-- `genLExpr` with `genLExprBase`'s branch weights read from `θ`, threaded through its own recursion
on `depth`.

This is what makes an expression weight reach the generator that the `expr:` properties draw from.
`genLExpr` calls `genLExprBase` *by name*, and so does `genIndirPoly`, so `@[tunable]` cannot thread
`θ` across that boundary. This wrapper therefore restates `genLExpr`'s body over the tuned callee, as
`genProcedureT` does for `genProcedure`. `genLExprT_defaults` below keeps the restatement from
drifting.

`genLExpr`'s own root `frequency` keeps its literal weights. That is the 1 to 9 split between the base
rules and an operator application. `θ` addresses `genLExprBase`'s 79 branches, and a second
generator's sites in the same flat index space would move every `ExprIdx` name to the wrong
branch. -/
def genLExprT [_root_.Gen G] (θ : Tuning) (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat := 3)
    (retryCont : (LMonoTy → G LExpr') → (LMonoTy → G LExpr') := id) : G LExpr' :=
  let genArg : LMonoTy → G LExpr' :=
    retryCont <|
      match depth with
      | 0 => genLExprBase.tuned θ fctx octx pctx tvars bctx 0
      | n + 1 => fun σ => genLExprT θ fctx octx pctx tvars bctx n σ maxNumArgs retryCont
  if h : (findOpsInCtx octx τ).length > 0 then
    frequency
      [ (1, fun () => genLExprBase.tuned θ fctx octx pctx tvars bctx depth τ),
        (9, fun () =>
        pick
          (fun () => genIndir octx τ genArg h)
          (fun () => genIndirPolyT θ fctx octx pctx tvars bctx depth τ maxNumArgs genArg)) ]
      (by simp)
  else
    pick
      (fun () => genLExprBase.tuned θ fctx octx pctx tvars bctx depth τ)
      (fun () => genIndirPolyT θ fctx octx pctx tvars bctx depth τ maxNumArgs genArg)

-- ══════════════════════════════════════════════════════════════════════════
-- The plumbing is the shipping generator
-- ══════════════════════════════════════════════════════════════════════════

/-! At `θ = defaults` each wrapper is the shipping generator *definitionally*, and the kernel checks
each `Eq.refl`. `genProcedureT` and `genLExprT` restate a generator body rather than delegate to one,
and these theorems are what keep them from drifting: a divergence in any field fails one of them.
`SetGen.TuningPrototypes` states the same facts at `SetGen.Set`, for every `θ` rather than for the
defaults alone. -/

/-! Well-founded recursion makes `genStmt` and `genStmtChain` irreducible. Unseal them, so that the
theorems below can see each one as a projection of the shared auxiliary that carries the tuning. -/
unseal StrataGenerators.Stmt.genStmt StrataGenerators.Stmt.genStmtChain

/-- At the shipping weights, the tuned statement generator is `genStmt`. -/
@[simp] theorem genStmtT_defaults [_root_.Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size : Nat) :
    genStmtT (G := G) stmtDefault octx tvars immutableVars procs labels C ctx pctx size
      = genStmt octx tvars immutableVars procs labels C ctx pctx size := rfl

/-- At the shipping weights, the tuned statement-chain generator is `genStmtChain`. -/
@[simp] theorem genStmtChainT_defaults [_root_.Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (pctx : PolyOpCtx) (size len : Nat) :
    genStmtChainT (G := G) stmtDefault octx tvars immutableVars procs labels C ctx pctx size len
      = genStmtChain octx tvars immutableVars procs labels C ctx pctx size len := rfl

/-- At the shipping weights, the tuned statement-list generator is `genProgramStmts`. -/
@[simp] theorem genProgramStmtsT_defaults [_root_.Gen G] (octx : OpCtx)
    (tvars : List TyIdentifier) (size len : Nat) (pctx : PolyOpCtx) :
    genProgramStmtsT (G := G) stmtDefault octx tvars size len pctx
      = genProgramStmts octx tvars size len pctx := rfl

/-- At the shipping weights, the tuned command chain is `genCmds`, for any chain length. -/
@[simp] theorem genCmdsT_defaults [_root_.Gen G] (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth n : Nat) :
    genCmdsT (G := G) cmdDefault octx tvars immutableVars ctx depth n
      = genCmds octx tvars immutableVars ctx depth n := by
  induction n generalizing ctx with
  | zero => rfl
  | succ n ih =>
    simp only [cmdDefault] at ih
    simp only [genCmdsT, genCmds, cmdDefault, genCmd.tuned_defaults, ih]

/-- At the shipping weights, the tuned procedure generator is `genProcedure`. -/
@[simp] theorem genProcedureT_defaults [_root_.Gen G] (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (size len : Nat) (pctx : PolyOpCtx) :
    genProcedureT (G := G) stmtDefault octx procs C Γ size len pctx
      = StrataGenerators.Procedure.genProcedure octx procs C Γ size len pctx := rfl

/-- At the shipping weights, the tuned base expression generator is `genLExprBase`, as a *function*
of the target type. `@[tunable]` states its own version at full application, and `genLExprT` needs
this partially applied form for its argument generator. -/
theorem genLExprBase_tuned_defaults_fn [_root_.Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (n : Nat) :
    genLExprBase.tuned (G := G) exprBreadth fctx octx pctx tvars bctx n
      = genLExprBase fctx octx pctx tvars bctx n :=
  funext fun _ => genLExprBase.tuned_defaults ..

/-- At the shipping weights, the tuned expression generator is `genLExpr`, at every depth. Proved by
induction on the depth: the argument generator recurses, so the weights alone do not settle it. -/
@[simp] theorem genLExprT_defaults [_root_.Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat) (retryCont : (LMonoTy → G LExpr') → (LMonoTy → G LExpr')) :
    genLExprT (G := G) exprBreadth fctx octx pctx tvars bctx depth τ maxNumArgs retryCont
      = genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs retryCont := by
  induction depth generalizing τ with
  | zero =>
    simp only [genLExprT, genLExpr, genIndirPolyT, genIndirPoly,
      genLExprBase_tuned_defaults_fn]
  | succ n ih =>
    have hArg : (fun σ => genLExprT (G := G) exprBreadth fctx octx pctx tvars bctx n σ
                            maxNumArgs retryCont)
              = (fun σ => genLExpr (G := G) fctx octx pctx tvars bctx n σ maxNumArgs retryCont) :=
      funext fun σ => ih σ
    simp only [genLExprT, genLExpr, genIndirPolyT, genIndirPoly, hArg,
      genLExprBase_tuned_defaults_fn]

/-! The index tables above name the branch that each profile means to move, and the examples below
pin them. If somebody reorders a branch in `genStmt`, in `genCmd` or in `genLExprBase`, an arity or an
offset changes and one of these examples fails. Without them, every profile would silently move to
the wrong branch. -/

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
/-- Indir and IndirPoly are the last two branches of every site, so their indices are one apart. -/
example : ExprIdx.indirAll.map (· + 1) = ExprIdx.indirPolyAll := rfl
/-- Every Indir branch carries the weight 4 that the source gives it. -/
example : ExprIdx.indirAll.all (fun i => genLExprBase.defaults.schedules[i]! == (4, 0)) := by
  decide

/-! Each profile moves the branch it names and leaves its neighbours alone. The expression profiles
fold over 79 schedule entries, which is why the recursion depth goes up here. -/

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
