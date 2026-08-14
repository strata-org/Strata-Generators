# Three questions about datatypes, aliases and `mutual` blocks

Three properties were asked for, and each is now a family in the shared property
catalog (`StrataGenerators/Properties.lean`), asserted by both Plausible harnesses
and — for the ones that quantify over a generated value — visualized by a Tyche
panel:

1. **assert injectivity and disjointness of a generated datatype's constructors,
   and see whether the SMT solver can handle them** (`adt:`, five properties);
2. **resolving every type alias before typechecking must give a program that
   evaluates the same as resolving them incrementally, during typechecking**
   (`alias:`, two properties);
3. **is a `mutual … end` block of *non*-mutually-recursive datatypes accepted?**
   (`mutual:`, five properties).

Uniformness is not covered, as requested; `TypeFactory.addMutualBlock` already
checks it syntactically, in `checkConstructorArgsWF`.

## Answers, in one line each

1. **Yes, for a datatype the encoder can express.** Injectivity: 74/74 obligations
   proved by cvc5, 75/75 by z3. Disjointness: 45/45 and 53/53. But *four* defects
   sit on the way there, all reported to the Strata team as #118, #119, #120 and
   #121.
2. **Yes.** Both properties hold on every draw — once the test is made non-vacuous,
   which took work: a generated program declares aliases that nothing uses.
3. **Yes**, and it means the same as declaring each datatype separately. Asking the
   question turned up a defect in the *eliminator* of any block whose datatypes do
   not all declare the same type parameters.

---

## 1. Injectivity and disjointness under SMT

`StrataGenerators/AdtLaws.lean` builds, for a generated block, a Core program whose
proof obligations are the two laws — the `injection` and `discriminate` facts of
[Software Foundations' `Tactics` chapter](https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html).
`StrataGenerators/AdtLawsSmt.lean` discharges them with a real solver through the
whole pipeline (`Core.verify`), so the path under test is
typecheck → transform → symbolic eval → `emitDatatypes` → solver.

Universal quantification is expressed without quantifiers: each variable is an
uninitialised local (`var x : τ;`), which symbolic evaluation turns into an
unconstrained symbolic constant. For a constructor `C(a : int, b : bool)`:

```
procedure inj_0_0 () {
  var x0 : int;  var x1 : bool;  var y0 : int;  var y1 : bool;
  var u : D int := C(x0, x1);    var v : D int := C(y0, y1);
  assume [inj_0_0_h]: u == v;
  assert [inj_0_0_f0]: x0 == y0;
  assert [inj_0_0_f1]: x1 == y1;
}
```

One `assert` per field, so a verdict names the field. The negative controls (assert
`x0 == y0` with no `assume`; assert `C(x⃗) == D(y⃗)`) both **fail**, which is what
establishes that the locals really are unconstrained and the harness is not
vacuous.

Two details were necessary rather than incidental:

* **The two constructed values are bound to typed locals.** A datatype may declare a
  type parameter no constructor field mentions, so unifying from the argument types
  alone can leave it undetermined and the encoder then reports
  `Unimplemented encoding for type var $__ty27` instead of a verdict. Binding the
  application to a local declared at the ground type pins every parameter.
* **Disjointness needs the *tester* form to reach the solver.** In the constructor
  form, Strata's partial evaluator folds `!(C x⃗ == D y⃗)` to `true` on its own, so
  `symbolicEval` emits `assert [disj_0_0_1]: true;` and the solver is asked nothing.
  That is a real (and reassuring) fact about the evaluator, so it is asserted as a
  property of its own — `adt: constructor-form disjointness folds during symbolic
  evaluation` — while the claim about SMT uses `!(isC u && isD u)` on a symbolic `u`,
  which has nothing to fold. The same property also asserts that the tester form is
  **not** folded, which is the non-vacuity guard for the solver property.

### Defect 1 (#118) — `bitvec 0` is Core-legal and illegal in SMT-LIB

`datatype AdtBv0 { Bv0Zero(w : bitvec 0), Bv0One() }` typechecks and is accepted by
`addMutualBlock`. The encoder emits

```
(declare-datatype AdtBv0 ( (Bv0Zero (AdtBv0..w (_ BitVec 0))) (Bv0One)))
```

and SMT-LIB 2.6 requires a `BitVec` index to be positive. cvc5:
`Parse Error: Illegal bitvector size: 0`; z3:
`bit-vector size must be greater than zero`. Every obligation mentioning the
datatype is lost — not answered wrongly, but never answered.

### Defect 2 (#119) — a Core identifier need not be a bare SMT-LIB symbol

Core's identifier alphabet includes `'`, and `_` alone is a legal Core name.
Neither is usable as a bare SMT-LIB symbol (§3.1: a simple symbol may hold letters,
digits and `~ ! @ $ % ^ & * _ - + = < > . ? /`, and may not be a reserved word such
as `_`, `par`, `let`). The datatype emitters interpolate names verbatim:

```
(declare-datatype Qu ( (c'x (Qu..g'y Int)) (d)))      -- cvc5: Error finding token
```

and the inconsistency is visible *within one line* for a type parameter, which is
pipe-quoted where it occurs in a field type but not in the `par` binder that
introduces it:

```
(par (vx' NK) ((b (U..r Int) (U..bz4! (U |vx'| NK))) …))
       ^^^ bare                            ^^^^^ quoted
```

Field types are rendered through the DDM SMT dialect formatter
(`SMTDDM.termTypeToString`), which quotes; the datatype name, the `par` binder list
and the constructor/selector names are raw `s!"…"` interpolations
(`Strata/DL/SMT/Solver.lean:244` for the batch path,
`Strata/DL/SMT/IncrementalSolver.lean:254` for the incremental one), which do not.
Measured over the special characters the generator draws, `'` is the only offending
*character*: `. ? @ ! $ _` all pass inside a name.

Both defects are reported by `adt: every emitted law query reaches a solver
verdict`, which draws unscreened blocks and asks only whether a verdict came back.
Its report distinguishes the causes:

```
× adt: every emitted law query reaches a solver verdict
  50/76 obligations got a verdict; bitvec-0 witness: 1/3; quoted-name witness: 1/3;
  2 distinct refusal cause(s): … Illegal bitvector size: 0 | … Error finding token
```

The two law properties apply the `blockIsSmtSafe` screen so that they are about the
laws rather than a re-run of these two defects; the pure half of each defect —
that the block is Core-legal and that the screen sees it — is pinned by `#guard`s in
`AdtLaws.lean`, which need no solver.

### Defect 3 (#120) — a field named `f!` collides with the unsafe destructor of `f`

Strata derives two destructors per field: `d..f` (safe, guarded by the tester) and
`d..f!` (unsafe). The unsafe name is the safe name with `!` appended
(`mkDestructorFunc`, `TypeFactory.lean:539`), and `!` is a legal Core identifier
character. So

```
datatype AdtBang { mkBang(f : int, f! : int) }
```

derives the name `AdtBang..f!` twice — as `f!`'s safe destructor and as `f`'s unsafe
one — and `Factory.tryAddAll` rejects the whole declaration:

```
A function of name AdtBang..f! already exists! Redefinitions are not allowed.
```

A legal datatype that cannot be declared, and the message names the derived
function rather than the two fields responsible. Property: `adt: no datatype derives
the same function name twice`.

Two field names differing by exactly a trailing `!` are rare in a random draw — 0 of
400 blocks in a dedicated sweep, one hit across several `--quick` runs — so the
property is a regression net and the **deterministic** pin is the `#guard`ed
`bangFieldWitness`. Expect it green on a short run, exactly as the repo's
`procInline:` properties behave.

A fix is to mint the unsafe name from a character the identifier alphabet excludes,
or to check for the clash where the pair is generated.

---

## 2. Eager versus incremental alias resolution

`StrataGenerators/AliasResolution.lean`. Strata resolves a `TypeSynonym` *during*
type checking: `Program.typeCheck`'s fold adds each `.syn` declaration to the type
environment as it reaches it, and later declarations are de-aliased wherever the
checker happens to need it — a datatype block through
`MutualDatatype.resolveAliases`, an annotation through `AnnotCompat`/`AliasEquiv`, a
signature through `LTy.resolveAliases`.

Two properties:

* `alias: eager and incremental resolution agree on acceptance`;
* `alias: eager and incremental resolution give the same obligations` — the
  "evaluates the same" half, under Strata's own symbolic evaluator, with both sides
  normalised so that a difference cannot be one of *spelling*.

**Both pass on every draw.** The interesting part was making them non-vacuous.
`ProgramGen.genDeclAlias` emits an alias declaration that nothing ever *uses*: the
generator's type vocabulary is deliberately kept disjoint from the alias names
(invariant `Inv.aliasVocabDisjoint`), because drawing a datatype block over alias
names could not be proved sound — that is repo issue #65, whose machine-checked
counterexample is in `docs/program-gen-interleaving.md` §"Direction (3)". So on a raw
draw, resolving every alias is the identity and the property tests nothing.

`introduceAlias` therefore *adds* the use: it picks a ground type the program
mentions, adds `type A := τ;` as the first declaration, and rewrites **every**
occurrence of `τ` to `A` — signatures, `var` annotations, constructor fields and
expression annotations alike (`mapProgramTys`, since Core has no generic
map-over-types traversal). Measured: introducible on 29 of 30 draws, and 27 of 30
reach the obligation comparison (the rest hold a loop, which makes the symbolic
evaluator panic, or fail to typecheck on one of the documented completeness gaps).

Candidates are restricted to *primitive* types. Aliasing a program-declared type
would need the alias declaration to be *positioned* after that type's own
declaration, with the rewrite touching only what follows; for a primitive the alias
goes first and the rewrite is total, which is the stronger test. Two targeted
hand-built probes were also tried, on the paths where a syntactic type match could
plausibly break: an axiom whose type is an alias for `bool` (the checker matches
`.bool` syntactically at `ProgramType.lean:97`) and a `var` declared at an alias for
`int`. Both are accepted in both resolution orders, so the checker does de-alias
before those matches.

This property is the *semantic* counterpart to issue #65, which is about which
programs the typing spec calls well-formed. Nothing found here contradicts it: for a
datatype block the checker already resolves eagerly.

---

## 3. `mutual … end` blocks that are not mutually recursive

`StrataGenerators/MutualBlockShape.lean`. `genIndependentBlock` draws datatypes
*independently* — each a one-datatype draw over a reserved set threaded across the
draws, so no field can even name a sibling — and concatenates them into one block.
`crossRefs` verifies the shape on every sample, so the properties cannot quietly
degrade into claims about connected blocks. Self-reference is retained: a
self-recursive datatype is recursive but not *mutually* recursive.

Four claims, all green:

| property | what it says |
| --- | --- |
| `mutual: a block of non-mutually-recursive datatypes is accepted` | joining datatypes that are each accepted alone into one `mutual` block keeps them accepted |
| `mutual: such a block's constructors are usable in a program` | the block survives `Program.typeCheck`'s fold *and* its constructors can be called (the `AdtLaws.lawProgram` shape, reused) |
| `mutual: splitting such a block preserves the derived vocabulary` | the joint form and `n` separate one-datatype blocks give the same constructors, testers and selectors, at the same types |
| `mutual: such a block prints without a conversion error` | the `mutual … end` form renders with no logged conversion error |

Two of these needed care to be *about* the block:

* the split-equivalence claim excludes the **eliminators**, which differ by design:
  `elimFuncs` gives `d$Elim` a case-function argument for every constructor of every
  datatype in the block, so the joint and split forms cannot agree there;
* the printing claim screens out the constructs the printer is already known not to
  render (a `bitvec` width outside `[1,8,16,32,64]` — issue #48 — plus `regex` and
  function-typed fields). Without the screen it is red on 16 of 26 blocks for
  reasons that have nothing to do with `mutual`.

### Defect 4 (#121) — `d$Elim` leaves other datatypes' type parameters free

`elimFuncs` builds the case-function arguments of `d$Elim` from the constructors of
every datatype in the block, but sets `typeArgs := retTyVars ++ d.typeArgs` — only
`d`'s own parameters. If the block's datatypes do not all declare the *same*
parameters, another datatype's parameters occur free. For
`datatype Aa x { mkA(fa : x) }` and `datatype Bb y z { mkB(fb : y), nilB() }` in one
block:

```
Aa$Elim : ∀[$__ty0, $__ty1, x].    Aa x   → (x → $__ty0) → (y → $__ty1) → $__ty1 → $__ty0
                                                            ^ unbound
Bb$Elim : ∀[$__ty0, $__ty1, y, z]. Bb y z → (x → $__ty0) → (y → $__ty1) → $__ty1 → $__ty1
                                             ^ unbound
```

The site states the assumption in a comment — `let typeArgs := block[0].typeArgs`,
"OK because all must have same typevars" — but nothing enforces it:
`validateMutualBlock` checks only for duplicate datatype names, and
`checkConstructorArgsWF` constrains *occurrences*, not parameter lists.

The consequence is **latent** rather than immediate: a program calling such an
eliminator still typechecks (an unbound variable unifies), so what is lost is the
constraint that a case function has the right argument type — a caller may pass one
of the wrong type and be accepted.

It is not specific to the independent shape, which is why the property lives with the
`adt:` block checks rather than with the `mutual:` ones: `visibleRefs` lets a
datatype refer to one whose parameters are a subset of its own, so an ordinary
generated block can have differing parameter lists too. Measured: **28 of 60
ordinary blocks** and 18 of 40 independent ones are well-scoped; the rest are not.
Either `addMutualBlock` should reject a block with differing parameters, or
`elimFuncs` should bind their union.

---

## Generator gap found on the way (this repo, not Strata)

`DatatypeGen.genConstructorsForAllTypes` passes the *same* `reserved` list to each
datatype of a block instead of threading it, so two datatypes of one block can
declare a constructor (or field, or tester) of the same name; `genBlockFactory` then
fails with "A function of name f already exists!" and `addMutualBlock` rejects the
block. Measured at 1–3 of 40 blocks.

Nothing depended on this before, because `ProgramGen.genDeclDatatype` emits a block
only on the `.ok` branch of `addMutualBlock` — so a colliding block was silently
dropped rather than used, and the existing `program: datatype blocks pass
addMutualBlock` property is conditional on that gate. The block-level properties here
draw from `DatatypeGen` directly, so they see it.

It is screened (`AdtLaws.blockAccepted`) rather than asserted, since it is this
repo's generator to fix: threading `reserved` through `genConstructorsForAllTypes`
changes the shape `DatatypeGenProofs` states its soundness results against, so it is
left as follow-up work. The `printDatatypeBlockCoverage` diagnostic reports the
rejection count on every run, so the screen cannot quietly grow.

## Where each piece lives

| file | contents |
| --- | --- |
| `StrataGenerators/AdtLaws.lean` | the law programs, the eligibility screens, the two pure companions, the `f!`-collision property, `#guard`ed witnesses for all four defects that need no solver |
| `StrataGenerators/AdtLawsSmt.lean` | the solver runs: per-family tallies, and the unscreened query-acceptance property |
| `StrataGenerators/AliasResolution.lean` | `mapProgramTys`, `introduceAlias`, `expandAlias`, the two alias properties |
| `StrataGenerators/MutualBlockShape.lean` | `genIndependentBlock`, `crossRefs`, the four block claims, the eliminator-scoping property |
| `StrataGenerators/Properties.lean` | the twelve names and the three shared name↔check bundles |
| `StrataGenerators/TestScaffold.lean` | `GenAdtBlock` / `GenIndepBlock` (with shrinkers) and `printDatatypeBlockCoverage` |
| `StrataGenerators/TycheViz.lean` | the block panel (`AdtBlockPropResult`) and the panel wiring |
