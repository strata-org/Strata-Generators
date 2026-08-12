# Calling ADT-derived functions (constructors, testers, field accessors)

## The gap

When a datatype block is declared, `LContext.addMutualBlock` (Strata,
`DL/Lambda/LExprTypeEnv.lean`) runs `genBlockFactory` and pushes **five** families
of derived `LFunc`s into `C.functions`:

| family | name shape | type (for `d : LDatatype`, `c : LConstr`) |
| --- | --- | --- |
| eliminator | `D$Elim` | higher-order, one case function per constructor of the block |
| constructor | `c` | `c.args.values → D<typeArgs>` |
| tester | `c.testerName` | `D<typeArgs> → bool` |
| safe accessor | `D..f` | `D<typeArgs> → fieldTy`, with precondition `D..isC(x)` |
| unsafe accessor | `D..f!` | `D<typeArgs> → fieldTy`, no precondition |

One naming wrinkle: the docs give the tester as `<Datatype>..is<Constructor>`
(`List..isCons`), and that *is* what Core's parser produces
(`DDMTransform/Translate.lean` expands the pattern `[.datatype, "..is",
.constructor]`). But `LConstr.testerName` defaults to `"is" ++ name`, and the
datatype *generator* keeps that default — so a generated block's tester is
`isCons`, not `List..isCons`. Reading the vocabulary out of `genBlockFactory`
(below) makes this a non-issue: whichever convention a block carries is the one
that lands in the vocabulary.

`ProgramGen`'s fold *did* thread the grown `LContext` (`s.C`) across declarations,
so those functions were genuinely present in the context of every later
declaration. But the **operator vocabularies feeding expression generation were
fixed for the whole fold**:

```lean
-- StrataGenerators/ProgramGen.lean, initState
octx := coreMonoOps        -- Int.Add, Bool.And, Str.Concat, …
pctx := corePolyOps        -- select, update, Sequence.append, …
```

Both are hand-written lists of Strata Core *primitives*. Nothing ever added a
datatype's derived functions to them, and `genLExpr` only emits an `.op` node for
a name it finds in `octx` (`pickOp` / `findOpsInCtx`) or `pctx`
(`findPolymorphicOps`). So **no generated function or procedure body ever
mentioned any earlier ADT** — not its constructors, not its testers, not its
accessors.

## The fix

Derive the operator vocabulary from the block, and thread it.

### 1. `adtDerivedOps` / `adtDerivedPolyOps` (`ProgramGen/Core.lean`)

A block's derived functions are read straight out of Strata's own
`genBlockFactory`, then projected with the *existing* `factoryOps` /
`factoryPolyOps` (`HasTypeAGen/Defs.lean`). Going through `genBlockFactory` rather
than re-deriving the names/types here is deliberate: it is the same function
`addMutualBlock` runs, so the vocabulary cannot drift from what the context
actually holds, and `factoryOps`/`factoryPolyOps` already build each type with
`mkArrow'` — the exact *generic type* form `OpsConsistentR` canonicalizes to.

A `selector` filter selects which families enter the vocabulary, so the eliminator
(`D$Elim`, whose type mentions `freshTypeArgs`-generated variables and which is not
what the docs describe) can be excluded while constructors, testers, and both
accessor variants are included.

### 2. Thread it through the fold (`ProgramGen.lean`)

`GenState.octx`/`pctx` stop being fixed: `genDeclDatatype` extends both on the
`.ok` branch, right where it already extends `C`, using the very block it added.
Every *later* `genDeclAxiom` / `genDeclFunction` / `genDeclProcedure` therefore
draws from a vocabulary containing the derived functions, and generated bodies
call them.

Monomorphic vs polymorphic placement matters, and the split is strict:

* A **monomorphic** datatype (`typeArgs = []`) yields ground-typed derived
  functions. These go in `octx` only, where the monomorphic `Indir` rule fully
  applies them — the cheapest route to a call.
* A **polymorphic** datatype yields schemes (`∀α. List<α> → bool`). These go in
  `pctx`, where `IndirPoly` unifies the return type with the target and samples
  the undetermined variables. An `octx` entry cannot serve these, since
  `opsOfType`/`findOpsInCtx` compare types with `==` and an uninstantiated `ftvar`
  never matches a concrete target.

`adtDerivedPolyOps` therefore filters out ground schemes rather than admitting
them as degenerate `∀[]. τ` entries — see "Cost" below for why that matters.

Bodies additionally receive `GenState.derivedPctx` (the derived schemes alone)
rather than the full `pctx`, again for cost reasons documented below.

### 3. Why the accessors are the interesting case

A safe accessor `D..f` carries a **precondition** `D..isC(x)`. `genLExpr` does not
know about preconditions — it emits the application regardless — so a generated
body can now contain a call whose precondition is *not* discharged. That is
intentional and is exactly what makes Strata's `PrecondElim` path reachable from
generated programs (the same rationale `genPreconditions` records for functions).
The unsafe variant `D..f!` has no precondition, so it is always well-typed in the
ordinary sense.

## Soundness

Widening `octx`/`pctx` is **soundness-neutral for `HasTypeA`**. Under the
annotated spec an `.op` node is typed from its own annotation:
`genLExpr_sound` quantifies over an *arbitrary* `octx`/`pctx`, and
`ProgramGen.lean` already records this ("Soundness is *indifferent* to this
list"). So `Inv` gains no field.

Getting there did require threading `pctx` through the generators that
previously hardcoded `pctx = []` — `genCmd`, `genStmt`/`genStmtChain`,
`genFunction`, `genProcedure` and their sub-generators — and correspondingly
generalizing the soundness chain over it (`GenCmdSoundEnv`/`GenStmtSoundEnv`
gained a `pctx` parameter; `genFunction_sound`, `genProcedure_sound`,
`genStmtChain_mutableVars`, `genCmd_outCtx_functional` and friends now quantify
over it). Every one of those is a *generalization*: each definition and theorem
is definitionally its old self at `pctx = []`, so no existing statement weakened.
The completeness side was deliberately left at `pctx = []`, matching how the repo
already scopes `retryCont`.

### The `genLExprBase` fallback

One genuine generator change was needed. `genLExprBase` ended in

```lean
| _, _ => default   -- other tcons — not generated
```

so **no datatype type was inhabitable by the base generator**. That made the
derived functions useless in practice: a tester `D..isC : D → bool` or accessor
`D..hd : D → int` is only reachable if the argument position — at type `D` — can
be filled, and at the depth floor arguments come from `genLExprBase`. The Indir
rule kept selecting those candidates and kept dead-ending.

That branch is now the same three context leaves the *depth-0* `.regex` case uses
(bvar / fvar / nullary op at that exact type — the last being precisely a nullary
constructor like `Nil`). It is still `default` when nothing in scope has the
type, so support is empty exactly where it was unreachable anyway. Three proof
sites case-split on that branch (`case h_21` in `genLExprBase_sound`,
`genLExpr_fvars_subset`, and `genLExprBase_opsConsistentR`); each previously
closed by "support is empty" and now reuses the corresponding depth-0 `.regex`
argument.

#### Leaf-only, and what that costs

Since #64 (#83) every *named* case gained `genApp`/`genIte`/Indir/IndirPoly
branches at `n + 1`. This case did **not**: it is leaf-only and therefore
depth-agnostic (`| _, τ` rather than a `0` / `n + 1` pair). The consequence is
worth stating precisely, because it bounds what the feature reaches:

> A datatype-typed *argument* is drawn from the context, never built up. So
> `isCons(xs)` is reachable with `xs` a variable or `Nil`, but `isCons(Cons(1, Nil))`
> is not — a non-nullary constructor application never fills a datatype position.

Extending this case with Indir/IndirPoly branches would lift that restriction and
is a real coverage gain. It is deliberately **not** done here, because those two
branches are recursive and the arm is currently discharged as leaf-only in four
places:

| proof | how it handles this arm today | what Indir branches would need |
| --- | --- | --- |
| `genLExprBase_sound` (`case h_21`) | three `pick*_sound` lemmas | inductive hypothesis per argument |
| `genLExprBase_fvars_subset` (`case h_21`) | three `mem_support_pick*_iff` rewrites | inductive hypothesis per argument |
| `genLExprBase_opsConsistentR` (`case h_21`) | three `pick*_mem_opsConsistentR` lemmas | inductive hypothesis, plus `hPoly` for IndirPoly |

Two proofs about `genLExprBase` are *not* affected, for different reasons:

* `genLExprBase_complete` — #64 records that it "needed no new cases: the branches
  are *appended*", and the same would hold here.
* `genLExprBase_termDepth_bound` — it never reaches this arm. It matches on
  `hτ : SimpleType τ`, and `SimpleType` has no case for a datatype `tcons`
  (`SimpleType` covers `bool`/`int`/`string`/`real`/`regex`/`bitvec` plus
  `map`/`seq`/`arrow`/`ftvar` built from those). So there is no depth bound stated
  for a datatype target today, with or without Indir branches. Stating one would
  mean extending `SimpleType` first, which is a larger change than this arm.

That belongs in its own change, with its own before/after measurements, rather than
riding along in a merge. Tracked as issue #104.

### Op-consistency

`adtDerivedPolyOps` is `factoryPolyOps` of a real factory, filtered — so it is
`PCtxWF` by construction. `mem_adtDerivedPolyOps` (in `ProgramGen/Core.lean`, which
is code-only and cannot see the Mathlib-importing `PCtxWF`) exposes the membership
fact a `PCtxWF` corollary needs.

Honest scope: `PCtxWF F pctx` is stated against *one* factory `F`, while the
threaded `pctx` mixes `corePolyOps` with per-block derived ops. A whole-program
`OpsConsistentR` statement would need `F = s.C.functions` plus
`corePolyOps ⊆ factoryPolyOps coreContext.functions`. That assembly is **not**
done here; it is recorded as future work rather than claimed.

## Cost, and the knob to turn it off

Making these calls reachable is not free. A body calling a *polymorphic*
datatype's tester or accessor goes through `IndirPoly`, which alpha-renames,
unifies at every split point, and *samples* instantiations — many of which are
unfillable, producing the same `inhabitedWitness` failure the existing retry
machinery absorbs. Two deliberate limits keep this in hand:

1. **Ground schemes are excluded from `pctx`.** A datatype with no type
   parameters already has concrete derived types, fully served by the cheap
   monomorphic `Indir` rule via `octx`. Routing them through `pctx` as well cost
   ~30× on a procedure draw for no extra coverage.
2. **Function and procedure bodies get `derivedPctx`, not `pctx`.** Those bodies
   previously ran at `pctx = []`. Handing them all of `pctx` would newly expose
   Core's 16 primitive schemes there — a ~100× cost on a procedure draw that
   nothing in this task asks for. They receive only the derived schemes.

With those in place, `ProgramGen.sample`'s default `fuel` still had to rise from
4000 to 30000. Measured at `numDecls = 12`, default bounds:

| configuration | `fuel = 4000` | `fuel = 30000` |
| --- | --- | --- |
| `derivedFamilies` all off | 8/8 | 8/8 |
| default (ADT calls enabled) | 1/8 | 8/8 |

Setting every `Bounds.derivedFamilies` flag to `false` recovers both the old
behaviour and the old fuel requirement.

## Verification

`lake build` is clean (the one pre-existing `sorry`,
`Constraints_unify_matching_complete`, is untouched) and neither driver regresses:
the failing-property set on this branch is a *subset* of `main`'s at every trial
count tried (the shared set is the documented honest failures — the `changed`-flag
bugs, the factory-stripping specs, the funcDecl gap — and both branches are
seed-dependent in exactly the same way).

### After the merge with `main`

Merging `main` (which brought the `OpCtx`-by-type index (#89), the adversarial
primitive generators (#73/#75), `genIdentName`'s support characterisation (#66), and
the whole-program shrinker (#72)) required three adaptations, none of them to the
generator's behaviour:

* **`OpCtx` is now a structure**, holding the operator list plus a hash-map index by
  type and an `agrees` proof tying them together, so it is no longer appendable as a
  list. `adtDerivedOps` accordingly returns an `OpList`, and `genDeclDatatype`
  rebuilds the context with `OpCtx.ofList` over the merged vocabulary — which is what
  re-establishes the index and its proof. `adtDerivedPolyOps` is unaffected:
  `PolyOpCtx` is still a plain list.
* **The `program` suite gained six checks from #72**, whose `programNamesNodup` label
  collides in meaning with this work's name-distinctness check. The two coexist:
  #72's is conditional on the typechecker accepting the draw, this one is
  unconditional (`programAllNamesNodup`). Both drivers and the Tyche panels run
  `programChecks ++ programADTProps`.
* **`GenProgram` now carries #72's real shrinker** rather than this branch's
  `shrink _ := []` stub, and its field is `prog` rather than `program`. The stub's
  rationale (a `Decl` cannot be dropped in isolation) is superseded: #72's shrinker
  re-checks every candidate with `Program.typeCheck`, so ill-formed sublists are
  filtered rather than avoided.

The retry fuel stayed at this branch's raised 30000 (`ProgramGen.sample`'s default
and both `genProgramWith`/`genProgramForTyche`), not `main`'s 4000/8000 — the
`IndirPoly` cost that forced the raise is exactly what enabling derived calls
introduces.

## Test coverage

`ProgramGen` is exercised in the `program` suite of both drivers. That suite has two
halves. The six checks in `Properties.programChecks` come from the whole-program
shrinker work (#72) and are *oracle-based*: each is conditional on Strata's own
`Program.typeCheck` accepting the draw. The four below are added by this work, live
in `Properties.programADTProps`, and are backed by the shared `check*` predicates in
`StrataGenerators/ProgramGen/TestSupport.lean`.

The split matters. `programChecks`'s invariants are vacuous on a draw the
typechecker rejects — about 60% of them, for the three pre-existing reasons listed
below — whereas each of the four here is established by the *fold itself* and so
holds unconditionally. They are therefore the checks that actually watch the
ADT-derived-call path on every draw, rather than only on the accepted minority.

Four properties, all passing:

| property | what it pins |
| --- | --- |
| `program: declared names are globally distinct` (`programAllNamesNodup`, distinct from `programChecks`'s typecheck-conditional `programNamesNodup`) | `ProgramHasType'`'s `getNames.Nodup`, which the fold establishes by threading one reserved set |
| `program: datatype blocks pass addMutualBlock` | the generate-and-check gate did not leak — replaying the adds (blocks *and* abstract types, since a block may reference one) succeeds |
| `program: called ADT functions are declared` | no body names a derived function of a datatype the program does not declare |
| `program: ADT calls follow the datatype declaration` | the ordering this feature is *about* — every derived call resolves against a block declared strictly **earlier** |

The last is the characteristic property: if the vocabulary were ever seeded before
the corresponding block was emitted, it would fail.

### Why `Core.Program.typeCheck` is not the oracle for *these* four

`programChecks` does assert "every generated program passes Strata's own program
typechecker" (as `program: typechecker accepts generated programs`), and it fails
honestly. The four properties here deliberately do not depend on it, because it is
**false today** for reasons that predate this work, tagged by
`programRejectionCause` (`ProgramGen/Shrink.lean`):

* `measure-no-body` — `a decreases clause was supplied but the function has no
  body`: `genFunction` draws `body` and `measure` independently. This is the known
  function-typechecker-completeness gap the function suite already pins.
* `distinct-fvar` — `Cannot find this fvar in the context! v`: `genDistinct` emits
  fresh variables, which the declarative spec accepts
  (`∃ mty, HasTypeA [] e mty`) but the algorithmic checker cannot resolve.
* `unknown-op` — `Cannot infer the type of this operation: <op>`: an operator applied
  that `Core.Factory` does not declare. This one was routinely triggered by
  `corePolyOps` itself, which listed `id`/`churchTrue`/`churchFalse`/`Sequence.map`
  — schemes absent from `Core.Factory`. Those entries have since been **removed**
  from `corePolyOps` on `main`, so the classifier still exists but no longer fires on
  a default draw; the observed causes are now `measure-no-body` and `distinct-fvar`.

Measured over 25 draws before that removal: 1 passed, 24 failed, every failure in
one of those classes. So conditioning the four checks above on it would make them vacuous on
those same 24 draws — including every draw that exercises a derived call — which is
exactly what the unconditional form avoids.

### Coverage report

The four properties above hold on every draw, so none of them would catch a
silent regression to the old structurally-zero behaviour. Both drivers therefore
also print an ungated **coverage statistic** (`printDerivedCallCoverage`): how
often a generated body actually calls a derived function, broken down by family.
A representative run:

```
ADT-derived-function call coverage:
  programs drawn: 12/12 (declaring >= 1 datatype: 12)
  bodies calling an ADT-derived function: 3
    constructors 3 | testers 3 | safe accessors 2 | unsafe accessors 1
```

Note this deliberately draws at a fixed `numDecls` (10) rather than the property
suite's size-scaled count: a derived call needs a datatype **and** a later
function/procedure in the same program, and the suite's small draws (`numDecls`
~3) essentially never exhibit one — measured 0/20 at suite sizes versus 3/12 at
the coverage size. The report prints an explicit NOTE if a run has datatypes but
no calls.

## Deliberately left open

One gap remains, recorded here rather than papered over: a **whole-program
`OpsConsistentR` statement**. `adtDerivedPolyOps` is `factoryPolyOps` of a real
factory, filtered, so it is `PCtxWF` by construction, and `mem_adtDerivedPolyOps`
exposes the membership fact a corollary needs. But `PCtxWF F pctx` is stated
against *one* factory `F`, while the threaded `pctx` mixes `corePolyOps` with
per-block derived ops — the assembly needs `F = s.C.functions` plus
`corePolyOps ⊆ factoryPolyOps coreContext.functions`.
