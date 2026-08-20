# Properties Tested & Bugs Found

## Properties tested

**LExprs**

- Preservation
- Progress (counterexamples found, known)
- Completeness of `LExpr.resolve` type inference (counterexamples found, previously unknown)
- `LExpr.eval` doesn't introduce any new free variables
- The concrete evaluator agrees with the SMT semantics: for a closed term `e`, if `LExpr.evalWithLState` reduces `e` to a constant, then the solver confirms that `SMTEncode(e) = SMTEncode(eval e)`
  - Restricted to base types (`int`, `string`, `bool`, `bitvec`) over `Core.Factory` operators, so that every subterm is SMT-encodable; terms that don't reduce to a constant are skipped rather than counted as counterexamples
  - Opt-in (`lake test -- --smt`), since it needs a live `cvc5` / `z3` on `PATH`

**Commands**

- Symbolic evaluation (`Cmd.eval`) agrees with concrete execution (`Cmd.run`)
  - Specifically, when concrete execution succeeds, symbolic evaluation also succeeds and results in the same store
- Preservation of store types
- `Cmd.run` preserves variables in the store (i.e. after it executes `set x (det e)`, `x` is still in the remaining store)

**Functions**

- Round-trip property (generating a random function AST, pretty-printing it and then parsing it should yield the same result)
  - 6 counterexamples found, previously unknown
- Functions are well-annotated (they satisfy the `fvars_annotated_by` predicate)
- Preservation (of the function body's type)

**Statement-related transformations**

- Completeness of typechecker with respect to the declarative typing spec
- Result of loop elimination is well-typed
- Loop elimination removes all loops
- The `detToKleene` transformation (converts deterministic control-flow to Kleene Algebra with Tests) produces a result when there are no `exit` or function + type declarations in the original list

**`FilterProcedures` transformation**

- The `FilterProcedures` transformation updates its `changed` flag correctly
  - This transformation removes unreachable procedures (unreachable from a given starting point, which is a list of procedures)
- `FilterProcedures` keeps the procedures that were specified as starting points
- `FilterProcedures` keeps all procedures that are in the transitive closure of the starting list of procedures
- `FilterProcedures` only removes procedures (and not other declarations)
- `FilterProcedures` removes all unreachable procedures (where unreachable = "not in the transitive closure")

**Precondition-filtering transformation**

(removes preconditions from procedures)

- This transformation indeed removes preconditions
- This transformation preserves the name + type signature of procedures & functions
- This transformation does not remove any declarations and preserves declaration order
- Each precondition is transformed into one `assert` in the body of the procedure

**ANF encoding / Common-subexpression elimination (CSE)**

- Result of ANF transformation is well-typed
- ANF transformation is idempotent
- ANF does not change the control-flow skeleton or call-graph
- ANF preserves procedure declarations and does not affect non-procedure declarations
- CSE does not result in dangling (unbound) bound De Bruijn variables
- Result of the symbolic evaluator is the same before/after CSE
  - (By the same, we mean that the path-condition expressions and the stores are the same after resolving the value of new variables that are created during CSE)

**Uniform `changed`-flag contract over every pipeline phase**

Rather than one property per pass, these quantify over a *phase list*, so a phase
added to `corePipelinePhases` later is covered with no new property written.

- Every phase of the Core pipeline (plus `RemoveIrrelevantAxioms`) reports `changed = true` exactly when it changed the program
- The phases that do *not* hardcode their flag all report it faithfully (the regression guard; this one passes)
- `RemoveIrrelevantAxioms` reports `changed = false` on a program with no axioms
- `FilterProcedures` reports `changed = false` when every procedure is a target

**Pretty-printer expressiveness**

The oracle is "the printer logged no conversion error", which needs no parser and
names the offending construct — strictly stronger than a string round-trip, since
the printer substitutes a syntactically valid placeholder rather than failing.

- Formatting a generated program logs no conversion error
- `bitvec 128` literals are printable
- Every `Bv{w}.ToInt` / `Bv{w}.ToUInt` / `Int.ToBv{w}` conversion operator is printable
- Every bitvector width the typechecker accepts is one the printer can express (#48)

**Whole programs**

- Completeness of the whole-program typechecker (`Program.typeCheck`) with respect to the declarative typing spec `ProgramHasTypeA`
- `getNames` of a well-typed program contains no duplicates (the first conjunct of `ProgramHasType'`, checked directly against the flat namespace rather than via the checker's incremental fold)
- If `Program.typeCheck` succeeds and produces an elaborated program, the elaborated program also typechecks
- `stripMetaData` preserves typeability
- `eraseTypes` preserves typeability 

**The eight Core transform passes with no correctness proof** (issue #69)

`Strata/Transform/` has 23 files, and only four passes have a correctness companion. Every property below is stated over a whole generated program (needed because three of these passes read declarations other than procedures: `IrrelevantAxioms` reads the axioms and the function call graph, `ProcedureInlining` reads the callee's declaration, and `FunctionInlining` reads a function body out of the factory). `TerminationCheck` is not covered: its properties need recursive functions to be non-vacuous (#15/#29).

- `IrrelevantAxioms` — the *relevance* oracle (the `changed` flag is #91): only `.ax` declarations are removed; declaration order is preserved; every retained axiom is relevant; every removed axiom is irrelevant; a removed axiom mentions no function in the call-graph closure of the seed set; the pruned program still typechecks; and — the semantic property — **pruning leaves the proof obligations exactly unchanged**.

  The last one uses Strata's executable symbolic evaluator (`toCoreProofObligationProgram`, the `symbolicEval` phase) as a differential oracle. *Equality* is the right claim here, unlike for `ProcedureInlining` where obligations legitimately duplicate per call site: an axiom is an assumption and never an obligation, so deleting one cannot add, remove or relabel a single one. Measured non-vacuous at 152 of 300 draws, all equal.

  It is necessary but **not sufficient** for the pass's `modelPreserving` annotation, and the docstring says so: pruning an axiom that some obligation *needed* leaves the obligation present but no longer provable, which is invisible without a solver since only its provability changed. Confirming that needs the `--smt` oracle and is the natural follow-up.

  One trap worth recording: the symbolic evaluator **panics** on a loop ("Cannot evaluate `loop` statement") rather than returning an error, so a `none` branch cannot absorb it — the property must screen the input with `programHasLoop` first or an unlucky draw aborts the whole run. Both symbolic-eval properties now do, and a `#guard` pins the screen
- `StructuredToUnstructured` — every `goto` target is a block label; block labels are distinct; the entry label exists; exactly one `.finish` block; every block is reachable from the entry; the command count does not shrink; a `.cfg`-bodied procedure prints
- `DetToKleene` — a measure-carrying loop translates, i.e. the measure is silently dropped rather than rejected the way an invariant is (a characterization, not a bug oracle: which of the pass and the predicate is wrong depends on whether the deterministic semantics signals `hasFailure` on a measure violation)
- `InsertLoopInvariantAsserts` + `LoopElim` — the inserted `assert` count is exactly `2n + 2m` for `n` invariants and `m` measure-carrying loops; every loop is bare after the pass; the pass is idempotent; the `insertedAssertAssumes` and `erasedLoops` statistics are faithful; no verification condition is lost through `LoopElim`; a nondeterministic loop carrying a `decreases` is rejected; `LoopElim` mints distinct block labels
- `CommonSubexprElim` — no fresh `$__cse.N` name is declared twice; the `assert` labels are preserved; the fresh declarations appear in the order the counter minted them (the weaker, checkable form of "bound before first use", which needs a scope-aware traversal to state exactly; the output-typechecks property covers the rest, since the checker rejects a reference preceding its declaration); the output typechecks
- `FunctionInlining` — fuel 0 is the identity; more fuel never un-inlines (stated as "no inlinable call remains that a smaller budget removed", not as a size comparison — a body smaller than the call it replaces makes correct inlining shrink the term); the type is preserved; no free variable is introduced (capture-freedom); and **evaluation agrees before and after inlining**, which is the sharpest of the five since it constrains the result's *meaning* rather than its shape. The factory is seeded with the program's own functions, since `Core.Factory` has no function bodies at all (0 of 310 entries).

  The eval-agreement property needs one setup step to be meaningful: `LExprEval.eval` unfolds a body only for an `.inline`-attributed function (`LExprEval.lean:274`), whereas `inlineFuncDefs` unfolds *any* bodied function — a deliberate asymmetry its module note documents. Comparing over the plain factory therefore disagrees on every sample (230 of 230, with the original stuck on the uninterpreted call), which is an oracle defect, not a pass defect. Marking the program's functions `.inline` lets the evaluator unfold exactly the set the transform does; then **266 of 266 agree**, 152 of them reducing to a canonical value. Full value-level equality over the plain factory is not testable this way — the original never reduces — and needs the SMT oracle, which remains follow-up work.

  These five fire on **231 of 400 draws**, up from 0. Four changes got there, and three addressed a bottleneck that was not the obvious one: (1) `GenState.octx` was fixed across the declaration fold, so a program declared functions its own bodies could not name — growing it left the rate at 0; (2) the property read only *procedure* bodies, whereas the pass fires in a *function* body or `requires` clause — 1 of 400; (3) polymorphic functions could not be registered at all (114 of 158 declared functions are polymorphic, and `OpCtx` holds one monotype per operator), so `funcPolyOpEntry` now sends them to `pctx`, plus order-aware declaration weights — 4 of 400; (4) the real bottleneck was **operator-selection dilution** — `genIndir`/`genIndirPoly` pick with `elements`, uniform over candidates for the target type, and `Core.Factory` supplies 105 operators returning `bool`, so one entry gave a declared function ~1% odds and it was simply never drawn. Repeating the entry (`declaredFuncWeight`) plus synthesizing one saturated call per declared bodied function (`synthesizedCalls`) took it to 231 of 400. All of it was soundness-neutral: `lake build` re-checks `genProgram_sound` unchanged.

  **Result: `FunctionInlining` is clean.** Over 600 programs and 439 inlining events — 336 at a *polymorphic* function, so `LFunc.computeTypeSubst` and `applySubst` are genuinely exercised — every property holds, as do two ad-hoc checks run while hunting (the output is a fixed point at high fuel; no type variable appears in the result that the input lacked). A real negative result rather than an absence of testing.

- `ProcedureInlining` — inlining introduces no duplicate label; no `assert` is lost; `visitedCalls`/`inlinedCalls` are consistent; the output typechecks; the cached call graph stays well-formed; and **symbolic evaluation loses no proof obligation**. The last one uses Strata's executable symbolic evaluator (`toCoreProofObligationProgram`, the `symbolicEval` phase of `corePipelinePhases`, preceded by the `nondetElim` phase it now requires) as a differential oracle, and it found the worst defect in the set (see below).

  Getting that claim right was the difficulty. Comparing the two obligation programs for *equality* is false by design — inlining verifies the callee's body once per call site, so the multiset grows (`[inner] → [inner, Callee_inner_1, Callee_inner_3]` on two call sites) — and an equality claim would report correct behaviour as a bug, the trap #79's `useArrayTheory` property fell into. Weakening it to *containment* keeps it true and still sharp enough to catch a dropped obligation.
- `NondetElim` and `LoopInitHoist` — the headline postcondition each module doc states but neither file proves: no `.nondet` guard is left after `NondetElim`, and no loop body holds an `init` after `LoopInitHoist`; plus `NondetElim`'s fresh guard names are distinct and `LoopInitHoist` preserves `uniqueInits` (the condition its same-name lift is sound under)

- **The three loop passes preserve the result of symbolic evaluation** — `InsertLoopInvariantAsserts`, `NondetElim` and `LoopInitHoist` each lose no proof obligation. The families above state these passes' claims *syntactically*; these three use Strata's executable symbolic evaluator instead, which is the only oracle that can see an obligation surviving as syntax but never being emitted to SMT.

  The evaluator refuses a loop (it *panics*, per the note above), and all three passes act on loops and leave loops behind, so neither side of the comparison can go straight to it: `LoopElim` runs after the pass **and** after the baseline. `InsertLoopInvariantAsserts` cannot be its own baseline, and `LoopElim` throws on a loop that still carries an invariant or a measure, so there the baseline is the same program with the loop annotations stripped — sound precisely because an invariant is an *annotation*: `while (c) invariant I { B }` and `while (c) { B }` run the same and owe the same obligations, and adding the ones `I` licenses is the pass's entire job.

  All three are stated as containment ("no obligation is lost"). `InsertLoopInvariantAsserts` adds obligations *by design*, so equality would report the pass working as a bug. `NondetElim` and `LoopInitHoist` both preserve the set exactly, by measurement; they are still stated as containment so a benign addition cannot turn one red while a lost obligation — a lost proof — still does.

  `NondetElim`'s claim changed shape once upstream fixed the evaluator defect below. Running the pass used to make the obligation set *grow*, because it repaired the defect, and that growth is how the defect was found. The evaluator now rejects a surviving `if *` outright and `nondetElimPipelinePhase` runs immediately before `symbolicEval` in `corePipelinePhases`, so there is no "without the pass" baseline left — a program only reaches the evaluator post-elimination. The oracle mirrors that phase pair, and the property now compares **early against late**: eliminating nondeterminism at the source, ahead of `InsertLoopInvariantAsserts` and `LoopElim`, against leaving it to the phase at the end.

  Live on 396–397 of 400 draws over two runs; the pass has something to do on 10–12 / 11–12 / 0–2 of those respectively. All three pass, so the small "fires" counts are what the `#guard`s exist to cover — and `LoopInitHoist` can be scored vacuously for a whole run. Mirroring the phase pair in the oracle is what keeps these numbers up: calling `symbolicEval` alone would make every draw carrying an `if *` return "no baseline, no claim", which measured `fires = 0` for `NondetElim` across two runs.

**Algebraic datatypes: injectivity and disjointness (`adt:`)**

Every generated `mutual … end` block denotes an initial algebra, so its constructors satisfy the `injection` and `discriminate` facts of [Software Foundations' `Tactics` chapter](https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html). The claims are about **Strata's SMT encoding of a datatype**, not about the generator, and the oracle is a real solver run through the whole Core pipeline (`Core.verify`). Universal quantification is expressed without quantifiers: each variable is an uninitialised local, which symbolic evaluation turns into an unconstrained symbolic constant. Uniformness is not covered — `addMutualBlock` already checks it syntactically.

- Constructor **injectivity** — `C x⃗ = C y⃗ → x_i = y_i`, one `assert` per field so a verdict names the field: **74/74 obligations proved by cvc5, 75/75 by z3** (opt-in, `--smt`)
- Constructor **disjointness** — in the *tester* form `!(isC u && isD u)` on a symbolic `u`: **45/45 and 53/53 proved** (opt-in, `--smt`)
  - The constructor-application form `!(C x⃗ == D y⃗)` never reaches the solver: Strata's partial evaluator folds it to `true`, so `symbolicEval` emits `assert: true`. That is asserted as a property of its own (and so is the fact that the tester form is *not* folded, which is what keeps the solver property non-vacuous)
- The law program typechecks — the screen that keeps the solver properties from being handed an ill-typed program
- No datatype derives the same function name twice (**fails honestly**, see below — though only on a rare draw: the deterministic pin is a `#guard`ed witness)
- Every emitted law query reaches a solver *verdict* — the deliberately unscreened property, which **fails honestly** on two encoder defects and reports them by cause (opt-in, `--smt`)

**Type aliases: eager versus incremental resolution (`alias:`)**

Strata resolves a type alias *during* typechecking, one declaration at a time. Both properties say this is equivalent to expanding every alias up front — that an alias is the transparent abbreviation it is documented to be. Both hold on every draw.

- The two resolution orders agree on **acceptance**
- The two resolution orders give the **same proof obligations** (the "evaluates the same" half, under Strata's own symbolic evaluator, with both sides normalised so a difference cannot be one of spelling)
- Non-vacuity took work: a generated program declares aliases that nothing *uses* (the generator's type vocabulary is kept disjoint from the alias names, repo issue #65), so resolution on a raw draw is the identity. `introduceAlias` adds the use — it aliases a ground type the program mentions and rewrites every occurrence. Introducible on 29/30 draws; 27/30 reach the obligation comparison

**`mutual … end` blocks of non-mutually-recursive datatypes (`mutual:`)**

Drawn by concatenating *independently* generated datatypes, so no field can name a sibling (verified per sample, so the properties cannot degrade into claims about connected blocks). All four hold.

- Joining datatypes that are each accepted alone into one `mutual` block keeps them accepted
- The block survives `Program.typeCheck` and its constructors are callable
- Splitting the block into one-datatype blocks preserves the derived vocabulary — the "same meaning" half (excluding the eliminators, which are block-wide by design)
- The block prints without a conversion error (screened against the printer gaps of #48, so the claim is about the block)
- Derived functions bind every type variable they mention (**fails honestly**, see below)

## Implementation bugs caught

- `LExpr` type inference is incomplete (if we erase type annotations on a well-typed term, if the resultant term contains an unannotated quantified free variable e.g. `\forall x. x`, type inference fails to reconstruct a type)
- Progress doesn't hold for `LExpr`s (this was previously known, due to uninterpreted functions, the fact that `\forall` and `\exists` quantifiers don't evaluate under `if` and equality of lambda expressions is conservative)
- 11 situations in which the parser + pretty-printer round-trip fails:
  - Type parameters to functions can't begin with `s` in their name (conflicts with `<s` signed less-than operator):
  - Pretty-printer mis-prints `real` numbers that are represented as rationals with a non-terminating decimal representation (e.g. `1/3` is `0.333...`, but is printed as `0.0` instead)
  - Unapplied unary operators can't be pretty-printed (e.g. `Bool.Not` can't be printed if it's not applied to an argument)
  - Pretty-printer misses parentheses around arrow / type constructors, so `Map int (int -> int)` is printed as `Map int int -> int`, which is mis-parsed as `(Map int int) -> int` (since type application binds tighter than `->`)
  - Pipe-escaping identifiers for types (wrapping identifiers with `|...|` to handle SMTLib names) is not done uniformly (only done for type annotations but not the return type for functions)
  - Periods are allowed in the grammar for identifiers but not accepted by the parser (which uses them to resolve namespaces)
  - Applying the factory function `Real.Neg` on a negative real number literal fails the round-trip property due to missing parenthesization (`Real.Neg (-3.0)` is printed as `--3.0`, which re-parses as `-(-3.0)`; note `Int.Neg (-3)` correctly prints as `-(-3)`)
  - Typechecker accepts bit-vector types with non-power-of-2 lengths, but the printer only supports printing the types `bv{1, 8, 16, 32, 64} `-- unsupported bitvec types are printed as `$__unknown_type` instead
  - Bit-vector literals with some width `n`, where `n` is not a power of 2, are printed as `bv{64}(n) `(i.e. the width `n` becomes the value, and the actual value of the bit-vector is discarded), changing the meaning of the term
  - `bv128` is registered in the Core factory & the DDM, but `bv128` literals are unprintable / unparseable 
  - Core contains factory functions `Bv{n}.ToInt` and `Int.ToBv{n}` for converting from bitvec <-> int, but these functions are unprintable
- The precondition elimination transformation erroneously reports its `changed` flag as false, even though it rewrites procedures to gain an `assert` statement in its body. This happens
for nested function declarations that don't have preconditions, but whose bodies invoke a precondition-carrying function (e.g. `Int.SafeDiv`).
- Non-ASCII strings are not escaped when passed to SMT-Lib, so the Core partial evaluator and SMT solvers disagree on the length of non-ASCII strings (The Core evaluator reports `Str.Length "é" = 1`, but Z3 says `Str.Length "é" = 2` and CVC5 reports `Parse Error: Non-printable character in string literal`)
- The SMT dialect's comparison operator on real numbers (represented as decimal orders) isn't a total order, i.e. it is possible for `r1 <= r2`, `r2 <= r1` and `r1 == r2` to all be false, violating trichotomy
- The SMT dialect's equality check returns false on two decimals that are mathematically equal but have different mantissa-exponent representations (e.g. `3.0` can be represented as `3 * 10^0` or `30 * 10^-1` , which are mathematically the same but considered to be not equal)
- Two more pipeline phases hardcode their `changed` flag to `true`, beyond the already-reported `FilterProcedures`: `RemoveIrrelevantAxioms` (`IrrelevantAxioms.lean:81`) reports `changed = true` even on a program containing *no axioms at all*, and the `typeCheck` / `symbolicEval` phases of `corePipelinePhases` (`Verifier.lean:1510`, `:1517`) do the same. Every other phase computes the flag honestly, which is what makes these read as oversights rather than a convention. No consumer reads the flag today (both call sites discard it), so nothing misbehaves at runtime — the defect is that the field is *specified* to mean something it does not mean.
- `bitvec 128` literals cannot be pretty-printed, even though the width is registered in the factory (`Factory.lean:872`) and has a grammar production (`bv128Lit`, `Grammar.lean:113`): `lconstToExpr` logs `unsupported bitvec width: 128`. Every other registered width prints.
- **None** of the 18 `Bv{w}.ToInt` / `Bv{w}.ToUInt` / `Int.ToBv{w}` conversion operators can be pretty-printed, at *any* registered width (`w ∈ {1, 8, 16, 32, 64, 128}`). They are all registered in the factory (`Factory.lean:850–872`) but have no grammar production and no arm in `handleUnaryOps`, so each falls through to `mkGenericCall` and is rendered as a call to a fresh free variable. A systematic hole rather than a missing case.
- The pretty-printer does not fail when it cannot express a construct: it substitutes a *syntactically valid* placeholder (`$__unknown_type` for a type, a generic call for an operator) and appends its errors to the output. So an unprintable program can round-trip "successfully" while denoting a **different** program — observed on 5 of 198 affected programs, which is exactly the case a string round-trip check structurally cannot detect. Conversion errors fire on ~50% of generated programs at the 2–5 declarations the shared whole-program wrapper samples (rising to ~86% at 6 declarations), spanning seven distinct printer sites.
- `Function.typeCheck` accepts `bitvec w` for **every** width `w` (checked 0–199, since `LMonoTy.bitvec` is unconstrained in the AST and the known type is the polymorphic `∀n. bitvec n`), but the pretty-printer supports exactly `[1, 8, 16, 32, 64]` — so 60 of the first 64 widths typecheck yet cannot be printed. This resolves issue #48, and **corrects its framing**: the supported set is not "the powers of two" (`bitvec 2`, `4` and `128` are all powers of two and all fail to print), it is the five arms hardcoded in `lmonoTyToCoreType` / `lconstToExpr` / `bvTypeOfWidth`. Note the three sites differ in how they fail: the first two substitute a placeholder, whereas `bvTypeOfWidth` silently returns `.bv64`, so an operator at an unsupported width is printed as a *64-bit* operator.
- For polymorphic functions whose type parameters are only used for type annotations on binders in their body, elaborated programs produced by the typechecker erroneously rewrite the type variable. For example, if we supply this program to the typechecker (which accepts it):

```
-- Note that the type parameter `a` only appears in the type annotation for the exists-quantified variable 
function s<a> () : bool {
  exists q : (a) :: false
}
```

`Program.typeCheck` produces the following elaborated program

```
function s () : bool {
  exists q : ($__ty1) :: false        -- the type variable `a` was rewritten to `$__ty1`
}
```

which fails to parse, with the error message `Undeclared type or category $__ty1`


- `Function.typeCheck` never inspects a function's `preconditions` field at all, so the typechecker can accept functions whose preconditions can:
  + refer to free variables not in the ambient typing context
  + have type other than Bool
  + refer to non-existent operators (i.e. operators that are not in the factory)
The function typing spec (`FuncHasType`) also does not enforce conditions on functions' preconditions, so this omission occurs both in the executable typechecker and its speccification.

One consequence is that the `PrecondElim` pass can turn a well-typed function (accpeted by the typechecker) into an ill-typed procedure. For example, given this function:

```
-- Precondition refers to a nonexistent variable `y`
function f5 () : bool requires Int.SafeDiv(1, 1) == y { true }
```

the `PrecondElim` pass produces the following:

```
-- Typechecker rejects this function with the error message: 
-- "rejected: [assume [precond_f5_0] ((~Int.SafeDiv #1 #1) == (y : int))] No free variables are allowed here!"
procedure f5$$wf ()
{
  assert [f5_precond_calls_Int.SafeDiv_0]: !(1 == 0);
  assume [precond_f5_0]: 1 / 1 == y;
};
function f5 () : bool {
  true
}
```

The five findings below come from testing the eight Core transform passes that have no correctness proof (issue #69). The first four have a self-contained reproducer in [`docs/strata-unproven-transform-bugs.md`](docs/strata-unproven-transform-bugs.md); the fifth — which is in the symbolic evaluator rather than in a pass — is in [`docs/strata-symbolic-eval-nondet-collision.md`](docs/strata-symbolic-eval-nondet-collision.md). Each is pinned by a `#guard` in `StrataGenerators/ProgramGen/UnprovenTransforms.lean` so a fix turns the guard red.

- `LoopElim` mints the same block label twice for a single loop. `removeLoop` builds one `havocd` block statement labelled `loopElim_havoc_{loop_num}` (`LoopElim.lean:126`) and places it in the output *twice* (`:139`): once inside the `arbitrary_iter_facts` block, and once after it to model the exit state. So the output contains two blocks under one label, per erased loop. The pass carries a collision *detector* for exactly these labels (`hasLabelConflict`, which rejects a body that already contains `loopElim_havoc_{n}`), which shows a duplicate is a defect and not a design choice — but the detector only compares the minted labels against the labels of the *body*, so it cannot see the collision the pass makes itself. Minimal reproducer: a procedure whose body is `while * { }`
- `ProcedureInlining` gives two call sites of the same procedure identical labels, for two independent reasons:
  + the wrapper block label is `procName ++ "$inlined"` (`ProcedureInlining.lean:288`), a plain string concatenation that reaches no counter, so two calls to `Callee` both produce a block labelled `Callee$inlined` in one caller body
  + `renameAllLocalNames` folds the *label* renaming inside the fold over `var_map` (`:110`), so when the callee declares no local variable `var_map` is empty, the fold body never runs, `replaceLabelsOfBlocksAndAssertAssumes` is never applied, and the callee's labels are copied verbatim at every call site. A callee that *does* declare a variable gets its labels freshened correctly (`Callee_inner_1`, `Callee_inner_3`), which shows the renaming itself works and the fold nesting is the defect

  A duplicate label makes two proof obligations share a name, and a verifier reports obligations by name, so the two become indistinguishable in the report
- **`ProcedureInlining` drops the callee's `requires` obligation, which is unsound.** Tracked as repo issue #107, with a self-contained runnable reproducer. A procedure's precondition is an obligation on its *callers*, emitted by `Program.eval` at the call site as `assert [(Origin_Callee_Requires)pre]`. `inlineCallCmd` (`ProcedureInlining.lean:207-289`) builds its replacement block from the callee's body plus argument/output plumbing and never reads `proc.spec.preconditions`; nothing downstream re-derives it, since after inlining there is no `call` left to attach one to.

  The minimal witness is a callee `requires x >= 0` with an **empty body**, called with `-1`. The empty body makes the precondition the program's *only* obligation, so the labels go from `[(Origin_Callee_Requires)pre]` to `[]` — the list does not shrink, it **empties**, and verifying the inlined program checks nothing at all. That also rules out the objection available against a non-empty-body witness (where the labels go `[inner, (Origin_Callee_Requires)pre] → [inner, Callee_inner_1]`), namely that the obligation was renamed rather than dropped: with an empty body there is no candidate for it to have become.

  The pass does not inspect the argument either — passing `5`, which *satisfies* the precondition, drops the check just the same; that case merely loses a check that would have succeeded, so only the `-1` case is unsound. `procedureInliningPipelinePhase` is declared `modelPreservingPipelinePhase`, so the pass asserts exactly the property it breaks. Mitigating: it is not in `corePipelinePhases`, so the default pipeline is unaffected; it is reached via `EntryPoint.lean:72`. The `ensures` mirror case (dropping an assumption — incomplete rather than unsound) is untested and worth a follow-up
- `ProcedureInlining` copies `old x` expressions verbatim while renaming `x`, turning a well-typed program into an ill-typed one. Inside a procedure body, `old x` is a free variable whose name is literally `"old x"`, which the typechecker admits because the enclosing procedure declares `x` as an `inout` parameter. The pass substitutes with `Statement.substFvar` over `var_map`, whose keys are the plain parameter names, so `"old x"` is not a key and no rule maps it. Given

```
procedure Callee (inout T : bool) { assert [inner]: old T; };
procedure Caller () { var T : bool := true; call Callee(inout T); };
```

the pass produces a caller body containing `assert [Callee_inner_2]: old T;` alongside `var Callee_T_1 : bool := T;`, and `Program.typeCheck` rejects it with `No free variables are allowed here! Free Variables: [old T]` — having accepted the input. A correct rewrite would bind the pre-state value at the call site (which is what `old` means) and rename `old x` to that binding

- **The symbolic evaluator silently drops every proof obligation after a second `if *`, which is unsound.** **Fixed upstream** by `fix(core): eliminate nondeterministic control before symbolic evaluation`, which makes `Core.Statement.eval` and `toCoreProofObligationProgram` reject a surviving nondeterministic guard and puts `nondetElimPipelinePhase` immediately before `symbolicEval` in `corePipelinePhases`. Every witness below now yields its obligations in full, and the `#guard`s at the end of `ProgramGen/UnprovenTransforms` are the regression witnesses. The analysis is kept because it is the one finding here that came out of the *evaluator* rather than a pass. Tracked as repo issue #113, with a self-contained runnable reproducer. Reproducer and analysis in [`docs/strata-symbolic-eval-nondet-collision.md`](docs/strata-symbolic-eval-nondet-collision.md). This one is in the *evaluator*, not in any of the eight passes, and it was found by the obligation-preservation properties for the three loop passes: `NondetElim` removes every `if *`, so running it made obligations **reappear**, and chasing the growth led back to `Core.Statement.evalOneStmt`.

  The evaluator has no `.nondet` case for `.ite`; it desugars one into a havoc of a synthesized boolean plus a deterministic `.ite`, and names that boolean `$__nondet_cond_{Ewn.env.pathConditions.scopes.length}` (`StatementEval.lean:586`) — from the current path-condition **depth**, not from a counter. A depth is not a supply of fresh names: it does not advance from one statement to the next, entering a `.block` does not advance it either (`Env.pushEmptyScope` touches `exprEnv.state` only), and an enclosing `.ite` advances it only until `Env.performMerge` pops the branch scope back off. So two `if *` that are siblings in one block get the *same* name; the second one's `init` re-declares a name already in scope, that path takes an error, and `evalAuxGo` stops at once (`if good.isEmpty then return`). Every obligation from there to the end of the procedure is never deferred.

  `if * { assert a }; if * { assert b }` yields the obligations `[a]`; adding `assert after` afterwards still yields `[a]`. `if (true) { … }; if (true) { … }` yields both, so it is about `.nondet` and not about `.ite`, and nesting the two guards (giving them different depths) also yields both. The name is predictable enough for a *source* program to collide with it: prefixing `init $__nondet_cond_2 : bool := true` to a body with a single `if *` empties the obligation list entirely — a program whose every assertion goes unchecked.

  It is silent in every channel: `toCoreProofObligationProgram` returns `.ok`, no `Message` is raised, the obligation program is well formed, and no statistic records it (it is not fuel exhaustion — `simulatingStmtHitOutOfFuel` stays at 0; `simulatedStmts` simply stops rising). And after `LoopElim` every `while *` **becomes** an `if *` (`LoopElim.lean:139`), so two sibling nondeterministic loops reach this on the standard pipeline. The fix suggested here was a monotone counter — the evaluator already threads `nextSplitId` for this purpose, and `NondetElim` does the same desugaring correctly with a `StringGenState`. Upstream instead removed the desugaring from the evaluator altogether and made `NondetElim` a mandatory phase in front of it, which is the same repair with one implementation of it rather than two
Coverage note, recorded because a green tick on the `CommonSubexprElim` properties should not be read as coverage: **CSE fires on 0 of 200 generated programs**, because no generated procedure body contains a duplicated subexpression (each expression is drawn independently, so two identical non-trivial subterms essentially never coincide). All four CSE properties are therefore vacuous on generated input and are tested by `#guard`s on hand-built bodies instead, and no finding above is attributed to them. This is the same limitation issue #36 measured for the `ANFEncoder` properties (599 of 600 vacuous). Making them non-vacuous needs a generator that plants a repeated subterm deliberately, which would change the expression generator and its soundness proof

- (#118) **`bitvec 0` is legal in Core and illegal in SMT-LIB.** `datatype AdtBv0 { Bv0Zero(w : bitvec 0), Bv0One() }` typechecks and is accepted by `addMutualBlock`; the encoder emits `(_ BitVec 0)`, whose index SMT-LIB 2.6 requires to be positive. cvc5 answers `Parse Error: Illegal bitvector size: 0` and z3 `bit-vector size must be greater than zero`, so every obligation mentioning the datatype is lost — never answered rather than answered wrongly
- (#119) **A legal Core identifier need not be a bare SMT-LIB symbol, and the datatype emitters do not quote.** Core's identifier alphabet includes `'`, and `_` alone is a legal Core name; neither is usable bare in SMT-LIB (§3.1). `datatype Qu { c'x(g'y : int), d() }` emits `(declare-datatype Qu ( (c'x (Qu..g'y Int)) (d)))` and cvc5 stops at `Error finding token`. The inconsistency is visible within a single line for a type parameter — pipe-quoted where it occurs in a field type, bare in the `par` binder that introduces it: `(par (vx' NK) (… (U |vx'| NK) …))`. Field types go through the DDM SMT dialect formatter, which quotes; the datatype name, the `par` list and the constructor/selector names are raw `s!"…"` interpolations (`DL/SMT/Solver.lean:244`, `DL/SMT/IncrementalSolver.lean:254`). Of the special characters the generator draws, `'` is the only offending character — `. ? @ ! $ _` all pass inside a name
- (#120) **A field named `f!` collides with the unsafe destructor of a field named `f`.** Strata derives `d..f` (safe) and `d..f!` (unsafe) per field, appending `!` (`TypeFactory.lean:539`), and `!` is a legal Core identifier character. So `datatype AdtBang { mkBang(f : int, f! : int) }` derives `AdtBang..f!` twice and `Factory.tryAddAll` rejects the whole declaration with `A function of name AdtBang..f! already exists!` — a legal datatype that cannot be declared, reported by the name of the derived function rather than by the two fields responsible
- (#121) **`d$Elim` leaves the other datatypes' type parameters free** whenever a `mutual` block's datatypes do not all declare the same type parameters — which `addMutualBlock` permits (`validateMutualBlock` checks only duplicate datatype *names*). `elimFuncs` builds `d$Elim`'s case-function arguments from every constructor of every datatype in the block but binds only `d`'s own parameters, so for `datatype Aa x { mkA(fa : x) }` and `datatype Bb y z { mkB(fb : y), nilB() }` in one block, `Aa$Elim` mentions an unbound `y` and `Bb$Elim` an unbound `x`. The site states the assumption in a comment (`let typeArgs := block[0].typeArgs`, "OK because all must have same typevars") and nothing enforces it. **Latent**: a program calling such an eliminator still typechecks, so what is lost is the constraint that a case function has the right argument type. Fires on 28 of 60 ordinary generated blocks

## Specification bugs caught during testing
- The function typing spec `FuncHasType'` permits a measure (a `decreases` clause) to exist without requiring the function body to also exist, even though the executable typechecker rejects a function if it has a measure but no body
  - The same gap is reachable at whole-program level, via both a top-level `function` declaration and an inline `funcDecl` inside a procedure body: it accounts for ~28% of generated programs being rejected by `Program.typeCheck`
- The `FilterProcedures` transformation returns a Boolean flag to indicate whether the transformation changed the program: this flag is hard-coded to `true`, even though the `Bool` is meant to be interpreted
as whether the transformation modified the analysis state (`CoreTransformState`)
- The spec for the precondition elimination transformation expects all functions in the output factory to have no preconditions, but this is not true, since the transformation doesn't eliminate preconditions for built-ins (e.g. `safeDiv`, safe destructors, etc)


## Specification bugs caught when trying to prove completeness about generators
- `MutualADTWF` doesn't require applications of type constructors to be well-kinded (i.e. match their known arities)
  - Note: this is a broader specification bug: `FuncHasTypeA`, `ProcHasTypeA`, `CmdHasTypeA` also need to enforce well-kindedness of type constructors (i.e. they're applied with the right arity). The following ill-kinded declarations are accepted by the current typing specs but rejected by the typechecker (with an error message `Type Sequence a a is not an instance of a previously registered type`):

```
-- FuncHasTypeA permits this, since it only requires the free type variable `a` to be declared
function f<a> (x : Sequence a a) : int;

-- ProcHasTypeA permits this, for the same reason as above
procedure p<a> (x : Sequence a a) { }

-- CmdHasTypeA permits both of the following commands (in the `init_nondet` / `init_det` rules)
-- Specifically, `init_nondet` only requires `RigidAnnotCompat` on the annotated type, but not well-kindedness
var y : Sequence a a := ...
```
The issue is that in `HasTypeA`, the `fvar` and `op` rules read off the type from the annotation, but it doesn't enforce well-kindedness, so any rule that relies on `HasTypeA.fvar/op` might be susceptible to the arity issue

- `MutualADTWF` doesn't allow arguments to constructors of algebraic data types to refer to type aliases 
- `MutualADTWF` doesn't require free type variables in constructor argument types (for an algebraic datta type) to be among the type parameters of the type being defined
- `CmdHasType` allows type annotations for variable initialization commands to be polymorphic, although the executable command type-checker enforces that type annotations must be monomorphic
- `ProgramHasType` is quantified over source programs (before type aliases are resolved), so it conservatively rejects some type definitions that pass the typechecker (which resolves type aliases before checking well-formedness of algebraic data type definitions).

Consider this source program:
```
type B x := int -> x;
datatype T3 { Base(), MkT3 (f : B T3) }
```

After the type alias `B` is resolved, we get:

```
datatype T3 { Base(), MkT3 (f : int -> T3) }
```
which is a legal datatype definition. However, `ProgramHasType` erroneously rejects the source program as violating the non-nested requirement for ADTs as it doesn't resolve type aliases.
