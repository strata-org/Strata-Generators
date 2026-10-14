# FuzzGen × Strata-Generators — backend comparison

An experiment: run the suite's property tests under **Basalt's coverage-guided `FuzzGen`** and under
the **random `IO` / `Plausible.Gen`** backends *from one polymorphic term*, and measure how much
code-under-test each backend covers at an equal execution budget. The question: does coverage-guided
fuzzing beat uniform random for a generator-based property suite?

**Answer (this experiment): no.** Across every regime measured — shallow expressions/statements and
deep whole programs — uniform random covers at least as much code-under-test as coverage-guided fuzz
at an equal budget, and substantially more on deep, structured inputs. A rich generator already turns
randomness into diverse valid inputs, so uniform sampling saturates the reachable coverage quickly;
libFuzzer's byte-mutation edge is blunted when a complex byte→program decode sits between the bytes
and the code. This *validates the suite's existing `Plausible.Gen` approach*. See **Results** below.

## Design (why this is safe to keep or drop)

- **Strictly additive, one-way dependency.** Everything fuzz-specific lives in `StrataFuzz/Props.lean`,
  `StrataFuzzMain.lean`, and this directory. It depends on the mainline suite; the suite never depends
  on it. Dropping fuzzing = delete those files + revert the `basalt` require and the `StrataFuzzMain`
  lean_lib stanza in `lakefile.toml`. The mainline suite is then byte-identical to fuzz never existing.
- **Single source for generators and checks.** Each property draws from the suite's *own* polymorphic
  generator (`genLExpr` / `genProgramStmts` / `genProgram`, the same terms behind the `Generable`
  instances the mainline `Arbitrary` instances use) and scores with the suite's *own* check functions
  (`checkPreservation`, `checkAnfPreservesTyping`, …). Only the generator *wiring* is restated in
  `Props.lean` — a few lines per property — because importing `TestScaffold` (for the `Generable`
  instances) would pull the Plausible/SMT/proof closure, and with it Mathlib, into the fuzz link set.
- **One property term, three backends.** A property is a `Basalt.PBT.PropM G Unit`, polymorphic in the
  `Gen` interpretation `G`. `StrataFuzzMain` runs the same term at `FuzzGen` (libFuzzer), `IO`, and
  `Plausible.Gen`. The random backends wrap the draw in `retryGen` (the suite's in-`Gen` retry), since
  a Basalt generator can fail on a dead-end draw and Plausible would otherwise repeat it; `FuzzGen`
  needs no wrapper. See `notes/plausible-rng-rollback-demo.lean` for the subtlety.
- **Mathlib-free fuzz closure.** The `strata-fuzz` executable is *not* built by `lake`: `scripts/build.sh`
  BFS-discovers the import closure of `StrataFuzzMain`, compiles each module's emitted C, SanitizerCoverage-
  instruments a chosen subset, and links libFuzzer. Mathlib in that closure would be intractable to
  compile and would pollute the coverage signal, so the closure is kept to generators + properties +
  the Strata code under test + Basalt's pure `Gen`/`PBT` layer. (`lake build` / `lake test` use Mathlib
  freely — it's only the hand-built fuzz binary's closure that must stay Mathlib-free.)

## Build & run

```bash
# the campaign binary (libFuzzer-instrumented)
fuzz-experiment/scripts/build.sh
# a property under a backend
fuzz-experiment/strata-fuzz <property> --backend=fuzz|io|plausible [-runs=N]
# reproduce a saved libFuzzer artifact (fuzz backend only)
fuzz-experiment/strata-fuzz replay <property> <crash-file>

# the coverage-meter binary (trace-pc-guard, no libFuzzer)
BUILD_MODE=cov fuzz-experiment/scripts/build.sh
# the head-to-head: distinct code-under-test edges per backend at equal budget
fuzz-experiment/scripts/coverage-study.sh <property> [budgets...]      # deep regime: MAXLEN=2048 …
```

Properties: `expr-preservation`, `expr-progress`, `expr-preservation-deep`, `stmt-anf-preservation`,
`stmt-typecheck-complete`, `prog-lift-output-typechecks`.

## Coverage metric

One metric for all three backends: **distinct code-under-test edges**, via SanitizerCoverage
`trace-pc-guard`, counted by `scripts/covmeter.c` (no `llvm-cov` needed). `build.sh`'s `INSTR_MODULES`
regex force-instruments the Strata modules a property exercises (evaluator, type checker, ANF, Lift
pass, …) from the otherwise-plain Strata package; generators/properties are instrumented too in fuzz
mode. `fuzz` grows a libFuzzer corpus for the budget, then replays it through `strata-cov`; `io` and
`plausible` run `strata-cov` directly for the budget.

## Results (re-run 2026-09-16 on upstream basalt `lean-4.29`)

| regime | budget | fuzz | io | plausible |
|---|---|---|---|---|
| whole program (`prog-lift-output-typechecks`, MAXLEN 2048) | 5 000 | 10 394 | 16 118 | 16 477 |
| whole program | 20 000 | 11 727 | 16 622 | 16 597 |
| whole program | 50 000 | 14 387 | 16 670 | 16 637 |
| stmt-anf (nesting 2) | 20 000 | 5 689 | 5 886 | 5 871 |
| stmt-typecheck (nesting 2) | 50 000 | 5 485 | 5 559 | 5 560 |
| expr-deep (depth 4) | 20 000 | 139 | 158 | 158 |

Whole-program fuzz climbs slowly (10.4k → 14.4k over a 10× budget) while random saturates by ~5 000
draws (~16.6k) and barely moves after. Counterexample-finding is likewise no better under fuzz on the
known-failure properties (`expr-progress`: found in a handful of runs under every backend).

Coverage-guided fuzzing would be expected to help only where a **narrow, deep target is gated behind a
conjunction random almost never hits** *and* byte-mutation can incrementally reach it. No such target
was found among these preservation/typecheck properties; constructing one is the natural next probe if
the question is revisited.
