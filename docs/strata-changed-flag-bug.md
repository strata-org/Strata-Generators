# Bug report for Strata: pipeline phases hardcode `changed := true`

**Target repo:** `strata-org/Strata` (observed on the vendored fork at rev
`7f94d01f`; the affected code is identical to public Strata — none of it is
fork-only, and the one local modification in the vendored tree
(`DL/Lambda/Denote/Assumptions.lean`, a visibility marker) does not touch these
files).

**Severity:** low today — no consumer currently reads the value, so nothing
misbehaves at runtime. It is worth fixing because the field is *specified* to
mean something it does not mean, and the first consumer to trust it will silently
get wrong answers.

---

## Summary

`Core.PipelinePhase.transform` returns `Bool × Program`. **Four** phases return the
`Bool` as the literal `true` regardless of whether they changed the program:

| Phase | Site | Code | Reported? |
|---|---|---|---|
| `FilterProcedures` | `Strata/Transform/FilterProcedures.lean:82` | `return (true, filtered)` | yes, via private correspondence |
| `RemoveIrrelevantAxioms` | `Strata/Transform/IrrelevantAxioms.lean:81` | `return (true, pruned)` | **not yet** |
| `typeCheck` | `Strata/Languages/Core/Verifier.lean:1510` | `return (true, prog')` | **not yet** |
| `symbolicEval` | `Strata/Languages/Core/Verifier.lean:1517` | `return (true, prog')` | **not yet** |

`FilterProcedures` and `RemoveIrrelevantAxioms` are no-ops on inputs where there
is nothing to remove, and both report `true` on those inputs.

The two `Verifier.lean` phases are `let`-bound inside `corePipelinePhases`, i.e.
they are part of the *real* verification pipeline rather than optional passes.
`typeCheck` is the most defensible of the four — it annotates, so it usually does
change the program — but it is still unconditional, and reports `true` even when
type checking is a no-op.

### Why these read as oversights rather than a convention

Every *other* phase computes the flag honestly:

- `CSE.runCSE` (`CommonSubexprElim.lean:375`) uses `changed || idx' > idx`, i.e.
  "did the fresh-variable counter advance";
- `loopElim`, `insertLoopInvariantAsserts`, `CallElim` and `ProcedureInlining` all
  thread it through `Transform.runProgramUntil` (`CoreTransform.lean:406`), which
  accumulates `anyChanged` across iterations;
- `PrecondElim` and `TermCheck` compute theirs (`TerminationCheck.lean:333` returns
  the `changed` its `transformDecls` accumulated).

So four sites out of twelve hardcode, and the eight that do not all bother to get
it right. `IrrelevantAxioms.run` and `FilterProcedures.run` already compute enough
information to return the correct value.

---

## Reproduction

A program with a single procedure `A`, filtered with `A` as the sole target, so
nothing *can* be removed. Same state seeding as the real pipeline (`callGraph`
pre-populated).

```lean
import Strata.Transform.FilterProcedures
import Strata.Transform.IrrelevantAxioms

open Lambda Core

def mkProc (n : String) : Procedure :=
  { header := { name := ⟨n, ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] }

def prog : Program := { decls := [Decl.proc (mkProc "A") .empty] }

def st (p : Program) : Transform.CoreTransformState :=
  { Transform.CoreTransformState.emp with
      currentProgram := some p
      cachedAnalyses := { callGraph := some p.toProcedureCG } }

#eval do
  let ph := Core.filterProceduresPipelinePhase ["A"]
  match Transform.runWith prog ph.transform (st prog) with
  | (.ok (changed, out), _) =>
      IO.println s!"changed = {changed}, output == input ? {decide (out = prog)}"
  | (.error e, _) => IO.println s!"error {e}"
```

Observed output (both phases):

```
FilterProcedures: changed = true
  output == input ? true
  decls before/after = 1/1
IrrelevantAxioms: changed = true
  output == input ? true
```

So `changed = true` while `progOut = progIn`.

**Re-confirmed** at the currently pinned rev (`865885871`) with a sharper witness
for `RemoveIrrelevantAxioms`: a program containing **no axiom declarations at
all**, so the phase cannot prune anything regardless of which axioms it considers
irrelevant.

```
RemoveIrrelevantAxioms on an axiom-free program:
  changed flag      = true
  output == input ? = true
```

## Regression tests

All four sites are now pinned by properties in the test suite
(`StrataGenerators/PhaseChangedFlag.lean`), run by both harnesses:

| Property | Status |
|---|---|
| `phase: RemoveIrrelevantAxioms changed flag is faithful on a no-op` | FAILS (pins `IrrelevantAxioms.lean:81`) |
| `phase: FilterProcedures changed flag is faithful on a no-op` | FAILS (pins `FilterProcedures.lean:82`) |
| `phase: every pipeline phase has a faithful changed flag` | FAILS (`typeCheck`, `symbolicEval`) |
| `phase: non-hardcoded pipeline phases have a faithful changed flag` | PASSES |

The third is deliberately stated over the *whole phase list* rather than over the
four known offenders, so a phase added to `corePipelinePhases` later that
hardcodes its flag is caught without a new property being written. The fourth is
the complement, and it passing is what makes the other three informative: it
establishes that the eight honestly-computing phases really are honest, so the
failures above localise to exactly the four sites in the table.

---

## Why this is a defect rather than a defensible convention

The honest counter-argument, which we considered and initially accepted, is that
the `Bool` might mean "this phase did work / state was touched" rather than "the
program changed." `FilterProcedures` does unconditionally `modify` the cached
call graph and bump `visitedProcedures`/`erasedProcedures` statistics, so under
that reading `true` is correct. Three things argue against it:

1. **The field is undocumented.** In `Strata/Languages/Core/PipelinePhase.lean:55-59`
   the structure documents `transform` only as "The program-to-program
   transformation." The `Bool` component of the return type has no name and no
   docstring, so neither reading is sanctioned by the source.

2. **The one consumer that reads a `changed` flag uses the program-changed
   reading.** `Transform.runProgramUntil`
   (`Strata/Transform/CoreTransform.lean:363-381`) iterates to a fixpoint with
   `if !changed then break`. That is only a correct termination test if `changed`
   means the program changed. A phase that always returns `true` under this
   reading would never terminate. (Note `runProgramUntil` drives *statement-level*
   transforms, not `PipelinePhase`s, so the two phases above cannot currently
   reach it — but it establishes which convention the codebase already uses for a
   flag by this name.)

3. **Sibling phases disagree.** `ANFEncoder`
   (`Strata/Transform/ANFEncoder.lean:280`) derives its flag from real work done:
   `changed || idx' > idx`, i.e. "did the fresh-variable counter advance."
   `PrecondElim` and `TerminationCheck` likewise compute theirs. Only the two
   removal passes hardcode it, which reads as an oversight rather than a
   deliberate different convention — especially since `IrrelevantAxioms.run` and
   `FilterProcedures.run` both already compute enough information to get it right.

---

## The specification requires the program-changed reading

`Strata/Transform/CustomSpecifications.lean` (branch `jlee/transform-specs`)
defines, at line 97:

```lean
def ChangedFlagValid
    (pass : Program → Transform.CoreTransformM (Bool × Program)) : Prop :=
  ∀ (progIn : Program) (st : Transform.CoreTransformState)
    (changed : Bool) (progOut : Program) (st' : Transform.CoreTransformState),
    (pass progIn).run st = (.ok (changed, progOut), st') →
    (changed = Bool.true ↔ progOut ≠ progIn)
```

and asserts it of all three passes it covers — `changedFlagValid` appears as a
field of `FilterProcedurePhaseCorrect` (line 164), `PrecondElimPhaseCorrect`
(275), and `ANFEncoderPhaseCorrect` (379). The `↔` makes it unambiguous: `true`
requires `progOut ≠ progIn`. The repro above is a direct counterexample to the
`FilterProcedures` instance. This is how we found it: the property is one of 28
executable transcriptions of those spec fields in our generator test suite, and
it fails on essentially every generated input.

So either the passes are wrong or the spec is. Our read is that the spec has it
right and the passes should compute the flag, but the decision is yours — the
actionable ask is that the two be made to agree, and that the field be documented
either way.

---

## No consumer is currently affected

Both call sites discard the flag:

- `Strata/Languages/Core/PipelinePhase.lean:101` — `let (_, next) ← pp.transform prog`
- `Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean:583` — `let (_, prog') ← phase.transform prog`

Hence "low severity." The risk is latent: the natural future uses of this flag
are fixpoint iteration and skipping downstream work, and a phase that always
claims `true` breaks both.

---

## Suggested fix

Compute the flag from the data each pass already has.

`FilterProcedures.lean` — `run` already computes `numProcsBefore` and
`numProcsAfter` for its statistics (lines 49/53), but they are local to `run`,
whose signature is `CoreTransformM Program`. So the flag has to be produced
inside `run` and threaded out: widen it to `CoreTransformM (Bool × Program)`,
finish with

```lean
  return (numProcsAfter != numProcsBefore, { prog with decls := prunedDecls })
```

and have the phase wrapper pass the pair through rather than synthesising `true`.
`FilterProcedures.run` has one other caller (`Strata/Languages/Core.lean:164`
goes through the phase; check `git grep FilterProcedures.run` before changing the
signature) — alternatively keep `run` as-is and compare `filtered.decls.length`
against `prog.decls.length` in the wrapper, since the pass only ever removes
declarations.

`IrrelevantAxioms.lean` — same shape: `run` builds `irrelevant` locally, so
either widen it to return `(!irrelevant.isEmpty, pruned)` or compare declaration
counts in the wrapper.

`Program` derives `DecidableEq`, so `decide (filtered ≠ prog)` is also available
as a blunt-instrument alternative if the per-pass bookkeeping is inconvenient,
though it is O(program size).

Separately, and independent of which convention wins: **give the `Bool` a name
and a docstring** in the `PipelinePhase` structure. Both readings are currently
defensible from the source alone, which is the root cause here.

---

## Verification notes

- Line numbers are against vendored Strata rev `7f94d01f`.
- The `changed = true, progOut = progIn` result is from the `#eval` above, not
  inferred from reading the source.
- We checked every `.transform` call site in the tree (`git grep` for
  `.transform prog` / `pp.transform` / `phase.transform`); the two listed above
  are the only ones.
- `PrecondElim` has a *separate*, more subtle flag issue (its `.funcDecl` branch
  at `PrecondElim.lean:338` returns `hasPreconds`, derived only from the
  declaration's own preconditions, while emitting a `$wf` block for obligations
  found in the function's *body*; the sibling branches at 402/424/453 all force
  `changed := true` for the same event). That is not a hardcoded `true` and is
  deliberately out of scope for this document.
