import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Diagnostics

Reports that measure rather than assert. Each prints and never gates the exit code,
because each is a *distribution* — and a green property computed over inputs that all
missed the interesting case is precisely what these exist to make visible.

They are discovered exactly like properties, so adding one is also a one-file change.
-/

open Lambda Core Imperative
open StrataGenerators.Test

/-- The verbatim `resolve` error messages behind any resolve-after-erase
    counterexamples. Plausible's failure output shows one shrunk term; this samples
    fresh terms and prints the errors, so the failure *mode* ("Quantifier body has
    non-Boolean type") is visible rather than inferred. -/
@[strata_diagnostic]
def resolveErrors : Diagnostic where
  name := "Resolve-after-erase error diagnostics:"
  run cfg := do
    let _ ← printResolveErrors cfg.numTrials cfg.maxSize

/-- Special-character identifier round-trip: for each syntactic position, a legal
    identifier containing special characters (`. ' | \ ? ! @`) rendered and re-parsed,
    with one reproducer per distinct (position, outcome, character class) so different
    mechanisms surface separately instead of collapsing.

    A diagnostic rather than a property: special-character round-tripping is a known
    limitation, and `genIdentName` — which feeds the gating round-trip property — never
    reaches these characters, so this is the only view of that path. -/
@[strata_diagnostic]
def specialCharProbe : Diagnostic :=
  Diagnostic.withPanel
    { name := "function: special-character identifier round-trip"
      run := fun cfg => do
        let (probeFail, probeOk) ← specialCharProbeDiagnostic cfg.numTrials cfg.maxSize
        if probeFail == 0 then
          IO.println s!"  PASS ({probeOk} ident/position round-trips)"
        else
          IO.println s!"  FOUND {probeFail} failing ident/position cases ({probeOk} ok) \
            — see reproducers above" }
    genAndCheckIdentProbe

/-- What the block-based suites actually drew: how many blocks held two or more
    datatypes, how many had uniform type parameters (the condition `elimFuncs`
    assumes), how many Strata's `addMutualBlock` accepted, how many passed the
    `blockIsSmtSafe` screen the `--smt` law properties apply, and how many independent
    draws really were independent.

    A green block property on blocks that are all single-datatype, or all rejected, is
    a property that tested nothing. -/
@[strata_diagnostic]
def datatypeBlockCoverageReport : Diagnostic where
  name := "Datatype-block coverage (adt: / mutual: suites):"
  run cfg := printDatatypeBlockCoverage (min cfg.numTrials 40)

/-- How often a generated function/procedure/axiom body actually **calls** a derived
    function of an earlier datatype, broken down by family (constructor / tester / safe
    accessor / unsafe accessor).

    The interesting failure mode for the ADT work is silent regression to zero, which
    no `True`-valued property would catch. Deliberately measured at a fixed, realistic
    declaration count rather than through the size-scaled generator: a derived call
    needs a datatype block *and* a later function in the same program, which the
    property suite's small draws essentially never exhibit. -/
@[strata_diagnostic]
def derivedCallCoverageReport : Diagnostic where
  name := "ADT-derived-function call coverage:"
  run cfg := printDerivedCallCoverage (min cfg.numTrials 60) (min cfg.maxSize 20)

/-- Which constructs `Core.formatProgram` cannot express, most frequent first, plus —
    of the programs that logged an error — how many still re-parse. Those are the
    dangerous ones: a placeholder produced a syntactically valid but *different*
    program, which the string round-trip property cannot detect.

    This is the localisation behind the `printer:` suite. The gating property says
    *that* the printer failed; this says *what* it could not print, across a whole
    sample rather than from one minimized witness. -/
@[strata_diagnostic]
def printerErrors : Diagnostic where
  name := "Printer conversion-error diagnostics:"
  run cfg := do
    let _ ← printerErrorDiagnostic cfg.numTrials cfg.maxSize

/-- Exercise the whole-program shrinker and report how far it reduces a program,
    checking on the way that every candidate it emits is well-typed and that no
    reduction leaves a `requires` clause stranded.

    Without this the `Shrinkable GenProgram` instance can go untouched for a whole
    run: its one reliable failure (`program: typechecker accepts generated programs`)
    fails only on gap-bearing programs, which are precisely the ones no shrinker with
    this oracle can minimize, and the one shrinkable failure fires on roughly 1 draw
    in 500. A regression in the shrinker would then pass unnoticed until the day it
    matters. -/
@[strata_diagnostic]
def programShrinker : Diagnostic where
  name := "Whole-program shrinker diagnostics:"
  run cfg := do
    let (_, illTyped, stranded) ← programShrinkDiagnostic cfg.numTrials
    if illTyped == 0 && stranded == 0 then
      IO.println "    PASS (every candidate well-typed, no stranded `requires`)"
    else
      IO.println "    SHRINKER BUG — see counts above"
