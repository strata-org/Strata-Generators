import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Diagnostics

A diagnostic measures and it makes no assertion. Each diagnostic prints a report, and it
never changes the exit code, because each result is a *distribution*. A property that holds
over inputs that all miss the interesting case is the condition that these reports make
visible.

The suite finds a diagnostic in the same way as a property. Therefore you add one in a
single file.
-/

open Lambda Core Imperative
open StrataGenerators.Test

/-- The exact `resolve` error messages for the counterexamples of the resolve-after-erase
    property. The output of Plausible shows one term that it shrank. This diagnostic draws
    fresh terms and prints their errors, so it shows the *kind* of error, such as
    `Quantifier body has non-Boolean type`. -/
@[strata_diagnostic]
def resolveErrors : Diagnostic where
  name := "Resolve-after-erase error diagnostics:"
  run cfg := do
    let _ ← printResolveErrors cfg.numTrials cfg.maxSize

/-- The round trip of an identifier that holds special characters. For each syntactic
    position, the diagnostic prints a legal identifier that holds the characters
    `. ' | \ ? ! @`, and then it parses the text again. It keeps one reproducer for each
    triple of position, result and class of character, so it shows each cause on its own.

    This is a diagnostic and not a property, because the round trip of a special character
    is a known limitation. `genIdentName` feeds the round-trip property that controls the
    exit code, and it draws none of these characters. Therefore this diagnostic is the only
    view of that path. -/
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

/-- What the suites for datatype blocks drew. The report counts the blocks that hold two or
    more datatypes, the blocks with uniform type parameters, which is the condition that
    `elimFuncs` assumes, the blocks that `addMutualBlock` accepted, the blocks that passed
    the `blockIsSmtSafe` screen of the `--smt` law properties, and the independent draws
    that really were independent.

    A block property that holds on blocks that all have one datatype, or that Strata all
    rejects, tests nothing. -/
@[strata_diagnostic]
def datatypeBlockCoverageReport : Diagnostic where
  name := "Datatype-block coverage (adt: / mutual: suites):"
  run cfg := printDatatypeBlockCoverage (min cfg.numTrials 40)

/-- How often the body of a generated function, procedure or axiom **calls** a derived
    function of an earlier datatype. The report gives one count for each family:
    constructor, tester, safe accessor and unsafe accessor.

    A count that falls to zero is the important condition, and no property that always
    holds can find it. The report uses a fixed and realistic number of declarations, and
    not the generator that scales with the size. A derived call needs a datatype block
    *and* a later function in one program, and the small draws of the property suite almost
    never give both. -/
@[strata_diagnostic]
def derivedCallCoverageReport : Diagnostic where
  name := "ADT-derived-function call coverage:"
  run cfg := printDerivedCallCoverage (min cfg.numTrials 60) cfg.maxSize

/-- The constructs that `Core.formatProgram` cannot write, with the most frequent construct
    first. For the programs that logged an error, the report also counts the programs that
    still parse again. Those programs are the dangerous ones, because a placeholder gave a
    program that is syntactically valid but *different*, and the round-trip property on
    strings cannot find such a program.

    This report locates the errors of the `printer:` suite. The property that controls the
    exit code says *that* the printer failed. This report says *what* the printer could not
    write, over a whole sample and not from one small witness. -/
@[strata_diagnostic]
def printerErrors : Diagnostic where
  name := "Printer conversion-error diagnostics:"
  run cfg := do
    let _ ← printerErrorDiagnostic cfg.numTrials cfg.maxSize

/-- This diagnostic runs the whole-program shrinker and it reports how much the shrinker
    reduces a program. During the run it also checks that each candidate is well-typed, and
    that no reduction leaves a `requires` clause without its declaration.

    Without this diagnostic, a whole run can use the `Shrinkable GenProgram` instance zero
    times. A change that breaks the shrinker can then stay hidden. -/
@[strata_diagnostic]
def programShrinker : Diagnostic where
  name := "Whole-program shrinker diagnostics:"
  run cfg := do
    let (_, illTyped, stranded) ← programShrinkDiagnostic cfg.numTrials
    if illTyped == 0 && stranded == 0 then
      IO.println "    PASS (every candidate well-typed, no stranded `requires`)"
    else
      IO.println "    SHRINKER BUG — see counts above"
