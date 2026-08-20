import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Printer-expressiveness properties

The oracle is "`Core.formatProgram` logged no conversion error", which needs no
parser and names the offending construct. It matters because the printer substitutes
a *placeholder* and logs an error instead of failing, so an unprintable construct can
round-trip as a syntactically valid but **different** program — which a string
round-trip cannot detect.

The three witness properties have a fixed finite input space (the factory-registered
bitvector widths, the eighteen `Bv↔Int` operators, the widths `0..63`), so they are
scored element by element and their panels enumerate that space rather than sampling
it: the panel then shows the *shape* of the gap where the property's single `Bool`
can only report that a gap exists.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.PrinterCoverage

/-- A `bitvec 128` literal is printable. It is not: 128 is factory-registered and a
    power of two, and still fails. -/
@[strata_property]
def printerBv128Literal : TestDecl :=
  (TestDecl.witness "printer: bitvec 128 literals are printable" "printer"
    checkBv128LiteralPrints).withEnumeratedPanel
    (factoryBvWidths.map fun w =>
      ({ width := w, passed := checkBvLitPrints w } : BvLitWidthResult))

/-- The eighteen `Bv↔Int` conversion operators are printable. -/
@[strata_property]
def printerBvIntConversions : TestDecl :=
  (TestDecl.witness "printer: Bv/Int conversion operators are printable" "printer"
    checkBvIntConversionsPrint).withEnumeratedPanel bvIntConversionSamples

/-- Every bitvector width the typechecker accepts is printable. `Function.typeCheck`
    accepts every width, the printer supports five, and the five are *not* the powers
    of two — so this is deterministic, and a scan rather than a sample. -/
@[strata_property]
def printerBvWidthAgreement : TestDecl :=
  (TestDecl.witness "printer: every typecheckable bitvec width is printable" "printer"
    checkAllWidthsAgree).withEnumeratedPanel bvWidthAgreementSamples

/-- No generated program provokes a conversion error. Quantifies over a whole
    program because the unprintable constructs are spread across type declarations
    (`bitvec` widths in a signature), expressions (`Bv↔Int` operators) and statements
    (a bodiless `funcDecl`), and only `genProgram` reaches all three.

    Its failures *do* shrink, unlike the typechecker-completeness ones: the oracle
    here is the printer, not the typechecker the shrinker uses to keep candidates
    well-typed, so a smaller unprintable program survives the filter. Read the panel's
    `error_sites` accordingly — it is which site the *minimal* witness blames, not
    which fires most often; the unbiased cross-sample tally is the
    `printer conversion-error` diagnostic. -/
@[strata_property]
def printerNoConversionError : TestDecl :=
  (TestDecl.forAll "printer: no conversion error on generated programs" "printer"
    (fun (gp : GenProgram) => checkProgramPrintsWithoutError gp.prog)).withPanel genPrinterProgramProp
