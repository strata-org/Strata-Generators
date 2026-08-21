import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# Properties for the expressiveness of the printer

The oracle is the claim that `Core.formatProgram` logged no conversion error. This oracle
needs no parser, and it names the construct that caused the error. The oracle matters
because the printer does not fail on a construct that it cannot write. It writes a
*placeholder* and it logs an error. Such a construct can therefore round-trip as a program
that is syntactically valid but **different**, and a round trip on strings cannot find this.

The three witness properties have a fixed and finite input space: the bitvector widths of
the factory, the eighteen `Bv↔Int` operators, and the widths `0` to `63`. Each property
scores one element at a time, and its panel lists the whole space in place of a sample. The
panel then shows the *shape* of a gap, where the single `Bool` of the property can say only
that a gap exists.
-/

open Lambda Core Imperative
open StrataGenerators.Test
open StrataGenerators.PrinterCoverage

/-- A `bitvec 128` literal is printable. The factory registers the width 128, and 128 is a
    power of two, but the printer cannot write such a literal. -/
@[strata_property]
def printerBv128Literal : TestDecl :=
  (TestDecl.witness "printer: bitvec 128 literals are printable"
    checkBv128LiteralPrints).withEnumeratedPanel
    (factoryBvWidths.map fun w =>
      ({ width := w, passed := checkBvLitPrints w } : BvLitWidthResult))

/-- The eighteen `Bv↔Int` conversion operators are printable. -/
@[strata_property]
def printerBvIntConversions : TestDecl :=
  (TestDecl.witness "printer: Bv/Int conversion operators are printable"
    checkBvIntConversionsPrint).withEnumeratedPanel bvIntConversionSamples

/-- Each bitvector width that the type checker accepts is printable. `Function.typeCheck`
    accepts every width, and the printer supports five widths. The five widths are *not* the
    powers of two. The property is therefore deterministic, and it scans the whole space in
    place of a sample. -/
@[strata_property]
def printerBvWidthAgreement : TestDecl :=
  (TestDecl.witness "printer: every typecheckable bitvec width is printable"
    checkAllWidthsAgree).withEnumeratedPanel bvWidthAgreementSamples

/-- No generated program causes a conversion error. The property quantifies over a whole
    program, because the constructs that the printer cannot write occur in three places: a
    type declaration holds a `bitvec` width in a signature, an expression holds a `Bv↔Int`
    operator, and a statement holds a `funcDecl` without a body. Only `genProgram` reaches
    all three places.

    The shrinker can reduce a counterexample to this property. The oracle here is the
    printer, and it is not the type checker that the shrinker uses to keep each candidate
    well-typed. Therefore a smaller program that the printer cannot write passes the filter
    of the shrinker. Read the `error_sites` axis of the panel with this in mind: it gives the
    site that the *smallest* witness blames, and not the site that occurs most often. The
    `printer conversion-error` diagnostic gives the counts over a whole sample. -/
@[strata_property]
def printerNoConversionError : TestDecl :=
  (TestDecl.property "printer: no conversion error on generated programs"
    (fun (gp : GenProgram) => checkProgramPrintsWithoutError gp.prog)).withPanel genPrinterProgramProp
