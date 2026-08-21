import StrataGenerators.ProgramGen
import StrataGenerators.FunctionHasTypeAGen.Roundtrip

/-!
# The printer writes what the language accepts

`Core.formatProgram` does **not** fail on a construct that it cannot write. Through
`formatWithDDM`, it adds the line

```
-- Errors encountered during conversion:
```

to its output, and it writes a placeholder in place of the construct. Two placeholders are
dangerous, because both are *syntactically valid*:

- `unknownTypeVar`, which is `"$__unknown_type"`, turns a type that the printer cannot write
  into a **type variable**. The result can therefore round-trip with no error, and it can
  denote a different program.
- `mkGenericCall` writes an unknown operator as a call to a fresh free variable. An operator
  that the printer cannot write therefore becomes an ordinary application.

The oracle here is therefore not the claim that the output parses again. It is the claim that
**the printer logged no conversion error**. That claim is stronger, it locates the problem
better, because it names the construct in place of a message such as "parse error at 2:2",
and it needs no parser.

## The yield of the oracle

The oracle finds an error in about half of the programs from the `Arbitrary GenProgram`
instance, which draws 2 to 5 declarations. The rate is higher at 6 declarations, because each
declaration is another chance to reach a construct that the printer cannot write. Compare a
run against the rate for the number of declarations that the run drew. The errors come from
seven different sites: `lmonoTyToCoreType`, `lconstToExpr`, `handleUnaryOps`,
`handleBitvecBinaryOps`, `lopToExpr`, `extractTriggerPatterns` and `funcDeclToStatement`.

Almost each program with an error also fails to parse again, so the round-trip property
already reports those programs, but it cannot say why. The few programs that parse again are
the interesting ones. There a placeholder gave a **different program**, and a round trip on
strings cannot find such a program. This is the reason to have this property next to
`function: pretty-print/parse round-trip`, and not in place of it.

## Two gaps at widths that the printer *supports*

The checks below pin both gaps, and neither one is the known story about a width that is not a
power of two:

1. **The printer cannot write a `bv128` literal.** The grammar holds `bv128Lit`, and the
   factory registers `bv128ToIntFunc`, but `lconstToExpr` logs
   `unsupported bitvec width: 128`.

2. **The printer cannot write any `Bv↔Int` conversion operator, at any width.** The factory
   registers `Bv{w}.ToInt`, `Bv{w}.ToUInt` and `Int.ToBv{w}` for each `w` in
   `{1, 8, 16, 32, 64, 128}`. The grammar holds **no production** for any of them, and the
   printer holds **no case** for any of them. `handleUnaryOps` therefore falls through to
   `mkGenericCall`. Code can build and typecheck these operators, and the printer cannot write
   them. This is a whole family and not one missing case, and that makes it the more
   interesting of the two gaps.

## No generated operator is absent from the factory

`coreMonoOps` and `corePolyOps` both come **from `Core.Factory`**. The theorems
`coreMonoOps_eq_factoryOps` and `corePolyOps_subset_factoryPolyOps` state this, and a `#guard`
says that no operator is absent. Each operator that a generated term can apply is therefore a
real Strata operator, and no synthetic name reaches the printer.

`syntheticOps` and the filter in `strataErrorLines` stay as a net. If someone adds a synthetic
entry again, that entry cannot become a false defect of Strata. The filter reads an *error
line* and not a program, so the suite still scores the other errors of a program that holds a
synthetic operator.
-/

namespace StrataGenerators.PrinterCoverage

open Lambda Core Imperative Strata Strata.CoreDDM
open StrataGenerators

-- ── How the module finds a conversion error ───────────────────────────────

/-- The marker that `formatWithDDM` adds when `finalCtx.errors` is not empty. The oracle matches
    on this marker and not on one message, so it still works when Strata changes the words of an
    error. -/
def errorMarker : String := "Errors encountered during conversion"

/-- The text at the start of the line for one error. `ASTToCSTError.toString` writes it. -/
def errorLinePrefix : String := "Unsupported construct in "

/-- The program text that the printer claims to have written, without the block of errors at the
    end. This is the text that a consumer gives to the parser. -/
def printedText (s : String) : String :=
  (s.splitOn s!"\n\n-- {errorMarker}:").headD s

/-- The operator names that belong to this package and not to Strata. The list is **now
    vacuous**, because both vocabularies of operators come from `Core.Factory` and no generated
    term can mention a name that Strata does not define. The list stays as a net: if someone adds
    a synthetic entry again, then the printer is *correct* to reject that entry, and the suite
    must not score the rejection as a defect of Strata. -/
def syntheticOps : List String := ["id", "churchTrue", "churchFalse"]

/-- The lines for a conversion error in a printed program. The list holds no line that a
    synthetic operator of this package caused. -/
def strataErrorLines (s : String) : List String :=
  (s.splitOn "\n").filter fun line =>
    line.startsWith errorLinePrefix
      && !(syntheticOps.any fun op => line.endsWith s!": {op}")

/-- The function of the printer that an error line names. A line has the form
    `Unsupported construct in {site}: {detail}`, and `ASTToCSTError.toString` writes it. A report
    groups the errors by *site* and not by the whole message: a failure of `lconstToExpr` at
    width 3 and a failure of it at width 129 are one gap and not two gaps. -/
def errorSite (line : String) : String :=
  let afterPrefix :=
    if line.startsWith errorLinePrefix then (line.drop errorLinePrefix.length).toString
    else line
  ((afterPrefix.splitOn ":").headD afterPrefix).trimAscii.toString

/-- **The oracle for the expressiveness of the printer.** The result is `true` when a print of
    `prog` logs no conversion error that Strata caused. -/
def printsWithoutError (prog : Program) : Bool :=
  (strataErrorLines (Core.formatProgram prog).pretty).isEmpty

-- ── The property over a whole program ─────────────────────────────────────

/-- **The printer can write each construct that the generator makes.** Each declaration here is
    well-typed by construction, because `genProgram` keeps that invariant and the harness checks
    it again. A construct that the printer cannot write is therefore a gap in the printer, and
    not an invalid input. -/
def checkProgramPrintsWithoutError (prog : Program) : Bool :=
  printsWithoutError prog

/-- The different error messages that Strata caused during a print of `prog`. The diagnostic uses
    them to report *which* constructs the printer cannot write, and not only the number of
    programs with an error. -/
def programErrorLines (prog : Program) : List String :=
  (strataErrorLines (Core.formatProgram prog).pretty).dedup

-- ── The witnesses for the two gaps ────────────────────────────────────────
-- These checks use a fixed input and not a generated one, on purpose. Both gaps are about a
-- *specific* operator or a specific width, so a witness that the code builds states the defect
-- more sharply and more stably than the claim that a generated program reached it. Such a
-- witness also keeps the report reproducible when the distribution of the generator changes.

/-- The bitvector widths that the factory of Strata registers. The list holds `128`, and both
    `lconstToExpr` in the printer and the list in `bvTypeOfWidth` do not. That difference *is*
    the first gap. -/
def factoryBvWidths : List Nat := [1, 8, 16, 32, 64, 128]

/-- Prints one expression, and reports whether the print gave no error. `Core.formatExprs` runs
    the same `lexprToExpr` conversion as `formatProgram`, so a gap here is a gap in the real
    printer. -/
def exprPrintsCleanly (e : Expression.Expr) : Bool :=
  let s := (Core.formatExprs [e]).pretty
  -- `formatExprs` uses its own shorter text for an error, which is `-- Errors: `. The check
  -- therefore reads both markers, and it does not read only the marker for a program.
  !(s.splitOn "-- Errors:").length > 1 && (strataErrorLines s).isEmpty

/-- A bitvector literal at the width `w`, as a constant with an annotation. -/
def bvLit (w : Nat) : Expression.Expr :=
  .const () (.bitvecConst w (BitVec.ofNat w 1))

/-- Whether a `bitvec w` literal prints with no conversion error. This is the check for one width
    under `checkBv128LiteralPrints`. It has a name, so that a report can score each registered
    width with the same function that the property applies at 128. -/
def checkBvLitPrints (w : Nat) : Bool := exprPrintsCleanly (bvLit w)

/-- **A `bitvec 128` literal prints.** The factory registers the width 128, and the grammar holds
    the production `bv128Lit` for it. Each *other* registered width prints, and that is what makes
    128 an omission and not a boundary of the design. -/
def checkBv128LiteralPrints : Bool := checkBvLitPrints 128

/-- The registered widths whose literal does not print. -/
def unprintableBvLiteralWidths : List Nat :=
  factoryBvWidths.filter (fun w => !checkBvLitPrints w)

/-- The names of the `Bv↔Int` conversion operators that the factory registers at the width `w`. -/
def bvIntConversionOps (w : Nat) : List String :=
  [s!"Bv{w}.ToInt", s!"Bv{w}.ToUInt", s!"Int.ToBv{w}"]

/-- The name of each registered `Bv↔Int` conversion operator. -/
def allBvIntConversionOps : List String :=
  factoryBvWidths.flatMap bvIntConversionOps

/-- An application of a named unary operator to a placeholder argument. The argument is an `int`
    literal. `handleUnaryOps` chooses its branch from the *name of the operator* alone, so the
    type of the argument does not change whether the printer can write the operator. -/
def unaryApp (name : String) : Expression.Expr :=
  .app () (.op () ⟨name, ()⟩ none) (.const () (.intConst 1))

/-- Whether an application of the named operator prints with no conversion error. This is the
    check for one operator under `checkBvIntConversionsPrint`. It has a name, so that a report can
    score each of the eighteen operators on its own. A total of `18/18` says that a whole family
    is absent, and only the verdict for each operator shows that the gap covers *each* width and
    *each* direction. -/
def checkBvIntConversionPrints (op : String) : Bool := exprPrintsCleanly (unaryApp op)

/-- **The printer can write each registered `Bv↔Int` conversion operator, at each width.**
    `handleUnaryOps` lists `.Not`, `.Neg`, `SafeNeg`, the predicates for an overflow, and nine
    shapes of `bvExtract`. An operator with no branch there falls through to `mkGenericCall`. -/
def checkBvIntConversionsPrint : Bool :=
  allBvIntConversionOps.all checkBvIntConversionPrints

/-- The `Bv↔Int` conversion operators that do not print. -/
def unprintableBvIntConversions : List String :=
  allBvIntConversionOps.filter (fun op => !checkBvIntConversionPrints op)

-- ── The bitvector widths: the type checker against the printer ────────────
/-!
## The difference between the two sets of widths

Two questions motivate this section. Does the type checker of Strata *accept* a bitvector whose
width is not a power of two? If it does, do the round-trip properties then fail on such a
bitvector?

**The answer to both questions is yes, and the difference itself is the finding.**
`Function.typeCheck` accepts `bitvec w` for **each** `w` from 0 to 199, because the AST puts no
constraint on `LMonoTy.bitvec` and the entry in the known types is the polymorphic
`t[∀n. bitvec n]`. The printer supports **five** widths.

### A correction to the usual account

The usual account says that a round trip fails because the DDM needs the width of a bit vector to
be a power of two. That predicate is **wrong**. `bitvec 2`, `bitvec 4` and `bitvec 128` are all
powers of two, and none of them prints. A scan over the widths 0 to 199 shows that the widths
which print are exactly

```
[1, 8, 16, 32, 64]
```

That set is not the set of the powers of two. It is *the five branches in the printer*:
`lmonoTyToCoreType` for a type, `lconstToExpr` for a literal, and `bvTypeOfWidth` for the type
argument of an operator. The correct statement of the defect is therefore that the printer
supports a fixed set of five widths, and that the type checker and the AST accept each width. A
guard for a power of two is not the fix.

`bitvec 128` needs a separate note, and it has its own property above. The factory registers that
width *and* the grammar holds a production for it, so it is the one width where the printer
differs from the rest of Strata and is not only narrow.

### Two different failure modes, and why the case for a type is the dangerous one

`bvTypeOfWidth` emits **no** placeholder type. It logs an error and it returns `.bv64`. The
printer therefore writes an operator at a width that it does not support as a **64-bit**
operator. This is a silent change of the width, and not a visible hole.

`lmonoTyToCoreType` writes `$__unknown_type`, which is a *type variable*. Therefore
`function f (x : bitvec 3) : bitvec 3` prints as
`function f (x : $__unknown_type) : $__unknown_type`. That text does not parse again, because
`$__unknown_type` is not a declared type argument, and it also does not parse in a host function
that *already* has a type parameter. Today this defect therefore appears as a parse failure in a
round trip, and not as a program that differs in silence. That is luck and not design: the
placeholder is syntactically valid, and the fallback to `.bv64` shows that the same code writes a
*plausible* wrong answer.
-/

/-- The bitvector widths that the printer supports. A scan over the widths 0 to 199 gives this
    list, and no one assumed it. The list holds the five branches in `lmonoTyToCoreType`,
    `lconstToExpr` and `bvTypeOfWidth`.

    The name holds the word `printable` and not the word `registered`, on purpose. The list is
    **not** the set that the factory registers, which is `SmtEval.registeredBvWidths` and `128`,
    and it is **not** the set of the powers of two. -/
def printableBvWidths : List Nat := [1, 8, 16, 32, 64]

/-- The identity function on one input at `bitvec w`. It is the smallest host for a width in a
    *type* position, because the width is the type of the input and the type of the output. -/
def bvIdentityFunc (w : Nat) : Function :=
  { name := ⟨"f", ()⟩, typeArgs := [], inputs := [("x", .bitvec w)],
    output := .bitvec w, body := some (.fvar () ⟨"x", ()⟩ (some (.bitvec w))) }

/-- Whether `Function.typeCheck` accepts the identity function at `bitvec w`. The result is `true`
    for each `w` from 0 to 199. -/
def widthTypeChecks (w : Nat) : Bool :=
  match Function.typeCheck funcCheckContext TEnv.default (bvIdentityFunc w) with
  | .ok _ => true
  | .error _ => false

/-- Whether the identity function at `bitvec w` prints with no conversion error. -/
def widthPrintsCleanly (w : Nat) : Bool :=
  (strataErrorLines (formatFuncAsProgram (bvIdentityFunc w))).isEmpty

/-- **The two sets of widths agree.** The *printer* must be able to write each width that the
    *type checker* accepts, because Strata must be able to write down each program that it
    accepts.

    The property is an implication, from the type check to the print, and not an equation with
    `printableBvWidths`. It is therefore a claim about the consistency of Strata, and not a second
    statement of the list of branches in the printer.

    The property quantifies over a width and not over a generated function, because the property
    belongs *to the width*. `genLMonoTyBitvec` draws from `Nat.arbitrary`, which samples each
    width, so the property over a whole program above already covers this space. A generated hit
    does not say *which* width caused the failure, and this property does. -/
def checkWidthTypeCheckPrinterAgreement (w : Nat) : Bool :=
  !widthTypeChecks w || widthPrintsCleanly w

/-- The widths from 0 to `bound` that the type checker accepts and the printer cannot write. The
    diagnostic uses this list. -/
def divergentBvWidths (bound : Nat) : List Nat :=
  (List.range bound).filter (fun w => !checkWidthTypeCheckPrinterAgreement w)

/-- **The claim that the two sets of widths agree, as one closed `Bool`**, over the widths 0 to
    63. That range holds several powers of two and both parities, and it stays cheap, because each
    width runs `Function.typeCheck` and then a print. -/
def checkAllWidthsAgree : Bool :=
  (List.range 64).all checkWidthTypeCheckPrinterAgreement

end StrataGenerators.PrinterCoverage
