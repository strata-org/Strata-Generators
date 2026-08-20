import StrataGenerators.ProgramGen
import StrataGenerators.FunctionHasTypeAGen.Roundtrip

/-!
# The printer expresses what the language admits

`Core.formatProgram` does **not** fail when it cannot express something. Via
`formatWithDDM` (`ASTtoCST.lean` → `FormatCore.lean`) it appends

```
-- Errors encountered during conversion:
```

to its output and substitutes a placeholder. Two placeholders are especially
dangerous because they are *syntactically valid*:

- `unknownTypeVar = "$__unknown_type"` (`FormatCore.lean`) — an unprintable
  type becomes a **type variable**, so the result can round-trip "successfully"
  while denoting a different program;
- `mkGenericCall` (`FormatCore.lean`) renders an unknown operator as a call
  to a fresh free variable, so an unprintable *operator* becomes an ordinary
  application.

So the oracle here is not "the output re-parses" but **"the printer logged no
conversion error"**. That is strictly stronger, far better localised (it names the
offending construct instead of reporting "parse error at 2:2"), and needs no
parser at all.

## Measured yield

The oracle fires on **~50%** of programs drawn from the shared `Arbitrary
GenProgram` wrapper (198/400, at its 2–5 declarations), and on **~86%** at
`numDecls = 6` (343/400) — the rate rises with declaration count because each
declaration is an independent chance to reach an unprintable construct, so the
figure to compare a run against is whichever bound that run sampled at. Errors
span **seven** distinct sites: `lmonoTyToCoreType`, `lconstToExpr`,
`handleUnaryOps`, `handleBitvecBinaryOps`, `lopToExpr`, `extractTriggerPatterns`,
`funcDeclToStatement`.

Nearly every erroring program also fails to re-parse (193 of 198; 341 of 343) — so
the existing round-trip property is *already* red on those, it just cannot say why.
The handful that re-parse cleanly are the interesting ones: there a placeholder
silently produced a **different program**, which is exactly what a string
round-trip structurally cannot catch, and the reason this property is worth having
alongside `function: pretty-print/parse round-trip` rather than instead of it.

## Two confirmed gaps at *supported* widths

Both are pinned by the unit-style checks below, and neither is the known
non-power-of-2 story:

1. **`bv128` literals are unprintable.** The grammar has `bv128Lit`
   (`Grammar.lean`) and the factory registers `bv128ToIntFunc`
   (`Factory.lean`), but `lconstToExpr` logs `unsupported bitvec width: 128`.

2. **The whole `Bv↔Int` conversion family is unprintable at *every* width.**
   `Factory.lean` registers `Bv{w}.ToInt` / `Bv{w}.ToUInt` /
   `Int.ToBv{w}` for `w ∈ {1, 8, 16, 32, 64, 128}`. There is **no grammar
   production and no printer case for any of them** — `handleUnaryOps` falls
   through to `mkGenericCall` (`FormatCore.lean`). So these operators can be
   constructed and typechecked but not printed. This is a systematic hole rather
   than a missing case, which is what makes it the more interesting of the two.

## The synthetic-operator caveat, now vacuous

This section used to explain a caveat: `corePolyOps` was a hand-written list that
held synthetic combinators (`id`, `churchTrue`, `churchFalse`) which are
deliberately *not* Strata operators, so the printer was right to reject them and
counting them would have failed this property for our own reasons.

That caveat no longer applies. `coreMonoOps` and `corePolyOps` are both **derived
from `Core.Factory`** (`coreMonoOps_eq_factoryOps`,
`corePolyOps_subset_factoryPolyOps`, plus the `#guard` that nothing is missing),
so every operator a generated term can apply is a real Strata operator. No
synthetic name can reach the printer.

`syntheticOps` and the `strataErrorLines` filter are kept as a no-op safety net,
so that re-introducing a synthetic entry cannot silently turn into a spurious
Strata defect. The filter is on the
*error line*, not on the program, so a program containing a synthetic op still
has its other errors scored.
-/

namespace StrataGenerators.PrinterCoverage

open Lambda Core Imperative Strata Strata.CoreDDM
open StrataGenerators

-- ── Detecting conversion errors ───────────────────────────────────────────

/-- The marker `formatWithDDM` appends when `finalCtx.errors` is non-empty
    (`FormatCore.lean`). Matching on this rather than on any particular
    message keeps the oracle robust to Strata rewording an individual error. -/
def errorMarker : String := "Errors encountered during conversion"

/-- The per-error line prefix (`ASTToCSTError.toString`, `FormatCore.lean`). -/
def errorLinePrefix : String := "Unsupported construct in "

/-- The program text the printer claims to have produced, with the appended error
    block removed. This is what a consumer would feed to the parser. -/
def printedText (s : String) : String :=
  (s.splitOn s!"\n\n-- {errorMarker}:").headD s

/-- Operator names that would be ours rather than Strata's. **Now vacuous**: both
    operator vocabularies are derived from `Core.Factory`, so no generated term can
    mention a name Strata does not define. Retained as a safety net — if a synthetic
    entry is ever added back, the printer is *correct* to reject it and it must not be
    scored as a Strata defect. -/
def syntheticOps : List String := ["id", "churchTrue", "churchFalse"]

/-- The conversion-error lines of a formatted program, excluding those caused by
    our own synthetic operators. -/
def strataErrorLines (s : String) : List String :=
  (s.splitOn "\n").filter fun line =>
    line.startsWith errorLinePrefix
      && !(syntheticOps.any fun op => line.endsWith s!": {op}")

/-- The printer function an error line blames, from a line of the shape
    `Unsupported construct in {site}: {detail}` (`ASTToCSTError.toString`). Used to
    group errors by *site* rather than by full message: `lconstToExpr` failing on
    width 3 and on width 129 are one gap, not two. -/
def errorSite (line : String) : String :=
  let afterPrefix :=
    if line.startsWith errorLinePrefix then (line.drop errorLinePrefix.length).toString
    else line
  ((afterPrefix.splitOn ":").headD afterPrefix).trimAscii.toString

/-- **The printer-expressiveness oracle.** `true` when formatting `prog` logs no
    conversion error attributable to Strata. -/
def printsWithoutError (prog : Program) : Bool :=
  (strataErrorLines (Core.formatProgram prog).pretty).isEmpty

-- ── The whole-program property ────────────────────────────────────────────

/-- **The printer can express every construct the generator produces.** Every
    declaration here is well-typed by construction (`genProgram` maintains that
    invariant and the harness re-checks it), so an inexpressible construct is a
    printer gap, not an invalid input. -/
def checkProgramPrintsWithoutError (prog : Program) : Bool :=
  printsWithoutError prog

/-- The distinct Strata-attributable error messages from formatting `prog`, for
    the diagnostic that reports *which* constructs are unprintable rather than
    merely how many programs are affected. -/
def programErrorLines (prog : Program) : List String :=
  (strataErrorLines (Core.formatProgram prog).pretty).dedup

-- ── Targeted witnesses: the two confirmed gaps ────────────────────────────
-- These are unit-style rather than generated, deliberately. Both gaps are about
-- a *specific* operator or width, so a constructed witness is a sharper and more
-- stable statement of the defect than "some generated program hit it" — and it
-- keeps the report reproducible if the generator's distribution shifts.

/-- The bitvector widths Strata's factory registers (`Factory.lean`).
    Note `128` is present here but absent from the printer's `lconstToExpr` and
    from `bvTypeOfWidth`'s enumeration — that mismatch *is* finding (1). -/
def factoryBvWidths : List Nat := [1, 8, 16, 32, 64, 128]

/-- Format a single expression and report whether it printed cleanly.
    `Core.formatExprs` runs the same `lexprToExpr` conversion `formatProgram`
    does, so a gap found here is a gap in the real printer. -/
def exprPrintsCleanly (e : Expression.Expr) : Bool :=
  let s := (Core.formatExprs [e]).pretty
  -- `formatExprs` uses its own shorter error prefix (`-- Errors: `), so check
  -- both markers rather than relying on the program-level one.
  !(s.splitOn "-- Errors:").length > 1 && (strataErrorLines s).isEmpty

/-- A bitvector literal of the given width, as an annotated constant. -/
def bvLit (w : Nat) : Expression.Expr :=
  .const () (.bitvecConst w (BitVec.ofNat w 1))

/-- Does a `bitvec w` literal print without a conversion error? The per-width
    check behind `checkBv128LiteralPrints`, named separately so a report can score
    each registered width by the same function the property applies at 128. -/
def checkBvLitPrints (w : Nat) : Bool := exprPrintsCleanly (bvLit w)

/-- **A `bitvec 128` literal prints.** It is registered by the factory and has a
    grammar production (`bv128Lit`, `Grammar.lean`). Every *other* registered width
    prints, which is what would make 128 an omission rather than a design
    boundary. -/
def checkBv128LiteralPrints : Bool := checkBvLitPrints 128

/-- The registered widths whose literals do not print. -/
def unprintableBvLiteralWidths : List Nat :=
  factoryBvWidths.filter (fun w => !checkBvLitPrints w)

/-- The `Bv↔Int` conversion operator names the factory registers at width `w`. -/
def bvIntConversionOps (w : Nat) : List String :=
  [s!"Bv{w}.ToInt", s!"Bv{w}.ToUInt", s!"Int.ToBv{w}"]

/-- Every registered `Bv↔Int` conversion operator name. -/
def allBvIntConversionOps : List String :=
  factoryBvWidths.flatMap bvIntConversionOps

/-- An application of a named unary operator to a placeholder argument. The
    argument is an `int` literal: `handleUnaryOps` dispatches on the *operator
    name* alone (`FormatCore.lean`), so the argument's type does not affect
    whether the operator is printable. -/
def unaryApp (name : String) : Expression.Expr :=
  .app () (.op () ⟨name, ()⟩ none) (.const () (.intConst 1))

/-- Does an application of the named operator print without a conversion error?
    The per-operator check behind `checkBvIntConversionsPrint`, named separately so
    a report can score each of the eighteen operators individually — an aggregate
    `18/18` says a family is missing, but only the per-operator verdicts show that
    it is *every* width and *every* direction. -/
def checkBvIntConversionPrints (op : String) : Bool := exprPrintsCleanly (unaryApp op)

/-- **Every registered `Bv↔Int` conversion operator is printable, at every width.**
    `handleUnaryOps` enumerates `.Not`, `.Neg`, `SafeNeg`, the overflow predicates
    and nine `bvExtract` shapes; anything it has no arm for falls through to
    `mkGenericCall`. -/
def checkBvIntConversionsPrint : Bool :=
  allBvIntConversionOps.all checkBvIntConversionPrints

/-- The `Bv↔Int` conversion operators that do not print. -/
def unprintableBvIntConversions : List String :=
  allBvIntConversionOps.filter (fun op => !checkBvIntConversionPrints op)

-- ── Bitvector widths: typechecker vs printer ──────────────────────────────
/-!
## The width divergence

Two questions motivate this section: does the Strata typechecker *accept*
bitvectors of non-power-of-2 width, and if so do round-trip properties fail on
them?

**Both answers are yes, and the interesting finding is the divergence itself.**
`Function.typeCheck` accepts `bitvec w` for **every** `w` tested (0–199), because
`LMonoTy.bitvec` is unconstrained in the AST and the known-type entry
is the polymorphic `t[∀n. bitvec n]`. The printer supports **five** widths.

### One correction to the usual framing

The usual account says round-trips fail because "the DDM expects bit-vector widths
to be a power of 2". That predicate is **wrong**, and measurably so: `bitvec 2`,
`bitvec 4` and `bitvec 128` are all powers of two and all fail to print. Scanning `0..199`
exhaustively, the widths that print cleanly are exactly

```
[1, 8, 16, 32, 64]
```

which is not "the powers of two" but *the five arms hardcoded in the printer* —
`lmonoTyToCoreType` for types, `lconstToExpr` for literals, and
`bvTypeOfWidth` for operator type
arguments. So the correct statement of the defect is "the printer supports a
hardcoded five-element set of widths, while the typechecker and the AST admit
every width", and the fix is not a power-of-2 guard.

`bitvec 128` deserves separate mention and gets its own property above: it is
factory-registered *and* has a grammar production, so it is the one width where
the printer is out of step with the rest of Strata rather than merely narrow.

### Two distinct failure modes, and why the type case is the dangerous one

`bvTypeOfWidth` does **not** emit a placeholder type — it logs an error and
returns `.bv64` (`FormatCore.lean`). So an operator at an unsupported width is
printed as though it were a **64-bit** operator: a silent width change, not a
visible hole.

`lmonoTyToCoreType` substitutes `$__unknown_type`, which is a *type variable*, so
`function f (x : bitvec 3) : bitvec 3` prints as
`function f (x : $__unknown_type) : $__unknown_type`. Checked: that text fails to
re-parse (`$__unknown_type` is not a declared type argument), and it still fails
in a host function that *already* has a type parameter — so today this shows up as
a round-trip parse failure rather than as a silently-different program. That is
luck rather than design: the placeholder is chosen to be syntactically valid, and
the `.bv64` fallback shows the same code path is willing to substitute a
*plausible* wrong answer.
-/

/-- The bitvector widths the printer actually supports, determined by scanning
    `0..199` rather than assumed: the five arms hardcoded in
    `lmonoTyToCoreType` / `lconstToExpr` / `bvTypeOfWidth`.

    Named `printable` rather than `registered` deliberately — it is **not** the
    factory's registered set (`SmtEval.registeredBvWidths` plus `128`), and it is
    **not** the powers of two. -/
def printableBvWidths : List Nat := [1, 8, 16, 32, 64]

/-- A one-input identity function at `bitvec w`, the minimal host for a width in
    *type* position (both an input type and the output type). -/
def bvIdentityFunc (w : Nat) : Function :=
  { name := ⟨"f", ()⟩, typeArgs := [], inputs := [("x", .bitvec w)],
    output := .bitvec w, body := some (.fvar () ⟨"x", ()⟩ (some (.bitvec w))) }

/-- Does `Function.typeCheck` accept the identity function at `bitvec w`?
    Measured `true` for every `w ∈ 0..199`. -/
def widthTypeChecks (w : Nat) : Bool :=
  match Function.typeCheck funcCheckContext TEnv.default (bvIdentityFunc w) with
  | .ok _ => true
  | .error _ => false

/-- Does the identity function at `bitvec w` print without a conversion error? -/
def widthPrintsCleanly (w : Nat) : Bool :=
  (strataErrorLines (formatFuncAsProgram (bvIdentityFunc w))).isEmpty

/-- **The width-agreement property.** Every width the *typechecker*
    accepts should be one the *printer* can express: a program Strata admits should be a
    program Strata can write down.

    Stated as an implication (`typechecks → prints`) rather than as an equality
    with `printableBvWidths`, so it is a claim about Strata's own consistency
    rather than a restatement of the printer's arm list.

    Quantified over a width rather than over a generated function because the
    property is one *of the width*: `genLMonoTyBitvec` draws from
    `Nat.arbitrary` (`HasTypeAGen/Core.lean`), which samples every width, so the
    whole-program property above already covers this space —
    but a generated hit does not say *which* width is at fault. This does. -/
def checkWidthTypeCheckPrinterAgreement (w : Nat) : Bool :=
  !widthTypeChecks w || widthPrintsCleanly w

/-- Widths in `0..bound` that the typechecker accepts but the printer cannot
    express, for the diagnostic. -/
def divergentBvWidths (bound : Nat) : List Nat :=
  (List.range bound).filter (fun w => !checkWidthTypeCheckPrinterAgreement w)

/-- **The width-agreement claim as one closed `Bool`**, over `0..63`
    (enough to include several powers of two and both parities, while staying
    cheap: each width runs `Function.typeCheck` plus a format). -/
def checkAllWidthsAgree : Bool :=
  (List.range 64).all checkWidthTypeCheckPrinterAgreement

end StrataGenerators.PrinterCoverage
