import StrataGenerators.PrimitiveGens
import Strata.DL.SMT.DDMTransform.Translate
import Strata.DL.SMT.Term

open Strata.SMT StrataGenerators.PrimitiveGens

/-!
# The SMT-LIB escape function for a string literal

This file holds a property-based test for a defect in the escape function. A Core
string literal that contains a non-ASCII codepoint goes into the SMT-LIB query as
**raw UTF-8 bytes**, and not as a `\u{...}` escape. cvc5 rejects such a query
outright, with `Parse Error: Non-printable character in string literal`. z3
accepts the query, but it reads each byte as a separate character. Thus
`str.len "é"` is `2` for z3, and the interpreted `Str.Length` of Strata, which is
`Int.ofNat s.length` and counts *codepoints*, gives `1`.

**This property FAILS until somebody corrects the escape function.** It fails
honestly: it pins a true defect, and it does not mask one. This is the same
convention as the four `proc:` properties that `Properties.lean` documents. After
the correction, the property must turn green with no change to this file, which is
what makes it a regression test.

## Why the test has this shape

Three things make this test better than a test that drives a solver:

1. **It needs no solver.** The root cause is `escapeSMTStringLit`
   (`StrataDDM/Util/String.lean`), which is a pure `String → String`. A check of
   its output directly puts the property in the *default* suite, and not behind
   `--smt`. Thus a machine without cvc5 cannot skip it. A property that does not
   run, and that gives no message about it, is how this defect stayed open for so
   long.
2. **The oracle is exact, and not an approximation.** SMT-LIB 2.6+ requires a
   string literal to hold only printable ASCII, and it requires every other
   codepoint as a `\u{...}` escape. Thus "each character of the emitted literal is
   in `[0x20, 0x7E]`" is the specification itself. `escapedIsPrintableAscii` below
   is that predicate.
3. **It puts the blame in one place.** A test at the solver level reports "cvc5
   errored", which can be any of a dozen problems in the encoder. This test
   reports the codepoint that causes the failure.

## What the generator contributes

The property is non-vacuous only because `genInterestingString`
(`StrataGenerators.PrimitiveGens`) draws a non-ASCII codepoint. `String.arbitrary`
of Basalt gives alphanumeric characters only. On that generator, this property
passes on each input while the defect stays hidden. Therefore the property draws
from the *same* generator that the `strConst` leaf of the expression generator
uses. Thus a verdict here is evidence about the true generation path, and not
about a hand-picked pool.
-/

namespace StrataGenerators.SmtStringEscaping

/-- The printable-ASCII range of SMT-LIB 2.6+: `0x20`, the space, through `0x7E`,
    the character `~`. A string literal that conforms holds only these characters.
    Every other codepoint must appear as a `\u{...}` escape. -/
def isPrintableAscii (c : Char) : Bool := c ≥ ' ' && c ≤ '~'

/-- The specification that `escapeSMTStringLit` must satisfy: the SMT-LIB literal
    for `s` holds only printable ASCII.

    This predicate uses `Strata.SMTDDM.termToString`, which is the *true*
    serializer for each `Term` on its way to the solver, because
    `Solver.termToSMTString` calls it. The predicate does not use
    `escapeSMTStringLit` directly. Thus the property tests the real path, and that
    path includes the format option `smtStringEscaping := true`, which selects the
    SMT escape function instead of the one for the Strata source. -/
def escapedIsPrintableAscii (s : String) : Bool :=
  match Strata.SMTDDM.termToString (Term.string s) with
  | .ok out => out.toList.all isPrintableAscii
  | .error _ => false

/-- The codepoints in `s` that cause a failure, which are the ones that go into
    the emitted literal without an escape. The list is empty if and only if the
    output for `s` is correct. The harness reports this list on a failure, so that
    the counterexample names the codepoint and not only the string. -/
def offendingCodepoints (s : String) : List Nat :=
  match Strata.SMTDDM.termToString (Term.string s) with
  | .ok out => (out.toList.filter (fun c => !isPrintableAscii c)).map Char.toNat |>.eraseDups
  | .error _ => []

-- ── Machine-checked reproducers ───────────────────────────────────────
--
-- These pin the *specific* cases of the defect, independently of what the random
-- generator draws. `#guard` makes the build fail, so each case is an `example`
-- with `decide` on the value that the code gives now, which is the incorrect one.
-- Each example records the current behaviour, and each example itself breaks after
-- a correction. Then it shows that this file needs an update together with the
-- property.

/-- The escape function is correct on ASCII. This is the path that works, and the
    example keeps it, so that a regression in it is also caught. -/
example : escapedIsPrintableAscii "abc" = true := by native_decide

/-- The escape function is correct on an ASCII control character, which it gives
    as `\u{0}`. This is why a test with a control character does not find the
    defect: `useXHex` covers that range. -/
example : escapedIsPrintableAscii "\x00" = true := by native_decide

/-- U+00AD, the soft hyphen, gets an escape. It is the one special case of
    `useXHex` above `0xA1`. -/
example : escapedIsPrintableAscii "­" = true := by native_decide

/-- **The Latin-1 case.** U+00E9, which is `é`, goes out raw. `useXHex` is false
    for each codepoint of U+00A1 or more, so the escape function stops exactly
    here. -/
example : escapedIsPrintableAscii "é" = false := by native_decide

/-- **The astral-plane case.** U+1D54A, which is `𝕊`, goes out raw as 4 UTF-8
    bytes. On this input, z3 reports `str.len = 4`. -/
example : escapedIsPrintableAscii "𝕊" = false := by native_decide

/-- The `useXHex` boundary is off by one codepoint. U+00A0 gets an escape, and
    U+00A1 does not. This is the sharpest statement of the root cause: the guard is
    a predicate for *8-bit* printability, and the escape function uses it for full
    Unicode. -/
example : escapedIsPrintableAscii " " = true := by native_decide
example : escapedIsPrintableAscii "¡" = false := by native_decide

-- ── The property ──────────────────────────────────────────────────────

/-- **Property: each generated string literal goes to SMT-LIB as printable
    ASCII.**

    The property runs over strings from `genInterestingString`, which is the exact
    generator that the `strConst` leaf of the expression generator uses. It
    serializes each string with `Strata.SMTDDM.termToString`, the real path to the
    solver.

    The result is `(success, passed, attempted, message)` for the `individualIO` or
    `runIOProperty` node of the harness. On a failure, the message names the
    codepoints that cause the first counterexample. It also gives the number of
    sampled strings with the defect. That rate is important, because it measures
    how much of the test surface for strings the defect makes invalid. -/
def escapingAction (numTrials : Nat) : IO (Bool × Nat × Nat × Option String) := do
  let total := max 1 (min numTrials 400)
  let mut passed := 0
  let mut failed := 0
  let mut firstBad : Option (String × List Nat) := none
  for _ in List.range total do
    -- Draw from the same generator that the `strConst` leaf of the expression
    -- generator uses. Thus a pass here is evidence about the real generation path.
    let s ← genInterestingString (G := IO)
    if escapedIsPrintableAscii s then
      passed := passed + 1
    else
      failed := failed + 1
      if firstBad.isNone then
        firstBad := some (s, offendingCodepoints s)
  if failed == 0 then
    pure (true, passed, total, none)
  else
    let detail := match firstBad with
      | some (s, cps) =>
        let hex := String.intercalate ", " (cps.map (fun n =>
          s!"U+{(String.ofList (Nat.toDigits 16 n)).toUpper}"))
        s!"first counterexample: {repr s} emitted with unescaped {hex}"
      | none => ""
    pure (false, passed, total,
      some s!"EXPECTED FAILURE: the SMT escape function drops non-ASCII. \
{failed} of {total} generated string literals go out as raw UTF-8. cvc5 rejects \
them, and z3 measures them incorrectly, because `str.len` counts bytes and not \
codepoints. {detail}. This property must turn green after a correction to the \
escape function.")

end StrataGenerators.SmtStringEscaping
