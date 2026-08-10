import Basalt.Gen
import Basalt.IO
import Basalt.Combinators

open RandomChoice

/-!
# Adversarial primitive generators for strings, characters, rationals and bitvectors

These generators supply the constant leaves of the expression generator. They
target the properties about the SMT encoding: bitvector overflow, strings and
UTF-8, and the SMT-LIB escape function.

The default Basalt primitives are too tame to reach the interesting cases:

* `Char.arbitrary` gives only characters that satisfy `Char.isAlphanum`.
  Therefore `String.arbitrary` gives **ASCII alphanumeric strings only**. On such
  a pool, every property about a non-ASCII string literal passes vacuously.
* `Nat.arbitrary` is a geometric distribution. It flips a coin and then
  increments, so its values group near `0`. The signed overflow predicates
  `BitVec.sdivOverflow` and `BitVec.negOverflow` are true **only** at `INT_MIN`.
  A generator whose values group near `0` reaches `INT_MIN` with probability
  about `2^-w`. At `w = 64` it never reaches it.
* `Nat.arbitrary` returns `0` half of the time. A rational with a zero numerator
  is `0`. Therefore a rational that takes its numerator from `Nat.arbitrary` is
  `0` about 46% of the time. Read the section on rationals below.

Do not use these generators as drop-in replacements for the Basalt primitives
elsewhere in the suite. They are biased on purpose, and a biased generator is a
poor input for the properties about types and round trips, because those
properties want broad coverage. These generators supply the constant leaves
`genStrConst`, `genRealConst` and `genBitvecConst` in `HasTypeAGen/Core.lean`,
which is what the SMT-agreement property exercises.

Each generator here is **complete**: its support is the whole type. Therefore
these generators narrow nothing that the completeness proofs quantify over.
Where a generator is biased, an explicit branch with a lower weight carries
completeness. These branches are the geometric tail of `genRat` and the uniform
fallback of `genBiasedBitVec`. A `*_support_set` lemma in `HasTypeAGen.lean`
witnesses each one.

## Shape constraint (do not "simplify" these)

The support proofs in `HasTypeAGen.lean` and `HasTypeAGenOpsConsistent.lean`
destructure the constant leaves as one `bind` and then one `pure`:

```lean
simp only [genStrConst, ..., SetGen.Set.mem_bind, SetGen.Set.mem_pure, ...] at he
· obtain ⟨s, _, rfl⟩ := he; exact .const
```

The proofs discard the membership hypothesis for the inner value generator
(`_`), so they do not depend on which generator supplies the value. But they do
depend on the outer `do let v ← gen; pure (.const … v)` shape. Keep that shape.
-/

namespace StrataGenerators.PrimitiveGens

/-- An unbounded geometric `Nat` generator, a `pick` between `0` and `(· + 1)`.
    Only the completeness tail of `genRat` uses it. Every other branch in this
    file samples uniformly with `chooseNat`.

    This file holds its own copy of the generator instead of an import, for the
    same reason that `HasTypeAGen/Core.lean` holds a copy: `BasaltExamples.ArbNat`
    pulls in the full `Basalt` umbrella, and thus Mathlib's `List.dedup`, which
    collides with Strata's. `HasTypeAGen/Core.lean` imports this file, so this
    file cannot depend on it. This copy is definitionally the same as the upstream
    generator. -/
def natArbGeom [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← natArbGeom
      pure (n + 1))
partial_fixpoint

/-! ## Non-ASCII characters and strings -/

/-- Codepoints that straddle each boundary that is related to the SMT-LIB escape
    function, and to the difference between a codepoint, a byte and a character.

    The groups below show *why* each codepoint is in the pool. The choice of pool
    is the full value of this generator.

    1. **ASCII printable**: the baseline that always worked.
    2. **ASCII control**: `escapeSMTStringLit` gives these a `\u{...}` escape.
       This is the correct path. The pool keeps them, so a regression there is
       also caught.
    3. **`"` and `\`**: SMT-LIB doubles `"`. SMT-LIB 2.6+ keeps `\` literal, but
       the Strata source syntax gives it an escape. This is the one place where
       the two escape functions truly disagree.
    4. **The `useXHex` boundary**: U+00A0 gets an escape, U+00A1 is the first
       codepoint that does not, and U+00AD is the soft hyphen special case. These
       three pin the exact off-by-one in the root cause.
    5. **Latin-1 and BMP, 2 to 3 UTF-8 bytes**: `é`, Greek, Cyrillic, CJK, and a
       right-to-left character. For these, `String.length`, which counts
       codepoints, is not equal to `utf8ByteSize`. This is the case that
       discriminates for each `Str.*` property about length or index.
    6. **Astral plane, 4 UTF-8 bytes**: `𝕊` and an emoji.
    7. **Above the SMT-LIB alphabet**: SMT-LIB strings range over the codepoints
       `0x0` to `0x2FFFF`. U+30000 and U+10FFFF are outside that range, so SMT-LIB
       cannot represent them at all. The pool includes them on purpose: this is an
       open question that needs a decision, not a repair.

    The pool does *not* include the surrogates `0xD800` to `0xDFFF`. They are not
    valid Lean `Char`s, and `Char.ofNat` folds them silently to a replacement
    character. Then the pool would tell a lie about its contents. -/
def interestingCodepoints : List Nat :=
  -- 1. ASCII printable
  [ 0x41, 0x7A, 0x30, 0x20, 0x7E
  -- 2. ASCII control (escaped path)
  , 0x00, 0x01, 0x09, 0x0A, 0x0D, 0x1F
  -- 3. Quote and backslash
  , 0x22, 0x5C
  -- 4. The `useXHex` boundary
  , 0x7F, 0xA0, 0xA1, 0xAD
  -- 5. Latin-1 / BMP (2–3 UTF-8 bytes)
  , 0xE9      -- é   LATIN SMALL LETTER E WITH ACUTE
  , 0xFF      -- ÿ
  , 0x3B1     -- α   GREEK SMALL LETTER ALPHA
  , 0x416     -- Ж   CYRILLIC CAPITAL LETTER ZHE
  , 0x5D0     -- א   HEBREW LETTER ALEF (RTL)
  , 0x4E2D    -- 中  CJK
  , 0xFFFD    -- �   REPLACEMENT CHARACTER
  -- 6. Astral plane (4 UTF-8 bytes)
  , 0x1D54A   -- 𝕊   MATHEMATICAL DOUBLE-STRUCK CAPITAL S
  , 0x1F600   -- 😀  EMOJI
  -- 7. Above the SMT-LIB string alphabet (0x0–0x2FFFF)
  , 0x30000
  , 0x10FFFF ]

theorem interestingCodepoints_ne_nil : interestingCodepoints ≠ [] := by
  unfold interestingCodepoints; simp

/-- Each codepoint in `interestingCodepoints` is a valid Lean `Char`. Thus
    `Char.ofNat` is faithful on the whole pool, and it folds no entry to the
    replacement character. Without this theorem, the pool can claim coverage that
    it does not have. Read the note about surrogates on
    `interestingCodepoints`. -/
theorem interestingCodepoints_isValid :
    ∀ n ∈ interestingCodepoints, (Char.ofNat n).toNat = n := by
  unfold interestingCodepoints; decide

/-- `interestingCodepoints` as `Char`s. The generator draws from this list, and
    not from the `Nat` list. Thus its support is literally "membership in a list
    of `Char`", and `mem_support_elements_iff` applies directly. This mirrors how
    `Char_arbitrary_support_set` uses `alphanumChars`. -/
def interestingChars : List Char := interestingCodepoints.map Char.ofNat

theorem interestingChars_ne_nil : interestingChars ≠ [] := by
  unfold interestingChars interestingCodepoints; simp

/-- A character from `interestingChars`: uniformly one of the codepoints above
    that straddle a boundary. This generator is not uniform over Unicode, on
    purpose. Its function is to hit the boundaries frequently, and not to sample
    the space.

    Compare `Char.arbitrary` from Basalt, which gives only characters that satisfy
    `Char.isAlphanum` and therefore never goes outside printable ASCII. -/
def genInterestingChar [Gen G] : G Char :=
  elements interestingChars interestingChars_ne_nil

/-- The non-ASCII members of `interestingChars`, with a codepoint of U+0080 or
    more. -/
def nonAsciiChars : List Char := interestingChars.filter (fun c => c.toNat ≥ 0x80)

theorem nonAsciiChars_ne_nil : nonAsciiChars ≠ [] := by
  unfold nonAsciiChars interestingChars interestingCodepoints; decide

/-- Each entry of `nonAsciiChars` is truly non-ASCII. `genNonAsciiString` needs
    this guarantee to be non-vacuous. -/
theorem nonAsciiChars_are_nonAscii : ∀ c ∈ nonAsciiChars, c.toNat ≥ 0x80 := by
  unfold nonAsciiChars; decide

/-- A character that is guaranteed to be **non-ASCII**, with a codepoint of
    U+0080 or more. Use it for a test that must not pass vacuously on an ASCII
    draw. -/
def genNonAsciiChar [Gen G] : G Char :=
  elements nonAsciiChars nonAsciiChars_ne_nil

/-- The upper limit on the length that the primary branch of
    `genInterestingString` draws.

    The limit is small on purpose. Above a few characters, a longer string mostly
    stresses how the printer handles digits and escapes. It does not stress the
    semantics of codepoints, bytes and characters, which is what these properties
    are about. Each additional character also costs the term size of one solver
    query. -/
def strMaxLen : Nat := 8

/-- A string over `genInterestingChar`, biased toward **short but not empty**.

    The generator mixes ASCII and non-ASCII characters in one string, which is
    important. A string that is *partly* multi-byte is where a confusion between a
    codepoint index and a byte index in `Str.At`, `Str.Substr` or `Str.IndexOf`
    becomes visible. A string that is fully ASCII, or fully astral, can agree by
    accident.

    **Why not plain `listOf`.** `listOf` recurses through `pick`, so it stops
    immediately half of the time. Its own docstring says that it "produces the
    empty list 50% of the time, so for production generators, you should consider
    using other combinators" (`Basalt/Combinators.lean`). Measured on this
    character pool, **51% of the draws were `""`**. That result halves the
    effective yield of each string property, because an empty string exercises no
    codepoint at all. It also holds the non-ASCII rate down to 32%,
    because each empty draw is trivially ASCII only.

    Therefore the primary branch, with weight 7, draws a length uniformly from
    `[1, strMaxLen]` and then fills it. The result is about 79% non-ASCII, with a
    mean length of 4.

    The branch with weight 1 is plain `listOf`, and it keeps the generator
    **complete**. The primary branch alone limits the length to `strMaxLen`. That
    limit falsifies `genInterestingString_support_set` and forces a bound on
    length into `AllTypesSimple.strConst`. This branch has the same shape, bias
    plus a completeness tail, as `genRat` and `genBiasedBitVec`.

    The tail also keeps `""` reachable at about 5%. This is wanted, and not merely
    tolerated: the empty string is a true edge case. Examples are `Str.Length "" =
    0`, the two-sided identity of `Str.Concat`, and an out-of-range `str.substr`.
    This is why the generator does not use `nonEmptyListOf`, which drives the rate
    of `""` to 0%. -/
def genInterestingString [Gen G] : G String :=
  frequency
    [ (7, fun () => do
        let k ← chooseNat 1 strMaxLen (by unfold strMaxLen; omega)
        String.ofList <$> vectorOf k genInterestingChar)
    , (1, fun () => String.ofList <$> listOf genInterestingChar) ]
    (by simp)

/-- A string that contains **one or more** non-ASCII characters.

    The generator builds `prefix ++ [c] ++ suffix`, where `c` is non-ASCII. Thus
    the guarantee is structural, and not probabilistic. A test run gave 300 such
    strings out of 300 draws. Use this generator where an ASCII-only draw makes
    the property vacuous. One example is the `Str.Length` differential.

    The two affixes use plain `listOf`, so they can be empty. This is correct
    here, because the guarantee on the non-ASCII character is independent of
    them. -/
def genNonAsciiString [Gen G] : G String := do
  let pre ← listOf genInterestingChar
  let c ← genNonAsciiChar
  let suf ← listOf genInterestingChar
  pure (String.ofList (pre ++ (c :: suf)))

/-! ## Rationals

A generator that draws both the numerator and the denominator from
`Nat.arbitrary`, and then assembles `↑num / (↑den + 1)` by hand, has two
problems:

1. **Almost half of the output is zero.** `Nat.arbitrary` flips a coin and then
   increments, so it returns `0` with probability `1/2`. A numerator of `0` makes
   the whole rational `0`. Measured over 400 draws: **46% zeros**. A generator
   that is one coin flip away from `0` hardly tests real arithmetic. Also, `0` is
   the one value that makes `Real.Div` degenerate, so `0` crowds out the
   interesting cases while the output looks varied.
2. **Hand-made construction.** The expression `↑num / (↑den + 1)` depends on the
   division of `Rat` to normalize, and the `+ 1` is a manual guard against a zero
   denominator. `mkRat` is the smart constructor from the standard library. It
   takes an `Int` and a `Nat`, it folds a zero denominator to `0` itself, and it
   normalizes internally. Normalization reduces the value to lowest terms and puts
   the sign on the numerator.

`genRat` below prevents both problems.
-/

/-- The limit on magnitude for the uniform branch of `genRat`. Numerators range
    over `[-ratBound, ratBound]`, and denominators range over
    `[1, ratBound + 1]`. Thus the values span about `±ratBound`, with denominators
    up to `ratBound + 1`.

    The limit is modest on purpose. The printer emits an SMT-LIB real literal as a
    decimal, or as `frac{num, den}` when the decimal does not terminate. Read
    `Core.FracLit`. A large numerator mostly stresses how the printer handles
    digits. It does not stress the arithmetic semantics that this property
    tests. -/
def ratBound : Nat := 32

/-- A rational that `mkRat`, the smart constructor from the standard library,
    builds. The generator is biased toward a **non-zero** value.

    The uniform branch draws `num` uniformly from `[-ratBound, ratBound]`, and
    `den` uniformly from `[1, ratBound + 1]`, with `chooseNat`. Thus `0` appears
    in that branch with probability `1/(2·ratBound + 1)`, which is about 1.5%.
    Denominators start at `1`, and not at `0`. Therefore the fold-to-`0` path in
    `mkRat` for a zero denominator is never the reason that a draw is zero.

    **Measured overall: about 9% zeros.** The geometric completeness tail, and not
    the uniform branch, is the main source. The prediction is about 7.6% in total:
    `7/8 · 1/65 ≈ 1.4%` from the uniform branch, plus `1/8 · 1/2 ≈ 6.3%` from the
    tail, whose `natArbGeom` numerator is `0` half of the time. If 9% is still too
    high, give the tail a different weight. Do not make `ratBound` larger. You
    cannot remove the tail without a loss of completeness.

    The branch with weight 1 keeps the generator **complete**. `mkRat`, together
    with an unbounded draw of a numerator and a denominator, can give *any*
    rational, by `Rat.mkRat_self`. Thus the support is all of `Rat`, and not only
    the bounded window. `genBiasedBitVec` has the same structure, for the same
    reason.

    `mkRat` also keeps each generated value in normal form. Thus `1/2` and `2/4`
    are one term, and not two terms that are syntactically different but equal.
    This is important for each property that compares terms structurally. -/
def genRat [Gen G] : G Rat :=
  frequency
    [ (7, fun () => do
        -- `num - ratBound` shifts `[0, 2·ratBound]` to `[-ratBound, ratBound]`,
        -- so negatives are as likely as positives without a separate sign draw.
        let num ← chooseNat 0 (2 * ratBound) (by omega)
        let den ← chooseNat 1 (ratBound + 1) (by omega)
        pure (mkRat ((num : Int) - (ratBound : Int)) den))
    , (1, fun () => do
        -- Unbounded tail, for completeness. It is geometric, and therefore its
        -- mass is near zero. This is correct: the function of this branch is to
        -- make the support total, and not to be the common case. It draws both
        -- signs. Without both signs, no *negative* rational outside the bounded
        -- window is reachable, and the generator is then not complete.
        let n ← natArbGeom
        let d ← natArbGeom
        pick (fun () => pure (mkRat (n : Int) d))
             (fun () => pure (mkRat (-(n : Int)) d))) ]
    (by simp)

/-! ## Boundary-biased bitvectors

`Nat.arbitrary` flips a coin and then increments, so it is a geometric
distribution. A bitvector generator that draws from it gives values that group
near `0`. But each interesting bitvector property lives at a boundary:

| Predicate | True only at |
| --- | --- |
| `BitVec.negOverflow` | `x = INT_MIN` |
| `BitVec.sdivOverflow` | `x = INT_MIN ∧ y = -1` |
| `BitVec.saddOverflow` | near `±INT_MAX` |
| `BitVec.umulOverflow` | near `⌈√(2^w)⌉`, which is a power of two |

Therefore the pool holds the boundaries themselves. It also holds the powers of
two and their neighbours, `2^k ± 1`, to catch an off-by-one in the arithmetic on
`w-1` that `BitVec.intMin` and `BitVec.intMax` do in `Nat`.
-/

/-- The boundary values for width `w`, as `BitVec w` values. The [bitvector
    API](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/#BitVec-api)
    of the Lean standard library builds them, and not a hand-made `Nat` bit
    pattern.

    The standard library constructors make this list *self-evidently* the correct
    one. `BitVec.intMin` is by definition the value that `BitVec.negOverflow`
    tests for. Thus the pool provably holds the sole witness. It does not hold a
    `Nat` expression that the reader must check for equality. The constructors
    also remove the need to reason about truncation, because each entry is already
    a `BitVec w`. There is no step with `BitVec.ofNat` or with modulo `2^w` to get
    wrong.

    The standard library, and not this file, handles a degenerate width. At
    `w = 0`, each entry is the unique `BitVec 0`. At `w = 1`, `intMin` and
    `fill w true`, which is `-1`, collapse to the same value. That collapse is the
    discrepancy in the `SDivOverflow` encoding, so width 1 gets exercise on
    purpose.

    **The pool stays small and independent of the width, to keep the boundaries
    likely.** The pool does not hold `BitVec.twoPow w k` and `twoPow w k ± 1` for
    each `k < w`, although those entries cover the square-root boundary of
    `umulOverflow` and some edge cases of shifts. Those `3w` entries dominate the
    list. Then `P(INT_MIN | boundary branch)` falls to `1/199` at `w = 64`, and it
    gets worse as the width grows. That behaviour is precisely backwards, because
    a wide bitvector is where the uniform fallback is least able to find a
    boundary by chance. Without those entries, the pool holds about 10 entries at
    each width, and `INT_MIN` keeps about `1/10` of the boundary branch. The
    uniform fallback still reaches each power of two. The pool simply gives them
    no priority.

    `BitVec.allOnes w` is absent because it is *definitionally*
    `BitVec.fill w true`. Both are `-1#w`, and
    `simp [BitVec.fill, BitVec.neg_one_eq_allOnes]` proves it. An entry for both
    is a duplicate that looks like additional coverage.

    * `BitVec.zero w`: the only false point of `unegOverflow x = (x != 0)`, and
      the divisor that trips the `y ≠ 0` precondition on `SafeSDiv` and
      `SafeSMod`, and the partial-op guard on `UDiv` and `UMod`. The entry is
      explicit because the fallback is *uniform* and reaches `0` with probability
      `2^-w`.
    * `1`: the multiplicative identity, the smallest shift amount, and the
      `y = 1` counterpart to `y = -1` in `sdivOverflow`.
    * `BitVec.fill w true`: all ones, which is unsigned `MAX`, signed `-1`, and the
      other half of the `sdivOverflow` witness.
    * `BitVec.intMin w`: signed `INT_MIN`, the sole witness of `negOverflow`, and
      half of the `sdivOverflow` witness.
    * `BitVec.intMax w`: signed `INT_MAX`.
    * `intMin ± 1` and `intMax ± 1`: the neighbours of a signed wrap, where
      `saddOverflow` and `ssubOverflow` flip. -/
def bitvecBoundaries (w : Nat) : List (BitVec w) :=
  [ BitVec.zero w, 1
  , BitVec.fill w true
  , BitVec.intMin w, BitVec.intMax w
  , BitVec.intMin w - 1, BitVec.intMin w + 1
  , BitVec.intMax w - 1, BitVec.intMax w + 1 ]

theorem bitvecBoundaries_ne_nil (w : Nat) : bitvecBoundaries w ≠ [] := by
  unfold bitvecBoundaries; simp

/-- `BitVec.intMin` is truly in the pool. It is the sole witness of
    `negOverflow`, and half of the `sdivOverflow` witness. This theorem is
    explicit because the whole function of the bias is to reach that value. If a
    refactor drops it, each signed overflow property goes quietly vacuous instead
    of a failure. -/
theorem intMin_mem_bitvecBoundaries (w : Nat) :
    BitVec.intMin w ∈ bitvecBoundaries w := by
  unfold bitvecBoundaries; simp

/-- `BitVec.intMax`, the `saddOverflow` boundary, is in the pool. -/
theorem intMax_mem_bitvecBoundaries (w : Nat) :
    BitVec.intMax w ∈ bitvecBoundaries w := by
  unfold bitvecBoundaries; simp

/-- `BitVec.allOnes`, signed `-1`, is in the pool. It is the other half of the
    `sdivOverflow` witness. The pool holds it as `BitVec.fill w true`. This
    theorem states the guarantee in terms of `allOnes`, and thus it proves that
    the absence of an explicit `allOnes` entry loses no coverage. -/
theorem allOnes_mem_bitvecBoundaries (w : Nat) :
    BitVec.allOnes w ∈ bitvecBoundaries w := by
  have h : BitVec.allOnes w = BitVec.fill w true := by
    simp [BitVec.fill, BitVec.neg_one_eq_allOnes]
  rw [h]; unfold bitvecBoundaries; simp

/-- `0` and `1` are in the pool. The list must hold them explicitly, because the
    fallback branch is *uniform*: `chooseNat 0 (2^w - 1)` hits `0` with
    probability `2^-w`. Thus the fallback does not supply them in practice. In
    particular, `0` is the divisor that trips each `y ≠ 0` precondition on
    `SafeSDiv` and `SafeSMod`, and it is the only false point of
    `unegOverflow`. -/
theorem zero_one_mem_bitvecBoundaries (w : Nat) :
    BitVec.zero w ∈ bitvecBoundaries w ∧ (1 : BitVec w) ∈ bitvecBoundaries w := by
  unfold bitvecBoundaries; simp

/-- A boundary-biased bitvector of width `w`. The generator draws it mostly from
    `bitvecBoundaries`, with a smaller **uniform** draw over the whole range of
    values. That draw keeps the generator *complete*: each `BitVec w` stays in its
    support, and the boundary pool does not confine it.

    The 7 to 1 split is deliberate. The bugs are at the boundaries, but a
    generator that gives only a boundary misses a counterexample in the interior.
    Worse, such a generator narrows the support that the completeness proofs
    quantify over, silently. Read `genBiasedBitVec_support_set`.

    The fallback is `chooseNat 0 (2^w - 1)`, which is **uniform over the full
    range**. It is not `natArb`. `natArb` flips a coin and then increments, so its
    mass decays geometrically. To draw an interior value near `2^63`, it needs
    about `2^63` coin flips, and it never does so in practice. A uniform sample
    makes the "interior" half of the generator sample the interior truly, which is
    the whole function of that half. `chooseNat` handles a range of `2^64`
    correctly. A check gives well-distributed values of 19 digits.

    The bound must be `2^w - 1`, the full range. A bound of `log₂ w`, for example,
    reaches only 6 of the `2^64` values at `w = 64`. Then this branch is useless
    as a completeness witness, *and* it reduces the support silently to the
    boundary pool plus a few small integers. `Nat.zero_le` discharges the `Nat.le`
    obligation, so the generator excludes no width. At `w = 0` it gives
    `chooseNat 0 0`, the unique `BitVec 0`. -/
def genBiasedBitVec [Gen G] (w : Nat) : G (BitVec w) :=
  frequency
    [ (7, fun () => elements (bitvecBoundaries w) (bitvecBoundaries_ne_nil w))
    , (1, fun () => BitVec.ofNat w <$> chooseNat 0 (2 ^ w - 1) (Nat.zero_le _)) ]
    (by simp)

end StrataGenerators.PrimitiveGens
