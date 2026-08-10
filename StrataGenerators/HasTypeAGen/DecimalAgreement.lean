import StrataGenerators.PrimitiveGens
import Strata.DL.SMT.Factory
import Strata.DL.SMT.Term

open Strata.SMT StrataDDM StrataGenerators.PrimitiveGens

/-!
# `Decimal` against `Rat`: the encoding of a real in the SMT dialect

Strata Core has **two** representations of a real number. At the level of the AST
and of the denotational semantics, a real is Lean's `Rat`: `LExpr.realConst` takes
a `Rat`, and `SortDenote` maps `real` to `Rat`. In the term language of the SMT
dialect, a real is a `StrataDDM.Decimal`, which is a pair of a `mantissa : Int`
and an `exponent : Int`.

`Rat` is canonical by construction. `Decimal` is **not**: nothing holds it to a
normal form, so one rational value has infinitely many `Decimal` spellings.
`3e0` and `30e-1` are both the value 3.

The two properties here test the consequences of that difference. Both need no
solver, because each one is a statement about a pure function in the SMT dialect.

## The two defects

**A fold of `eq` on two reals of equal value gives `false`.** `Factory.eq` folds a
comparison of two literals by **structural** equality:

```lean
def eq (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ then true
  else if t₁.isLiteral && t₂.isLiteral then false    -- a real reaches here
  else …
```

`Term.isLiteral` is `true` for each `.prim`, so two `Term.real` literals take the
`false` branch whenever they are not structurally identical. Therefore the folder
does not merely fail to simplify: it **asserts a false fact** into the term. The
path for `Int` is correct, because `Int` is canonical, and `eq_correct_int` proves
it. The asymmetry comes from the choice of representation.

**`eq` is structural, but `lt` is by value.** `TermPrim.lt` compares two reals with
`r₁.toRat < r₂.toRat`. Therefore, for `a = 3e0` and `b = 30e-1`, each of
`lt a b`, `lt b a` and `eq a b` is `false`. The comparator is not a total order.

One correction fixes both defects: make `eq` compare by value. Normalization of
`Decimal` fixes the first defect alone, and it leaves `eq` and `lt` on different
notions of equality.

## Scope: these are unit properties, and they are latent

Each property is a statement about `Decimal` values, and **not** about a `Rat`
routed through the encoder for Core. That distinction is the whole point.

Each real literal of Core reaches SMT through `Decimal.fromRat`, which normalizes.
`Rat` is canonical, so two literals of Core with the same value normalize to
*identical* `Decimal`s, and the folder gets the right answer. Therefore a
generator-driven property over `Rat` **passes**, and it hides both defects. The
one producer in the tree that does not normalize is the parser for a model, whose
values go to the display of a counterexample and never reach `Factory.eq`.

For this reason both defects are **latent**: no path in Strata reaches them today.
They are a trap for a future caller, such as one that wires the parser for a model
into a term. Each property below states the invariant that such a caller needs.

## What the generator contributes

A pair of independent draws is almost never equal, so the branch of `eq` that
should give `true`, which is the branch that breaks, would almost never run. The
generator therefore draws a rational and then builds a **second `Decimal` for the
same value**, by inflation of the mantissa and the exponent. Without that bias,
each property below passes vacuously.
-/

namespace StrataGenerators.DecimalAgreement

/-- Multiply the mantissa by `10 ^ k` and subtract `k` from the exponent. The value
    does not change, because
    `(m · 10^k) · 10^(e-k) = m · 10^e`, but the pair is a different `Decimal` for
    each `k > 0`.

    This function is what makes the properties non-vacuous. It manufactures the
    second spelling of one value, which a pair of independent draws would almost
    never give. -/
def inflate (d : Decimal) (k : Nat) : Decimal :=
  { mantissa := d.mantissa * (10 ^ k : Int), exponent := d.exponent - (k : Int) }

/-- Regroup a power of ten out of a product. This is the arithmetic core of
    `inflate_toRat`, and it is separate because `Int.pow_add` needs the base to be
    an `Int`, which it is not inside the goal until the exponents are natural
    numbers. -/
private theorem mul_pow_split (m : Int) (a b : Nat) :
    m * 10 ^ (a + b) = m * 10 ^ a * 10 ^ b := by
  rw [Int.pow_add]; grind

/-- **`inflate` does not change the value, for every `Decimal` and every `k`.**

    This theorem is what lets a failure of either property below be read as a
    defect in `Factory.eq` or in `TermPrim.lt`, and not as a fault in the
    generator. The two `Decimal`s that `genSameValuePair` gives truly denote one
    rational, so a correct `eq` must fold them to `true`.

    Without this theorem, a defect in `inflate` looks exactly like a defect in
    `Factory.eq`: the pair would denote two *different* values, a fold to `false`
    would be correct, and both properties would report a defect that is not there.
    A check of a sample of values cannot exclude that, because it says nothing
    about the values that the generator draws but the sample omits.

    `Decimal.toRat` divides into cases on the sign of the exponent, so the proof
    has four cases. One case is impossible: the exponent of `inflate d k` is
    `d.exponent - k`, which cannot be non-negative while `d.exponent` is negative.
    `Rat.mkRat_mul_right` cancels the common factor of `10 ^ k` in the case where
    both exponents are negative. -/
theorem inflate_toRat (d : Decimal) (k : Nat) :
    Decimal.toRat (inflate d k) = Decimal.toRat d := by
  unfold inflate Decimal.toRat
  simp only []
  split <;> rename_i h1 <;> split <;> rename_i h2
  · -- Both exponents are negative. Cancel the common factor of `10 ^ k`.
    rw [show (d.exponent - (k:Int)).natAbs = d.exponent.natAbs + k by omega, Nat.pow_add]
    exact Rat.mkRat_mul_right (a := 10 ^ k) (by simp)
  · -- The exponent of the pair is negative, and the exponent of `d` is not.
    -- Correct the exponent first, and then split `k`, so that neither rewrite
    -- disturbs the other.
    rw [show (d.exponent - (k:Int)).natAbs = k - d.exponent.natAbs by omega]
    rw [show Rat.ofInt (d.mantissa * 10 ^ d.exponent.natAbs)
          = mkRat (d.mantissa * 10 ^ d.exponent.natAbs) 1 from by
            simp [Rat.mkRat_one, Rat.ofInt],
        Rat.mkRat_eq_iff (by simp) (by simp)]
    simp
    rw [show k = d.exponent.natAbs + (k - d.exponent.natAbs) by omega]
    rw [show d.exponent.natAbs + (k - d.exponent.natAbs) - d.exponent.natAbs
          = k - d.exponent.natAbs by omega]
    exact mul_pow_split d.mantissa d.exponent.natAbs (k - d.exponent.natAbs)
  · -- Impossible: `d.exponent - k` cannot be non-negative when `d.exponent` is
    -- negative, because `k` is a natural number.
    omega
  · -- Both exponents are non-negative.
    congr 1
    rw [← show k + (d.exponent - (k:Int)).natAbs = d.exponent.natAbs by omega]
    grind

/-- Draw a `Decimal` together with a second spelling of the same value.

    The first component comes from `Decimal.fromRat` on a drawn rational, so it is
    a `Decimal` that Core itself can produce. `fromRat` gives `none` for a rational
    whose denominator has a factor other than 2 or 5, because such a value has no
    terminating decimal expansion. In that case the generator falls back to a
    `Decimal` built directly, so a draw is never wasted.

    The second component is `inflate` of the first, by a factor between 1 and 4.
    The factor starts at 1, and not at 0, because `inflate d 0` is `d` itself, and
    then the pair is structurally equal and the defect does not appear. -/
def genSameValuePair [Gen G] : G (Decimal × Decimal) := do
  let r ← genRat
  let d := match Decimal.fromRat r with
    | some d => d
    | none => { mantissa := r.num, exponent := 0 }
  let k ← chooseNat 1 4 (by omega)
  pure (d, inflate d k)

/-- The value that `Factory.eq` must fold to for two real literals: the comparison
    of the two values that they denote. -/
def expectedEqFold (d₁ d₂ : Decimal) : Bool :=
  Decimal.toRat d₁ == Decimal.toRat d₂

/-- The value that `Factory.eq` truly folds to, as an `Option Bool`. The result is
    `none` when the fold gives a term that is not a literal `bool`, which happens
    when `Factory.eq` leaves the comparison for the solver. -/
def actualEqFold (d₁ d₂ : Decimal) : Option Bool :=
  match Factory.eq (Term.real d₁) (Term.real d₂) with
  | .prim (.bool b) => some b
  | _ => none

/-- **Property P1.2: a fold of `eq` on two real literals agrees with a comparison
    of their values.**

    The property holds when `Factory.eq` either folds to
    `expectedEqFold`, or leaves the comparison for the solver, which is `none`. A
    fold to the *wrong* boolean is the failure, because it puts a false fact into
    the term.

    This property **fails** today. For each pair from `genSameValuePair` the two
    `Decimal`s denote one value, so a correct fold gives `true`. `Factory.eq`
    compares the pair structurally, finds it unequal, and folds to `false`. -/
def checkEqFold (d₁ d₂ : Decimal) : Bool :=
  match actualEqFold d₁ d₂ with
  | none => true
  | some b => b == expectedEqFold d₁ d₂

/-- **Property P1.3: the comparator on two real literals is a total order.**

    Exactly one of `lt d₁ d₂`, `lt d₂ d₁` and `eq d₁ d₂` must hold. This is
    trichotomy, and each order needs it.

    This property **fails** today. For a pair of equal value with different
    spellings, `lt` is `false` in each direction, because it compares by value, and
    the fold of `eq` is `false`, because it compares structurally. Therefore no one
    of the three holds, and the count is 0 instead of 1. -/
def checkTrichotomy (d₁ d₂ : Decimal) : Bool :=
  let lt₁ := TermPrim.lt (.real d₁) (.real d₂)
  let lt₂ := TermPrim.lt (.real d₂) (.real d₁)
  let eqv := actualEqFold d₁ d₂ == some true
  (if lt₁ then 1 else 0) + (if lt₂ then 1 else 0) + (if eqv then 1 else 0) == 1

-- ── Machine-checked reproducers ───────────────────────────────────────
--
-- These pin the specific pair from the report, independently of what the generator
-- draws. Each states the behaviour of the code as it is now, which is the
-- incorrect behaviour, so each breaks after a correction and shows that this file
-- needs an update.

/-- `3e0` and `30e-1` denote one value. -/
example : Decimal.toRat ⟨3, 0⟩ = Decimal.toRat ⟨30, -1⟩ := by native_decide

/-- **The defect in the fold of `eq`.** The two spellings above fold to `false`,
    although they denote one value. -/
example : actualEqFold ⟨3, 0⟩ ⟨30, -1⟩ = some false := by native_decide
example : checkEqFold ⟨3, 0⟩ ⟨30, -1⟩ = false := by native_decide

/-- **The defect in the comparator.** Each of `lt` in both directions and the fold
    of `eq` is `false`, so the comparator is not a total order. -/
example : TermPrim.lt (.real ⟨3, 0⟩) (.real ⟨30, -1⟩) = false := by native_decide
example : TermPrim.lt (.real ⟨30, -1⟩) (.real ⟨3, 0⟩) = false := by native_decide
example : checkTrichotomy ⟨3, 0⟩ ⟨30, -1⟩ = false := by native_decide

/-- The path for `Int` is correct, which shows that the defect comes from the
    representation and not from `Factory.eq` itself. `Int` is canonical, so a
    structural comparison of two `Int` literals is a comparison of their values. -/
example : Factory.eq (Term.int 3) (Term.int 3) = Term.prim (.bool true) := by native_decide
example : Factory.eq (Term.int 3) (Term.int 4) = Term.prim (.bool false) := by native_decide

/-- A pair of structurally identical reals folds to `true`, through the first
    branch of `Factory.eq`. Therefore the defect needs two *different* spellings,
    which is what `genSameValuePair` builds. -/
example : actualEqFold ⟨3, 0⟩ ⟨3, 0⟩ = some true := by native_decide

-- ── The properties as suite nodes ─────────────────────────────────────

/-- Run one property over `numTrials` pairs from `genSameValuePair`.

    `check` takes the two `Decimal`s and reports whether the property holds. The
    result has the shape that the suite needs:
    `(success, passed, attempted, message)`. On a failure the message gives the
    first counterexample, with the two spellings and the value that both denote, and
    the number of pairs with the defect. -/
def runDecimalProperty (numTrials : Nat) (label : String)
    (check : Decimal → Decimal → Bool) :
    IO (Bool × Nat × Nat × Option String) := do
  let total := max 1 (min numTrials 400)
  let mut passed := 0
  let mut failed := 0
  let mut firstBad : Option (Decimal × Decimal) := none
  for _ in List.range total do
    let (d₁, d₂) ← genSameValuePair (G := IO)
    if check d₁ d₂ then
      passed := passed + 1
    else
      failed := failed + 1
      if firstBad.isNone then firstBad := some (d₁, d₂)
  if failed == 0 then
    pure (true, passed, total, none)
  else
    let detail := match firstBad with
      | some (d₁, d₂) =>
        s!"first counterexample: {d₁.mantissa}e{d₁.exponent} and \
{d₂.mantissa}e{d₂.exponent}, which both denote {Decimal.toRat d₁}"
      | none => ""
    pure (false, passed, total,
      some s!"EXPECTED FAILURE: {label} {failed} of {total} pairs of equal value \
have the defect. `Decimal` has no normal form, so one value has many spellings. \
{detail}. This property must turn green after `Factory.eq` compares a real by \
value.")

/-- Property P1.2 as a suite node: a fold of `eq` agrees with a comparison of the
    values. -/
def eqFoldAction (numTrials : Nat) : IO (Bool × Nat × Nat × Option String) :=
  runDecimalProperty numTrials
    "`Factory.eq` folds two reals of equal value to `false`:" checkEqFold

/-- Property P1.3 as a suite node: the comparator is a total order. -/
def trichotomyAction (numTrials : Nat) : IO (Bool × Nat × Nat × Option String) :=
  runDecimalProperty numTrials
    "`eq` is structural and `lt` is by value, so neither `<` nor `=` holds:"
    checkTrichotomy

end StrataGenerators.DecimalAgreement
