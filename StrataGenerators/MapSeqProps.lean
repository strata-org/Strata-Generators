import StrataGenerators.MapSeqGen
import Strata.Languages.Core.Factory
import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.Verifier

open Lambda

/-!
# Properties over Strata Core's `Map` and `Sequence` datatypes

Three property families, all enabled by the literal generators in
`MapSeqGen.lean` (issue #5) and all aimed at parts of Strata that carry **no
machine-checked correctness argument** (issue #69):

1. **`SeqModel` differential** (§1) — `Strata/Languages/Core/SeqModel.lean` is
   172 lines of Lean theorems over `List` that mirror the 19 sequence axioms in
   `Factory.lean`. Nothing imports it except the top-level `Strata.lean`
   aggregator, no lemma mentions a Strata definition, and there is no bridge
   theorem relating `List α` to `Sequence a` — so it is a *hand-maintained
   claim*, not a proof. This family turns it into an executable oracle by
   asserting the `List`-predicted answer against the solver.

2. **`useArrayTheory` metamorphic** (§2) — `Options.lean` documents the flag as
   an encoding choice ("Use SMT-LIB Array theory instead of axiomatized maps")
   and `MetaVerifier.lean` frames the two as alternative treatments of the *same*
   semantics. If that is right, toggling it cannot change any obligation's
   outcome. It does; see the module doc on `arrayTheoryKnownGaps` below.

3. **Precondition obligations** (§3) — `Sequence.select`/`update`/`take`/`drop`
   are the only *partial* Core operators with non-trivial bounds preconditions
   (`mkSeqBoundsPrecond` in `Factory.lean`). Literals make the resulting
   obligations non-vacuous, which exercises `Preconditions.lean`'s short-circuit
   `&&`/`||`/`ite` hypothesis threading — subtle, hand-written, and unproven.

## Why every oracle here goes through the solver

`Core.Factory` declares all nine `Sequence.*` ops and all three `Map` ops with
`polyUneval`, i.e. **axioms only, no `concreteEval` and no body**. The in-Lean
evaluator therefore cannot reduce them at all: `LExpr.evalWithLState` leaves
`Sequence.length(Sequence.build(Sequence.empty<int>(), 10))` completely
unreduced rather than returning `1` (verified directly). So unlike the
`--smt` expression property in `HasTypeAGen/SmtEval.lean`, which cross-checks
the evaluator *against* SMT, there is no second evaluator to differ from here.
The `List` model plays that role instead: Lean computes the expected answer, the
solver is asked to confirm it from the axioms, and a disagreement means the
axioms and the model have drifted apart.

Consequence: these properties need a live solver and are opt-in, exactly like
`exprSmtEvalAgreement`.
-/

namespace StrataGenerators.MapSeqProps

open StrataGenerators.MapSeqGen

/-- A generated `Sequence` literal paired with the Lean `List` it is meant to
    denote. Carrying both together is what makes the differential oracle
    possible: `elems` is the `SeqModel` side, `expr` the Strata side.

    The invariant the oracle checks is the `SeqModel.lean` mapping table:
    `Sequence.length(expr) = elems.length`, `Sequence.select(expr, i) = elems[i]`,
    and so on. -/
structure SeqLiteral where
  /-- Element type of the sequence. -/
  elemTy : LMonoTy
  /-- The Lean-side model: the list this literal denotes, head at index 0. -/
  elems  : List Int
  /-- The Strata-side term: a snoc-chain of `Sequence.build` over
      `Sequence.empty`. -/
  expr   : LExpr'
deriving Inhabited

/-- A generated `Map` literal paired with the bindings it denotes.

    `dflt` is the `mapConst` default — every key not in `entries` selects to it,
    which is the `mapConst` axiom. `entries` is already
    duplicate-resolved (`mapLiteralEntries`), so `select(expr, k)` is predicted
    by a plain lookup with `dflt` as the fallback. -/
structure MapLiteral where
  keyTy   : LMonoTy
  valTy   : LMonoTy
  /-- The `mapConst` default: the value of every unbound key. -/
  dflt    : Int
  /-- Effective bindings, last-write-wins, as `mapLiteralEntries` computes. -/
  entries : List (Int × Int)
  expr    : LExpr'
deriving Inhabited

/-- The value `select(m, k)` must have, per the `mapConst`/`updateSelect`/
    `updatePreserve` axioms: the bound value if `k` is bound, else the
    constant-map default. -/
def MapLiteral.expectedSelect (m : MapLiteral) (k : Int) : Int :=
  match m.entries.find? (fun (k', _) => k' == k) with
  | some (_, v) => v
  | none        => m.dflt

-- ── §1. `SeqModel` differential expectations ─────────────────────────

/-- The `SeqModel.lean` mapping table, as computable predictions over the Lean
    `List` model. Each field is named after the `SeqModel` theorem (and hence
    after the `Factory.lean` axiom) it encodes, so a failure names the axiom that
    disagrees with the model.

    Only *total* projections are listed. The partial ops
    (`select`/`update`/`take`/`drop`) are predicted by the functions below,
    guarded by their bounds preconditions — §3 covers the obligations those
    preconditions generate. -/
structure SeqExpectations where
  /-- `seqLengthFunc` / `SeqModel.length_nonneg`, `length_empty`,
      `build_length`: the length is the model list's length. -/
  length   : Nat
  /-- `seqContainsFunc` / `SeqModel.contains_iff_exists`. -/
  contains : Int → Bool
  /-- `seqAppendFunc` / `SeqModel.append_length`. -/
  appendSelfLength : Nat

/-- Compute the expected total-op answers for a literal from its `List` model. -/
def SeqLiteral.expectations (s : SeqLiteral) : SeqExpectations where
  length := s.elems.length
  contains := fun v => s.elems.contains v
  appendSelfLength := s.elems.length + s.elems.length

/-- `seqSelectFunc` / `SeqModel.build_select_old`, `build_select_last`:
    the element at `i`, or `none` when `i` is out of bounds (in which case the
    Strata side has an unsatisfied precondition rather than a value). -/
def SeqLiteral.expectedSelect (s : SeqLiteral) (i : Nat) : Option Int :=
  s.elems[i]?

/-- `seqTakeFunc` / `SeqModel.take_length`, `take_select`. -/
def SeqLiteral.expectedTake (s : SeqLiteral) (n : Nat) : List Int :=
  s.elems.take n

/-- `seqDropFunc` / `SeqModel.drop_length`, `drop_select`. -/
def SeqLiteral.expectedDrop (s : SeqLiteral) (n : Nat) : List Int :=
  s.elems.drop n

/-- `seqUpdateFunc` / `SeqModel.update_length`, `update_select_same`,
    `update_select_other`. -/
def SeqLiteral.expectedUpdate (s : SeqLiteral) (i : Nat) (v : Int) : List Int :=
  s.elems.set i v

-- ── Generators ───────────────────────────────────────────────────────

/-- Generate a small integer element. Kept deliberately narrow: the oracle
    asserts *equalities* against solver-derived values, so wide integers buy no
    extra coverage of the axioms while making counterexamples harder to read. -/
def genSmallInt [Gen G] : G Int := do
  let n ← chooseNat 0 20 (by omega)
  pure (n : Int)

/-- Generate a `Sequence int` literal of length `1 … maxLen` together with its
    `List` model. Non-empty by construction — an empty sequence makes every
    `select`/`take`/`drop` property vacuous, which is the failure mode this whole
    exercise exists to avoid. -/
def genSeqLiteralWithModel [Gen G] (maxLen : Nat := 3) : G SeqLiteral := do
  let n ← chooseNat 1 (max 1 maxLen) (Nat.le_max_left 1 maxLen)
  let elems ← (List.range n).mapM (fun _ => genSmallInt)
  let intTy : LMonoTy := .tcons "int" []
  pure { elemTy := intTy
         elems  := elems
         expr   := seqLiteralOfList intTy (elems.map (fun v => .intConst () v)) }

/-- Generate a `Map int int` literal of `1 … maxSize` updates together with its
    (duplicate-resolved) bindings. -/
def genMapLiteralWithModel [Gen G] (maxSize : Nat := 3) : G MapLiteral := do
  let n ← chooseNat 1 (max 1 maxSize) (Nat.le_max_left 1 maxSize)
  let dflt ← genSmallInt
  let rawEntries ← (List.range n).mapM (fun _ => do
    let k ← genSmallInt
    let v ← genSmallInt
    pure (k, v))
  let intTy : LMonoTy := .tcons "int" []
  let exprEntries := rawEntries.map (fun (k, v) =>
    ((.intConst () k : LExpr'), (.intConst () v : LExpr')))
  -- Resolve duplicates the same way the built chain does (last write wins), so
  -- `expectedSelect` agrees with the term by construction.
  let resolved := (rawEntries.reverse.foldl
    (fun acc (k, v) => if acc.any (fun (k', _) => k' == k) then acc else (k, v) :: acc)
    []).reverse
  pure { keyTy   := intTy
         valTy   := intTy
         dflt    := dflt
         entries := resolved
         expr    := mapLiteralOfList intTy intTy (.intConst () dflt) exprEntries }

end StrataGenerators.MapSeqProps
