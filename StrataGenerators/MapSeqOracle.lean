import StrataGenerators.MapSeqProps
import StrataGenerators.FunctionHasTypeAGen.Roundtrip

open Lambda Strata

/-!
# Solver-backed oracles for `Map`/`Sequence` properties (opt-in, needs a solver)

The property *expectations* live in `MapSeqProps.lean` (pure, no solver). This
module renders a generated literal into a Core program whose asserts encode those
expectations, runs `Core.verify`, and scores the outcome.

## Why surface syntax rather than a hand-built `Program` AST

Emitting text and parsing it back with `parseCoreProgram` means each sample also
traverses the printer/parser path (`Grammar.lean` → `Translate.lean`), so a
malformed literal shows up as a parse failure rather than silently typechecking
into something else. It also makes counterexamples directly pasteable into a
`#strata` block, which matters because these programs are the *inputs* to a
solver run and need to be reproducible by hand.

## Three outcome classes, deliberately distinguished

`Core.verify` can return `pass`, `fail`, or `unknown`, and conflating the last two
would make this suite either useless or a liar:

- **`fail`** — the solver refuted an assertion the `List` model predicts. That is
  a genuine axiom/model disagreement and the only thing scored as a
  counterexample.
- **`unknown`** — the solver neither proved nor refuted it. For these axioms that
  is *expected* in characterised cases (see `containsKnownIncomplete`), so it is
  reported and counted but never fails the suite.
- **`pass`** — the axioms entail the model's prediction.

## Characterised incompleteness: `Sequence.contains`

`seqContainsFunc`'s axiom is an equivalence whose trigger is
`Sequence.contains(s, v)`, and whose right-hand side is an *existential* over the
index. On a snoc-chain literal the solver reliably witnesses the existential only
for the **outermost** `Sequence.build` — i.e. the last element. Measured on this
tree (`16d680b9a`), at both `useArrayTheory` settings:

| literal | `contains(last)` | `contains(earlier)` |
| --- | --- | --- |
| length 1 | pass | — |
| length 2 | pass | unknown |
| length 3 | pass | unknown |

So `contains` on a non-final element is quantifier-instantiation depth, not
unsoundness: the negative direction (`!contains(s, absent)`) also passes at
length 1. `containsKnownIncomplete` encodes exactly this shape so the oracle
asserts `contains` only where a verdict is meaningful, rather than accumulating
`unknown`s that hide a real regression.
-/

namespace StrataGenerators.MapSeqOracle

open StrataGenerators.MapSeqGen StrataGenerators.MapSeqProps

/-- Render a Lean `Int` as a Core integer literal. Negative values need
    parenthesising so they parse in argument position. -/
def intLit (n : Int) : String :=
  if n < 0 then s!"({n})" else toString n

/-- Render a `Sequence int` literal as the surface-syntax snoc-chain
    `Sequence.build(… Sequence.build(Sequence.empty<int>(), e0) …, eN)`. -/
def renderSeqLiteral (elems : List Int) : String :=
  elems.foldl
    (fun acc v => s!"Sequence.build({acc}, {intLit v})")
    "Sequence.empty<int>()"

/-- Render a `Map int int` literal as `mapConst<int>(d)[k := v]…`, matching
    `mapLiteralOfList`'s left-to-right update order (so later duplicate keys
    win, exactly as `mapLiteralEntries` predicts). -/
def renderMapLiteral (dflt : Int) (entries : List (Int × Int)) : String :=
  entries.foldl
    (fun acc (k, v) => s!"{acc}[{intLit k} := {intLit v}]")
    s!"mapConst<int>({intLit dflt})"

/-- Whether a `contains` query on this literal falls in the characterised
    incomplete region described in the module doc: the solver only reliably
    discharges `contains` for the **last** element of a snoc-chain, since that is
    where the axiom's trigger fires without nested instantiation.

    Returns `true` when the query should be *skipped* rather than asserted. -/
def containsKnownIncomplete (elems : List Int) (v : Int) : Bool :=
  match elems.getLast? with
  | none      => true            -- empty literal: nothing to witness
  | some last => v != last       -- only the final element is reliably provable

/-- Build a Core program whose asserts encode the `SeqModel`-predicted answers
    for `s`, per the mapping table in `SeqModel.lean`.

    Each assert is labelled with the `SeqModel` theorem it encodes, so a solver
    `fail` names the axiom that disagrees with the `List` model. Only total ops
    and in-bounds partial ops appear; out-of-bounds queries belong to §3
    (precondition obligations), not here. -/
def seqModelProgram (s : SeqLiteral) : String :=
  let lit := renderSeqLiteral s.elems
  let exp := s.expectations
  let n := s.elems.length
  -- `SeqModel.length_empty` / `build_length`
  let lengthAssert := s!"  assert [seqmodel_length]: Sequence.length({lit}) == {n};"
  -- `SeqModel.build_select_old` / `build_select_last`: one assert per index
  let selectAsserts := (List.range n).filterMap (fun i =>
    match s.expectedSelect i with
    | some v => some s!"  assert [seqmodel_select_{i}]: Sequence.select({lit}, {i}) == {intLit v};"
    | none   => none)
  -- `SeqModel.append_length`
  let appendAssert :=
    s!"  assert [seqmodel_append_length]: \
Sequence.length(Sequence.append({lit}, {lit})) == {exp.appendSelfLength};"
  -- `SeqModel.take_length` / `drop_length`, at a mid-list split point
  let mid := n / 2
  let takeAssert :=
    s!"  assert [seqmodel_take_length]: \
Sequence.length(Sequence.take({lit}, {mid})) == {(s.expectedTake mid).length};"
  let dropAssert :=
    s!"  assert [seqmodel_drop_length]: \
Sequence.length(Sequence.drop({lit}, {mid})) == {(s.expectedDrop mid).length};"
  -- `SeqModel.contains_iff_exists`, only where a verdict is meaningful
  let containsAsserts := match s.elems.getLast? with
    | some last =>
      if containsKnownIncomplete s.elems last then []
      else [s!"  assert [seqmodel_contains_last]: Sequence.contains({lit}, {intLit last});"]
    | none => []
  let body := String.intercalate "\n"
    ([lengthAssert] ++ selectAsserts ++ [appendAssert, takeAssert, dropAssert]
      ++ containsAsserts)
  s!"program Core;\n\nprocedure SeqModelCheck()\n\{\n{body}\n};\n"

/-- Build a Core program whose asserts encode the `Map` axioms' predictions for
    `m`: every bound key selects to its (last-written) value, and an unbound key
    selects to the `mapConst` default.

    The unbound-key probe is what exercises `mapConstFunc`'s axiom together with
    `updatePreserve`; it is skipped when the drawn keys happen to cover the probe
    point. -/
def mapModelProgram (m : MapLiteral) : String :=
  let lit := renderMapLiteral m.dflt m.entries
  let boundAsserts := m.entries.mapIdx (fun i (k, _) =>
    s!"  assert [mapmodel_select_{i}]: {lit}[{intLit k}] == {intLit (m.expectedSelect k)};")
  -- A key guaranteed absent from `entries`, to probe the `mapConst` default.
  let absentKey := (m.entries.map (fun (k, _) => k)).foldl max 0 + 1
  let defaultAssert :=
    s!"  assert [mapmodel_default]: {lit}[{intLit absentKey}] == {intLit m.dflt};"
  let body := String.intercalate "\n" (boundAsserts ++ [defaultAssert])
  s!"program Core;\n\nprocedure MapModelCheck()\n\{\n{body}\n};\n"

/-- Build a program asserting `Map` **equalities** that hold semantically but
    need *extensionality* to prove.

    This is the input the `useArrayTheory` metamorphic property actually needs.
    Pointwise `select` assertions (`mapModelProgram`) are provable from
    `updateSelect`/`updatePreserve` alone and therefore agree under both encoding
    modes — they cannot witness the divergence. Map equality can only be
    discharged with an extensionality axiom, which SMT-LIB `Array` theory has
    built in and `Factory.lean` does *not* declare, so this is where the two
    modes come apart.

    Three shapes, all semantically valid:

    - `commute` — updating two *distinct* keys in either order yields equal maps;
    - `absorb` — updating the same key twice equals updating it once with the
      second value;
    - `idem` — writing back a key's existing value is the identity.

    `k1`/`k2` must be distinct for `commute` to be valid, which the caller
    guarantees. -/
def mapExtensionalityProgram (dflt k1 v1 k2 v2 : Int) : String :=
  let base := s!"mapConst<int>({intLit dflt})"
  let commuteL := s!"{base}[{intLit k1} := {intLit v1}][{intLit k2} := {intLit v2}]"
  let commuteR := s!"{base}[{intLit k2} := {intLit v2}][{intLit k1} := {intLit v1}]"
  let absorbL  := s!"{base}[{intLit k1} := {intLit v1}][{intLit k1} := {intLit v2}]"
  let absorbR  := s!"{base}[{intLit k1} := {intLit v2}]"
  let idemL    := s!"{base}[{intLit k1} := {intLit dflt}]"
  let body := String.intercalate "\n"
    [ s!"  assert [ext_commute]: {commuteL} == {commuteR};"
    , s!"  assert [ext_absorb]: {absorbL} == {absorbR};"
    , s!"  assert [ext_idem]: {idemL} == {base};" ]
  s!"program Core;\n\nprocedure MapExtCheck()\n\{\n{body}\n};\n"

/-- Build a program that pairs each in-bounds partial-op call with the bounds
    fact the precondition needs, and each out-of-bounds call with none.

    This is the §3 (precondition-obligation) input. The point is not the asserts
    themselves but the *obligations Strata generates around them*: every
    `Sequence.select`/`take`/`drop` call must produce an
    `assert_…_calls_Sequence.…` out-of-bounds check, and an in-bounds call's
    check must be dischargeable. -/
def seqPrecondProgram (s : SeqLiteral) : String :=
  let lit := renderSeqLiteral s.elems
  let n := s.elems.length
  -- In-bounds: index 0 always exists (literals are non-empty), so its
  -- out-of-bounds obligation must be provable.
  let inBounds :=
    s!"  assert [precond_inbounds]: Sequence.select({lit}, 0) == \
{intLit (s.expectedSelect 0 |>.getD 0)};"
  -- `take`/`drop` take a *non-strict* upper bound (`Le`), so `n` is legal for
  -- both while `n + 1` is not — the boundary `mkSeqBoundsPrecond` distinguishes.
  let takeFull :=
    s!"  assert [precond_take_full]: Sequence.length(Sequence.take({lit}, {n})) == {n};"
  let dropFull :=
    s!"  assert [precond_drop_full]: Sequence.length(Sequence.drop({lit}, {n})) == 0;"
  let body := String.intercalate "\n" [inBounds, takeFull, dropFull]
  s!"program Core;\n\nprocedure SeqPrecondCheck()\n\{\n{body}\n};\n"

end StrataGenerators.MapSeqOracle
