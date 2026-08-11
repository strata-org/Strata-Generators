import StrataGenerators.FunctionHasTypeAGen.Roundtrip

open Lambda Core Imperative

/-!
# Signature-preserving shrinker for the `Shrinkable Function` instance

The candidate list backing the `Shrinkable Function` instance (wired up in
`StrataGenerators.TestScaffold`). It deliberately **holds the entire type signature
fixed** — inputs, output, type-args and measure — and reduces only the two things
that are not part of it: the body *expression* and the `requires` clauses (dropped
or reduced). A shrunk function is therefore still a drop-in replacement at the same
type.

This is kept separate from `StrataGenerators.FunctionHasTypeAGen.Roundtrip`, whose
contents are exactly what the parser/pretty-printer round-trip property needs (the
format/parse machinery, the failure predicates, and the greedy signature-reducing
minimizer `shrinkWhile`). This shrinker reuses two pieces from there —
`funcWellFormed` (the candidate well-formedness filter) and the shared
`shrinkLExpr` (from `HasTypeAGen.TestSupport`) — but is otherwise independent.
-/

/-- Candidate set for the `Shrinkable Function` instance: **signature-preserving**
    structural shrinks (reusing the shared `shrinkLExpr`), holding the entire type
    signature fixed — same inputs (count and types), same output type, same
    type-args, and same measure. Two things are reduced: the body *expression*,
    toward a minimal expression that still type-checks at the declared `output`; and
    the `requires` clauses, either dropped or reduced.

    Preconditions are reduced here even though this reducer is otherwise
    conservative, because a `requires` clause is not part of the type signature —
    the promise this family makes is that a shrunk function is still a drop-in
    replacement at the same *type*, and dropping a clause preserves that. Reducing
    them also matters for reach: `genFunction` carries a clause on roughly half its
    draws, so a counterexample resting on one is only minimizable through this
    instance if the clause can go. Dropping precedes reducing, so the bigger
    reduction is tried first.

    Well-typedness of every candidate is enforced by `funcWellFormed` in
    `shrinkFuncWellFormed`: since `output` is unchanged here, that filter keeps only
    bodies whose type still matches the (fixed) output, and it keeps every surviving
    clause Boolean and scoped to the formals — which matters because
    `Function.typeCheck` does not check preconditions at all.

    (Note: this is intentionally narrower than the round-trip `shrinkFunc`, which
    also drops/retypes the signature and drops the body/measure. That broader
    reducer is what the greedy round-trip minimizer `shrinkWhile` uses.) -/
def shrinkFuncCandidates (f : Function) : List Function :=
  let pres := f.preconditions
  let shrinkBody := match f.body with
    | some b => (fun b' => { f with body := some b' }) <$> shrinkLExpr b
    | none => []
  let dropPrecond := (fun ps => { f with preconditions := ps }) <$> dropEach pres
  let shrinkPrecond := pres.zipIdx.flatMap fun (pc, i) =>
    (fun e => { f with preconditions := pres.set i { pc with expr := e } })
      <$> shrinkLExpr pc.expr
  dropPrecond ++ shrinkBody ++ shrinkPrecond

/-- Well-typed signature-preserving shrinks of a function (for the `Shrinkable
    Function` instance): every candidate that satisfies `funcWellFormed`. The type
    signature — inputs, output, type-args, and measure — is preserved exactly; the
    body expression and the `requires` clauses are what get reduced. Unlike the
    round-trip `shrinkWhile`, this is a plain one-step candidate list, as the
    `Shrinkable` typeclass expects. -/
def shrinkFuncWellFormed (f : Function) : List Function :=
  (shrinkFuncCandidates f).filter funcWellFormed
