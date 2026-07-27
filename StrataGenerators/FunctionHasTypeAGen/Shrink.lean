import StrataGenerators.FunctionHasTypeAGen.Roundtrip

open Lambda Core Imperative

/-!
# Body-only shrinker for the `Shrinkable Function` instance

The candidate list backing the `Shrinkable Function` instance (wired up in
`StrataGenerators.TestScaffold`). It is deliberately **body-only**: it simplifies
the function's body *expression* while holding the entire type signature fixed.

This is kept separate from `StrataGenerators.FunctionHasTypeAGen.Roundtrip`, whose
contents are exactly what the parser/pretty-printer round-trip property needs (the
format/parse machinery, the failure predicates, and the greedy signature-reducing
minimizer `shrinkWhile`). This shrinker reuses two pieces from there —
`funcWellFormed` (the candidate well-formedness filter) and the shared
`shrinkLExpr` (from `HasTypeAGen.TestSupport`) — but is otherwise independent.
-/

/-- Candidate set for the `Shrinkable Function` instance: **body-only** structural
    shrinks (reusing the shared `shrinkLExpr`), holding the entire type signature
    fixed — same inputs (count and types), same output type, same type-args, and
    same measure. Only the body *expression* is simplified, toward a minimal
    expression that still type-checks at the declared `output`. Nothing else about
    the function changes.

    Well-typedness of every candidate is enforced by `funcWellFormed` in
    `shrinkFuncWellFormed`; since `output` is unchanged here, that filter keeps
    only bodies whose type still matches the (fixed) output.

    (Note: this is intentionally narrower than the round-trip `shrinkFunc`, which
    also drops/retypes the signature and drops the body/measure. That broader
    reducer is still used by the greedy round-trip minimizer `shrinkWhile`.) -/
def shrinkFuncCandidates (f : Function) : List Function :=
  match f.body with
  | some b => (fun b' => { f with body := some b' }) <$> shrinkLExpr b
  | none => []

/-- Well-typed body-only shrinks of a function (for the `Shrinkable Function`
    instance): every body-shrunk candidate that satisfies `funcWellFormed`. The
    type signature — inputs, output, type-args, and measure — is preserved
    exactly; only the body expression is reduced. Unlike the round-trip
    `shrinkWhile`, this is a plain one-step candidate list, as the `Shrinkable`
    typeclass expects. -/
def shrinkFuncWellFormed (f : Function) : List Function :=
  (shrinkFuncCandidates f).filter funcWellFormed
