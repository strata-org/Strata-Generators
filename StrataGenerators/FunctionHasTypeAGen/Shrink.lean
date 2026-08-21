import StrataGenerators.FunctionHasTypeAGen.Roundtrip

open Lambda Core Imperative

/-!
# The shrinker for the `Shrinkable Function` instance, which keeps the signature

This file holds the list of candidates for the `Shrinkable Function` instance, which
`StrataGenerators.TestScaffold` connects. The shrinker **keeps the whole type signature**:
the inputs, the output, the type arguments and the measure. It reduces only the two parts
that are not in the signature: the *expression* of the body, and the `requires` clauses,
which it removes or reduces. A smaller function is therefore still usable in place of the
original function at the same type.

This file is separate from `StrataGenerators.FunctionHasTypeAGen.Roundtrip`. That module
holds exactly what the round-trip property for the parser and the printer needs: the code
that formats and parses, the predicates for a failure, and the greedy shrinker `shrinkWhile`,
which also reduces the signature. This shrinker uses two parts from that module,
`funcWellFormed`, which filters a candidate, and the shared `shrinkLExpr`. It is otherwise
independent.
-/

/-- The candidates for the `Shrinkable Function` instance. The structural reductions **keep the
    signature**, and they use the shared `shrinkLExpr`. The inputs keep their number and their types,
    the output type stays the same, the type arguments stay the same, and the measure stays the same.
    The shrinker reduces two parts: the *expression* of the body, toward the smallest expression that
    still typechecks at the declared `output`; and the `requires` clauses, which it removes or
    reduces.

    The shrinker reduces a precondition, although it is careful in each other part, because a
    `requires` clause is not in the type signature. The promise of this family is that a smaller
    function is still usable in place of the original at the same *type*, and the removal of a clause
    keeps that promise. The reduction also matters for reach: `genFunction` gives a clause on about
    half of its draws, so this instance can reduce a counterexample that rests on a clause only when
    the clause can go. The removal comes before the reduction, so the shrinker tries the larger
    reduction first.

    `funcWellFormed` in `shrinkFuncWellFormed` keeps each candidate well-typed. The `output` does not
    change here, so that filter keeps only a body whose type still matches the output. It also keeps
    each remaining clause Boolean and in the scope of the formal parameters. That matters, because
    `Function.typeCheck` checks no precondition.

    This shrinker is narrower than `shrinkFunc` in the module for the round trip, which also removes a
    part of the signature, gives it another type, and removes the body and the measure. The greedy
    shrinker `shrinkWhile` for the round trip uses that wider reducer. -/
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

/-- The reductions of a function that keep the signature and stay well-typed, for the
    `Shrinkable Function` instance. The list holds each candidate that satisfies `funcWellFormed`.
    The type signature does not change: the inputs, the output, the type arguments and the measure
    stay the same. The shrinker reduces the expression of the body and the `requires` clauses. Unlike
    `shrinkWhile` for the round trip, this function gives a plain list of candidates for one step,
    which is what the `Shrinkable` class needs. -/
def shrinkFuncWellFormed (f : Function) : List Function :=
  (shrinkFuncCandidates f).filter funcWellFormed
