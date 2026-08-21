import StrataGenerators.Test.Types

/-!
# `family` — many properties over one input type

Sugar over `TestDecl.property` for a family of claims that share an input type and
differ only in the check:

```lean
@[strata_properties]
def stmtTransforms : List TestDecl :=
  family GenStmts
    [ ("stmt: LoopElim preserves typeability", fun gs => checkLoopElimPreservesTyping gs.stmts),
      ("stmt: LoopElim eliminates all loops",  fun gs => checkLoopElimZeroLoops gs.stmts) ]
```

It is a macro rather than a function, and that is the whole point. A function would
receive the entries as a `List (String × (α → Prop))`, and the `Decidable` and `Testable`
instances a check needs are resolved *per check*, at the site where the check is written
— a list literal handed to a function offers no such site. The macro expands each entry
to its own `TestDecl.property` call, so every entry resolves its own instances and
reports a failure as precisely as a standalone property does:

```
issue: 3 ≤ 2 does not hold          -- an entry stating an order
issue: 0 = 99 does not hold         -- an entry stating an equality
```

A function `family` could only take the *decided* form, and every entry would report
`issue: false does not hold`. There is therefore one way to state a check throughout the
API — a decidable `Prop` — with no exception for a family.

Naming the type once, in the `family GenStmts` position, is what lets the entries drop
their binder annotations: each check is ascribed to `GenStmts → Prop` during expansion.
-/

open Lean

namespace StrataGenerators.Test

/-- `family T [ (name, check), … ]` — one registered property per entry, each check a
    decidable `Prop` over `T`.

    An entry may carry a third component, an `Expectation`, for a member that is known
    to fail against a defect in the code under test:

    ```lean
    ("lift: the output typechecks", fun gp => checkLiftOutputTypechecks gp.prog,
     .knownFailure "strata-org/Strata#123: a snapshot name escapes its scope")
    ```

    The alternative would be to lift such a member out of the family into a standalone
    declaration, which costs the family its shape: these lists are ordered and commented
    by what the pass is supposed to do (`P1 — closedness`, `P6/P7 — name hygiene`), and
    the members that fail are exactly the ones a reader most needs to find in that
    order.

    `T` parses at maximum precedence, so a compound type needs parentheses:
    `family (List Nat) [ … ]`.

    Scoped, so `family` is a keyword only where `StrataGenerators.Test` is open. -/
scoped macro "family " α:term:max " [" entries:term,* "]" : term => do
  let mut out := #[]
  for e in entries.getElems do
    match e with
    | `(($n:term, $check:term)) =>
        out := out.push
          (← `(StrataGenerators.Test.TestDecl.property $n (($check : $α → Prop))))
    | `(($n:term, $check:term, $expect:term)) =>
        out := out.push
          (← `({ StrataGenerators.Test.TestDecl.property $n (($check : $α → Prop)) with
                 expect := ($expect : StrataGenerators.Test.Expectation) }))
    | _ =>
        Macro.throwErrorAt e
          "`family` expects each entry to be a `(name, check)` pair — or a \
           `(name, check, expectation)` triple for a member that is known to fail — \
           where `check` is a function from the family's input type to a decidable `Prop`"
  `([$out,*])

end StrataGenerators.Test
