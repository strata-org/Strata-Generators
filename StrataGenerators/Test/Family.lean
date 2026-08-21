import StrataGenerators.Test.Types

/-!
# `family`: many properties over one input type

`family` is sugar over `TestDecl.property` for a group of claims that share an input type and
differ only in the check:

```lean
@[strata_properties]
def stmtTransforms : List TestDecl :=
  family GenStmts
    [ ("stmt: LoopElim preserves typeability", fun gs => checkLoopElimPreservesTyping gs.stmts),
      ("stmt: LoopElim eliminates all loops",  fun gs => checkLoopElimZeroLoops gs.stmts) ]
```

`family` is a macro and not a function, and this is the point of it. A function would receive
the entries as a `List (String × (α → Prop))`. Lean resolves the `Decidable` instance and the
`Testable` instance of a check *at the site of that check*, and a list literal that goes to a
function gives no such site. The macro expands each entry to its own `TestDecl.property` call.
Each entry therefore resolves its own instances, and it reports a counterexample as exactly as
a property that stands alone:

```
issue: 3 ≤ 2 does not hold          -- an entry that states an order
issue: 0 = 99 does not hold         -- an entry that states an equality
```

A function `family` could take only the *decided* form, and each entry would report
`issue: false does not hold`. There is therefore one way to state a check in the whole API, a
decidable `Prop`, and a family is no exception.

The `family GenStmts` position names the type one time. The entries can then drop their type
annotations, because the macro ascribes each check to `GenStmts → Prop`.
-/

open Lean

namespace StrataGenerators.Test

/-- `family T [ (name, check), … ]` gives one registered property for each entry. Each check is
    a decidable `Prop` over `T`.

    An entry can hold a third component, an `Expectation`, for a member that a defect in the
    code under test falsifies:

    ```lean
    ("lift: the output typechecks", fun gp => checkLiftOutputTypechecks gp.prog,
     .knownFailure "a minted snapshot name escapes its scope")
    ```

    The other option is to move such a member out of the family into its own declaration, and
    this costs the family its shape. These lists have an order, and a comment gives what the
    pass must do for each part, such as `P1: closedness` or `P6 and P7: name hygiene`. The
    members that do not hold are the members that a reader most needs to find in that order.

    `T` parses at maximum precedence, so a compound type needs parentheses:
    `family (List Nat) [ … ]`.

    The macro is scoped, so `family` is a keyword only where `StrataGenerators.Test` is
    open. -/
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
