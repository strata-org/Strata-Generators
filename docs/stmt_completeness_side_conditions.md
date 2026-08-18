# The side conditions of `spec_complete`

## The task

Remove `AlphabetOk`, `InGenShape` and `CallOk` from
`StrataGenerators/StmtHasTypeAGenComplete.lean`. Replace them with an upstream
predicate, or remove them from the theorem.

## The result

You cannot remove them. The support of `genStmt` is a strict subset of the
statements that `StatementHasTypeA` accepts. Each of the three predicates keeps
one clause that closes a real gap. `StrataGenerators/StmtHasTypeAGenCompleteGaps.lean`
proves this. For each predicate it gives a statement with two properties:

1. `StatementHasTypeA` accepts the statement.
2. The support of `genStmt` does not hold the statement, at every size and at
   every procedure context.

The three gap theorems are `metadata_gap`, `label_gap` and `call_argorder_gap`.
The proofs need no new axiom and no `sorry`.

## Gap 1: metadata (`InGenShape`)

`genStmt` always emits `default` metadata. The spec leaves the metadata free.
The Core grammar has an annotation prefix on every statement (`MetadataAnn` in
`Strata/Languages/Core/DDMTransform/Grammar.lean`), so the gap is visible in the
source text:

```
program Core;

procedure caller ()
{
  @[myKey] assert [lbl]: true;
};
```

Theorem: `metadata_gap`. Well-typedness: `assert_wt`.

`Imperative.Stmt.stripMetaData` is the closest upstream function. It erases the
metadata of a `block`, an `ite`, a `loop`, an `exit`, a `funcDecl` and a
`typeDecl`. It leaves a `.cmd` node untouched, so it cannot close this gap. This
is an upstream defect: the function claims to remove all metadata from a
statement, but it does not recurse into `Imperative.Cmd` or into `Core.CmdExt`.
Upstream has no `Cmd.stripMetaData`.

## Gap 2: the identifier alphabet (`AlphabetOk`)

`genAssertCmd` draws an `assert` label from `String.arbitrary`. The support of
`String.arbitrary` holds the alphanumeric strings only (`ArbChar.alphanumChars`).
An underscore is legal in a Core label, and the `assert` rule accepts every
label:

```
program Core;

procedure caller ()
{
  assert [loop_invariant]: true;
};
```

Theorem: `label_gap`. Well-typedness: `assert_wt`.

The same gap applies to an `assume` label, to a `cover` label and to an `init`
variable name. An `init` name comes from `NonEmptyString.arbitrary`, which uses
the same alphabet. A `block` label, an invariant label, a type-constructor name
and a type-parameter name come from `genIdentName`. Its support is exactly the
legal Core bare identifiers that are not reserved keywords
(`mem_support_genIdentName_iff_isId`), so those clauses hold for every parsed
program. They are still necessary at the level of the abstract syntax tree,
because the tree admits any string.

Upstream has no predicate for the syntax of an identifier.
`LContext.WellKindedTy` is a premise of the two `init` rules and bounds the type
constructors of the annotation. The support of `genLMonoTy` also bounds the depth
of the type and its free type variables (`genLMonoTy_support`), so
`WellKindedTy` cannot replace the `init` clause of `AlphabetOk`.

## Gap 3: the order of the call arguments (`CallOk`)

The `call` rule of `CmdExtHasType'` constrains the input positions and the write
positions of a call one at a time. It uses `CallArg.getInputExprs` and
`CallArg.getLhs`, and both drop the other kind of argument. So the rule does not
constrain the order of the `CallArg` nodes. `mkArgs` fixes that order: every
`inoutArg`, then every `inArg`, then every `outArg`.

```
program Core;

procedure p (x : int, out r : int)
{

};
procedure caller ()
{
  var y : int := 0;
  call p(out y, 1);
};
```

`mkArgs` would produce `call p(1, out y);` for the same callee. Theorem:
`call_argorder_gap`. Well-typedness: `badOrderCall_wt`. The two facts together
are `badOrderCall_gap`.

`Core.WF.WFcallProp.lhsWF` states the `Nodup` fact that `CallOk` needs for the
write keys of a call, so that one conjunct has an upstream form. Its parent
`Core.WF.WFStatementProp` is not recursive: its `block`, `ite` and `loop` cases
are empty structures. So it says nothing about a call inside a body, and a
recursive form of it does not exist upstream.

`CallOk` has two more clauses with no upstream counterpart:

* The generator picks the receiving variable of each `out` parameter itself
  (`outTargets`). It reuses the name of the callee, or it invents a fresh name.
  The spec accepts any writable variable of the right type. So a call that
  receives into another in-scope variable of the right type is well-typed and out
  of reach.
* The generator draws each type argument from `generableTypesFromCtx`. The spec
  accepts every type instantiation.

## The one clause with no source-level counterexample

`InGenShape` demands that an `init` annotation is monomorphic (`.forAll [] mty`).
The `init_det` and `init_nondet` rules accept a polymorphic annotation with a
matching list of type arguments. The Core front end builds only `.forAll []`
local annotations (`translateInitStatement` and `translateVarStatement` in
`Strata/Languages/Core/DDMTransform/Translate.lean`). So this clause is necessary
at the level of the abstract syntax tree, but no parsed program can violate it.

## A separate risk: vacuity of `spec_complete`

`spec_complete` takes two environment hypotheses at every depth:

```
(hExprC : ∀ d (ctx : VarCtx), GenLExprComplete ctx.toFVarCtx octx tvars d)
(hFuncReach : ∀ d C Γ (func : Function), FuncHasTypeA C Γ func →
   func ∈ SetGen.support (genFunction (G := SetGen.Set) [] octx d))
```

Both quantify over every depth `d`, so both must hold at `d = 0`. At `d = 0` the
generator has two branches only. `genLExprBase … 0 τ` gives a leaf: a constant, a
bound variable, a free variable or an operator. `genIndir` applies one operator
to arguments that come from `genLExprBase … 0`, which are again leaves. So the
support at `d = 0` holds no term with an argument that is itself an application.

The term `1 + (2 + 3)` is such a term. `LExpr.HasTypeA` accepts it, because
`HasTypeA.op` reads the type off the annotation and ignores the context. So
`GenLExprComplete fctx octx tvars 0` looks false for every `fctx`, `octx` and
`tvars`, and `hExprC` looks unsatisfiable. Then `spec_complete` is vacuous.
`genFunction` at depth 0 has the same shape, so `hFuncReach` has the same risk.
Nothing in the package applies `spec_complete` today.

This claim is not machine-checked. It needs an inversion lemma for the support of
`genLExpr … 0`. Treat it as an open item, not as a result. Note that `genApp` in
`genLExprBase` does make a nested application reachable at a higher depth, so the
argument is about `d = 0` alone. The three gaps above are independent of this
item: they are statements about the support of `genStmt` alone.
