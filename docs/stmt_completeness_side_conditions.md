# The side conditions of `spec_complete`

## The task

Remove `AlphabetOk`, `InGenShape` and `CallOk` from
`StrataGenerators/StmtHasTypeAGenComplete.lean`. Replace them with an upstream
predicate, or remove them from the theorem.

## The result

You cannot remove them. The support of `genStmt` is a strict subset of the
statements that `StatementHasTypeA` accepts. Each of the three predicates keeps at
least one clause that closes a real gap.
`StrataGenerators/StmtHasTypeAGenCompleteGaps.lean` proves this. For each
predicate it gives a statement with two properties:

1. `StatementHasTypeA` accepts the statement.
2. The support of `genStmt` does not hold the statement, at every size and at
   every procedure context.

The three gap theorems are `metadata_gap`, `label_gap` and `outTarget_gap`. The
proofs need no new axiom and no `sorry`.

Two gaps that earlier versions of this report recorded are now **closed**, by a
change to the generators rather than to the proofs:

| Gap                              | State  | Cause                                    |
| -------------------------------- | ------ | ---------------------------------------- |
| metadata at `default`            | open   | the generator emits no metadata          |
| name outside `genIdentName`      | open in the AST only | a `Statement` holds a bare `String` |
| label outside the alphanumerics  | closed | labels now come from `genIdentName`      |
| fixed call-argument order        | closed | `mkArgs` takes an interleaving mask      |
| out target is the callee's name  | open   | `outTargets` picks the name              |

So exactly two of the surviving clauses have a counterexample you can write in
Core: the metadata clause and the out-target clause.

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

## Gap 2: the identifier alphabet (`AlphabetOk`) — closed at the source level

`genAssertCmd`, `genAssumeCmd`, `genCoverCmd` and `genFreshName` now draw from
`genIdentName`. Its support is exactly the legal Core bare identifiers that are not
reserved keywords (`mem_support_genIdentName_iff_isId`). So every name a parsed
program can hold is reachable, and **no Core program breaks the clause any more**.

The earlier sources were `String.arbitrary` for a label and
`NonEmptyString.arbitrary` for an `init` variable name. The support of each holds
the alphanumeric strings only, so this was a counterexample:

```
program Core;

procedure caller ()
{
  assert [loop_invariant]: true;
};
```

The gap mattered in practice. The parser mints `assert_0` for an unlabelled
`assert` (`translateLabeledCheck`), and an underscore is not alphanumeric, so the
generator could not produce the label shape that the front end produces. The old
generator also emitted `""` often, which `Core.formatProgram` renders as the
degenerate `assert [||]: true;`.

`label_gap` survives, because a `Statement` holds a bare `String` that need not be
a legal identifier. `emptyLabel_not_reachable` gives a witness that lives in the
abstract syntax tree alone. The `dodgeKeyword` conjunct is gone from `AlphabetOk`:
`genIdentName`'s support already excludes every keyword.

`LContext.WellKindedTy` is a premise of the two `init` rules and bounds the type
constructors of the annotation. The support of `genLMonoTy` also bounds the depth
of the type and its free type variables (`genLMonoTy_support`), so `WellKindedTy`
cannot replace the `init` type clause of `AlphabetOk`.

## Gap 3: the order of the call arguments (`CallOk`) — closed

The `call` rule of `CmdExtHasType'` constrains the input positions and the write
positions one at a time. It uses `CallArg.getInputExprs` and `CallArg.getLhs`, and
each projection drops one kind of node. So order matters *inside* each projection
only:

| swap                  | `getInputExprs` | `getLhs`  | visible to the rule |
| --------------------- | --------------- | --------- | ------------------- |
| `inArg` ↔ `outArg`    | unchanged       | unchanged | no                  |
| `inArg` ↔ `inoutArg`  | changes         | unchanged | yes                 |
| `outArg` ↔ `inoutArg` | unchanged       | changes   | yes                 |

Four `#guard`s in `GenCallStmtSound.lean` pin this table down.

`mkArgs` used to fix the order as in-out, then by-value input, then out target, so
this was a counterexample:

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

`mkArgs` now takes an interleaving mask and `genCallStmt` samples one, so the call
above is reachable. `mkArgs_out_then_in` witnesses it. The in-out block still
leads, because it heads both the input signature and the output signature, and the
in-out premise pins `getInputExprs[i]` to the very name the callee declares.

`getIn_mkArgs` and `getLhs_mkArgs` keep their right-hand sides at every mask, so no
soundness proof changed. `genStmt_sound` still holds.

## Gap 3': the out-target name choice (`CallOk`) — open

The `call` rule constrains an `out` argument's existence, its type and its
writability. It says nothing about its *name*. `outTargets` fixes the name: it
reuses the name the callee declares when that name is in scope at the declared
type, and otherwise it invents a fresh one. So a call that receives the result into
another in-scope variable of the same type is well-typed and out of reach:

```
program Core;

procedure p (x : int, out r : int)
{

};
procedure caller ()
{
  var r : int := 0;
  var z : int := 0;
  call p(1, out z);
};
```

Theorem: `outTarget_gap`. Well-typedness: `otherTargetCall_wt`. Both facts
together: `otherTargetCall_gap`.

`Core.WF.WFcallProp.lhsWF` states the `Nodup` fact that `CallOk` needs for the
write keys of a call, so that one conjunct has an upstream form. Its parent
`Core.WF.WFStatementProp` is not recursive: its `block`, `ite` and `loop` cases are
empty structures. So it says nothing about a call inside a body, and a recursive
form of it does not exist upstream.

`CallOk` keeps one more clause with no upstream counterpart: the generator draws
each type argument from `generableTypesFromCtx`, and the spec accepts every type
instantiation.

## The clauses with no source-level counterexample

The name clauses of `AlphabetOk` are one case, described above.

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

## Test-suite effect

`lake test -- --quick` reports the same set of failing properties before and after
the change, with one exception: `program: typeCheck output re-typechecks`. That
property also fails on the baseline at 200 trials, and its counterexample is a
procedure with an empty body whose signature holds a `bitvec 0`. It has no label,
no local variable and no call, so neither change can cause it. The change shifts
the random stream, so a draw-dependent known defect surfaces on a different
property.

The label change reduces one source of noise. `checkInlineProcLabelsNodup` and
`checkS2uLabelsNodup` guard on the input having distinct labels, because
`String.arbitrary` gave `""` often enough that about 4 percent of programs held a
duplicate label before any pass ran. `genIdentName` collides far less often, so the
guard now holds off the property far less often.
