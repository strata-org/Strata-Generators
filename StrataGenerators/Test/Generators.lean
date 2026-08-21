import StrataGenerators.TestScaffold
import StrataGenerators.Test.Types

/-!
# The catalog of generators

A property picks its generator in the way that Plausible and QuickCheck do: by the **type** of
the value that it quantifies over.

```lean
@[strata_property]
def myProp : TestDecl :=
  .property "mypass: idempotent" fun (gp : GenProgram) => checkMyPass gp.prog
```

`GenProgram` already has `Arbitrary`, `Repr` and `Shrinkable` instances.
`StrataGenerators.TestScaffold` holds them, and it stays the one source of truth for *how* a
draw, a reduction and the output work for each shape. `TestDecl.property` therefore needs
nothing from this module to run that property.

This module adds a fourth instance, `TycheFeatures`, which breaks a generated value into Tyche
axes. Those axes belong to the type and not to one property, because `num_decls`, `decl_kinds`,
`program_size` and `rejection_cause` are facts about a generated program, and each property
over `GenProgram` wants the same axes. One declaration here therefore gives a Tyche panel to a
property that someone writes later, and it lets a reader tell a vacuous draw from a live one.

The `Generators.*` values below are the same instances as `PropertyRunner` values. A property
needs one only to *differ* from the default of its type. See `PropertyRunner.withRender`,
`PropertyRunner.withFeatures` and `TestDecl.forAll`.
-/

open Lambda Core Imperative Plausible
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport

namespace StrataGenerators.Test.Generators

-- ── The features ──────────────────────────────────────────────────────
-- Each function below gives the axes for one input *type*. One declaration therefore serves
-- each panel over that type, and no new panel can miss an axis.

/-- The depth of the nested subexpressions of an expression. -/
private def exprDepth : LExpr' → Nat
  | .abs _ _ _ body => exprDepth body + 1
  | .app _ fn arg => max (exprDepth fn) (exprDepth arg) + 1
  | .ite _ c t e => max (exprDepth c) (max (exprDepth t) (exprDepth e)) + 1
  | .eq _ e₁ e₂ => max (exprDepth e₁) (exprDepth e₂) + 1
  | .quant _ _ _ _ tr body => max (exprDepth tr) (exprDepth body) + 1
  | _ => 0

/-- The name of the constructor at the top of an expression. -/
private def exprKind : LExpr' → String
  | .bvar _ _ => "bvar"
  | .fvar _ _ _ => "fvar"
  | .op _ _ _ => "op"
  | .abs _ _ _ _ => "abs"
  | .app _ _ _ => "app"
  | .ite _ _ _ _ => "ite"
  | .eq _ _ _ => "eq"
  | .const _ (.boolConst _) => "boolConst"
  | .const _ (.intConst _) => "intConst"
  | .const _ (.strConst _) => "strConst"
  | .const _ (.realConst _) => "realConst"
  | .const _ (.bitvecConst _ _) => "bitvecConst"
  | .quant _ _ _ _ _ _ => "quant"

/-- The name of the constructor at the top of a type. -/
def typeKind : LMonoTy → String
  | .bool => "bool"
  | .int => "int"
  | .arrow _ _ => "arrow"
  | .ftvar _ => "ftvar"
  | .bitvec _ => "bitvec"
  | .tcons _ _ => "tcons"

/-- The Tyche axes for an expression and the type of that expression. -/
def exprFeatures (e : LExpr') (τ : LMonoTy) : List (String × Tyche.Feature) :=
  [ ("expr_kind", .nominal (exprKind e)),
    ("type_kind", .nominal (typeKind τ)),
    ("expr_depth", .ordinal (exprDepth e)),
    ("expr_size", .ordinal (LExpr.size LExprParamsT' e)) ]

/-- The name of the constructor at the top of a command. For `init` and `set`, the name also
    gives whether the assignment is deterministic. -/
def cmdKind : Cmd Expression → String
  | .init _ _ (.det _) _ => "init_det"
  | .init _ _ .nondet _ => "init_nondet"
  | .set _ (.det _) _ => "set_det"
  | .set _ .nondet _ => "set_nondet"
  | .assert _ _ _ => "assert"
  | .assume _ _ _ => "assume"
  | .cover _ _ _ => "cover"

/-- Whether a generated function has a body, a measure, both or neither. A property is often
    vacuous when the function has neither, so this axis shows how often a draw was non-trivial. A
    function with a measure and no body is the counterexample to the completeness of the type
    checker. -/
private def funcShape (f : Function) : String :=
  match f.body.isSome, f.measure.isSome with
  | true,  true  => "body+measure"
  | true,  false => "body"
  | false, true  => "measure"
  | false, false => "neither"

/-- The Tyche axes for a generated function. -/
def functionFeatures (f : Function) : List (String × Tyche.Feature) :=
  [ ("func_shape", .nominal (funcShape f)),
    ("has_body", .nominal (if f.body.isSome then "yes" else "no")),
    ("has_measure", .nominal (if f.measure.isSome then "yes" else "no")),
    ("num_type_args", .ordinal f.typeArgs.length),
    ("num_inputs", .ordinal f.inputs.toList.length),
    ("output_kind", .nominal (typeKind f.output)) ]

/-- The Tyche axes for a list of generated statements. -/
def stmtsFeatures (ss : List Statement) : List (String × Tyche.Feature) :=
  [ ("num_stmts", .ordinal ss.length),
    ("ast_size", .ordinal (sizeStmts ss)),
    ("num_loops", .ordinal (countLoopsStmts ss)),
    ("num_exits", .ordinal (countExitStmts ss)),
    ("num_funcDecls", .ordinal (countFuncDeclStmts ss)),
    ("num_typeDecls", .ordinal (countTypeDeclStmts ss)),
    ("has_funcDecl", .nominal (if stmtsHaveFuncDecl ss then "yes" else "no")),
    ("top_kind", .nominal (match ss with | s :: _ => stmtKind s | [] => "empty")) ]

open StrataGenerators.Procedure.TestSupport in
/-- The Tyche axes for a list of generated procedures. -/
def procsFeatures (ps : List Core.Procedure) : List (String × Tyche.Feature) :=
  [ ("num_procs", .ordinal ps.length),
    ("total_body_stmts", .ordinal (ps.foldl (fun n p => n + (bodyStmts p.body).length) 0)) ]

/-- The kind of a declaration, as a name. -/
private def declKind : Core.Decl → String
  | .type (.con _) _ => "type.con"
  | .type (.syn _) _ => "type.syn"
  | .type (.data _) _ => "type.data"
  | .ax _ _ => "axiom"
  | .distinct _ _ _ => "distinct"
  | .proc _ _ => "proc"
  | .func _ _ => "func"
  | .recFuncBlock _ _ => "recFuncBlock"

/-- The Tyche axes for a generated program: the number of declarations, the size, the kinds of
    declaration that occur, and the documented gap of the type checker that the program holds.
    The last axis is what makes a panel for completeness readable. -/
def programFeatures (p : Core.Program) : List (String × Tyche.Feature) :=
  let causes := programRejectionCause p
  [ ("num_decls", .ordinal p.decls.length),
    ("program_size", .ordinal (sizeProgram p)),
    ("decl_kinds", .nominal (" ".intercalate (p.decls.map declKind).eraseDups)),
    ("rejection_cause", .nominal (if causes.isEmpty then "none" else "+".intercalate causes)) ]

open StrataGenerators.MutualBlockShape StrataGenerators.AdtLaws in
/-- The Tyche axes for a generated `mutual … end` datatype block. -/
def blockFeatures (b : Lambda.MutualDatatype Unit) : List (String × Tyche.Feature) :=
  [ ("num_datatypes", .ordinal b.length),
    ("num_constrs", .ordinal (b.foldl (fun n d => n + d.constrs.length) 0)),
    ("params_uniform", .nominal (if blockParamsUniform b then "yes" else "no")),
    ("independent", .nominal (if isIndependentBlock b then "yes" else "no")),
    ("addMutualBlock", .nominal (if blockAccepted b then "accepted" else "rejected")),
    ("smt_safe", .nominal (if blockIsSmtSafe b then "yes" else "no")) ]

-- ── The catalog ───────────────────────────────────────────────────────
--
-- There is one `TycheFeatures` instance for each input type, and then the same data as a
-- `PropertyRunner`. A property that accepts the default of its type names neither of them,
-- because `TestDecl.property` finds the instances. Almost every property does that.

section Instances
open StrataGenerators.Test

/-- The axes for a well-typed expression and its type. The generator uses `defaultFCtx`, so the
    expression can hold free variables. -/
instance : TycheFeatures TypedExpr := ⟨fun te => exprFeatures te.expr te.ty⟩

/-- The axes for a *closed* well-typed expression. Such an expression has no free variable, so
    the empty typing context is enough. Progress and preservation use this shape. -/
instance : TycheFeatures ClosedTypedExpr := ⟨fun te => exprFeatures te.expr te.ty⟩

/-- The axes for a closed expression over `coreOpCtx`, for the round trip through `eraseTypes`
    and `resolve`. -/
instance : TycheFeatures ResolveTypedExpr := ⟨fun te => exprFeatures te.expr te.ty⟩

/-- The axes for one command and the variable context that the generator used for it. -/
instance : TycheFeatures GenCmdWithCtx := ⟨fun gc =>
  [ ("cmd_kind", .nominal (cmdKind gc.cmd)),
    ("in_ctx_size", .ordinal gc.inCtx.length),
    ("out_ctx_size", .ordinal gc.outCtx.length) ]⟩

/-- The axes for a *sequence* of commands and its input and output contexts. -/
instance : TycheFeatures GenCmdsWithCtx := ⟨fun gc =>
  [ ("num_cmds", .ordinal gc.cmds.length),
    ("in_ctx_size", .ordinal gc.inCtx.length),
    ("out_ctx_size", .ordinal gc.outCtx.length) ]⟩

/-- The axes for a function that the generator draws against `defaultFCtx`. The value also holds
    that context, so a property can read the matching type map. -/
instance : TycheFeatures GenFunction := ⟨fun gf => functionFeatures gf.func⟩

/-- The axes for a function with a *closed* body. `Function.typeCheck` accepts such a function
    without an ambient context. -/
instance : TycheFeatures ClosedGenFunction := ⟨fun gf => functionFeatures gf.func⟩

/-- The axes for a well-typed list of statements, which the relation `StatementsHasTypeA`
    describes. The generator is sound *and* complete against the declarative specification, so
    its output is an input with a certificate for an oracle. -/
instance : TycheFeatures GenStmts := ⟨fun gs => stmtsFeatures gs.stmts⟩

/-- The axes for a list of well-typed procedures that form an acyclic call graph. The generator
    gives them the names `P0` to `Pk`, so two identities never collide. -/
instance : TycheFeatures GenProcs := ⟨fun gp => procsFeatures gp.procs⟩

/-- The axes for a whole well-typed program. Such a program holds every kind of declaration, and
    the generator threads the ambient context through the fold over the declarations. This is the
    best input for a property that reads more than one declaration. -/
instance : TycheFeatures GenProgram := ⟨fun gp => programFeatures gp.prog⟩

/-- The axes for a `mutual … end` datatype block of the ordinary shape, which is usually
    connected. -/
instance : TycheFeatures GenAdtBlock := ⟨fun gb => blockFeatures gb.block⟩

/-- The axes for a `mutual … end` block whose datatypes are pairwise *independent*. The generator
    draws each datatype on its own, and it threads one set of reserved names through the draws, so
    no field can mention a sibling datatype. -/
instance : TycheFeatures GenIndepBlock := ⟨fun gb => blockFeatures gb.block⟩

end Instances

-- The same runners as first-class values, for a property that must differ from the default.
-- `Generators.program.withRender …` keeps each axis and it changes only the printer.

open StrataGenerators.Test in
def typedExpr      : PropertyRunner TypedExpr        := .ofInstances _
open StrataGenerators.Test in
def closedExpr     : PropertyRunner ClosedTypedExpr  := .ofInstances _
open StrataGenerators.Test in
def resolveExpr    : PropertyRunner ResolveTypedExpr := .ofInstances _
open StrataGenerators.Test in
def cmd            : PropertyRunner GenCmdWithCtx    := .ofInstances _
open StrataGenerators.Test in
def cmds           : PropertyRunner GenCmdsWithCtx   := .ofInstances _
open StrataGenerators.Test in
def function       : PropertyRunner GenFunction      := .ofInstances _
open StrataGenerators.Test in
def closedFunction : PropertyRunner ClosedGenFunction := .ofInstances _
open StrataGenerators.Test in
def stmts          : PropertyRunner GenStmts         := .ofInstances _
open StrataGenerators.Test in
def procs          : PropertyRunner GenProcs         := .ofInstances _
open StrataGenerators.Test in
def program        : PropertyRunner GenProgram       := .ofInstances _
open StrataGenerators.Test in
def adtBlock       : PropertyRunner GenAdtBlock      := .ofInstances _
open StrataGenerators.Test in
def indepBlock     : PropertyRunner GenIndepBlock    := .ofInstances _

end StrataGenerators.Test.Generators
