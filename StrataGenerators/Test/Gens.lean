import StrataGenerators.TestScaffold
import StrataGenerators.Test.Types

/-!
# The generator catalog

One `GenSpec` per input type the suite generates. A property picks its input by
naming one of these:

```lean
@[strata_property]
def myProp : TestDecl :=
  .property "mypass: idempotent" "mypass" Gens.program checkMyPass
```

Each entry is `GenSpec.ofInstances` over a wrapper type that already carries
`Arbitrary`/`Repr`/`Shrinkable` (they live in `StrataGenerators.TestScaffold`,
which stays the single source of truth for *how* each shape is drawn, shrunk and
printed), plus the Tyche breakdown for that shape.

The breakdown belongs to the generator, not to the property: `num_decls`,
`decl_kinds`, `program_size` and `rejection_cause` are facts about a generated
program, and every property drawn from `Gens.program` wants the same axes. That is
what makes a Tyche panel free for a newly written property — the axes that tell a
vacuous draw from a live one are already attached to the input it draws from.

A new generator is a new entry here, or — since nothing in this module is
privileged — a `GenSpec` defined in the property's own file.
-/

open Lambda Core Imperative Plausible
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport

namespace StrataGenerators.Test.Gens

-- ── Feature extraction ────────────────────────────────────────────────
-- Ported from the hand-written panels of `StrataGenerators.TycheViz`, where each
-- of these was duplicated across the panels of one input shape. Attaching them to
-- the generator instead removes the duplication *and* the possibility of a new
-- panel forgetting an axis.

/-- Nesting depth of an expression. -/
private def exprDepth : LExpr' → Nat
  | .abs _ _ _ body => exprDepth body + 1
  | .app _ fn arg => max (exprDepth fn) (exprDepth arg) + 1
  | .ite _ c t e => max (exprDepth c) (max (exprDepth t) (exprDepth e)) + 1
  | .eq _ e₁ e₂ => max (exprDepth e₁) (exprDepth e₂) + 1
  | .quant _ _ _ _ tr body => max (exprDepth tr) (exprDepth body) + 1
  | _ => 0

/-- Top-level expression constructor. -/
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

/-- Top-level type constructor. -/
def typeKind : LMonoTy → String
  | .bool => "bool"
  | .int => "int"
  | .arrow _ _ => "arrow"
  | .ftvar _ => "ftvar"
  | .bitvec _ => "bitvec"
  | .tcons _ _ => "tcons"

private def exprFeatures (e : LExpr') (τ : LMonoTy) : List (String × Tyche.Feature) :=
  [ ("expr_kind", .nominal (exprKind e)),
    ("type_kind", .nominal (typeKind τ)),
    ("expr_depth", .ordinal (exprDepth e)),
    ("expr_size", .ordinal (LExpr.size LExprParamsT' e)) ]

/-- Top-level command constructor. -/
private def cmdKind : Cmd Expression → String
  | .init _ _ (.det _) _ => "init_det"
  | .init _ _ .nondet _ => "init_nondet"
  | .set _ (.det _) _ => "set_det"
  | .set _ .nondet _ => "set_nondet"
  | .assert _ _ _ => "assert"
  | .assume _ _ _ => "assume"
  | .cover _ _ _ => "cover"

/-- Whether a generated function has a body and/or a measure. The property under
    test is often vacuous when both are absent, so this is the axis that shows how
    often it was exercised non-trivially — and `measure` alone is precisely the
    typechecker-completeness counterexample. -/
private def funcShape (f : Function) : String :=
  match f.body.isSome, f.measure.isSome with
  | true,  true  => "body+measure"
  | true,  false => "body"
  | false, true  => "measure"
  | false, false => "neither"

private def functionFeatures (f : Function) : List (String × Tyche.Feature) :=
  [ ("func_shape", .nominal (funcShape f)),
    ("has_body", .nominal (if f.body.isSome then "yes" else "no")),
    ("has_measure", .nominal (if f.measure.isSome then "yes" else "no")),
    ("num_type_args", .ordinal f.typeArgs.length),
    ("num_inputs", .ordinal f.inputs.toList.length),
    ("output_kind", .nominal (typeKind f.output)) ]

private def stmtsFeatures (ss : List Statement) : List (String × Tyche.Feature) :=
  [ ("num_stmts", .ordinal ss.length),
    ("ast_size", .ordinal (sizeStmts ss)),
    ("num_loops", .ordinal (countLoopsStmts ss)),
    ("num_exits", .ordinal (countExitStmts ss)),
    ("num_funcDecls", .ordinal (countFuncDeclStmts ss)),
    ("num_typeDecls", .ordinal (countTypeDeclStmts ss)),
    ("has_funcDecl", .nominal (if stmtsHaveFuncDecl ss then "yes" else "no")),
    ("top_kind", .nominal (match ss with | s :: _ => stmtKind s | [] => "empty")) ]

open StrataGenerators.Procedure.TestSupport in
private def procsFeatures (ps : List Core.Procedure) : List (String × Tyche.Feature) :=
  [ ("num_procs", .ordinal ps.length),
    ("total_body_stmts", .ordinal (ps.foldl (fun n p => n + (bodyStmts p.body).length) 0)) ]

private def declKind : Core.Decl → String
  | .type (.con _) _ => "type.con"
  | .type (.syn _) _ => "type.syn"
  | .type (.data _) _ => "type.data"
  | .ax _ _ => "axiom"
  | .distinct _ _ _ => "distinct"
  | .proc _ _ => "proc"
  | .func _ _ => "func"
  | .recFuncBlock _ _ => "recFuncBlock"

/-- Declaration count, reducible size, which declaration kinds are present, and —
    the axis that makes the completeness panels legible — which documented
    typechecker gap (if any) the program bears. -/
private def programFeatures (p : Core.Program) : List (String × Tyche.Feature) :=
  let causes := programRejectionCause p
  [ ("num_decls", .ordinal p.decls.length),
    ("program_size", .ordinal (sizeProgram p)),
    ("decl_kinds", .nominal (" ".intercalate (p.decls.map declKind).eraseDups)),
    ("rejection_cause", .nominal (if causes.isEmpty then "none" else "+".intercalate causes)) ]

open StrataGenerators.MutualBlockShape StrataGenerators.AdtLaws in
private def blockFeatures (b : Lambda.MutualDatatype Unit) : List (String × Tyche.Feature) :=
  [ ("num_datatypes", .ordinal b.length),
    ("num_constrs", .ordinal (b.foldl (fun n d => n + d.constrs.length) 0)),
    ("params_uniform", .nominal (if blockParamsUniform b then "yes" else "no")),
    ("independent", .nominal (if isIndependentBlock b then "yes" else "no")),
    ("addMutualBlock", .nominal (if blockAccepted b then "accepted" else "rejected")),
    ("smt_safe", .nominal (if blockIsSmtSafe b then "yes" else "no")) ]

-- ── The catalog ───────────────────────────────────────────────────────

/-- A well-typed expression paired with its type, over `defaultFCtx` (so it may
    contain free variables). -/
def typedExpr : GenSpec TypedExpr :=
  .ofInstances "typed expression" _ (fun te => exprFeatures te.expr te.ty)

/-- A *closed* well-typed expression: no free variables, so the empty typing
    context suffices (what progress and preservation are stated against). -/
def closedExpr : GenSpec ClosedTypedExpr :=
  .ofInstances "closed typed expression" _ (fun te => exprFeatures te.expr te.ty)

/-- A closed expression over `coreOpCtx`, for round-tripping through `eraseTypes`
    and `resolve`. -/
def resolveExpr : GenSpec ResolveTypedExpr :=
  .ofInstances "resolvable typed expression" _ (fun te => exprFeatures te.expr te.ty)

/-- One command, paired with the variable context it was generated against. -/
def cmd : GenSpec GenCmdWithCtx :=
  .ofInstances "command" _ (fun gc =>
    [ ("cmd_kind", .nominal (cmdKind gc.cmd)),
      ("in_ctx_size", .ordinal gc.inCtx.length),
      ("out_ctx_size", .ordinal gc.outCtx.length) ])

/-- A command *sequence*, paired with its input and output contexts. -/
def cmds : GenSpec GenCmdsWithCtx :=
  .ofInstances "command sequence" _ (fun gc =>
    [ ("num_cmds", .ordinal gc.cmds.length),
      ("in_ctx_size", .ordinal gc.inCtx.length),
      ("out_ctx_size", .ordinal gc.outCtx.length) ])

/-- A function generated against `defaultFCtx`, carrying that context so a
    property can consult the matching type map. -/
def function : GenSpec GenFunction :=
  .ofInstances "function" _ (fun gf => functionFeatures gf.func)

/-- A function with a *closed* body, which `Function.typeCheck` can accept without
    an ambient context. -/
def closedFunction : GenSpec ClosedGenFunction :=
  .ofInstances "closed function" _ (fun gf => functionFeatures gf.func)

/-- A well-typed statement list (`StatementsHasTypeA`: proven sound *and* complete
    against the declarative spec, so it is a certified oracle input). -/
def stmts : GenSpec GenStmts :=
  .ofInstances "statement list" _ (fun gs => stmtsFeatures gs.stmts)

/-- A list of well-typed procedures forming an acyclic call DAG, relabelled
    `P0…Pk` so their identities never collide. -/
def procs : GenSpec GenProcs :=
  .ofInstances "procedure list" _ (fun gp => procsFeatures gp.procs)

/-- A whole well-typed program: every declaration kind, with the ambient context
    threaded across the declaration fold. The input of choice for anything that
    reads more than one declaration. -/
def program : GenSpec GenProgram :=
  .ofInstances "program" _ (fun gp => programFeatures gp.prog)

/-- A `mutual … end` datatype block of the ordinary (usually connected) shape. -/
def adtBlock : GenSpec GenAdtBlock :=
  .ofInstances "datatype block" _ (fun gb => blockFeatures gb.block)

/-- A `mutual … end` block whose datatypes are pairwise *independent*: drawn
    separately over a threaded reserved-name set, so no field can mention a
    sibling. -/
def indepBlock : GenSpec GenIndepBlock :=
  .ofInstances "independent datatype block" _ (fun gb => blockFeatures gb.block)

end StrataGenerators.Test.Gens
