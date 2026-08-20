import StrataGenerators.TestScaffold
import StrataGenerators.Test.Types

/-!
# The generator catalog

A property picks its generator the way Plausible and QuickCheck do: by the **type** of
the value it quantifies over.

```lean
@[strata_property]
def myProp : TestDecl :=
  .forAll "mypass: idempotent" "mypass" fun (gp : GenProgram) => checkMyPass gp.prog
```

`GenProgram` already carries `Arbitrary`/`Repr`/`Shrinkable` instances — they live in
`StrataGenerators.TestScaffold`, which stays the single source of truth for *how* each
shape is drawn, shrunk and printed — so `TestDecl.forAll` needs nothing from this
module in order to run that property.

What this module adds is a fourth instance: `TycheFeatures`, the breakdown of a
generated value into Tyche axes. That belongs to the type rather than to any one
property, because `num_decls`, `decl_kinds`, `program_size` and `rejection_cause` are
facts about a generated program, and every property over `GenProgram` wants the same
axes. Declaring them once here is what makes a Tyche panel free for a property written
later, and what lets a reader tell a vacuous draw from a live one.

The `Gens.*` values below are those same instances reified as `GenSpec`s. A property
needs one only in order to *deviate* from the type's default generator — see
`GenSpec.withRender`, `GenSpec.withFeatures` and `TestDecl.property`.
-/

open Lambda Core Imperative Plausible
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport

namespace StrataGenerators.Test.Gens

-- ── Feature extraction ────────────────────────────────────────────────
-- Ported from the hand-written panels of `StrataGenerators.TycheViz`, where each
-- of these was duplicated across the panels of one input shape. Attaching them to
-- the *type* instead removes the duplication and the possibility of a new panel
-- forgetting an axis.

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

def exprFeatures (e : LExpr') (τ : LMonoTy) : List (String × Tyche.Feature) :=
  [ ("expr_kind", .nominal (exprKind e)),
    ("type_kind", .nominal (typeKind τ)),
    ("expr_depth", .ordinal (exprDepth e)),
    ("expr_size", .ordinal (LExpr.size LExprParamsT' e)) ]

/-- Top-level command constructor. -/
def cmdKind : Cmd Expression → String
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

def functionFeatures (f : Function) : List (String × Tyche.Feature) :=
  [ ("func_shape", .nominal (funcShape f)),
    ("has_body", .nominal (if f.body.isSome then "yes" else "no")),
    ("has_measure", .nominal (if f.measure.isSome then "yes" else "no")),
    ("num_type_args", .ordinal f.typeArgs.length),
    ("num_inputs", .ordinal f.inputs.toList.length),
    ("output_kind", .nominal (typeKind f.output)) ]

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
def procsFeatures (ps : List Core.Procedure) : List (String × Tyche.Feature) :=
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
def programFeatures (p : Core.Program) : List (String × Tyche.Feature) :=
  let causes := programRejectionCause p
  [ ("num_decls", .ordinal p.decls.length),
    ("program_size", .ordinal (sizeProgram p)),
    ("decl_kinds", .nominal (" ".intercalate (p.decls.map declKind).eraseDups)),
    ("rejection_cause", .nominal (if causes.isEmpty then "none" else "+".intercalate causes)) ]

open StrataGenerators.MutualBlockShape StrataGenerators.AdtLaws in
def blockFeatures (b : Lambda.MutualDatatype Unit) : List (String × Tyche.Feature) :=
  [ ("num_datatypes", .ordinal b.length),
    ("num_constrs", .ordinal (b.foldl (fun n d => n + d.constrs.length) 0)),
    ("params_uniform", .nominal (if blockParamsUniform b then "yes" else "no")),
    ("independent", .nominal (if isIndependentBlock b then "yes" else "no")),
    ("addMutualBlock", .nominal (if blockAccepted b then "accepted" else "rejected")),
    ("smt_safe", .nominal (if blockIsSmtSafe b then "yes" else "no")) ]

-- ── The catalog ───────────────────────────────────────────────────────
--
-- One `TycheFeatures` instance per input type, then the same thing reified as a
-- `GenSpec`. A property that is content with the type's default generator — almost
-- every property — mentions neither: `TestDecl.forAll` finds the instances.

section Instances
open StrataGenerators.Test

/-- A well-typed expression paired with its type, over `defaultFCtx` (so it may
    contain free variables). -/
instance : TycheFeatures TypedExpr := ⟨fun te => exprFeatures te.expr te.ty⟩

/-- A *closed* well-typed expression: no free variables, so the empty typing context
    suffices (what progress and preservation are stated against). -/
instance : TycheFeatures ClosedTypedExpr := ⟨fun te => exprFeatures te.expr te.ty⟩

/-- A closed expression over `coreOpCtx`, for round-tripping through `eraseTypes` and
    `resolve`. -/
instance : TycheFeatures ResolveTypedExpr := ⟨fun te => exprFeatures te.expr te.ty⟩

/-- One command, paired with the variable context it was generated against. -/
instance : TycheFeatures GenCmdWithCtx := ⟨fun gc =>
  [ ("cmd_kind", .nominal (cmdKind gc.cmd)),
    ("in_ctx_size", .ordinal gc.inCtx.length),
    ("out_ctx_size", .ordinal gc.outCtx.length) ]⟩

/-- A command *sequence*, paired with its input and output contexts. -/
instance : TycheFeatures GenCmdsWithCtx := ⟨fun gc =>
  [ ("num_cmds", .ordinal gc.cmds.length),
    ("in_ctx_size", .ordinal gc.inCtx.length),
    ("out_ctx_size", .ordinal gc.outCtx.length) ]⟩

/-- A function generated against `defaultFCtx`, carrying that context so a property
    can consult the matching type map. -/
instance : TycheFeatures GenFunction := ⟨fun gf => functionFeatures gf.func⟩

/-- A function with a *closed* body, which `Function.typeCheck` can accept without an
    ambient context. -/
instance : TycheFeatures ClosedGenFunction := ⟨fun gf => functionFeatures gf.func⟩

/-- A well-typed statement list (`StatementsHasTypeA`: proven sound *and* complete
    against the declarative spec, so it is a certified oracle input). -/
instance : TycheFeatures GenStmts := ⟨fun gs => stmtsFeatures gs.stmts⟩

/-- A list of well-typed procedures forming an acyclic call DAG, relabelled `P0…Pk` so
    their identities never collide. -/
instance : TycheFeatures GenProcs := ⟨fun gp => procsFeatures gp.procs⟩

/-- A whole well-typed program: every declaration kind, with the ambient context
    threaded across the declaration fold. The input of choice for anything that reads
    more than one declaration. -/
instance : TycheFeatures GenProgram := ⟨fun gp => programFeatures gp.prog⟩

/-- A `mutual … end` datatype block of the ordinary (usually connected) shape. -/
instance : TycheFeatures GenAdtBlock := ⟨fun gb => blockFeatures gb.block⟩

/-- A `mutual … end` block whose datatypes are pairwise *independent*: drawn separately
    over a threaded reserved-name set, so no field can mention a sibling. -/
instance : TycheFeatures GenIndepBlock := ⟨fun gb => blockFeatures gb.block⟩

end Instances

-- The same generators as first-class values, for a property that needs to deviate from
-- the default: `Gens.program.withRender …` keeps every axis and changes the rendering.

open StrataGenerators.Test in
def typedExpr      : GenSpec TypedExpr        := .ofInstances _
open StrataGenerators.Test in
def closedExpr     : GenSpec ClosedTypedExpr  := .ofInstances _
open StrataGenerators.Test in
def resolveExpr    : GenSpec ResolveTypedExpr := .ofInstances _
open StrataGenerators.Test in
def cmd            : GenSpec GenCmdWithCtx    := .ofInstances _
open StrataGenerators.Test in
def cmds           : GenSpec GenCmdsWithCtx   := .ofInstances _
open StrataGenerators.Test in
def function       : GenSpec GenFunction      := .ofInstances _
open StrataGenerators.Test in
def closedFunction : GenSpec ClosedGenFunction := .ofInstances _
open StrataGenerators.Test in
def stmts          : GenSpec GenStmts         := .ofInstances _
open StrataGenerators.Test in
def procs          : GenSpec GenProcs         := .ofInstances _
open StrataGenerators.Test in
def program        : GenSpec GenProgram       := .ofInstances _
open StrataGenerators.Test in
def adtBlock       : GenSpec GenAdtBlock      := .ofInstances _
open StrataGenerators.Test in
def indepBlock     : GenSpec GenIndepBlock    := .ofInstances _

end StrataGenerators.Test.Gens
