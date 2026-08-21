import StrataGenerators.TestScaffold
import StrataGenerators.Test.Types
import StrataGenerators.TuningProfiles
import StrataGenerators.ProgramTuning

/-!
# The generator catalog

A property picks its generator the way Plausible and QuickCheck do: by the **type** of
the value it quantifies over.

```lean
@[strata_property]
def myProp : TestDecl :=
  .property "mypass: idempotent" fun (gp : GenProgram) => checkMyPass gp.prog
```

`GenProgram` already carries `Arbitrary`/`Repr`/`Shrinkable` instances — they live in
`StrataGenerators.TestScaffold`, which stays the single source of truth for *how* each
shape is drawn, shrunk and printed — so `TestDecl.property` needs nothing from this
module in order to run that property.

What this module adds is a fourth instance: `TycheFeatures`, the breakdown of a
generated value into Tyche axes. That belongs to the type rather than to any one
property, because `num_decls`, `decl_kinds`, `program_size` and `rejection_cause` are
facts about a generated program, and every property over `GenProgram` wants the same
axes. Declaring them once here is what makes a Tyche panel free for a property written
later, and what lets a reader tell a vacuous draw from a live one.

The `Generators.*` values below are those same instances reified as `PropertyRunner`s.
A property needs one only in order to *deviate* from the type's default — see
`PropertyRunner.withRender`, `PropertyRunner.withFeatures` and `TestDecl.forAll`.
-/

open Lambda Core Imperative Plausible
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Program.TestSupport
open ProgramGen.TestSupport

namespace StrataGenerators.Test.Generators

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
-- `PropertyRunner`. A property content with the type's default — almost every
-- property — mentions neither: `TestDecl.property` finds the instances.

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

-- The same runners as first-class values, for a property that needs to deviate from the
-- default: `Generators.program.withRender …` keeps every axis and changes the printer.

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

-- ── Tunable generators ────────────────────────────────────────────────
--
-- One instance per input type whose generator's branch weights can be set at run time,
-- which is what `TestDecl.tuned` / `TestDecl.underTunings` need. Each is the sampler
-- above with the tuned entry point substituted for the shipping one — same `size`/`len`
-- schedule, same operator contexts, same `retryGen` budget — so `genWith defaults` is the
-- type's `Arbitrary` instance and a tuned property differs only in the distribution. The
-- wrappers, and the proof that no `θ` changes what is reachable, are in
-- `StrataGenerators.TuningProfiles` and `StrataGenerators.SetGen.TuningPrototypes`.
--
-- An instance here is what makes a *profile* reach the properties it was written for, so the list
-- tracks the input types the tuned families quantify over rather than the generators alone: both
-- command shapes, and all three expression shapes.
--
-- A type absent from this list cannot be tuned: `GenFunction`, `GenAdtBlock` and `GenIndepBlock`
-- draw through generators whose weights are not yet exposed, so `TestDecl.tuned` on one of them is
-- a missing-instance error rather than a silent no-op.

section Tunable
open StrataGenerators.Test StrataGenerators.TuningProfiles
open StrataGenerators.ProgramTuning
open StrataGenerators.Procedure.TestSupport (relabelProcs)

/-- Statement lists, with `genStmt`'s branch weights read from `θ` — threaded through the
    whole mutual recursion, so statements nested in a `block`/`ite`/`loop` body are tuned
    too. `stmtLoopHeavy` and friends address this. -/
instance : TunableGen GenStmts where
  genWith θ := retryGen 4000 <| Gen.sized fun s => do
    let size := max 1 (min 3 (s / 25))
    let len := max 1 (min 4 (s / 20))
    let (ss, _, _) ← genProgramStmtsT (G := Plausible.Gen) θ coreMonoOps [] size len
    pure ⟨ss⟩
  sites := StrataGenerators.Stmt.genStmt._mutual.sites

/-- Procedure lists, with the statement weights of each *body* read from `θ`. The three
    transform passes key on what those bodies contain, so this is the instance the
    `proc:` properties tune through. -/
instance : TunableGen GenProcs where
  genWith θ := retryGen 8000 <| Gen.sized fun s => do
    let n := max 2 (min 4 (2 + s / 30))
    let size := max 1 (min 2 (s / 30))
    let len := max 1 (min 3 (s / 25))
    let (ps, _) ← (List.range n).foldlM
      (fun (acc : List Core.Procedure × StrataGenerators.Stmt.ProcSigCtx) (i : Nat) => do
        let proc ← (retryGen 8000 (genProcedureT (G := Plausible.Gen) θ
          corePartialOps acc.2 LContext.default {} size len) : Gen Core.Procedure)
        let sigs := acc.2 ++ [StrataGenerators.Procedure.headerProcSig s!"P{i}" proc.header]
        pure (acc.1 ++ [proc], sigs))
      (([], []) : List Core.Procedure × StrataGenerators.Stmt.ProcSigCtx)
    pure ⟨relabelProcs ps⟩
  sites := StrataGenerators.Stmt.genStmt._mutual.sites

/-- Command sequences, with `genCmd`'s branch weights read from `θ` (`cmdSetHeavy`,
    `cmdInitHeavy`, `cmdCheckHeavy`). -/
instance : TunableGen GenCmdsWithCtx where
  genWith θ := retryGen 1000 <| do
    let (cmds, ctx') ← genCmdsT (G := Plausible.Gen) θ coreMonoOps [] [] [] 2 4
    pure ⟨cmds, [], ctx'⟩
  sites := genCmd.sites

/-- One command drawn against a context a first chain built, with `genCmd`'s branch weights read
    from `θ`. This is the shape four of the five `cmd:` properties quantify over — including the two
    `cmdSetHeavy` exists for, since `set` is offered only by the site reached when something in the
    context is writable, and an empty context reaches the other one. -/
instance : TunableGen GenCmdWithCtx where
  genWith θ := retryGen 1000 <| do
    let (_, baseCtx) ← genCmdsT (G := Plausible.Gen) θ coreMonoOps [] [] [] 2 3
    let ⟨cmd, ctx'⟩ ← genCmd.tuned (G := Plausible.Gen) θ coreMonoOps [] [] baseCtx 2 []
    pure ⟨cmd, baseCtx, ctx'⟩
  sites := genCmd.sites

/-- Typed expressions over `defaultFCtx`, with `genLExprBase`'s 79 branch weights read from `θ`
    (`exprEvalHeavy`, `exprQuantHeavy`, `exprIndirHeavy`, `exprFVarHeavy`).

    Drawn through `genLExprWithOpsT`, the tuned restatement of the entry point `Arbitrary` uses —
    root Indir/IndirPoly `frequency` and per-subterm `retryGenArg` continuation included, which is
    what makes the pin below hold and keeps a tuned property's cost the same as the untuned one's. -/
instance : TunableGen TypedExpr where
  genWith θ := retryGen 500 <| Gen.sized fun s => do
    let depth := max 1 (s / 20)
    let τ ← genLMonoTy (G := Plausible.Gen) [] depth
    let e ← genLExprT (G := Plausible.Gen) θ defaultFCtx coreMonoOps corePolyOps [] []
      depth τ 3 (retryGenArg 20)
    pure ⟨e, τ⟩
  sites := genLExprBase.sites

/-- The same over the *empty* fvar context: the shape `expr: preservation` and `expr: progress`
    quantify over, and hence what `exprEvalHeavy`/`exprQuantHeavy`/`exprIndirHeavy` have to act on
    to reach the properties their docstrings name. -/
instance : TunableGen ClosedTypedExpr where
  genWith θ := retryGen 500 <|
    (fun (te : TypedExpr) => (⟨te.expr, te.ty⟩ : ClosedTypedExpr)) <$> (Gen.sized fun s => do
      let depth := max 1 (s / 20)
      let τ ← genLMonoTy (G := Plausible.Gen) [] depth
      let e ← genLExprT (G := Plausible.Gen) θ [] coreMonoOps corePolyOps [] []
        depth τ 3 (retryGenArg 20)
      pure (⟨e, τ⟩ : TypedExpr))
  sites := genLExprBase.sites

/-- Whole programs, with `genDeclStep`'s declaration-kind weights read from `θ`
    (`progPolyHeavy`, `progDatatypeHeavy`). This is the instance the `mono:` family tunes
    through: how many polymorphic functions and polymorphic datatype blocks a program declares is
    what decides whether `MonomorphizeFunctions` has anything to specialize. -/
instance : TunableGen GenProgram where
  genWith θ := retryGen 8000 <| Gen.sized fun s => do
    let numDecls := max 2 (min 5 (2 + s / 25))
    let prog ← (retryGen 30000 (genProgramT (G := Plausible.Gen) θ numDecls {})
      : Gen Core.Program)
    pure ⟨prog⟩
  sites := progSites

/-- The same over `coreOpCtx` and no polymorphic operators: the shape
    `expr: resolve after type erasure` quantifies over, which is the second property
    `exprQuantHeavy` is for. -/
instance : TunableGen ResolveTypedExpr where
  genWith θ := retryGen 500 <| Gen.sized fun s => do
    let depth := max 1 (s / 20)
    let τ ← genLMonoTy (G := Plausible.Gen) [] depth
    let e ← genLExprT (G := Plausible.Gen) θ [] coreOpCtx [] [] [] depth τ 3 (retryGenArg 20)
    pure ⟨e, τ⟩
  sites := genLExprBase.sites

/-! **Tuning is opt-in.** At a generator's own `.defaults` the tuned sampler is the type's
`Arbitrary` instance, so `underTunings`'s "default" row is the property `TestDecl.property` would
have registered, and adding a tuned row cannot perturb the untuned one. Every instance above is
pinned, so a wrapper that drifts from the generator it claims to wrap fails the build here. -/

example : TunableGen.genWith (α := GenStmts) stmtDefault = Arbitrary.arbitrary := by
  simp only [TunableGen.genWith, genProgramStmtsT_defaults]; rfl
example : TunableGen.genWith (α := GenProcs) stmtDefault = Arbitrary.arbitrary := by
  simp only [TunableGen.genWith, genProcedureT_defaults]; rfl
example : TunableGen.genWith (α := GenCmdsWithCtx) cmdDefault = Arbitrary.arbitrary := by
  simp only [TunableGen.genWith, genCmdsT_defaults]; rfl
example : TunableGen.genWith (α := GenCmdWithCtx) cmdDefault = Arbitrary.arbitrary := by
  simp only [TunableGen.genWith, cmdDefault, genCmd.tuned_defaults]; rfl
example : TunableGen.genWith (α := TypedExpr) exprBreadth = Arbitrary.arbitrary := by
  simp only [TunableGen.genWith, genLExprT_defaults]; rfl
example : TunableGen.genWith (α := ClosedTypedExpr) exprBreadth = Arbitrary.arbitrary := by
  simp only [TunableGen.genWith, genLExprT_defaults]; rfl
example : TunableGen.genWith (α := ResolveTypedExpr) exprBreadth = Arbitrary.arbitrary := by
  simp only [TunableGen.genWith, genLExprT_defaults]; rfl
example : TunableGen.genWith (α := GenProgram) progDefault = Arbitrary.arbitrary := by
  simp only [TunableGen.genWith, genProgramT_defaults]; rfl

/-! The arity a hand-built tuning must match. `TestDecl.withTuning` checks a `θ` against it, so a
tuning meant for another generator is a red line naming both numbers rather than a silent
reindexing. -/
example : TunableGen.arity GenStmts = 14 := rfl
example : TunableGen.arity GenProcs = 14 := rfl
example : TunableGen.arity GenCmdsWithCtx = 12 := rfl
example : TunableGen.arity GenCmdWithCtx = 12 := rfl
example : TunableGen.arity TypedExpr = 79 := rfl
example : TunableGen.arity ClosedTypedExpr = 79 := rfl
example : TunableGen.arity ResolveTypedExpr = 79 := rfl
example : TunableGen.arity GenProgram = 9 := rfl

end Tunable

end StrataGenerators.Test.Generators
