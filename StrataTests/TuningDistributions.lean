import StrataGenerators.Test
import StrataGenerators.TycheViz
import StrataGenerators.DistReport

/-!
# The distributions of the expression and statement generators under each tuning

One Tyche panel per profile in `StrataGenerators.DistReport`'s `exprProfiles` (closed rows),
`stmtProfiles` and `cmdProfiles`, each sampled as `dist-report` samples it, and one per expression profile
and fixed target type in `fixedTypes`. The features count every node of a sample by
constructor, and `size` counts a sample's nodes, so a panel shows how a profile moves the generator's
distribution.
-/

open Lambda Core Imperative
open StrataGenerators.Test StrataGenerators.DistReport StrataGenerators.TuningProfiles
open StrataGenerators.Stmt.TestSupport

namespace StrataTests.TuningDistributions

/-- The constructor of every node of an expression, in preorder. -/
partial def exprNodeKinds (e : LExpr') : List String :=
  exprKind e :: match e with
    | .abs _ _ _ b => exprNodeKinds b
    | .app _ f a => exprNodeKinds f ++ exprNodeKinds a
    | .ite _ c t f => exprNodeKinds c ++ exprNodeKinds t ++ exprNodeKinds f
    | .eq _ a b => exprNodeKinds a ++ exprNodeKinds b
    | .quant _ _ _ _ tr b => exprNodeKinds tr ++ exprNodeKinds b
    | _ => []

/-- The kind of a statement, with a procedure `call` told apart from the other commands. -/
def stmtNodeKind (s : Statement) : String :=
  if isCallStmt s then "call" else stmtKind s

/-- The kind of every statement node of a list, in preorder. -/
partial def stmtNodeKinds (ss : List Statement) : List String :=
  ss.flatMap fun s => stmtNodeKind s :: match s with
    | .block _ body _ => stmtNodeKinds body
    | .ite _ t e _ => stmtNodeKinds t ++ stmtNodeKinds e
    | .loop _ _ _ body _ => stmtNodeKinds body
    | _ => []

/-- One ordinal feature `n_<kind>` per kind in `kinds`: the number of nodes of that kind. -/
def countFeatures (kinds : List String) (nodes : List String) : List (String × Tyche.Feature) :=
  kinds.map fun k => (s!"n_{k}", .ordinal (nodes.count k))

/-- The expression nodes of a deterministic right-hand side or guard. -/
def eonSize : ExprOrNondet Expression → Nat
  | .det e => exprSize e
  | .nondet => 0

/-- One node for the command, plus the nodes of its expression. -/
def cmdSize : Cmd Expression → Nat
  | .init _ _ e _ | .set _ e _ => 1 + eonSize e
  | .assert _ b _ | .assume _ b _ | .cover _ b _ => 1 + exprSize b

/-- One node per statement, plus the expression nodes of its commands, guards, measures and
    invariants. A `funcDecl` counts as one node: its body is not a statement. -/
partial def stmtSize : Statement → Nat
  | .cmd (.cmd c) => cmdSize c
  | .cmd _ => 1
  | .block _ b _ => 1 + (b.map stmtSize).sum
  | .ite c t e _ => 1 + eonSize c + (t.map stmtSize).sum + (e.map stmtSize).sum
  | .loop g m inv b _ =>
    1 + eonSize g + (m.map exprSize).getD 0 + (inv.map (exprSize ·.2)).sum + (b.map stmtSize).sum
  | _ => 1

def exprKinds : List String :=
  ["app", "abs", "ite", "eq", "quant", "op", "bvar", "fvar",
   "boolConst", "intConst", "strConst", "realConst", "bitvecConst"]

def stmtKinds : List String :=
  ["cmd", "call", "block", "ite_det", "ite_nondet", "loop", "exit", "funcDecl", "typeDecl"]

def _root_.cmdKinds : List String :=
  ["init_det", "init_nondet", "set_det", "set_nondet", "assert", "assume", "cover"]

/-- The target types of the fixed-type expression panels. Each isolates the expression weights from
    the type distribution that `exprGen` draws its target from. -/
def fixedTypes : List (String × LMonoTy) :=
  [("bool", .bool), ("int", .int), ("int → int", .arrow .int .int)]

/-- `exprGen` at the fixed target type `τ`, with no draw of the type. -/
def exprAtGen (θe : Tuning) (τ : LMonoTy) (s : Nat) : Plausible.Gen LExpr' :=
  genLExprT (G := Plausible.Gen) θe [] coreMonoOps corePolyOps [] [] (max 1 s) τ 3
    (retryGenArg 20)

def cmdSample (cmds : List (Cmd Expression)) : Tyche.Sample :=
  { representation := "\n".intercalate (cmds.map ppCmd)
    features := countFeatures _root_.cmdKinds (cmds.map _root_.cmdKind) ++
      [("size", .ordinal (cmds.map cmdSize).sum),
       ("first_kind", .nominal (match cmds with | c :: _ => _root_.cmdKind c | [] => "empty")),
       ("num_cmds", .ordinal cmds.length)] }

def exprSample (e : LExpr') (size : Nat) : Tyche.Sample :=
  { representation := ppExpr e
    features := countFeatures exprKinds (exprNodeKinds e) ++
      [("size", .ordinal (exprSize e)), ("root_kind", .nominal (exprKind e)), ("expr_size", .ordinal (exprSize e)),
       ("expr_depth", .ordinal (exprDepth e)), ("generator_size", .ordinal size)] }

def stmtSample (ss : List Statement) (size : Nat) : Tyche.Sample :=
  { representation := stmtRepr ss
    features := countFeatures stmtKinds (stmtNodeKinds ss) ++
      [("size", .ordinal (ss.map stmtSize).sum), ("num_stmts", .ordinal ss.length), ("ast_size", .ordinal (sizeStmts ss)),
       ("generator_size", .ordinal size)] }

/-- Write `numSamples` lines under `property`, drawing at sizes `0 … maxSize` in turn, as
    `dist-report` does. A draw that fails even after its retries writes nothing. -/
def writeProfile (handle : IO.FS.Handle) (property : String) (numSamples maxSize runStart : Nat)
    (sample : Nat → IO (Option Tyche.Sample)) : IO Unit := do
  for i in List.range numSamples do
    if let some s ← sample (i % (maxSize + 1)) then
      handle.putStrLn (s.toJsonLine property runStart)

@[strata_diagnostic]
def exprTuningPanels : Diagnostic where
  name := "Expression generator under each tuning (Tyche panels only):"
  run _ := pure ()
  panel := some fun handle cfg numSamples runStart => do
    for (label, (θty, θe, fctx)) in exprProfiles.filter (·.2.2.2.isEmpty) do
      writeProfile handle s!"dist: expr [{label}]" numSamples cfg.maxSize runStart fun sz => do
        let (o, _) ← draw (exprGen θty θe fctx sz) 500 sz
        pure (o.map fun (e, _) => exprSample e sz)

@[strata_diagnostic]
def exprFixedTypePanels : Diagnostic where
  name := "Expression generator at each fixed type, under each tuning (Tyche panels only):"
  run _ := pure ()
  panel := some fun handle cfg numSamples runStart => do
    for (tyName, τ) in fixedTypes do
      for (label, (_, θe, _)) in exprProfiles.filter (·.2.2.2.isEmpty) do
        -- A row that tunes only the type generator has nothing to show at a fixed type.
        if label == "tyCompoundHeavy" then continue
        writeProfile handle s!"dist: expr@{tyName} [{label}]" numSamples cfg.maxSize runStart
          fun sz => do
            let (o, _) ← draw (exprAtGen θe τ sz) 500 sz
            pure (o.map fun e => exprSample e sz)

@[strata_diagnostic]
def cmdTuningPanels : Diagnostic where
  name := "Command generator under each tuning (Tyche panels only):"
  run _ := pure ()
  panel := some fun handle _ numSamples runStart => do
    for (label, θ) in cmdProfiles do
      writeProfile handle s!"dist: cmd [{label}]" numSamples 0 runStart fun _ => do
        let (o, _) ← draw (cmdsGen θ) 1000 20
        pure (o.map fun (cmds, _, _) => cmdSample cmds)

@[strata_diagnostic]
def stmtTuningPanels : Diagnostic where
  name := "Statement generator under each tuning (Tyche panels only):"
  run _ := pure ()
  panel := some fun handle cfg numSamples runStart => do
    for (label, θ) in stmtProfiles do
      writeProfile handle s!"dist: stmt [{label}]" numSamples cfg.maxSize runStart fun sz => do
        let (o, _) ← draw (stmtsGen θ sz) 500 sz
        pure (o.map fun ss => stmtSample ss sz)

end StrataTests.TuningDistributions
