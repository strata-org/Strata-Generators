import StrataGenerators.TuningProfiles
import StrataGenerators.ProgramTuning
import StrataGenerators.MonomorphizeFns
import StrataGenerators.ProcedureHasTypeAGen.Shrink
import StrataGenerators.RetryGen
import Basalt.PlausibleGen

/-!
# `dist-report`: measuring what a tuning actually generates

Each profile in `StrataGenerators.TuningProfiles` is a claim about a distribution, such as "this makes
loops common". This module checks those claims. It samples each family's generator under each profile,
and counts how often the shapes that the properties discriminate on appear. This is how to derive a
weight empirically: pick a candidate, run `lake exe dist-report`, read the column that matters, and
adjust.

Every column is a coverage column or a cost column.

A **coverage** column is the precondition of a property in the suite, which is the shape without which
that property is vacuous or trivially true. A `loop` for `stmt: LoopElim …`, one `call` for the
FilterProcedures family and a quantifier for `expr: progress` are such shapes. A coverage column can
instead witness that a transform did something, as `LoopElim≠id`, `ANF≠id` and `PE fires` do. That
witness is the sharpest available form of "not vacuous".

A **cost** column is one of two. `1st-try` is the fraction of draws that succeed with no retry, and
`dropped` is the fraction that produce nothing even after the retry budget. The generators are
partial: a sub-generator with empty support throws, and `retryGen` then redraws the *whole* sample. So
a profile that steers into failure-prone shapes buys its coverage with generation time. The point of
these two columns is to show that price next to the coverage it bought.

**The two kinds of column use different denominators.** A coverage column is a fraction of the samples
that *exist*, so its denominator excludes a dropped draw. The cost denominator would scale every
coverage figure down by the drop rate, and that would read as a change in the distribution that never
happened. `1st-try` and `dropped` are fractions of the draws *attempted*, so they keep the full count.

Samples are drawn as the suite draws them. The `size` and `len` schedules are those of
`TestScaffold`'s `Arbitrary` instances. The operator contexts are the suite's: `coreMonoOps` for
statements and commands, and `corePartialOps` for procedures. The `retryGen` budgets are the suite's
too. A rate here is therefore the rate that the corresponding property sees.

**One caveat, which the output repeats.** The command rows measure the `GenCmdsWithCtx` chain, and that
chain starts from the empty context. The four `GenCmdWithCtx` properties draw one command against a
context that a first chain built. They condition on a non-empty context, so they see a higher `set`
rate from the same weights.
-/

open Lambda Core Imperative Plausible
open StrataGenerators.Stmt.TestSupport
open StrataGenerators.Procedure.TestSupport
open StrataGenerators.TuningProfiles

namespace StrataGenerators.DistReport

-- ══════════════════════════════════════════════════════════════════════════
-- Formatting
-- ══════════════════════════════════════════════════════════════════════════

/-- `k` out of `n` as a whole-number percentage, right-aligned in 4 columns. -/
def pct (k n : Nat) : String :=
  let p := if n == 0 then 0 else (k * 200 + n) / (2 * n)
  let s := s!"{p}%"
  "".pushn ' ' (4 - min 4 s.length) ++ s

/-- `sum / n` to one decimal place, right-aligned in 4 columns. -/
def mean1 (sum n : Nat) : String :=
  let t := if n == 0 then 0 else (sum * 10 + n / 2) / n
  let s := s!"{t / 10}.{t % 10}"
  "".pushn ' ' (4 - min 4 s.length) ++ s

def padTo (w : Nat) (s : String) : String := s ++ "".pushn ' ' (w - min w s.length)

/-- Print one table. The label column has a fixed width. Each other column is as wide as the wider of
    its header and its widest cell. -/
def printTable (title : String) (labelWidth : Nat) (headers : List String)
    (rows : List (String × List String)) : IO Unit := do
  let widths := headers.zipIdx.map (fun (h, j) =>
    rows.foldl (fun w (_, cells) => max w ((cells[j]?.getD "").length)) (max 6 h.length))
  let cols (cells : List String) : String :=
    " │ ".intercalate ((cells.zip widths).map (fun (c, w) => padTo w c))
  IO.println ""
  IO.println title
  IO.println (padTo labelWidth "" ++ " │ " ++ cols headers)
  IO.println ("".pushn '─' labelWidth ++ "─┼─" ++
    "─┼─".intercalate (widths.map (fun w => "".pushn '─' w)))
  for (label, cells) in rows do
    IO.println (padTo labelWidth label ++ " │ " ++ cols cells)

-- ══════════════════════════════════════════════════════════════════════════
-- Drawing
-- ══════════════════════════════════════════════════════════════════════════

/-- Draw once at Plausible size `size`, and report whether the *first* attempt succeeded. On a
    failure, retry with `fuel`, as the suite's `Arbitrary` instances do. The sample set is then the
    suite's, and not a biased subset of it. -/
def draw (g : Plausible.Gen α) (fuel size : Nat) : IO (Option α × Bool) := do
  match ← (try (some <$> Gen.run g size) catch _ => pure none) with
  | some a => pure (some a, true)
  | none =>
    match ← (try (some <$> Gen.run (retryGen fuel g) size) catch _ => pure none) with
    | some a => pure (some a, false)
    | none => pure (none, false)

-- ══════════════════════════════════════════════════════════════════════════
-- Statement family
-- ══════════════════════════════════════════════════════════════════════════

/-- The deepest chain of nested `loop`s. `stmt: LoopElim …` is most likely to catch a defect in the
    pass at depth 2 or more, and one loop weight buys that only when the tuning threads through the
    recursion. -/
partial def loopNesting : Statement → Nat
  | .loop _ _ _ body _ => 1 + (body.map loopNesting).foldl max 0
  | .block _ body _ => (body.map loopNesting).foldl max 0
  | .ite _ t e _ => max ((t.map loopNesting).foldl max 0) ((e.map loopNesting).foldl max 0)
  | _ => 0

def isCallStmt : Statement → Bool
  | .call _ _ _ => true
  | _ => false

/-- The statement family's sample. It uses the `size` and `len` schedule of
    `TestScaffold.genStmtsG`, and draws through the tuned entry point. -/
def stmtsGen (θ : Tuning) (s : Nat) : Gen (List Statement) := do
  let size := max 1 (min 3 s)
  let len := max 1 s
  let (ss, _, _) ← genProgramStmtsT (G := Plausible.Gen) θ coreMonoOps [] size len
  pure ss

structure StmtStats where
  /-- Draws attempted: the denominator of `1st-try` and `dropped`. -/
  n : Nat := 0
  /-- Draws that produced nothing even after the retry budget. `n - dropped` is the denominator of
      every coverage column; see the module docstring on the two denominators. -/
  dropped : Nat := 0
  firstTry : Nat := 0
  loop : Nat := 0
  loop2 : Nat := 0
  exit : Nat := 0
  funcDecl : Nat := 0
  typeDecl : Nat := 0
  call : Nat := 0
  invLoop : Nat := 0
  loopElim : Nat := 0
  anf : Nat := 0
  kleene : Nat := 0
  stmts : Nat := 0
  size : Nat := 0

def stmtRow (θ : Tuning) (samples maxSize : Nat) : IO (List String) := do
  let mut t : StmtStats := {}
  for i in List.range samples do
    let (o, ok) ← draw (stmtsGen θ (i % (maxSize + 1))) 4000 (i % (maxSize + 1))
    match o with
    | none => t := { t with n := t.n + 1, dropped := t.dropped + 1 }
    | some ss =>
      let nest := (ss.map loopNesting).foldl max 0
      t := { t with
        n := t.n + 1
        firstTry := t.firstTry + (if ok then 1 else 0)
        loop := t.loop + (if nest ≥ 1 then 1 else 0)
        loop2 := t.loop2 + (if nest ≥ 2 then 1 else 0)
        exit := t.exit + (if countExitStmts ss != 0 then 1 else 0)
        funcDecl := t.funcDecl + (if countFuncDeclStmts ss != 0 then 1 else 0)
        typeDecl := t.typeDecl + (if countTypeDeclStmts ss != 0 then 1 else 0)
        call := t.call + (if countStmtsByList isCallStmt ss != 0 then 1 else 0)
        invLoop := t.invLoop + (if hasInvLoopStmts ss then 1 else 0)
        loopElim := t.loopElim + (if stmtsEq (loopElimStmts ss) ss then 0 else 1)
        anf := t.anf + (if stmtsEq (anfStmts ss) ss then 0 else 1)
        kleene := t.kleene + (if (kleeneStmts ss).isSome then 1 else 0)
        stmts := t.stmts + ss.length
        size := t.size + sizeStmts ss }
  let k := t.n - t.dropped
  pure [pct t.loop k, pct t.loop2 k, pct t.invLoop k, pct t.exit k,
        pct t.funcDecl k, pct t.typeDecl k, pct t.call k,
        pct t.loopElim k, pct t.anf k, pct t.kleene k,
        mean1 t.stmts k, mean1 t.size k, pct t.firstTry t.n, pct t.dropped t.n]

def stmtHeaders : List String :=
  ["loop", "loop²", "invLoop", "exit", "fnDecl", "tyDecl", "call",
   "LpElim≠", "ANF≠id", "Kleene✓", "#stmts", "astSize", "1st-try", "dropped"]

-- ══════════════════════════════════════════════════════════════════════════
-- Procedure family
-- ══════════════════════════════════════════════════════════════════════════

/-- The procedure family's sample. It is `TestScaffold.genProcsG`, and it draws each body through
    `genProcedureT θ`. -/
def procsGen (θ : Tuning) (s : Nat) : Gen (List Procedure) := do
  let n := max 2 s
  let size := max 1 (min 2 s)
  let len := max 1 (min 3 s)
  let (ps, _) ← (List.range n).foldlM
    (fun (acc : List Procedure × StrataGenerators.Stmt.ProcSigCtx) (i : Nat) => do
      let proc ← (retryGen 8000 (genProcedureT (G := Plausible.Gen) θ
        corePartialOps acc.2 LContext.default {} size len) : Gen Procedure)
      let sigs := acc.2 ++ [StrataGenerators.Procedure.headerProcSig s!"P{i}" proc.header]
      pure (acc.1 ++ [proc], sigs))
    (([], []) : List Procedure × StrataGenerators.Stmt.ProcSigCtx)
  pure (relabelProcs ps)

/-- Did PrecondElim rewrite the program at all? This is the precondition of all thirteen
    `proc: PrecondElim …` properties. The pass is the identity on a program with no partial call and no
    declared precondition. Every one of those properties then holds for a reason that has nothing to do
    with the pass. -/
def precondFires (prog : Program) : Bool :=
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) => decide (out ≠ prog)
  | none => false

/-- Did PrecondElim emit a well-formedness procedure? That is the shape that
    `proc: PrecondElim $wf procs are well-formed` inspects. -/
def precondEmitsWF (prog : Program) : Bool :=
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) =>
    out.decls.any (fun d =>
      match d with
      | .proc p _ => ((CoreIdent.toPretty p.header.name).splitOn "$wf").length > 1
      | _ => false)
  | none => false

/-- Did FilterProcedures remove anything, with the first procedure as the only entry target? The five
    `FilterCorrect` fields say what a removal keeps, so a run that removes nothing satisfies all five
    trivially. -/
def filterDrops (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase (Core.filterProceduresPipelinePhase ["P0"] true) prog with
  | some (_, out) => out.decls.length < prog.decls.length
  | none => false

/-- Did `CommonSubexprElim` rewrite the program? The pass hoists a *duplicated* non-leaf subexpression
    into a `var`, so it fires only when two independent draws coincide.
    `StrataGenerators.TuningProfiles` says why no weight buys that reliably. -/
def anfChanges (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.commonSubexprElimPhase prog with
  | some (_, out) => decide (out ≠ prog)
  | none => false

structure ProcStats where
  n : Nat := 0
  dropped : Nat := 0
  firstTry : Nat := 0
  call : Nat := 0
  funcDecl : Nat := 0
  loop : Nat := 0
  pe : Nat := 0
  peWF : Nat := 0
  filt : Nat := 0
  anf : Nat := 0
  bodyStmts : Nat := 0

def procRow (θ : Tuning) (samples maxSize : Nat) : IO (List String) := do
  let mut t : ProcStats := {}
  for i in List.range samples do
    let (o, ok) ← draw (procsGen θ (i % (maxSize + 1))) 8000 (i % (maxSize + 1))
    match o with
    | none => t := { t with n := t.n + 1, dropped := t.dropped + 1 }
    | some ps =>
      let bodies := ps.flatMap (fun p => bodyStmts p.body)
      t := { t with
        n := t.n + 1
        firstTry := t.firstTry + (if ok then 1 else 0)
        call := t.call + (if countStmtsByList isCallStmt bodies != 0 then 1 else 0)
        funcDecl := t.funcDecl + (if countFuncDeclStmts bodies != 0 then 1 else 0)
        loop := t.loop + (if (bodies.map loopNesting).foldl max 0 ≥ 1 then 1 else 0)
        pe := t.pe + (if precondFires (mkProgram ps) then 1 else 0)
        peWF := t.peWF + (if precondEmitsWF (mkMixedProgram ps) then 1 else 0)
        filt := t.filt + (if filterDrops ps then 1 else 0)
        anf := t.anf + (if anfChanges ps then 1 else 0)
        bodyStmts := t.bodyStmts + bodies.length }
  let k := t.n - t.dropped
  pure [pct t.call k, pct t.funcDecl k, pct t.loop k, pct t.pe k, pct t.peWF k,
        pct t.filt k, pct t.anf k, mean1 t.bodyStmts k, pct t.firstTry t.n, pct t.dropped t.n]

def procHeaders : List String :=
  ["call", "fnDecl", "loop", "PE fires", "PE $wf", "Filt cut", "ANF≠id", "#body", "1st-try",
   "dropped"]

-- ══════════════════════════════════════════════════════════════════════════
-- Command family
-- ══════════════════════════════════════════════════════════════════════════

def isSet : Cmd Expression → Bool
  | .set _ _ _ => true
  | _ => false

def isInit : Cmd Expression → Bool
  | .init _ _ _ _ => true
  | _ => false

def isCheck : Cmd Expression → Bool
  | .assert _ _ _ | .assume _ _ _ | .cover _ _ _ => true
  | _ => false

/-- The command family's sample. It is `TestScaffold.genCmdsWithCtxG`, one chain of four commands from
    the **empty** context, drawn through the tuned chain.

    The empty start is not incidental. `genCmd` has two sites, and only the site that a writable context
    reaches offers `set`. The first command of a chain can therefore never be a `set`. A measurement
    against a pre-built context would report a `set` rate that the `GenCmdsWithCtx` properties never
    see. The four `GenCmdWithCtx` properties draw *one* command against a context that a first chain
    built, which is the second site conditioned on a non-empty context. The weights are the same, so a
    profile moves both, but the rates are not the same. -/
def cmdsGen (θ : Tuning) : Gen (List (Cmd Expression) × VarCtx × VarCtx) := do
  let (cmds, outCtx) ← genCmdsT (G := Plausible.Gen) θ coreMonoOps [] [] [] 2 4
  pure (cmds, [], outCtx)

structure CmdStats where
  n : Nat := 0
  dropped : Nat := 0
  firstTry : Nat := 0
  set : Nat := 0
  init : Nat := 0
  check : Nat := 0
  setCmds : Nat := 0
  cmds : Nat := 0
  growth : Nat := 0

def cmdRow (θ : Tuning) (samples : Nat) : IO (List String) := do
  let mut t : CmdStats := {}
  for _ in List.range samples do
    let (o, ok) ← draw (cmdsGen θ) 1000 20
    match o with
    | none => t := { t with n := t.n + 1, dropped := t.dropped + 1 }
    | some ((cmds : List (Cmd Expression)), (inCtx : VarCtx), (outCtx : VarCtx)) =>
      t := { t with
        n := t.n + 1
        firstTry := t.firstTry + (if ok then 1 else 0)
        set := t.set + (if cmds.any isSet then 1 else 0)
        init := t.init + (if cmds.any isInit then 1 else 0)
        check := t.check + (if cmds.any isCheck then 1 else 0)
        setCmds := t.setCmds + (cmds.filter isSet).length
        cmds := t.cmds + cmds.length
        growth := t.growth + (outCtx.length - inCtx.length) }
  let k := t.n - t.dropped
  pure [pct t.set k, pct t.init k, pct t.check k,
        mean1 t.setCmds k, mean1 t.growth k, mean1 t.cmds k, pct t.firstTry t.n,
        pct t.dropped t.n]

def cmdHeaders : List String :=
  ["has set", "has init", "has chk", "#sets", "growth", "#cmds", "1st-try", "dropped"]

-- ══════════════════════════════════════════════════════════════════════════
-- Expression family
-- ══════════════════════════════════════════════════════════════════════════

partial def countQuant : LExpr' → Nat
  | .quant _ _ _ _ tr body => 1 + countQuant tr + countQuant body
  | .abs _ _ _ b => countQuant b
  | .app _ f a => countQuant f + countQuant a
  | .ite _ c t e => countQuant c + countQuant t + countQuant e
  | .eq _ a b => countQuant a + countQuant b
  | _ => 0

/-- Is the term already a value? A constant, a variable and an operator with no arguments are values.
    `expr: preservation` and `expr: progress` are about `LExpr.eval`, and on a value they hold without
    the evaluator taking a step. -/
def isLeaf : LExpr' → Bool
  | .bvar _ _ | .fvar _ _ _ | .op _ _ _ | .const _ _ => true
  | _ => false

/-- Count the operator occurrences. An operator is how a partial builtin such as `Int.SafeDiv` enters
    a term, and such a builtin is what gives PrecondElim an obligation. -/
partial def countOps : LExpr' → Nat
  | .op _ _ _ => 1
  | .abs _ _ _ b => countOps b
  | .app _ f a => countOps f + countOps a
  | .ite _ c t e => countOps c + countOps t + countOps e
  | .eq _ a b => countOps a + countOps b
  | .quant _ _ _ _ tr b => countOps tr + countOps b
  | _ => 0

/-- Does the term mention a free variable? `expr: eval preserves fvars` says that evaluation
    introduces no new one, so a term with none satisfies it for no interesting reason. -/
partial def hasFVarNode : LExpr' → Bool
  | .fvar _ _ _ => true
  | .abs _ _ _ b => hasFVarNode b
  | .app _ f a => hasFVarNode f || hasFVarNode a
  | .ite _ c t e => hasFVarNode c || hasFVarNode t || hasFVarNode e
  | .eq _ a b => hasFVarNode a || hasFVarNode b
  | .quant _ _ _ _ tr b => hasFVarNode tr || hasFVarNode b
  | _ => false

def hasRedexKind : LExpr' → Bool
  | .app _ _ _ | .ite _ _ _ _ | .eq _ _ _ => true
  | _ => false

/-- The expression family's sample: a type, then a term of that type. It is `TestScaffold`'s
    `genTypedExprWith` through the tuned entry point, so the root Indir and IndirPoly choice and the
    per-subterm `retryGenArg` continuation are the suite's.

    This sampler tunes the *type* generator as well, which no property does. `genLMonoTy`'s weights
    reach no `TunableGen` instance, so the `tyCompoundHeavy` row is exploratory. Every other row passes
    `tyDefault`, and at `tyDefault` the tuned type generator is `genLMonoTy`. -/
def exprGen (θty θe : Tuning) (fctx : FVarCtx) (s : Nat) : Gen (LExpr' × LMonoTy) := do
  let depth := max 1 s
  let τ ← genLMonoTy.tuned (G := Plausible.Gen) θty [] depth
  let e ← genLExprT (G := Plausible.Gen) θe fctx coreMonoOps corePolyOps [] [] depth τ 3
    (retryGenArg 20)
  pure (e, τ)

structure ExprStats where
  n : Nat := 0
  dropped : Nat := 0
  firstTry : Nat := 0
  quant : Nat := 0
  leaf : Nat := 0
  redex : Nat := 0
  op : Nat := 0
  hasFVar : Nat := 0
  progress : Nat := 0
  preservation : Nat := 0
  fvars : Nat := 0

def exprRow (θ : Tuning × Tuning × FVarCtx) (samples maxSize : Nat) : IO (List String) := do
  let (θty, θe, fctx) := θ
  let mut t : ExprStats := {}
  for i in List.range samples do
    let sz := i % (maxSize + 1)
    let (o, ok) ← draw (exprGen θty θe fctx sz) 500 sz
    match o with
    | none => t := { t with n := t.n + 1, dropped := t.dropped + 1 }
    | some (e, τ) =>
      t := { t with
        n := t.n + 1
        firstTry := t.firstTry + (if ok then 1 else 0)
        quant := t.quant + (if countQuant e != 0 then 1 else 0)
        leaf := t.leaf + (if isLeaf e then 1 else 0)
        redex := t.redex + (if hasRedexKind e then 1 else 0)
        op := t.op + (if countOps e != 0 then 1 else 0)
        hasFVar := t.hasFVar + (if hasFVarNode e then 1 else 0)
        progress := t.progress + (if checkProgress e then 1 else 0)
        preservation := t.preservation + (if checkPreservation e τ then 1 else 0)
        fvars := t.fvars + (if checkFvarsPreserved e then 1 else 0) }
  let k := t.n - t.dropped
  pure [pct t.quant k, pct t.leaf k, pct t.redex k, pct t.op k, pct t.hasFVar k,
        pct t.progress k, pct t.preservation k, pct t.fvars k, pct t.firstTry t.n,
        pct t.dropped t.n]

def exprHeaders : List String :=
  ["quant", "value", "redex", "op", "hasFvar", "prog✓", "presv✓", "fvars✓", "1st-try", "dropped"]

-- ══════════════════════════════════════════════════════════════════════════
-- Program family
-- ══════════════════════════════════════════════════════════════════════════

open StrataGenerators.ProgramTuning StrataGenerators.Mono in
/-- The program family's sample. It is `TestScaffold.genProgramG`, drawn through the tuned
    declaration fold. -/
def programsGen (θ : Tuning) (s : Nat) : Gen Program := do
  let numDecls := max 2 s
  retryGen 30000 (genProgramT (G := Plausible.Gen) θ numDecls {})

structure ProgStats where
  n : Nat := 0
  dropped : Nat := 0
  firstTry : Nat := 0
  polyFn : Nat := 0
  polyData : Nat := 0
  monoFires : Nat := 0
  /-- Declarations in the pass output. The table reports it next to `decls` rather than as a
      difference, because the pass can also *shrink* a program and a `Nat` difference truncates at 0. -/
  outDecls : Nat := 0
  decls : Nat := 0

open StrataGenerators.Mono in
def programRow (θ : Tuning) (samples maxSize : Nat) : IO (List String) := do
  let mut t : ProgStats := {}
  for i in List.range samples do
    let sz := i % (maxSize + 1)
    let (o, ok) ← draw (programsGen θ sz) 8000 sz
    match o with
    | none => t := { t with n := t.n + 1, dropped := t.dropped + 1 }
    | some prog =>
      let (changed, out) := monoChangedOut prog
      t := { t with
        n := t.n + 1
        firstTry := t.firstTry + (if ok then 1 else 0)
        polyFn := t.polyFn + (if polyProgramFuncNames prog != [] then 1 else 0)
        polyData := t.polyData +
          (if (datatypeParams prog).any (fun d => d.2 != []) then 1 else 0)
        monoFires := t.monoFires + (if changed then 1 else 0)
        outDecls := t.outDecls + out.decls.length
        decls := t.decls + prog.decls.length }
  let k := t.n - t.dropped
  pure [pct t.polyFn k, pct t.polyData k, pct t.monoFires k,
        mean1 t.decls k, mean1 t.outDecls k, pct t.firstTry t.n, pct t.dropped t.n]

def programHeaders : List String :=
  ["polyFn", "polyData", "mono≠id", "#decls", "#out", "1st-try", "dropped"]

/-! There is deliberately no property-outcome table here. `TestDecl.underTunings` already runs the
suite's own properties under each profile. It registers one property per claim and weighting, and each
gets its own verdict and its own Tyche panel. So that comparison belongs in the suite, where a
distribution-sensitive failure gates CI, rather than in a report that nobody runs.
`StrataTests/Stmt.lean` and `StrataTests/Monomorphization.lean` hold the properties that use it. -/

-- ══════════════════════════════════════════════════════════════════════════
-- The report
-- ══════════════════════════════════════════════════════════════════════════

/-- The profiles that each family is measured under. The first row of every table is the shipping
    distribution, so every other row reads as a difference against it. -/
def stmtProfiles : List (String × Tuning) :=
  [ ("(default)", stmtDefault),
    ("stmtLoopHeavy", stmtLoopHeavy),
    ("stmtLoopWide", stmtLoopWide),
    ("stmtFuncDeclHeavy", stmtFuncDeclHeavy),
    ("stmtMixed", stmtMixed) ]

def procProfiles : List (String × Tuning) :=
  [ ("(default)", stmtDefault),
    ("procCallHeavy", procCallHeavy),
    ("procPrecondHeavy", procPrecondHeavy),
    ("stmtLoopHeavy", stmtLoopHeavy),
    ("stmtMixed", stmtMixed) ]

def cmdProfiles : List (String × Tuning) :=
  [ ("(default)", cmdDefault),
    ("cmdSetHeavy", cmdSetHeavy),
    ("cmdInitHeavy", cmdInitHeavy),
    ("cmdCheckHeavy", cmdCheckHeavy) ]

/-- An expression row carries two tunings, one for the type generator and one for the term generator.
    Which shapes appear depends on both. -/
def exprProfiles : List (String × (Tuning × Tuning × FVarCtx)) :=
  [ ("(default), closed", (tyDefault, exprBreadth, [])),
    ("exprEvalHeavy", (tyDefault, exprEvalHeavy, [])),
    ("exprQuantHeavy", (tyDefault, exprQuantHeavy, [])),
    ("exprIndirHeavy", (tyDefault, exprIndirHeavy, [])),
    ("tyCompoundHeavy", (tyCompoundHeavy, exprBreadth, [])),
    ("(default), open", (tyDefault, exprBreadth, defaultFCtx)),
    ("exprFVarHeavy, open", (tyDefault, exprFVarHeavy, defaultFCtx)) ]

open StrataGenerators.ProgramTuning in
def programProfiles : List (String × Tuning) :=
  [ ("(default)", progDefault),
    ("progPolyHeavy", progPolyHeavy),
    ("progDatatypeHeavy", progDatatypeHeavy) ]

def runFamily {θ : Type} (name : String) (headers : List String) (profiles : List (String × θ))
    (row : θ → IO (List String)) (note : String := "") : IO Unit := do
  let mut rows := #[]
  for (label, θ) in profiles do
    IO.print s!"  … {name}/{label}\n"
    rows := rows.push (label, ← row θ)
  printTable name 20 headers rows.toList
  unless note.isEmpty do IO.println s!"  {note}"

def report (samples maxSize : Nat) (families : List String) : IO Unit := do
  IO.println s!"dist-report: {samples} samples per profile, max size {maxSize}"
  if families.contains "stmt" then
    runFamily "statements" stmtHeaders stmtProfiles (stmtRow · samples maxSize)
      ("every column is a % of samples. LpElim≠ and ANF≠id say the transform did something, and "
       ++ "Kleene✓ says it is defined. `call` is structurally 0 here, because genProgramStmts gets "
       ++ "no callable procedure. A call statement then has empty support whatever its weight. See "
       ++ "the procedures table")
  if families.contains "proc" then
    runFamily "procedures" procHeaders procProfiles (procRow · samples maxSize)
      ("PE fires = PrecondElim rewrote the program. Filt cut = FilterProcedures removed a decl. "
       ++ "1st-try is near 100% by construction, because the harness retries each procedure on its "
       ++ "own before it assembles the list, as TestScaffold does")
  if families.contains "cmd" then
    runFamily "commands" cmdHeaders cmdProfiles (fun θ => cmdRow θ samples)
      ("one chain of four commands from the empty context, as GenCmdsWithCtx draws it. The four "
       ++ "GenCmdWithCtx properties draw one command against a context that a first chain built, so "
       ++ "their `set` rate is higher than `has set` here. The genCmd weights are the same and the "
       ++ "conditioning is not. See `cmdsGen`")
  if families.contains "expr" then
    runFamily "expressions" exprHeaders exprProfiles (exprRow · samples maxSize)
      ("a closed row uses fctx = [], which is the ClosedTypedExpr shape that progress and "
       ++ "preservation quantify over. An open row uses defaultFCtx. Every row draws through "
       ++ "genLExprT, the entry point the expr: properties use. tyCompoundHeavy tunes the *type* "
       ++ "generator, which no property does")
  if families.contains "prog" then
    runFamily "programs" programHeaders programProfiles (programRow · samples maxSize)
      ("polyFn and polyData say the program declares a polymorphic function, and a polymorphic "
       ++ "datatype. Those are the two shapes the mono: family needs. mono≠id says "
       ++ "MonomorphizeFunctions rewrote the program. #out is the output declaration count, against "
       ++ "the input count #decls, so a pass that replaces rather than appends shows here")

end StrataGenerators.DistReport
