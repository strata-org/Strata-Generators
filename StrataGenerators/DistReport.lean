import StrataGenerators.TuningProfiles
import StrataGenerators.ProcedureHasTypeAGen.Shrink
import StrataGenerators.RetryGen
import Basalt.PlausibleGen

/-!
# `dist-report`: measuring what a tuning actually generates

The profiles in `StrataGenerators.TuningProfiles` are claims about a distribution ("this makes
loops common"). This module checks them: it samples each family's generator under each profile and
counts how often the shapes the properties discriminate on actually appear. It is the "empirically
derive" half of choosing weights — pick a candidate, run `lake exe dist-report`, read the column
that matters, adjust.

Every column is either

* the **precondition of a property** in the suite — the shape without which that property is
  vacuous or trivially true (`loop` for `stmt: LoopElim …`, `≥1 call` for the FilterProcedures
  family, a quantifier for `expr: progress`), or a *witness that a transform did something*
  (`LoopElim≠id`, `ANF≠id`, `PE fires`), which is the sharpest available form of "not vacuous"; or
* a **cost**: `1st-try`, the fraction of draws that succeed with no retry. The generators are
  partial — a sub-generator with empty support throws and `retryGen` redraws the *whole* sample —
  so a profile that steers into failure-prone shapes buys coverage with generation time. Seeing
  that next to the coverage it bought is the point.

Samples are drawn exactly as the suite draws them: the same `size`/`len` schedules as
`TestScaffold`'s `Arbitrary` instances, the same operator contexts (`coreMonoOps` for statements
and commands, `corePartialOps` for procedures), the same `retryGen` budgets. So a rate here is the
rate the corresponding property sees.

**One caveat, stated in the output too.** The expression rows sample `genLExprBase` directly,
because that is the definition the expression weights live in. The suite's `expr:` properties draw
through `genLExprWithOps`, which reaches `genLExprBase` by name and therefore *unmodified* — see
the "Composition" section of `StrataGenerators.TuningProfiles`. The expression rows are the
distribution of the tuned generator, not of the suite's current entry point.
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

/-- One table: a fixed label column, then one column per header, each as wide as the widest of its
    header and its cells. -/
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

/-- Draw once at Plausible size `size`, reporting whether the *first* attempt
    succeeded. On failure, retry with `fuel` (exactly as the suite's `Arbitrary`
    instances do) so the sample set is the suite's, not a biased subset of it. -/
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

/-- Deepest chain of nested `loop`s. `stmt: LoopElim …` is most likely to catch a
    pass bug at depth ≥ 2, which one loop weight cannot buy unless the tuning
    threads through the recursion. -/
partial def loopNesting : Statement → Nat
  | .loop _ _ _ body _ => 1 + (body.map loopNesting).foldl max 0
  | .block _ body _ => (body.map loopNesting).foldl max 0
  | .ite _ t e _ => max ((t.map loopNesting).foldl max 0) ((e.map loopNesting).foldl max 0)
  | _ => 0

def isCallStmt : Statement → Bool
  | .call _ _ _ => true
  | _ => false

/-- The statement family's sample, drawn with `TestScaffold.genStmtsWith`'s
    `size`/`len` schedule but through the tuned entry point. -/
def stmtsGen (θ : Tuning) (s : Nat) : Gen (List Statement) := do
  let size := max 1 (min 3 (s / 25))
  let len := max 1 (min 4 (s / 20))
  let (ss, _, _) ← genProgramStmtsT (G := Plausible.Gen) θ coreMonoOps [] size len
  pure ss

structure StmtStats where
  n : Nat := 0
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
    | none => t := { t with n := t.n + 1 }
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
  pure [pct t.loop t.n, pct t.loop2 t.n, pct t.invLoop t.n, pct t.exit t.n,
        pct t.funcDecl t.n, pct t.typeDecl t.n, pct t.call t.n,
        pct t.loopElim t.n, pct t.anf t.n, pct t.kleene t.n,
        mean1 t.stmts t.n, mean1 t.size t.n, pct t.firstTry t.n]

def stmtHeaders : List String :=
  ["loop", "loop²", "invLoop", "exit", "fnDecl", "tyDecl", "call",
   "LpElim≠", "ANF≠id", "Kleene✓", "#stmts", "astSize", "1st-try"]

-- ══════════════════════════════════════════════════════════════════════════
-- Procedure family
-- ══════════════════════════════════════════════════════════════════════════

/-- The procedure family's sample: `TestScaffold.genProcsWith` verbatim, except
    that each body is drawn through `genProcedureT θ`. -/
def procsGen (θ : Tuning) (s : Nat) : Gen (List Procedure) := do
  let n := max 2 (min 4 (2 + s / 30))
  let size := max 1 (min 2 (s / 30))
  let len := max 1 (min 3 (s / 25))
  let (ps, _) ← (List.range n).foldlM
    (fun (acc : List Procedure × StrataGenerators.Stmt.ProcSigCtx) (i : Nat) => do
      let proc ← (retryGen 8000 (genProcedureT (G := Plausible.Gen) θ
        corePartialOps acc.2 LContext.default {} size len) : Gen Procedure)
      let sigs := acc.2 ++ [StrataGenerators.Procedure.headerProcSig s!"P{i}" proc.header]
      pure (acc.1 ++ [proc], sigs))
    (([], []) : List Procedure × StrataGenerators.Stmt.ProcSigCtx)
  pure (relabelProcs ps)

/-- Did PrecondElim rewrite the program at all? This is the precondition of all
    thirteen `proc: PrecondElim …` properties: on a program with no partial call
    and no declared precondition the pass is the identity and every one of them
    holds for a reason that has nothing to do with the pass. -/
def precondFires (prog : Program) : Bool :=
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) => decide (out ≠ prog)
  | none => false

/-- Did PrecondElim emit a well-formedness procedure? That is the shape
    `proc: PrecondElim $wf procs are well-formed` inspects. -/
def precondEmitsWF (prog : Program) : Bool :=
  match runPhase Core.precondElimPipelinePhase prog with
  | some (_, out) =>
    out.decls.any (fun d =>
      match d with
      | .proc p _ => ((CoreIdent.toPretty p.header.name).splitOn "$wf").length > 1
      | _ => false)
  | none => false

/-- Did FilterProcedures remove anything, with only the first procedure as the
    entry target? The five `FilterCorrect` fields are about what a removal keeps;
    on a run that removes nothing they are all trivially satisfied. -/
def filterDrops (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase (Core.filterProceduresPipelinePhase ["P0"] true) prog with
  | some (_, out) => out.decls.length < prog.decls.length
  | none => false

/-- Did `CommonSubexprElim` (the pass formerly called ANFEncoder) rewrite the program?
    It hoists a *duplicated* non-leaf subexpression into a `var`, so this fires only when
    two independently drawn subterms happen to coincide — see the note in
    `StrataGenerators.TuningProfiles` on why no weight buys this reliably. -/
def anfChanges (ps : List Procedure) : Bool :=
  let prog := mkProgram ps
  match runPhase Core.commonSubexprElimPhase prog with
  | some (_, out) => decide (out ≠ prog)
  | none => false

structure ProcStats where
  n : Nat := 0
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
    | none => t := { t with n := t.n + 1 }
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
  pure [pct t.call t.n, pct t.funcDecl t.n, pct t.loop t.n, pct t.pe t.n, pct t.peWF t.n,
        pct t.filt t.n, pct t.anf t.n, mean1 t.bodyStmts t.n, pct t.firstTry t.n]

def procHeaders : List String :=
  ["call", "fnDecl", "loop", "PE fires", "PE $wf", "Filt cut", "ANF≠id", "#body", "1st-try"]

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

/-- The command family's sample: `TestScaffold.genCmdFromBuiltCtx`'s shape (a
    context built by a first chain, then the commands under test), through the
    tuned chain. -/
def cmdsGen (θ : Tuning) : Gen (List (Cmd Expression) × VarCtx × VarCtx) := do
  let (_, baseCtx) ← genCmdsT (G := Plausible.Gen) θ coreMonoOps [] [] [] 2 3
  let (cmds, outCtx) ← genCmdsT (G := Plausible.Gen) θ coreMonoOps [] [] baseCtx 2 4
  pure (cmds, baseCtx, outCtx)

structure CmdStats where
  n : Nat := 0
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
    | none => t := { t with n := t.n + 1 }
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
  pure [pct t.set t.n, pct t.init t.n, pct t.check t.n,
        mean1 t.setCmds t.n, mean1 t.growth t.n, mean1 t.cmds t.n, pct t.firstTry t.n]

def cmdHeaders : List String :=
  ["has set", "has init", "has chk", "#sets", "growth", "#cmds", "1st-try"]

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

/-- Is the term already a value — a constant, a variable, or an operator with no
    arguments? `expr: preservation` and `expr: progress` are about `LExpr.eval`,
    and on a value they hold without the evaluator taking a step. -/
def isLeaf : LExpr' → Bool
  | .bvar _ _ | .fvar _ _ _ | .op _ _ _ | .const _ _ => true
  | _ => false

/-- Operator occurrences: the route by which a partial builtin (`Int.SafeDiv`) — and hence a
    PrecondElim obligation — can enter a term. -/
partial def countOps : LExpr' → Nat
  | .op _ _ _ => 1
  | .abs _ _ _ b => countOps b
  | .app _ f a => countOps f + countOps a
  | .ite _ c t e => countOps c + countOps t + countOps e
  | .eq _ a b => countOps a + countOps b
  | .quant _ _ _ _ tr b => countOps tr + countOps b
  | _ => 0

/-- Does the term mention a free variable? `expr: eval preserves fvars` is about *not introducing*
    one, so a term with none satisfies it for no interesting reason. -/
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

/-- The expression family's sample: a type from `genLMonoTy`, then a term of that
    type from `genLExprBase` — both tuned. See the module doc's caveat: this is the
    tuned generator's distribution, not that of the suite's `genLExprWithOps`
    entry point, which reaches `genLExprBase` by name and so untuned. -/
def exprGen (θty θe : Tuning) (fctx : FVarCtx) (s : Nat) : Gen (LExpr' × LMonoTy) := do
  let depth := max 1 (s / 20)
  let τ ← genLMonoTy.tuned (G := Plausible.Gen) θty [] depth
  let e ← genLExprBase.tuned (G := Plausible.Gen) θe fctx coreMonoOps corePolyOps [] [] depth τ
  pure (e, τ)

structure ExprStats where
  n : Nat := 0
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
    | none => t := { t with n := t.n + 1 }
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
  pure [pct t.quant t.n, pct t.leaf t.n, pct t.redex t.n, pct t.op t.n, pct t.hasFVar t.n,
        pct t.progress t.n, pct t.preservation t.n, pct t.fvars t.n, pct t.firstTry t.n]

def exprHeaders : List String :=
  ["quant", "value", "redex", "op", "hasFvar", "prog✓", "presv✓", "fvars✓", "1st-try"]

/-! There is deliberately no property-outcome table here. Running the suite's own properties under
each profile is what `TestDecl.underTunings` does — one registered property per (claim, weighting)
pair, each with its own verdict and Tyche panel — so the comparison belongs in the suite, where a
distribution-sensitive failure gates CI, rather than in a report nobody runs. See
`StrataTests/Stmt.lean` for the two properties that use it. -/

-- ══════════════════════════════════════════════════════════════════════════
-- The report
-- ══════════════════════════════════════════════════════════════════════════

/-- The profiles each family is measured under. The first row of every table is
    the shipping distribution, so every other row reads as a delta against it. -/
def stmtProfiles : List (String × Tuning) :=
  [ ("(default)", stmtDefault),
    ("stmtLoopHeavy", stmtLoopHeavy),
    ("stmtLoopWide", stmtLoopWide),
    ("stmtFuncDeclHeavy", stmtFuncDeclHeavy),
    ("stmtKleeneBalanced", stmtKleeneBalanced),
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

/-- Expression rows carry two tunings: the type generator's and the term
    generator's, since "what shapes appear" depends on both. -/
def exprProfiles : List (String × (Tuning × Tuning × FVarCtx)) :=
  [ ("(default), closed", (tyDefault, exprBreadth, [])),
    ("exprEvalHeavy", (tyDefault, exprEvalHeavy, [])),
    ("exprQuantHeavy", (tyDefault, exprQuantHeavy, [])),
    ("exprIndirHeavy", (tyDefault, exprIndirHeavy, [])),
    ("tyCompoundHeavy", (tyCompoundHeavy, exprBreadth, [])),
    ("(default), open", (tyDefault, exprBreadth, defaultFCtx)),
    ("exprFVarHeavy, open", (tyDefault, exprFVarHeavy, defaultFCtx)) ]

def runFamily {θ : Type} (name : String) (headers : List String) (profiles : List (String × θ))
    (row : θ → IO (List String)) (note : String := "") : IO Unit := do
  let mut rows := #[]
  for (label, θ) in profiles do
    IO.print s!"  … {name}/{label}\n"
    rows := rows.push (label, ← row θ)
  printTable name 20 headers rows.toList
  unless note.isEmpty do IO.println s!"  {note}"

def report (samples maxSize : Nat) (families : List String) : IO Unit := do
  IO.println s!"dist-report: {samples} samples/profile, max size {maxSize}"
  if families.contains "stmt" then
    runFamily "statements" stmtHeaders stmtProfiles (stmtRow · samples maxSize)
      ("columns are % of samples; LpElim≠/ANF≠id/Kleene✓ = the transform did something / is "
       ++ "defined. `call` is structurally 0 here: genProgramStmts is given no callable procedures, "
       ++ "so a call statement has empty support whatever its weight — see the procedures table")
  if families.contains "proc" then
    runFamily "procedures" procHeaders procProfiles (procRow · samples maxSize)
      ("PE fires = PrecondElim rewrote the program; Filt cut = FilterProcedures removed a decl. "
       ++ "1st-try is ~100% by construction: the harness retries each procedure individually "
       ++ "(retryGen 8000) before assembling the list, as TestScaffold does")
  if families.contains "cmd" then
    runFamily "commands" cmdHeaders cmdProfiles (fun θ => cmdRow θ samples)
  if families.contains "expr" then
    runFamily "expressions" exprHeaders exprProfiles (exprRow · samples maxSize)
      ("closed rows use fctx = [] (the ClosedTypedExpr shape of progress/preservation), open rows "
       ++ "defaultFCtx; sampled from genLExprBase, which the suite reaches by name and so untuned")

end StrataGenerators.DistReport
