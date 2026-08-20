import StrataGenerators.FunctionHasTypeAGen.TestSupport
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda Core Imperative Strata Strata.CoreDDM
open StrataDDM (initDialect)

/-!
# Shared round-trip helpers for Strata Core `Function`s

This module holds exactly what the parser/pretty-printer round-trip property
needs. It is imported by *both* views in the merged `TestMain` driver — the
Plausible/LSpec property suite and the Tyche panels (`StrataGenerators.TycheViz`)
— so the pretty-print/parse round-trip machinery lives in exactly one place.

It provides:
- `formatFuncAsProgram` / `parseCoreProgram` / `parseCoreProgramErr` — embed a
  `Function` in a one-decl `Program`, format via `Core.formatProgram`, and parse
  back via the Core DDM dialect (the error variant surfaces the parser message).
- A greedy structural minimizer (`shrinkWhile`) plus failure predicates, used to
  reduce a round-trip counterexample to a minimal reproducer. This is a
  *signature-reducing* minimizer specific to the round-trip property — distinct
  from the body-only `Shrinkable Function` instance shrinker, which lives in
  `StrataGenerators.FunctionHasTypeAGen.Shrink`.

**Well-formedness invariant.** Every minimizer candidate is required to satisfy
`funcWellFormed` (every free type variable in the signature is declared in
`typeArgs`), matching the invariant `genFunction` maintains. Without this the
minimizer could drop a `∀`-bound type-arg while leaving it used in a type,
yielding an *undeclared type variable* — an ill-formed function whose parse
failure is a minimizer artifact rather than a genuine printer/parser bug.

`funcWellFormed` is `public` here because `Shrink` reuses it as its candidate
filter.
-/

-- ── Format / parse round-trip ────────────────────────────────────────────

/-- Embed a function into a one-decl Program and format it via Strata's own
    `Core.formatProgram`. This is the string the round-trip property tests. -/
def formatFuncAsProgram (func : Function) : String :=
  let prog : Core.Program := { decls := [ .func func .empty ] }
  (Core.formatProgram prog).pretty

/-- Format a single `Function` using Strata's own `Core.formatProgram`, with the
    `program Core;` header stripped — the Strata Core concrete syntax for the
    function declaration alone, for use as a display label. Prefer this over any
    hand-rolled printer so displays match the real formatter exactly. -/
def formatFunc (func : Function) : String :=
  let s := formatFuncAsProgram func
  if s.startsWith "program Core;\n\n" then
    (s.drop "program Core;\n\n".length).toString else s.trimAscii.toString

/-- Embed a statement list as the body of a trivial procedure `p` in a one-decl
    `Program`, and format it via Strata's own `Core.formatProgram`. This yields
    genuine Strata Core concrete syntax for the statements (a `funcDecl`, `block`,
    `while`, etc. rendered exactly as the real grammar prescribes) rather than any
    hand-rolled approximation.

    Caveat (a faithful reflection of a real limitation, not a display bug): the
    Core CST formatter cannot represent a **bodiless `funcDecl` statement** — the
    `funcDecl_statement` grammar requires a body, so `funcDeclToStatement`
    substitutes a dummy `body` expression (and logs an internal error) for a
    `funcDecl` whose declaration has no body. Such a statement is exactly the
    typechecker-completeness counterexample (a `funcDecl` with a measure but no
    body), so its rendered form shows a placeholder body. The `[body=…]` tag on
    the counterexample (see the harness `Repr`) records the true shape. -/
def formatStmtsAsProgram (ss : List Statement) : String :=
  let proc : Core.Procedure :=
    { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
      spec := default,
      body := .structured ss }
  let prog : Core.Program := { decls := [ .proc proc .empty ] }
  (Core.formatProgram prog).pretty

/-- Format a statement list using Strata's own formatter, with the `program Core;`
    header stripped — for use as a display label in counterexamples. Renders
    `funcDecl`/`block`/`while`/etc. in real Core concrete syntax. -/
def formatStmts (ss : List Statement) : String :=
  let s := formatStmtsAsProgram ss
  if s.startsWith "program Core;\n\n" then
    (s.drop "program Core;\n\n".length).toString else s.trimAscii.toString

/-- Parse a Core program string back to the Strata Core AST (`none` on any
    parse or translation failure). -/
def parseCoreProgram (input : String) : IO (Option Core.Program) := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  let body := if input.startsWith "program Core;\n\n" then
    (input.drop "program Core;\n\n".length).toString else input
  let inputCtx := StrataDDM.Parser.stringInputContext ⟨"roundtrip"⟩ body
  try
    let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx
    let (ast, errs) := TransM.run Inhabited.default (Strata.translateProgram sp)
    if !errs.isEmpty then pure none
    else pure (some ast)
  catch _ => pure none

/-- Like `parseCoreProgram`, but on failure returns the diagnostic message
    (parser exception text, or the translation errors) instead of discarding it. -/
def parseCoreProgramErr (input : String) : IO (Except String Core.Program) := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  let body := if input.startsWith "program Core;\n\n" then
    (input.drop "program Core;\n\n".length).toString else input
  let inputCtx := StrataDDM.Parser.stringInputContext ⟨"roundtrip"⟩ body
  try
    let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx
    let (ast, errs) := TransM.run Inhabited.default (Strata.translateProgram sp)
    if !errs.isEmpty then pure (.error s!"translate: {(toString errs).replace "\n" " "}")
    else pure (.ok ast)
  catch e => pure (.error ((toString e).replace "\n" " "))

-- ── Structural shrinker ──────────────────────────────────────────────────

/-- Structural size; each shrink step below strictly decreases it. -/
def sizeTy : LMonoTy → Nat
  | .ftvar _ => 2
  | .bitvec _ => 2
  | .tcons _ args => 1 + (args.map sizeTy).foldl (· + ·) 0

def sizeFunc (f : Function) : Nat :=
  f.name.name.length
    + sizeTy f.output
    + (f.inputs.toList.map (fun p => 1 + sizeTy p.2)).foldl (· + ·) 0
    + f.typeArgs.length
    + (match f.body with | some _ => 1 | none => 0)
    + (match f.measure with | some _ => 1 | none => 0)
    -- Each `requires` clause counts its expression's AST size plus one for the
    -- clause itself, so *dropping* a clause is strictly smaller than reducing its
    -- expression to a leaf (the same convention as `sizeCheck` for a procedure's
    -- contract). Without this summand the precondition reductions below would all
    -- be filtered out by the strict-decrease test in `shrinkWhile`.
    + (f.preconditions.map (fun pc => 1 + pc.expr.sizeOf)).foldl (· + ·) 0

/-- Immediate smaller candidates for a monotype: collapse a compound toward a
    child or toward `int`, a type variable / bitvector toward `int`, and shrink
    children in place. Base types have no smaller form. -/
partial def shrinkTy : LMonoTy → List LMonoTy
  | .ftvar _ => []
  | .bitvec _ => []
  | .tcons _ [] => []
  | .tcons "arrow" [a, b] =>
    [a, b]
      ++ (.tcons "arrow" [·, b]) <$> shrinkTy a
      ++ (.tcons "arrow" [a, ·]) <$> shrinkTy b
  | .tcons "Map" [k, v] =>
    [k, v]
      ++ (.tcons "Map" [·, v]) <$> shrinkTy k
      ++ (.tcons "Map" [k, ·]) <$> shrinkTy v
  | .tcons "Sequence" [e] =>
    e :: (.tcons "Sequence" [·]) <$> shrinkTy e
  | .tcons _ args => args ++ List.flatMap shrinkTy args

/-- Well-formedness of a shrink candidate. `genFunction` maintains all of these
    invariants; the shrinker must preserve them so it never fabricates a failure
    that is really an *ill-formed* function (which the parser would rightly
    reject) rather than a genuine printer/parser bug. Four conditions:

    1. **Scoping** — every free type variable in the signature (inputs + output)
       is declared in `typeArgs`.
    2. **Body typing** — the body (if present) type-checks at the declared
       `output`, and the measure (if present) at `int`. This is essential:
       `shrinkFunc` can collapse `output` toward `int` (`shrinkOut`) *without*
       touching the body, which would leave e.g. a `real`-returning lambda body
       under an `int` output — an ill-typed function whose parse failure is a
       shrinker artifact, not a Strata bug. Re-checking here rejects such
       candidates.
    3. **Precondition typing** — each `requires` clause type-checks at `bool`.
    4. **Precondition scoping** — each clause's free variables are all formals.

    Conditions 3 and 4 are *not* redundant with any typechecker: `Function.typeCheck`
    never inspects `preconditions` at all — neither type-checking them nor free-var
    checking them. So nothing but this predicate stops a shrink from stranding a
    clause: dropping the input a clause mentions (`dropInput` below) leaves
    `requires y == 0` with no `y` in sight, and reducing a clause's expression can
    make it non-Boolean. `genFunction` emits a clause over the formals on roughly
    half of its draws (measured 101/200), so both are reachable rather than
    hypothetical.

    Condition 4 is also available on its own as
    `StrataGenerators.Program.TestSupport.funcPreconditionsScoped`, whose docstring
    records the full analysis of the gap. Enforcing both here means every
    function-shrinking family — this module's `shrinkFunc`, the `Shrinkable Function`
    instance, and the whole-program shrinker's `.func` case — inherits them from one
    filter. -/
def funcWellFormed (f : Function) : Bool :=
  let used := f.output.freeVars ++ (f.inputs.toList.flatMap (fun p => p.2.freeVars))
  let scopedOk := used.all (· ∈ f.typeArgs)
  let bodyOk := match f.body with
    | some b => LExpr.typeCheck (T := CoreLParams) [] b == some f.output
    | none => true
  let measureOk := match f.measure with
    | some m => LExpr.typeCheck (T := CoreLParams) [] m == some .int
    | none => true
  let formals := f.inputs.keys.map (·.name)
  let precondsOk := f.preconditions.all fun pc =>
    LExpr.typeCheck (T := CoreLParams) [] pc.expr == some .bool
      && (LExpr.collectFvarNames pc.expr).all (fun x => x.name ∈ formals)
  scopedOk && bodyOk && measureOk && precondsOk

/-- Candidate smaller functions: drop body/measure, drop a `requires` clause, drop
    an input, drop a type-arg, reduce a `requires` clause's expression, shrink an
    input type, shrink the output type, or shorten the name. All candidates are
    strictly smaller by `sizeFunc`. Ill-formed candidates are filtered out by
    `shrinkWhile` (via `funcWellFormed`).

    The two precondition families delegate to the shared `shrinkLExpr`, exactly as
    the procedure shrinker does for a contract clause. Dropping a clause is offered
    before reducing one, so the bigger reduction is tried first. Both are guarded by
    `funcWellFormed`, which keeps a reduced clause Boolean and scoped to the formals
    — a guard nothing else provides, since `Function.typeCheck` does not check
    preconditions at all.

    Note the interaction with `dropInput`: a candidate that drops the formal a clause
    mentions *is* proposed here, and `funcWellFormed` rejects it, because the clause
    would be left referring to nothing. Dropping that formal is still reachable in
    two steps — drop the clause, then the input — which is why the drop-clause family
    comes first. -/
def shrinkFunc (f : Function) : List Function :=
  let ins := f.inputs.toList
  let pres := f.preconditions
  let dropBody    := if f.body.isSome then [{ f with body := none }] else []
  let dropMeasure := if f.measure.isSome then [{ f with measure := none }] else []
  let dropPrecond := (fun ps => { f with preconditions := ps }) <$> dropEach pres
  let dropInput   := (fun i => { f with inputs := ListMap.ofList i }) <$> dropEach ins
  let dropTyArg   := (fun tas => { f with typeArgs := tas }) <$> dropEach f.typeArgs
  let shrinkPrecond := pres.zipIdx.flatMap (fun (pc, i) =>
    (fun e => { f with preconditions := pres.set i { pc with expr := e } })
      <$> shrinkLExpr pc.expr)
  let shrinkInput := ins.zipIdx.flatMap (fun ((x, ty), i) =>
    (fun ty' => { f with inputs := ListMap.ofList (ins.set i (x, ty')) }) <$> shrinkTy ty)
  let shrinkOut   := (fun o => { f with output := o }) <$> shrinkTy f.output
  let shrinkName  := if f.name.name.length > 1 then [{ f with name := ⟨"f", ()⟩ }] else []
  dropBody ++ dropMeasure ++ dropPrecond ++ dropInput ++ dropTyArg
    ++ shrinkPrecond ++ shrinkInput ++ shrinkOut ++ shrinkName

/-- First candidate (in order) that still satisfies the failure predicate. -/
partial def firstSatisfying (p : Function → IO Bool) : List Function → IO (Option Function)
  | [] => pure none
  | c :: rest => do if ← p c then pure (some c) else firstSatisfying p rest

/-- Greedily shrink `f` while preserving `p`. Candidates must be strictly
    smaller *and* well-formed, so the minimal witness is a genuine
    `genFunction`-shaped function. -/
partial def shrinkWhile (p : Function → IO Bool) (fuel : Nat) (f : Function) : IO Function := do
  match fuel with
  | 0 => pure f
  | fuel + 1 =>
    let cands := (shrinkFunc f).filter (fun c => sizeFunc c < sizeFunc f && funcWellFormed c)
    match ← firstSatisfying p cands with
    | some c => shrinkWhile p fuel c
    | none => pure f

-- ── Failure predicates (shrink targets) ──────────────────────────────────

/-- Any round-trip failure: the printed program either fails to parse, or
    format→parse→re-format is not a fixed point. -/
def failsRoundtrip (f : Function) : IO Bool := do
  let s1 := formatFuncAsProgram f
  match ← parseCoreProgram s1 with
  | some ast2 => pure (s1 != (Core.formatProgram ast2).pretty)
  | none => pure true

/-- The printed program PARSES but does not round-trip (mismatch class). -/
def failsRoundtripParsed (f : Function) : IO Bool := do
  let s1 := formatFuncAsProgram f
  match ← parseCoreProgram s1 with
  | some ast2 => pure (s1 != (Core.formatProgram ast2).pretty)
  | none => pure false

/-- The printed program does NOT parse at all (parse-failure class). -/
def failsRoundtripParseFail (f : Function) : IO Bool := do
  match ← parseCoreProgram (formatFuncAsProgram f) with
  | some _ => pure false
  | none => pure true
