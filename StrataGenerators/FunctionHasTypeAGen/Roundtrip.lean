import StrataGenerators.FunctionHasTypeAGen.TestSupport
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda Core Imperative Strata Strata.CoreDDM
open StrataDDM (initDialect)

/-!
# Shared round-trip helpers and shrinker for Strata Core `Function`s

This module is imported by *both* property-based test harnesses
(`PlausibleTestMain.lean` and `TycheMain.lean`) so the pretty-print/parse
round-trip machinery and the structural shrinker live in exactly one place.

It provides:
- `formatFuncAsProgram` / `parseCoreProgram` / `parseCoreProgramErr` — embed a
  `Function` in a one-decl `Program`, format via `Core.formatProgram`, and parse
  back via the Core DDM dialect (the error variant surfaces the parser message).
- A greedy structural shrinker (`shrinkWhile`) plus failure predicates, used to
  reduce a round-trip counterexample to a minimal reproducer.

**Well-formedness invariant.** Every shrink candidate is required to satisfy
`funcWellFormed` (every free type variable in the signature is declared in
`typeArgs`), matching the invariant `genFunction` maintains. Without this the
shrinker could drop a `∀`-bound type-arg while leaving it used in a type,
yielding an *undeclared type variable* — an ill-formed function whose parse
failure is a shrinker artifact rather than a genuine printer/parser bug.
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

/-- Immediate smaller candidates for a monotype: collapse a compound toward a
    child or toward `int`, a type variable / bitvector toward `int`, and shrink
    children in place. Base types have no smaller form. -/
partial def shrinkTy : LMonoTy → List LMonoTy
  | .ftvar _ => []
  | .bitvec _ => []
  | .tcons _ [] => []
  | .tcons "arrow" [a, b] =>
    [a, b]
      ++ (shrinkTy a).map (fun a' => .tcons "arrow" [a', b])
      ++ (shrinkTy b).map (fun b' => .tcons "arrow" [a, b'])
  | .tcons "Map" [k, v] =>
    [k, v]
      ++ (shrinkTy k).map (fun k' => .tcons "Map" [k', v])
      ++ (shrinkTy v).map (fun v' => .tcons "Map" [k, v'])
  | .tcons "Sequence" [e] =>
    e :: (shrinkTy e).map (fun e' => .tcons "Sequence" [e'])
  | .tcons _ args => args ++ List.flatMap shrinkTy args

/-- All ways to drop exactly one element of a list. -/
def dropEach {α} : List α → List (List α)
  | [] => []
  | x :: xs => xs :: (dropEach xs).map (x :: ·)

/-- Well-formedness of a shrink candidate. `genFunction` maintains all of these
    invariants; the shrinker must preserve them so it never fabricates a failure
    that is really an *ill-formed* function (which the parser would rightly
    reject) rather than a genuine printer/parser bug. Two conditions:

    1. **Scoping** — every free type variable in the signature (inputs + output)
       is declared in `typeArgs`.
    2. **Body typing** — the body (if present) type-checks at the declared
       `output`, and the measure (if present) at `int`. This is essential:
       `shrinkFunc` can collapse `output` toward `int` (`shrinkOut`) *without*
       touching the body, which would leave e.g. a `real`-returning lambda body
       under an `int` output — an ill-typed function whose parse failure is a
       shrinker artifact, not a Strata bug. Re-checking here rejects such
       candidates. -/
def funcWellFormed (f : Function) : Bool :=
  let used := f.output.freeVars ++ (f.inputs.toList.flatMap (fun p => p.2.freeVars))
  let scopedOk := used.all (· ∈ f.typeArgs)
  let bodyOk := match f.body with
    | some b => LExpr.typeCheck (T := CoreLParams) [] b == some f.output
    | none => true
  let measureOk := match f.measure with
    | some m => LExpr.typeCheck (T := CoreLParams) [] m == some .int
    | none => true
  scopedOk && bodyOk && measureOk

/-- Candidate smaller functions: drop body/measure, drop an input, drop a
    type-arg, shrink an input type, shrink the output type, or shorten the name.
    All candidates are strictly smaller by `sizeFunc`. Ill-formed candidates are
    filtered out by `shrinkWhile`. -/
def shrinkFunc (f : Function) : List Function :=
  let ins := f.inputs.toList
  let dropBody    := if f.body.isSome then [{ f with body := none }] else []
  let dropMeasure := if f.measure.isSome then [{ f with measure := none }] else []
  let dropInput   := (dropEach ins).map (fun i => { f with inputs := ListMap.ofList i })
  let dropTyArg   := (dropEach f.typeArgs).map (fun tas => { f with typeArgs := tas })
  let shrinkInput := (List.range ins.length).flatMap (fun i =>
    match ins[i]? with
    | some (x, ty) => (shrinkTy ty).map (fun ty' =>
        { f with inputs := ListMap.ofList (ins.set i (x, ty')) })
    | none => [])
  let shrinkOut   := (shrinkTy f.output).map (fun o => { f with output := o })
  let shrinkName  := if f.name.name.length > 1 then [{ f with name := ⟨"f", ()⟩ }] else []
  dropBody ++ dropMeasure ++ dropInput ++ dropTyArg ++ shrinkInput ++ shrinkOut ++ shrinkName

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
