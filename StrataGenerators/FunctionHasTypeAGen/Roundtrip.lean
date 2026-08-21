import StrataGenerators.FunctionHasTypeAGen.TestSupport
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda Core Imperative Strata Strata.CoreDDM
open StrataDDM (initDialect)

/-!
# The shared functions for the round trip of a Strata Core `Function`

This module holds exactly what the round-trip property for the parser and the printer needs.
*Both* consumers import it: the property suite, and the Tyche panels in
`StrataGenerators.TycheViz`. The code for the round trip from a printed form to a parsed form
therefore has one place only.

The module gives two groups of definitions:
- `formatFuncAsProgram`, `parseCoreProgram` and `parseCoreProgramErr`. They put a `Function`
  into a `Program` with one declaration, they print it with `Core.formatProgram`, and they
  parse the text again through the Core dialect of DDM. The variant with `Err` in its name
  also gives the message of the parser.
- A greedy shrinker, `shrinkWhile`, and the predicates for a failure. They reduce a
  counterexample of the round trip to a small reproducer. This shrinker also *reduces the
  signature*, and it belongs to the round-trip property. It is separate from the shrinker for
  the `Shrinkable Function` instance, which changes only the body and which lives in
  `StrataGenerators.FunctionHasTypeAGen.Shrink`.

**The invariant about good form.** Each candidate of the shrinker must satisfy
`funcWellFormed`, which says that `typeArgs` declares each free type variable of the
signature. `genFunction` keeps the same invariant. Without the filter, the shrinker could
remove a type argument that a type still uses, and the result would hold a type variable with
no declaration. Such a function is not well formed, and a failure of its parse is an artifact
of the shrinker and not a real defect of the printer or of the parser.

`funcWellFormed` is public here, because the `Shrink` module uses it as its filter for a
candidate.
-/

-- ── The round trip from a printed form to a parsed form ──────────────────

/-- Puts a function into a `Program` with one declaration, and prints it with
    `Core.formatProgram`. The round-trip property tests this string. -/
def formatFuncAsProgram (func : Function) : String :=
  let prog : Core.Program := { decls := [ .func func .empty ] }
  (Core.formatProgram prog).pretty

/-- Prints one `Function` with `Core.formatProgram`, and removes the `program Core;` header. The
    result is the concrete syntax of Strata Core for the declaration of the function alone, for use
    as a label in a report. Use this function and not a printer of your own, so that a report shows
    the output of the real formatter. -/
def formatFunc (func : Function) : String :=
  let s := formatFuncAsProgram func
  if s.startsWith "program Core;\n\n" then
    (s.drop "program Core;\n\n".length).toString else s.trimAscii.toString

/-- Puts a list of statements into the body of a trivial procedure `p`, in a `Program` with one
    declaration, and prints it with `Core.formatProgram`. The result is the real concrete syntax of
    Strata Core for the statements, so a `funcDecl`, a `block`, a `while` and each other statement
    appear as the grammar gives them, and not in a form that this package invents.

    One limit applies, and it shows a real limitation and not a defect of the output. The CST
    formatter of Core cannot write a **`funcDecl` statement with no body**. The grammar rule
    `funcDecl_statement` needs a body, so `funcDeclToStatement` writes a placeholder `body`
    expression and it logs an internal error for a `funcDecl` whose declaration has no body. Such a
    statement is exactly the counterexample to the completeness of the type checker, which is a
    `funcDecl` with a measure and no body. Its printed form therefore shows a placeholder body. The
    `[body=…]` tag on the counterexample, which the `Repr` instance of the harness writes, gives the
    true shape. -/
def formatStmtsAsProgram (ss : List Statement) : String :=
  let proc : Core.Procedure :=
    { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
      spec := default,
      body := .structured ss }
  let prog : Core.Program := { decls := [ .proc proc .empty ] }
  (Core.formatProgram prog).pretty

/-- Prints a list of statements with the formatter of Strata, and removes the `program Core;`
    header. A report of a counterexample uses the result as a label. The output holds a `funcDecl`, a
    `block`, a `while` and each other statement in the real concrete syntax of Core. -/
def formatStmts (ss : List Statement) : String :=
  let s := formatStmtsAsProgram ss
  if s.startsWith "program Core;\n\n" then
    (s.drop "program Core;\n\n".length).toString else s.trimAscii.toString

/-- Parses the text of a Core program back to the Strata Core AST. The result is `none` when the
    parse fails or when the translation fails. -/
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

/-- The same work as `parseCoreProgram`, but on a failure the result holds the message. That message
    is the text of the exception from the parser, or the errors from the translation. -/
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

-- ── The structural shrinker ──────────────────────────────────────────────

/-- The structural size of a type. Each reduction below makes this size smaller. -/
def sizeTy : LMonoTy → Nat
  | .ftvar _ => 2
  | .bitvec _ => 2
  | .tcons _ args => 1 + (args.map sizeTy).foldl (· + ·) 0

/-- The structural size of a function. Each reduction below makes this size smaller. -/
def sizeFunc (f : Function) : Nat :=
  f.name.name.length
    + sizeTy f.output
    + (f.inputs.toList.map (fun p => 1 + sizeTy p.2)).foldl (· + ·) 0
    + f.typeArgs.length
    + (match f.body with | some _ => 1 | none => 0)
    + (match f.measure with | some _ => 1 | none => 0)
    -- Each `requires` clause counts the size of its expression and one more for the clause
    -- itself. The *removal* of a clause is therefore smaller than a reduction of its expression
    -- to a leaf. `sizeCheck` uses the same convention for the contract of a procedure. Without
    -- this part of the sum, the test for a smaller size in `shrinkWhile` would remove each
    -- reduction of a precondition below.
    + (f.preconditions.map (fun pc => 1 + pc.expr.sizeOf)).foldl (· + ·) 0

/-- The smaller candidates for a monotype, in one step. The function replaces a compound type by one
    of its children, and it reduces a child in place. A base type has no smaller form. -/
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

/-- Whether a candidate of the shrinker is well formed. `genFunction` keeps each of these
    invariants, and the shrinker must keep them also, so that it never gives a failure that comes
    from an *ill-formed* function. The parser correctly rejects such a function, and that rejection
    is not a defect of the printer or of the parser. Four conditions must hold:

    1. **The scope.** `typeArgs` declares each free type variable of the signature, which holds the
       inputs and the output.
    2. **The typing of the body.** The body, when it exists, typechecks at the declared `output`, and
       the measure, when it exists, typechecks at `int`. This condition is necessary. `shrinkFunc`
       can replace `output` by `int` through `shrinkOut` and *not* change the body. The result can
       then be a lambda body that returns a `real` under an output of `int`. Such a function is
       ill-typed, and a failure of its parse is an artifact of the shrinker and not a defect of
       Strata. A second type check here rejects such a candidate.
    3. **The typing of a precondition.** Each `requires` clause typechecks at `bool`.
    4. **The scope of a precondition.** Each free variable of a clause is a formal parameter.

    Conditions 3 and 4 duplicate no type checker. `Function.typeCheck` never reads
    `preconditions`, so it neither typechecks a clause nor checks its free variables. This predicate
    is therefore the only thing that stops a reduction from leaving a clause without its variable.
    The removal of an input that a clause mentions, which `dropInput` below offers, leaves
    `requires y == 0` with no `y` in the signature. A reduction of the expression of a clause can
    also make the expression not Boolean. `genFunction` emits a clause over the formal parameters on
    about half of its draws, so both cases occur and neither is only theoretical.

    `StrataGenerators.Program.TestSupport.funcPreconditionsScoped` also states condition 4 on its
    own, and its documentation gives the full analysis of the gap. Both conditions are here, so each
    family that reduces a function gets them from one filter. Those families are the `shrinkFunc` of
    this module, the `Shrinkable Function` instance, and the `.func` case of the whole-program
    shrinker. -/
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

/-- The smaller candidates for a function. The shrinker removes the body, removes the measure,
    removes a `requires` clause, removes an input, removes a type argument, reduces the expression of
    a `requires` clause, reduces an input type, reduces the output type, or makes the name shorter.
    Each candidate is smaller by `sizeFunc`. `shrinkWhile` removes a candidate that is not well
    formed, through `funcWellFormed`.

    The two families for a precondition use the shared `shrinkLExpr`, in the same way as the
    shrinker for a procedure does for a clause of a contract. The removal of a clause comes before a
    reduction of one, so the shrinker tries the larger reduction first. `funcWellFormed` guards both
    families, and it keeps a reduced clause Boolean and in the scope of the formal parameters.
    Nothing else gives that guard, because `Function.typeCheck` checks no precondition.

    Note how the families work with `dropInput`. This function *does* offer a candidate that removes
    the formal parameter which a clause mentions, and `funcWellFormed` then rejects that candidate,
    because the clause would refer to nothing. The removal of that formal parameter is still
    reachable in two steps: remove the clause, and then remove the input. This is the reason why the
    family that removes a clause comes first. -/
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

/-- The first candidate in the list that still satisfies the predicate for a failure. -/
partial def firstSatisfying (p : Function → IO Bool) : List Function → IO (Option Function)
  | [] => pure none
  | c :: rest => do if ← p c then pure (some c) else firstSatisfying p rest

/-- Reduces `f` greedily, and keeps `p` true. Each candidate must be smaller *and* well formed, so
    the smallest witness is a function with the shape that `genFunction` gives. -/
partial def shrinkWhile (p : Function → IO Bool) (fuel : Nat) (f : Function) : IO Function := do
  match fuel with
  | 0 => pure f
  | fuel + 1 =>
    let cands := (shrinkFunc f).filter (fun c => sizeFunc c < sizeFunc f && funcWellFormed c)
    match ← firstSatisfying p cands with
    | some c => shrinkWhile p fuel c
    | none => pure f

-- ── The predicates for a failure, which the shrinker keeps true ──────────

/-- Any failure of the round trip. Either the printed program does not parse, or the sequence of a
    print, a parse and a second print is not a fixed point. -/
def failsRoundtrip (f : Function) : IO Bool := do
  let s1 := formatFuncAsProgram f
  match ← parseCoreProgram s1 with
  | some ast2 => pure (s1 != (Core.formatProgram ast2).pretty)
  | none => pure true

/-- The printed program parses, and the round trip does not give the same text. This is the class of
    failure where the two printed forms differ. -/
def failsRoundtripParsed (f : Function) : IO Bool := do
  let s1 := formatFuncAsProgram f
  match ← parseCoreProgram s1 with
  | some ast2 => pure (s1 != (Core.formatProgram ast2).pretty)
  | none => pure false

/-- The printed program does not parse. This is the class of failure where the parser rejects the
    text. -/
def failsRoundtripParseFail (f : Function) : IO Bool := do
  match ← parseCoreProgram (formatFuncAsProgram f) with
  | some _ => pure false
  | none => pure true
