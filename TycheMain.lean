import StrataGenerators.Tyche
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.Roundtrip
import StrataGenerators.StmtHasTypeAGen.TestSupport
import Basalt.IO
import Strata.DL.Lambda.LExprT
-- Imports for Function.typeCheck property (typeCheck_annotated_sound)
import Strata.Languages.Core.FunctionType
import Strata.DL.Lambda.Denote.LExprAnnotated
-- Imports for pretty-print/parse round-trip property
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Grammar
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

open Lambda RandomChoice ArbNat Tyche Std Core Imperative
open Strata Strata.CoreDDM
open StrataDDM (initDialect)

/-!
# Tyche Visualization Runner

This executable generates samples from the `HasTypeA` generator and writes
them in Tyche JSONL format for visualization.

## Usage

```
lake build tyche-viz && .lake/build/bin/tyche-viz [numSamples] [outputPath]
```

Then open the output file with the Tyche VS Code extension (`Tyche: Open`).
-/

-- ── Pretty-printing ──────────────────────────────────────────────────
-- These differ from Strata's built-in `ToFormat LMonoTy` / `ToFormat (LExpr T)`:
--   • Types: arrows print as `α -> bool` instead of `(arrow α bool)`.
--     Higher-order function arguments are parenthesized appropriately, e.g.
--     `(int -> int) -> bool` (since the function arrow is right-associative by default)
--   • Exprs: precedence-based parenthesization instead of wrapping every
--     compound subexpression in parens. Binder bodies extend to the right
--     without extra parens (`λint. λint. #1`), and application is left-
--     associative (`f x y` means `(f x) y`; only compound arguments like
--     lambdas or if-then-else get wrapped).

-- ppType and ppExpr are imported from TestSupport

-- ── Feature extraction ────────────────────────────────────────────────

/-- Compute the depth (nesting level) of an LExpr. -/
def exprDepth : LExpr' → Nat
  | .abs _ _ _ body => exprDepth body + 1
  | .app _ fn arg => max (exprDepth fn) (exprDepth arg) + 1
  | .ite _ c t e => max (exprDepth c) (max (exprDepth t) (exprDepth e)) + 1
  | .eq _ e₁ e₂ => max (exprDepth e₁) (exprDepth e₂) + 1
  | .quant _ _ _ _ tr body => max (exprDepth tr) (exprDepth body) + 1
  | _ => 0

/-- Compute the size (number of nodes) of an LExpr (delegates to `LExpr.size` from Strata). -/
def exprSize (e : LExpr') : Nat := LExpr.size LExprParamsT' e

/-- Classify the top-level expression constructor. -/
def exprKind : LExpr' → String
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

/-- Classify the top-level type constructor. -/
def typeKind : LMonoTy → String
  | .bool => "bool"
  | .int => "int"
  | .arrow _ _ => "arrow"
  | .ftvar _ => "ftvar"
  | .bitvec _ => "bitvec"
  | .tcons _ _ => "tcons"

/-- A generated expression paired with its type and the depth (size parameter to the generator) used to generate it, ready for Tyche. -/
structure TypedExpr where
  expr : LExpr'
  ty : LMonoTy
  generatorSize : Nat
instance : Tyche.TycheSample TypedExpr where
  toSample te :=
    { representation := ppExpr te.expr
      features := [
        ("depth", .ordinal (exprDepth te.expr)),
        ("LExpr.size", .ordinal (exprSize te.expr)),
        ("expr_kind", .nominal (exprKind te.expr)),
        ("type_kind", .nominal (typeKind te.ty)),
        ("type_depth", .ordinal (monoTyDepth te.ty)),
        ("generator_size", .ordinal te.generatorSize)
      ] }

/-- A generated expression carrying *only* its term-kind classification.
    Because the sample has a single nominal feature, Tyche renders it as a
    plain bar chart (the "distribution of term_kind") rather than a mosaic. -/
structure TermKind where
  expr : LExpr'
instance : Tyche.TycheSample TermKind where
  toSample tk :=
    { representation := ppExpr tk.expr
      features := [
        ("term_kind", .nominal (exprKind tk.expr))
      ] }

/-- A generated monotype, ready for Tyche. -/
instance : Tyche.TycheSample LMonoTy where
  toSample ty :=
    { representation := ppType ty
      features := [
        ("depth", .ordinal (monoTyDepth ty)),
        ("type_kind", .nominal (typeKind ty))
      ] }

-- ── Typecheck property ────────────────────────────────────────────────

/-- Result of generating an expression and running the typechecker on it. -/
structure TypeCheckResult where
  expr : LExpr'
  expectedTy : LMonoTy
  actualTy : Option LMonoTy
  generatorSize : Nat

/-- The typecheck property passes when `LExpr.typeCheck [] expr = some expectedTy`. -/
instance : Tyche.TycheSample TypeCheckResult where
  toSample r :=
    let passed := r.actualTy == some r.expectedTy
    let statusStr := if passed then "pass" else "fail"
    { representation := s!"{ppExpr r.expr} : {ppType r.expectedTy}"
      status := if passed then .passed else .failed
      features := [
        ("typecheck_result", .nominal statusStr),
        ("expected_type_kind", .nominal (typeKind r.expectedTy)),
        ("exprDepth", .ordinal (exprDepth r.expr)),
        ("LExpr.size", .ordinal (exprSize r.expr)),
        ("exprKind", .nominal (exprKind r.expr)),
        ("monoTyDepth", .ordinal (monoTyDepth r.expectedTy)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

-- ── Type preservation property ────────────────────────────────────────

/-- Result of generating, evaluating, and re-typechecking. -/
structure EvalResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  evaledTy : Option LMonoTy
  exprIsValue : Bool
  madeProgress : Bool
  generatorSize : Nat

instance : Tyche.TycheSample EvalResult where
  toSample r :=
    let preserved := r.evaledTy == some r.expectedTy
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status := if preserved then .passed else .failed
      features := [
        ("preservation", .nominal (if preserved then "pass" else "fail")),
        ("is_value", .nominal (if r.exprIsValue then "value" else "non-value")),
        ("made_progress", .nominal (if r.madeProgress then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

-- ── Generator wrappers ────────────────────────────────────────────────
-- Each wrapper varies the depth parameter uniformly over [1, 5] so that
-- Tyche visualizations cover the full range of generator behavior, not
-- just a single fixed depth.

/-- Randomly choose a depth between 1 and `maxDepth` (inclusive). -/
def randomDepth (maxDepth : Nat := 5) : IO Nat := do
  let r ← IO.rand 1 maxDepth
  return r

/-- Generate a typed expression with free variables from `defaultFCtx`. -/
def genTypedExpr (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO TypedExpr := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) defaultFCtx coreOpCtx corePolyOps tvars [] d ty
  return ⟨expr, ty, d⟩

/-- Generate an expression and keep only its term-kind classification. -/
def genTermKind (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO TermKind := do
  let te ← genTypedExpr depth tvars
  return ⟨te.expr⟩

/-- Generate just a monotype. -/
def genType (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO LMonoTy := do
  let d ← if depth == 0 then randomDepth else pure depth
  genLMonoTy (G := IO) tvars d

/-- Generate an expression and typecheck it against the expected type. -/
def genAndTypeCheck (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO TypeCheckResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) defaultFCtx coreOpCtx corePolyOps tvars [] d ty
  let actualTy := LExpr.typeCheck (T := LExprParams') [] expr
  return ⟨expr, ty, actualTy, d⟩

/-- Generate a closed expression, evaluate it, and check type preservation.
    Uses empty fctx since preservation is stated for the empty context. -/
def genAndEval (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] coreOpCtx corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  let evaledTy := LExpr.typeCheck (T := LExprParams') [] evaled
  return ⟨expr, ty, evaled, evaledTy, isValue expr, !(expr == evaled), d⟩

-- ── Eval progress property ───────────────────────────────────────────

/-- Result of checking whether `LExpr.eval` makes progress on a generated term. -/
structure EvalProgressResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  madeProgress : Bool
  inputIsValue : Bool
  generatorSize : Nat

instance : Tyche.TycheSample EvalProgressResult where
  toSample r :=
    let status := if r.madeProgress || r.inputIsValue then Tyche.Status.passed
                  else .failed
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status
      features := [
        ("made_progress", .nominal (if r.madeProgress then "yes" else "no")),
        ("input_is_value", .nominal (if r.inputIsValue then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_depth", .ordinal (exprDepth r.expr)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a closed expression and check whether eval makes progress (or
    the input is already a value). Uses empty fctx since progress is stated
    for the empty context. -/
def genAndCheckProgress (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO EvalProgressResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] coreOpCtx corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  return ⟨expr, ty, evaled, !(expr == evaled), isValue expr, d⟩

-- ── Fvar preservation property ───────────────────────────────────────

structure FvarPreservationResult where
  expr : LExpr'
  expectedTy : LMonoTy
  evaled : LExpr'
  fvarsPreserved : Bool
  genDepth : Nat

instance : Tyche.TycheSample FvarPreservationResult where
  toSample r :=
    { representation := s!"{ppExpr r.expr}  ⟶  {ppExpr r.evaled}"
      status := if r.fvarsPreserved then .passed else .failed
      features := [
        ("fvars_preserved", .nominal (if r.fvarsPreserved then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("input_size", .ordinal (exprSize r.expr)),
        ("output_size", .ordinal (exprSize r.evaled)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("gen_depth", .ordinal r.genDepth)
      ] }

def genAndCheckFvarPreservation (depth : Nat := 0) (tvars : List TyIdentifier := ["α", "β"]) : IO FvarPreservationResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) defaultFCtx coreOpCtx corePolyOps tvars [] d ty
  let evaled := eval 100 expr
  let inputFvars := LExpr.collectFvarNames expr
  let outputFvars := LExpr.collectFvarNames evaled
  let preserved := outputFvars.all (· ∈ inputFvars)
  return ⟨expr, ty, evaled, preserved, d⟩

-- ── Sequence.map inspection panel ────────────────────────────────────
-- This panel is *not* a pass/fail property in the usual sense: it exists so we
-- can eyeball the terms `genLExpr` produces that actually call `Sequence.map`
-- via the IndirPoly rule, and confirm the type variables `α`, `β` are
-- instantiated consistently. `Sequence.map : ∀α β. (α → β) → Sequence<α> →
-- Sequence<β>`; targeting `Sequence<β>` fixes `β` by unification but leaves `α`
-- to be *sampled* from the generable types.

/-- Find the first `Sequence.map` op-node in an expression and recover the
    instantiated `(α, β)` from its annotation `(α → β) → Sequence<α> → Sequence<β>`. -/
partial def seqMapInstantiation : LExpr' → Option (LMonoTy × LMonoTy)
  | .op _ o (some (.arrow (.arrow a b) _)) =>
    if o.name == "Sequence.map" then some (a, b) else none
  | .op _ _ _ => none
  | .app _ fn arg => match seqMapInstantiation fn with
    | some r => some r | none => seqMapInstantiation arg
  | .abs _ _ _ body => seqMapInstantiation body
  | .quant _ _ _ _ tr body => match seqMapInstantiation tr with
    | some r => some r | none => seqMapInstantiation body
  | .ite _ c t e => match seqMapInstantiation c with
    | some r => some r
    | none => match seqMapInstantiation t with
      | some r => some r | none => seqMapInstantiation e
  | .eq _ e₁ e₂ => match seqMapInstantiation e₁ with
    | some r => some r | none => seqMapInstantiation e₂
  | _ => none

/-- Whether an expression calls `Sequence.map` anywhere. -/
def usesSeqMap (e : LExpr') : Bool := (seqMapInstantiation e).isSome

structure SeqMapResult where
  expr : LExpr'
  ty : LMonoTy
  /-- Whether rejection sampling actually found a `Sequence.map` call within
      budget (if `false`, the panel shows a fallback term). -/
  found : Bool
  generatorSize : Nat

instance : Tyche.TycheSample SeqMapResult where
  toSample r :=
    let inst := seqMapInstantiation r.expr
    let wellTyped := LExpr.typeCheck (T := LExprParams') [] r.expr == some r.ty
    -- A sample "passes" iff it is a well-typed Sequence.map call.
    let passed := r.found && wellTyped
    let instStr := match inst with
      | some (a, b) => s!"   [α := {ppType a}, β := {ppType b}]"
      | none => ""
    { representation := s!"{ppExpr r.expr} : {ppType r.ty}{instStr}"
      status := if passed then .passed else .failed
      features := [
        ("calls_seq_map", .nominal (if r.found then "yes" else "no")),
        ("well_typed", .nominal (if wellTyped then "yes" else "no")),
        -- The sampled α and the unification-fixed β, as observed on the node.
        ("alpha", .nominal (match inst with | some (a, _) => ppType a | none => "—")),
        ("beta", .nominal (match inst with | some (_, b) => ppType b | none => "—")),
        ("alpha_eq_beta", .nominal (match inst with
          | some (a, b) => if a == b then "yes" else "no"
          | none => "—")),
        ("expr_depth", .ordinal (exprDepth r.expr)),
        ("expr_size", .ordinal (exprSize r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Rejection-sample until `genLExpr` produces a term that calls `Sequence.map`.
    We target `Sequence<elem>` types directly (element drawn from a small easy
    set) to keep the hit rate up, and retry up to `budget` draws. If none is
    found in budget, return the last generated term with `found := false` so the
    run still terminates (mirrors `genResolveCounterexample`).

    The per-sample depth floor is 3 (not 2): at depth 2 there is often not
    enough budget to build both of `Sequence.map`'s arguments (a function
    `α → β` and a `Sequence<α>`) in one non-backtracking draw. `budget` is kept
    modest to keep the overall run fast — most samples are genuine
    `Sequence.map` calls, and the occasional fallback (a non-`Sequence.map`
    term) is fine: it is marked `calls_seq_map = no` and scored `failed` so it
    is visually distinct in the panel. -/
partial def genSeqMapCall (budget : Nat := 600) : IO SeqMapResult := do
  let d ← IO.rand 3 5
  let elems : List LMonoTy := [.int, .bool]
  let mut last : Option (LExpr' × LMonoTy) := none
  for _ in List.range budget do
    let ei ← IO.rand 0 (elems.length - 1)
    let ty := LMonoTy.seq (elems.getD ei .int)
    let r ← try some <$> genLExprWithOps (G := IO) defaultFCtx coreOpCtx corePolyOps [] [] d ty
            catch _ => pure none
    match r with
    | some e =>
      last := some (e, ty)
      if usesSeqMap e then return ⟨e, ty, true, d⟩
    | none => pure ()
  match last with
  | some (e, ty) => return ⟨e, ty, false, d⟩
  | none => return ⟨.const () (.boolConst true), .bool, false, d⟩

-- ── Resolve after erasure property ──────────────────────────────────

private def resolveKnownTypes : Lambda.KnownTypes :=
  open Lambda.LTy.Syntax in
  Lambda.makeKnownTypes ([t[∀a b. %a → %b],
    t[bool], t[int], t[string], t[real], t[regex],
    t[∀n. bitvec n],
    t[∀a b. Map %a %b],
    t[∀a. Sequence %a]].map (fun k => k.toKnownType!))

private def resolveLContext : Lambda.LContext LExprParams' :=
  { Lambda.LContext.default with
    functions := intBoolFactory,
    knownTypes := resolveKnownTypes }

private def intBoolOpCtx : OpCtx := factoryOps intBoolFactory

/-- Erase *all* type annotations on an `LExpr`, including the binder-type
    annotations on lambdas (`abs`) and quantifiers (`quant`). -/
private def eraseAllTypes : LExpr' → LExpr'
  | .const m c => .const m c
  | .op m o _ => .op m o none
  | .fvar m x _ => .fvar m x none
  | .bvar m i => .bvar m i
  | .abs m name _ e => .abs m name none (eraseAllTypes e)
  | .quant m qk name _ tr e => .quant m qk name none (eraseAllTypes tr) (eraseAllTypes e)
  | .app m e1 e2 => .app m (eraseAllTypes e1) (eraseAllTypes e2)
  | .ite m c t f => .ite m (eraseAllTypes c) (eraseAllTypes t) (eraseAllTypes f)
  | .eq m e1 e2 => .eq m (eraseAllTypes e1) (eraseAllTypes e2)

/-- Whether the expression contains a quantifier (`∀`/`∃`) anywhere. Every known
    counterexample to the resolve-after-erase property contains one: after the
    binder annotation is erased, `LExpr.resolve` gives the bound variable a fresh
    type variable and then rejects the quantifier with a *syntactic* `≠ bool`
    check on the body instead of unifying it with `bool`. -/
private def containsQuant : LExpr' → Bool
  | .quant _ _ _ _ _ _ => true
  | .abs _ _ _ b => containsQuant b
  | .app _ a b => containsQuant a || containsQuant b
  | .ite _ c t e => containsQuant c || containsQuant t || containsQuant e
  | .eq _ a b => containsQuant a || containsQuant b
  | _ => false

/-- Whether the ground type `target` is a substitution instance of `inferred`
    (i.e. `inferred` generalizes `target`), checked via unification. This also
    abstracts over the names of the fresh type variables `resolve` introduces. -/
private def isInstanceOf (target inferred : LMonoTy) : Bool :=
  match Lambda.Constraints.unify [(inferred, target)] Lambda.SubstInfo.empty with
  | .ok _ => true
  | .error _ => false

structure ResolveAfterEraseResult where
  expr : LExpr'
  expectedTy : LMonoTy
  resolvedTy : Option LMonoTy
  generatorSize : Nat

instance : Tyche.TycheSample ResolveAfterEraseResult where
  toSample r :=
    -- Counterexample-focused scoring: a sample PASSES only when `resolve`
    -- succeeds *and* infers a type the generation type is an instance of.
    -- A `resolve` *failure* is now scored as a FAIL (a counterexample) rather
    -- than a vacuous pass, so these cases surface in the Tyche panel. The
    -- `failure_mode` feature distinguishes the two kinds of counterexample.
    let failureMode := match r.resolvedTy with
      | some inferred => if isInstanceOf r.expectedTy inferred then "none" else "wrong_type"
      | none => "resolve_failed"
    let passed := failureMode == "none"
    let general := match r.resolvedTy with
      | some inferred => !(inferred == r.expectedTy)
      | none => false
    { representation := match r.resolvedTy with
        | some inferred => s!"{ppExpr r.expr}, expected = {ppType r.expectedTy}, inferred = {ppType inferred}"
        | none => s!"{ppExpr r.expr} : {ppType r.expectedTy} (LExpr.resolve failed to infer type)"
      status := if passed then .passed else .failed
      features := [
        ("resolve_result", .nominal (if passed then "pass" else "fail")),
        -- Which kind of counterexample: `resolve_failed` (resolve errored) vs
        -- `wrong_type` (resolve succeeded but inferred a non-instance type) vs
        -- `none` (passing sample).
        ("failure_mode", .nominal failureMode),
        -- Does the counterexample contain a quantifier? (Expected: every failure.)
        ("has_quantifier", .nominal (if containsQuant r.expr then "yes" else "no")),
        ("inferred_more_general", .nominal (if general then "yes" else "no")),
        ("resolve_succeeded", .nominal (if r.resolvedTy.isSome then "yes" else "no")),
        ("type_kind", .nominal (typeKind r.expectedTy)),
        ("expr_depth", .ordinal (exprDepth r.expr)),
        ("expr_size", .ordinal (exprSize r.expr)),
        ("expr_kind", .nominal (exprKind r.expr)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate one expression, erase its type annotations, and re-infer with
    `LExpr.resolve`. The `resolvedTy` is `none` when `resolve` errors. -/
def genAndCheckResolveAfterErase (depth : Nat := 0) : IO ResolveAfterEraseResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let tvars : List TyIdentifier := []
  let ty ← genLMonoTy (G := IO) tvars d
  let expr ← genLExprWithOps (G := IO) [] intBoolOpCtx [] tvars [] d ty
  let erased := eraseAllTypes expr
  let resolvedTy := match LExpr.resolve resolveLContext Lambda.TEnv.default erased with
    | .ok (resolved, _) => some resolved.toLMonoTy
    | .error _ => none
  return ⟨expr, ty, resolvedTy, d⟩

/-- Whether a result is a counterexample to the resolve-after-erase property:
    either `resolve` failed, or it inferred a type the generation type is not an
    instance of. -/
private def isResolveCounterexample (r : ResolveAfterEraseResult) : Bool :=
  match r.resolvedTy with
  | some inferred => !(isInstanceOf r.expectedTy inferred)
  | none => true

/-- Search for a *counterexample* to the resolve-after-erase property, so the
    Tyche panel is densely populated with failing cases (counterexamples are
    rare — well under 1% of generated terms — so an unbiased panel shows only a
    handful). Retries generation up to `budget` times; if none is found within
    the budget, returns the last sample generated so the run still terminates. -/
partial def genResolveCounterexample (budget : Nat := 4000) : IO ResolveAfterEraseResult := do
  let mut last : Option ResolveAfterEraseResult := none
  for _ in List.range budget do
    let r ← try some <$> genAndCheckResolveAfterErase catch _ => pure none
    match r with
    | some res =>
      if isResolveCounterexample res then return res
      last := some res
    | none => pure ()
  match last with
  | some res => return res
  | none => genAndCheckResolveAfterErase

-- ── Command-level Tyche support ──────────────────────────────────────

/-- Classify the top-level command constructor. -/
def cmdKind (cmd : Cmd Expression) : String :=
  match cmd with
  | .init _ _ (.det _) _ => "init_det"
  | .init _ _ .nondet _ => "init_nondet"
  | .set _ (.det _) _ => "set_det"
  | .set _ .nondet _ => "set_nondet"
  | .assert _ _ _ => "assert"
  | .assume _ _ _ => "assume"
  | .cover _ _ _ => "cover"

/-- Shared helper: generate a command from a random-size context.
    Uses a large `numCmds` (3× desired context size) to compensate for the
    fact that only `init` commands grow the context, while `assert`/`assume`/
    `cover`/`set` leave it unchanged. -/
private def genCmdFromRandomCtx (depth : Nat := 0) : IO (Cmd Expression × VarCtx × VarCtx × Nat) := do
  let d ← if depth == 0 then randomDepth else pure depth
  let tvars : List TyIdentifier := []
  let numCmds ← IO.rand 0 8
  let (_, baseCtx) ← genCmds (G := IO) [] coreOpCtx tvars [] d numCmds
  let ⟨cmd, ctx'⟩ ← genCmd (G := IO) [] coreOpCtx tvars baseCtx d
  return (cmd, baseCtx, ctx', d)

-- ── Panel 1: init freshness ──────────────────────────────────────────

structure CmdInitFreshResult where
  cmd : Cmd Expression
  ctxSize : Nat
  generatorSize : Nat
  passed : Bool

instance : Tyche.TycheSample CmdInitFreshResult where
  toSample r :=
    { representation := ppCmd r.cmd
      status := if r.passed then .passed else .failed
      features := [
        ("cmd_kind", .nominal (cmdKind r.cmd)),
        ("ctx_size", .ordinal r.ctxSize),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckInitFresh : IO CmdInitFreshResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctxSize := baseCtx.length, generatorSize := d,
           passed := checkInitFreshNotInRhs cmd }

-- ── Panel 2: expression typechecks ───────────────────────────────────

structure CmdExprTypecheckResult where
  cmd : Cmd Expression
  ctxSize : Nat
  generatorSize : Nat
  passed : Bool

instance : Tyche.TycheSample CmdExprTypecheckResult where
  toSample r :=
    { representation := ppCmd r.cmd
      status := if r.passed then .passed else .failed
      features := [
        ("cmd_kind", .nominal (cmdKind r.cmd)),
        ("ctx_size", .ordinal r.ctxSize),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckExprTypecheck : IO CmdExprTypecheckResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctxSize := baseCtx.length, generatorSize := d,
           passed := checkExprTypechecks cmd }

-- ── Panel 3: set preserves variable ─────────────────────────────────

structure CmdSetPreservesVarResult where
  cmd : Cmd Expression
  ctxSize : Nat
  generatorSize : Nat
  passed : Bool

instance : Tyche.TycheSample CmdSetPreservesVarResult where
  toSample r :=
    { representation := ppCmd r.cmd
      status := if r.passed then .passed else .failed
      features := [
        ("cmd_kind", .nominal (cmdKind r.cmd)),
        ("ctx_size", .ordinal r.ctxSize),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckSetPreservesVar : IO CmdSetPreservesVarResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctxSize := baseCtx.length, generatorSize := d,
           passed := checkSetPreservesVar cmd baseCtx }

-- ── Panel 4: store type preservation ─────────────────────────────────

structure CmdStoreTypePreservationResult where
  cmd : Cmd Expression
  ctxSize : Nat
  generatorSize : Nat
  passed : Bool

instance : Tyche.TycheSample CmdStoreTypePreservationResult where
  toSample r :=
    { representation := ppCmd r.cmd
      status := if r.passed then .passed else .failed
      features := [
        ("cmd_kind", .nominal (cmdKind r.cmd)),
        ("ctx_size", .ordinal r.ctxSize),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckStoreTypePreservation : IO CmdStoreTypePreservationResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctxSize := baseCtx.length, generatorSize := d,
           passed := checkStoreTypePreservation cmd baseCtx }

-- ── Panel 5: symbolic/concrete eval agreement ────────────────────────

structure CmdEvalRunAgreementResult where
  cmd : Cmd Expression
  ctx : VarCtx
  ctxSize : Nat
  generatorSize : Nat
  passed : Bool

instance : Tyche.TycheSample CmdEvalRunAgreementResult where
  toSample r :=
    { representation := ppCmd r.cmd
      status := if r.passed then .passed else .failed
      features := [
        ("cmd_kind", .nominal (cmdKind r.cmd)),
        -- How the command's condition reduced, which determines whether the
        -- symbolic and concrete evaluators take the same branch.
        ("condition_kind", .nominal (cmdConditionKind r.cmd r.ctx)),
        ("ctx_size", .ordinal r.ctxSize),
        ("generator_size", .ordinal r.generatorSize)
      ] }

def genAndCheckEvalRunAgreement : IO CmdEvalRunAgreementResult := do
  let (cmd, baseCtx, _, d) ← genCmdFromRandomCtx
  return { cmd, ctx := baseCtx, ctxSize := baseCtx.length, generatorSize := d,
           passed := checkEvalRunAgreement cmd baseCtx }

-- ── Function-level Tyche support ─────────────────────────────────────

/-- Whether a generated function has a body / a measure, for the panel's
    breakdown (the property is vacuously true when both are absent, so this
    lets us see how often the property is exercised non-trivially). -/
private def funcShape (func : Function) : String :=
  match func.body.isSome, func.measure.isSome with
  | true,  true  => "body+measure"
  | true,  false => "body"
  | false, true  => "measure"
  | false, false => "neither"

structure FunctionFvarsAnnotatedResult where
  func : Function
  /-- The property under test: all fvars in body/measure annotated per the
      context type map. -/
  passed : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionFvarsAnnotatedResult where
  toSample r :=
    { representation := formatFunc r.func
      status := if r.passed then .passed else .failed
      features := [
        ("fvars_annotated", .nominal (if r.passed then "yes" else "no")),
        -- Which optional sub-expressions are present (so we can see how often
        -- the property is checked non-vacuously).
        ("func_shape", .nominal (funcShape r.func)),
        ("has_body", .nominal (if r.func.body.isSome then "yes" else "no")),
        ("has_measure", .nominal (if r.func.measure.isSome then "yes" else "no")),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a `Function` via `genFunction` (against `defaultFCtx`) and check the
    `fvars_annotated_by` property against the matching type map. -/
def genAndCheckFunctionFvarsAnnotated (depth : Nat := 0) : IO FunctionFvarsAnnotatedResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO defaultFCtx coreOpCtx d
  let passed := functionFvarsAnnotatedBy (fctxToTyMap defaultFCtx) func
  return { func, passed, generatorSize := d }

-- ── Known types and context for Function.typeCheck ─────────────────────

/-- Known types covering all base types + type constructors the generator can
    produce. Required for `Function.typeCheck` to resolve arrow/Map/Seq aliases. -/
private def funcCheckKnownTypes : Lambda.KnownTypes :=
  open Lambda.LTy.Syntax in
  Lambda.makeKnownTypes ([t[∀a b. %a → %b],
    t[bool], t[int], t[string], t[real], t[regex],
    t[∀n. bitvec n],
    t[∀a b. Map %a %b],
    t[∀a. Sequence %a]].map (fun k => k.toKnownType!))

/-- LContext with `intBoolFactory` and all generator-relevant known types. -/
private def funcCheckContext : Lambda.LContext CoreLParams :=
  { Lambda.LContext.default with
    functions := intBoolFactory,
    knownTypes := funcCheckKnownTypes }

-- ── Function property 1: typeCheck_annotated_sound ─────────────────────
-- Tests the *sorry*'d theorem `Function.typeCheck_annotated_sound`
-- (`Strata/Languages/Core/FunctionTypeSpecSound.lean:31`): when
-- `Function.typeCheck` accepts a generated (spec-well-typed) function, the
-- output satisfies the declarative spec `FuncHasTypeA`. Generated with an
-- *empty* fvar context so bodies are closed (no ambient-context dependency).

/-- Reflect `FuncHasTypeA` on a function via `LExpr.typeCheck`: body types at
    the declared output, measure types at int, inputs/typeArgs `Nodup`. -/
private def checkFuncHasTypeA (func : Function) : Bool :=
  let bodyOk := match func.body with
    | some b => LExpr.typeCheck (T := CoreLParams) [] b == some func.output
    | none => true
  let measureOk := match func.measure with
    | some m => LExpr.typeCheck (T := CoreLParams) [] m == some .int
    | none => true
  bodyOk && measureOk && decide (func.inputs.keys.Nodup) && decide (func.typeArgs.Nodup)

structure FunctionTypeCheckSoundResult where
  func : Function
  /-- Whether `Function.typeCheck` accepted the function. -/
  accepted : Bool
  /-- When accepted, whether the output satisfies `FuncHasTypeA`. -/
  specHolds : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionTypeCheckSoundResult where
  toSample r :=
    -- A sample "passes" iff soundness is not violated: either typeCheck
    -- rejected (vacuous — soundness untriggered) or it accepted and the spec
    -- holds. A failure is: accepted but spec violated.
    let passed := !r.accepted || r.specHolds
    { representation := formatFunc r.func
      status := if passed then .passed else .failed
      features := [
        ("typecheck_accepted", .nominal (if r.accepted then "yes" else "no")),
        ("spec_holds", .nominal (if r.accepted then (if r.specHolds then "yes" else "no") else "—")),
        ("func_shape", .nominal (funcShape r.func)),
        ("has_body", .nominal (if r.func.body.isSome then "yes" else "no")),
        ("has_measure", .nominal (if r.func.measure.isSome then "yes" else "no")),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a closed function (empty fctx), run `Function.typeCheck`, and record
    whether it was accepted and whether the output satisfies `FuncHasTypeA`. -/
def genAndCheckFunctionTypeCheckSound (depth : Nat := 0) : IO FunctionTypeCheckSoundResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreOpCtx d
  match Function.typeCheck funcCheckContext TEnv.default func with
  | .ok (func', _) =>
    return { func := func', accepted := true, specHolds := checkFuncHasTypeA func', generatorSize := d }
  | .error _ =>
    return { func, accepted := false, specHolds := true, generatorSize := d }

-- ── Function property 2: pretty-print / parse round-trip ───────────────
-- Embeds a generated function in a `Program`, formats it via
-- `Core.formatProgram`, re-parses via DDM, re-formats, and compares. A parse
-- failure is scored as a FAILURE: names are legal Core identifiers by
-- construction (`genIdentName`), so unparseable output is a printer/parser bug.

-- `formatFuncAsProgram`, `parseCoreProgram`, `parseCoreProgramErr`, the
-- structural shrinker (`shrinkWhile` et al.) and the failure predicates
-- (`failsRoundtrip`, …) are shared with the Plausible harness — see
-- `StrataGenerators.FunctionHasTypeAGen.Roundtrip`.

/-- Extract a short, position-independent "kind" from a parser error message,
    for grouping in the Tyche panel. Strips the `Parse errors:` prefix and the
    `line:col` location so that e.g. every "Map expects 2 arguments" collapses
    into one bucket regardless of where in the input it occurred. -/
private def parseErrorKind (msg : String) : String :=
  -- Drop everything up to and including the last "N:M:" location marker.
  let afterLoc := (msg.splitOn ": ").reverse.headD msg
  let core := afterLoc.trimAscii
  (core.take 45).toString

structure FunctionRoundtripResult where
  func : Function
  /-- Whether the printed function parsed back successfully. -/
  parsed : Bool
  /-- When parsed, whether format→parse→re-format is a fixed point. -/
  roundtripped : Bool
  /-- On parse failure, the parser's diagnostic message (else ""). -/
  parseError : String
  generatorSize : Nat

instance : Tyche.TycheSample FunctionRoundtripResult where
  toSample r :=
    -- Passes iff the printed function parsed back AND round-tripped. A parse
    -- failure is a FAILURE, not vacuous: `genIdentName` produces only legal Core
    -- identifiers by construction, so legal-but-unparseable output is a genuine
    -- printer/parser bug to report.
    let passed := r.parsed && r.roundtripped
    -- Show the exact string the round-trip tested (Strata's `Core.formatProgram`
    -- output), so the panel is a faithful reproducer of any failure.
    { representation := formatFuncAsProgram r.func
      status := if passed then .passed else .failed
      statusReason := r.parseError
      features := [
        ("parsed", .nominal (if r.parsed then "yes" else "no")),
        ("roundtripped", .nominal (if r.parsed then (if r.roundtripped then "yes" else "no") else "—")),
        ("error_kind", .nominal (if r.parsed then "—" else parseErrorKind r.parseError)),
        ("func_shape", .nominal (funcShape r.func)),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Build a `FunctionRoundtripResult` for a specific function. -/
def mkRoundtripResult (func : Function) (d : Nat) : IO FunctionRoundtripResult := do
  let s1 := formatFuncAsProgram func
  match ← parseCoreProgramErr s1 with
  | .ok ast2 =>
    let s2 := (Core.formatProgram ast2).pretty
    return { func, parsed := true, roundtripped := s1 == s2, parseError := "", generatorSize := d }
  | .error e =>
    return { func, parsed := false, roundtripped := false, parseError := e, generatorSize := d }

def genAndCheckFunctionRoundtrip (depth : Nat := 0) : IO FunctionRoundtripResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreOpCtx d
  -- If the function fails to round-trip, shrink it to a minimal witness and
  -- report that instead, so the Tyche `representation` shows the smallest
  -- reproducer (features / status_reason are recomputed on the shrunk func).
  if ← failsRoundtrip func then
    let minF ← shrinkWhile failsRoundtrip 1000 func
    mkRoundtripResult minF d
  else
    mkRoundtripResult func d

-- ── Function property 3: type preservation under eval ──────────────────
-- Corresponds to `Step.type_preserved` / `StepStar.type_preserved` /
-- `eval_denote_sound`. Evaluates a generated function body and checks the
-- result still type-checks at the declared output type.

structure FunctionBodyPreservationResult where
  func : Function
  /-- Whether the function has a body (the property is exercised non-vacuously). -/
  hasBody : Bool
  /-- When a body is present, whether eval preserved the output type. -/
  preserved : Bool
  generatorSize : Nat

instance : Tyche.TycheSample FunctionBodyPreservationResult where
  toSample r :=
    -- Passes iff no body (vacuous) or the body's type is preserved under eval.
    let passed := !r.hasBody || r.preserved
    { representation := formatFunc r.func
      status := if passed then .passed else .failed
      features := [
        ("has_body", .nominal (if r.hasBody then "yes" else "no")),
        ("type_preserved", .nominal (if r.hasBody then (if r.preserved then "yes" else "no") else "—")),
        ("num_type_args", .ordinal r.func.typeArgs.length),
        ("num_inputs", .ordinal r.func.inputs.toList.length),
        ("output_kind", .nominal (typeKind r.func.output)),
        ("generator_size", .ordinal r.generatorSize)
      ] }

/-- Generate a closed function, evaluate its body (if any), and check the result
    still type-checks at the declared output type. -/
def genAndCheckFunctionBodyPreservation (depth : Nat := 0) : IO FunctionBodyPreservationResult := do
  let d ← if depth == 0 then randomDepth else pure depth
  let func ← genFunctionIO [] coreOpCtx d
  match func.body with
  | some body =>
    let evaled := eval 100 body
    let preserved := LExpr.typeCheck (T := CoreLParams) [] evaled == some func.output
    return { func, hasBody := true, preserved, generatorSize := d }
  | none =>
    return { func, hasBody := false, preserved := true, generatorSize := d }

-- ── Function property: special-character identifier round-trip ─────────
-- Isolates one *legal* identifier that contains special (non-alphanumeric)
-- characters (`genQuotedName`: letter/`_`/`$`-initial, then `. ' | \ ? ! @` in
-- the interior) in one syntactic position (function name / type-arg / binder)
-- inside an otherwise-trivial function, so a failure is a minimal reproducer.
-- Every generated name is a legal Core identifier by construction, so a failure
-- is a genuine printer/parser bug, not a generator artifact. Mirrors the probe
-- in `PlausibleTestMain.lean` (those defs live in a separate executable root and
-- can't be imported, so they're restated here).

/-- The three syntactic positions an identifier can occupy in a `Function`. -/
inductive IdentPosition where
  | funcName
  | typeArg
  | binder
  deriving Repr, DecidableEq

def IdentPosition.label : IdentPosition → String
  | .funcName => "function-name"
  | .typeArg  => "type-arg"
  | .binder   => "binder"

/-- Character class of the identifier that likely triggered a failure — used as
    the panel's grouping feature so distinct mechanisms surface separately. -/
def identCharClass (name : String) : String :=
  if name.any (· == '.') then "dot"
  else if name.any (· == '|') then "pipe"
  else if name.any (· == '\\') then "backslash"
  else if name.any (· == '\'') then "apostrophe"
  else if name.toList.head?.map (·.isDigit) == some true then "leading-digit"
  else if name.any (fun c => c == '?' || c == '!' || c == '@') then "special"
  else "plain"

/-- Build a minimal `Function` that places `name` in the given position and is
    otherwise trivial (no body, no measure, `int` output). -/
def minimalFuncWithName (pos : IdentPosition) (name : String) : Function :=
  let ident : Identifier Unit := ⟨name, ()⟩
  match pos with
  | .funcName => LFunc.mk (name := ident) (inputs := []) (output := .int)
  | .typeArg  => LFunc.mk (name := ⟨"f", ()⟩) (typeArgs := [name]) (inputs := [])
                   (output := .ftvar name)
  | .binder   => LFunc.mk (name := ⟨"f", ()⟩) (inputs := [(ident, .int)]) (output := .int)

structure IdentProbeResult where
  pos : IdentPosition
  name : String
  /-- Whether the printed single-identifier function parsed back. -/
  parsed : Bool
  /-- When parsed, whether format→parse→re-format is a fixed point. -/
  roundtripped : Bool
  /-- On parse failure, the parser's diagnostic message (else ""). -/
  parseError : String
  rendered : String

instance : Tyche.TycheSample IdentProbeResult where
  toSample r :=
    -- Passes iff the identifier parsed back AND round-tripped. A parse failure
    -- is a FAILURE: the name is a legal Core identifier, so unparseable output
    -- is a printer/parser bug.
    let passed := r.parsed && r.roundtripped
    { representation := r.rendered.replace "\n" " "
      status := if passed then .passed else .failed
      statusReason := r.parseError
      features := [
        ("position", .nominal r.pos.label),
        ("char_class", .nominal (identCharClass r.name)),
        ("parsed", .nominal (if r.parsed then "yes" else "no")),
        ("roundtripped", .nominal (if r.parsed then (if r.roundtripped then "yes" else "no") else "—")),
        ("error_kind", .nominal (if r.parsed then "—" else parseErrorKind r.parseError))
      ] }

/-- Draw an adversarial identifier, place it in a random position, and record
    whether that single identifier round-trips. -/
def genAndCheckIdentProbe : IO IdentProbeResult := do
  let name ← genQuotedName (G := IO)
  let posIdx ← IO.rand 0 2
  let pos := match posIdx with
    | 0 => IdentPosition.funcName
    | 1 => IdentPosition.typeArg
    | _ => IdentPosition.binder
  let s1 := formatFuncAsProgram (minimalFuncWithName pos name)
  match ← parseCoreProgramErr s1 with
  | .ok ast2 =>
    let s2 := (Core.formatProgram ast2).pretty
    return { pos, name, parsed := true, roundtripped := s1 == s2, parseError := "", rendered := s1 }
  | .error e =>
    return { pos, name, parsed := false, roundtripped := false, parseError := e, rendered := s1 }

-- ── Statement-level Tyche support ────────────────────────────────────
-- Panels visualizing the six statement-transform / typechecker properties on
-- well-typed statement lists from `genProgramStmts` (proven sound+complete
-- against `StmtsHasTypeA`). The `check*` predicates and measurements are shared
-- with the Plausible harness via `StrataGenerators.StmtHasTypeAGen.TestSupport`.

open StrataGenerators.Stmt.TestSupport

/-- Shared statement-list features for every statement panel: structural
    breakdown (size, kind counts) plus the generator size. -/
private def stmtListFeatures (ss : List Statement) (genSize : Nat) :
    List (String × Tyche.Feature) :=
  [ ("num_stmts", .ordinal ss.length),
    ("ast_size", .ordinal (sizeStmts ss)),
    ("num_loops", .ordinal (countLoopsStmts ss)),
    ("num_exits", .ordinal (countExitStmts ss)),
    ("num_funcDecls", .ordinal (countFuncDeclStmts ss)),
    ("num_typeDecls", .ordinal (countTypeDeclStmts ss)),
    ("has_funcDecl", .nominal (if stmtsHaveFuncDecl ss then "yes" else "no")),
    ("top_kind", .nominal (match ss with | s :: _ => stmtKind s | [] => "empty")),
    ("generator_size", .ordinal genSize) ]

/-- A generated statement list paired with a single property's pass/fail verdict
    and the property name (used as the pass/fail nominal feature). One structure
    serves every boolean statement property; the panel title distinguishes them. -/
structure StmtPropResult where
  stmts : List Statement
  passed : Bool
  genSize : Nat
  /-- Short property tag, surfaced as the primary nominal feature. -/
  tag : String

instance : Tyche.TycheSample StmtPropResult where
  toSample r :=
    { representation := (Std.format r.stmts).pretty
      status := if r.passed then .passed else .failed
      features := (r.tag, .nominal (if r.passed then "pass" else "fail"))
        :: stmtListFeatures r.stmts r.genSize }

/-- Generate one well-typed statement list in `IO` for the Tyche panels. Caps
    `size`/`len` low (mirrors the Plausible wrapper) so whole-list generation
    rarely hits an empty sub-generator. -/
def genStmtsForTyche : IO (List Statement × Nat) := do
  let d ← IO.rand 1 3
  let len ← IO.rand 1 4
  let ss ← genProgramStmtsIO d len
  return (ss, d)

/-- Build a `StmtPropResult` by generating a statement list and applying a check
    predicate under the given tag. -/
def genStmtProp (tag : String) (check : List Statement → Bool) : IO StmtPropResult := do
  let (ss, d) ← genStmtsForTyche
  return { stmts := ss, passed := check ss, genSize := d, tag }

-- ── The `StmtToKleeneStmt` definedness panel (extra breakdown) ────────
-- Unlike the pass/fail panels, this one also records *why* the transform was (un)
-- defined, so the definedness contract (#6) is eyeballable.

structure KleeneDefinedResult where
  stmts : List Statement
  defined : Bool
  genSize : Nat

instance : Tyche.TycheSample KleeneDefinedResult where
  toSample r :=
    let unsupported := hasKleeneUnsupported r.stmts
    let invLoop := hasInvLoopStmts r.stmts
    -- Passes iff the definedness matches the documented contract.
    let passed := checkKleeneDefinedIff r.stmts
    { representation := (Std.format r.stmts).pretty
      status := if passed then .passed else .failed
      features := [
        ("defined", .nominal (if r.defined then "yes" else "no")),
        ("has_unsupported_ctor", .nominal (if unsupported then "yes" else "no")),
        ("has_invariant_loop", .nominal (if invLoop then "yes" else "no")),
        ("contract_holds", .nominal (if passed then "yes" else "no"))
      ] ++ stmtListFeatures r.stmts r.genSize }

def genKleeneDefined : IO KleeneDefinedResult := do
  let (ss, d) ← genStmtsForTyche
  return { stmts := ss, defined := (kleeneStmts ss).isSome, genSize := d }

-- ── Main ──────────────────────────────────────────────────────────────

def main (args : List String) : IO Unit := do
  let numSamples := (args[0]? >>= String.toNat?).getD 1000
  let outputPath := (args[1]?).getD "tyche_output.jsonl"
  IO.println s!"Generating {numSamples} samples..."

  -- Run the typed expression generator
  Tyche.run (genTypedExpr) { numSamples, propertyName := "Distribution of terms generated by genLExpr", outputPath }

  -- Run the term-kind-only generator (single nominal feature → plain bar chart)
  Tyche.run (genTermKind)
    { numSamples, propertyName := "Distribution of term_kind", outputPath := outputPath ++ ".tk" }
  let tkContent ← IO.FS.readFile (outputPath ++ ".tk")
  let tkHandle ← IO.FS.Handle.mk outputPath .append
  tkHandle.putStr tkContent
  IO.FS.removeFile (outputPath ++ ".tk")

  -- Run the typecheck property
  Tyche.run (genAndTypeCheck)
    { numSamples, propertyName := "Terms generated by genLExpr typecheck", outputPath := outputPath ++ ".tc" }

  -- Append typecheck results to the main file
  let tcContent ← IO.FS.readFile (outputPath ++ ".tc")
  let handle ← IO.FS.Handle.mk outputPath .append
  handle.putStr tcContent
  IO.FS.removeFile (outputPath ++ ".tc")

  -- Run the type preservation property
  Tyche.run (genAndEval)
    { numSamples, propertyName := "Type preservation under eval (closed terms)", outputPath := outputPath ++ ".ev" }
  let evContent ← IO.FS.readFile (outputPath ++ ".ev")
  handle.putStr evContent
  IO.FS.removeFile (outputPath ++ ".ev")

  -- Run the eval progress property
  Tyche.run (genAndCheckProgress)
    { numSamples, propertyName := "LExpr.eval makes progress on closed terms", outputPath := outputPath ++ ".prog" }
  let progContent ← IO.FS.readFile (outputPath ++ ".prog")
  handle.putStr progContent
  IO.FS.removeFile (outputPath ++ ".prog")

  -- Run the fvar preservation property
  Tyche.run (genAndCheckFvarPreservation)
    { numSamples, propertyName := "LExpr.eval preserves fvars", outputPath := outputPath ++ ".cls" }
  let clsContent ← IO.FS.readFile (outputPath ++ ".cls")
  handle.putStr clsContent
  IO.FS.removeFile (outputPath ++ ".cls")

  -- Counterexample-focused panel: every sample here is a *counterexample* to the
  -- resolve-after-erase property (found by rejection-sampling), so the panel is
  -- densely populated with failing cases for visualization.
  Tyche.run (genResolveCounterexample)
    { numSamples, propertyName := "Counterexamples: erase types then resolve", outputPath := outputPath ++ ".resX" }
  let resXContent ← IO.FS.readFile (outputPath ++ ".resX")
  handle.putStr resXContent
  IO.FS.removeFile (outputPath ++ ".resX")

  -- Inspection panel: terms that call Sequence.map via the IndirPoly rule.
  -- Most samples are (rejection-sampled to be) Sequence.map calls with the α/β
  -- instantiation eyeballable; the occasional fallback is marked
  -- `calls_seq_map = no`. This is an inspection aid, not a coverage property, so
  -- we cap it at 300 samples to keep the run fast regardless of `numSamples`.
  Tyche.run (genSeqMapCall)
    { numSamples := min numSamples 300, propertyName := "Terms calling Sequence.map (IndirPoly rule)", outputPath := outputPath ++ ".smap" }
  let smapContent ← IO.FS.readFile (outputPath ++ ".smap")
  handle.putStr smapContent
  IO.FS.removeFile (outputPath ++ ".smap")

  -- Run command-level property tests (one panel each)
  Tyche.run (genAndCheckInitFresh)
    { numSamples, propertyName := "genCmd: init var not in RHS", outputPath := outputPath ++ ".cmd1" }
  let cmd1 ← IO.FS.readFile (outputPath ++ ".cmd1")
  handle.putStr cmd1
  IO.FS.removeFile (outputPath ++ ".cmd1")

  Tyche.run (genAndCheckExprTypecheck)
    { numSamples, propertyName := "genCmd: expressions typecheck", outputPath := outputPath ++ ".cmd2" }
  let cmd2 ← IO.FS.readFile (outputPath ++ ".cmd2")
  handle.putStr cmd2
  IO.FS.removeFile (outputPath ++ ".cmd2")

  Tyche.run (genAndCheckSetPreservesVar)
    { numSamples, propertyName := "genCmd: set preserves variable", outputPath := outputPath ++ ".cmd3" }
  let cmd3 ← IO.FS.readFile (outputPath ++ ".cmd3")
  handle.putStr cmd3
  IO.FS.removeFile (outputPath ++ ".cmd3")

  Tyche.run (genAndCheckStoreTypePreservation)
    { numSamples, propertyName := "genCmd: store type preservation under eval", outputPath := outputPath ++ ".cmd4" }
  let cmd4 ← IO.FS.readFile (outputPath ++ ".cmd4")
  handle.putStr cmd4
  IO.FS.removeFile (outputPath ++ ".cmd4")

  Tyche.run (genAndCheckEvalRunAgreement)
    { numSamples, propertyName := "genCmd: symbolic/concrete eval agreement", outputPath := outputPath ++ ".cmd5" }
  let cmd5 ← IO.FS.readFile (outputPath ++ ".cmd5")
  handle.putStr cmd5
  IO.FS.removeFile (outputPath ++ ".cmd5")

  -- Function generator property: fvars in generated functions are annotated
  -- consistently with the context type map.
  Tyche.run (genAndCheckFunctionFvarsAnnotated)
    { numSamples, propertyName := "genFunction: fvars annotated by context type map", outputPath := outputPath ++ ".fn1" }
  let fn1 ← IO.FS.readFile (outputPath ++ ".fn1")
  handle.putStr fn1
  IO.FS.removeFile (outputPath ++ ".fn1")

  -- Function property: Function.typeCheck_annotated_sound. When typeCheck
  -- accepts a generated (spec-well-typed) function, the output satisfies the
  -- declarative spec FuncHasTypeA.
  Tyche.run (genAndCheckFunctionTypeCheckSound)
    { numSamples, propertyName := "genFunction: typeCheck output satisfies FuncHasTypeA (typeCheck_annotated_sound)", outputPath := outputPath ++ ".fn2" }
  let fn2 ← IO.FS.readFile (outputPath ++ ".fn2")
  handle.putStr fn2
  IO.FS.removeFile (outputPath ++ ".fn2")

  -- Function property: pretty-print / parse round-trip. Format → parse →
  -- re-format is a fixed point (parse failures marked separately).
  Tyche.run (genAndCheckFunctionRoundtrip)
    { numSamples, propertyName := "genFunction: pretty-print/parse round-trip", outputPath := outputPath ++ ".fn3" }
  let fn3 ← IO.FS.readFile (outputPath ++ ".fn3")
  handle.putStr fn3
  IO.FS.removeFile (outputPath ++ ".fn3")

  -- Function property: type preservation under eval (Step.type_preserved /
  -- StepStar.type_preserved / eval_denote_sound). Evaluating a function body
  -- preserves the declared output type.
  Tyche.run (genAndCheckFunctionBodyPreservation)
    { numSamples, propertyName := "genFunction: body type preserved under eval", outputPath := outputPath ++ ".fn4" }
  let fn4 ← IO.FS.readFile (outputPath ++ ".fn4")
  handle.putStr fn4
  IO.FS.removeFile (outputPath ++ ".fn4")

  -- Function property: special-character identifier round-trip. A legal
  -- identifier containing special (non-alphanumeric) characters (`genQuotedName`)
  -- in one syntactic position; a parse failure or mismatch is a minimal
  -- printer/parser bug reproducer.
  Tyche.run genAndCheckIdentProbe
    { numSamples, propertyName := "genFunction: special-character identifier round-trip", outputPath := outputPath ++ ".fn5" }
  let fn5 ← IO.FS.readFile (outputPath ++ ".fn5")
  handle.putStr fn5
  IO.FS.removeFile (outputPath ++ ".fn5")

  -- ── Statement generator panels (transforms + typechecker) ───────────
  -- One panel per property (#1, #3, #4, #5a, #5b, #6, #9). Each generates a
  -- well-typed statement list (proven sound+complete against `StmtsHasTypeA`) and
  -- visualizes the property's pass/fail against structural features.
  -- Panel #1 uses the HONEST completeness predicate, so `funcDecl`-bearing
  -- statements render as failed marks (the real spec/algorithm gap is visible,
  -- not masked). Panel #1b shows that every such rejection carries a `funcDecl`.
  let stmtPanels : List (String × String × (List Statement → Bool)) :=
    [ (".st1", "stmt: typechecker accepts generated statements (#1 — funcDecl gap visible)", checkTypeCheckerComplete),
      (".st1b", "stmt: typecheck rejections are only funcDecl (#1b)", rejectionImpliesFuncDecl),
      (".st3", "stmt: LoopElim preserves typeability (#3)", checkLoopElimPreservesTyping),
      (".st4", "stmt: LoopElim eliminates all loops (#4)", checkLoopElimZeroLoops),
      (".st5a", "stmt: ANF is idempotent (#5a)", checkAnfIdempotent),
      (".st5b", "stmt: ANF preserves typeability (#5b)", checkAnfPreservesTyping),
      (".st9", "stmt: mapExprs id = id (#9)", checkMapExprsId) ]
  for (suffix, title, check) in stmtPanels do
    Tyche.run (genStmtProp title check)
      { numSamples, propertyName := title, outputPath := outputPath ++ suffix }
    let content ← IO.FS.readFile (outputPath ++ suffix)
    handle.putStr content
    IO.FS.removeFile (outputPath ++ suffix)

  -- #6 gets its own richer panel (definedness + why).
  Tyche.run genKleeneDefined
    { numSamples, propertyName := "stmt: DetToKleene defined iff supported (#6)", outputPath := outputPath ++ ".st6" }
  let st6 ← IO.FS.readFile (outputPath ++ ".st6")
  handle.putStr st6
  IO.FS.removeFile (outputPath ++ ".st6")

  -- Also generate type samples into the same file
  let startTime ← IO.monoMsNow
  for _ in List.range numSamples do
    try
      let d ← randomDepth
      let ty ← genType d
      let sample := TycheSample.toSample ty
      let line := sample.toJsonLine "Distribution of types generated by genLMonoTy" startTime
      handle.putStrLn line
    catch _ => pure ()

  IO.println s!"Done! Output written to {outputPath}"
  IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
