import StrataGenerators.Tyche
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.CmdHasTypeAGen.TestSupport
import StrataGenerators.FunctionHasTypeAGen.TestSupport
import Basalt.IO
import Strata.DL.Lambda.LExprT

open Lambda RandomChoice ArbNat Tyche Std Core Imperative

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
    { representation := ppFunction r.func
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
