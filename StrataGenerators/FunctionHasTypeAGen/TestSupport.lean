import StrataGenerators.FunctionHasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.Languages.Core.FunctionType

open Lambda RandomChoice Core Imperative

/-!
# The test support for the `FunctionHasTypeAGen` generator

This module holds the shared functions for the property-based tests of `genFunction`:
- the functions that print a generated `Function`;
- a `Bool` copy of the `fvars_annotated_by` predicate of Strata;
- the wrappers that run a generator in `IO` and in `Plausible.Gen`.

## Why this module has its own copy of `fvars_annotated_by`

The predicate under test is `Lambda.fvars_annotated_by` of Strata:

```
def fvars_annotated_by [DecidableEq T.IDMeta]
    (tyMap : Map T.Identifier LMonoTy) : LExpr T.mono → Prop
  | .fvar _ name (some ty) => ∀ ty', Map.find? tyMap name = some ty' → ty = ty'
  | .fvar _ _ none         => False
  | .const _ _ | .bvar _ _ | .op _ _ _ => True
  | .app _ fn arg          => fvars_annotated_by tyMap fn ∧ fvars_annotated_by tyMap arg
  | .abs _ _ _ body        => fvars_annotated_by tyMap body
  | .ite _ c t e           => fvars_annotated_by tyMap c ∧ … ∧ …
  | .eq _ e1 e2            => fvars_annotated_by tyMap e1 ∧ fvars_annotated_by tyMap e2
  | .quant _ _ _ _ tr body => fvars_annotated_by tyMap tr ∧ fvars_annotated_by tyMap body
```

This file cannot import that predicate. It is in a file that uses the module system of Lean,
with no `public section`, so only an `import all` reaches it. The generator files of this
repository are not modules, and Lean rejects an import of such a symbol into a file that is
not a module. This module therefore has its own copy, `fvarsAnnotatedBy`, which is a
decidable `Bool` function that follows the `Prop` clause by clause. The harness for a command
does the same for `storeWellTyped` and for the type check, and it imports no `Prop` of Strata
for them.

One clause needs care, and that is the case of an `fvar` with an annotation. The claim
`∀ ty', find? tyMap name = some ty' → ty = ty'` holds exactly when `find? tyMap name` is
`none`, or when it is `some ty'` and `ty` equals `ty'`. One lookup with `Map.find?` decides
both cases.
-/

-- ── The `Bool` copy of `fvars_annotated_by` ──────────────────────────────

/-- A `Bool` copy of `Lambda.fvars_annotated_by tyMap e`. The documentation of this module says why
    the module has its own copy and does not import the predicate.

    Each free variable with an annotation, `(name : ty)`, must agree with `tyMap`. If `tyMap` binds
    `name`, then the type in `tyMap` must equal `ty`. A free variable with *no* annotation, which is
    `.fvar _ _ none`, always fails, and this follows the `False` clause of the `Prop`. Each other
    leaf passes, and a compound node recurses into each of its subexpressions. -/
def fvarsAnnotatedBy (tyMap : Map (Identifier Unit) LMonoTy) : LExpr' → Bool
  | .fvar _ name (some ty) =>
    match Map.find? tyMap name with
    | some ty' => ty == ty'
    | none => true
  | .fvar _ _ none => false
  | .const _ _ => true
  | .bvar _ _ => true
  | .op _ _ _ => true
  | .app _ fn arg => fvarsAnnotatedBy tyMap fn && fvarsAnnotatedBy tyMap arg
  | .abs _ _ _ body => fvarsAnnotatedBy tyMap body
  | .ite _ c t e => fvarsAnnotatedBy tyMap c && fvarsAnnotatedBy tyMap t && fvarsAnnotatedBy tyMap e
  | .eq _ e1 e2 => fvarsAnnotatedBy tyMap e1 && fvarsAnnotatedBy tyMap e2
  | .quant _ _ _ _ tr body => fvarsAnnotatedBy tyMap tr && fvarsAnnotatedBy tyMap body

/-- The `FVarCtx` that the generator used for a function, as the type map that the annotations on its
    free variables must agree with. An `FVarCtx` is a `List (String × LMonoTy)`, and the identifiers
    that the generator makes are of the form `⟨name, ()⟩`, so this function changes each key to that
    form. -/
def fctxToTyMap (fctx : FVarCtx) : Map (Identifier Unit) LMonoTy :=
  fctx.map (fun (name, ty) => (⟨name, ()⟩, ty))

/-- **The property under test**, for a whole function. Each free variable in the body and in the
    measure has an annotation that agrees with `tyMap`. The body and the measure are optional, and a
    function that has neither is a vacuous pass. -/
def functionFvarsAnnotatedBy (tyMap : Map (Identifier Unit) LMonoTy) (func : Function) : Bool :=
  (match func.body with | some b => fvarsAnnotatedBy tyMap b | none => true) &&
  (match func.measure with | some m => fvarsAnnotatedBy tyMap m | none => true)

-- The output for a function goes through the `Core.formatProgram` of Strata. `formatFunc` and
-- `formatFuncAsProgram` in `StrataGenerators.FunctionHasTypeAGen.Roundtrip` call it, so a report
-- shows the output of the real formatter.

-- ── The wrappers around the generator ─────────────────────────────────────

/-- Makes one well-typed `Function` in `IO`, with a direct call of `genFunction`. The default values
    follow the other wrappers of the harness: `defaultFCtx`, `coreMonoOps` and the depth 3. -/
def genFunctionIO (fctx : FVarCtx := defaultFCtx) (octx : OpCtx := coreMonoOps)
    (depth : Nat := 3) : IO Function :=
  genFunction (G := IO) fctx octx depth

-- ── The known types and the context for `Function.typeCheck` ──────────────

/-- The known types. The list covers each base type and each type constructor that the generator can
    make. `Function.typeCheck` needs it to resolve the alias of an arrow, of a `Map` and of a
    `Sequence`. -/
def funcCheckKnownTypes : Lambda.KnownTypes :=
  open Lambda.LTy.Syntax in
  Lambda.makeKnownTypes ([t[∀a b. %a → %b],
    t[bool], t[int], t[string], t[real], t[regex],
    t[∀n. bitvec n],
    t[∀a b. Map %a %b],
    t[∀a. Sequence %a]].map (fun k => k.toKnownType!))

/-- An `LContext` that holds `coreFactory` and each known type that the generator needs. It is the
    same context as the `resolveLContext` that the tests for an expression use. -/
def funcCheckContext : Lambda.LContext CoreLParams :=
  { Lambda.LContext.default with
    functions := coreFactory,
    knownTypes := funcCheckKnownTypes }

-- ── The checks for a function, which both drivers share ───────────────────

/-- A `Bool` copy of `FuncHasTypeA` for a function, through `LExpr.typeCheck`. The body, when it
    exists, has the declared output type. The measure, when it exists, has the type `int`. The list
    of inputs and the list of type arguments each hold no duplicate. -/
def checkFuncHasTypeA (func : Function) : Bool :=
  let bodyOk := match func.body with
    | some b => LExpr.typeCheck (T := CoreLParams) [] b == some func.output
    | none => true
  let measureOk := match func.measure with
    | some m => LExpr.typeCheck (T := CoreLParams) [] m == some .int
    | none => true
  bodyOk && measureOk && decide (func.inputs.keys.Nodup) && decide (func.typeArgs.Nodup)

/-- Soundness of `Function.typeCheck`, which upstream states as `typeCheck_annotated_sound`. When
    `typeCheck` accepts a function, its output satisfies the declarative specification
    `FuncHasTypeA`. When `typeCheck` rejects a function, the check is a vacuous pass. A function
    with a measure and no body is one such case, because the specification allows it and the
    algorithm rejects it. The property states soundness and not completeness. -/
def checkTypeCheckAnnotatedSound (func : Function) : Bool :=
  match Function.typeCheck funcCheckContext TEnv.default func with
  | .ok (func', _) => checkFuncHasTypeA func'
  | .error _ => true

/-- Evaluation keeps the type. Upstream states this claim as `Step.type_preserved`,
    `StepStar.type_preserved` and `eval_denote_sound`. If a function has a body, then the evaluation
    of that body keeps the declared output type. A function with no body is a vacuous pass. -/
def checkFunctionBodyPreservation (func : Function) : Bool :=
  match func.body with
  | some body => LExpr.typeCheck (T := CoreLParams) [] (eval 100 body) == some func.output
  | none => true

-- ── The probe for an identifier with a special character ──────────────────
-- Both drivers share this probe. The round trip of a whole function holds a name, the type
-- arguments, the types, a body and more, so a reader cannot give one cause for a failure. This probe
-- puts one generated identifier in one syntactic position at a time, inside a function that is
-- otherwise trivial. A failure therefore gives a small reproducer.

/-- The three syntactic positions where an identifier can occur in a `Function`. -/
inductive IdentPosition where
  | funcName
  | typeArg
  | binder
  deriving Repr, DecidableEq

/-- The label of a position, for a report. -/
def IdentPosition.label : IdentPosition → String
  | .funcName => "function-name"
  | .typeArg  => "type-arg"
  | .binder   => "binder"

/-- Builds the smallest `Function` that holds `name` in the given position. The function is otherwise
    trivial: it has no body, it has no measure, and its output type is `int`. For a `typeArg`, the
    output type is also `ftvar name`, so the name occurs in a use position and not only in its
    declaration. For a `binder`, the one input uses the name as the identifier of its parameter, at
    the type `int`. -/
def minimalFuncWithName (pos : IdentPosition) (name : String) : Function :=
  let ident : Identifier Unit := ⟨name, ()⟩
  -- `Function` is an alias for the decidable base type `LFuncDefined`, which has no `concreteEval`
  -- field. The code therefore builds the record directly, and it does not call `LFunc.mk`, which
  -- builds the larger `LFunc`.
  match pos with
  | .funcName => { name := ident, inputs := [], output := .int }
  | .typeArg  => { name := ⟨"f", ()⟩, typeArgs := [name], inputs := [],
                   output := .ftvar name }
  | .binder   => { name := ⟨"f", ()⟩, inputs := [(ident, .int)], output := .int }
