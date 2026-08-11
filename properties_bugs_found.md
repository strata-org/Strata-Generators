# Properties Tested & Bugs Found

## Properties tested

**LExprs**

- Preservation
- Progress (counterexamples found, known)
- Completeness of `LExpr.resolve` type inference (counterexamples found, previously unknown)
- `LExpr.eval` doesn't introduce any new free variables
- The concrete evaluator agrees with the SMT semantics: for a closed term `e`, if `LExpr.evalWithLState` reduces `e` to a constant, then the solver confirms that `e = eval e`
  - Restricted to base types (`int` / `bool`) over `Core.Factory` operators, so that every subterm is SMT-encodable; terms that don't reduce to a constant are skipped rather than counted as counterexamples
  - Opt-in (`lake test -- --smt`), since it needs a live `cvc5` / `z3` on `PATH`

**Commands**

- Symbolic evaluation (`Cmd.eval`) agrees with concrete execution (`Cmd.run`)
  - Specifically, when concrete execution succeeds, symbolic evaluation also succeeds and results in the same store
- Preservation of store types
- `Cmd.run` preserves variables in the store (i.e. after it executes `set x (det e)`, `x` is still in the remaining store)

**Functions**

- Round-trip property (generating a random function AST, pretty-printing it and then parsing it should yield the same result)
  - 6 counterexamples found, previously unknown
- Functions are well-annotated (they satisfy the `fvars_annotated_by` predicate)
- Preservation (of the function body's type)

**Statement-related transformations**

- Completeness of typechecker with respect to the declarative typing spec
- Result of loop elimination is well-typed
- Loop elimination removes all loops
- The `detToKleene` transformation (converts deterministic control-flow to Kleene Algebra with Tests) produces a result when there are no `exit` or function + type declarations in the original list

**`FilterProcedures` transformation**

- The `FilterProcedures` transformation updates its `changed` flag correctly
  - This transformation removes unreachable procedures (unreachable from a given starting point, which is a list of procedures)
- `FilterProcedures` keeps the procedures that were specified as starting points
- `FilterProcedures` keeps all procedures that are in the transitive closure of the starting list of procedures
- `FilterProcedures` only removes procedures (and not other declarations)
- `FilterProcedures` removes all unreachable procedures (where unreachable = "not in the transitive closure")

**Precondition-filtering transformation**

(removes preconditions from procedures)

- This transformation indeed removes preconditions
- This transformation preserves the name + type signature of procedures & functions
- This transformation does not remove any declarations and preserves declaration order
- Each precondition is transformed into one `assert` in the body of the procedure

**ANF encoding / Common-subexpression elimination (CSE)**

- Result of ANF transformation is well-typed
- ANF transformation is idempotent
- ANF does not change the control-flow skeleton or call-graph
- ANF preserves procedure declarations and does not affect non-procedure declarations
- CSE does not result in dangling (unbound) bound De Bruijn variables
- Result of the symbolic evaluator is the same before/after CSE
  - (By the same, we mean that the path-condition expressions and the stores are the same after resolving the value of new variables that are created during CSE)

**Uniform `changed`-flag contract over every pipeline phase**

Rather than one property per pass, these quantify over a *phase list*, so a phase
added to `corePipelinePhases` later is covered with no new property written.

- Every phase of the Core pipeline (plus `RemoveIrrelevantAxioms`) reports `changed = true` exactly when it changed the program
- The phases that do *not* hardcode their flag all report it faithfully (the regression guard; this one passes)
- `RemoveIrrelevantAxioms` reports `changed = false` on a program with no axioms
- `FilterProcedures` reports `changed = false` when every procedure is a target

**Pretty-printer expressiveness**

The oracle is "the printer logged no conversion error", which needs no parser and
names the offending construct — strictly stronger than a string round-trip, since
the printer substitutes a syntactically valid placeholder rather than failing.

- Formatting a generated program logs no conversion error
- `bitvec 128` literals are printable
- Every `Bv{w}.ToInt` / `Bv{w}.ToUInt` / `Int.ToBv{w}` conversion operator is printable
- Every bitvector width the typechecker accepts is one the printer can express (#48)

**Whole programs**

- Completeness of the whole-program typechecker (`Program.typeCheck`) with respect to the declarative typing spec `ProgramHasTypeA`
- `getNames` of a well-typed program contains no duplicates (the first conjunct of `ProgramHasType'`, checked directly against the flat namespace rather than via the checker's incremental fold)
- If `Program.typeCheck` succeeds and produces an elaborated program, the elaborated program also typechecks
- `stripMetaData` preserves typeability
- `eraseTypes` preserves typeability 

## Implementation bugs caught

- `LExpr` type inference is incomplete (if we erase type annotations on a well-typed term, if the resultant term contains an unannotated quantified free variable e.g. `\forall x. x`, type inference fails to reconstruct a type)
- Progress doesn't hold for `LExpr`s (this was previously known, due to uninterpreted functions, the fact that `\forall` and `\exists` quantifiers don't evaluate under `if` and equality of lambda expressions is conservative)
- 11 situations in which the parser + pretty-printer round-trip fails:
  - Type parameters to functions can't begin with `s` in their name (conflicts with `<s` signed less-than operator):
  - Pretty-printer mis-prints `real` numbers that are represented as rationals with a non-terminating decimal representation (e.g. `1/3` is `0.333...`, but is printed as `0.0` instead)
  - Unapplied unary operators can't be pretty-printed (e.g. `Bool.Not` can't be printed if it's not applied to an argument)
  - Pretty-printer misses parentheses around arrow / type constructors, so `Map int (int -> int)` is printed as `Map int int -> int`, which is mis-parsed as `(Map int int) -> int` (since type application binds tighter than `->`)
  - Pipe-escaping identifiers for types (wrapping identifiers with `|...|` to handle SMTLib names) is not done uniformly (only done for type annotations but not the return type for functions)
  - Periods are allowed in the grammar for identifiers but not accepted by the parser (which uses them to resolve namespaces)
  - Applying the factory function `Real.Neg` on a negative real number literal fails the round-trip property due to missing parenthesization (`Real.Neg (-3.0)` is printed as `--3.0`, which re-parses as `-(-3.0)`; note `Int.Neg (-3)` correctly prints as `-(-3)`)
  - Typechecker accepts bit-vector types with non-power-of-2 lengths, but the printer only supports printing the types `bv{1, 8, 16, 32, 64} `-- unsupported bitvec types are printed as `$__unknown_type` instead
  - Bit-vector literals with some width `n`, where `n` is not a power of 2, are printed as `bv{64}(n) `(i.e. the width `n` becomes the value, and the actual value of the bit-vector is discarded), changing the meaning of the term
  - `bv128` is registered in the Core factory & the DDM, but `bv128` literals are unprintable / unparseable 
  - Core contains factory functions `Bv{n}.ToInt` and `Int.ToBv{n}` for converting from bitvec <-> int, but these functions are unprintable
- The precondition elimination transformation erroneously reports its `changed` flag as false, even though it rewrites procedures to gain an `assert` statement in its body. This happens
for nested function declarations that don't have preconditions, but whose bodies invoke a precondition-carrying function (e.g. `Int.SafeDiv`).
- Non-ASCII strings are not escaped when passed to SMT-Lib, so the Core partial evaluator and SMT solvers disagree on the length of non-ASCII strings (The Core evaluator reports `Str.Length "é" = 1`, but Z3 says `Str.Length "é" = 2` and CVC5 reports `Parse Error: Non-printable character in string literal`)
- The SMT dialect's comparison operator on real numbers (represented as decimal orders) isn't a total order, i.e. it is possible for `r1 <= r2`, `r2 <= r1` and `r1 == r2` to all be false, violating trichotomy
- The SMT dialect's equality check returns false on two decimals that are mathematically equal but have different mantissa-exponent representations (e.g. `3.0` can be represented as `3 * 10^0` or `30 * 10^-1` , which are mathematically the same but considered to be not equal)
- Two more pipeline phases hardcode their `changed` flag to `true`, beyond the already-reported `FilterProcedures`: `RemoveIrrelevantAxioms` (`IrrelevantAxioms.lean:81`) reports `changed = true` even on a program containing *no axioms at all*, and the `typeCheck` / `symbolicEval` phases of `corePipelinePhases` (`Verifier.lean:1510`, `:1517`) do the same. Every other phase computes the flag honestly, which is what makes these read as oversights rather than a convention. No consumer reads the flag today (both call sites discard it), so nothing misbehaves at runtime — the defect is that the field is *specified* to mean something it does not mean.
- `bitvec 128` literals cannot be pretty-printed, even though the width is registered in the factory (`Factory.lean:872`) and has a grammar production (`bv128Lit`, `Grammar.lean:113`): `lconstToExpr` logs `unsupported bitvec width: 128`. Every other registered width prints.
- **None** of the 18 `Bv{w}.ToInt` / `Bv{w}.ToUInt` / `Int.ToBv{w}` conversion operators can be pretty-printed, at *any* registered width (`w ∈ {1, 8, 16, 32, 64, 128}`). They are all registered in the factory (`Factory.lean:850–872`) but have no grammar production and no arm in `handleUnaryOps`, so each falls through to `mkGenericCall` and is rendered as a call to a fresh free variable. A systematic hole rather than a missing case.
- The pretty-printer does not fail when it cannot express a construct: it substitutes a *syntactically valid* placeholder (`$__unknown_type` for a type, a generic call for an operator) and appends its errors to the output. So an unprintable program can round-trip "successfully" while denoting a **different** program — observed on 5 of 198 affected programs, which is exactly the case a string round-trip check structurally cannot detect. Conversion errors fire on ~50% of generated programs at the 2–5 declarations the shared whole-program wrapper samples (rising to ~86% at 6 declarations), spanning seven distinct printer sites.
- `Function.typeCheck` accepts `bitvec w` for **every** width `w` (checked 0–199, since `LMonoTy.bitvec` is unconstrained in the AST and the known type is the polymorphic `∀n. bitvec n`), but the pretty-printer supports exactly `[1, 8, 16, 32, 64]` — so 60 of the first 64 widths typecheck yet cannot be printed. This resolves issue #48, and **corrects its framing**: the supported set is not "the powers of two" (`bitvec 2`, `4` and `128` are all powers of two and all fail to print), it is the five arms hardcoded in `lmonoTyToCoreType` / `lconstToExpr` / `bvTypeOfWidth`. Note the three sites differ in how they fail: the first two substitute a placeholder, whereas `bvTypeOfWidth` silently returns `.bv64`, so an operator at an unsupported width is printed as a *64-bit* operator.
- For polymorphic functions whose type parameters are only used for type annotations on binders in their body, elaborated programs produced by the typechecker erroneously rewrite the type variable. For example, if we supply this program to the typechecker (which accepts it):

```
-- Note that the type parameter `a` only appears in the type annotation for the exists-quantified variable 
function s<a> () : bool {
  exists q : (a) :: false
}
```

`Program.typeCheck` produces the following elaborated program

```
function s () : bool {
  exists q : ($__ty1) :: false        -- the type variable `a` was rewritten to `$__ty1`
}
```

which fails to parse, with the error message `Undeclared type or category $__ty1`


- `Function.typeCheck` never inspects a function's `preconditions` field at all, so the typechecker can accept functions whose preconditions can:
  + refer to free variables not in the ambient typing context
  + have type other than Bool
  + refer to non-existent operators (i.e. operators that are not in the factory)
The function typing spec (`FuncHasType`) also does not enforce conditions on functions' preconditions, so this omission occurs both in the executable typechecker and its speccification.

One consequence is that the `PrecondElim` pass can turn a well-typed function (accpeted by the typechecker) into an ill-typed procedure. For example, given this function:

```
-- Precondition refers to a nonexistent variable `y`
function f5 () : bool requires Int.SafeDiv(1, 1) == y { true }
```

the `PrecondElim` pass produces the following:

```
-- Typechecker rejects this function with the error message: 
-- "rejected: [assume [precond_f5_0] ((~Int.SafeDiv #1 #1) == (y : int))] No free variables are allowed here!"
procedure f5$$wf ()
{
  assert [f5_precond_calls_Int.SafeDiv_0]: !(1 == 0);
  assume [precond_f5_0]: 1 / 1 == y;
};
function f5 () : bool {
  true
}
```

## Specification bugs caught during testing
- The function typing spec `FuncHasType'` permits a measure (a `decreases` clause) to exist without requiring the function body to also exist, even though the executable typechecker rejects a function if it has a measure but no body
  - The same gap is reachable at whole-program level, via both a top-level `function` declaration and an inline `funcDecl` inside a procedure body: it accounts for ~28% of generated programs being rejected by `Program.typeCheck`
- The `FilterProcedures` transformation returns a Boolean flag to indicate whether the transformation changed the program: this flag is hard-coded to `true`, even though the `Bool` is meant to be interpreted
as whether the transformation modified the analysis state (`CoreTransformState`)
- The spec for the precondition elimination transformation expects all functions in the output factory to have no preconditions, but this is not true, since the transformation doesn't eliminate preconditions for built-ins (e.g. `safeDiv`, safe destructors, etc)


## Specification bugs caught when trying to prove completeness about generators
- `MutualADTWF` doesn't require applications of type constructors to be well-kinded (i.e. match their known arities)
  - Note: this is a broader specification bug: `FuncHasTypeA`, `ProcHasTypeA`, `CmdHasTypeA` also need to enforce well-kindedness of type constructors (i.e. they're applied with the right arity). The following ill-kinded declarations are accepted by the current typing specs but rejected by the typechecker (with an error message `Type Sequence a a is not an instance of a previously registered type`):

```
-- FuncHasTypeA permits this, since it only requires the free type variable `a` to be declared
function f<a> (x : Sequence a a) : int;

-- ProcHasTypeA permits this, for the same reason as above
procedure p<a> (x : Sequence a a) { }

-- CmdHasTypeA permits both of the following commands (in the `init_nondet` / `init_det` rules)
-- Specifically, `init_nondet` only requires `RigidAnnotCompat` on the annotated type, but not well-kindedness
var y : Sequence a a := ...
```
The issue is that in `HasTypeA`, the `fvar` and `op` rules read off the type from the annotation, but it doesn't enforce well-kindedness, so any rule that relies on `HasTypeA.fvar/op` might be susceptible to the arity issue

- `MutualADTWF` doesn't allow arguments to constructors of algebraic data types to refer to type aliases 
- `MutualADTWF` doesn't require free type variables in constructor argument types (for an algebraic datta type) to be among the type parameters of the type being defined
- `CmdHasType` allows type annotations for variable initialization commands to be polymorphic, although the executable command type-checker enforces that type annotations must be monomorphic
- `ProgramHasType` is quantified over source programs (before type aliases are resolved), so it conservatively rejects some type definitions that pass the typechecker (which resolves type aliases before checking well-formedness of algebraic data type definitions).

Consider this source program:
```
type B x := int -> x;
datatype T3 { Base(), MkT3 (f : B T3) }
```

After the type alias `B` is resolved, we get:

```
datatype T3 { Base(), MkT3 (f : int -> T3) }
```
which is a legal datatype definition. However, `ProgramHasType` erroneously rejects the source program as violating the non-nested requirement for ADTs as it doesn't resolve type aliases.
