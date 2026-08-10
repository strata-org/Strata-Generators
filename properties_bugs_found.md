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

## Implementation bugs caught

- `LExpr` type inference is incomplete (if we erase type annotations on a well-typed term, if the resultant term contains an unannotated quantified free variable e.g. `\forall x. x`, type inference fails to reconstruct a type)
- Progress doesn't hold for `LExpr`s (this was previously known, due to uninterpreted functions, the fact that `\forall` and `\exists` quantifiers don't evaluate under `if` and equality of lambda expressions is conservative)
- 7 situations in which the parser + pretty-printer round-trip for functions fails:
  - Type parameters to functions can't begin with `s` in their name (conflicts with `<s` signed less-than operator):
  - Pretty-printer mis-prints `real` numbers that are represented as rationals with a non-terminating decimal representation (e.g. `1/3` is `0.333...`, but is printed as `0.0` instead)
  - Unapplied unary operators can't be pretty-printed (e.g. `Bool.Not` can't be printed if it's not applied to an argument)
  - Pretty-printer misses parentheses around arrow / type constructors, so `Map int (int -> int)` is printed as `Map int int -> int`, which is mis-parsed as `(Map int int) -> int` (since type application binds tighter than `->`)
  - Pipe-escaping identifiers for types (wrapping identifiers with `|...|` to handle SMTLib names) is not done uniformly (only done for type annotations but not the return type for functions)
  - Periods are allowed in the grammar for identifiers but not accepted by the parser (which uses them to resolve namespaces)
  - Applying the factory function `Real.Neg` on a negative real number literal fails the round-trip property due to missing parenthesization (`Real.Neg (-3.0)` is printed as `--3.0`, which re-parses as `-(-3.0)`; note `Int.Neg (-3)` correctly prints as `-(-3)`)
- The precondition elimination transformation erroneously reports its `changed` flag as false, even though it rewrites procedures to gain an `assert` statement in its body. This happens
for nested function declarations that don't have preconditions, but whose bodies invoke a precondition-carrying function (e.g. `Int.SafeDiv`).
- Non-ASCII strings are not escaped when passed to SMT-Lib, so the Core partial evaluator and SMT solvers disagree on the length of non-ASCII strings (The Core evaluator reports `Str.Length "é" = 1`, but Z3 says `Str.Length "é" = 2` and CVC5 reports `Parse Error: Non-printable character in string literal`)
- The SMT dialect's comparison operator on real numbers (represented as decimal orders) isn't a total order, i.e. it is possible for `r1 <= r2`, `r2 <= r1` and `r1 == r2` to all be false, violating trichotomy
- The SMT dialect's equality check returns false on two decimals that are mathematically equal but have different mantissa-exponent representations (e.g. `3.0` can be represented as `3 * 10^0` or `30 * 10^-1` , which are mathematically the same but considered to be not equal)

## Specification bugs caught during testing
- The function typing spec `FuncHasType'` permits a measure (a `decreases` clause) to exist without requiring the function body to also exist, even though the executable typechecker rejects a function if it has a measure but no body
- The `FilterProcedures` transformation returns a Boolean flag to indicate whether the transformation changed the program: this flag is hard-coded to `true`, even though the `Bool` is meant to be interpreted
as whether the transformation modified the analysis state (`CoreTransformState`)
- The spec for the precondition elimination transformation expects all functions in the output factory to have no preconditions, but this is not true, since the transformation doesn't eliminate preconditions for built-ins (e.g. safeDiv, safe destructors, etc)

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
