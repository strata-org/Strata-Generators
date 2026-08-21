# Properties Tested & Bugs Found

## Properties tested

**LExprs**

- Preservation
- Progress (counterexamples found, known)
- Completeness of `LExpr.resolve` type inference (counterexamples found, previously unknown)
- `LExpr.eval` doesn't introduce any new free variables
- The concrete evaluator agrees with the SMT semantics: for a closed term `e`, if `LExpr.evalWithLState` reduces `e` to a constant, then the solver confirms that `SMTEncode(e) = SMTEncode(eval e)`
  - Restricted to base types (`int`, `string`, `bool`, `bitvec`) over `Core.Factory` operators, so that every subterm is SMT-encodable; terms that don't reduce to a constant are skipped rather than counted as counterexamples
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
- Completeness of executable typechecker with respect to the declarative typing spec

**`FilterProcedures` transformation**
(Removes procedures that are unreachable from an input list of procedure declarations, where unreachable = "not in the transitive closure")

- The `FilterProcedures` transformation updates its `changed` flag correctly
  - This transformation removes unreachable procedures (unreachable from a given starting point, which is a list of procedures)
- `FilterProcedures` keeps the procedures that were specified as starting points
- `FilterProcedures` keeps all procedures that are in the transitive closure of the starting list of procedures
- `FilterProcedures` only removes procedures (and not other declarations)
- `FilterProcedures` removes all unreachable procedures 
- List of output procedure declarations is a subset of the procedures fed as input to `FilterProcedures`
- Call-graphs remain well-formed after the `FilterProcedures` transformation

**`PrecondElim` transformation**
(removes preconditions from procedures)

- This transformation indeed removes preconditions
- This transformation preserves the name + type signature of procedures & functions
- This transformation does not remove any declarations and preserves declaration order
- Each precondition is transformed into one `assert` in the body of the procedure
- All calls to partial procedures are translated into an assertion
- Call-graphs remain well-formed after the `PrecondElim` transformation

**ANF encoding / Common-subexpression elimination (CSE)**

- Result of ANF transformation is well-typed
- ANF transformation is idempotent
- ANF does not change the control-flow skeleton or call-graph
- ANF preserves procedure declarations and does not affect non-procedure declarations
- CSE does not result in dangling (unbound) bound De Bruijn variables
- Result of the symbolic evaluator is the same before/after CSE
  - (By the same, we mean that the path-condition expressions and the stores are the same after resolving the value of new variables that are created during CSE)
- Declaration order is preserved after ANF encoding

**`LiftInternalFuncDecls` transformation (Lambda lifting)**
- Every hoisted function declaration is closed
- After lambda lifting, no procedure body contains a local function declaration
- Lambda lifting does not change a program that has no local function declarations
- No hoisted functions have free type variables
- Output of lambda lifting typechecks
- Lambda lifting transformation is idempotent

**Monomorphization of top-level functions**
- A monomorphized program still typechecks
- In monomorphized programs, there are no top-level functions / factory functions that are parameterized by type variables
- Monomorphization transformation is idempotent
- Monomorphization does not change type definitions / declarations
- Polymorphic datatype definitions remain polymorphic after monomorphization
- Derived tester / field projection functions for polymorphic datatypes are monomorphized 
- No naming collisions in output program
- Monomorphization does not change programs that don't contain polymorphic functions
- Declaration order is preserved by monomorphization
- Result of evaluation is preserved by monomorphization

**SMT dialect**
- Decimal comparison is a total order
- Two decimals which are mathematically equal (but have different mantissa-exponent representations) are still considered to be equal by the equality check
- All string literals passed to SMT are printable ASCII

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

**`IrrelevantAxioms` transformation**
(Removes axioms that do not mention any of the functions named in the `--functions` flag, thereby reducing the size of the analysis problem.)
- The transformation only removes axioms and nothing else 
- The transformation preserves declaration order
- All axioms retained by the transformation are relevant
- All axioms removed are irrelevant 
- An axiom that is removed doesn't mention any function that is in the call-graph closure of the functions passed as input
- The output program typechecks
- The transformation does not change proof obligations

**`StructuredToUnstructured` transformation**
(Takes a sequence of statements with structured control flow, and compiles it into a control-flow graph consisting of basic blocks and `goto`s)
- All block labels in the output program are distinct 
- There exists a label to an entry block in the output program
- There is exactly one block labelled `.finish` in the output program
- In the output program, all blocks are reachable from the entry block 
- The no. of commands in the output program is at least the no. of commands in the input program 
- All targets of `goto`s in the output program are block labels 

**`DetToKleene` transformation**
(Converts deterministic structured control-flow into Kleene Algebra with Tests: `if` and `while` are replaced with non-deterministic choice and Kleene star)
- Loops with measures are translated to KAT and not dropped
- The `detToKleene` transformation produces a result when there are no `exit` or function + type declarations in the original list 

- **`InsertLoopInvariantAsserts` transformation**
(Converts loop invariants into relevant `assert`/`assume` statements)
- For a program containing `n` loop invariants and `m` measure-carrying loops, the transformation inserts exactly `2n + 2m` assertions
- Loops in the output program don't contain loop variants or measures
- Transformation is idempotent
- Non-deterministic loops with `decreases` clauses are rejected
- Proof obligations incurred by symbolic evaluation are preserved by this transformation

**`LoopElim` transformation**
(Removes loops to simplify verification problems, keeping only the relevant assertions related to loop invariants, facilitating verification)
- There are no loops in the output program
- `LoopElim` does not drop any verification conditions
- All block labels in the output program are distinct

**Common sub-expression elimination (`CommonSubexprElim`)**
- No fresh variables are declared twice in the output program
- All assertions are preserved
- Output program typechecks (this catches bugs where variables are used before they're defined)

**Function inlining**
(Note: the function that implements this transformation takes a `fuel` parameter)
- If we supply `fuel = 0` to the transformation, the program is unchnaged
- Function inlining preserves the type of programs
- No free variables are introduced by function inlining
- Function inlining preserves the result of evaluation
- Function inlining preserves the types of expressions
- The number of still-inlinable calls if we supply `fuel = 4` ≤ no. of inlinable calls if we supply `fuel = 1`

**Procedure inlining**
- No duplicate labels are introduced by this transformation
- No assertions are removed
- The `visitedCalls` and `inlinedCalls` statistics are consistent after this transformation
- Output program typechecks
- The call-graph remains well-formed after this transformation
- Proof obligations produced via symbolic evaluation are preserved by this transformation (specifically the set of proof obligations for the input program is a subset of the proof obligations for the output program)

**`NondetElim` transformation**
- No non-deterministic loops or conditionals are present in the output program
- All fresh labels for guards are distinct 
- Proof obligations incurred by symbolic evaluation are preserved by this transformation

**`LoopInitHoist` transformation**
(Hoists variable initialization inside a loop to outside the loop)
- No loop body contains a variable initialization command after this transformation
- The set of all initialized variables is preserved by this transformation
- Proof obligations incurred by symbolic evaluation are preserved by this transformation

**Injectivity and disjointness of constructors for algebraic data types**
- SMT encoding of algebraic data types allows the SMT solver to prove injectivity of constructors
- SMT encoding of algebraic data types allows the SMT solver to prove disjointness of constructors 
- The Core program which encodes injectivity and disjointness assertions typechecks

**Functions derived from ADT definitions**
- No ADT definition triggers functions with duplicate names

**Type aliases**
- Resolving all type aliases before typechecking vs incrementally resolving type aliases during typechecking (one declaration at a time) result in the same proof obligations and agree on whether they accept the program

**Mutually recursive datatypes**
- Typechecker accepts individual non-mutually-recursive datatypes which are placed in the same `mutual` block
- The types of all derived functions don't contain free type variables
- The derived functions produced by a block `mutual t1, ..., tk end` where all the `ti` are *not* mutually-recursive are the same as the functions
produced by `k` individual blocks `mutual t1 end; mutual t2 end; ..., mutual tk end` 

## Implementation bugs caught

- **(FIXED)** `LExpr` type inference is incomplete (if we erase type annotations on a well-typed term, if the resultant term contains an unannotated quantified free variable e.g. `\forall x. x`, type inference fails to reconstruct a type)
- Progress doesn't hold for `LExpr`s (this was previously known, due to uninterpreted functions, the fact that `\forall` and `\exists` quantifiers don't evaluate under `if` and equality of lambda expressions is conservative)
- 11 situations in which the parser + pretty-printer round-trip fails:
  - **(FIXED)** `Type parameters to functions can't begin with `s` in their name (conflicts with `<s` signed less-than operator):
  - **(FIXED)** `Pretty-printer mis-prints `real` numbers that are represented as rationals with a non-terminating decimal representation (e.g. `1/3` is `0.333...`, but is printed as `0.0` instead)
  - Unapplied unary operators can't be pretty-printed (e.g. `Bool.Not` can't be printed if it's not applied to an argument)
  - **(FIXED)** `Pretty-printer misses parentheses around arrow / type constructors, so `Map int (int -> int)` is printed as `Map int int -> int`, which is mis-parsed as `(Map int int) -> int` (since type application binds tighter than `->`)
  - Pipe-escaping identifiers for types (wrapping identifiers with `|...|` to handle SMTLib names) is not done uniformly (only done for type annotations but not the return type for functions)
  - **(FIXED)** Periods are allowed in the grammar for identifiers but not accepted by the parser (which uses them to resolve namespaces)
  - **(FIXED)** `Applying the factory function `Real.Neg` on a negative real number literal fails the round-trip property due to missing parenthesization (`Real.Neg (-3.0)` is printed as `--3.0`, which re-parses as `-(-3.0)`; note `Int.Neg (-3)` correctly prints as `-(-3)`)
  - Typechecker accepts bit-vector types with non-power-of-2 lengths, but the printer only supports printing the types `bv{1, 8, 16, 32, 64} `-- unsupported bitvec types are printed as `$__unknown_type` instead
  - **(FIXED)** `Bit-vector literals with some width `n`, where `n` is not a power of 2, are printed as `bv{64}(n) `(i.e. the width `n` becomes the value, and the actual value of the bit-vector is discarded), changing the meaning of the term
  - **(FIXED)** ``bv128` is registered in the Core factory & the DDM, but `bv128` literals are unprintable / unparseable 
  - Core contains factory functions `Bv{n}.ToInt` and `Int.ToBv{n}` for converting from bitvec <-> int, but these functions are unprintable
- The precondition elimination transformation erroneously reports its `changed` flag as false, even though it rewrites procedures to gain an `assert` statement in its body. This happens
for nested function declarations that don't have preconditions, but whose bodies invoke a precondition-carrying function (e.g. `Int.SafeDiv`).
- Non-ASCII strings are not escaped when passed to SMT-Lib, so the Core partial evaluator and SMT solvers disagree on the length of non-ASCII strings (The Core evaluator reports `Str.Length "é" = 1`, but Z3 says `Str.Length "é" = 2` and CVC5 reports `Parse Error: Non-printable character in string literal`)
- The SMT dialect's comparison operator on real numbers (represented as decimal orders) isn't a total order, i.e. it is possible for `r1 <= r2`, `r2 <= r1` and `r1 == r2` to all be false, violating trichotomy
- The SMT dialect's equality check returns false on two decimals that are mathematically equal but have different mantissa-exponent representations (e.g. `3.0` can be represented as `3 * 10^0` or `30 * 10^-1` , which are mathematically the same but considered to be not equal)
- `bitvec 128` literals cannot be pretty-printed, even though the width is registered in the factory (`Factory.lean`) and has a grammar production (`bv128Lit`, `Grammar.lean:113`): `lconstToExpr` logs `unsupported bitvec width: 128`. Every other registered width prints.
- **(FIXED)** `None of the 18 `Bv{w}.ToInt` / `Bv{w}.ToUInt` / `Int.ToBv{w}` conversion operators can be pretty-printed, at *any* registered width (`w ∈ {1, 8, 16, 32, 64, 128}`). They are all registered in the factory (`Factory.lean`) but have no grammar production, so each of these is 
rendered as a fresh type variable instead. 
- `Function.typeCheck` accepts `bitvec w` for all natural numbers `w`, but the pretty-printer only support widths in the set `{1, 8, 16, 32, 64}`
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

The five findings below come from testing the eight Core transform passes that have no correctness proof (issue #69). The first four have a self-contained reproducer in [`docs/strata-unproven-transform-bugs.md`](docs/strata-unproven-transform-bugs.md); the fifth — which is in the symbolic evaluator rather than in a pass — is in [`docs/strata-symbolic-eval-nondet-collision.md`](docs/strata-symbolic-eval-nondet-collision.md). Each is pinned by a `#guard` in `StrataGenerators/ProgramGen/UnprovenTransforms.lean` so a fix turns the guard red.


- For a given loop, the `LoopElim` transformation creates two blocks that share the same label. Minimal counterexample: a procedure whose body is a non-determinsitic loop (`while * { }`).
- `ProcedureInlining` gives two call sites of the same procedure identical labels
- `ProcedureInlining` drops the callee's `requires` obligation. Consider this sourc ep

Consider this source Core program:
```
procedure Foo(x : int)
spec { 
  requires [pre]: x >= 0; 
} { };

procedure Main () {
  var y : int := -1;
  call Foo(y);
};
```

and this resultant program (obtained via ProcedureInlining):

```
-- Foo is same as before

-- Note that `Foo`'s precondition is missing after it is inlined into `Main`
procedure Main () {
  var y : int := -1;
  Foo$inlined: {
    var Foo_x_0 : int := y;
  }
}
```
The symbolic evaluator returns 1 obligation on the source program, but 0 obligations in the transformed program (a missing proof obligation).


- `ProcedureInlining` copies `old x` expressions verbatim while renaming `x`, turning a well-typed program into an ill-typed one. Consider this source Core program:
```
procedure Foo (inout T : bool) {
  assert [inner]: old T;
};

procedure Main () {
  var T : bool := true;
  call Foo(inout T);
};
Transformed program:
procedure Foo (inout T : bool) {
  assert [inner]: old T;
};
```

Transformed program after procedure inlining:

```
procedure Main () {
  var T : bool := true;
  Foo$inlined: {
    var Foo_T_1 : bool := T;               -- <-- Note that `T` is renamed to `Foo_T_1`, but the `old T` inside the `assert` is copied as-is
    assert [Foo_inner_2]: old T;
    T := Foo_T_1;
  }
};
```

On the transformed program, the typechecker emits an error:

```
No free variables are allowed here! Free Variables: [old T]]
```

- Symbolic evaluator drops proof obligations in programs with two consecutive non-deterministic conditionals. Consider this Core source program:

```
procedure P ()
{
  if * {
    assert [a]: true;
  }
  if * {
    assert [b]: true;
  }
};
```

The symbolic evaluator emits the following:

```

};
procedure P ()                        // ← the obligation program
{
  assume [|<label_ite_cond_true: $__nondet_cond_2>|]: $__nondet_cond_2;
  assert [a]: true;
};
```
Note that we only have `assert [a]`, and `assert [b]` is missing.

- The datatype `bitvec 0` is legal in Core and illegal in SMT-LIB: cvc5 emits the error `Parse Error: Illegal bitvector size: 0` and z3 emits the error `bit-vector size must be greater than zero`

- **(FIXED)** Naming collisions for auto-derived ADT functions in Core: An ADT field named `f!` (which is legal, since `!` is a valid identifier character) collides with the name of the automatically derived unsafe field accessor for another field `f`

- Type of auto-derived eliminators for Core ADTs contain free type variables. Consider these two Core datatype definitions which are put in the same mutual block (even though they are not actually mutually recursive):

```
mutual 
  datatype Aa (x : Type) { 
    mkA(fa: x) 
  }
  datatype Bb (y : Type, z : Type) { 
    mkB(fb: y), 
    nilB() 
  }
end
```

These two type definitions are accepted by the typechecker.

For these two ADTs, genBlockFactory produces eliminators with the following types:

```
Aa$Elim : ∀[$__ty0, $__ty1, x].    Aa x   → (x → $__ty0) → (y → $__ty1) → $__ty1 → $__ty0
                                                            ^ y is free
Bb$Elim : ∀[$__ty0, $__ty1, y, z]. Bb y z → (x → $__ty0) → (y → $__ty1) → $__ty1 → $__ty1
                                             ^ x is free
```                                             
Note that the types for both `Aa$Elim` and `Bb$Elim` contain free type variables which are not bound (`y` for the former, `x` for the latter).

- `CommonSubexprElim` produces variable definitions that read other variables before they're defined. Consider this source Core program, which contains a common subterm `int.add(G, 4)`, where `G` is a local variable:

```
procedure P () {
  var G : int := 0;
  var a : int := int.add(G, 4);
  var b : int := int.add(G, 4);
};
```

CommonSubexprElim (CSE) rewrites it to the following:

```
procedure P () {
  -- Hoisted variable refers to `G` before it is defined
  var $__cse.0 : int := int.add(G, 4);
  var G : int := 0;
  var a : int := $__cse.0;
  var b : int := $__cse.0;
};
```

Note that the hoisted variable `$__cse.0` comes before the declaration of `G`, so the transformed program doesn't typecheck. The typechecker emits the following error:

```
[init ($__cse.0 : int) := ((~Int.Add : (arrow int (arrow int int))) (G : int) #4)]
No free variables are allowed here! Free Variables: [G]
```


## Specification bugs caught during testing
- **(FIXED)** `The function typing spec `FuncHasType'` permits a measure (a `decreases` clause) to exist without requiring the function body to also exist, even though the executable typechecker rejects a function if it has a measure but no body
  - The same gap is reachable at whole-program level, via both a top-level `function` declaration and an inline `funcDecl` inside a procedure body: it accounts for ~28% of generated programs being rejected by `Program.typeCheck`
- **(FIXED)** `The `FilterProcedures` transformation returns a Boolean flag to indicate whether the transformation changed the program: this flag is hard-coded to `true`, even though the `Bool` is meant to be interpreted
as whether the transformation modified the analysis state (`CoreTransformState`)
  - Note: after discussion with the Strata Core team, this is a larger design ambiguity related to inconsistent interpreteations of this Boolean flag for a range of transformations across the Strata codebase. This issue has since been rectified.
- The spec for the precondition elimination transformation expects all functions in the output factory to have no preconditions, but this is not true, since the transformation doesn't eliminate preconditions for built-ins (e.g. `safeDiv`, safe destructors, etc)


## Specification bugs caught when trying to prove completeness about generators
- **(FIXED)** `MutualADTWF` doesn't require applications of type constructors to be well-kinded (i.e. match their known arities)
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
- **(FIXED)** `MutualADTWF` doesn't require free type variables in constructor argument types (for an algebraic data type) to be among the type parameters of the type being defined
- **(FIXED)** `CmdHasType` allows type annotations for variable initialization commands to be polymorphic, although the executable command type-checker enforces that type annotations must be monomorphic
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
- Typing spec for local function declarations allows for arbitrary well-typed functions in output context. Consider the following (declarative) typing rule for local function declarations (in `StatementHasType`):

```
  /-- Local function declaration. The function is non-recursive and well-typed
      (per `FuncHasType'`, evaluated in the ambient `C, Γ`); the resulting `func`
      is added to `C` for subsequent statements. -/
  | funcDecl : ∀ C Γ L decl func md Δ,
      ¬ decl.isRecursive →
      FuncHasType' τ C Γ func →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementHasType' τ P C Γ L (.funcDecl decl md) (C.addFactoryFunction func.toLFunc) Δ
```

This rule does not connect the function declaration `decl` with the actual function `func`. Specifically, `func` is allowed to be any arbitrary well-typed function in this rule. 

The executable typechecker in `StatementType.lean` implements this rule
as follows:

```lean
  | .funcDecl decl md => do
    if decl.isRecursive then .error …
    let (decl', func, Env) ← PureFunc.typeCheck C Env decl
    let C := C.addFactoryFunction func.toLFunc
    .ok (.funcDecl decl' md, Env, C)
```
Note that the typechecker calls `let func ← Function.ofPureFunc decl` to convert the function declaration into a function, so it derives `func` from `decl`, which is currently not done in the typing spec. 

The typing spec currently allows us to declare the local function `f` (as a statement inside a procedure):

```
procedure caller () {
    function f (x : int) : bool { x };  
}
```
but the output context is allowed to any other arbitrary function that is well-typed (e.g. `function g() : bool { ... }`).
