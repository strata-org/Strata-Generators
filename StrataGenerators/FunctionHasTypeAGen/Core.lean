import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import BasaltExamples.ArbString.Def
import Strata.Languages.Core.Function
import StrataGenerators.HasTypeAGen.Core
import Std.Data.HashSet

open Lambda RandomChoice Core Imperative ArbString Std

/-!
# The core definitions of the generator for a well-typed Strata Core `Function`

This file holds the definition of `genFunction`, which is a generator for a well-typed
Strata Core function. Such a function is a `Function` and therefore an `LFunc CoreLParams`,
and it satisfies the relation `FuncHasTypeA`.

The generator uses `genLExpr` to make a well-typed expression for the body of the function
and for its measure of termination, which is optional. It uses `genLMonoTy` to make the input
types and the output type.

A generated `Function` is well-typed in the sense of `FuncHasTypeA` for four reasons:
1. `List.dedup` builds its `typeArgs` and its `inputs.keys`, so both hold no duplicate.
2. `genLMonoTy typeArgs` builds its input types and its output type, so each free type
   variable of the signature comes from `typeArgs`. This is `noUndeclaredVars`.
3. `genLExpr ... output` builds its body, when it has one, so the body has the declared
   return type. The annotated typing specification `instHasTypeA` *ignores* the ambient
   typing context, so `bodyTyped` reduces to `HasTypeA [] body output`.
4. `genLExpr ... .int` builds its measure, when it has one, so the measure has the type
   `int`.

`FuncHasTypeA` says nothing about `preconditions`. The optional `requires` clause that
`genFunction` also emits, through `genPreconditions`, is therefore invisible to the proof of
soundness. The generator makes that clause over the *formal parameters only*, because the
`precond_freevars` field of `FuncWF` asks that the free variables of a precondition be among
the names of the inputs. Such a clause is also what makes a generated function *partial*,
and it therefore makes the path of `PrecondElim` that strips a precondition reachable from
generated input.
-/

-- ── The generators for a name and for a type argument ───────────────────

/-- The 52 ASCII letters `A-Z` followed by `a-z`. -/
def alphaChars : List Char :=
  (List.range 26).map (fun n => Char.ofNat ('A'.toNat + n)) ++
  (List.range 26).map (fun n => Char.ofNat ('a'.toNat + n))

/-- The characters that a Core identifier can start with: a letter, a `_` or a `$`. This list is a
    subset of `strataIsIdFirst` of Core, which accepts a letter, a `_` and a `$`. Each character
    here is therefore legal at the start of an identifier. -/
def startChars : List Char :=
  alphaChars ++ ['_', '$']

/-- Draws one character from `startChars`. -/
def genStartChar [Gen G] : G Char :=
  elements startChars (by decide)

/-- The characters that a Core identifier can hold after its first character. -/
def remainingChars : List Char :=
  startChars ++ "0123456789".toList ++ ['\'', '.', '?', '!', '$', '@']

/-- Draws one character from `remainingChars`. -/
def genRemainingChar [Gen G] : G Char :=
  elements remainingChars (by decide)

/-- The reserved keywords of Strata Core, as a list. This list is the *source of truth*. Each entry
    is a bare word that the Core lexer reads as a keyword, so the parser rejects it in the position
    of an identifier. For example, `function if () : int;` fails with the message
    "unexpected token 'if'".

    The list comes from the grammar of Core, and it holds four groups:
    - the names of the built-in types, such as `bool`, and the type constructors `Map`, `Sequence`
      and `Type`;
    - the words at the start of a structured statement, such as `if`, `then`, `else`, `forall`,
      `exists`, `var`, `assume`, `assert`, `cover` and `while`;
    - the words at the start of a declaration or of a specification, such as `spec`, `requires`,
      `ensures`, `free`, `procedure`, `function`, `type`, `const`, `axiom`, `distinct`, `datatype`,
      `goto`, `branch`, `return`, `inline`, `decreases`, `invariant`, `out`, `inout`, `old` and
      `have`;
    - the Boolean literals `true` and `false`.

    The module keeps this list, and not only the `HashSet` below, so that `decide` and `simp` can
    evaluate a membership test in a proof. A membership test at run time goes through the `HashSet`
    in `reservedKeywords`. -/
def reservedKeywordsList : List String :=
  -- type names
  [ "bool", "int", "string", "regex", "real",
    "bv1", "bv8", "bv16", "bv32", "bv64", "bv128",
    "Map", "Sequence", "Type",
  -- expressions / structured statements
    "if", "then", "else", "forall", "exists",
    "var", "assume", "assert", "cover", "while",
  -- specs
    "spec", "requires", "ensures", "free", "invariant", "decreases",
  -- declarations
    "procedure", "function", "const", "type", "axiom", "distinct", "datatype",
    "inline",
  -- CFG transfers
    "goto", "branch", "return",
  -- modifiers / misc
    "out", "inout", "old", "have",
  -- boolean literals
    "true", "false" ]

/-- The reserved keywords as a `HashSet`, for a fast membership test in the generator.
    `isReservedKeyword` runs on each generated name. `reservedKeywordsList` builds this set, and
    `HashSet.contains_ofList` joins the two, so a proof can still reason over the list with
    `decide`. -/
def reservedKeywords : Std.HashSet String := Std.HashSet.ofList reservedKeywordsList

/-- Whether `s` is a reserved keyword of Strata Core. The function uses the `HashSet`, so the
    expected time of a lookup is constant. `isReservedKeyword_eq_list_contains` joins this function
    to `reservedKeywordsList`, which the proofs use. -/
def isReservedKeyword (s : String) : Bool := reservedKeywords.contains s

/-- A membership test on the `HashSet` agrees with a membership test on the list. This theorem lets a
    proof reason over `reservedKeywordsList`, which `decide` can evaluate, while the generator uses
    the fast `HashSet`. -/
theorem isReservedKeyword_eq_list_contains (s : String) :
    isReservedKeyword s = reservedKeywordsList.contains s := by
  unfold isReservedKeyword reservedKeywords
  exact Std.HashSet.contains_ofList

/-- Maps a reserved keyword to an identifier that is not a keyword, by an added `_` at the end. The
    map is deterministic. No reserved keyword ends with `_`, and an added `_` keeps a legal
    identifier legal, because `_` is in `strataIsIdRest`. `dodgeKeyword s` is therefore always a
    legal identifier and never a keyword. The function is the identity on a name that is not a
    keyword. -/
def dodgeKeyword (s : String) : String :=
  if isReservedKeyword s then s ++ "_" else s

/-- Makes a legal Core identifier *by construction*. The name starts with a character from
    `startChars`, which holds the letters, `_` and `$`, and each of those is in `strataIsIdFirst`. A
    run of characters from `remainingChars` follows, and that run can be empty. Each character of
    `remainingChars` is in `strataIsIdRest`. `dodgeKeyword` then maps a reserved keyword to a name
    that is not a keyword.

    Each output is therefore a legal Core identifier and not a keyword. It is not empty, and it
    starts with a letter, a `_` or a `$`, so the lexer reads it as an `Ident` and never as a `Num`.
    The parser also accepts it in the position of an identifier.

    `genFunction` takes its names from this generator. `remainingChars` holds `.`, which is legal in
    a bare identifier but which collides with the syntax of a binder and of a qualified name under
    maximal munch. An output that holds a `.` can therefore fail to round-trip. This is deliberate:
    the name is legal by construction, so such a failure is a real defect of the Core printer or of
    the Core parser to report, and not an artifact of the generator. For a character that only the
    form with pipes can hold, such as `|` and `\`, see `genQuotedName`. -/
def genIdentName [Gen G] : G String := do
  let x ← genStartChar
  let xs ← listOf genRemainingChar
  return dodgeKeyword (String.ofList (x :: xs))

-- ── The generator for a hard but legal identifier ────────────────────────

/-- The alphabet of `genQuotedName`. Beyond the characters that a bare identifier can hold, it adds
    the special characters that force an interesting path in the printer or in the parser:
    - `'`, which the lexer accepts bare and which the printer writes between pipes;
    - `.`, which both accept bare, but which collides with the syntax of a binder and of a qualified
      name under maximal munch;
    - `|` and `\`, which a bare identifier can hold in no position. Only the form between pipes,
      `|…|`, can hold them, and it needs the escapes `\|` and `\\`. -/
def quotedNameChars : List Char :=
  remainingChars ++ ['|', '\\']

/-- Draws one character from `quotedNameChars`. -/
def genQuotedNameChar [Gen G] : G Char :=
  elements quotedNameChars (by decide)

/-- Makes an identifier that is hard for the printer and the parser, and that is still **legal**. The
    name starts with a character from `startChars`, which holds the letters, `_` and `$`, and each of
    those is in `strataIsIdFirst`. A run of characters from `quotedNameChars` follows, and that run
    can be empty. That run holds the special characters `. ' ? ! $ @`, and it can also hold `|` and
    `\`, which only the form between pipes can carry.

    The condition on the first character is what keeps each output a *legal Core identifier*. A
    leading `@`, `?`, digit or `|` is not a legal identifier in any position, bare or between pipes in
    the slot of a type variable. Without the condition, this generator would emit an illegal name, and
    a failure of the round trip would be an artifact of the generator and not a defect of Strata. With
    the condition, a failure is a real defect of faithfulness in the Core printer or in the Core
    parser, and `genIdentName` gives the same guarantee. The special characters inside the name still
    exercise the path that quotes and escapes, which is `escapePipeIdent` against
    `parsePipeDelimitedIdent`, and the hazards of a bare form, such as a collision of a `.` under
    maximal munch.

    This generator is separate from `genIdentName` on purpose. It feeds neither `genFunction` nor the
    proofs of soundness and completeness. Run it through the harness for the round trip of one
    identifier. The first character also makes each name not empty, so a tail of `[]` from `listOf` is
    correct. -/
def genQuotedName [Gen G] : G String := do
  let c ← genStartChar
  let cs ← listOf genQuotedNameChar
  return String.ofList (c :: cs)

/-- Makes a random list of names whose length is not more than `depth`.

    The definition uses the `listOfMaxLength` combinator, which this package vendors from Basalt.
    `SetGen.mem_support_listOfMaxLength_iff` gives its support. -/
def genNameList [Gen G] (depth : Nat) : G (List String) :=
  listOfMaxLength depth genIdentName

/-- Makes a list of names for the type arguments. The names are *different* in pairs, because
    `List.dedup` builds the list. -/
def genTypeArgs [Gen G] (depth : Nat) : G (List TyIdentifier) :=
  List.dedup <$> genNameList depth

/-- Makes a list of identifiers for the inputs. The names are *different* in pairs, because
    `List.dedup` builds the list. The identifiers are therefore also different, because the map from a
    name to `⟨·, ()⟩` is injective. -/
def genIdents [Gen G] (depth : Nat) : G (List (Identifier Unit)) :=
  (fun names => (names.map (fun s => (⟨s, ()⟩ : Identifier Unit))).dedup) <$> genNameList depth

-- ── The generator for the signature of the inputs ───────────────────────

/-- Makes the signature of the parameters. The result is a `ListMap` from identifiers that differ in
    pairs to monotypes. `genLMonoTy tvars` draws each type, so each free type variable of a type is in
    `tvars`. -/
def genInputs [Gen G] (tvars : List TyIdentifier) (depth : Nat) :
    G (ListMap (Identifier Unit) LMonoTy) := do
  let idents ← genIdents depth
  idents.mapM (fun x => do
    let ty ← genLMonoTy tvars depth
    pure (x, ty))

-- ── The generator for an optional body and an optional measure ──────────

/-- Makes an optional well-typed expression of the type `τ`. The result is `none`, or it is `some e`
    where `genLExpr` made `e` at the type `τ`, in the empty context of bound variables and with an
    empty context of polymorphic operators. The bias is 3 to 1 toward `some`, so a body and a measure
    are usually present. -/
def genOptExpr [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy) (pctx : PolyOpCtx := []) : G (Option LExpr') :=
  biasedOptionGen (3 / 4) (genLExpr fctx octx pctx tvars [] depth τ)

-- ── The generator for a precondition ────────────────────────────────────

/-- Reads the signature of the formal parameters as a `FVarCtx`, so that a generated expression can
    refer to an input of the function by its name.

    This is the *only* free-variable context for a precondition. `FuncWF.precond_freevars` asks that
    the free variables of each precondition be a subset of the names of the formal parameters, and
    `body_freevars` asks the same for the body. A call that gave the ambient `fctx` to `genLExpr` here
    would therefore make a function that is not well formed, and not only a function that is dull. -/
def inputsAsFVarCtx (inputs : ListMap (Identifier Unit) LMonoTy) : FVarCtx :=
  inputs.toList.map (fun (id, mty) => (id.name, mty))

/-- Makes an expression of the type `bool` that *always* mentions a formal parameter of the function.
    It picks a formal parameter `(x, τ)`, and it then builds `x == e`, where it made `e` at the type
    `τ` of that parameter.

    This function gives the bias toward a precondition that mentions an input. A draw from `genLExpr`
    at `.bool` alone is not enough. The `bool` rules of `genLExprBase` can reach a leaf that is a
    *variable* only through `fvarsOfType fctx .bool`, so a formal parameter is reachable only when its
    own type is `bool`, and few generated signatures have such a parameter. An equality between a
    formal parameter of *any* type and an expression of that same type avoids the problem: the
    equality node has the type `bool` whatever `τ` is, so each formal parameter becomes usable.

    The function needs a proof that `inputs` is not empty, and that proof is what makes the pick by
    `elements` total. `genPrecondition` gives the proof from a `dif`. -/
def genInputMentioningPrecond [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier)
    (depth : Nat) (hne : inputs.toList ≠ []) (pctx : PolyOpCtx := []) : G LExpr' := do
  let (x, τ) ← elements inputs.toList hne
  let e ← genLExpr (inputsAsFVarCtx inputs) octx pctx tvars [] depth τ
  pure (.eq () (.fvar () x (some τ)) e)

/-- Makes an optional precondition of the type `bool`, which is a `requires` clause, over the formal
    parameters of the function. `optionGen` gives a `some` with probability 1/2.

    The bias is 3 to 1 toward a clause that mentions a formal parameter, which
    `genInputMentioningPrecond` builds, over a plain draw from `genLExpr` at `.bool`. Both branches
    make an expression in the free-variable context `inputsAsFVarCtx inputs`, so *each* free variable
    is a formal parameter in both branches. The bias is about how often a variable occurs at all, and
    not about good form. A function with no formal parameter has nothing to mention, so it uses the
    draw with no bias, which gives a closed Boolean expression over `octx`.

    The code threads `octx` through without a change, so a precondition can itself call a *partial*
    operator, such as `Int.SafeDiv`, when the caller gives one. This is what makes the path of
    `PrecondElim` that strips a precondition reachable from generated input. -/
def genPrecondition [Gen G] (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx := []) :
    G (Option (Strata.DL.Util.FuncPrecondition LExpr' Unit)) :=
  optionGen (do
    let e ←
      if hne : inputs.toList ≠ [] then
        frequency
          [ (3, fun () => genInputMentioningPrecond octx inputs tvars depth hne pctx),
            (1, fun () => genLExpr (inputsAsFVarCtx inputs) octx pctx tvars [] depth .bool) ]
          (by show 0 < 3 + 1; omega)
      else
        genLExpr (inputsAsFVarCtx inputs) octx pctx tvars [] depth .bool
    pure { expr := e, md := () })

/-- The `preconditions` field of a generated function. The result is the list `[p]` when
    `genPrecondition` gives `some p`, and it is `[]` otherwise.

    The field needs a list and not an `Option`. One clause is enough to make each code path that
    reads a precondition non-vacuous. A limit of one clause also keeps the obligation about
    reachability in `genFunction_complete` a side condition about one expression. -/
def genPreconditions [Gen G] (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx := []) :
    G (List (Strata.DL.Util.FuncPrecondition LExpr' Unit)) :=
  (fun o => o.toList) <$> genPrecondition octx inputs tvars depth pctx

-- ── The main generator for a function ───────────────────────────────────

/-- Makes a well-typed `Function`, which is an `LFunc CoreLParams`.

    The function satisfies `FuncHasTypeA C Γ` for each ambient context `Γ`, as
    `genFunction_sound` states.

    The generator makes these parts:
    - `typeArgs`: a list of names for the type variables, with no duplicate;
    - `inputs`: a signature whose keys hold no duplicate, and whose types are over `typeArgs`;
    - `output`: a type over `typeArgs`;
    - `body`: an optional expression of the type `output`;
    - `measure`: an optional expression of the type `int`;
    - `preconditions`: at most one clause of the type `bool` over the *formal parameters*, which
      `genPreconditions` makes. It gives a clause half of the time, and it favours a clause that
      mentions a formal parameter.

    `FuncHasType'` puts no condition on a precondition, because it has no field for one. A draw of a
    precondition therefore cannot change `genFunction_sound`. A precondition matters later: a
    function with a `preconditions` list that is not empty is *partial*. This is what makes the path
    of `PrecondElim` that strips a precondition, and the property `preconditionsStripped`, reachable
    from generated input, and not only from a reproducer that someone builds by hand.

    The fields that the typing specification does not constrain keep their default values. Those
    fields are `isConstr`, `isRecursive`, `attr` and `axioms`. -/
def genFunction [Gen G] (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) : G Function := do
  let name ← genIdentName
  let typeArgs ← genTypeArgs depth
  let inputs ← genInputs typeArgs depth
  let output ← genLMonoTy typeArgs depth
  let body ← genOptExpr fctx octx typeArgs depth output pctx
  let measure ← genOptExpr fctx octx typeArgs depth .int pctx
  let preconditions ← genPreconditions octx inputs typeArgs depth pctx
  pure {
    name := ⟨name, ()⟩,
    typeArgs := typeArgs,
    inputs := inputs,
    output := output,
    body := body,
    measure := measure,
    preconditions := preconditions
  }
