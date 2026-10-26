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
Strata Core function. Such a function is a `Function` and therefore an `LFunc CoreLParams`.

The generator uses `genLExpr` to make the well-typed expressions of the function: its optional
body, its preconditions, its axioms and its optional measure. It uses `genLMonoTy` to make the
input types and the output type.

A generated `Function` satisfies the typing spec `FuncWellTyped` for these reasons:
1. `List.uniq` builds its `typeArgs` and its `inputs.keys`, so both hold no duplicate.
2. The generator keeps only the type arguments that the signature mentions, and `genLMonoTy`
   builds the signature over them, so the signature mentions exactly its type arguments.
3. Every expression is drawn by `genLExpr` at its declared type, over the formals and the ambient
   variables that no formal shadows, restricted to the type arguments: a variable or an operator
   whose type mentions any other type variable would put a type variable that is not a type
   argument into an annotation.
4. A constructor has no body, a non-recursive function has no measure, and a bare-variable
   measure is a formal of type `int` or of a datatype type.
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
    `List.uniq` builds the list. -/
def genTypeArgs [Gen G] (depth : Nat) : G (List TyIdentifier) :=
  List.uniq <$> genNameList depth

/-- Makes a list of identifiers for the inputs. The names are *different* in pairs, because
    `List.uniq` builds the list. The identifiers are therefore also different, because the map from a
    name to `⟨·, ()⟩` is injective. -/
def genIdents [Gen G] (depth : Nat) : G (List (Identifier Unit)) :=
  (fun names => (names.map (fun s => (⟨s, ()⟩ : Identifier Unit))).uniq) <$> genNameList depth

-- ── The generator for the signature of the inputs ───────────────────────

/-- Makes the signature of the parameters: a `ListMap` from identifiers that differ in pairs to
    types that `genTy` draws. -/
def genInputs [Gen G] (genTy : G LMonoTy) (depth : Nat) :
    G (ListMap (Identifier Unit) LMonoTy) := do
  let idents ← genIdents depth
  idents.mapM (fun x => do
    let ty ← genTy
    pure (x, ty))

/-- Draws the type of a formal: a type from `genLMonoTy`, or, one time in four when `dts` is not
    empty, a datatype of `dts` applied to as many such types as its arity. -/
def genInputTy [Gen G] (dts : List (String × Nat)) (tvars : List TyIdentifier) (depth : Nat) :
    G LMonoTy :=
  if h : dts ≠ [] then
    frequency
      [ (3, fun () => genLMonoTy tvars depth),
        (1, fun () => do
          let kc ← elements dts h
          let args ← vectorOf kc.2 (genLMonoTy tvars depth)
          pure (.tcons kc.1 args)) ]
      (by simp)
  else
    genLMonoTy tvars depth

-- ── The generator for an optional body ──────────────────────────────────

/-- Makes an optional well-typed expression of the type `τ`. The result is `none`, or it is `some e`
    where `genLExpr` made `e` at the type `τ`, in the empty context of bound variables. The bias is
    3 to 1 toward `some`, so a body is usually present. -/
def genOptExpr [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy) (pctx : PolyOpCtx := []) : G (Option LExpr') :=
  biasedOptionGen (3 / 4) (genLExpr fctx octx pctx tvars [] depth τ)

-- ── The variables a function's expressions read ─────────────────────────

/-- Reads the signature of the formal parameters as a `FVarCtx`, so that a generated expression can
    refer to an input of the function by its name. -/
def inputsAsFVarCtx (inputs : ListMap (Identifier Unit) LMonoTy) : FVarCtx :=
  inputs.toList.map (fun (id, mty) => (id.name, mty))

/-- The ambient variables of `fctx` that no formal of `inputs` shadows and whose types are over
    `typeArgs`. -/
def ambientFctx (fctx : FVarCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (typeArgs : List TyIdentifier) : FVarCtx :=
  fctx.filter (fun p =>
    !inputs.keys.contains ⟨p.1, ()⟩ && (LMonoTy.freeVars p.2).all typeArgs.contains)

/-- The variables a function's expressions draw on: the formals, then `ambientFctx`. -/
def funcFctx (fctx : FVarCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (typeArgs : List TyIdentifier) : FVarCtx :=
  inputsAsFVarCtx inputs ++ ambientFctx fctx inputs typeArgs

-- ── The generator for a precondition ────────────────────────────────────

/-- Makes an expression of the type `bool` that *always* mentions a formal parameter of the function.
    It picks a formal parameter `(x, τ)`, and it then builds `x == e`, where it made `e` at the type
    `τ` of that parameter over the formals and `ambient`.

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
    (depth : Nat) (hne : inputs.toList ≠ []) (pctx : PolyOpCtx := []) (ambient : FVarCtx := []) :
    G LExpr' := do
  let (x, τ) ← elements inputs.toList hne
  let e ← genLExpr (inputsAsFVarCtx inputs ++ ambient) octx pctx tvars [] depth τ
  pure (.eq () (.fvar () x (some τ)) e)

/-- Makes a precondition of the type `bool`, which is a `requires` clause, over the formal
    parameters and the variables of `ambient`.

    The bias is 3 to 1 toward a clause that mentions a formal parameter, which
    `genInputMentioningPrecond` builds, over a plain draw from `genLExpr` at `.bool`. A function
    with no formal parameter uses the plain draw.

    The code threads `octx` through without a change, so a precondition can itself call a *partial*
    operator, such as `Int.SafeDiv`, when the caller gives one. -/
def genPrecondition [Gen G] (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx := []) (ambient : FVarCtx := []) :
    G (Strata.DL.Util.FuncPrecondition LExpr' Unit) := do
  let e ← (if hne : inputs.toList ≠ [] then
      frequency
        [ (3, fun () => genInputMentioningPrecond octx inputs tvars depth hne pctx ambient),
          (1, fun () =>
            genLExpr (inputsAsFVarCtx inputs ++ ambient) octx pctx tvars [] depth .bool) ]
        (by show 0 < 3 + 1; omega)
    else
      genLExpr (inputsAsFVarCtx inputs ++ ambient) octx pctx tvars [] depth .bool)
  pure { expr := e, md := () }

/-- The most preconditions, and the most axioms, that a generated function has. -/
def maxFuncClauses : Nat := 2

/-- The `preconditions` field of a generated function: at most `maxFuncClauses` clauses from
    `genPrecondition`. -/
def genPreconditions [Gen G] (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx := []) (ambient : FVarCtx := []) :
    G (List (Strata.DL.Util.FuncPrecondition LExpr' Unit)) :=
  listOfMaxLength maxFuncClauses (genPrecondition octx inputs tvars depth pctx ambient)

-- ── The generators for the flags, the measure and the attributes ───────

/-- Draws a flag that is `true` one time in eight. -/
def genRareFlag [Gen G] : G Bool :=
  frequency [(1, fun () => pure true), (7, fun () => pure false)] (by simp)

/-- Whether `m` may be the measure of a function with formals `inputs`: a bare variable must be a
    formal. -/
def measureOnFormal (inputs : ListMap (Identifier Unit) LMonoTy) (m : LExpr') : Bool :=
  match m with
  | .fvar _ x _ => inputs.keys.contains x
  | _ => true

/-- Whether `ty` is a datatype of `dts`, applied to any arguments. -/
def isDatatypeIn (dts : List (String × Nat)) : LMonoTy → Bool
  | .tcons n _ => dts.any (·.1 == n)
  | _ => false

/-- The formals of `inputs` whose types are datatypes of `dts`. -/
def datatypeFormals (dts : List (String × Nat)) (inputs : ListMap (Identifier Unit) LMonoTy) :
    List (Identifier Unit × LMonoTy) :=
  inputs.toList.filter (fun p => isDatatypeIn dts p.2)

/-- Makes an optional `int` measure whose bare variable, if it is one, is a formal. -/
def genIntMeasure [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (pctx : PolyOpCtx) (inputs : ListMap (Identifier Unit) LMonoTy) :
    G (Option LExpr') :=
  (fun m => m.filter (measureOnFormal inputs)) <$> genOptExpr fctx octx tvars depth .int pctx

/-- Makes an optional measure: one from `genIntMeasure`, or, one time in four when there is one, a
    formal whose type is a datatype of `dts`. -/
def genMeasure [Gen G] (dts : List (String × Nat)) (fctx : FVarCtx) (octx : OpCtx)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) : G (Option LExpr') :=
  if h : datatypeFormals dts inputs ≠ [] then
    frequency
      [ (3, fun () => genIntMeasure fctx octx tvars depth pctx inputs),
        (1, fun () => (fun p => some (.fvar () p.1 (some p.2))) <$>
          elements (datatypeFormals dts inputs) h) ]
      (by simp)
  else
    genIntMeasure fctx octx tvars depth pctx inputs

/-- The parameter index that a function attribute names, if any. -/
def attrParamIdx : Strata.DL.Util.FuncAttr → Option Nat
  | .inlineIfConstr i | .evalIfConstr i | .evalIfValue i => some i
  | _ => none

/-- Makes one function attribute whose parameter index, if any, is at most `depth`. -/
def genFuncAttr [Gen G] (depth : Nat) : G Strata.DL.Util.FuncAttr := do
  let i ← elements (List.range (depth + 1)) (by simp)
  elements [.inline, .inlineIfConstr i, .evalIfConstr i, .evalIfValue i, .inlineIfAllValues]
    (by simp)

-- ── The filters that keep a generated function well typed ──────────────

/-- The operators of `octx` whose types mention only type variables of `tvars`. -/
def opsOver (tvars : List TyIdentifier) (octx : OpCtx) : OpCtx :=
  OpCtx.ofList (octx.ops.filter (fun p => (LMonoTy.freeVars p.2).all tvars.contains))

/-- An operator is in `opsOver tvars octx` exactly when it is an operator of `octx` whose type
    mentions only type variables of `tvars`. -/
theorem mem_opsOver_iff {tvars : List TyIdentifier} {octx : OpCtx} {p : String × LMonoTy} :
    p ∈ (opsOver tvars octx).ops ↔ p ∈ octx.ops ∧ ∀ v ∈ LMonoTy.freeVars p.2, v ∈ tvars := by
  simp only [opsOver, OpCtx.ops_ofList, List.mem_filter, List.all_eq_true, List.contains_iff_mem]

-- ── The main generator for a function ───────────────────────────────────

/-- The function with the name and signature of `f` and no other part. -/
def funcStub (f : Function) : Function :=
  { name := f.name, typeArgs := f.typeArgs, inputs := f.inputs, output := f.output }

/-- Makes a function named `name` with only a signature: type arguments with no duplicate, each
    mentioned by the signature; inputs with distinct keys whose types `genInputTy dts` draws over
    the type arguments, none of whose names `avoid` flags; and an output over the type arguments. -/
def genFuncSig [Gen G] (name : String) (depth : Nat) (avoid : String → Bool)
    (dts : List (String × Nat)) : G Function := do
  let sigTypeArgs ← genTypeArgs depth
  let rawInputs ← genInputs (genInputTy dts sigTypeArgs depth) depth
  let inputs : ListMap (Identifier Unit) LMonoTy := rawInputs.filter (fun p => !avoid p.1.name)
  let output ← genLMonoTy sigTypeArgs depth
  let typeArgs := sigTypeArgs.filter
    (fun a => (LMonoTy.freeVars (LMonoTy.mkArrow' output inputs.values)).contains a)
  pure { name := ⟨name, ()⟩, typeArgs := typeArgs, inputs := inputs, output := output }

/-- Makes a function with the name and signature of `sig`, an optional body, preconditions,
    axioms, attributes and lemma names, and a recursion flag from `genRecursive` that allows a
    measure from `genMeasure`. -/
def genFuncParts [Gen G] (genRecursive : G Bool) (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (pctx : PolyOpCtx) (dts : List (String × Nat)) (sig : Function) : G Function := do
  let exprFctx := funcFctx fctx sig.inputs sig.typeArgs
  let exprOctx := opsOver sig.typeArgs octx
  let isConstr ← genRareFlag
  let body ← (if isConstr then pure none
    else genOptExpr exprFctx exprOctx sig.typeArgs depth sig.output pctx)
  let preconditions ← genPreconditions exprOctx sig.inputs sig.typeArgs depth pctx
    (ambientFctx fctx sig.inputs sig.typeArgs)
  let axioms ← listOfMaxLength maxFuncClauses
    (genLExpr exprFctx exprOctx pctx sig.typeArgs [] depth .bool)
  let isRecursive ← genRecursive
  let measure ← (if isRecursive then
      genMeasure dts exprFctx exprOctx sig.typeArgs depth pctx sig.inputs
    else pure none)
  let attr ← listOfMaxLength depth (genFuncAttr depth)
  let lemmas ← genNameList depth
  pure {
    name := sig.name,
    typeArgs := sig.typeArgs,
    isConstr := isConstr,
    isRecursive := isRecursive,
    inputs := sig.inputs,
    output := sig.output,
    body := body,
    attr := attr.toArray,
    axioms := axioms,
    preconditions := preconditions,
    measure := measure,
    lemmas := lemmas
  }

/-- Makes a well-typed `Function`, which is an `LFunc CoreLParams`. It satisfies `FuncWellTyped`
    in every context whose functions and variable scopes agree with the contexts it reads, as
    `genFunction_sound` states.

    The generator makes these parts:
    - `typeArgs`: names for the type variables, with no duplicate. A name that the signature
      does not mention is dropped after the signature is drawn;
    - `inputs`: a signature whose keys hold no duplicate, whose types are over the type arguments
      and may be datatypes of `dts`, and whose names `avoid` does not flag;
    - `output`: a type over the type arguments;
    - `isConstr`: a rare flag; a constructor has no body;
    - `body`: an optional expression of the type `output`;
    - `preconditions` and `axioms`: at most `maxFuncClauses` expressions of the type `bool` each;
    - `isRecursive`: a rare flag; a recursive function has an optional measure from `genMeasure`;
    - `attr`: at most `depth` attributes, with parameter indices at most `depth`;
    - `lemmas`: a list of names.

    Every expression draws on the formals and on the ambient variables of `fctx` that no formal
    shadows and whose types are over the type arguments (`funcFctx`), on the operators whose types
    are over the type arguments (`opsOver`), and on every scheme of `pctx`. -/
def genFunction [Gen G] (fctx : FVarCtx) (octx : OpCtx) (depth : Nat)
    (pctx : PolyOpCtx := []) (avoid : String → Bool := fun _ => false)
    (dts : List (String × Nat) := []) : G Function := do
  let name ← genIdentName
  let sig ← genFuncSig name depth avoid dts
  genFuncParts genRareFlag fctx octx depth pctx dts sig
