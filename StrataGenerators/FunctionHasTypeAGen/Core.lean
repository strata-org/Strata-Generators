import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import BasaltExamples.ArbString.Def
import Strata.Languages.Core.Function
import StrataGenerators.HasTypeAGen.Core
import Std.Data.HashSet

open Lambda RandomChoice Core Imperative ArbString Std

/-!
# Core generator definitions for well-typed Strata Core `Function`s

This file contains the canonical definition of `genFunction`, a generator of
well-typed Strata Core functions (`Function = LFunc CoreLParams`) satisfying the
`FuncHasTypeA` relation of `Strata.Languages.Core.FunctionTypeSpec`.

The generator reuses `genLExpr` from `HasTypeAGen/Core.lean` to generate
well-typed expressions for the function body and (optional) termination measure,
and `genLMonoTy` to generate the input/output types.

A generated `Function` is well-typed in the sense of `FuncHasTypeA` because:
1. Its `typeArgs` and its `inputs.keys` are produced via `List.dedup`, hence
   `Nodup`.
2. Its input and output types are produced by `genLMonoTy typeArgs`, hence every
   free type variable in the signature is drawn from `typeArgs`
   (`noUndeclaredVars`).
3. Its body (when present) is produced by `genLExpr ... output`, hence has the
   declared return type. Note the annotated typing spec `instHasTypeA` *ignores*
   the ambient typing context, so `bodyTyped` reduces to `HasTypeA [] body output`.
4. Its measure (when present) is produced by `genLExpr ... .int`, hence has type
   `int`.

`FuncHasTypeA` says nothing about `preconditions`, so the optional `requires`
clause `genFunction` also emits (see `genPreconditions`) is invisible to the
soundness proof. It is generated over the *formals only* — `FuncWF`'s
`precond_freevars` field demands precondition free variables ⊆ input names — and
it is what makes a generated function *partial*, hence what makes Strata's
`PrecondElim` precondition-stripping path reachable from generated input.
-/

-- ── Name / type-argument generation ─────────────────────────────────────

/-- The 52 ASCII letters `A-Z` followed by `a-z`. -/
def alphaChars : List Char :=
  (List.range 26).map (fun n => Char.ofNat ('A'.toNat + n)) ++
  (List.range 26).map (fun n => Char.ofNat ('a'.toNat + n))

/-- Valid first characters of a Core identifier, restricted to letters plus
    `_`/`$`. This is a subset of Core's `strataIsIdFirst` (`isAlpha || '_' ||
    '$'`), so every character here is legal in leading position. -/
def startChars : List Char :=
  alphaChars ++ ['_', '$']

def genStartChar [Gen G] : G Char :=
  elements startChars (by decide)

def remainingChars : List Char :=
  startChars ++ "0123456789".toList ++ ['\'', '.', '?', '!', '$', '@']

def genRemainingChar [Gen G] : G Char :=
  elements remainingChars (by decide)

/-- The Strata Core reserved keywords as a plain list — the *source of truth*.
    These are the bare words the Core lexer tokenizes as keywords, so the parser
    rejects them in identifier position (e.g. `function if () : int;` fails with
    "unexpected token 'if'").

    Compiled from `Strata/Languages/Core/DDMTransform/Grammar.lean`:
    - built-in type names (`type bool;` … and the `Map`/`Sequence`/`Type` cons),
    - structured-statement / declaration leading words (`if`/`then`/`else`,
      `forall`/`exists`, `var`/`assume`/`assert`/`cover`/`while`, `spec`/
      `requires`/`ensures`/`free`, `procedure`/`function`/`type`/`const`/
      `axiom`/`distinct`/`datatype`, `goto`/`branch`/`return`, `inline`/
      `decreases`/`invariant`/`out`/`inout`/`old`/`have`),
    - boolean literals (`true`/`false`).

    The list is retained (rather than only the `HashSet` below) so `decide`/`simp`
    can evaluate membership in proofs; runtime membership goes through the
    `HashSet` via `reservedKeywords`. -/
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

/-- The reserved keywords as a `HashSet` for efficient membership testing in the
    generator (`isReservedKeyword` runs on every generated name). Built from
    `reservedKeywordsList`; `HashSet.contains_ofList` bridges the two so proofs
    can still reason over the concrete list via `decide`. -/
def reservedKeywords : Std.HashSet String := Std.HashSet.ofList reservedKeywordsList

/-- `true` iff `s` is a reserved Strata Core keyword. Uses the `HashSet` for an
    O(1) expected-time lookup (see `isReservedKeyword_eq_list_contains` for the
    bridge to `reservedKeywordsList` used in proofs). -/
def isReservedKeyword (s : String) : Bool := reservedKeywords.contains s

/-- Membership via the `HashSet` agrees with membership in the source list. This
    is the bridge that lets proofs reason over the concrete `reservedKeywordsList`
    (which `decide` can evaluate) while the generator uses the efficient
    `HashSet`. -/
theorem isReservedKeyword_eq_list_contains (s : String) :
    isReservedKeyword s = reservedKeywordsList.contains s := by
  unfold isReservedKeyword reservedKeywords
  exact Std.HashSet.contains_ofList

/-- Deterministically map a reserved keyword to a fresh non-keyword identifier by
    appending `_`. No reserved keyword ends in `_`, and appending `_` to a legal
    identifier yields a legal identifier (`_ ∈ strataIsIdRest`), so `dodgeKeyword
    s` is always a legal, non-keyword identifier — and it is the identity on names
    that were not keywords to begin with. -/
def dodgeKeyword (s : String) : String :=
  if isReservedKeyword s then s ++ "_" else s

/-- Generate a valid Core identifier *by construction*: a first character from
    `startChars` (letters plus `_`/`$`, all in `strataIsIdFirst`), then a
    possibly-empty run of `remainingChars` (all in `strataIsIdRest`), finally
    mapping any reserved keyword to a non-keyword via `dodgeKeyword`. Every
    output is therefore a legal, non-keyword Core identifier — non-empty and
    letter-initial (so it lexes as an `Ident`, never a `Num`), and never a
    reserved word the parser would reject in identifier position.

    This is the name source for `genFunction`. Note `remainingChars` includes
    `.`, which is legal in a bare identifier but collides with binder /
    qualified-name syntax under maximal munch — so an output containing `.` may
    fail to round-trip. That is intentional: because the name is legal by
    construction, such a failure is a genuine Core printer/parser bug to report,
    not a generator artifact. For characters that are only representable via the
    pipe-delimited form (`|`, `\`), see `genQuotedName`. -/
def genIdentName [Gen G] : G String := do
  let x ← genStartChar
  let xs ← listOf genRemainingChar
  return dodgeKeyword (String.ofList (x :: xs))

-- ── Adversarial identifier generation (round-trip fuzzing) ───────────────

/-- Alphabet for `genQuotedName`. Beyond the bare-legal characters this adds the
    special characters that force interesting formatter/parser paths:
    - `'` — accepted bare by the lexer but pipe-quoted on output;
    - `.` — accepted bare by both, but collides with binder / qualified-name
      syntax under maximal munch;
    - `| \` — *not* bare-legal in any position; only representable via the
      SMT-LIB-style pipe-delimited form (`|…|`) with `\|`/`\\` escaping. -/
def quotedNameChars : List Char :=
  remainingChars ++ ['|', '\\']

def genQuotedNameChar [Gen G] : G Char :=
  elements quotedNameChars (by decide)

/-- Generate an adversarial-but-**legal** identifier: a first character from
    `startChars` (letters plus `_`/`$`, all in `strataIsIdFirst`), followed by a
    possibly-empty run of `quotedNameChars` (special characters `. ' ? ! $ @` and
    the pipe-only `| \`) in the *interior*.

    Constraining the first character to `strataIsIdFirst` is what keeps every
    output a *legal Core identifier*: a leading `@`/`?`/digit/`|` is not a valid
    identifier in any position (bare or pipe-quoted in a type-variable slot), so
    without this restriction the probe would emit illegal names and its round-trip
    "failures" would be generator artifacts, not Strata bugs. With it, a failure
    is a genuine Core printer/parser faithfulness bug — the same guarantee
    `genIdentName` gives — while still exercising the pipe-quote / escape path
    (`escapePipeIdent` ↔ `parsePipeDelimitedIdent`) and bare-render hazards
    (`.` munch collisions) via interior special characters.

    NOTE: kept separate from `genIdentName` on purpose — it does not feed
    `genFunction` or the soundness/completeness proofs; drive it through a
    dedicated single-identifier round-trip harness. The leading character also
    guarantees a non-empty name (so `listOf` yielding `[]` for the tail is fine). -/
def genQuotedName [Gen G] : G String := do
  let c ← genStartChar
  let cs ← listOf genQuotedNameChar
  return String.ofList (c :: cs)

/-- Generate a random list of alphanumeric names of length ≤ `depth`.

    Defined via the `listOfMaxLength` combinator (vendored from Basalt); its
    support is characterized by `SetGen.mem_support_listOfMaxLength_iff`. -/
def genNameList [Gen G] (depth : Nat) : G (List String) :=
  listOfMaxLength depth genIdentName

/-- Generate a list of *distinct* type-argument names. Distinctness is
    guaranteed by `List.dedup`. -/
def genTypeArgs [Gen G] (depth : Nat) : G (List TyIdentifier) :=
  List.dedup <$> genNameList depth

/-- Generate a list of *distinct* input identifiers. Distinctness of the
    underlying names (and hence of the identifiers, since `⟨·, ()⟩` is injective)
    is guaranteed by `List.dedup`. -/
def genIdents [Gen G] (depth : Nat) : G (List (Identifier Unit)) :=
  (fun names => (names.map (fun s => (⟨s, ()⟩ : Identifier Unit))).dedup) <$> genNameList depth

-- ── Input signature generation ──────────────────────────────────────────

/-- Generate the parameter signature: a `ListMap` from distinct
    identifiers to monotypes, where every type is drawn from `genLMonoTy tvars`
    (so its free type variables all lie in `tvars`). -/
def genInputs [Gen G] (tvars : List TyIdentifier) (depth : Nat) :
    G (ListMap (Identifier Unit) LMonoTy) := do
  let idents ← genIdents depth
  idents.mapM (fun x => do
    let ty ← genLMonoTy tvars depth
    pure (x, ty))

-- ── Optional body / measure generation ──────────────────────────────────

/-- Generate an optional well-typed expression of type `τ`: either `none`, or
    `some e` for `e` generated by `genLExpr` at type `τ` (empty bvar context,
    empty polymorphic-op context). Biased 3:1 toward `some` (≈75%), so measures
    and bodies are usually present rather than absent. -/
def genOptExpr [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (τ : LMonoTy) (pctx : PolyOpCtx := []) : G (Option LExpr') :=
  biasedOptionGen (3 / 4) (genLExpr fctx octx pctx tvars [] depth τ)

-- ── Precondition generation ─────────────────────────────────────────────

/-- Reinterpret a formal-parameter signature as a `FVarCtx`, so that a generated
    expression can refer to the function's own inputs by name.

    This is the *only* free-variable context a precondition may be generated in.
    `FuncWF.precond_freevars` (`Strata/DL/Util/Func.lean`) requires the free
    variables of every precondition to be a subset of the formal-parameter names,
    exactly as `body_freevars` does for the body — so handing `genLExpr` the
    ambient `fctx` here would produce ill-formed functions rather than merely
    uninteresting ones. -/
def inputsAsFVarCtx (inputs : ListMap (Identifier Unit) LMonoTy) : FVarCtx :=
  inputs.toList.map (fun (id, mty) => (id.name, mty))

/-- Generate a `bool`-typed expression that is *guaranteed* to mention one of the
    function's formals: pick a formal `(x, τ)`, then build `x == e` for `e`
    generated at that formal's own type `τ`.

    This is the mechanism behind the "prefer preconditions that mention the
    inputs" bias. Going through `genLExpr` at `.bool` alone is not enough in
    practice: `genLExprBase`'s `bool` rules can only reach a *variable* leaf via
    `fvarsOfType fctx .bool`, so a formal is reachable only when it is itself
    `bool`-typed — empirically ~2% of generated signatures. Equating a formal of
    *any* type against a same-typed expression sidesteps that: the equality node
    is `bool` whatever `τ` is, so every formal becomes usable.

    Requires a proof that `inputs` is non-empty, which is what makes the `elements`
    pick total; `genPrecondition` supplies it from a `dif`. -/
def genInputMentioningPrecond [Gen G] (octx : OpCtx)
    (inputs : ListMap (Identifier Unit) LMonoTy) (tvars : List TyIdentifier)
    (depth : Nat) (hne : inputs.toList ≠ []) (pctx : PolyOpCtx := []) : G LExpr' := do
  let (x, τ) ← elements inputs.toList hne
  let e ← genLExpr (inputsAsFVarCtx inputs) octx pctx tvars [] depth τ
  pure (.eq () (.fvar () x (some τ)) e)

/-- Generate an optional `bool`-typed precondition (a `requires` clause) over the
    function's own formals, `some` with probability 1/2 via `optionGen`.

    Biased 3:1 toward clauses that mention a formal (`genInputMentioningPrecond`)
    over a plain `genLExpr` draw at `.bool`, per the "prefer expressions that
    mention the inputs" requirement. Both branches generate in the free-variable
    context `inputsAsFVarCtx inputs`, so *every* free variable is a formal either
    way — the bias is about how often a variable appears at all, not about
    well-formedness. A function with no formals has nothing to mention, so it
    falls back to the unbiased draw (a closed boolean expression over `octx`).

    The `octx` is threaded through unchanged, so a precondition can itself call a
    *partial* operator (e.g. `Int.SafeDiv`) when the caller supplies one — which is
    what makes PrecondElim's precondition-stripping path reachable from generated
    input. -/
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

/-- The `preconditions` field for a generated function: the singleton list
    `[p]` when `genPrecondition` yields `some p`, and `[]` otherwise.

    A list (rather than an `Option`) is what the field wants, and one clause is
    enough to make every precondition-sensitive code path non-vacuous; keeping it
    at most one also keeps `genFunction_complete`'s reachability obligation a
    single-expression side condition. -/
def genPreconditions [Gen G] (octx : OpCtx) (inputs : ListMap (Identifier Unit) LMonoTy)
    (tvars : List TyIdentifier) (depth : Nat) (pctx : PolyOpCtx := []) :
    G (List (Strata.DL.Util.FuncPrecondition LExpr' Unit)) :=
  (fun o => o.toList) <$> genPrecondition octx inputs tvars depth pctx

-- ── Main function generator ─────────────────────────────────────────────

/-- Generate a well-typed `Function` (i.e. `LFunc CoreLParams`).

    The generated function satisfies `FuncHasTypeA C Γ` for any ambient context
    `Γ` (see `genFunction_sound`).

    Components generated:
    - `typeArgs` — a `Nodup` list of type-variable names,
    - `inputs`   — a `Nodup`-keyed signature with types over `typeArgs`,
    - `output`   — a type over `typeArgs`,
    - `body`     — an optional expression of type `output`,
    - `measure`  — an optional expression of type `int`,
    - `preconditions` — at most one `bool` clause over the *formals*
      (`genPreconditions`; `some` half the time, and biased toward clauses that
      actually mention a formal).

    Preconditions are unconstrained by `FuncHasType'` — it has no precondition
    field — so generating them cannot affect `genFunction_sound`. They matter
    downstream: a function with a non-empty `preconditions` list is *partial*, so
    this is what makes Strata's `PrecondElim` precondition-stripping path (and the
    `preconditionsStripped` property) reachable from generated input rather than
    only from hand-built reproducers.

    The remaining fields not constrained by the typing spec (`isConstr`,
    `isRecursive`, `attr`, `concreteEval`, `axioms`) are left at their defaults. -/
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
