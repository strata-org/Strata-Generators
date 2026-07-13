# Catalog of Strata Core pretty-print/parse round-trip failures

This document catalogs the distinct classes of **round-trip failure** surfaced by
the property-based test harnesses (`PlausibleTestMain.lean` / `make test` and
`TycheMain.lean` / `make tyche`). The round-trip property is:

> `format → parse → re-format` should be a fixed point — embedding a generated
> `Function` in a one-decl `Program`, formatting via Strata's own
> `Core.formatProgram`, re-parsing via the Core DDM dialect, and re-formatting
> should reproduce the original string.

Both the round-trip check **and** the displayed `representation` now go through
Strata's real printer (`Core.formatProgram` / `formatFunc`, in
`StrataGenerators/FunctionHasTypeAGen/Roundtrip.lean`). So every example below is
the *actual* output of the Strata pretty-printer, verbatim from `tyche_output.jsonl`
(the harness shrinks each counterexample to a minimal witness). Line/column
references point into the [Strata repo](../../Strata).

**Important framing.** The name generators (`genIdentName`, `genQuotedName` in
`StrataGenerators/FunctionHasTypeAGen/Core.lean`) produce only *legal* Core
identifiers by construction, and `genLMonoTy` produces only *well-formed* types.
So a failure to round-trip is a genuine printer/parser faithfulness bug in Strata
Core, **not** a generator artifact: the printer emits something its own parser
cannot read back (or reads back differently).

> **Correction vs. earlier drafts.** An earlier version of this catalog claimed
> the printer emits angle-bracket type syntax (`Map<K, V>`, `Sequence<T>`). That
> described a *display-only* hand-rolled printer that has since been removed. The
> real `Core.formatProgram` uses **juxtaposition** (`Map K V`, `Sequence T`), as
> the grammar dictates. The dominant bug is therefore not "angle brackets" — it
> is **missing parentheses around compound type arguments** (Class 1 below).

## Invoking the Strata parser / printer directly (for bug reports)

Every failure below can be triggered by calling two Strata entry points directly —
no generator or test harness required. Use these when writing up GitHub issues.

**Printer** — `Core.formatProgram : Core.Program → Std.Format`
(`Strata/Languages/Core/DDMTransform/ASTtoCST.lean:274`). Wrap an expression in a
one-decl program and format it. (The generic `Std.format` on a `Core.Program`
dispatches to the same function via the `ToFormat` instance in `FormatCore.lean`,
so `(Std.format prog).pretty` and `(Core.formatProgram prog).pretty` are
interchangeable.)

**Parser** — the DDM pipeline used by the harness, wrapped as `parseCoreProgram` /
`parseCoreProgramErr` in `StrataGenerators/FunctionHasTypeAGen/Roundtrip.lean:52,66`.
The underlying Strata calls are:

```lean
-- parse a Core source string → CST → Core.Program (with translation errors)
let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
let ictx := StrataDDM.Parser.stringInputContext ⟨"repro"⟩ src
let sp   ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" ictx  -- Elab.lean:515
let (ast, errs) := TransM.run Inhabited.default (Strata.translateProgram sp)   -- Translate.lean:2249
```

A **round-trip** is then `Core.formatProgram ∘ parse ∘ Core.formatProgram`; a bug is
either a parse/translate failure on the printer's output, or a *mismatch* (both
parse, but the two `Core.formatProgram` strings differ). Each class below lists a
**Reproduce** recipe: the minimal source string and/or the AST expression to feed
these two functions, and what you should observe. All recipes were verified by
running `parseCoreProgramErr` and `Core.formatProgram` directly.

## Summary of the run

From a representative `make tyche` run (1000 samples on the round-trip panel):

- **466 failed / 534 passed** on the full-function round-trip.
- **25 failed / 975 passed** on the special-character identifier round-trip.
- Failures group (via the `error_kind` feature) into the classes below.

| Class | count (approx) | Kind | Root cause |
|---|---|---|---|
| 1. Missing parens around compound type arguments | ~428 | parse-fail (366) + mismatch (62) | printer doesn't parenthesize an arrow/compound used as a type argument; application binds tighter than `->` |
| 2. `<s` operator / type-arg bracket collision | ~19 | parse-failure | `<s` token swallows `<` + an `s`-initial type-arg |
| 3. Body expression not re-typecheckable | ~8 | parse-failure | printed body fails the parser's type check (unapplied ops, non-terminating reals) |
| 4. Dot-in-identifier | ~22 | parse-failure | `.` is legal in idents but reparses as a qualified name |
| 5. Type-variable use-site not quoted | ~13 | parse-failure | printer emits a `\|`/`\`-containing type var bare at its use site |
| ⚠ Generator artifact | 1–2 | (false positive) | `genIdentName` can produce reserved keywords like `if` |

(491 total failures across both panels. Class 1 dominates at ~87%.
The 1–2 generator artifacts are *not* Strata bugs; see the note at the end.)

---

## Class 1 — Missing parentheses around compound type arguments (dominant)

This is one bug with two surface manifestations: a **parse failure** (the
mis-grouped string is rejected) or a **mismatch** (it parses but re-formats to a
different string). Both stem from the printer omitting parentheses.

**Parse-failure examples** (`tyche_output.jsonl`):

```
function f () : Map int -> bool regex;
    → Parse errors: 1:16: Map expects 2 arguments.  1:32: Unexpected argument to bool.

function f (V : Map bool -> bool bool) : string;
    → Parse errors: 1:16: Map expects 2 arguments.  1:33: Unexpected argument to bool.

function f (Z : Map int Map int int -> string) : int;
    → Parse errors: 1:24: Map expects 2 arguments.  1:24: Unexpected argument to Map.
```

**Mismatch examples** (parse OK, but `format → parse → re-format` is not a fixed
point — `parsed=yes, roundtripped=no`, empty `status_reason`). Minimal shrunk
witnesses from `tyche_output.jsonl`:

```
function C () : Sequence (Map int int -> bool);
function f () : Sequence (Sequence int -> int);
function f () : Map int (Sequence int -> bool);
function f<F> () : Map F (Map F F -> bool);
```

**Root cause — the printer does not parenthesize an arrow (or other compound)
type when it appears as an argument to another type constructor.**

Consider the generated type `Map int (int -> int)` (a `Map` from `int` to the
function type `int -> int`). Strata's type converter renders it, child by child,
as `Map int int -> int` **without** parenthesizing the arrow-typed value. But in
the grammar, type application binds *tighter* than `->`:

- `TypeApp` (juxtaposition) is **prec 40** — `StrataDDM/StrataDDM/BuiltinDialects/Init.lean:119-126`
- `TypeArrow` (`->`) is **prec 30** — `StrataDDM/StrataDDM/BuiltinDialects/Init.lean:110-117`

So the parser reads `Map int int -> int` as `(Map int int) -> int`: it greedily
applies `Map` to both `int int` by juxtaposition *before* the `->`. The correct
output would have been `Map int (int -> int)`.

**Confirmed directly** (standalone parse probes on the real printer/parser):

```
Map int (int -> int)   →  PARSES            (the correct, parenthesized form)
Map int int -> int     →  FAILS             (what the printer actually emits)
Map (int -> int) int   →  PARSES
```

**Interpreting the error messages.** They are the parser's downstream reaction to
the mis-grouping, not the root cause:

- `Map expects 2 arguments` — `Map` is arity-2 (`Grammar.lean:53`), but the
  greedy juxtaposition applied it to the wrong number/shape of arguments.
- `Unexpected argument to int` / `... to bool` — having consumed `Map int`, the
  parser sees a *further* juxtaposed token and tries to apply the base type
  `int`/`bool` (arity 0) to an argument. Base types take no arguments, so the
  extra token is "unexpected." (Column points at that trailing token.)

**Where in the code.** The type converter recurses into children without tracking
whether a child needs parenthesization for its surrounding context:

- `Strata/Languages/Core/DDMTransform/FormatCore.lean:220-223` — `Map [k,v]`
- `Strata/Languages/Core/DDMTransform/FormatCore.lean:224-226` — `Sequence [e]`
- `Strata/Languages/Core/DDMTransform/FormatCore.lean:227-230` — `arrow [a,b]`

The grammar it must satisfy:

- `Strata/Languages/Core/DDMTransform/Grammar.lean:53-54` — `type Map (dom, range);`, `type Sequence (elem);`

**One fix addresses the whole class**: parenthesize a type argument whenever it is
an arrow (prec 30) — or, more conservatively, any non-atomic type — before
splicing it into a juxtaposition position.

**Why both parse-failures and mismatches arise from the same bug.** Consider the
minimal case `Sequence (Map int int -> bool)`:

- The *correct* form `Sequence (Map int int -> bool)` **parses** (the parser
  accepts explicit parentheses) but `Core.formatProgram` reprints it as
  `Sequence Map int int -> bool` (parens dropped) — so `s1 ≠ s2`, a **mismatch**.
- The *printer's* form `Sequence Map int int -> bool` **parse-fails** outright
  (the parser mis-groups it).

So the printer always loses the parens, and what you see in the Tyche panel
depends on the *shrinker*: if the shrinker's final `representation` is the
parenthesized first-print, you see a mismatch; if it's the un-parenthesized
reprint, you see a parse-failure. Both are the same underlying bug.

This class is independent of names and fires for essentially any signature
containing a `Map`, `Sequence`, or arrow nested inside another type constructor.

**Reproduce.** Both manifestations, verified directly:

```lean
-- Mismatch: the correct source parses, but Core.formatProgram drops the parens.
parseCoreProgram "function C () : Sequence (Map int int -> bool);"
  -- parses OK; Core.formatProgram of the result yields
  --   "function C () : Sequence Map int int -> bool;"   (parens gone ⇒ s1 ≠ s2)

-- Parse-failure: feed that printer output straight back in.
parseCoreProgramErr "function C () : Sequence Map int int -> bool;"
  -- .error "… 1:25: Map expects 2 arguments.  1:29: Unexpected argument to Sequence."
```

Minimal one-constructor variant: `Map int (int -> int)` parses but reformats to the
non-fixed-point `Map int int -> int`; `Map (int -> int) int` parses and is stable.

---

## Class 2 — `<s` operator / type-argument bracket collision

**Examples** (`tyche_output.jsonl`):

```
function f<sP> () : int;    → Parse errors: 1:10: unexpected token '<s'; expected Core.Bindings
function f<s> () : bool;    → Parse errors: 1:10: unexpected token '<s'; expected Core.Bindings
```

**Root cause — maximal-munch tokenization of `<s`.** Type arguments print with
`<...>` brackets:

- `Strata/Languages/Core/DDMTransform/Grammar.lean:62` — `op type_args (...) : TypeArgs => "<" args ">";`

and the signed-less-than bitvector operator is the token `<s`:

- `Strata/Languages/Core/DDMTransform/Grammar.lean:187` — `fn bvslt (…) => @[prec(20), leftassoc] a " <s " b;`

When a type-argument name begins with `s` (e.g. `s`, `sP`), the printed `f<sP>` is
lexed as `f` `<s` `P>` — the `<s` operator token is grabbed before `<` can open
the type-argument bracket. The parser then expects bindings after `f` and reports
`unexpected token '<s'; expected Core.Bindings`.

**Confirmed directly**: `function f<s> () : int;` fails, while `function f< s>
() : int;` (space after `<`) parses. So it is specifically `<` immediately
followed by `s`. This affects even the clean `genIdentName`, which readily
produces type-variable names starting with `s`. The special-character identifier
panel shows this as `char_class=plain` failures whose names start with `s`.

Note the space is *not* absorbed into the type-variable name: the lexer treats it
as inter-token whitespace (`StrataDDM/StrataDDM/Parser.lean` — `whitespace` is run
after each token and stored in trailing `SourceInfo`, and an identifier's value
is `mkIdResult`'s `c.extract startPart stopPart`, which spans only id-characters).
So `f< s>` parses with type parameter `s`, not `" s"` — reformatting yields `f<s>`.

**Reproduce.**

```lean
parseCoreProgramErr "function f<s> () : int;"    -- .error "… 1:10: unexpected token '<s'; expected Core.Bindings"
parseCoreProgram    "function f< s> () : int;"   -- parses; Core.formatProgram ⇒ "function f<s> () : int;"
```

---

## Class 3 — Printed function body is not re-typecheckable

These parse structurally but fail during the parser's translation/type-check
phase. Several are really **printer gaps for expression constructs**, surfaced as
a type error.

**Examples** (`tyche_output.jsonl`):

```
function F () : bool -> bool { re.none() }
    (conversion note: "Unsupported construct in lopToExpr: 0-ary op not found: Bool.Not")

function f () : real { 0.0 }
    → Parse errors: 6:0: unexpected token '-'; expected 'function', Core.Block …
    (conversion note: "Unsupported construct in lconstToExpr: unsupported real: 1/3")

function f () : bool { fun __q0 : bool -> regex => fun __q1 : bool => -2 }
    → Parse errors: 2:2: Expression has type bool -> regex -> bool -> int when bool expected.
```

**Root cause — mixed.** The `conversion note`s point at the *printer* side
(`Core.formatProgram` via `lopToExpr` / `lconstToExpr` in `FormatCore.lean`), but
the sub-cases have genuinely different root causes:

- **Unapplied builtin operators** like `Bool.Not` — this is an **inexpressibility
  gap, not a mere missing printer case**. The generated body is the *unapplied*
  operator `Bool.Not`, a well-typed `LExpr.op` of type `bool -> bool`. Note the
  function is declared `: bool -> bool`, so the AST **is** well-typed — the
  operator's type matches the return type; there is no type mismatch. The problem
  is purely surface syntax:

  1. Core's grammar has no production for a bare/unapplied operator. `Bool.Not`
     is declared as the `fn`

     ```
     fn not (b : bool) : bool => "!" b;
     ```

     at `Strata/Languages/Core/DDMTransform/Grammar.lean:87`. The right-hand side
     `"!" b` is the operator's *entire* concrete syntax, and it is a template with
     the argument slot `b` baked in: the surface form is the two tokens `!`
     followed by an expression `b`. In other words, `Bool.Not` only ever appears
     concretely as `!b` — the prefix `!` **must** be immediately followed by some
     boolean expression `b` (e.g. `!x`, `!#true`, `!(f y)`).

     There is no grammar production that yields the bare token `!` on its own, and
     none that names the operator (there is no surface form spelled `Bool.Not`).
     So the operator can be *written* only in fully-applied position; it has no
     concrete syntax as a standalone `bool -> bool` value. This is exactly the
     mismatch: at the AST level `Bool.Not` is a first-class value of type
     `bool -> bool` (an `LExpr.op` that can sit anywhere a `bool -> bool` is
     expected, including as a whole function body), but the concrete grammar can
     only express it *saturated* — applied to its one argument. There is no way to
     write down "the `!` function itself."
  2. The printer renders a bare `.op` node by calling `lopToExpr name []` with an
     **empty** argument list (`FormatCore.lean:576`).
  3. `lopToExpr` dispatches purely on `args.length` (`FormatCore.lean:529-534`);
     with `args = []`, `Bool.Not` is routed to `handleZeroaryOps` — even though
     `Bool.Not` *is* handled as a unary op when applied (`handleUnaryOps`,
     `FormatCore.lean:322`, `.bool .Not => .not default arg`).
  4. `handleZeroaryOps` (`FormatCore.lean:290-299`) only knows three regex
     constants (`re.all`/`re.allchar`/`re.none`); `Bool.Not` falls into the `_`
     branch, logs `"0-ary op not found"`, and emits the fallback `re.none()`
     (type `regex`), which then fails to re-typecheck.

  Because no correct printout exists, this is better read as the **generator
  producing a term with no concrete-syntax representation** than as a printer
  defect. A robust fix would eta-expand unapplied operators on print
  (`Bool.Not` → `fun x => !x`); alternatively the generator could avoid emitting
  bare operators at function-value positions.

  **This is one bug, not two.** It is tempting to split this into (a) "unapplied
  `Bool.Not` can't be printed" and (b) "factory operators are printed via special
  notation (`!b`) instead of by name (`Bool.Not`), which breaks round-tripping."
  Direct probing shows (b) is a non-issue and there is only one real defect:

  - **Applied occurrences round-trip cleanly via notation.** The *applied*
    operator `Bool.Not true` — i.e. `LExpr.app (.op ⟨"Bool.Not"⟩) (boolConst true)`
    — prints as `!true`, which re-parses to the same AST. Notation on both the
    print and parse sides is exactly consistent; there is no round-trip failure
    for any *applied* operator. (`!(true)` also parses, normalizing to `!true`.)
  - **The operator has no name-form to fall back to — on either side.** There is
    no concrete syntax spelled `Bool.Not` at all: **neither `Bool.Not true`
    (juxtaposition) nor `Bool.Not(true)` (call form) parses** — both are rejected
    by the parser. So "print by notation instead of by name" is not a *choice* the
    printer makes over an available name-form; the name-form simply does not exist
    in the grammar. The notation `!b` is the operator's *only* surface syntax, and
    it is unavoidably saturated (the `b` slot is mandatory).

  So the notation scheme is not itself a bug (it round-trips whenever the operator
  is applied); the single defect is that the notation-only grammar has **no
  representation for the bare, unapplied operator**, which the *generator* can
  nonetheless construct as a well-typed `bool -> bool` value. That is the whole of
  this failure. See the reproducers below.

- **Non-terminating-decimal real literals** like `1/3` — this one is a **lossy,
  incorrect print (a soundness bug), not just a parse failure**. The exact chain:

  1. `Strata/Languages/Core/DDMTransform/FormatCore.lean:272-277` — `lconstToExpr`
     for a `.realConst r` calls `StrataDDM.Decimal.fromRat r`; on `none` it logs
     `"unsupported real"` and emits `.realLit default ⟨default, default⟩` — i.e. a
     **default `Decimal`** in place of the real value (line 277).
  2. `StrataDDM/StrataDDM/Util/DecimalRat.lean:45-54` — `fromRat` returns `none`
     whenever the denominator has a prime factor other than 2 or 5
     (`isTerminatingDenominator`), so `1/3` (denominator 3) is unrepresentable.
  3. `default : Decimal` is `{ mantissa := 0, exponent := 0 }` (derived `Inhabited`,
     `StrataDDM/StrataDDM/Util/Decimal.lean:16-19`), and `Decimal.toString`
     (`StrataDDM/StrataDDM/Util/Decimal.lean:31-35`) renders mantissa 0 as the
     literal string `"0.0"`.

  So the printer emits `0.0` where the AST held `1/3`: the printed term has a
  **different value** from the original (`0.0 ≠ 1/3`). This is more serious than
  the syntactic round-trip bugs — it silently changes meaning. The
  `unexpected token '-'` parse error in the sample is a *secondary* effect (the
  logged error text lands in the stream); the primary defect is the value
  substitution at `FormatCore.lean:277`.

**Reproduce.** Both sub-cases are *printer-side*, so build the AST expression
directly and format it — no parse step needed to trigger them:

```lean
-- Unapplied Bool.Not: prints the wrong (untypeable) fallback re.none().
-- (Build the one-decl program however is convenient; the operative call is
--  Core.formatProgram on a body holding this bare .op node.)
(.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool)) : Core.Expression.Expr)
  -- Core.formatProgram / Std.format ⇒ "re.none()"
  --   + logged: "Unsupported construct in lopToExpr: 0-ary op not found: Bool.Not"

-- Contrast (NOT a bug): the applied operator round-trips via notation.
(.app () (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool))) (.boolConst () true))
  -- Core.formatProgram / Std.format ⇒ "!true", which re-parses to the same AST.

-- And the name-form does not exist in the grammar at all:
parseCoreProgramErr "function f () : bool { Bool.Not true }"    -- .error (parse fails)
parseCoreProgramErr "function f () : bool { Bool.Not(true) }"   -- .error (parse fails)

-- Non-terminating real: prints 0.0 in place of 1/3 (value corruption).
(.realConst () (1/3 : Rat) : Core.Expression.Expr)
  -- Core.formatProgram / Std.format ⇒ "0.0"
  --   + logged: "Unsupported construct in lconstToExpr: unsupported real: 1/3"
```

These are worth triaging individually; the common thread is printer
incompleteness for certain expression/constant forms rather than a single
localized rule.

> **Fixed shrinker artifact (was mis-reported as a bug).** Earlier runs produced
> apparent Class-3 failures like
> `function L () : int { fun __q0 : c -> int => if true then -1.0 else 5.0 }`,
> where the body is a lambda of type `(c -> int) -> real` but the function is
> declared `: int`. This function is **genuinely ill-typed** (`(c -> int) -> real`
> ≠ `int`), so the parser is correct to reject it — it is *not* a Strata bug.
>
> The cause was the shrinker: `shrinkFunc`'s `shrinkOut` collapses the declared
> `output` toward `int` *without touching the body*, and the old `funcWellFormed`
> only checked type-variable scoping, not body typing. So it let through a
> well-formed-*looking* but ill-typed candidate. `funcWellFormed` now additionally
> requires `LExpr.typeCheck [] body == some output` (and the measure at `int`), so
> the shrinker can no longer manufacture these. Genuine body-side failures that
> survive — e.g. the compound-type reassociation ones where the body's inferred
> type prints identically to the declared type yet differs structurally — are real
> Class 1 manifestations inside the body position, not artifacts.

---

## Class 4 — Dot-in-identifier reparses as a qualified name

Rare in the full-function panel at this sample size, but reliably reproduced by
the special-character identifier panel
(`genFunction: special-character identifier round-trip`, `char_class=dot`).

**Example form**:

```
function f<F.pl>() : F.pl;   → Undeclared type or category F.pl.
```

**Root cause — `.` is a legal identifier character but also the qualified-name
separator.**

- `StrataDDM/StrataDDM/Parser.lean:124-125` — `strataIsIdRest` includes `'.'`, so
  a type variable named `F.pl` is a legal identifier *value*.
- `StrataDDM/StrataDDM/BuiltinDialects/Init.lean:81-89` — a type name parses as a
  `QualifiedIdent`, whose explicit form is `Ident "." Ident` (a dialect-qualified
  reference).

So `F.pl` is read as *dialect `F`, name `pl`* — an undeclared qualified reference,
hence `Undeclared type or category F.pl`. The variable *is* declared in the
`<...>`, so this is the dot-driven misparse, not a real scoping error. In the probe
panel it shows as error `expected Init.QualifiedIdent`.

**Reproduce.**

```lean
parseCoreProgramErr "function f<F.pl>() : F.pl;"   -- .error "… 1:21: Undeclared type or category F.pl."
```

---

## Class 5 — Type-variable use-site not pipe-quoted

Surfaced primarily via the special-character identifier panel.

**Examples** (`tyche_output.jsonl`):

```
function f<|A\|L|> () : A|L;        → unterminated pipe-delimited identifier
function f<|hCxl\\49|> () : hCxl\49;  → expected token
function f<|J\||> () : J|;          → unterminated pipe-delimited identifier
```

**Root cause — the printer pipe-quotes the identifier at its *binding* site
(`<|A\|L|>`) but emits it **bare** at its *use* site (`: A|L`).** The use-site
renderer (`lmonoTyToCoreType`'s `.ftvar name => .tvar default name`,
`FormatCore.lean:209`) doesn't pipe-quote; it passes the raw name value through.
When the name contains `|` or `\` (which are legal *values* — the pipe form
`|A\|L|` demonstrates both sites can accept it), the bare use position produces
unparseable text (`A|L` triggers the pipe-delimited-ident parser mid-token and it
sees an unterminated `|…` without a closing `|`).

**Confirmed directly**: `function f<|A\|L|> () : |A\|L|;` (both sites quoted)
**parses fine**. So the identifier value is legal; the failure is purely that the
*use-site* doesn't quote it.

This is the same asymmetry visible in Class 4 (dot names) and leading-digit names
(e.g. `f<|8W|> () : 8W`), but for `|`/`\` characters specifically. The fix is a
single "pipe-quote the name at the use site when `needsPipeDelimiters` would be
true" check in the `.ftvar` rendering path.

**Reproduce.**

```lean
-- Use-site bare (what the printer emits): fails.
parseCoreProgramErr "function f<|A\\|L|> () : A|L;"    -- .error "… 1:26: unterminated pipe-delimited identifier"
-- Both sites quoted: parses (proving the value is legal), but Core.formatProgram
-- re-emits the use site bare, so it does not round-trip.
parseCoreProgram    "function f<|A\\|L|> () : |A\\|L|;" -- parses; reformat ⇒ "function f<|A\|L|> () : A|L;"
```

---

## Known generator artifacts (NOT Strata bugs)

The following failure(s) are **false positives** caused by the generator producing
names that, while syntactically legal identifiers, collide with reserved keywords
in the Core grammar:

```
function if () : int;   → unexpected token 'if'; expected identifier
```

`if` is a keyword (`Grammar.lean:99`, `fn if (…) : tp => "if " …`). The parser is
correct to reject it as a function name. `genIdentName` produces syntactically
valid identifiers but does not currently exclude reserved keywords. These
represent ~0.2% of failures (1–2 in a 1000-sample run); the remaining 99.8% are
genuine Strata printer/parser bugs.

---

## How to reproduce

- `make test` — the Plausible harness prints, per failing class, the original
  counterexample, the **shrunk** minimal witness, and the parser's error message.
  It also runs a special-character identifier round-trip (`genQuotedName`:
  legal identifiers containing special characters) isolating name-position bugs
  (Classes 2, 4, 5).
- `make tyche` — writes `tyche_output.jsonl`; open with the Tyche VS Code
  extension. The `error_kind` feature groups failures by parser message
  (position-stripped), and the full parser message is in each sample's
  `status_reason` field. The `representation` is the exact string tested (real
  `Core.formatProgram` output).

Shared round-trip + shrinker machinery lives in
`StrataGenerators/FunctionHasTypeAGen/Roundtrip.lean`. The shrinker preserves the
`funcWellFormed` invariant — every candidate is both **well-scoped** (every free
type variable in the signature is declared in `typeArgs`) and **well-typed** (the
body type-checks at the declared `output`, the measure at `int`) — so a minimal
witness is always a genuine `genFunction`-shaped function, never a fabricated
ill-formed artifact.

> **History / caveat.** The earlier version of the function shrinker was
> LLM-synthesized, and it was **producing ill-typed functions after shrinking**:
> `shrinkOut` collapsed a function's declared `output` toward `int` without
> adjusting the body, so a `real`-returning (or otherwise mismatched) body would
> be left under an `int` output. The original `funcWellFormed` only checked
> type-variable scoping, so these ill-typed candidates passed the filter and their
> parse failures were mis-reported as Strata printer/parser bugs (they are not —
> an ill-typed function is correctly rejected by the parser). The well-typedness
> check described above was added to close this gap; treat any pre-fix results in
> older reports with suspicion.

## Priority for reporting to the Strata Core team

1. **Class 1 (missing parens around compound type arguments)** — highest impact
   (~93% of failures), trivially reproducible (`Map int (int -> int)` parses but
   the printer emits the unparseable `Map int int -> int`), and a clear
   printer/parser contract violation in one place (`FormatCore.lean:220-230`
   vs. the type grammar precedences `Init.lean:110-126`). A single
   "parenthesize non-atomic type arguments" fix resolves both the parse-failure
   and mismatch manifestations.
2. **Class 2 (`<s` collision)** — a tokenizer/precedence issue
   (`Grammar.lean:62,187`), self-contained and easy to demonstrate
   (`f<s>` fails, `f< s>` parses).
3. **Class 3** — the three sub-cases are genuinely different and route to
   different owners:
   - **Real-literal soundness bug** (`FormatCore.lean:277`) — highest priority
     within Class 3. Prints a non-terminating decimal like `1/3` as `0.0`,
     silently changing the term's value. Unlike the syntactic bugs, this produces
     a *wrong* program rather than an unparseable one; report as a **printer
     correctness defect**.
   - **Unapplied builtin operators** (`Bool.Not`) — *not* a printer bug, and *not*
     two bugs. The *applied* form round-trips fine via notation (`!true` prints and
     re-parses); the operator simply has **no concrete syntax at all** in its bare
     form (neither `Bool.Not true` nor `Bool.Not(true)` parses — notation `!b` is
     the only surface form, and it is mandatorily saturated). So the single defect
     is a generator/grammar expressibility gap: the generator emits a bare
     `bool -> bool` operator value the grammar cannot write down. Either the printer
     should eta-expand unapplied operators (`Bool.Not` → `fun x => !x`), or the
     **generator** should not emit bare operators at function-value positions. Best
     filed against the generator (or as a Core surface-syntax feature request), not
     as a round-trip printer defect.
4. **Class 4 (dot-in-identifier)** — a genuine tension between the identifier
   lexer (`Parser.lean:124-125`) and qualified-name syntax (`Init.lean:81-89`);
   arguably a spec question about whether `.` should be a legal bare-identifier
   character.
5. **Class 5 (type-variable use-site not quoted)** — same root as Classes 4 and
   the pipe-char cases: the formatter quotes the *binding* site but not the *use*
   site (`FormatCore.lean:209`). A single "apply `needsPipeDelimiters` at the use
   site too" fix addresses this and the leading-digit / dot variants. Low
   incremental effort once the fix is in that one spot.
