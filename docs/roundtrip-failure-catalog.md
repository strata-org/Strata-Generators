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

## Summary of the run

From a representative `make tyche` run (200 samples on the round-trip panel):

- **88 failed / 112 passed.**
- Failures group (via the `error_kind` feature) into the classes below.

| Class | count | Kind | Root cause |
|---|---|---|---|
| 1. Missing parens around compound type arguments | 82 | parse-fail (71) + mismatch (11) | printer doesn't parenthesize an arrow/compound used as a type argument; application binds tighter than `->` |
| 2. `<s` operator / type-arg bracket collision | 3 | parse-failure | `<s` token swallows `<` + an `s`-initial type-arg |
| 3. Body expression not re-typecheckable | 2 | parse-failure | printed body fails the parser's type check (often a builtin-op printing gap) |
| 4. Dot-in-identifier (rarer here; see probe panel) | ~0–1 | parse-failure | `.` is legal in idents but reparses as a qualified name |

(88 failures total, from 200 round-trip samples. Class 1 dominates at ~93%.)

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
point — `parsed=yes, roundtripped=no`, empty `status_reason`):

```
function r () : Sequence (Map int string -> int);
function f () : Sequence (Sequence int -> int);
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
splicing it into a juxtaposition position. Whether a given instance shows up as a
parse-failure or a mismatch just depends on whether the mis-grouped string happens
to be rejected outright or re-associates into a different valid-looking string.

This class is independent of names and fires for essentially any signature
containing a `Map`, `Sequence`, or arrow nested inside another type constructor.

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
produces type-variable names starting with `s`. The single-identifier probe panel
shows this as `char_class=plain` failures whose names start with `s`.

---

## Class 3 — Printed function body is not re-typecheckable

These parse structurally but fail during the parser's translation/type-check
phase. Several are really **printer gaps for expression constructs**, surfaced as
a type error.

**Examples** (`tyche_output.jsonl`):

```
function L () : bool { re.none() }
    → Parse errors: 2:2: Expression has type regex when bool expected.
    (conversion note: "Unsupported construct in lopToExpr: 0-ary op not found: Bool.Not")

function f () : real { 0.0 }
    → Parse errors: 6:0: unexpected token '-'; expected 'function', Core.Block …
    (conversion note: "Unsupported construct in lconstToExpr: unsupported real: 1/3")

function f () : bool { fun __q0 : bool -> regex => fun __q1 : bool => -2 }
    → Parse errors: 2:2: Expression has type bool -> regex -> bool -> int when bool expected.
```

**Root cause — mixed.** The `conversion note`s point at the *printer* side:
`Core.formatProgram` (via `lopToExpr` / `lconstToExpr` in `FormatCore.lean`)
hitting a construct it cannot faithfully render — a builtin op like `Bool.Not`, or
a real literal such as `1/3` it prints as `0.0`. The resulting text then either
doesn't parse (`0.0` case) or parses to an expression whose type no longer matches
the declared output (`Expression has type … when bool expected`). These are worth
triaging individually; the common thread is printer incompleteness for certain
expression/constant forms rather than a single localized rule.

> **Note on a related, subtler case: unbound type variables in bodies.** A body
> can mention a type variable that the function's `typeArgs` never declares, e.g.
> `function L () : int { fun __q0 : c -> int => if true then -1.0 else 5.0 }`.
> Here the *AST* is well-typed by construction (`genFunction` generates the body
> at the declared output type — `Core.lean:174`), and the `int` inside `c -> int`
> is `__q0`'s parameter codomain, not the lambda's result (the lambda's result is
> the `real`-typed `if`, so `__q0 : (c -> int) -> real`). The defect is that `c`
> appears in the printed body but `L` has no `<c>` type-argument list, so on
> re-parse `c` is undeclared. This is the body-side analogue of an
> undeclared-type-variable print, distinct from the type errors above.

---

## Class 4 — Dot-in-identifier reparses as a qualified name

Rare in the full-function panel at this sample size, but reliably reproduced by
the single-identifier probe (`genFunction: single-identifier round-trip probe`,
`char_class=dot`).

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

---

## How to reproduce

- `make test` — the Plausible harness prints, per failing class, the original
  counterexample, the **shrunk** minimal witness, and the parser's error message.
  It also runs a single-identifier probe (`genQuotedName`) isolating name-position
  bugs (Classes 2, 4).
- `make tyche` — writes `tyche_output.jsonl`; open with the Tyche VS Code
  extension. The `error_kind` feature groups failures by parser message
  (position-stripped), and the full parser message is in each sample's
  `status_reason` field. The `representation` is the exact string tested (real
  `Core.formatProgram` output).

Shared round-trip + shrinker machinery lives in
`StrataGenerators/FunctionHasTypeAGen/Roundtrip.lean`. The shrinker preserves the
`funcWellFormed` invariant (every free type variable in the signature is declared
in `typeArgs`), so a minimal witness is always a genuine `genFunction`-shaped
function and never a fabricated undeclared-variable artifact.

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
3. **Class 3 (body re-typecheck / printer gaps)** — triage individually; several
   are printer incompleteness for specific ops/constants (e.g. `Bool.Not`, real
   `1/3`).
4. **Class 4 (dot-in-identifier)** — a genuine tension between the identifier
   lexer (`Parser.lean:124-125`) and qualified-name syntax (`Init.lean:81-89`);
   arguably a spec question about whether `.` should be a legal bare-identifier
   character.
