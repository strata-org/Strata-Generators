# Catalog of Strata Core pretty-print/parse round-trip failures

This document catalogs the distinct classes of **round-trip failure** surfaced by
the property-based test harnesses (`PlausibleTestMain.lean` / `make test` and
`TycheMain.lean` / `make tyche`). The round-trip property is:

> `format → parse → re-format` should be a fixed point — embedding a generated
> `Function` in a one-decl `Program`, formatting via Strata's own
> `Core.formatProgram`, re-parsing via the Core DDM dialect, and re-formatting
> should reproduce the original string.

Every failing example below is drawn verbatim from the shrunk `representation`
field of `tyche_output.jsonl` (the harness shrinks each counterexample to a
minimal witness, so these are already close to minimal reproducers). Line/column
references point into the [Strata repo](../../Strata).

**Important framing.** The name generators (`genIdentName`, `genQuotedName` in
`StrataGenerators/FunctionHasTypeAGen/Core.lean`) produce only *legal* Core
identifiers by construction, and `genLMonoTy` produces only *well-formed* types.
So a failure to round-trip is a genuine printer/parser faithfulness bug in Strata
Core, **not** a generator artifact. In every case below the printer emits
something the parser cannot read back (or reads back differently).

## Summary of the run

From the most recent `make tyche` (1000 samples on the round-trip panel):

- **436 failed / 564 passed.**
- Failures group (via the `error_kind` feature) into the classes below.

| Class | count | Kind | Root cause |
|---|---|---|---|
| 1. Compound-type angle brackets | 342 | parse-failure | formatter emits `Map<K,V>`/`Sequence<T>`; parser wants `Map K V` |
| 2. Parenthesization loss (mismatch) | 54 | mismatch | nested compound type loses parens on reprint |
| 3. `<s` operator/bracket collision | 10 | parse-failure | `<s` token swallows `<` + `s`-initial type-arg |
| 4. Dot-in-identifier | 17 | parse-failure | `.` is legal in idents but reparses as a qualified name |
| 5. Body expression not re-typecheckable | 13 | parse-failure | printed function body fails the parser's type check |

(436 failures total, from 1000 round-trip samples.)

---

## Class 1 — Compound-type angle-bracket syntax (dominant)

**Examples** (`tyche_output.jsonl`):

```
func f :  → Map<int, Map<int, int> -> int>;
    → Parse errors: 1:24: Map expects 2 arguments.  1:24: Unexpected argument to Map.

func D :  → Sequence<Sequence<int> -> string>;
    → Parse errors: 1:25: Sequence expects 1 arguments.  1:25: Unexpected argument to Sequence.

func f :  → Map<int -> int, int>;
    → Parse errors: 1:16: Map expects 2 arguments.  1:31: Unexpected argument to int.
```

**Root cause — formatter/parser disagree on compound-type surface syntax.**

The Core grammar declares parameterized types with **juxtaposition** (space-separated
application), not angle brackets:

- `Strata/Languages/Core/DDMTransform/Grammar.lean:53` — `type Map (dom : Type, range : Type);`
- `Strata/Languages/Core/DDMTransform/Grammar.lean:54` — `type Sequence (elem : Type);`

So the parser expects `Map int bool` and `Sequence regex`. But the formatter's
type converter renders these with `<...>` angle-bracket / comma syntax. The
converter is:

- `Strata/Languages/Core/DDMTransform/FormatCore.lean:220-223` — `Map [k,v]` → `.Map default kty vty`
- `Strata/Languages/Core/DDMTransform/FormatCore.lean:224-226` — `Sequence [e]` → `.Sequence default ety`

and the `.Map`/`.Sequence` CST constructors (from the `Strata.CoreDDM`
grammar-derived namespace) print as `Map<k, v>` / `Sequence<e>`.

**Confirmed directly** (standalone parse probes):

```
function f () : Map<int, bool>;   →  PARSE-EXCEPTION: unexpected token '<'
function f () : Map int bool;     →  OK
function f () : Sequence regex;   →  OK
function f () : bv16;             →  OK   (formatter emits bv<16>, also rejected)
```

The `Map expects 2 arguments` / `Unexpected argument to int` messages are the
parser's downstream reaction: it parses `Map` (arity 2) applied by juxtaposition,
grabs the following tokens as juxtaposed arguments, and the counts/kinds don't
line up because the `<`, `,`, `>` were never valid there.

This is the **single largest failure class** and is independent of names — it
fires for any function whose signature contains a `Map`, `Sequence`, or `bv<N>`
type. It does not appear in the single-identifier probe panel because that probe
uses only `int` outputs.

---

## Class 2 — Parenthesization loss on nested compound types (mismatch)

These *parse* successfully but are **not a fixed point**: `format → parse →
re-format` yields a different (and semantically wrong) string. In the Tyche panel
they show `parsed=yes, roundtripped=no` and an empty `status_reason`.

**Examples** (`tyche_output.jsonl` — original) and their reprint (from
`make test`'s mismatch shrinker):

```
func f : (dh : Map (Sequence bool -> bool) int) : bool;
    re-formats to:  func f : (dh : Map Sequence bool -> bool int) : bool;

func f :  → Sequence (Sequence int -> int);
    re-formats to:  func f :  → Sequence Sequence int -> int;
```

**Root cause — the formatter does not parenthesize a compound type used as a
type argument.** When a `Map`/`Sequence`/arrow type appears *as an argument* to
another type constructor, the juxtaposition syntax needs parentheses to preserve
grouping: `Map (Sequence bool -> bool) int` is a 2-arg `Map`, but without the
parens `Map Sequence bool -> bool int` re-associates entirely.

The type converter at `Strata/Languages/Core/DDMTransform/FormatCore.lean:220-230`
recurses into children (`lmonoTyToCoreType k`, `… v`, `… a`, `… b`) without
tracking whether the child needs parenthesization for the surrounding
juxtaposition context. The first reprint parses (the angle-bracket form of Class 1
notwithstanding — these particular cases happen to survive the initial parse),
but the re-formatted output drops the grouping, so `s1 ≠ s2`.

> Note: Classes 1 and 2 are two facets of the same underlying compound-type
> formatting code (`FormatCore.lean:220-230`). Class 1 is "the angle-bracket form
> doesn't parse at all"; Class 2 is "even when a form parses, nested grouping is
> lost." A fix to emit correctly-parenthesized juxtaposition syntax would address
> both.

---

## Class 3 — `<s` operator / type-argument bracket collision

**Examples** (`tyche_output.jsonl`):

```
func f : ∀ss.  → int;      → Parse errors: 1:10: unexpected token '<s'; expected Core.Bindings
func M : ∀sw.  → bool;     → Parse errors: 1:10: unexpected token '<s'; expected Core.Bindings
func G : ∀s6.  → int;      → Parse errors: 1:10: unexpected token '<s'; expected Core.Bindings
```

(The `∀ss.` display is `ppFunction`'s rendering; the *formatter* emits the
type-argument list as `f<ss>` — angle brackets around the type args.)

**Root cause — maximal-munch tokenization of `<s`.** Type arguments are printed
with the `<...>` bracket syntax:

- `Strata/Languages/Core/DDMTransform/Grammar.lean:62` — `op type_args (args : CommaSepBy TypeVar) : TypeArgs => "<" args ">";`

Meanwhile the signed-less-than bitvector operator is the token `<s`:

- `Strata/Languages/Core/DDMTransform/Grammar.lean:187` — `fn bvslt (…) : bool => @[prec(20), leftassoc] a " <s " b;`

When a type argument's name begins with `s` (e.g. `ss`, `sw`, `s6`), the printed
`f<ss>` is lexed by maximal munch as `f` `<s` `s>` — the `<s` operator token is
grabbed before `<` can open the type-argument bracket. The parser is now looking
for bindings after `f` and reports `unexpected token '<s'; expected
Core.Bindings`.

**Confirmed directly**: `function f<s> () : int;` fails identically, while
`function f< s> () : int;` (space after `<`) parses. So it is specifically the
`<` immediately followed by `s`.

This class affects even the clean `genIdentName` generator, since it happily
produces type-variable names starting with `s`.

---

## Class 4 — Dot-in-identifier reparses as a qualified name

**Examples** (`tyche_output.jsonl`):

```
func f : ∀F.pl.  → F.pl;   → Parse errors: 1:22: Undeclared type or category F.pl.
func h : ∀w.Z.  → w.Z;     → Parse errors: 1:21: Undeclared type or category w.Z.
func _ : ∀o..  → o.;       → Parse errors: 1:20: Undeclared type or category o.||.
```

**Root cause — `.` is a legal identifier character but also the qualified-name
separator.** The lexer permits `.` inside identifiers:

- `StrataDDM/StrataDDM/Parser.lean:124-125` — `strataIsIdRest` includes `'.'`.

So a generated type variable named `F.pl` is a legal identifier *value*. But at
parse time a type name is parsed as a `QualifiedIdent`, whose explicit form is
`Ident "." Ident` (a dialect-qualified name):

- `StrataDDM/StrataDDM/BuiltinDialects/Init.lean:81-89` — `qualifiedIdentExplicit` = `dialect "." name`.

So `F.pl` is read as *dialect `F`, name `pl`* — a qualified reference to a type in
dialect `F` — which doesn't exist, hence `Undeclared type or category F.pl`. The
trailing-dot cases (`o.`, `q.`) additionally hit the pipe-quote escape (`o.||`)
because the formatter pipe-quotes some of these.

These are genuine: the type variable *is* declared (in the `∀`), so the failure
is the dot-driven misparse, not an actual scoping error. See also
[`docs/function-roundtrip-invalid-identifiers.md`](function-roundtrip-invalid-identifiers.md)
for the identifier-generation analysis, and the single-identifier probe panel
(`genFunction: single-identifier round-trip probe`), where this shows up as
`char_class=dot` with error `expected Init.QualifiedIdent`.

---

## Class 5 — Printed function body is not re-typecheckable

**Examples** (`tyche_output.jsonl`):

```
func D :  → bool := λbool -> bool. λint. #false
    → Parse errors: 2:2: Expression has type bool -> bool -> int -> bool when bool expected.

func f :  → bool := Bool.Not
    → Parse errors: 2:2: Expression has type regex when bool expected.

func f :  → int := λint -> bool. #-1
    → Parse errors: 2:2: Expression has type int -> bool -> int when int expected.
```

**Root cause — this is a *type-checking* failure during re-parse, not a lexical
or grammar failure.** The parser's translation phase (`Strata.translateProgram`,
invoked in `parseCoreProgram` /
`StrataGenerators/FunctionHasTypeAGen/Roundtrip.lean`) type-checks the parsed
body against the declared output type and rejects it. These are the residual
cases where the printed body's inferred type doesn't match the declared return
type after the round-trip.

These are less common and are more likely to reflect an interaction between the
expression generator, the printer, and the parser's type inference than a single
localized printer bug. They are worth triaging individually rather than treating
as one bug; the `Bool.Not` / `Unknown variable Bool.Implies` variants in
particular suggest a builtin-operator naming/printing mismatch.

---

## How to reproduce

- `make test` — the Plausible harness prints, per failing class, the original
  counterexample, the **shrunk** minimal witness, and the parser's error message.
  It also runs a single-identifier probe (`genQuotedName`) that isolates
  name-position bugs (Classes 3, 4).
- `make tyche` — writes `tyche_output.jsonl`; open with the Tyche VS Code
  extension. The `error_kind` feature groups failures by parser message
  (position-stripped), and the full parser message is in each sample's
  `status_reason` field.

Shared round-trip + shrinker machinery lives in
`StrataGenerators/FunctionHasTypeAGen/Roundtrip.lean`.

## Priority for reporting to the Strata Core team

1. **Class 1 (compound-type angle brackets)** — highest impact (342/436
   failures), trivially reproducible (`Map<int,bool>` vs `Map int bool`), and a
   clear formatter/parser contract violation in one place
   (`FormatCore.lean:220-230` vs `Grammar.lean:53-54`).
2. **Class 2 (parenthesization loss)** — same code region; a correct fix to
   compound-type printing should resolve both 1 and 2.
3. **Class 3 (`<s` collision)** — a tokenizer/precedence issue
   (`Grammar.lean:62,187`), self-contained and easy to demonstrate.
4. **Class 4 (dot-in-identifier)** — a genuine tension between the identifier
   lexer (`Parser.lean:124-125`) and qualified-name syntax
   (`Init.lean:81-89`); arguably a spec question about whether `.` should be a
   legal bare-identifier character.
5. **Class 5 (body re-typecheck)** — triage individually.
