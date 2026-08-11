# Bug report for Strata: the pretty-printer cannot express constructs the language admits

**Target repo:** `strata-org/Strata` (observed on the vendored fork pinned at rev
`865885871`; the affected code — `Strata/Languages/Core/DDMTransform/FormatCore.lean`
and `Grammar.lean` — is not fork-only).

**Severity:** medium. Unlike the `changed`-flag issue (see
`strata-changed-flag-bug.md`), this one has an observable consequence today: the
printer emits a **syntactically valid placeholder** rather than failing, so a
program can round-trip "successfully" while denoting something different.

---

## Summary

Three related findings, in increasing order of scope:

| # | Finding | Site |
|---|---|---|
| 1 | `bitvec 128` literals are unprintable, though the width is registered and has a grammar production | `FormatCore.lean` `lconstToExpr` |
| 2 | **All 18** `Bv{w}.ToInt` / `Bv{w}.ToUInt` / `Int.ToBv{w}` operators are unprintable, at *every* registered width | `FormatCore.lean:407` `handleUnaryOps` fallback |
| 3 | The printer substitutes a syntactically valid placeholder instead of failing, so unprintable input can round-trip as a *different* program | `FormatCore.lean:1179` `formatWithDDM` |
| 4 | `Function.typeCheck` accepts `bitvec w` for **every** `w`; the printer supports exactly five widths | `lmonoTyToCoreType:243–247`, `lconstToExpr:319–323`, `bvTypeOfWidth:343–350` |

Finding 4 answers repo issue #48 and subsumes the "non-power-of-2 width" framing —
see the correction below, because that framing is measurably wrong. Findings 1 and
2 are *within* the supported set and so are not instances of finding 4: `bitvec 128`
is factory-registered with a grammar production, and the `Bv↔Int` operators are
missing at all widths including `1, 8, 16, 32, 64`.

---

## Finding 1 — `bitvec 128` literals

`bv128` is registered in the factory (`Factory.lean:872`, `bv128ToIntFunc`) and has
a grammar production (`Grammar.lean:113`, `bv128Lit`). But `lconstToExpr` logs

```
Unsupported construct in lconstToExpr: unsupported bitvec width: 128
```

Every *other* registered width (`1, 8, 16, 32, 64`) prints, which is what makes
128 an omission rather than a design boundary. Measured over the registered set,
the unprintable widths are exactly `[128]`.

---

## Finding 2 — the whole `Bv↔Int` conversion family, at every width

`Factory.lean:850–872` registers, for `w ∈ {1, 8, 16, 32, 64, 128}`:

```lean
def bvToIntFunc (size : Nat) : WFLFunc CoreLParams :=
  unaryFuncUneval s!"Bv{size}.ToInt" (.bitvec size) .int rfl rfl
def intToBvFunc (size : Nat) : WFLFunc CoreLParams :=
  unaryFuncUneval s!"Int.ToBv{size}" .int (.bitvec size) rfl rfl
```

There is **no grammar production and no printer arm for any of them.**
`handleUnaryOps` (`FormatCore.lean:353–407`) enumerates `.Not`, `.Neg`,
`SafeNeg`/`SafeUNeg`, the two overflow predicates and nine `bvExtract` shapes, then
falls through:

```lean
| _ => mkGenericCall "handleUnaryOps" name [arg]
```

`mkGenericCall` logs an error and renders the operator as an application of a
freshly registered **free variable**. So all 18 operators can be constructed and
typechecked but not printed:

```
Bv1.ToInt   Bv1.ToUInt   Int.ToBv1
Bv8.ToInt   Bv8.ToUInt   Int.ToBv8
Bv16.ToInt  Bv16.ToUInt  Int.ToBv16
Bv32.ToInt  Bv32.ToUInt  Int.ToBv32
Bv64.ToInt  Bv64.ToUInt  Int.ToBv64
Bv128.ToInt Bv128.ToUInt Int.ToBv128
```

Measured: **18/18 unprintable.** This is the systematic half of the report — a
whole feature missing from the printer and grammar, not a missing case in an
otherwise complete enumeration.

---

## Finding 3 — placeholders make failure silent

`formatWithDDM` (`FormatCore.lean:1179`) does not fail when conversion errors were
logged. It appends them to the output as a comment block:

```
-- Errors encountered during conversion:
```

and leaves a placeholder in the program text. Two placeholders are dangerous
because they are *syntactically valid*:

- `unknownTypeVar = "$__unknown_type"` (`FormatCore.lean:80`) — an unprintable type
  becomes a **type variable**, so a program mentioning an unsupported type parses
  back as a *polymorphic* program;
- `mkGenericCall` (`FormatCore.lean:225`) — an unprintable operator becomes an
  ordinary application of a free variable.

Measured over generated whole programs: conversion errors fire on **~50%** of
programs at the bounds the shared `Arbitrary GenProgram` wrapper samples (198/400,
at 2–5 declarations) and on **~86%** at a fixed `numDecls = 6` (343/400). The rate
climbs with declaration count because each declaration is an independent chance to
reach an unprintable construct, so a run's observed rate should be compared against
whichever bound it sampled at. Errors span seven distinct printer sites —
`lmonoTyToCoreType`, `lconstToExpr`, `handleUnaryOps`, `handleBitvecBinaryOps`,
`lopToExpr`, `extractTriggerPatterns`, `funcDeclToStatement`.

Nearly every erroring program also fails to re-parse (193 of 198 at the shared
bounds; 341 of 343 at `numDecls = 6`) — so a round-trip check is already red on
those, it simply cannot say *why*. The few that **re-parse cleanly** are the
interesting ones: there the placeholder produced a syntactically valid but
semantically different program. That is precisely what a string round-trip check
structurally cannot detect, and it is the reason the "printer logged no error"
oracle is worth having in addition to round-trip.

### Suggested fix direction

Make `formatWithDDM` (or a strict variant) return `Except`, so a caller can choose
between "best-effort render for display" and "render or fail". The placeholders are
reasonable for a debug dump and actively harmful for anything that re-parses.

---

## Finding 4 — the typechecker admits every bitvector width; the printer admits five

`Function.typeCheck` accepts `bitvec w` for **every** `w` tested (`0..199`), because
`LMonoTy.bitvec` is unconstrained in the AST and the known-type entry is the
polymorphic `∀n. bitvec n`. Scanning the same range, the widths that print cleanly
are exactly:

```
[1, 8, 16, 32, 64]
```

So 60 of the first 64 widths typecheck but cannot be printed.

### Correction to the framing in repo issue #48

#48 predicts round-trips fail because "the DDM expects bit-vector widths to be a
power of 2". **That predicate is wrong**, and measurably so:

| width | power of 2? | prints? |
|---|---|---|
| 2 | yes | **no** |
| 4 | yes | **no** |
| 128 | yes | **no** |
| 1, 8, 16, 32, 64 | yes | yes |
| 3, 5, 6, 7, 9, … | no | no |

The supported set is not "the powers of two" — it is *the five arms hardcoded in the
printer*. So the correct statement of the defect is "the printer supports a
hardcoded five-element set while the typechecker and AST admit every width", and
the fix is **not** a power-of-2 guard. Either the printer should cover the widths
the language admits, or the typing spec should constrain widths to the printable
set (#48's own second bullet) — but a power-of-2 constraint would still leave
`2`, `4` and `128` broken.

### Two failure modes, and why the type case is the subtler one

The three sites do not behave alike:

- `lmonoTyToCoreType` (`:243–247`) substitutes `$__unknown_type` — a **type
  variable**. So `function f (x : bitvec 3) : bitvec 3` prints as
  `function f (x : $__unknown_type) : $__unknown_type`.
- `lconstToExpr` (`:319–323`) logs and emits nothing usable for the literal.
- `bvTypeOfWidth` (`:343–350`) logs and returns **`.bv64`**. An operator at an
  unsupported width is therefore printed as though it were a *64-bit* operator: a
  silent width change rather than a visible hole.

Checked: the `$__unknown_type` output fails to re-parse (it is not a declared type
argument), and it still fails when the host function *already* has a type
parameter — so today finding 4 surfaces as a round-trip parse failure rather than
as a silently-different program. That is luck rather than design; the `.bv64`
fallback shows the same code path is willing to substitute a *plausible* wrong
answer instead of an obviously broken one.

---

## Regression tests

Pinned by properties in `StrataGenerators/PrinterCoverage.lean`, run by both
harnesses:

| Property | Status |
|---|---|
| `printer: bitvec 128 literals are printable` | FAILS (finding 1) |
| `printer: Bv/Int conversion operators are printable` | FAILS (finding 2, 18/18) |
| `printer: no conversion error on generated programs` | FAILS ~50% (finding 3) |
| `printer: every typecheckable bitvec width is printable` | FAILS 60/64 (finding 4) |

Finding 4's property is stated as an implication — *typechecks → prints* — rather
than as an equality against the printer's arm list, so it is a claim about Strata's
internal consistency rather than a restatement of the implementation. It is a
deterministic scan rather than a sample because the defect is a property of the
width: `genLMonoTyBitvec` draws widths from `Nat.arbitrary`
(`HasTypeAGen/Core.lean:164` — exactly the generator #48 proposes), so the
whole-program property already samples this space, but a generated hit does not say
*which* width is at fault.

The `Printer conversion-error diagnostics` pass tallies the distinct error messages
most-frequent-first, and reports how many erroring programs still re-parse — the
finding-3 count.

**One caveat built into the property.** Our own `corePolyOps` contains synthetic
combinators (`id`, `churchTrue`, `churchFalse`) that are deliberately *not* Strata
operators; the printer is correct to reject those. `strataErrorLines` filters them
out, so the property scores only genuine Strata gaps. `bitvec 0` and other
non-power-of-2 widths are *not* filtered, and remain the separate open question of
repo issues #48/#38 — they contribute to the error rate above but are not claimed
as new findings here.
