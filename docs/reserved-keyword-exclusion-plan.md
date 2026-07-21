# Excluding Strata Core reserved keywords from identifier/label generators

**Status:** design + implementation plan (not yet started in code). Handoff notes.
**Date:** 2026-07-20.

## Goal

Make the identifier- and label-producing generators in this repo incapable of
producing a **Strata Core reserved keyword** (e.g. `if`, `var`, `while`, `int`).
Store the keyword set in a `Std.HashSet String`, filter every relevant generator
against it, and update the affected soundness/completeness proofs.

This supersedes the narrower, "don't bother" recommendation in
[`genidentname-keyword-filter-proof-impact.md`](./genidentname-keyword-filter-proof-impact.md),
which only looked at `genIdentName` in `FunctionHasTypeAGen` and pre-dates the
decision to do this repo-wide. Read that doc for the completeness-chain reasoning
in the function generator specifically; this doc is the authoritative plan for the
repo-wide change.

## Decisions locked in

- **Storage:** a `Std.HashSet String`, built from a backing `List String` via
  `Std.HashSet.ofList`.
- **Keyword set:** the Strata Core grammar's keyword + type tokens **only**. The
  previously-discussed SMT-LIB subset (`!`, `_`, `as`, `BINARY`, `lambda`, `let`,
  `match`, …) is **dropped** per the latest instruction.
- **Case-sensitive:** the DDM tokenizer is case-sensitive, so `If`/`VAR` are legal
  identifiers. The set contains only the lowercase/exact grammar spellings.

## The keyword list (61 entries, derived from the grammar)

Source of truth: `~/Documents/Strata/Strata/Languages/Core/DDMTransform/Grammar.lean`
(the `dialect Core;` block). Extraction method + the tokenizer subtlety are
documented at the bottom of this file. The list:

```
-- Core grammar keyword tokens (alphabetic string literals that reserve the whole word)
ashr assert assume axiom bool call cfg const cover datatype decreases distinct
div else ensures exists exit false forall free fun function goto have havoc if
in inline inout invariant mapConst mod old out procedure rec requires sdiv sge
sgt sle slt smod spec then true type var while
-- Core type names (also reserved tokens)
Map Sequence int real regex string bv1 bv8 bv16 bv32 bv64 bv128
```

Notes:
- `bool` appears in both the keyword and type categories; include it once.
- **Deliberately NOT reserved** (their grammar tokens carry trailing punctuation,
  so a bare identifier of that name lexes fine): `branch` (`"branch ("`), `return`
  (`"return;"`), `program`, and all dotted/braced builtins (`str.*`, `re.*`,
  `Sequence.*`, `Bv.*`, `Int.*`, `bv{N}`, `frac{`, `as_uint`, …). Excluding them
  would be harmless but is not required.

## Verified facts (checked via `lean_run_code` against this project)

1. **Bridge lemma exists:** `Std.HashSet.contains_ofList` :
   `(Std.HashSet.ofList l).contains k = l.contains k`
   (module `Std.Data.HashSet.Lemmas`). This reduces all `HashSet.contains`
   reasoning to `List.contains` on the concrete backing list.
2. **Concrete membership is `decide`-able:** with the bridge lemma,
   `kws.contains "if" = true` and `kws.contains "notakeyword" = false` both close
   with `simp only [kws, Std.HashSet.contains_ofList]; decide`.
3. **Max keyword length is 9** (`decreases`, `invariant`, `procedure`). The fact
   `∀ s ∈ coreReservedKeywordsList, s.length ≤ 9` is `decide`-able. **Use this for
   the fallback proof** (see below).
4. **`String.all` does NOT reduce under `decide`** — `∀ k ∈ list, k.all (· == 'x')
   = false` gets stuck on the String iterator. So do **not** try to prove the
   all-`x` fallback is non-reserved via a character predicate. Use the length
   argument instead (fact 3), which mirrors the existing `fallbackFreshLabel_not_mem`
   proof exactly.

## Design

### 1. Definitions (in `StrataGenerators/HasTypeAGen/Core.lean`)

Put these near the top of the `Lambda` namespace section (before the first
generator that references them; `genStrConst` etc. live in this file, and both
`CmdHasTypeAGen/Core.lean` and `StmtHasTypeAGen/Core.lean` import it, so this is
the right shared home).

```lean
/-- Backing list of Strata Core reserved words: the grammar's keyword tokens and
    type names. Source: Strata `Languages/Core/DDMTransform/Grammar.lean`. -/
def coreReservedKeywordsList : List String :=
  [ "ashr", "assert", "assume", "axiom", "bool", "call", "cfg", "const", "cover",
    "datatype", "decreases", "distinct", "div", "else", "ensures", "exists",
    "exit", "false", "forall", "free", "fun", "function", "goto", "have", "havoc",
    "if", "in", "inline", "inout", "invariant", "mapConst", "mod", "old", "out",
    "procedure", "rec", "requires", "sdiv", "sge", "sgt", "sle", "slt", "smod",
    "spec", "then", "true", "type", "var", "while",
    "Map", "Sequence", "int", "real", "regex", "string",
    "bv1", "bv8", "bv16", "bv32", "bv64", "bv128" ]

/-- Reserved words a generated identifier/label must avoid, as a `HashSet` for
    O(1) membership at generation time. -/
def coreReservedKeywords : Std.HashSet String :=
  Std.HashSet.ofList coreReservedKeywordsList

/-- Bridge: `HashSet` membership reduces to membership in the backing list. -/
theorem mem_coreReservedKeywords_iff (s : String) :
    coreReservedKeywords.contains s = coreReservedKeywordsList.contains s := by
  simp only [coreReservedKeywords, Std.HashSet.contains_ofList]
```

Requires `import Std.Data.HashSet` (or the `.Lemmas` module) at the top of
`HasTypeAGen/Core.lean`, and likely `open Std`.

### 2. Generator shape (the "test + fallback" pattern)

Every affected generator already uses a **test-and-fallback** idiom (see
`genFreshLabel`, `genFreshName`). Keep that shape and just add the keyword test to
the guard. The fallback (`fallbackFreshLabel` / `fallbackFreshName`) is an all-`x`
string strictly longer than everything in context — and since no keyword is all-`x`
(indeed all are ≤ length 9), **the existing fallbacks are already non-reserved**,
so they remain valid fallbacks with no change.

For a generator that has no existing freshness fallback (e.g. `genInvariant`'s
label, `genTypeConstructor`'s names), add one. A fixed safe constant works because
we only need *some* non-reserved witness; e.g. a string of `'x'` of length 10
(longer than the max keyword length 9) is provably non-reserved by the length
argument, independent of context.

Sketch:

```lean
def genLabelName [Gen G] : G String := do
  let s ← String.arbitrary
  if coreReservedKeywords.contains s then
    pure someFixedNonReservedString      -- e.g. String.ofList (List.replicate 10 'x')
  else
    pure s
```

### Affected generators

| Generator | File | Produces | Action |
|---|---|---|---|
| `genFreshLabel` | `StmtHasTypeAGen/Core.lean:102` | block label (Ident) | add keyword test to guard; fallback already non-reserved |
| `genFreshName` | `CmdHasTypeAGen/Core.lean:51` | variable name (Ident) | same |
| `genInvariant` (label `l`) | `StmtHasTypeAGen/Core.lean:170` | invariant label | wrap `String.arbitrary` in keyword filter + fallback |
| `genTypeConstructor` (`name`, `params`) | `StmtHasTypeAGen/Core.lean:114` | type ctor + param names | same, per name |
| **`genStrConst`** | `HasTypeAGen/Core.lean:229` | **string *literal*, not an Ident** | **DO NOT filter** — a `strConst` is quoted data, keywords are legal here |

The last row is important: `genStrConst` produces a string *value* (`.strConst`),
which is quoted in surface syntax and so may legally equal `"if"`. Leave it alone.
Confirm there are no other identifier producers by re-running the
`String.arbitrary` grep (see below).

## Proof impact

### Soundness — no change

Every soundness proof that touches a generated name **discards the name witness**
(binds it as `_` and never uses it) — the same pattern documented for
`genFunction_sound`. Narrowing a generator's support only *removes* elements, so
`support ⊆ old support`, and any `∀ x ∈ support, P x` soundness statement stays
true. Expect `genStmt_sound`, `genCmd*_sound`, `genInvariants_sound`,
`genTypeConstructor`-related soundness to be **verbatim**. Verify by building.

### Freshness proofs — small edits

- `genFreshLabel_not_mem` (`StmtHasTypeAGen.lean:218`) and
  `genFreshName_produces_fresh` (`CmdHasTypeAGen.lean:267`): these currently case-
  split on the `if s ∈ labels`/`isFresh` guard. After adding a keyword conjunct to
  the guard, the case split gains a branch; both branches still yield freshness
  (the random branch from the guard hypothesis, the fallback branch from the
  length lemma). Mechanical.
- Consider adding companion lemmas `genFreshLabel_not_reserved` /
  `genFreshName_not_reserved` (`∀ s ∈ support, ¬ coreReservedKeywords.contains s`)
  so downstream users get the guarantee. These are the *new value* of the change;
  prove via the same case split + `mem_coreReservedKeywords_iff` + `decide` for the
  fallback's length.

### Completeness — statement changes (narrowing), then mechanical proof edits

Narrowing support means the completeness theorems must gain a **`¬ reserved`
side-condition** on each name hypothesis (exactly the pattern from the older doc,
§"What changes with a whole-string filter"). Affected:

- `genInvariant_complete` (`StmtHasTypeAGen.lean:572`) — `hlabel` gains
  `∧ ¬ coreReservedKeywords.contains p.1` (or the label is drawn from the new
  filtered generator's support, characterized by a new support lemma).
- `genInvariants_complete` (`:581`) — threads the per-element side-condition.
- `genTypeConstructor_complete` (`:593`) — `hname` and `hparams` each gain the
  side-condition.
- `genInvariant_complete`'s **one caller** is `genInvariants_complete:588`; update
  the passed facts. `genTypeConstructor_complete` and `genInvariants_complete` have
  **no in-repo callers** (grep confirmed), so the narrowing does not ripple further.

Each affected generator needs a **new support-characterization lemma** of the form:

```lean
theorem mem_support_genLabelName_iff (s : String) :
    s ∈ SetGen.support (genLabelName (G := SetGen.Set)) ↔
      (s ∈ SetGen.support (String.arbitrary …) ∧ ¬ coreReservedKeywords.contains s)
      ∨ s = fallback   -- fallback branch is reachable too; state honestly
```

The fallback branch makes the clean `↔` slightly messier (the older doc flagged
this as "the single biggest new proof burden"). Two options:
1. **State it honestly** with the `∨ s = fallback` disjunct. Downstream completeness
   only needs the `←` direction (reachability), so the extra disjunct is harmless
   there; soundness ignores it.
2. Keep completeness hypotheses phrased as "`s ∈ support (filtered generator)`"
   rather than re-deriving them, pushing the characterization into the one new
   lemma. Preferred — minimizes churn in the `_complete` statements.

### `String_arbitrary_support_set` stays

The helper `String_arbitrary_support_set` (`HasTypeAGen.lean:1260`) characterizes
the *unfiltered* `String.arbitrary` support and is still needed for `genStrConst`
completeness (`:1993`, `:2384`). Do not remove it; the new filtered-generator
support lemma builds *on top of* it.

## Step-by-step plan for tomorrow

1. Add `import Std.Data.HashSet` + defs (`coreReservedKeywordsList`,
   `coreReservedKeywords`, `mem_coreReservedKeywords_iff`) to
   `HasTypeAGen/Core.lean`. Build that file alone first.
2. Prove the two reusable facts as standalone lemmas:
   `∀ s ∈ coreReservedKeywordsList, s.length ≤ 9` (`by decide`) and a
   `fallback_not_reserved` helper. These unblock every fallback proof.
3. Update `genFreshName` + its freshness proof; build `CmdHasTypeAGen`.
4. Update `genFreshLabel`, `genInvariant`, `genTypeConstructor` + support/freshness
   lemmas; build `StmtHasTypeAGen/Core.lean`.
5. Update completeness lemmas (`genInvariant_complete`, `genInvariants_complete`,
   `genTypeConstructor_complete`) and the one caller; build `StmtHasTypeAGen.lean`.
6. Full `lake build`. Soundness should need zero edits — if it doesn't, revisit
   whether a proof was accidentally *using* a name witness.
7. Optional: add `genX_not_reserved` guarantee lemmas as the payoff.

## Appendix: why the token list is what it is

The DDM tokenizer (`StrataDDM/Parser.lean`, `isToken` at :130) treats a word as
reserved **only when a registered token spans the entire identifier**. Registered
tokens come from the *trimmed* string literals in the grammar (`Parser.lean:946`,
`l.trimAscii`). So `"if "` → token `if` → bare `if` reserved; but `"branch ("` →
token `branch (` (space + paren retained) → bare `branch` is *not* reserved.
Matches the grammar's own comment at `Grammar.lean:544`.

Extraction (whitespace-stripped, `//`-comments removed, from the `dialect Core;`
block): collect every `"…"` literal that is purely alphabetic after trimming →
keyword tokens; collect every `type NAME …;` → type tokens. Union = the 61-entry
list above.

## Related files

- Older, narrower analysis: `docs/genidentname-keyword-filter-proof-impact.md`
- Roundtrip artifact that motivated this (`function if () : int;`):
  `docs/roundtrip-failure-catalog.md` ("Known generator artifacts")
