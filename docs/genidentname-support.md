# `genIdentName` — support characterised in both directions

Closes item 1 of issue #66 ("What is missing before we can prove `genProgram`
complete"), which named this as *"the biggest lever"* and *"the highest-value
item"*: it removes name-reachability side conditions from every completeness
proof in the package, not just the program-level one.

## The result

`StrataGenerators/FunctionHasTypeAGen/IdentName.lean`:

```lean
theorem mem_support_genIdentName_iff (s : String) :
    s ∈ SetGen.support (genIdentName (G := SetGen.Set)) ↔
      IsGenIdentName s ∧ isReservedKeyword s = false
```

where `IsGenIdentName s` says `s.toList = c :: cs` with `c ∈ startChars` and
every `c' ∈ cs` in `remainingChars`. In words:

> `genIdentName` reaches **exactly** the strings that Core's lexer accepts as a
> bare identifier and that are not reserved keywords.

Both conjuncts are decidable (`decidableIsGenIdentName` is provided), so for a
concrete name the side condition closes by `decide`.

Three presentations of the same fact, pick by use:

| lemma | right-hand side | use when |
| --- | --- | --- |
| `mem_support_genIdentName_iff` | `IsGenIdentName s ∧ isReservedKeyword s = false` | general reasoning |
| `mem_support_genIdentName_iff_isId` | Core's `isIdFirst`/`isIdRest` predicates | explaining *what* the support is; no generator internals appear |
| `mem_support_genIdentName_iff'` | `IsGenIdentName s ∧ s ∉ reservedKeywordsList` | the name is **concrete** — this is the `decide`-able one |

The primed version exists for a practical reason: `isReservedKeyword` is a
`Std.HashSet` lookup, which the kernel cannot reduce, so `decide +kernel` gets
stuck on it. Routing through `isReservedKeyword_eq_list_contains` puts the
condition back on a concrete `List String`, where it does reduce.

## Why the statement is not circular

Phrased over `startChars`/`remainingChars` alone, the lemma would risk saying
only *"the generator reaches the names it can spell"* — leaving open whether some
name a well-typed program may legitimately contain is unspellable. The file
closes that by proving the generator's alphabets are **equal** to the DDM lexer's
identifier character classes:

```lean
theorem mem_startChars_iff      (c : Char) : c ∈ startChars      ↔ isIdFirst c
theorem mem_remainingChars_iff  (c : Char) : c ∈ remainingChars  ↔ isIdRest c
```

The `⊆` directions are `decide`. The `⊇` directions are the real content — they
say `alphaChars` really is *all* the ASCII letters (not a subset) and the digit
block really is all ten digits, proved by exhibiting the index into the
`List.range` blocks (`alphaChars_of_isAlpha`, `digits_of_isDigit`).

So `IsGenIdentName` is the spec-level notion "legal bare Core identifier", and
the support lemma is a genuine completeness result over names.

**Caveat, deliberately recorded:** DDM's `strataIsIdFirst`/`strataIsIdRest` are
`private` in `StrataDDM/Parser.lean` and so cannot be referenced; they are
transcribed as `isIdFirst`/`isIdRest` in `IdentName.lean`. If the lexer's classes
ever change, those transcriptions must be updated in step — the equality proofs
will not catch the drift on their own.

## The one non-obvious point: `dodgeKeyword` does not enlarge the support

`genIdentName` post-processes each raw draw with `dodgeKeyword`, which maps a
reserved keyword `k` to `k ++ "_"`. One might expect the support to need two
cases (raw draws, plus dodged keywords). It does not: `k ++ "_"` is *itself* a raw
draw — `k`'s leading character is a letter and `'_' ∈ remainingChars` — so the
dodge branch only re-reaches strings the direct branch already reaches. Hence the
single clean right-hand side above.

The only visible effect of `dodgeKeyword` on the support is therefore
*subtractive*: it removes the keywords themselves, which is exactly the
`isReservedKeyword s = false` conjunct. `"if"` is a perfectly legal identifier
*shape* that the generator provably cannot emit; `"if_"` is reachable, but only
because it is an ordinary draw.

## Enabling lemma: `listOf`'s support, both directions

`genIdentName`'s tail run is a `listOf`, whose `SetGen.Set` port previously had
only the forward direction (`SetGen.mem_support_listOf`). Added in
`StrataGenerators/SetGen/Support.lean`:

```lean
theorem SetGen.mem_support_listOf_iff {g : Set α} {xs : List α} :
    xs ∈ support (listOf g) ↔ ∀ x ∈ xs, x ∈ support g
```

No length bound appears — unlike `listOfMaxLength`, `listOf`'s support is *all*
lists over the element support, which is why identifiers of any length are
reachable. (The `SPMF` interpretation already had this as `support_listOf` in
`Basalt.SPMF.Support`; this is the `SetGen.Set` counterpart.)

## Downstream effect

The three sites that previously took `s ∈ support genIdentName` as an unanalysed
hypothesis now have side-condition-discharged companions:

| original (hypothesis assumed) | new (syntactic, decidable) |
| --- | --- |
| `DatatypeGen.genFreshName_complete` | `genFreshName_complete_of_syntactic` |
| `Stmt.SpecComplete.genFreshLabel_complete` | `genFreshLabel_complete_of_syntactic` |
| `Stmt.genTypeConstructor_complete` | `genTypeConstructor_complete_of_syntactic` |

The originals are kept — callers thread that form — but the hypothesis is no
longer an assumption about the generator, just a decidable check on a name.

**Scope, stated precisely.** Around 43 statements across `DatatypeGenProofs`,
`StmtHasTypeAGen{,Complete}`, `FunctionHasTypeAGen` and `ProcedureHasTypeAGen`
still *mention* `∈ support genIdentName` in their signatures. That is deliberate
and is not remaining work in the mathematical sense: they all bottom out in the
three leaf generators above, so the hypothesis is now *derivable* wherever it
appears rather than assumed. Rewriting all 43 signatures to take
`IsGenIdentName` instead would be mechanical churn touching every caller; the
useful content — that the condition is decidable and provable — is done. Convert
them opportunistically when a proof is being edited anyway.

The one-directional lemmas `genIdentName_not_keyword` and `genIdentName_no_space`
are now corollaries (they were proved directly from the two draws before, in
`FunctionHasTypeAGen.lean`; they moved to `IdentName.lean` under the same names
and namespace, so all use sites still resolve). `genIdentName_ne_empty` is new.

## Verification

* Whole library builds clean.
* All new results are `sorry`-free and depend only on `propext`,
  `Classical.choice`, `Quot.sound`. (`HasTypeAGen.lean:3511` carries a
  pre-existing `sorry` unrelated to names — Strata's unifier
  matching-completeness, present in the baseline build.)
* `FunctionHasTypeAGen/IdentNameTests.lean` machine-checks **tightness** — that
  the `iff`'s right-hand side is not accidentally trivial. It records reachable
  names (`foo`, `_x`, `$x`, `x$y.z'w?v!u@t0`, `if_`, the all-`x` fallbacks) and,
  more importantly, names that are provably **un**reachable: reserved keywords
  (`if`, `procedure`), the empty name, digit-initial names (`1x`), pipe-only
  characters (`a|b`, `a\b`), and space-containing names (`a b`). All by `decide`.

## What this does *not* close

Item 1 only. The rest of #66 stands *except* `ArityOk` (#65), which upstream's
`argsWellKinded` closed — see `mutualadtwf-arity-gap.md` and issue #101:
the four missing per-step reachability lemmas, the `recFuncBlock` generator, and
expression-level incompleteness (#64) — which remains the strict prerequisite for
a *tight* program-level statement.
