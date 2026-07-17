# Proof impact of filtering reserved keywords out of `genIdentName`

This document gauges how much of the `FunctionHasTypeAGen` proof development would
need to change if we made `genIdentName` exclude Strata Core **reserved keywords**
(e.g. `if`, `then`, `else`, `forall`, `Map`, `int`, …). The motivation is the one
generator artifact seen in the round-trip harness — `function if () : int;`, where
`if` is a legal identifier by our character rules but a reserved keyword the parser
rejects (see `docs/roundtrip-failure-catalog.md`, "Known generator artifacts").

**TL;DR.** Soundness is untouched. Completeness needs changes, and their magnitude
depends entirely on *how* we filter:

- **Character-level restriction** — impossible for keywords (a keyword like `if`
  is made of perfectly legal characters), so this option does not apply.
- **Whole-string post-filter** (the only viable option) — turns `genIdentName`
  into a `bind`/guard whose support is a *comprehension*, which forces changes to
  **1 bridge lemma + 3 hypotheses in 1 theorem**, plus a new "not a keyword"
  side-condition threaded through completeness. Estimated ~1 rewritten lemma,
  ~3 reworded hypotheses, and 1 new small lemma. It does **not** ripple into the
  helper lemmas or soundness.

## Current baseline (important caveat)

The proof file `StrataGenerators/FunctionHasTypeAGen.lean` **does not currently
build** against the present `genIdentName`. It still refers to `String.arbitrary`
(the pre-`genIdentName` leaf generator) in:

- `mem_support_genNameList_iff` (`:241-244`) — RHS says
  `∈ support (String.arbitrary …)`; errors with `unsolved goals` at `:243`.
- `genFunction_complete` (`:347-...`) — the three reachability hypotheses
  `hNameReach` / `hTyArgsReach` / `hInputNamesReach` (`:359-364`) are stated over
  `String.arbitrary`; errors with an application type mismatch at `:375`.

So there is **already a pending migration** ("`String.arbitrary` → `genIdentName`")
independent of keywords. A keyword filter would layer on top of that migration.
The estimates below describe the delta *relative to a hypothetical world where the
`String.arbitrary → genIdentName` rename is already done* — i.e. the incremental
cost of keyword filtering specifically.

## Why soundness is unaffected (0 changes)

`genFunction_sound` (`:187`) destructures the support witness and **discards the
name witness**:

```lean
obtain ⟨name, _hname, typeArgs, htypeArgs, …⟩ := hfunc   -- :195
```

`_hname` (the proof that the name is in `genIdentName`'s support) is bound and
never used. Soundness only consumes `typeArgs.Nodup` and the input/output facts,
which come from `List.dedup` and `genLMonoTy`, not from the name generator. Any
change to `genIdentName`'s support — narrowing it to exclude keywords included —
leaves `genFunction_sound` and `genFunction_sound_nil` (`:224`) **verbatim**.

## Why the character-level approach doesn't apply

`genIdentName` is built to be legal *by construction*:

```lean
def genIdentName [Gen G] : G String := do
  let x ← genStartChar            -- first char ∈ startChars (letters, _, $)
  let xs ← listOf genRemainingChar -- tail ∈ remainingChars
  return String.ofList (x :: xs)
```

Its "always a legal identifier" guarantee comes from restricting the *alphabet* of
each character. But a reserved keyword such as `if` = `['i','f']` is composed
entirely of legal characters, so no per-character restriction can exclude it.
Keyword exclusion is inherently a **whole-string predicate** (`s ∉ keywords`), and
must be applied *after* the string is assembled. That is what forces the
`bind`/filter shape below, and with it the proof changes.

## The completeness chain, and where a filter cuts it

Completeness flows through this chain (all in `FunctionHasTypeAGen.lean`):

```
genFunction_complete (:347)
  └─ mem_support_genNameList_iff (:241)   ← THE bridge lemma
       └─ genNameList = listOfMaxLength depth genIdentName   (Core.lean:117)
            └─ mem_support_listOfMaxLength_iff  (element-wise support, from Basalt)
```

The bridge lemma is what makes the whole thing tractable today:

```lean
theorem mem_support_genNameList_iff (depth : Nat) (l : List String) :
    l ∈ SetGen.support (genNameList … depth) ↔
      l.length ≤ depth ∧ ∀ s ∈ l, s ∈ SetGen.support (genIdentName …) := by
  simp only [genNameList, mem_support_listOfMaxLength_iff]
```

The one-line proof works because `genNameList` is *exactly* `listOfMaxLength depth
genIdentName`, and `listOfMaxLength`'s support is characterized element-wise. The
element generator (`genIdentName`) appears only opaquely — its support is carried
as an abstract `∈ support genIdentName`.

### What changes with a whole-string filter

Suppose we define:

```lean
def genIdentNameNK [Gen G] : G String := do
  let s ← genIdentName
  if isKeyword s then pure <fallback>   -- or a retry/guard combinator
  else pure s
```

(any post-filter has this bind-with-conditional shape). Then:

1. **`support genIdentNameNK` is no longer atomic.** It becomes a set defined by a
   comprehension over `support genIdentName` intersected with `{s | ¬ isKeyword s}`
   (modulo how the fallback is handled). We need a **new support lemma**:

   ```lean
   theorem mem_support_genIdentNameNK_iff (s : String) :
     s ∈ support genIdentNameNK ↔ s ∈ support genIdentName ∧ ¬ isKeyword s
   ```

   Its proof must reason about the `bind`/`if` (via `mem_support_bind_iff` and a
   case split on `isKeyword`), and — critically — must handle the **fallback
   branch** (what a filtered-out draw becomes). If the fallback is a fixed string
   like `"x"`, the `↔` above is slightly wrong (the fallback is reachable too), so
   the honest statement is messier. A *retry/`Gen.backtrack`* style filter avoids
   polluting the image but has its own (harder) support characterization. **This
   is the single biggest new proof burden.**

2. **`mem_support_genNameList_iff` gains a conjunct.** Its RHS per-name condition
   becomes `s ∈ support genIdentName ∧ ¬ isKeyword s`. The `simp only [genNameList,
   mem_support_listOfMaxLength_iff]` proof still fires (the `listOfMaxLength`
   characterization is agnostic to the element generator), but it now bottoms out
   on `support genIdentNameNK` rather than `support genIdentName`, so it must chain
   through the new lemma from (1). Small edit, but no longer a one-liner.

3. **Three hypotheses in `genFunction_complete` gain a side-condition.** The
   reachability hypotheses (`:359-364`)

   - `hNameReach : func.name.name ∈ support genIdentName`
   - `hTyArgsReach : ∀ s ∈ func.typeArgs, s ∈ support genIdentName`
   - `hInputNamesReach : ∀ s ∈ func.inputs.keys.map (·.name), s ∈ support genIdentName`

   each need `∧ ¬ isKeyword …` (or a separate `∀ … ¬ isKeyword s` hypothesis).
   This is a **statement change**, and it *narrows* the theorem: `genFunction_complete`
   now covers only functions whose every name is a non-keyword identifier — which
   is correct and desirable (a keyword-named function genuinely cannot be produced).
   The proof body (`:373-...`) changes only at the two call sites that feed
   `mem_support_genNameList_iff` (`:383`, `:387`), to also pass the `¬ isKeyword`
   facts.

### What does NOT change

- **The helper lemmas are phrased over `genNameList`, not the leaf**, so their
  *statements* are unchanged: `genIdents_complete` (`:273`), `genTypeArgs_complete`
  (`:291`), `genInputs_complete` (`:301`), `mapM_genInputs_complete` (`:250`). They
  consume `∈ support (genNameList …)` opaquely and never mention the element
  generator. Only the *call sites* inside `genFunction_complete` that construct
  those `genNameList` facts (via the bridge lemma) are touched.
- **`genIdents_nodup` (`:99`) and all `Nodup`/`dedup` reasoning** — unaffected
  (dedup is oblivious to which strings it dedups).
- **Soundness** — unaffected (see above).

## Magnitude estimate

Relative to a codebase where the `String.arbitrary → genIdentName` rename is
already complete, adding a keyword filter costs approximately:

| Change | Kind | Effort |
|---|---|---|
| New `genIdentNameNK` definition | generator | trivial |
| New `mem_support_genIdentNameNK_iff` lemma | **new proof** | **moderate–hard** (bind + `if` + fallback/backtrack reasoning; this is the crux) |
| `mem_support_genNameList_iff` RHS + proof | edit | small (add conjunct, chain through new lemma) |
| 3 reachability hypotheses in `genFunction_complete` | statement change | small (mechanical) |
| 2 call sites in `genFunction_complete` proof body | edit | small |
| Helper lemmas (`gen*_complete`, `mapM_…`) | — | none |
| Soundness (`genFunction_sound{,_nil}`) | — | none |

So: **one genuinely new lemma (the hard part), one bridge-lemma edit, three
hypothesis rewordings, two call-site edits — all localized to `genFunction_complete`
and its immediate bridge.** No ripple into the helper layer or soundness.

## Recommendation

Because the payoff is small (the `if` collision was ~0.2% of round-trip failures,
a single case) and the cost centers on the one genuinely tricky lemma
(`mem_support_genIdentNameNK_iff`, whose difficulty depends on the still-open
`support genIdentName` characterization — see the residual bottleneck noted at
`FunctionHasTypeAGen.lean:238`), the cheaper path is to **filter reserved keywords
at the harness level** rather than in the generator: when reporting a round-trip
counterexample, skip or relabel any whose name is a reserved keyword. That keeps
the generator and its proofs untouched while still preventing the false positive
in bug reports.

Filtering *inside* `genIdentName` is only worth it if we want the "every generated
name is a legal, parser-acceptable identifier" guarantee to hold at the generator
level (and eventually be provable) — in which case the changes above are the scope,
and the `mem_support_genIdentNameNK_iff` lemma is the item to budget for.
