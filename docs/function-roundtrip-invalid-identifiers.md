# Function round-trip: invalid-identifier vacuous cases & the fix

This document explains why the `genFunction` pretty-print/parse round-trip
property produces a large number of *vacuous* (parse-rejected) test cases, and
sketches a generator change that fixes the root cause. **No code or proofs have
been changed** — this is a design write-up.

## Context

Three property-based tests exercise `genFunction` (defined in
`StrataGenerators/FunctionHasTypeAGen/Core.lean`, proved sound & complete in
`StrataGenerators/FunctionHasTypeAGen.lean`) against Strata's checker and
semantics:

1. **`Function.typeCheck_annotated_sound`** — when `Function.typeCheck` accepts a
   generated (spec-well-typed) function, the output satisfies the declarative
   spec `FuncHasTypeA`. (Tests the `sorry`'d theorem at
   `Strata/Languages/Core/FunctionTypeSpecSound.lean:31`.)
2. **Pretty-print / parse round-trip** — embed a generated `Function` in a
   `Program`, format via `Core.formatProgram`, re-parse via the Core DDM
   dialect, re-format, and compare. Format → parse → re-format should be a fixed
   point.
3. **Type preservation under eval** — `Step.type_preserved` /
   `StepStar.type_preserved` / `eval_denote_sound`.

Both harnesses (`PlausibleTestMain.lean`, pass/fail; `TycheMain.lean`,
visualization) cover all three.

## The observation

Running the Tyche harness at 300 samples, the round-trip panel reports:

- **273 vacuous** (`parsed = no`): the printed function did not parse back.
- **27 parsed** (`parsed = yes`), and **all 27 round-tripped** (`roundtripped =
  yes`) — no format→parse→re-format mismatch.

So the round-trip property itself never fails; it is simply *exercised* on only
~9% of samples. The 273 vacuous cases are printed strings the Core grammar
rejects. The harness correctly scores them as vacuous (a generator artifact, not
a printer/parser bug) rather than as failures.

## Root cause: `String.arbitrary` can produce `""` (and digit-leading names)

Every vacuous case traces to **name generation**. The name generator bottoms out
in Basalt's `String.arbitrary`
(`.lake/packages/basalt/Basalt/Examples/ArbString/Def.lean`):

```lean
def genCharList [Gen G] : G (List Char) :=
  pick (fun _ => pure [])                                   -- ← empty string
       (fun () => do let x ← Char.arbitrary
                     let xs ← genCharList
                     return x :: xs)

def String.arbitrary [Gen G] : G String := String.ofList <$> genCharList
```

and `Char.arbitrary` (`.../ArbChar/Def.lean`) draws from **all 62** alphanumerics
*including digits*:

```lean
def alphanumChars : List Char :=
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList
```

Two consequences:

- The leading `pick []` branch yields the **empty string** `""` with substantial
  probability.
- A generated name can **start with a digit** or be **purely numeric** (`"8"`,
  `"7H"`, `"5"`).

The Core `Ident` token requires a non-empty, letter-initial identifier, so both
forms are rejected on re-parse.

## The three visible failure categories (all one root cause)

Inspecting the JSONL `representation` strings, the vacuous cases split into:

### 1. Empty identifiers (the dominant category)

```
func  : ∀R, . ( : bool) → ...     -- empty function name, empty typearg, empty param
func  :  → Sequence<bool>;         -- empty name + empty parameter name
```

The function name is drawn directly from `String.arbitrary`
(`FunctionHasTypeAGen/Core.lean:96`); type-arg and input names come from
`genTypeArgs` (`:46`) and `genIdents` (`:52`), both `List.dedup <$>
genNameList`. `dedup` keeps a `""` element (and collapses several `""`s to one —
that is the `, .` you see inside `∀R, .`).

### 2. Numeric / digit-leading names in binding positions

```
func f : ∀F, K, . (5 : Map<...     -- parameter named "5"
func  : ∀51mu, XnwKmMak9g, , 8tB. ...   -- typeargs "51mu", "8tB"
```

From `Char.arbitrary` including `0-9`. (Note: a leading digit on the *function*
name is sometimes tolerated by the parser — the parsed-yes list contains `func
9nP`, `func 4` — but a bare numeric in a *binding* position lexes as a `Num`, not
an `Ident`.)

### 3. Empty type slots — a *symptom* of category 1, not a separate bug

```
Map<PiL,  -> >     Sequence<>     int -> )     Map<, >
```

An empty type slot is the printer faithfully rendering an
**`LMonoTy.ftvar ""`** — a type variable whose *name* is the empty string.
`ppType (.ftvar name) = name` (`HasTypeAGen/TestSupport.lean:26`), and the real
`Core.formatProgram` path does the same; when `name = ""` you get a blank where a
type should be.

**The type generator is not at fault.** `genLMonoTy`
(`HasTypeAGen/Core.lean:167`) always builds `.map τ₁ τ₂`, `.arrow τ₁ τ₂`,
`.seq τ` with fully-generated children — it never produces a structurally
truncated type (e.g. a `Map` with one argument). The chain is:

1. `genFunction` builds `typeArgs` via `genTypeArgs depth`
   (`Core.lean:97`), which can contain `""` (category 1).
2. `genFunction` passes *those same* `typeArgs` into `genLMonoTy typeArgs depth`
   for the inputs and output (`Core.lean:98-99`).
3. Inside `genLMonoTy`, `pickTyVar tvars` draws a variable **uniformly from
   `tvars`** (`Core.lean:144-147`) — behaving correctly — so it can pick the
   `""` element and return `ftvar ""`.
4. The printer renders that `ftvar ""` as a blank slot.

Empirical confirmation: in the JSONL, **every** empty-type-slot case also has an
empty *typearg* (a leading `∀,` or interior `, ,`). There are no empty type slots
in functions without an empty typearg. Fixing the empty typearg eliminates the
empty type slots automatically.

## The fix: constrain name generation at one leaf

The single point of leverage is the name generator. Everything downstream
(`genTypeArgs`, `genIdents`, `genInputs`, `pickTyVar`, the function name)
inherits validity for free.

### Generator change (one new definition, two call-site swaps)

**1. A valid-identifier name generator.** Add a `genIdentName : G String` that
generates *by construction*: pick a first character from letters only
(`a-z A-Z`), then append a possibly-empty alphanumeric run (reuse `genCharList`),
and concatenate. This structurally rules out both the empty string (always at
least the leading letter) and digit-leading names (first char is a letter).

*Generate-by-construction, not post-filter.* A filter (`String.arbitrary` then
reject `""`/digit-initial) would introduce generation failures/backtracking and
turn the support into a comprehension-with-predicate, which is far harder to
reason about than the image of a clean generator.

**2. Repoint `genNameList`** (`FunctionHasTypeAGen/Core.lean:41-42`), currently
`listOfMaxLength depth String.arbitrary`, to `listOfMaxLength depth genIdentName`.
Because `genTypeArgs` (`:46`) and `genIdents` (`:52`) both derive from
`genNameList`, this one swap makes **type-arg and input/binder names valid**, and
— via the `ftvar ""` chain above — makes the **empty type slots vanish** with no
change to `genLMonoTy` or `pickTyVar`.

**3. Repoint the function name** in `genFunction` (`Core.lean:96`) from
`String.arbitrary` to `genIdentName`.

That is the entire generator change. `pickTyVar`, `genLMonoTy`, `genInputs`,
`genTypeArgs`, `genIdents` are structurally untouched; they just now consume
valid names.

### Why the empty type slots need no type-generator change

Restated because it's the focus: once `genTypeArgs` can no longer produce `""`,
`pickTyVar` can no longer emit `ftvar ""`, so the empty slots disappear — with
**zero** changes to `genLMonoTy`, `pickTyVar`, or any type-related proof. The
type generator was never wrong; it was being fed a bad variable set. Fixing the
name leaf fixes the type slots for free.

## Proof impact

### Soundness — unaffected

`genFunction_sound` (`FunctionHasTypeAGen.lean:187`) and `genFunction_sound_nil`
(`:224`) destructure the components and immediately discard the name witness
(`⟨name, _hname, …⟩`, `:195`). The only name-related facts used are
`typeArgs.Nodup` (`genTypeArgs_nodup`, `:92`) and `inputs.keys.Nodup`
(`genInputs_support`, `:138`), both from `List.dedup` — true regardless of which
name generator feeds them. `genIdents_nodup` (`:99`),
`genLMonoTy_support`/`genLMonoTy_simple` (used at `:200-202`), and
`allFtvarsIn_freeVars` (`:47`) never mention the name generator. All carry over
verbatim.

### Support bridge lemma — mechanical rename

`mem_support_genNameList_iff` (`:241`) currently says each element is
`∈ support String.arbitrary`; after the swap it says `∈ support genIdentName`.
The proof stays `simp [genNameList, mem_support_listOfMaxLength_iff]` — the
`listOfMaxLength` support characterization is agnostic to the element generator.

### Completeness — localized rewording, same structure

`genFunction_complete` (`:347`): three reachability hypotheses change from
`∈ support String.arbitrary` to `∈ support genIdentName`:

- `hNameReach` (`:359`)
- `hTyArgsReach` (`:361`)
- `hInputNamesReach` (`:363`)

The helpers `genTypeArgs_complete` (`:291`), `genIdents_complete` (`:273`),
`genInputs_complete` (`:301`) are phrased over `∈ support genNameList`, not the
element generator, so their *statements* don't change — only the call sites in
`genFunction_complete` that build those facts via the (reworded)
`mem_support_genNameList_iff`. The name-witness step (`refine ⟨func.name.name,
hNameReach, …⟩`, around `:375`) lines up automatically because `genFunction` now
expects the name from `genIdentName`.

**Meaning:** completeness *narrows* — the generator can no longer produce
empty/digit-leading names, so `genFunction_complete` now covers only functions
with valid identifiers. That is correct and desirable; the reachability
hypotheses exist precisely to characterize the generator's image, and they simply
get stricter. It remains *relative* completeness, as before.

**Residual bottleneck: unchanged.** Fully discharging `hNameReach` for a concrete
function still needs a two-directional support lemma for the name generator.
`genIdentName` is `String.ofList <$> (letter, then genCharList)`, so it still
bottoms out on characterizing `support genCharList` — the same open obligation as
for `String.arbitrary` today (already flagged at `FunctionHasTypeAGen.lean:238-240`
and in `docs/vectorof-listofmaxlength-integration.md` §4/§5). The change neither
creates nor removes this lemma; it only makes the reachability condition
correspond to valid identifiers instead of arbitrary strings.

## Before implementing

1. **Other consumers of `genNameList`.** Grep for call sites before repointing it
   in place. If it's shared (e.g. with the Cmd generator), either the rename
   ripples there too, or introduce a separate `genIdentNameList` and point only
   `genFunction`'s path at it.
2. **Residual non-name failures.** The JSONL shows empty slots are name-derived,
   but an earlier ad-hoc run also surfaced parser errors like `"Map expects 2
   arguments"` that may be *printer*-side. Valid identifiers should absorb the
   large majority of the 273; re-run the round-trip panel afterward and inspect
   whatever remains vacuous. Any surviving non-name failure is a printer/parser
   faithfulness issue living in the `Core.formatProgram` / `lmonoTyToCoreType`
   path, not the generator.

## Summary

- The 273 vacuous round-trip cases are **parse failures**, all rooted in
  `String.arbitrary` producing `""` (dominant) or digit-leading names.
- **Empty type slots** (`Map<X, >`, `int -> `, `Sequence<>`) are `ftvar ""`
  renderings — a downstream symptom of empty *type-arg* names, not a
  type-generator or printer bug.
- **Fix:** one `genIdentName` definition + repoint `genNameList` and the
  function-name draw. Soundness untouched; completeness needs a mechanical
  rename in one bridge lemma plus three reworded hypotheses; empty type slots
  fall out for free with no type-generator/proof change.
- The 27 samples that parsed **all round-tripped cleanly** — the positive signal
  that whenever a generated function is expressible in Core surface syntax,
  format → parse → re-format is a fixed point.
