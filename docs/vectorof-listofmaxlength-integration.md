# Adopting Basalt's `vectorOf` / `listOfMaxLength` for the name generators

This doc records whether — and how — the `vectorOf` / `listOfMaxLength`
combinators added to Basalt in
[hgoldstein95/basalt#8](https://github.com/hgoldstein95/basalt/pull/8) (not yet
merged) could replace the bespoke `genNameList` / `genIdents` generators in
`StrataGenerators/FunctionHasTypeAGen/Core.lean`, and what their support lemmas
would buy the function-generator soundness/completeness proofs
(`StrataGenerators/FunctionHasTypeAGen.lean`).

> Convention (as in `docs/side-conditions.md`): "support" means
> `SetGen.support (gen … (G := SetGen.Set))`. Soundness = `support → property`;
> completeness = `property → support`.

## TL;DR

- **Yes, the support lemmas would help completeness** — but only after being
  **ported from `SPMF` to `SetGen.Set`**, and only up to the residual bottleneck
  of `String.arbitrary` (see §4).
- **They do nothing for soundness** — `Nodup` comes from `List.dedup` alone,
  independent of the underlying list generator (§3).
- **Rewriting `genCharList` on top of `listOfMaxLength` is a semantics change,
  not a refactor**, and would *weaken* the existing repo lemmas. Only worth doing
  for Basalt's own PMF/termination goals, and only if paired with a public
  two-way `String.arbitrary` support lemma (§5).

## 1. What the PR provides

Definitions (`Basalt/Combinators.lean`):

```lean
def vectorOf [Gen G] (n : Nat) (g : G α) : G (List α) :=
  List.foldr (fun m acc => do
    let x ← m; let xs ← acc; pure (x :: xs)) (pure []) (List.replicate n g)

def listOfMaxLength [Gen G] (n : Nat) (g : G α) : G (List α) := do
  let ⟨k, _⟩ ← ULift.down <$> RandomChoice.choose 0 n (Nat.zero_le n)
  vectorOf k g
```

Lemmas, **stated over `SPMF`** (`Basalt/SPMF/Support.lean`,
`Basalt/SPMF/Termination.lean`):

```lean
theorem support_vectorOf {n : Nat} {g : SPMF α} :
    support (vectorOf n g) = { xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ g.support }
@[simp] theorem mem_support_vectorOf_iff {n : Nat} {g : SPMF α} :
    xs ∈ (vectorOf n g).support ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ g.support
theorem support_listOfMaxLength {n : Nat} {g : SPMF α} :
    support (listOfMaxLength n g) = { xs | xs.length ≤ n ∧ ∀ x ∈ xs, x ∈ g.support }
@[simp] theorem mem_support_listOfMaxLength_iff {n : Nat} {g : SPMF α} :
    xs ∈ (listOfMaxLength n g).support ↔ xs.length ≤ n ∧ ∀ x ∈ xs, x ∈ g.support
theorem IsPMF_vectorOf       {g : SPMF α} (hg : IsPMF g) : IsPMF (vectorOf n g)
theorem IsPMF_listOfMaxLength {g : SPMF α} (hg : IsPMF g) : IsPMF (listOfMaxLength n g)
```

Monotonicity lemmas (`@[partial_fixpoint_monotone]`) are `Gen`-generic
(`[Gen G]`, any `PartialOrder γ`), not SPMF-specific. The PR touches
`Basalt/Examples/ArbList.lean` (a new `List.arbitrary'` example) — **it does not
change `genCharList`.**

## 2. How close is `genNameList` already?

`genNameList` (`FunctionHasTypeAGen/Core.lean:37`) is definitionally almost
exactly `listOfMaxLength depth String.arbitrary`:

```lean
-- ours
genNameList depth =
  do let k ← choose 0 depth _
     (List.replicate k.down.val ()).mapM (fun _ => String.arbitrary)
-- PR
listOfMaxLength n g =
  do let ⟨k,_⟩ ← ULift.down <$> choose 0 n _
     vectorOf k g
```

The only gap is the body shape:

- ours: `(List.replicate k ()).mapM (fun _ => g)`
- PR:   `vectorOf k g = foldr (…) (pure []) (List.replicate k g)`

These produce the same set, but are **not syntactically equal**, so
`genNameList := listOfMaxLength depth String.arbitrary` requires a small
bridging lemma (a `rfl`/rewrite equating the `replicate … |>.mapM` form with the
`vectorOf` `foldr` form), or adopting `vectorOf`'s shape directly.

## 3. Impact on soundness: none

`genFunction_sound` (`FunctionHasTypeAGen.lean:187`) never inspects
`genNameList`'s support. The `inputsNodup` / `typeArgsNodup` obligations are
discharged purely from `List.dedup`:

- `genTypeArgs_nodup` / `genIdents_nodup` (`FunctionHasTypeAGen.lean:92,99`) use
  only `nodup_dedup` (`FunctionHasTypeAGen/Dedup.lean`) and **discard** the
  membership witness for the underlying list.

So the `vectorOf` / `listOfMaxLength` support lemmas add nothing to the
soundness direction.

## 4. Impact on completeness: real, after a SetGen port

`genFunction_complete` (`FunctionHasTypeAGen.lean:329`) currently takes three
**opaque** reachability hypotheses, because the repo has no support
characterization for `genNameList`:

| Hypothesis | Current (opaque) form |
|---|---|
| `hNameReach` | `func.name.name ∈ support String.arbitrary` |
| `hTyArgsReach` | `func.typeArgs ∈ support (genNameList depth)` |
| `hInputNamesReach` | `func.inputs.keys.map (·.name) ∈ support (genNameList depth)` |

With a **SetGen-ported** `mem_support_listOfMaxLength_iff`, the two
`genNameList` hypotheses could be replaced by a transparent side-condition:

```lean
l ∈ support (genNameList depth) ↔ l.length ≤ depth ∧ ∀ s ∈ l, s ∈ support String.arbitrary
```

i.e. "at most `depth` names, each an alphanumeric string." That is strictly more
legible and reusable than the opaque `∈ support (genNameList …)` — and the same
lemma would serve any other bounded-list generator (e.g. fuel-bounded command
sequences in `genCmds`).

**Two caveats:**

1. **The SPMF lemmas do not transfer.** This repo runs everything over
   `SetGen.Set`; the PR's `support_*` / `IsPMF_*` lemmas are over `SPMF`. They
   must be **re-proved over `Set`** — mechanically similar to the existing
   `mem_mapM_iff` (`HasTypeAGen.lean:3242`) and `genAlphanumList_support_set`
   (`HasTypeAGen.lean:1206`). The `monotone_*` lemmas are `Gen`-generic and
   carry over as-is; the `IsPMF_*` lemmas are SPMF-only and irrelevant to us.
2. **It still bottoms out at `String.arbitrary`.** Even after the port, the iff
   above only reduces name-list reachability to per-name
   `s ∈ support String.arbitrary`, which in this repo is characterized only
   **one-directionally and privately**: `String_arbitrary_support_set`
   (`HasTypeAGen.lean:1222`) proves `alphanumeric → in support`, not the
   converse, and is `private`. So a fully concrete completeness statement needs
   §5 as well.

## 5. Rewriting `genCharList` via `vectorOf` / `listOfMaxLength`: caution

This is a **semantics change, not a refactor**:

- Current `genCharList` (`Basalt/Examples/ArbString/Def.lean`) is an
  **unbounded, geometric-length** list (`partial_fixpoint`, 50/50
  stop/continue). `listOfMaxLength n` is **bounded** (length ≤ n). So
  `String.arbitrary` would change from "any-length alphanumeric string" to
  "alphanumeric string of length ≤ n," requiring an `n` in its signature.
- This **weakens the existing repo lemmas** `genAlphanumList_support_set` and
  `String_arbitrary_support_set`, which today assert *every* alphanumeric
  list/string is reachable. Post-change they hold only up to the bound.
- Downstream, name reachability in `genFunction_complete` would inherit a
  per-name length bound — a strictly stronger side-condition than "alphanumeric."

The upside of the rewrite is **for Basalt, not us**: removing the
`partial_fixpoint` makes `String.arbitrary` a genuine PMF (that's what
`IsPMF_listOfMaxLength` buys). If Basalt wants that independently, fine — but it
should be paired with a public **two-directional** `String.arbitrary` support
lemma so our completeness statement does not regress:

```lean
theorem String_arbitrary_support (s : String) :
    s ∈ support String.arbitrary ↔ ∀ c ∈ s.toList, c ∈ alphanumChars
```

## 6. Recommendation / action items

Priority order:

1. **Port `vectorOf` + `listOfMaxLength` and their `mem_support_*_iff` to
   `SetGen.Set`** (in this repo, or the SetGen-flavored corner of Basalt). Then
   redefine `genNameList := listOfMaxLength depth String.arbitrary` (with the
   §2 bridging lemma) and concretize the three §4 completeness hypotheses.
2. **Add a public two-way `String.arbitrary` support lemma** (§5). This is the
   actual bottleneck for fully transparent name reachability — more so than the
   list combinator.
3. **Rewriting `genCharList`**: only if Basalt wants the PMF/termination win;
   treat it as a semantics change and land it together with item 2.

None of this is required for the current proofs, which are complete and
`sorry`-free — it is a legibility/reuse improvement to the completeness
side-conditions. Items 1–2 can be gated on PR #8 landing, or the definitions can
be vendored locally in the meantime.
