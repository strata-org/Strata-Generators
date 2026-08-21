import StrataGenerators.SetGen
import StrataGenerators.FunctionHasTypeAGen.Core

open RandomChoice SetGen
open scoped SetGen.Set

/-!
# The support of `genIdentName`, in both directions

`genIdentName` is the only source of names in this package. Each function name, type
parameter, parameter name, statement label, datatype name, constructor name and field name
comes from it. Some names come from it directly. The other names come through
`genNameList`, `DatatypeGen.genFreshName`, or the generator for a statement label.

`mem_support_genIdentName_iff` gives the support exactly:

```
s ∈ support genIdentName  ↔  IsGenIdentName s ∧ isReservedKeyword s = false
```

`IsGenIdentName s` is a syntactic condition on `s.toList`. The list is not empty.
Its first character is in `startChars`. Each of the other characters is in
`remainingChars`. Both conjuncts are decidable. Therefore the instance
`decidableIsGenIdentName` lets `decide` close the condition for a concrete name.

A completeness proof needs the backward direction: a name that a well-typed
program contains must be a name that the generator can draw.
`mem_support_genIdentName_of_syntactic` gives that step.

## `dodgeKeyword` does not make the support larger

`genIdentName` sends each raw draw through `dodgeKeyword`, which maps a reserved
keyword `k` to `k ++ "_"`. You can expect two cases in the support: the raw
draws, and the dodged keywords. Only one case is necessary. The string `k ++ "_"`
is itself a raw draw, because the first character of `k` is a letter and
`'_' ∈ remainingChars`. Therefore the dodge branch reaches only strings that the
direct branch reaches also.

The one effect of `dodgeKeyword` on the support is subtractive. It removes the
keywords, and this is the conjunct `isReservedKeyword s = false`.

## Contents

- the theorems that say that no name from `dodgeKeyword` or from `genIdentName` is a
  keyword. These results are in this file, and not in the main module for a function, so
  that the proofs for a datatype can use them without the whole development of the
  generator for a function;
- `IsGenIdentName` and its decidability;
- `mem_support_genIdentName_iff`, the support lemma in both directions;
- corollaries: the one-directional lemmas, and the
  `mem_support_genIdentName_of_*` helpers that discharge the side condition.
-/

namespace StrataGenerators.Function

-- ── A generated name is never a keyword ──────────────────────────────
-- `genIdentName` sends each candidate through `dodgeKeyword`. Therefore it never
-- gives a reserved Strata Core keyword. The lemmas below make this guarantee
-- explicit and provable. It is a soundness property of the name generator. No
-- generated function name, type argument or parameter name is a reserved word.
-- Therefore the parser rejects no such name in identifier position.

/-- No character list of a reserved keyword ends with `_`. The check is over the
    concrete source list `reservedKeywordsList`. -/
theorem no_keyword_ends_underscore :
    ∀ k ∈ reservedKeywordsList, k.toList.getLast? ≠ some '_' := by decide +kernel

/-- `s ++ "_"` is never a reserved keyword. It ends with `_`, and no keyword ends
    with `_`. The statement uses `isReservedKeyword`, which is the `HashSet`
    lookup. The proof goes through `isReservedKeyword_eq_list_contains` to
    `reservedKeywordsList`. -/
theorem append_underscore_not_keyword (s : String) :
    isReservedKeyword (s ++ "_") = false := by
  rw [isReservedKeyword_eq_list_contains, Bool.eq_false_iff]
  intro hc
  rw [List.contains_iff_mem] at hc
  have hlast : (s ++ "_").toList.getLast? = some '_' := by
    rw [String.toList_append]; exact List.getLast?_concat
  exact no_keyword_ends_underscore _ hc hlast

/-- `dodgeKeyword` never gives a reserved keyword. It maps a keyword `k` to
    `k ++ "_"`, which is not a keyword. It returns each other name without a
    change. -/
theorem dodgeKeyword_not_keyword (s : String) :
    isReservedKeyword (dodgeKeyword s) = false := by
  unfold dodgeKeyword
  split
  · rename_i h
    exact append_underscore_not_keyword s
  · rename_i h
    simpa using h

/-- `dodgeKeyword` is the identity on a name that is not a reserved keyword. The
    backward direction of the support lemma needs this fact. The generator returns
    a target name that is not a keyword without a change. Therefore the raw
    character draws are enough to reach it. -/
theorem dodgeKeyword_eq_self {s : String} (h : isReservedKeyword s = false) :
    dodgeKeyword s = s := by
  unfold dodgeKeyword; simp [h]

/-- `dodgeKeyword` never puts a space into a name. The keyword branch appends
    `"_"`, which is not a space. The other branch returns the string without a
    change. -/
theorem dodgeKeyword_no_space (s : String) (h : ' ' ∉ s.toList) :
    ' ' ∉ (dodgeKeyword s).toList := by
  unfold dodgeKeyword
  split
  · rw [String.toList_append]
    intro hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · exact h h1
    · simp at h2
  · exact h

-- ── The alphabets of the generator are the identifier classes of Core ──
--
-- `IsGenIdentName` below is phrased over `startChars` and `remainingChars`, which
-- are the character lists of the generator. Alone, this makes the support lemma
-- almost circular as a completeness statement. It then says only that the
-- generator reaches the names that it can spell. It leaves open the question
-- whether a well-typed program can contain a name that the generator cannot
-- spell.
--
-- This section answers that question. `startChars` and `remainingChars` are equal
-- to the character classes `strataIsIdFirst` and `strataIsIdRest` of the DDM
-- lexer. Therefore `IsGenIdentName` is the spec-level notion "legal Core
-- identifier", and the support lemma is a true completeness result for names.
--
-- `strataIsIdFirst` and `strataIsIdRest` are `private` in the parser of DDM, so this file cannot
-- refer to them. `isIdFirst` and `isIdRest` below are copies of them. If the character classes of
-- the lexer change, you must change these two copies also. The proofs of equality below cannot
-- find such a difference.

/-- A copy of `strataIsIdFirst`, which is `private` in the parser of DDM. These are the
    characters that are legal in the first position of a bare Core identifier. -/
def isIdFirst (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'

/-- A copy of `strataIsIdRest`, which is `private` in the parser of DDM. These are the
    characters that are legal after the first position of a bare Core identifier. -/
def isIdRest (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '?' || c == '!' ||
  c == '$' || c == '@'

/-- Each character that the generator can put in first position is legal there for
    the lexer. This is the soundness direction. `decide` closes it, because
    `startChars` is a concrete finite list. -/
theorem startChars_isIdFirst : ∀ c ∈ startChars, isIdFirst c := by decide +kernel

/-- Each character that the generator can put after the first position is legal
    there for the lexer. -/
theorem remainingChars_isIdRest : ∀ c ∈ remainingChars, isIdRest c := by
  decide +kernel

/-- Each upper-case ASCII letter is in `alphaChars`. It is at index `c - 'A'` of
    the first `List.range 26` block. -/
theorem alphaChars_of_upper (c : Char) (h1 : c.val ≥ 'A'.val) (h2 : c.val ≤ 'Z'.val) :
    c ∈ alphaChars := by
  have hn1 : c.val.toNat ≥ 65 := by simpa using UInt32.le_iff_toNat_le.mp h1
  have hn2 : c.val.toNat ≤ 90 := by simpa using UInt32.le_iff_toNat_le.mp h2
  have hA : 'A'.toNat = 65 := by decide +kernel
  simp only [alphaChars, List.mem_append]
  left; rw [List.mem_map]
  refine ⟨c.val.toNat - 65, by rw [List.mem_range]; omega, ?_⟩
  rw [hA]
  have hidx : (65 + (c.val.toNat - 65)) = c.val.toNat := by omega
  rw [hidx]; exact Char.ofNat_toNat c

/-- Each lower-case ASCII letter is in `alphaChars`. It is at index `c - 'a'` of
    the second block. -/
theorem alphaChars_of_lower (c : Char) (h1 : c.val ≥ 'a'.val) (h2 : c.val ≤ 'z'.val) :
    c ∈ alphaChars := by
  have hn1 : c.val.toNat ≥ 97 := by simpa using UInt32.le_iff_toNat_le.mp h1
  have hn2 : c.val.toNat ≤ 122 := by simpa using UInt32.le_iff_toNat_le.mp h2
  have ha : 'a'.toNat = 97 := by decide +kernel
  simp only [alphaChars, List.mem_append]
  right; rw [List.mem_map]
  refine ⟨c.val.toNat - 97, by rw [List.mem_range]; omega, ?_⟩
  rw [ha]
  have hidx : (97 + (c.val.toNat - 97)) = c.val.toNat := by omega
  rw [hidx]; exact Char.ofNat_toNat c

/-- `alphaChars` contains each `Char.isAlpha` character. Thus it holds all of the
    ASCII letters, and not a subset of them. -/
theorem alphaChars_of_isAlpha (c : Char) (h : c.isAlpha = true) : c ∈ alphaChars := by
  rw [Char.isAlpha, Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Char.isUpper, decide_eq_true_eq] at h
    exact alphaChars_of_upper c h.1 h.2
  · rw [Char.isLower, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    exact alphaChars_of_lower c h.1 h.2

/-- The digit block of `remainingChars` contains each `Char.isDigit` character. -/
theorem digits_of_isDigit (c : Char) (h : c.isDigit = true) :
    c ∈ "0123456789".toList := by
  rw [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  have hn1 : c.val.toNat ≥ 48 := by simpa using UInt32.le_iff_toNat_le.mp h.1
  have hn2 : c.val.toNat ≤ 57 := by simpa using UInt32.le_iff_toNat_le.mp h.2
  have h0 : '0'.toNat = 48 := by decide +kernel
  rw [show "0123456789".toList
      = (List.range 10).map (fun n => Char.ofNat ('0'.toNat + n)) from by decide +kernel]
  rw [List.mem_map]
  refine ⟨c.val.toNat - 48, by rw [List.mem_range]; omega, ?_⟩
  rw [h0]
  have hidx : (48 + (c.val.toNat - 48)) = c.val.toNat := by omega
  rw [hidx]; exact Char.ofNat_toNat c

/-- **`startChars` holds all of `strataIsIdFirst`.** With `startChars_isIdFirst`,
    this makes the two character classes equal. Therefore the condition on the
    first character in `IsGenIdentName` is the condition of Core. -/
theorem startChars_of_isIdFirst (c : Char) (h : isIdFirst c = true) : c ∈ startChars := by
  rw [isIdFirst, Bool.or_eq_true, Bool.or_eq_true] at h
  simp only [startChars, List.mem_append]
  rcases h with (h | h) | h
  · exact Or.inl (alphaChars_of_isAlpha c h)
  · rw [beq_iff_eq] at h; subst h; right; decide +kernel
  · rw [beq_iff_eq] at h; subst h; right; decide +kernel

/-- **`remainingChars` holds all of `strataIsIdRest`.** With
    `remainingChars_isIdRest`, this makes the two character classes equal.
    Therefore the condition on the other characters in `IsGenIdentName` is the
    condition of Core. -/
theorem remainingChars_of_isIdRest (c : Char) (h : isIdRest c = true) :
    c ∈ remainingChars := by
  simp only [isIdRest, Bool.or_eq_true, beq_iff_eq] at h
  simp only [remainingChars, startChars, List.mem_append]
  rcases h with ((((((h|h)|h)|h)|h)|h)|h)|h
  · rw [Char.isAlphanum, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl (alphaChars_of_isAlpha c h)))
    · exact Or.inl (Or.inr (digits_of_isDigit c h))
  all_goals (subst h; first
    | (left; left; right; decide +kernel)
    | (left; right; decide +kernel)
    | (right; decide +kernel))

/-- **The first-character alphabet of the generator is equal to the alphabet of
    Core.** -/
theorem mem_startChars_iff (c : Char) : c ∈ startChars ↔ isIdFirst c :=
  ⟨fun h => startChars_isIdFirst c h, startChars_of_isIdFirst c⟩

/-- **The alphabet of the generator after the first character is equal to the
    alphabet of Core.** -/
theorem mem_remainingChars_iff (c : Char) : c ∈ remainingChars ↔ isIdRest c :=
  ⟨fun h => remainingChars_isIdRest c h, remainingChars_of_isIdRest c⟩

-- ── The syntactic condition for a drawable identifier ────────────────

/-- **A name that `genIdentName` can draw, in syntactic form.** The string `s` is
    not empty. Its first character is a character that the generator can put in
    first position. These characters are `startChars`: the letters, `_` and `$`,
    and all of them are in `strataIsIdFirst` of Core. Each of the other characters
    is a character that the generator can put after the first position. These
    characters are `remainingChars`: `startChars`, the digits, and `' . ? ! $ @`,
    and all of them are in `strataIsIdRest` of Core.

    The condition uses an existential over the split into a first character and a
    list of other characters. It does not use `List.head?` and `List.tail`, because
    both directions of `mem_support_genIdentName_iff` must destructure it
    directly. -/
def IsGenIdentName (s : String) : Prop :=
  ∃ c cs, s.toList = c :: cs ∧ c ∈ startChars ∧ ∀ c' ∈ cs, c' ∈ remainingChars

/-- `IsGenIdentName` is decidable. It splits a finite character list into a first
    character and the other characters, then compares them against two concrete
    character lists. `isReservedKeyword` is decidable also. Therefore `decide` can
    close the right-hand side of `mem_support_genIdentName_iff` for a concrete
    name, and the side condition on name reachability needs no manual work. -/
instance decidableIsGenIdentName (s : String) : Decidable (IsGenIdentName s) :=
  match h : s.toList with
  | [] =>
    .isFalse (by
      rintro ⟨c, cs, hsplit, _, _⟩
      rw [h] at hsplit
      exact absurd hsplit (by simp))
  | c :: cs =>
    if hc : c ∈ startChars ∧ ∀ c' ∈ cs, c' ∈ remainingChars then
      .isTrue ⟨c, cs, h, hc.1, hc.2⟩
    else
      .isFalse (by
        rintro ⟨c', cs', hsplit, hc', hcs'⟩
        rw [h] at hsplit
        obtain ⟨rfl, rfl⟩ := List.cons.inj hsplit
        exact hc ⟨hc', hcs'⟩)

-- ── The support lemma in both directions ─────────────────────────────

/-- **Support of `genIdentName`, in both directions.**

    `genIdentName` draws the first character from `startChars`. Then it draws a run
    of characters from `remainingChars` with `listOf`. Then it sends the result
    through `dodgeKeyword`. By `SetGen.mem_support_listOf_iff`, the support of
    `listOf` is all of the lists over the support of the element generator. The run
    therefore has no bound on its length. The support of `genIdentName` is the set
    of names that are drawable in syntax and are not reserved keywords.

    Forward: a draw is `dodgeKeyword (String.ofList (x :: xs))`. In the branch for
    a name that is not a keyword, this is `String.ofList (x :: xs)`. In the branch
    for a keyword, it is `String.ofList (x :: xs) ++ "_"`, whose character list is
    `x :: (xs ++ ['_'])`. The first character is still legal. The other characters
    are still legal, because `'_' ∈ remainingChars`. In both branches
    `dodgeKeyword_not_keyword` gives the conjunct for keyword-freedom.

    Backward: use the first character of `s` and the other characters of `s` as the
    two draws. `dodgeKeyword` is the identity on `s`, because `s` is not a keyword.
    `dodgeKeyword_eq_self` gives this step, and `String.ofList` builds `s` again. -/
theorem mem_support_genIdentName_iff (s : String) :
    s ∈ SetGen.support (genIdentName (G := SetGen.Set)) ↔
      IsGenIdentName s ∧ isReservedKeyword s = false := by
  simp only [genIdentName, mem_support_bind_iff, mem_support_pure_iff]
  constructor
  · -- Forward: destructure the two draws, then do the two branches of `dodgeKeyword`.
    rintro ⟨x, hx, xs, hxs, rfl⟩
    have hstart : x ∈ startChars := by
      simpa only [genStartChar,
        mem_support_elements_iff (show startChars ≠ [] from by decide +kernel)] using hx
    have hrest : ∀ c ∈ xs, c ∈ remainingChars := by
      intro c hc
      have := SetGen.mem_support_listOf hxs c hc
      simpa only [genRemainingChar,
        mem_support_elements_iff (show remainingChars ≠ [] from by decide +kernel)] using this
    refine ⟨?_, dodgeKeyword_not_keyword _⟩
    unfold dodgeKeyword
    split
    · -- Keyword branch: the name is `String.ofList (x :: xs) ++ "_"`, so the run
      -- of other characters is `xs ++ ['_']`. Note `'_' ∈ startChars ⊆ remainingChars`.
      refine ⟨x, xs ++ ['_'], ?_, hstart, ?_⟩
      · rw [String.toList_append, String.toList_ofList]
        simp
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hrest c hc
        · rw [List.mem_singleton] at hc
          subst hc
          decide +kernel
    · -- Other branch: the name is `String.ofList (x :: xs)` itself.
      exact ⟨x, xs, by rw [String.toList_ofList], hstart, hrest⟩
  · -- Backward: use the split of `s` itself as the two draws.
    rintro ⟨⟨c, cs, hsplit, hc, hcs⟩, hnotkw⟩
    refine ⟨c, ?_, cs, ?_, ?_⟩
    · simpa only [genStartChar,
        mem_support_elements_iff (show startChars ≠ [] from by decide +kernel)] using hc
    · refine SetGen.mem_support_listOf_of_forall (fun c' hc' => ?_)
      simpa only [genRemainingChar,
        mem_support_elements_iff (show remainingChars ≠ [] from by decide +kernel)]
        using hcs c' hc'
    · -- `dodgeKeyword` is the identity on `s`, and `String.ofList (c :: cs) = s`.
      rw [← hsplit, String.ofList_toList, dodgeKeyword_eq_self hnotkw]

/-- The same claim as `mem_support_genIdentName_iff`, as an equation between sets. -/
theorem support_genIdentName :
    SetGen.support (genIdentName (G := SetGen.Set)) =
      {s | IsGenIdentName s ∧ isReservedKeyword s = false} := by
  ext s; exact mem_support_genIdentName_iff s

-- ── Corollaries ──────────────────────────────────────────────────────

/-- **No name in the support of `genIdentName` is a keyword.** This claim is the right part of
    `mem_support_genIdentName_iff`. -/
theorem genIdentName_not_keyword (s : String)
    (hs : s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    isReservedKeyword s = false :=
  (mem_support_genIdentName_iff s).mp hs |>.2

/-- Each name in the support of `genIdentName` has the syntax that the generator can draw. This
    claim is the left part of `mem_support_genIdentName_iff`. -/
theorem genIdentName_isGenIdentName (s : String)
    (hs : s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    IsGenIdentName s :=
  (mem_support_genIdentName_iff s).mp hs |>.1

/-- **The side condition, discharged from syntax.** Each completeness proof in the
    package needs this direction. Take a name that is drawable in syntax and is not
    a keyword. Then the generator draws that name. Both hypotheses are decidable,
    so `decide` closes this for a concrete name. -/
theorem mem_support_genIdentName_of_syntactic {s : String}
    (hsyn : IsGenIdentName s) (hnotkw : isReservedKeyword s = false) :
    s ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
  (mem_support_genIdentName_iff s).mpr ⟨hsyn, hnotkw⟩

/-- **The spec-level form of the support lemma.** This states `IsGenIdentName` over
    the lexer classes of Core. It does not use the character lists of the
    generator. The proof uses `mem_startChars_iff` and `mem_remainingChars_iff`.

    Quote this form to explain what the support is. The generator reaches exactly
    the strings that the lexer of Core accepts as a bare identifier and that are
    not reserved keywords. No internal alphabet of the generator is in the
    statement. -/
theorem mem_support_genIdentName_iff_isId (s : String) :
    s ∈ SetGen.support (genIdentName (G := SetGen.Set)) ↔
      (∃ c cs, s.toList = c :: cs ∧ isIdFirst c ∧ ∀ c' ∈ cs, isIdRest c') ∧
        isReservedKeyword s = false := by
  rw [mem_support_genIdentName_iff]
  unfold IsGenIdentName
  constructor
  · rintro ⟨⟨c, cs, hsplit, hc, hcs⟩, hkw⟩
    exact ⟨⟨c, cs, hsplit, (mem_startChars_iff c).mp hc,
            fun c' hc' => (mem_remainingChars_iff c').mp (hcs c' hc')⟩, hkw⟩
  · rintro ⟨⟨c, cs, hsplit, hc, hcs⟩, hkw⟩
    exact ⟨⟨c, cs, hsplit, (mem_startChars_iff c).mpr hc,
            fun c' hc' => (mem_remainingChars_iff c').mpr (hcs c' hc')⟩, hkw⟩

/-- **The form of the support lemma that `decide` can close.** The content is the
    same as `mem_support_genIdentName_iff`. The conjunct for keywords is stated as
    non-membership in the concrete list `reservedKeywordsList`, and not with
    `isReservedKeyword`.

    This form is necessary in practice. `isReservedKeyword` is a `Std.HashSet`
    lookup, and the kernel cannot reduce it, so `decide +kernel` stops on
    `isReservedKeyword s = false`. `isReservedKeyword_eq_list_contains` puts the
    condition back onto a concrete `List String`, which `decide` can reduce. Use
    this form when the name is concrete. -/
theorem mem_support_genIdentName_iff' (s : String) :
    s ∈ SetGen.support (genIdentName (G := SetGen.Set)) ↔
      IsGenIdentName s ∧ s ∉ reservedKeywordsList := by
  rw [mem_support_genIdentName_iff, isReservedKeyword_eq_list_contains,
      Bool.eq_false_iff, Ne, List.contains_eq_mem, decide_eq_true_eq]

/-- Reachability from the two decidable syntactic conditions. Both conditions are
    over concrete lists, which is the form that `decide` can close. -/
theorem mem_support_genIdentName_of_syntactic' {s : String}
    (hsyn : IsGenIdentName s) (hnotkw : s ∉ reservedKeywordsList) :
    s ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
  (mem_support_genIdentName_iff' s).mpr ⟨hsyn, hnotkw⟩

/-- Reachability of a name that is given as an explicit split into a first
    character and a list of other characters. This form occurs when a proof builds
    a name, and does not do a pattern match on it. -/
theorem mem_support_genIdentName_of_cons {c : Char} {cs : List Char} {s : String}
    (hsplit : s.toList = c :: cs)
    (hc : c ∈ startChars) (hcs : ∀ c' ∈ cs, c' ∈ remainingChars)
    (hnotkw : isReservedKeyword s = false) :
    s ∈ SetGen.support (genIdentName (G := SetGen.Set)) :=
  mem_support_genIdentName_of_syntactic ⟨c, cs, hsplit, hc, hcs⟩ hnotkw

/-- **No name in the support of `genIdentName` holds a space.** The generator draws the first
    character from `startChars` and each other character from `remainingChars`, and `' '` is in
    neither of those two lists.

    The first context of a body for an `inout` procedure needs this fact. `CoreIdent.mkOld` adds the
    prefix `"old "` to a name, and that prefix holds a space. No generated parameter name is
    therefore equal to a key of an `old` binding. -/
theorem genIdentName_no_space (s : String)
    (hs : s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    ' ' ∉ s.toList := by
  obtain ⟨c, cs, hsplit, hc, hcs⟩ := genIdentName_isGenIdentName s hs
  rw [hsplit]
  intro hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact (by decide +kernel : ' ' ∉ startChars) hc
  · exact (by decide +kernel : ' ' ∉ remainingChars) (hcs _ hmem)

/-- A generated identifier is not empty. This is immediate from the split into a
    first character and a list of other characters. -/
theorem genIdentName_ne_empty (s : String)
    (hs : s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    s.toList ≠ [] := by
  obtain ⟨c, cs, hsplit, _, _⟩ := genIdentName_isGenIdentName s hs
  rw [hsplit]; simp

end StrataGenerators.Function
