import StrataGenerators.FunctionHasTypeAGen.IdentName

open StrataGenerators.Function

/-!
# Tightness checks for `mem_support_genIdentName_iff`

A statement about a support is useful only if it is tight. An `iff` whose
right-hand side is trivial typechecks, but proves nothing. The examples below are
machine-checked witnesses that the statement cuts in both directions. They give
names that the generator reaches, and names that it provably does not reach.

`decide` closes each example. This is the practical value of the lemma: a side
condition on name reachability needs no manual work for a concrete name.

`isReservedKeyword` is a `Std.HashSet` lookup, and the kernel cannot reduce it.
Therefore these examples use the primed lemmas
`mem_support_genIdentName_iff'` and `mem_support_genIdentName_of_syntactic'`,
which state the condition for keywords over the concrete `reservedKeywordsList`.
-/

namespace StrataGenerators.Function.Tests

-- ── Names that the generator reaches ─────────────────────────────────

/-- A usual lower-case name. -/
example : "foo" ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  apply mem_support_genIdentName_of_syntactic' <;> decide +kernel

/-- The generator reaches the digits and the special characters `$ . ' ? ! @` in
    each position after the first. -/
example : "x$y.z'w?v!u@t0" ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  apply mem_support_genIdentName_of_syntactic' <;> decide +kernel

/-- The generator reaches a name that starts with `_` or with `$`. Both characters
    are in `strataIsIdFirst`. -/
example : "_x" ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  apply mem_support_genIdentName_of_syntactic' <;> decide +kernel

example : "$x" ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  apply mem_support_genIdentName_of_syntactic' <;> decide +kernel

/-- A name of one character. The run of `remainingChars` can be empty. -/
example : "q" ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  apply mem_support_genIdentName_of_syntactic' <;> decide +kernel

/-- The generator reaches a name of only `x` characters, at each length.
    `DatatypeGen.fallbackName` and `CmdHasTypeAGen.indexedFreshName` use such a
    name after a collision. -/
example : "xxxxxxx" ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  apply mem_support_genIdentName_of_syntactic' <;> decide +kernel

/-- **`dodgeKeyword` does not make the support larger.** The generator reaches the
    dodged form of a keyword. But it reaches that form because the form is itself a
    usual draw, and `_` is legal after the first character. The dodge branch adds
    no new name. -/
example : "if_" ∈ SetGen.support (genIdentName (G := SetGen.Set)) := by
  apply mem_support_genIdentName_of_syntactic' <;> decide +kernel

-- ── Names that the generator does not reach: the tight half ──────────

/-- **The support excludes the reserved keywords.** This is the one subtractive
    effect of `dodgeKeyword`. The name `if` has the shape of a legal identifier, but
    the generator can never give it. Each completeness statement over names must
    carry this exclusion, and therefore it is a conjunct of the support lemma. -/
example : "if" ∉ SetGen.support (genIdentName (G := SetGen.Set)) := by
  rw [mem_support_genIdentName_iff']
  intro h; exact h.2 (by decide +kernel)

example : "procedure" ∉ SetGen.support (genIdentName (G := SetGen.Set)) := by
  rw [mem_support_genIdentName_iff']
  intro h; exact h.2 (by decide +kernel)

/-- The generator does not reach the empty name. It always draws a first
    character. -/
example : "" ∉ SetGen.support (genIdentName (G := SetGen.Set)) := fun h =>
  genIdentName_ne_empty _ h (by decide +kernel)

/-- The generator does not reach a name that starts with a digit. Therefore the
    lexer never reads a generated identifier as a `Num`. Read the docstring of
    `genIdentName`. -/
example : "1x" ∉ SetGen.support (genIdentName (G := SetGen.Set)) := by
  rw [mem_support_genIdentName_iff']
  intro h; exact absurd h.1 (by decide +kernel)

/-- The generator does not reach a character that only the form with pipe
    delimiters can hold. `genQuotedName` reaches such a character. `genIdentName`
    does not, and the support lemma records this. -/
example : "a|b" ∉ SetGen.support (genIdentName (G := SetGen.Set)) := by
  rw [mem_support_genIdentName_iff']
  intro h; exact absurd h.1 (by decide +kernel)

example : "a\\b" ∉ SetGen.support (genIdentName (G := SetGen.Set)) := by
  rw [mem_support_genIdentName_iff']
  intro h; exact absurd h.1 (by decide +kernel)

/-- The generator does not reach a name that has a space. `genIdentName_no_space`
    gives this fact in general, and this example is one concrete case. The fact
    separates a generated parameter name from a key `"old "` of
    `CoreIdent.mkOld`. -/
example : "a b" ∉ SetGen.support (genIdentName (G := SetGen.Set)) := by
  rw [mem_support_genIdentName_iff']
  intro h; exact absurd h.1 (by decide +kernel)

-- The same check at a real use site is at the end of the module for the proofs about a datatype.
-- There, `decide` discharges the side condition about the reach of `DatatypeGen.genFreshName`. That
-- check cannot be in this file, because this file would then import the development for a datatype,
-- and that development imports this file.

end StrataGenerators.Function.Tests
