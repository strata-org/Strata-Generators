/-
Vendored from https://github.com/hgoldstein95/basalt, from the `SetGen` branch.

This code reads a generator as a `Set α`. The set holds the values that the generator can
produce, which is its support, and it holds no probability. A proof of the soundness or the
completeness of a generator against a predicate for validity can therefore use it.
-/
import StrataGenerators.SetGen.Defs
import StrataGenerators.SetGen.Core
import StrataGenerators.SetGen.Support
import StrataGenerators.SetGen.Classes
