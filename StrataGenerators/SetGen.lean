/-
Vendored from https://github.com/hgoldstein95/basalt (SetGen branch, not yet on `main`).

A simplified interpretation of generators as `Set α`, tracking only which values are reachable
(the support) without probabilities. This is useful for proving soundness and completeness
of generators with respect to validity predicates.
-/
import StrataGenerators.SetGen.Defs
import StrataGenerators.SetGen.Core
import StrataGenerators.SetGen.Support
import StrataGenerators.SetGen.Classes
import StrataGenerators.SetGen.Tuning
import StrataGenerators.SetGen.WeightedOptionGen
