import StrataGenerators.HasTypeAGen
-- HasTypeGen cannot be imported alongside HasTypeAGen because LExprTypeSpec
-- (imported by HasTypeGen) defines List.Forall₂ which conflicts with Batteries
-- (imported transitively by HasTypeAGen via Basalt.Examples.ArbNat → Mathlib).
-- import StrataGenerators.HasTypeGen
