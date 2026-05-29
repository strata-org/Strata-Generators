import StrataGenerators.Tyche
import Basalt.IO

open RandomChoice Tyche

/-!
# Tyche Demo (Lightweight)

A lightweight Tyche demo that generates random natural numbers without
requiring Mathlib. Useful for quickly testing the Tyche integration pipeline.

## Usage

```
lake build tyche-demo && .lake/build/bin/tyche-demo [numSamples] [outputPath]
```
-/

/-- Generate a geometric-distributed natural number. -/
partial def Nat.geometric : IO Nat := do
  let coin ← choose (m := IO) 0 1 (by omega)
  if coin.down == 0 then return 0
  else return (← Nat.geometric) + 1

/-- A pair of (value, number of coin flips used). -/
structure NatSample where
  value : Nat

instance : Tyche.TycheSample NatSample where
  toSample s :=
    { representation := toString s.value
      features := [
        ("value", .ordinal s.value),
        ("parity", .nominal (if s.value % 2 == 0 then "even" else "odd")),
        ("magnitude", .nominal
          (if s.value < 3 then "small"
           else if s.value < 7 then "medium"
           else "large"))
      ] }

def main (args : List String) : IO Unit := do
  let numSamples := (args[0]? >>= String.toNat?).getD 500
  let outputPath := (args[1]?).getD "tyche_demo.jsonl"
  IO.println s!"Generating {numSamples} geometric nat samples..."

  Tyche.run (NatSample.mk <$> Nat.geometric)
    { numSamples, propertyName := "geometric_nat", outputPath }

  IO.println s!"Done! Output written to {outputPath}"
  IO.println "Open with Tyche: VS Code → Ctrl+Shift+P → 'Tyche: Open' → select the file"
