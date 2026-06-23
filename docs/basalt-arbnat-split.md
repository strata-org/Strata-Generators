# Splitting `Basalt.Examples.ArbNat` (and similar) into Def + Proofs

## Motivation

`Basalt.Examples.ArbNat`, `ArbChar`, and `ArbString` each define a generator
AND prove properties about it (support, termination, cost) in the same file.
The proofs require `SPMF` which transitively pulls in Mathlib:

```
Basalt.Examples.ArbNat
  → import Basalt        (umbrella)
    → Basalt.Basic
      → Basalt.SPMF
        → Basalt.SPMF.Core
          → Mathlib.Topology.Instances.ENNReal.Lemmas
```

This means any file that imports `Basalt.Examples.ArbNat` gets Mathlib, which
collides with Strata's public `List.dedup` (defined in `Strata.DL.Util.List`,
also defined in `Mathlib.Data.List.Defs`).

If the definitions were split from the proofs, downstream projects could import
just the definitions (which only need `Basalt.Gen`) without pulling in Mathlib.

## What to split

Each of these files follows the same pattern:

| File | Definition | Proofs |
|------|-----------|--------|
| `Basalt/Examples/ArbNat.lean` | `Nat.arbitrary` | `Nat.arbitrary_support`, `Nat.arbitrary_terminates`, `Nat.arbitrary_cost`, `LawfulGenerator` instance |
| `Basalt/Examples/ArbChar.lean` | `Char.arbitrary`, `indexToChar` | `Char.arbitrary_support`, `Char.arbitrary_terminates`, `Char.arbitrary_cost` |
| `Basalt/Examples/ArbString.lean` | `String.arbitrary`, `genCharList` | `genCharList_support`, `String.arbitrary_support`, `genCharList_terminates`, `String.arbitrary_terminates`, `genCharList_cost`, `String.arbitrary_cost` |

## Proposed structure

```
Basalt/Examples/ArbNat.lean         -- imports Basalt (keeps proofs, re-exports def)
Basalt/Examples/ArbNat/Def.lean     -- NEW: only imports Basalt.Gen
```

### `Basalt/Examples/ArbNat/Def.lean`

```lean
import Basalt.Gen

open RandomChoice

namespace ArbNat

def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

end ArbNat
```

**Import cost**: Only `Basalt.Gen` → `Basalt.RandomChoice` → no Mathlib.

### `Basalt/Examples/ArbNat.lean` (modified)

```lean
import Basalt
import Basalt.Examples.ArbNat.Def  -- re-export the definition

open RandomChoice

namespace ArbNat

-- All proofs stay here (they need SPMF → Mathlib)
theorem Nat.arbitrary_support : ...
theorem Nat.arbitrary_terminates : ...
theorem Nat.arbitrary_cost : ...
instance : LawfulGenerator Nat.arbitrary ⊤ (fun n => n + 1) where ...

end ArbNat
```

### Same pattern for ArbChar

```
Basalt/Examples/ArbChar/Def.lean    -- Char.arbitrary, indexToChar
                                    -- imports Basalt.Gen (+ Basalt.Combinators for `choose`)
Basalt/Examples/ArbChar.lean        -- proofs (imports Basalt + Batteries.Data.Char)
```

Note: `Char.arbitrary` in Basalt uses `choose 0 61` which is from `Basalt.Gen`,
so the def file only needs `Basalt.Gen`.

### Same pattern for ArbString

```
Basalt/Examples/ArbString/Def.lean  -- genCharList, String.arbitrary
                                    -- imports Basalt.Gen + Basalt.Examples.ArbChar.Def
Basalt/Examples/ArbString.lean      -- proofs (imports Basalt + ArbChar proofs)
```

## Impact on strata-generators

After this split, `HasTypeAGen/Core.lean` could replace its local copies with:

```lean
import Basalt.Examples.ArbNat.Def
import Basalt.Examples.ArbChar.Def
import Basalt.Examples.ArbString.Def
```

This avoids Mathlib entirely, eliminating the `List.dedup` collision and removing
~50 lines of duplicated generator code from `Core.lean`.

## Considerations

- **Backward compatible**: Existing imports of `Basalt.Examples.ArbNat` keep
  working (the file re-exports the def).
- **`ArbChar` dependency**: Basalt's `Char.arbitrary` uses `choose` (from
  `Basalt.Gen`) — no extra dependencies needed for the def file.
- **`ArbString` dependency**: `genCharList` calls `Char.arbitrary`, so
  `ArbString/Def.lean` must import `ArbChar/Def.lean`.
- **Namespace consistency**: Both def and proof files use `namespace ArbNat` /
  `ArbChar` / `ArbString`, so the qualified names stay the same.
- **strata-generators proofs**: The `SetGen`-based support proofs in
  `HasTypeAGen.lean` (e.g., `Nat_arbitrary_support_set`) would still need to be
  local since they prove properties about a *different* semantics (`SetGen.Set`)
  than Basalt's SPMF-based proofs. These are not duplicates of Basalt's proofs.
