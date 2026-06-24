# SPMF vs SetGen Support Proofs

A comparison of support proofs for common generator combinators between:
- **SPMF** (`basalt/Basalt/SPMF/Support.lean`) — full measure-theoretic interpretation
- **SetGen** (`StrataGenerators/SetGen/Support.lean`) — set-based reachability interpretation

## Theorem Correspondence

Both files prove the same set of theorems with matching names and identical conclusions:

| Combinator | Theorem | Conclusion |
|---|---|---|
| `pure` | `support_pure` | `= {a}` |
| `bind` | `support_bind` | `{b \| ∃ a ∈ x.support, b ∈ (f a).support}` |
| `map` | `support_map` | `{b \| ∃ a ∈ x.support, b = f a}` |
| `pick` | `support_pick` | `x.support ∪ y.support` |
| `choose` | `support_choose` | all elements (full support) |
| `elements` | `support_elements` | `{x \| x ∈ xs}` |
| `oneOf` | `support_oneOf` | `{a \| ∃ g ∈ gs, a ∈ (g ()).support}` |
| `frequency` | `support_frequency` | `{a \| ∃ w g, ⟨w,g⟩ ∈ gs ∧ 0 < w ∧ a ∈ (g ()).support}` |
| `dite`/`ite` | `mem_support_dite_iff` / `mem_support_ite_iff` | case split on condition |
| `csup` | `mem_support_csup` | `∃ f, c f ∧ a ∈ f.support` |
| `bind_congr` | `bind_congr_support` | equal on support implies equal bind |

Both also provide `mem_support_X_iff` variants alongside the `support_X` set-equality versions.

## Key Differences

### 1. Proof Complexity

SetGen proofs are dramatically simpler. Since `Set α` *is* its own support (`def support (s : Set α) := s`), most proofs reduce to `Iff.rfl`, `rfl`, or one-line `ext`/`simp` chains.

Examples:
- `support_bind`: `ext b; exact Iff.rfl` (SetGen) vs. a 15-line `tsum`/`ENNReal` argument (SPMF)
- `support_pure`: `rfl` (SetGen) vs. `classical` + `ext` + `if/then/else` reasoning (SPMF)
- `support_pick`: 1-line `simp` (SetGen) vs. case-splitting on `Nat.le_one_iff_eq_zero_or_eq_one` (SPMF)

### 2. The `bind` Proof (Most Illustrative Difference)

**SPMF** must show `∑' a, x(a) * f(a)(b) ≠ 0 ↔ ∃ a, x(a) ≠ 0 ∧ f(a)(b) ≠ 0`, which requires:
- A contrapositive argument with `ENNReal.mul_pos` and `ENNReal.le_tsum`
- Reasoning about infinite sums equaling zero

**SetGen** is just set-comprehension membership — definitionally true.

### 3. The `elements`/`oneOf` Proofs

Both repos use essentially the **same proof structure** — the index-manipulation arguments are identical (`omega`, `List.mem_iff_getElem`, `List.getElem_mem`). This makes sense: both must show that a random index into a list covers exactly the list's elements.

The only difference is that SPMF proofs have an extra `simp [Pure.pure]` step to handle the SPMF `pure` encoding, while SetGen's `pure` is just `{a}`.

### 4. The `frequency` / `frequencyAux` Proofs

Nearly copy-paste identical structure. Both prove:
- `frequencyAux_mem`: induction on `gs`, split on `n < w`
- `frequencyAux_n_exists`: induction on `gs`, case split head vs. tail

The SPMF version has slightly more verbose final assembly in `support_frequency` because it must handle the `dite` branch where `n ≥ total` (falling to `default`), whereas SetGen uses `dif_pos` more directly.

### 5. `csup` Proof

**SPMF** requires a helper lemma `csup_apply` that characterizes the supremum pointwise via `⨆ f, ⨆ (_ : c f), f a`, then reasons about `iSup₂_le` / `le_iSup₂_of_le`.

**SetGen** simply unfolds the set-union definition of `csup` and applies `le_csup`/`csup_le` directly — no pointwise `iSup` reasoning needed.

### 6. Extra Theorems

**SPMF-only:**
- `support_countable` — the support is always countable (measure-theoretic property)
- `apply_pos_iff` / `apply_eq_zero_iff` — relate positivity to support membership

**SetGen-only:**
- `bot_bind` / `bot_mem_iff` — explicit lemmas about the bottom element (`∅`)

## Summary

The two are intentionally parallel — same theorem statements, same API surface. SetGen acts as a simplified model: you get the same support characterizations with trivial proofs, which is useful for rapid development or when you only care about reachability (not probabilities). The SPMF versions carry the full measure-theoretic weight, with proofs 5-15x longer due to `ENNReal`/`tsum` reasoning, but establish the same logical facts.
