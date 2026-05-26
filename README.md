# strata-generators

Experiments with random generators for [Strata](https://github.com/strata-org/strata) via [Basalt](https://github.com/hgoldstein95/basalt).

## Prerequisites

- [Lean 4](https://lean-lang.org/) (see `lean-toolchain` for the required version)
- SSH access to `github.com/strata-org/strata`

## Building

1. Clone this repo and `cd` into it.

2. Run `lake update` to resolve dependencies.

3. Fetch prebuilt Mathlib build artifacts (avoids compiling Mathlib from scratch):
   ```bash
   lake exe cache get
   ```

4. Build:
   ```bash
   lake build
   ```
