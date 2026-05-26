# strata-generators

Experiments with random generators for [Strata](https://github.com/strata-org/strata) via [Basalt](https://code.amazon.com/packages/Basalt/trees/mainline).

## Prerequisites

- [Lean 4](https://lean-lang.org/) (see `lean-toolchain` for the required version)
- SSH access to `github.com/strata-org/strata`
- A local clone of [Basalt](https://code.amazon.com/packages/Basalt/trees/mainline) named `basalt` in the **parent directory**

The expected directory layout is:

```
parent/
  strata-generators/   ← this repo
  basalt/              ← Basalt clone from code.amazon.com
```

## Building

1. Run `lake update` to resolve dependencies.

2. Fetch prebuilt Mathlib build artifacts by doing `lake exe cache get` (avoids compiling Mathlib from scratch).

3. Run `lake build`
