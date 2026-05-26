# strata-generators

(Work in progress) Experiments with random generators for [Strata](https://github.com/strata-org/strata) via [Basalt](https://github.com/hgoldstein95/basalt).

[`StrataGenerators/LExprGen.lean`](./StrataGenerators/LExprGen.lean) contains a (work-in-progress) Basalt generator for 
`LExpr`s synthesized using an LLM. 

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
