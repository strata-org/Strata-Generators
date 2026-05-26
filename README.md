# strata-generators

(Work in progress) Experiments with random generators for [Strata](https://github.com/strata-org/strata) via [Basalt](https://github.com/hgoldstein95/basalt).

[`StrataGenerators/LExprGen.lean`](./StrataGenerators/LExprGen.lean) contains a (work-in-progress) Basalt generator for 
`LExpr`s synthesized using an LLM. 

**Dependencies**: 
- `Strata`
- `Basalt` 
  - In order for GitHub Actions to function properly, this repo depends on Harry's public Basalt repo on GitHub, not the 
AWS-internal fork. As a result, the `SetGen` portions of our internal Basalt fork (which aren't in the public-facing repo) have been manually copied over to this repo.

## Building

1. Run `lake update` to resolve dependencies.

2. Fetch prebuilt Mathlib build artifacts (avoids compiling Mathlib from scratch):
   ```bash
   lake exe cache get
   ```

3. Build:
   ```bash
   lake build
   ```
