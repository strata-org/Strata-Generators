# strata-generators

(Work in progress) Experiments with random generators for [Strata](https://github.com/strata-org/strata) via [Basalt](https://github.com/hgoldstein95/basalt).

[`StrataGenerators/LExprGen.lean`](./StrataGenerators/LExprGen.lean) contains a (work-in-progress) Basalt generator for 
`LExpr`s synthesized using an LLM. 

## Well-typed generators

Two generators produce well-typed `LExpr`s with proved soundness, using different variable representations:

- **[`HasTypeAGen.lean`](./StrataGenerators/HasTypeAGen.lean)** — Generator of well-typed terms (using De Bruijn indices) satisfying the `HasTypeA` relation. Lambda bodies use `bvar i` directly; the context is a positional list (`BVarCtx = List LMonoTy`). No fresh names needed.
- **[`HasTypeGen.lean`](./StrataGenerators/HasTypeGen.lean)** — Generator of well-typed terms (using the locally-nameless representation) satisfying the `HasType` relation. Lambda bodies are built with free variables (`fvar`), then closed over with `varClose`. A monotonic counter supplies fresh binder names, and the soundness proof must establish freshness and the `varOpen`/`varClose` roundtrip.

`HasTypeAGen` targets `HasTypeA` (an annotated, de Bruijn typing relation). `HasTypeGen` targets the real `HasType` from `Strata.DL.Lambda.LExprTypeSpec` (locally-nameless, with polymorphic schemes instantiated via `tinst`).

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
