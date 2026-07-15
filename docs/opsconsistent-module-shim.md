# Why `OpsConsistent` is reproduced locally (`GenOpsConsistent`)

> **SUPERSEDED (this workaround was retired).** The local copies described below
> (`GenOpsConsistent` / `GenOpsConsistentR` + their `faithful` bridges) **no longer
> exist.** Strata's `OpsConsistent` was made `@[expose] public`, `OpsConsistentR`
> `public`, and `OpsConsistent_OpsConsistentR` `public` (in
> `Strata/DL/Lambda/Denote/Assumptions.lean`), so the non-`module` proof files now
> name and unfold the *real* predicates directly — no mirror copies, no `faithful`
> theorems. The former shim file `HasTypeAGen/OpsConsistentDef.lean` was renamed to
> **`HasTypeAGen/OpsConsistentBridge.lean`** and now holds only the handful of
> helper lemmas that genuinely require a `module` file (Factory `nameMap` lookup,
> self-unification, generic-type op-consistency) — not any predicate definition.
> The text below is retained only as background on the module-system constraint
> that originally motivated the copy.

## TL;DR

The generator's `OpsConsistent` proofs need to *name* Strata's
`Lambda.OpsConsistent`. But Lean 4's **module system** makes that impossible from
the files where the proofs live: `OpsConsistent` is only visible from a `module`
file, and the generator is a non-`module` file that a `module` file cannot import.
The two can never meet in one file. So we mirror the definition as
`Lambda.GenOpsConsistent` in a `module` shim (`HasTypeAGen/OpsConsistentDef.lean`),
marked `@[expose] public`, and prove — at build time — that it is *definitionally
identical* to the real one (`GenOpsConsistent.faithful`). The non-`module` proof
files reason about `GenOpsConsistent`; `faithful` certifies the results transfer
to Strata's `OpsConsistent`.

## Background: Lean's module system, in one paragraph

Lean 4 (recent versions, as used by Strata) has an optional **module system**. A
file that begins with the `module` keyword is a *module*; it gets stricter,
opt-in visibility:

- Declarations are **private to the module by default**. Only declarations marked
  `public` (or inside a `public section`) are visible to importers, and only if
  the importer uses `public import` / `import all`.
- A `module` file may import another `module` file (seeing its `public` parts, or
  everything with `import all`). **A `module` file may *not* import a
  non-`module` file** — that is a hard error:
  `cannot import non-`module` X from `module``.
- A non-`module` file importing a `module` file sees only the module's `public`
  declarations.

## The specific obstruction

Three facts collide:

1. **`Lambda.OpsConsistent` is private.** It is defined in
   `Strata/DL/Lambda/Denote/Assumptions.lean`, which is a `module` file
   (`module` on line 6), and `OpsConsistent` (line 64) is **not** inside any
   `public section` and is not marked `public`. Therefore it is only nameable
   from a `module` file that does `import all Strata...Denote.Assumptions`. From a
   non-`module` file it is simply invisible (Lean reports
   `Unknown identifier `Lambda.OpsConsistent`` with a note that a private
   declaration of that name exists).

2. **The generator is non-`module`.** `HasTypeAGen/Core.lean` (and the proof
   files built on it) `import Basalt.Gen`, `Basalt.Examples.ArbNat.Def`, etc. The
   vendored **Basalt** library is not a module system package (its files have no
   `module` header). A `module` file cannot import Basalt, so the generator files
   cannot be modules either — they transitively depend on Basalt.

3. **So no single file can see both.** To name `OpsConsistent` a file must be a
   `module` doing `import all` on `Assumptions`. But such a `module` file cannot
   import the generator (which needs Basalt). Conversely, the generator's
   non-`module` files cannot see the private `OpsConsistent`. There is no file
   that can mention *both* `genLExpr` and `Lambda.OpsConsistent`.

We confirmed each of these empirically:
- `import all` on `Assumptions` from a plain (non-`module`) file: `OpsConsistent`
  still `Unknown identifier` (privacy, not just import kind).
- `module` file with `import Basalt.Gen`:
  `error: cannot import non-`module` Basalt.Gen from `module``.
- `module` file with `import all Strata...Assumptions`: `#check @Lambda.OpsConsistent`
  succeeds.

Editing Strata to add `public` to `OpsConsistent` was rejected: the task treats
`Assumptions.lean` as unchanged upstream, and we did not want the generator's
correctness story to depend on a patch to Strata.

## The shim: `GenOpsConsistent` + `faithful`

`HasTypeAGen/OpsConsistentDef.lean` is a `module` file that `import all`s
`Assumptions`. It contains:

- `@[expose] public def Lambda.GenOpsConsistent` — a *verbatim copy* of
  `OpsConsistent`'s definition (same match, same op/app/abs/ite/eq/quant cases).
  `public` makes it visible to the non-`module` proof files; `@[expose]` makes its
  body available so those files can `unfold`/`simp` it and see the op-annotation
  coherence condition.

- `theorem Lambda.GenOpsConsistent.faithful (F) (e) : GenOpsConsistent F e = Lambda.OpsConsistent F e`
  — proved by induction on `e` (the `.op`/const/bvar/fvar leaves are `rfl`; the
  compound cases rewrite by the IHs). This is the **build-time certificate** that
  the copy is not just similar but *definitionally identical* to Strata's
  predicate. It is checked every build. (It cannot itself be `public` — its
  statement mentions the private `Lambda.OpsConsistent` — but it does not need to
  be: it is an internal cross-check, and downstream code only needs
  `GenOpsConsistent` and the knowledge, guaranteed by `faithful`, that the two
  agree.)

Because `faithful` mentions the private symbol, it can only be *stated and proved*
inside this `module` file — which is exactly the one place `import all` grants
access to `Lambda.OpsConsistent`. That is why the shim, the faithful check, and
all the Strata-facing bridge lemmas (`unify_self`, `opGeneric_opsConsistent`,
`mkArrow_destructArrow`, `mem_get?_eq`, `opGroundInstance_opsConsistent`) live
together in `OpsConsistentDef.lean`.

## What downstream files do

`StrataGenerators/HasTypeAGenOpsConsistent.lean` (non-`module`) imports the shim
and the generator, and proves everything in terms of `Lambda.GenOpsConsistent`
(e.g. `genLExpr_opsConsistent_of_PCtxWF : … → Lambda.GenOpsConsistent F e`). To
read any such result as a statement about Strata's real predicate, compose it with
`GenOpsConsistent.faithful` — inside a `module` context, or informally, since the
two are proven equal. In effect:

```
generator (non-module)  ──imports──▶  GenOpsConsistent  (public, in module shim)
                                          ║  faithful (build-checked)
Strata OpsConsistent (private, module) ═══╝
```

## Consequence / caveat

The restatement of the final result *in terms of the private `Lambda.OpsConsistent`*
can only be written inside a `module` file that `import all`s `Assumptions` — which,
per the obstruction above, cannot import the generator. So there is no single
theorem `… → Lambda.OpsConsistent F e` over generated `e`; the guarantee is
delivered as `… → Lambda.GenOpsConsistent F e` **plus** the definitional equality
`faithful`. If Strata ever marks `OpsConsistent` `public` (or moves it to a
`public section`), the shim can be deleted and `GenOpsConsistent` replaced by the
real predicate throughout, with no change to the proof structure.

## Files

| File | Role |
|------|------|
| `Strata/.../Denote/Assumptions.lean` | Defines the private `Lambda.OpsConsistent` (upstream, unchanged) |
| `HasTypeAGen/OpsConsistentDef.lean` | `module` shim: `GenOpsConsistent` (`@[expose] public`) + `faithful` + Strata-facing bridge lemmas |
| `HasTypeAGenOpsConsistent.lean` | Non-`module` proofs about `GenOpsConsistent` for the generator |
| `HasTypeAGen/Core.lean` | The generator (non-`module`, imports Basalt) |
