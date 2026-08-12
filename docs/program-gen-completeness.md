# Whole-program generator — completeness scope

**Soundness** (`ProgramGen.genProgram_sound`) is proven in full and `sorry`-clean:
every generated program satisfies `ProgramHasTypeA coreContext {} P` (both
conjuncts — `getNames.Nodup` and the `DeclsHasType'` derivation).

**Completeness** — "every well-typed program is reachable" — is inherently a
*bounded-sampler* statement and inherits every reachability caveat the
sub-generators already carry, plus a program-level one. This document records
exactly what holds and what the honest side conditions are, mirroring
`mutualadtwf-arity-gap.md`.

## Inherited per-declaration reachability conditions

Program completeness cannot be stronger than the sub-generators it composes:

* **Names** — **no longer a side condition.**
  `mem_support_genIdentName_iff` (`FunctionHasTypeAGen/IdentName.lean`)
  characterises `genIdentName`'s support in both directions: exactly the legal
  bare Core identifiers that are not reserved keywords, both conditions
  decidable. See `genidentname-support.md`. The `∈ support genIdentName`
  hypotheses below are therefore dischargeable rather than assumed.
* **Expressions** (`genLExpr_complete`, `HasTypeAGen.lean`) — reachable only for
  `SimpleType` targets, with `emptyNames`/`allVarsInCtx`/`AllTypesSimple`/
  `termDepth ≤ depth` side conditions. So axiom bodies and function bodies are
  reachable only within those.
* **Functions** (`genFunction_complete`) — requires default non-varied fields
  (`isConstr=false`, `isRecursive=false`, `attr=#[]`, `axioms=[]`,
  `preconditions.length ≤ 1`) plus per-component `genIdentName`/`genLMonoTy`/
  `genLExpr` reachability. The generator only ever produces `.func` (never
  `.recFuncBlock`), so recursive function blocks are out of range by construction.
* **Datatypes** (`genArgTy_complete_of_MutualADTWF`) — complete against
  `MutualADTWF` with the `BitvecWidthOnly` side condition and `VocabOk` (see
  `mutualadtwf-arity-gap.md`; the old hand-written `ArityOk` is gone, closed by
  upstream's `argsWellKinded`); `MutualADTWF`-alone completeness is provably false.
* **Type aliases** — the generator stores the body verbatim with
  `typeArgs := (freeVars body).dedup`. It therefore reaches exactly the aliases
  whose declared `typeArgs` are the dedup'd free vars in the *written* order the
  generator draws; a user alias with a permuted or superset `typeArgs` list (still
  WF) is a different syntactic declaration and not directly in range. Aliases are
  also kept flat (body references no other alias name), matching the checker's
  post-`resolveAliases` stored form.

## Program-level reachability condition (the fold)

Beyond the per-declaration conditions, `genProgram` reaches a program `P` only if
its declaration list is a possible *fold trace*:

* Each declaration's name must be drawable fresh against the running reserved set
  — automatic for any `getNames.Nodup` program whose names avoid the seed
  (`initialReserved` over Core's known types), which every well-typed program's
  names do (a name clashing with a Core known type is rejected by the checker).
* The declaration *kinds* must be ones the generator emits: `type (con/syn/data)`,
  `ax`, `distinct`, and non-recursive `func`. Programs containing `proc` or
  `recFuncBlock` declarations are out of range (see below).
* Datatype blocks reference only the default vocabulary + abstract types declared
  earlier (the Tier-1 interleaving scope); a block referencing a *prior datatype*
  is well-typed but not generator-reachable (documented scope decision — the
  generator's inhabitance argument needs referenced heads to be external).

## What is proven

Per-declaration *soundness* is complete and `sorry`-clean for all six kinds. For
completeness we expose the reachability of each declaration step by re-exporting
the sub-generators' completeness lemmas at the program-step level where they apply
without new side conditions, and document (here) the conditions that are inherent
to bounded sampling rather than hiding them behind `sorry`.

A monolithic `genProgram_complete` (every `ProgramHasTypeA` program is reachable)
is **not** claimed, because it is false without the union of all the side
conditions above — exactly analogous to why datatype completeness needs
`BitvecWidthOnly`.

## Procedures / recursive-function blocks

Procedures are now **included and proved sound** (see `program-gen-design.md`,
"Option B"). The generator threads the real ambient `C`/`Γ` into `genProcedure`
and uses a rigidTypeVars weakening (`genProcedure_sound_ambient`) to reconcile
with `DeclHasType'.proc`'s ambient context. Program-level *completeness* for
procedures inherits `genProcedure_complete`'s reachability side conditions (body
statement reachability via `genStmtChain`, three-block signature decomposition,
default non-varied fields) — documented, not a monolithic claim.

**Recursive-function blocks** (`recFuncBlock`) remain excluded: the generator only
emits non-recursive `.func`.

## Note: the interleaving changes (directions (2) and (4))

Exercising ADT→abstract-type and ADT→prior-datatype references (see
`program-gen-interleaving.md`) changed the *soundness* side only. The
completeness statements in `ProgramGen/Complete.lean` are unaffected in form:
the datatype step still calls `genMutuallyRecursiveDatatypes`, only with a wider
applied-constructor vocabulary (`s.tyCons ++ s.dtCons` instead of
`defaultTyCons`).

That widening does not weaken the documented side conditions
(`mutualadtwf-arity-gap.md`): prior datatypes and abstract types enter the
vocabulary *with* their arities and are drawn through the same
`vectorOf arity …` application branch as the primitives, so the arity discipline
— and the gap on the spec side — is exactly as before.
