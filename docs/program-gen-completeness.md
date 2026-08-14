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

### Per-step reachability: 5 of the 7 kinds

`ProgramGen/Complete.lean` has per-step reachability lemmas for **axioms, abstract
types, aliases, `distinct` and datatype blocks**:

| kind | lemma | needs `genLExpr`? | needs an arity hypothesis? |
| --- | --- | --- | --- |
| axiom | `genDeclAxiom_complete` | yes, as a hypothesis | no |
| abstract type | `genDeclAbstract_complete` | no | no |
| alias | `genDeclAlias_complete`, `…_of_body` | no | yes, through the body |
| `distinct` | `genDeclDistinct_complete` | no, only `.op` nodes | yes, through `τ` |
| datatype | `genDeclDatatype_complete`, `…_of_MutualADTWF` | no, types only | yes, through the block |
| function / procedure | none | yes | — |

The arity hypotheses are `VocabOk` on the pool the generator draws from, plus
`ArgsWellKinded` and `BitvecWidthOnly` on the type. `VocabOk` ties the pool to `C`'s
arity register, so upstream's `argsWellKinded` carries the arity discipline and only
`BitvecWidthOnly` remains as a condition on the type itself.

The four non-axiom lemmas are provable because none of those four generators makes
a general expression. The two kinds that have no lemma are the two whose bodies are
general expressions.

`genNonRecursiveArgTy_complete` is a support lemma. An alias body and the monotype
of `distinct` both come from `genNonRecursiveArgTy`, which is `genArgTy` at the
empty block. The lemma gives `genArgTy_complete_of_wf` at that block. The
block-shaped hypotheses degenerate there: see `constrArgWF_nil`, and note that
three of the four fields of `NamesOk` become vacuous. Only the free-variable
condition and the arity hypotheses remain.

The datatype step has two lemmas. `genDeclDatatype_complete` takes reachability of
the block at `b.maxDatatypeSize` and the `.ok` branch of the `LContext.addMutualBlock`
gate, and it pins the same `CoreLParams`-native instances that the generator pins, so
the hypothesis matches the gate with no instance-diamond bridge.
`genDeclDatatype_complete_of_MutualADTWF` discharges the block hypothesis from
`MutualADTWF` alone, through the capstone
`genMutuallyRecursiveDatatypes_complete_of_MutualADTWF`. The caller gives no order of
the datatypes and no rank; the capstone builds both. The side conditions are stated at
the *combined* pool `s.tyCons ++ s.dtCons`, which is what the step draws over
(interleaving direction (4)), and at `extraReserved := s.reserved`. The size is
existential for the same reason it is existential in the capstone, so the conclusion
varies `b.maxDatatypeSize`.

The arity hypotheses are at the same position as in the datatype development, and
they need no more plumbing. The hand-written `ArityOk` predicate these lemmas used to
carry is gone, closed by `VocabOk` plus upstream's `argsWellKinded`.

**The reduction is in use from end to end.** Two `example`s at the end of
`Complete.lean` compose a per-step lemma through the weighted dispatch, the fold
and the assembly of the program. The result is a reachable whole `Program`. One
takes the abstract-type step, which grows one field of the generator state; the
other takes the datatype step, which grows six (`C`, `reserved`, `dtCons` and the
three operator contexts) and passes the `addMutualBlock`
gate, and so is the one that checks that the state a per-step lemma names is the
state the fold threads onward. Both paths remain narrow, because each has a single
declaration. But they show that the interface of the reduction lemmas has the
correct shape.

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
