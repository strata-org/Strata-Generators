# Whole-program generator (`ProgramGen`) — design & soundness architecture

> **Status.** Soundness is fully proven and `sorry`-clean: `ProgramGen.genProgram_sound`
> (`StrataGenerators/ProgramGen/SoundProgram.lean`) shows every generated program
> satisfies `ProgramHasTypeA coreContext {} P` — both conjuncts (`getNames.Nodup`
> and the `DeclsHasType'` derivation). Axioms: the standard three plus
> `Lean.ofReduceBool` (inherited from the datatype generator's `defaultContextOk`
> `native_decide`, exactly as its existing `_default` corollaries). Completeness is
> the fold-inversion composition in `Complete.lean` (see
> `program-gen-completeness.md`).
>
> **Note on IO sampling.** `ProgramGen.sample` runs the generator under Basalt's
> `IO` `Gen` interpretation, which inherits a pre-existing `panic!` in the
> sub-generators (`genFunction`/`genLExpr` panic on some degenerate draws in `IO`,
> independent of this work). This does *not* affect the proofs, which are stated
> over `SetGen.Set` (the support semantics), not the `IO` interpretation. The
> declaration kinds this generator adds (abstract types, aliases, axioms, distinct)
> and datatype blocks sample cleanly under the real Strata checker (verified 100/100
> under `coreContext` during development).

**Target:** a Basalt `Gen` generator for random Strata Core `Program`s, proved
sound (and, where tractable, complete) wrt `Core.TypeSpec.ProgramHasType'`
(instantiated at `HasTypeA` → `ProgramHasTypeA`), defined in
`.lake/packages/Strata/Strata/Languages/Core/ProgramTypeSpec.lean`.

`ProgramHasType' τ C Γ P := P.getNames.Nodup ∧ ∃ C' Γ', DeclsHasType' τ P C Γ P.decls C' Γ'`.

## Declaration kinds covered

New surface the task asks for, beyond the existing expr/cmd/stmt/func/proc/ADT
generators: **type aliases**, **abstract types** (type constructors), **axioms**,
**`distinct`** assertions. We reuse the existing generators for everything else.

## The central design decision: generate-and-check gating

Several `DeclHasType'` constructors require that a *checker operation succeeds*
and produce its result context:

* `type_con`  needs `C.addKnownTypeWithError {name, arity} default = .ok C'`;
* `type_data` needs `MutualADTWF C block` **and** `C.addMutualBlock block = .ok C'`;
* `func`      needs `FuncHasType' … func`, `¬func.isRecursive`, and
  `FactoryExtendedBy C C' [func.toLFunc]`.

There is **no** existing "WF ⟹ checker succeeds" bridge in Strata, and the
`MutualADTWF ⟹ addMutualBlock = .ok` direction in particular would require
proving executable↔inductive equivalences for `validateMutualBlock`,
`checkConstructorArgsWF`, `validateTypeReferences`, and — hardest, entirely
unproven — `adt_inhab ↔ TySymInhab`. That is a `sorry`-risk we refuse.

**Instead we thread the real `LContext`/`Γ` through the generator and run the
actual checker-add operations, emitting a declaration only on the `.ok` branch.**
Consequences:

* The `= .ok C'` premises fall out of *support membership* for free: an element
  of the gated generator's support came from the `.ok` branch, so
  `C.add… = .ok C'` holds definitionally for the value we produced. We never
  prove the hard inhabitance equivalence.
* The *declarative* premises (`MutualADTWF C block`, `FuncHasTypeA C Γ func`)
  come from the existing sub-generator soundness theorems
  (`genMutuallyRecursiveDatatypes_MutualADTWF`, `genFunction_sound`).

The generator is therefore a fold with state `(C : LContext CoreLParams,
Γ : TContext Unit, reserved : List String)`, producing
`Gen (Decl × LContext CoreLParams × TContext Unit × List String)` per step and
accumulating a `DeclsHasType'` derivation.

## Why threading `C` is forced (not a free choice)

The existing sub-generators prove soundness for an *arbitrary* `C`/`Γ`, exploiting
that the annotated spec's `exprTyped C Γ e mty = HasTypeA [] e mty` ignores the
context. But `type_con`/`type_data`/`func` need the real *output* context `C'`,
which only exists relative to the real input `C`. Program-level soundness cannot
avoid threading `C`.

## `ContextOk` maintenance (the Tier-1 proof obligation)

`genMutuallyRecursiveDatatypes_MutualADTWF` needs `ContextOk C baseTypes tyCons
extraReserved`. We maintain it as a fold invariant:

* start at `coreContext` (`defaultContextOk`, uses `native_decide`/`ofReduceBool`);
* set `extraReserved := C.knownTypes.keywords ++ C.datatypes.allTypeNames` at each
  ADT step, so freshly-drawn datatype names avoid every existing name
  (`knownTypes_reserved`/`datatypes_reserved`);
* `base_known`/`tyCon_known`/`arrow_known` are monotone under adds (adding never
  removes a known type);
* `base_external`/`tyCon_external`/`arrow_external` (`getType … = none`) survive
  because abstract types add to `knownTypes` not `datatypes`, and generated
  datatype names avoid the base/tyCon/arrow names (they are reserved).

Abstract types are the mechanism that *grows* the referenceable `tyCons` pool:
declaring `type Foo _ _;` adds `(Foo, arity)` — external, known, reserved — so
later ADT blocks may reference `Foo` while `ContextOk` still holds.

## Interleaving directions actually in the sound fragment

> **Update.** Directions (2) and (4) are now *exercised and proven*; direction (3)
> is exercised behind a separate, explicitly-unproven entry point, and the reason
> is now a machine-checked counterexample rather than a judgement call. See
> `program-gen-interleaving.md` and repo issue #65.
> The list below records the original analysis; the deltas are noted inline.

* **alias → prior ADT / prior abstract type**: literal and clean. An alias body
  may reference any prior datatype (at its arity) or abstract type.
* **ADT → prior abstract type**: clean — abstract types are external known types,
  satisfying `refsKnown` and `ContextOk`. **Now actually exercised**: the datatype
  step passes the threaded `s.baseTypes`/`s.tyCons` (not the fixed defaults), and
  `Inv.ctxOk` is stated at the grown vocabulary.
* **ADT → prior alias**: the checker (`ProgramType.lean:88`) *de-aliases* ADT
  blocks (`MutualDatatype.resolveAliases`) before `addMutualBlock`, so the stored
  block references the alias's *expansion*, never the alias name. We therefore
  emit the already-resolved type directly; "ADT references alias" is functionally
  "ADT references what the alias expands to". **Correction:** this is a genuine
  gap, not merely documented. Resolution does *not* preserve `MutualADTWF` — an
  arrow-bodied alias moves a block name into an arrow's domain, breaking strict
  positivity (worked example in repo issue #65). The alias-expanding
  step was prototyped and then **removed** as unproven; the question of whether
  positivity is meant to be checked pre- or post-resolution is parked for the
  Strata team (repo issue #65).
* **ADT → prior ADT datatype** (Tier 2): ~~*excluded*~~ **now supported and
  proven**. The stated reason — a prior datatype cannot ride
  `TySymInhab.external` — is true but not the only route: it rides
  `TySymInhab.datatype`, whose premise the fold already has from the
  `MutualADTWF.inhabited` field of the block that introduced it. Prior datatypes
  live in a separate pool (`GenState.dtCons`, `DatatypePoolOk`) and their
  inhabitance is transported across the block push by `tySymInhab_push`. The
  generator's inhabitance proofs were extended, not reworked.

Aliases are kept *flat* (no alias body references another alias name), so
`storedTy := ts.type` is `aliasFree Γ.aliases` and `AliasEquiv Γ.aliases storedTy
ts.type` holds by `.refl`. Type args are *derived* from the body:
`typeArgs := (LMonoTy.freeVars body).dedup`, which makes `typeArgs.Nodup`,
`freeVars ⊆ typeArgs`, and `typeArgs ⊆ freeVars` (no phantom) all hold by
construction.

## `getNames.Nodup`

The program's flat namespace spans type names, function names, axiom labels,
`distinct` labels, and procedure names. We thread a single global reserved-name
set across *all* declaration generation, adding each declared name, so
`P.getNames.Nodup` follows from pairwise-distinct fresh generation.

## New proofs required (all tractable, `sorry`-clean)

1. `ContextOk` preservation across the fold (mechanical).
2. `FactoryExtendedBy C C' [fn]` from `addFactoryFunctionWithError C fn = .ok C'`
   (short; `Factory.push_mem_iff`).
3. `addKnownTypeWithError` success handling for `type_con`
   (`addKnownTypeWithError_diag_irrel` swaps `default` for the checker diagnostic).
4. `type_syn` WF conditions from the derive-typeArgs-from-body construction.
5. `DeclsHasType'` fold plumbing + `getNames.Nodup`.

## Completeness

Program-level completeness inherits the datatype generator's documented `ArityOk`
side condition (see `mutualadtwf-arity-gap.md`) plus per-declaration reachability
side conditions of the form used by `genFunction_complete`. It is stated in
`∃`-budget form. Where a gap is inherent to bounded sampling, it is documented,
not hidden behind a `sorry`.

## Procedures (Option B — now included)

Procedures **are** generated and proved sound. The obstacle was that
`genProcedure_sound` originally pinned the body's ambient context to
`{LContext.default with rigidTypeVars := proc.typeArgs}`, whereas
`DeclHasType'.proc` threads the fold's shared growing `C` at the ambient
`rigidTypeVars`. This was resolved by:

1. **Threading `C`/`Γ` into `genProcedure`** (Option B): the body is generated
   under the *real* ambient context `{C with rigidTypeVars := typeArgs}` and
   type-scope `Γ`, so `genProcedure_sound` concludes at the caller's `C`/`Γ`
   (needs `Γ.types = []`, which the fold maintains — top-level decls never bind
   value variables).
2. **A rigidTypeVars weakening** (`genProcedure_sound_ambient` in
   `ProcedureHasTypeAGen.lean`): `RigidAnnotCompat` is *antitone* in `rigidVars`,
   and `C.rigidTypeVars` flows unchanged through `StmtsHasType'` (used only in
   `init`'s `RigidAnnotCompat`). So `ProcHasTypeA` at `rigidVars := typeArgs`
   transports to any `rv ⊆ typeArgs` — in particular the fold's `[]`. This is a
   genuine mutual induction (`Cmd → Stmt → Stmts`), all `sorry`-clean.

The program generator renames each procedure to a globally fresh name
(`ProcHasType'` is name-invariant) and threads the fold invariants `typesNil`
(`Γ.types = []`) and `rigidNil` (`C.rigidTypeVars = []`).

> **Update — inter-procedure calls.** Procedures were originally emitted with
> `procs = []`, making `ProcSigCorresponds [] P` vacuous at the cost that no
> generated body contained a `call`. The fold now *accumulates* callable
> signatures (`GenState.procs`) and passes them to `genProcedure`, so bodies do
> emit calls. The obligation `ProcSigCorresponds procs P` cannot be established
> step-by-step (the enclosing `P` does not exist yet), so it is carried as a
> hypothesis through `genDeclStep_sound`/`genDeclsFold_sound` — sound because
> `ProcSigCorresponds` is antitone and `procs` only grows — and discharged once in
> `genProgram_sound`, where `P` is complete. See
> `StrataGenerators/ProgramGen/ProcSigThread.lean`.
>
> Likewise the operator contexts: `octx`/`pctx` were `[]` and are now seeded with
> `coreMonoOps`/`corePolyOps`. That change is soundness-neutral — under the
> annotated spec an `.op` node is typed from its own annotation, and
> `genLExpr_sound`/`genFunction_sound` quantify over an arbitrary context — so it
> widened the support at the cost of a two-line proof change.

**Recursive-function blocks** (`recFuncBlock`) remain out of scope: the generator
only emits non-recursive `.func`.
