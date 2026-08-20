import StrataGenerators.ProgramGen

/-!
# Completeness of the whole-program generator (fold inversion)

A monolithic "every `ProgramHasTypeA` program is reachable" theorem is inherently
false for a *bounded sampler* without a union of per-declaration reachability side
conditions (the same reason datatype completeness needs `BitvecWidthOnly`).

What *is* cleanly provable — and is the useful completeness contribution — is that
the **fold composes**: if each declaration step is individually reachable from its
incoming state, the whole declaration list is reachable by `genDeclsFold`, and
hence the assembled `Program` by `genProgram`. Composed with the sub-generators'
own completeness lemmas (`genFunction_complete`, `genArgTy_complete_of_MutualADTWF`,
`genLExpr_complete`), this reduces program reachability to per-declaration
reachability with no new program-level obligation.

This file proves that composition, plus the per-step reachability lemmas that a
caller composes with it.

## Status: 5 of the 7 declaration kinds

This file has per-step reachability lemmas for **axioms, abstract types, aliases,
`distinct` and datatype blocks** (the `genDecl*_complete` theorems below). Two
kinds have no lemma: functions and procedures. What the remaining two need is
catalogued in the repo's issue tracker, along with the other blockers
(`genIdentName` has no two-directional support lemma, `recFuncBlock` is not
generated, and `genLExpr` is itself incomplete). The `ArityOk` blocker is
**gone**: upstream's `argsWellKinded` plus a vocabulary derived from
`Core.KnownTypes` discharged it.

Four of the five lemmas have a useful property: their generators never call
`genLExpr`, so they do not depend on the completeness of the expression generator
at all. The `distinct` step does contain expressions, but `genDistinct` builds them
directly as annotated `.fvar` nodes; and a datatype block is types only. The axiom
lemma is the exception — it is stated *relative to* a `genLExpr` reachability
hypothesis on the body, which the caller discharges from `genLExpr_complete`.

`genNonRecursiveArgTy_complete` is a support lemma. It gives
`genArgTy_complete_of_wf` at the empty block, which is what an alias body and the
monotype of `distinct` need.

The datatype step has two lemmas, in the same relation as `genDeclAlias_complete`
to `genDeclAlias_complete_of_body`. `genDeclDatatype_complete` takes reachability
of the block at the size in `b`; `genDeclDatatype_complete_of_MutualADTWF`
discharges that from `MutualADTWF` alone through the capstone
`genMutuallyRecursiveDatatypes_complete_of_MutualADTWF`, at the cost of an
existential size.

The two `example`s at the end of this file compose a per-step lemma through the
dispatch, the fold and the assembly of a program, for an abstract-type step and for
a datatype step. The result is a reachable whole program, so the interface of these
lemmas holds up in use.

Three items block a tighter result:

* `BitvecWidthOnly` is a hypothesis of each lemma that generates a type. It is the
  one residual condition of the arity discipline, because `Core.KnownTypes`
  registers `bitvec` at arity 1 but no `LMonoTy` argument position can hold a
  width. The hand-written `ArityOk` predicate
  that these lemmas used to carry is gone: `VocabOk` plus upstream's
  `argsWellKinded` discharge the rest of the arity discipline.
* The generator does not emit `recFuncBlock`, so the eighth constructor of
  `DeclHasType'` is unreachable by construction.
* `genLExpr` is incomplete.

**Do not read this module as a proof of completeness.** There is no whole-program
completeness theorem, and a tight theorem is not possible while `genLExpr` is
incomplete. This file proves two things. First, program reachability *reduces to*
per-declaration reachability, and this adds no obligation at the program level.
Second, 5 of the 7 per-declaration obligations are discharged.
-/

open Lambda RandomChoice Core Imperative SetGen
open DatatypeGen

namespace ProgramGen

/-! ## Fold inversion -/

/-- **Fold step composition.** Prepending a reachable step to a reachable fold
    tail gives a reachable `n+1`-step fold. -/
theorem genDeclsFold_cons_complete {s s₁ s₂ : GenState} {b : Bounds} {n : Nat}
    {ds₁ rest : List Decl}
    (hstep : (ds₁, s₁) ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b))
    (hrest : (rest, s₂) ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s₁ b n)) :
    (ds₁ ++ rest, s₂) ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s b (n + 1)) := by
  simp only [genDeclsFold, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq]
  exact ⟨(ds₁, s₁), hstep, (rest, s₂), hrest, rfl, rfl⟩

/-- **Reachability of a step kind implies reachability through the dispatch.** If
    `(ds, s')` is reachable by *any* of the seven declaration generators, it is
    reachable by `genDeclStep`.

    Deliberately stated **without mentioning the dispatch weights**. Weights are
    irrelevant to reachability — `mem_support_frequency_iff` needs only that the
    chosen entry's weight is positive, and every `genDeclStep` weight is — so
    exposing them here would make a completeness statement break whenever the
    distribution is re-tuned. The positivity witness is discharged inside the
    proof instead, one `exact` per branch. -/
theorem genDeclStep_complete_of_mem {s s' : GenState} {b : Bounds} {ds : List Decl}
    (hmem :
      (ds, s') ∈ SetGen.support (genDeclAbstract (G := SetGen.Set) s b) ∨
      (ds, s') ∈ SetGen.support (genDeclAlias (G := SetGen.Set) s b) ∨
      (ds, s') ∈ SetGen.support (genDeclAxiom (G := SetGen.Set) s b) ∨
      (ds, s') ∈ SetGen.support (genDeclDistinct (G := SetGen.Set) s b) ∨
      (ds, s') ∈ SetGen.support (genDeclDatatype (G := SetGen.Set) s b) ∨
      (ds, s') ∈ SetGen.support (genDeclFunction (G := SetGen.Set) s b) ∨
      (ds, s') ∈ SetGen.support (genDeclProcedure (G := SetGen.Set) s b)) :
    (ds, s') ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b) := by
  simp only [genDeclStep, mem_support_frequency_iff]
  -- One branch per kind, each naming its generator and that generator's weight.
  -- The weights appear *only here*, never in the statement, so re-tuning the
  -- dispatch touches at most these seven witnesses and no downstream user.
  --
  -- The last two are `wFunc`/`wProc`, which `genDeclStep` picks by phase
  -- (`(3, 4)` once a function is callable, `(6, 1)` before), so their witness is
  -- the projection of that `if` rather than a literal. `split` takes the
  -- positivity goal to one per phase, which is the whole content of "reachability
  -- does not depend on the weights": both phases keep every entry positive.
  rcases hmem with h | h | h | h | h | h | h
  · exact ⟨1, fun () => genDeclAbstract s b, by simp, by omega, h⟩
  · exact ⟨1, fun () => genDeclAlias s b, by simp, by omega, h⟩
  · exact ⟨1, fun () => genDeclAxiom s b, by simp, by omega, h⟩
  · exact ⟨1, fun () => genDeclDistinct s b, by simp, by omega, h⟩
  · exact ⟨3, fun () => genDeclDatatype s b, by simp, by omega, h⟩
  · exact ⟨(if hasCallableFunc s then (3, 4) else (6, 1)).fst,
           fun () => genDeclFunction s b, by simp, by split <;> decide, h⟩
  · exact ⟨(if hasCallableFunc s then (3, 4) else (6, 1)).snd,
           fun () => genDeclProcedure s b, by simp, by split <;> decide, h⟩

/-! ## Representative per-step reachability: axioms

For each concrete Bool expression `e` reachable by `genLExpr` at the axiom depth
and each fresh name reachable by `genFreshName`, the axiom step emits
`[.ax {name, e} .empty]`. This is the shape a caller composes with
`genLExpr_complete` (for `e`) and the name-reachability side condition. -/

theorem genDeclAxiom_complete {s : GenState} {b : Bounds} {nm : String} {e : PExpr}
    (hnm : nm ∈ SetGen.support (DatatypeGen.genFreshName (G := SetGen.Set) s.reserved))
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) [] s.octx s.pctx [] [] b.exprDepth .bool)) :
    (([mkAxiomDecl nm e]),
        { s with reserved := nm :: s.reserved }) ∈
      SetGen.support (genDeclAxiom (G := SetGen.Set) s b) := by
  simp only [genDeclAxiom, genAxiom, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq]
  exact ⟨(mkAxiomDecl nm e, nm), ⟨nm, hnm, e, he, rfl⟩, rfl, rfl⟩

/-! ## Reachability of `genNonRecursiveArgTy`

An alias body and the monotype of `distinct` both come from
`genNonRecursiveArgTy`, which is `genArgTy` at the *empty* block
(`blockRefs := []`, `recCallsAllowed := false`). The datatype development has the
difficult lemma `genArgTy_complete_of_wf`. Therefore this section must show only
that the block-shaped hypotheses of that lemma degenerate at the empty block.

They degenerate as follows:

* `ConstrArgWF [] ty` holds for **each** type. Each of the two halves needs an
  induction, because the arrow cases recurse. Neither half needs a side condition.
  See `constrArgWF_nil`.
* `BlockAbsent [] ty` is vacuous, because there is nothing to be absent.
* Three of the four fields of `NamesOk` are vacuous. Only
  `∀ kc ∈ tyCons, kc.1 ≠ "arrow"` remains.

Thus the hypotheses that remain are the free variables of the type are in the
supplied parameters, the type obeys the arities of `C` (`ArgsWellKinded`), and each
`bitvec` in it is a width (`BitvecWidthOnly`).

The arity hypotheses are at the same position as in the datatype development, and
they need no more plumbing. `VocabOk` ties the pool the generator draws from to the
arity register of `C`, so upstream's `argsWellKinded` carries the arity discipline.
`BitvecWidthOnly` is the one residual condition. -/

/-- `NotNested` is unconditional at the empty block: there are no block datatypes
    to nest. The arrow case recurses, hence the induction. -/
theorem notNested_nil (ty : LMonoTy) : NotNested [] ty := by
  induction ty using LMonoTy.induct with
  | ftvar v => exact .ftvar v
  | bitvec n => exact .bitvec n
  | tcons k args ih =>
    by_cases hba : IsBinaryArrow (.tcons k args)
    · obtain ⟨t1, t2, heq⟩ := hba
      have hmem : t1 ∈ args ∧ t2 ∈ args := by
        simp only [LMonoTy.arrow, LMonoTy.tcons.injEq] at heq
        obtain ⟨-, rfl⟩ := heq; simp
      rw [heq]
      exact .arrow t1 t2 (ih t1 hmem.1) (ih t2 hmem.2)
    · exact .headOther k args hba (by simp) (by simp) (fun a ha => ih a ha)

/-- `StrictPosUnif` is unconditional at the empty block: the uniformity obligation
    is quantified over block datatypes, of which there are none. -/
theorem strictPosUnif_nil (ty : LMonoTy) : StrictPosUnif [] ty := by
  induction ty using LMonoTy.induct with
  | ftvar v => exact .base _ (by rintro ⟨a, b, h⟩; simp [LMonoTy.arrow] at h) (by simp)
  | bitvec n => exact .base _ (by rintro ⟨a, b, h⟩; simp [LMonoTy.arrow] at h) (by simp)
  | tcons k args ih =>
    by_cases hba : IsBinaryArrow (.tcons k args)
    · obtain ⟨t1, t2, heq⟩ := hba
      have ht2 : t2 ∈ args := by
        simp only [LMonoTy.arrow, LMonoTy.tcons.injEq] at heq
        obtain ⟨-, rfl⟩ := heq; simp
      rw [heq]; exact .arrow t1 t2 (by simp) (ih t2 ht2)
    · exact .base _ hba (by simp)

/-- Every type is a well-formed constructor argument for the empty block. -/
theorem constrArgWF_nil (ty : LMonoTy) : ConstrArgWF [] ty :=
  ⟨notNested_nil ty, strictPosUnif_nil ty⟩

/-- **Reachability of `genNonRecursiveArgTy`.** A type is reachable at some size if
    its free variables are in `tyParams` and it obeys the arities of `C`. This is
    `genArgTy_complete_of_wf` with the empty-block hypotheses discharged. Only the
    arity hypotheses (`VocabOk` on the pool, `ArgsWellKinded` and `BitvecWidthOnly`
    on the type) and the free-variable condition remain.

    The statement has the `∃ size` form, as the completeness statements of the
    datatype generator do. The generator is a bounded sampler, so no *fixed* size
    can reach each type. -/
theorem genNonRecursiveArgTy_complete {baseTypes : BaseTys} {tyCons : TyCons}
    {C : LContext CoreLParams}
    (htyCons : ∀ kc ∈ tyCons, kc.1 ≠ "arrow")
    (hvocab : VocabOk C baseTypes tyCons)
    (tyParams : List TyIdentifier) (ty : LMonoTy)
    (hfv : ∀ v ∈ LMonoTy.freeVars ty, v ∈ tyParams)
    (hwk : ArgsWellKinded C [] ty)
    (hbv : BitvecWidthOnly ty) :
    ∃ size, ty ∈ SetGen.support
      (genNonRecursiveArgTy (G := SetGen.Set) baseTypes tyCons tyParams size) := by
  unfold genNonRecursiveArgTy
  refine genArgTy_complete_of_wf (block := []) (blockRefs := []) ?_ hvocab ?_ ty
    (constrArgWF_nil ty) hfv hwk hbv false (fun _ => fun d hd => absurd hd (by simp))
  · exact ⟨by simp, fun kc hkc => htyCons kc hkc, by simp, by simp⟩
  · simp

/-! ## Per-step reachability: abstract types

The abstract-type step draws a fresh name and an arity in `[0, maxTyConArity]`. It
then emits `type name (_ … _);` and adds the new type constructor to the state.
The step has no expression and no type body. Thus it is the one step whose
reachability needs only the reachability of the name and a bound on the arity. It
does not depend on `genLExpr` and it needs no arity hypothesis.

The step has two branches. `genDeclAbstract` calls `addKnownTypeWithError`. On
`.error`, the step emits no declaration and keeps the state. To get the branch
that emits a declaration, the caller must supply the `.ok` result as the
hypothesis `hC`. This is not a true restriction, because a fresh name does not
clash. But the generator has both branches, so the support lemma must show which
branch it is about. -/

/-- **Reachability of the abstract-type step, on the branch that emits.** The
    caller supplies a name that `genFreshName` can reach, an arity not more than
    `b.maxTyConArity`, and the `.ok` result that shows the name does not clash in
    `s.C`. Then the step emits `[mkAbstractTypeDecl nm ar]` and goes to the state
    `s.addAbstract nm ar C'`. -/
theorem genDeclAbstract_complete {s : GenState} {b : Bounds} {nm : String} {ar : Nat}
    {C' : LContext CoreLParams}
    (hnm : nm ∈ SetGen.support (DatatypeGen.genFreshName (G := SetGen.Set) s.reserved))
    (har : ar ≤ b.maxTyConArity)
    (hC : s.C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    (([mkAbstractTypeDecl nm ar]), s.addAbstract nm ar C') ∈
      SetGen.support (genDeclAbstract (G := SetGen.Set) s b) := by
  simp only [genDeclAbstract, genAbstractType, mem_support_bind_iff, mem_support_pure_iff]
  refine ⟨(mkAbstractTypeDecl nm ar, nm, ar), ⟨nm, hnm, ar, ?_, rfl⟩, ?_⟩
  · exact mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, har⟩
  · -- Take the `.ok` branch of the `match` using `hC`.
    rw [hC]
    exact mem_support_pure_iff.mpr rfl

/-! ## Per-step reachability: type aliases

The alias step draws a fresh name, a count of parameters, a fresh list of
parameters, and a body over the type constructors in scope *and* those parameters.
It then emits `mkAliasDecl nm body`, whose `typeArgs` field is
`(LMonoTy.freeVars body).dedup`.

Two facts give the lemma its shape:

**1. `typeArgs` is a function of the body, so it is not a free parameter.** Thus
the lemma is about the *body*. If you supply a reachable body, you get the alias
declaration that `mkAliasDecl` makes from that body. The lemma does not apply to a
well-typed alias whose declared `typeArgs` are a permutation or a superset of the
free variables of the body.

**2. The list of drawn parameters must only *include* the free variables of the
body.** The step calls `genNonRecursiveArgTy` with the drawn `tyParams`, so the
free variables of the body must come from that list. But `mkAliasDecl` then
discards `tyParams` and calculates `typeArgs` again from the body. Thus the caller
can use any list that includes those free variables. The usual selection is the
deduplicated free variables of the body. `genDeclAlias_complete_of_body` below
makes this selection. -/

/-- **Reachability of the alias step**, for a given list of drawn parameters. Three
    conditions apply. `genFreshNames` must reach `tyParams` at the length of
    `tyParams`. That length must not be more than `b.maxAliasTyParams`. And
    `genNonRecursiveArgTy` must reach `body` over the type constructors in scope and
    `tyParams`. -/
theorem genDeclAlias_complete {s : GenState} {b : Bounds} {nm : String}
    {tyParams : List TyIdentifier} {body : LMonoTy}
    (hnm : nm ∈ SetGen.support (DatatypeGen.genFreshName (G := SetGen.Set) s.reserved))
    (hlen : tyParams.length ≤ b.maxAliasTyParams)
    (hparams : tyParams ∈ SetGen.support
      (DatatypeGen.genFreshNames (G := SetGen.Set) s.reserved tyParams.length))
    (hbody : body ∈ SetGen.support
      (genNonRecursiveArgTy (G := SetGen.Set) s.baseTypes s.tyCons tyParams b.tySize)) :
    (([mkAliasDecl nm body]),
        { s with
          Γ := { s.Γ with aliases :=
                   { typeArgs := (LMonoTy.freeVars body).dedup, name := nm, type := body }
                     :: s.Γ.aliases }
          reserved := nm :: s.reserved }) ∈
      SetGen.support (genDeclAlias (G := SetGen.Set) s b) := by
  simp only [genDeclAlias, genAlias, mem_support_bind_iff, mem_support_pure_iff]
  refine ⟨(mkAliasDecl nm body, nm), ⟨nm, hnm, tyParams.length, ?_, tyParams, hparams,
            body, hbody, rfl⟩, ?_⟩
  · exact mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, hlen⟩
  · -- The `Γ`-update in `genDeclAlias` matches on `mkAliasDecl nm body`, which is
    -- syntactically a `.type (.syn …)`, so the match reduces.
    rfl

/-- **Reachability of the alias step at the usual list of parameters.** This is
    `genDeclAlias_complete` with `tyParams := (LMonoTy.freeVars body).dedup`, which
    is the list that `mkAliasDecl` calculates. Thus the caller must supply only a
    reachable body and the bound on the count of parameters. -/
theorem genDeclAlias_complete_of_body {s : GenState} {b : Bounds} {nm : String}
    {body : LMonoTy}
    (hnm : nm ∈ SetGen.support (DatatypeGen.genFreshName (G := SetGen.Set) s.reserved))
    (hlen : (LMonoTy.freeVars body).dedup.length ≤ b.maxAliasTyParams)
    (hparams : (LMonoTy.freeVars body).dedup ∈ SetGen.support
      (DatatypeGen.genFreshNames (G := SetGen.Set) s.reserved
        (LMonoTy.freeVars body).dedup.length))
    (hbody : body ∈ SetGen.support
      (genNonRecursiveArgTy (G := SetGen.Set) s.baseTypes s.tyCons
        (LMonoTy.freeVars body).dedup b.tySize)) :
    (([mkAliasDecl nm body]),
        { s with
          Γ := { s.Γ with aliases :=
                   { typeArgs := (LMonoTy.freeVars body).dedup, name := nm, type := body }
                     :: s.Γ.aliases }
          reserved := nm :: s.reserved }) ∈
      SetGen.support (genDeclAlias (G := SetGen.Set) s b) :=
  genDeclAlias_complete hnm hlen hparams hbody

/-! ## Per-step reachability: `distinct`

The `distinct` step draws a fresh name, one monotype `τ` over the type
constructors in scope, a count of constants, and that many fresh constant names.
It declares each constant as a 0-ary function at `τ`, and then emits
`distinct[nm] c₁ … cₙ`. Each element is the annotated operator
`.op () ⟨c, ()⟩ (some τ)`, which `distinctElems` builds.

This step *does* contain expressions. But `distinctElems` builds each expression
directly as an annotated `.op` node, and the step does not call `genLExpr`. Thus,
as for the two steps above, this step does not depend on the completeness of the
expression generator.

The step has two branches. It declares the constants through `addConstants`, which
is a fold of `addFactoryFunctionWithError` over the names, and it emits nothing
when any one of those adds fails. So the caller supplies the `some` result as the
hypothesis `hadd`, just as the abstract-type step takes an `.ok` result. Fresh
names do not clash, so this is no true restriction. -/

/-- **Reachability of the `distinct` step, on the branch that emits.** The caller
    supplies a fresh name, a reachable monotype `τ`, a reachable list of constant
    names whose length is not more than `b.maxDistinctVars`, and the `some` result
    of `addConstants`. Then the step emits the constant declarations followed by the
    `distinct` declaration over those names, each element annotated at `τ`.

    The constant names are drawn against `nm :: s.reserved`, which is what the
    generator does, so they are distinct from each other *and* from the
    declaration's own name. -/
theorem genDeclDistinct_complete {s : GenState} {b : Bounds} {nm : String}
    {τ : LMonoTy} {constNames : List String} {C' : LContext CoreLParams}
    {constDecls : List Decl}
    (hnm : nm ∈ SetGen.support (DatatypeGen.genFreshName (G := SetGen.Set) s.reserved))
    (hτ : τ ∈ SetGen.support
      (genNonRecursiveArgTy (G := SetGen.Set) s.baseTypes s.tyCons [] b.tySize))
    (hlen : constNames.length ≤ b.maxDistinctVars)
    (hconsts : constNames ∈ SetGen.support
      (DatatypeGen.genFreshNames (G := SetGen.Set) (nm :: s.reserved) constNames.length))
    (hadd : addConstants s.C τ constNames = some (C', constDecls)) :
    ((constDecls ++ [mkDistinctDecl nm (distinctElems τ constNames)]),
        { s with C := C', reserved := constNames ++ nm :: s.reserved }) ∈
      SetGen.support (genDeclDistinct (G := SetGen.Set) s b) := by
  simp only [genDeclDistinct, genDistinctAssertion, mem_support_bind_iff]
  refine ⟨(nm, τ, constNames),
          ⟨nm, hnm, τ, hτ, constNames.length,
           mem_support_chooseNat_iff.mpr ⟨Nat.zero_le _, hlen⟩, constNames, hconsts, rfl⟩, ?_⟩
  -- Take the branch of the `match` that emits, using `hadd`.
  rw [hadd]
  exact mem_support_pure_iff.mpr rfl

/-! ## Per-step reachability: datatype blocks

The datatype step draws a block over the *combined* pool `s.tyCons ++ s.dtCons`
(the external applied constructors, plus the datatypes that earlier blocks
declared — interleaving direction (4)), and then gates on
`LContext.addMutualBlock`. The generator pins the `CoreLParams`-native
`Inhabited`/`ToFormat` instances at that gate, so the hypothesis below pins them
too and matches the generator with no instance-diamond bridge.

Unlike the three steps above, this step *does* generate types, so the arity
hypotheses apply. But it does **not** call `genLExpr`: a datatype block is types
only. That is why
the step is provable, and it is the fourth of the four `genLExpr`-free kinds.

Two lemmas, in the same relation as `genDeclAlias_complete` to
`genDeclAlias_complete_of_body`. The first takes reachability of the block at the
size in `b` as a hypothesis. The second discharges that hypothesis from
`MutualADTWF` alone, through the capstone
`genMutuallyRecursiveDatatypes_complete_of_MutualADTWF`, at the cost of an
existential size. -/

/-- **Reachability of the datatype step**, given a reachable block and the `.ok`
    branch of the gate. The state grows in six fields: `C` by the block, `reserved`
    and `dtCons` by the names of the block, and the three operator contexts by the
    block's derived functions. Each datatype enters `dtCons` at its own arity, which
    is `typeArgs.length`. -/
theorem genDeclDatatype_complete {s : GenState} {b : Bounds}
    {block : MutualDatatype Unit} {C' : LContext CoreLParams}
    (hblock : block ∈ SetGen.support
      (DatatypeGen.genMutuallyRecursiveDatatypes (G := SetGen.Set)
        s.baseTypes (s.tyCons ++ s.dtCons) b.maxExtraDatatypes b.maxTyParams
        b.maxExtraBaseConstrs b.maxRecConstrs b.maxArgs b.maxDatatypeSize s.reserved))
    (hC : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams s.C block = .ok C') :
    (([.type (.data block) .empty]),
        { s with C := C'
                 reserved := block.map (·.name) ++ s.reserved
                 dtCons := block.map (fun d => (d.name, d.typeArgs.length)) ++ s.dtCons
                 octx := OpCtx.ofList (adtDerivedOps block b.derivedFamilies ++ s.octx.ops)
                 pctx := adtDerivedPolyOps block b.derivedFamilies ++ s.pctx
                 derivedPctx :=
                   adtDerivedPolyOps block b.derivedFamilies ++ s.derivedPctx }) ∈
      SetGen.support (genDeclDatatype (G := SetGen.Set) s b) := by
  simp only [genDeclDatatype, mem_support_bind_iff]
  refine ⟨block, hblock, ?_⟩
  -- Take the `.ok` branch of the gate using `hC`.
  rw [hC]
  exact mem_support_pure_iff.mpr rfl

open Core.TypeSpec DatatypeGen in
/-- **Reachability of the datatype step from `MutualADTWF` alone.** This is
    `genDeclDatatype_complete` with its block hypothesis discharged by the capstone
    `genMutuallyRecursiveDatatypes_complete_of_MutualADTWF`. The caller gives no
    order of the datatypes and no rank; the capstone builds those itself.

    The side conditions are the capstone's, at the combined pool
    `s.tyCons ++ s.dtCons` and at `extraReserved := s.reserved`. They are the
    reachability and the freshness of the names and the parameters,
    `hasDefaultTesterName`, the limits of the generator, `VocabOk` on the pool and
    `BitvecWidthOnly` on each constructor argument type.

    The size is existential, for the reason it is existential in the capstone: a
    constructor argument type can be of any size, so no fixed `maxDatatypeSize`
    reaches every block. Hence the conclusion varies that one field of `b`. -/
theorem genDeclDatatype_complete_of_MutualADTWF {s : GenState} {b : Bounds}
    {block : MutualDatatype Unit} {C' : LContext CoreLParams}
    (hn : NamesOk s.baseTypes (s.tyCons ++ s.dtCons) (block.map (·.name)))
    (hwf : MutualADTWF s.C block)
    (hnew : ∀ d ∈ block, s.C.datatypes.getType d.name = none)
    (hcount : block.length ≤ b.maxExtraDatatypes + 1)
    (hnamesIdent : ∀ d ∈ block, d.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hnamesFresh : ∀ d ∈ block,
      d.name ∉ initialReserved s.baseTypes (s.tyCons ++ s.dtCons) s.reserved)
    (hparamsLen : ∀ d ∈ block, d.typeArgs.length ≤ b.maxTyParams)
    (hparamsNodup : ∀ d ∈ block, d.typeArgs.Nodup)
    (hparamsIdent : ∀ d ∈ block, ∀ p ∈ d.typeArgs,
      p ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hparamsFresh : ∀ d ∈ block, ∀ p ∈ d.typeArgs,
      p ∉ block.map (·.name)
        ++ initialReserved s.baseTypes (s.tyCons ++ s.dtCons) s.reserved)
    (hctors_nf : ∀ d ∈ block, ∀ c ∈ d.constrs, hasDefaultTesterName c)
    (hctors_len : ∀ d ∈ block, ∀ c ∈ d.constrs, c.args.length ≤ b.maxArgs)
    (hnames_ident : ∀ d ∈ block, ∀ nm' ∈ ctorsNames d.constrs,
      nm' ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hnames_nd : ∀ d ∈ block, (ctorsNames d.constrs).Nodup)
    (hnames_fresh : ∀ d ∈ block, ∀ nm' ∈ ctorsNames d.constrs,
      nm' ∉ d.typeArgs ++ (block.map (·.name)
        ++ initialReserved s.baseTypes (s.tyCons ++ s.dtCons) s.reserved))
    (hreclen : ∀ d ∈ block, d.constrs.length ≤ b.maxRecConstrs + 1)
    (hvocab : VocabOk s.C s.baseTypes (s.tyCons ++ s.dtCons))
    (hbv : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, BitvecWidthOnly arg.2)
    (hC : @LContext.addMutualBlock CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams s.C block = .ok C') :
    ∃ sz, (([.type (.data block) .empty]),
        { s with C := C'
                 reserved := block.map (·.name) ++ s.reserved
                 dtCons := block.map (fun d => (d.name, d.typeArgs.length)) ++ s.dtCons
                 octx := OpCtx.ofList (adtDerivedOps block b.derivedFamilies ++ s.octx.ops)
                 pctx := adtDerivedPolyOps block b.derivedFamilies ++ s.pctx
                 derivedPctx :=
                   adtDerivedPolyOps block b.derivedFamilies ++ s.derivedPctx }) ∈
      SetGen.support
        (genDeclDatatype (G := SetGen.Set) s { b with maxDatatypeSize := sz }) := by
  obtain ⟨sz, hblock⟩ := genMutuallyRecursiveDatatypes_complete_of_MutualADTWF
    (maxExtraDatatypes := b.maxExtraDatatypes) (maxTyParams := b.maxTyParams)
    (maxExtraBaseConstrs := b.maxExtraBaseConstrs) (maxRecConstrs := b.maxRecConstrs)
    (maxArgs := b.maxArgs) (extraReserved := s.reserved)
    hn hwf hnew hcount hnamesIdent hnamesFresh hparamsLen hparamsNodup hparamsIdent
    hparamsFresh hctors_nf hctors_len hnames_ident hnames_nd hnames_fresh hreclen
    hvocab hbv
  exact ⟨sz, genDeclDatatype_complete (b := { b with maxDatatypeSize := sz }) hblock hC⟩

/-! ## Program assembly

`genProgram` is `genDeclsFold` from `initState` wrapped into a `Program`. So a
reachable fold trace gives a reachable program. -/

theorem genProgram_complete_of_fold {numDecls : Nat} {b : Bounds} {decls : List Decl}
    {sf : GenState}
    (h : (decls, sf) ∈ SetGen.support (genDeclsFold (G := SetGen.Set) initState b numDecls)) :
    (Program.mk (decls := decls)) ∈ SetGen.support (genProgram (G := SetGen.Set) numDecls b) := by
  simp only [genProgram, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨(decls, sf), h, rfl⟩

/-! ## The reduction, in use from end to end

This section shows that the lemmas above fit together. Each `example` composes a
reachable step through three lemmas: the weighted dispatch
(`genDeclStep_complete_of_mem`), the fold (`genDeclsFold_cons_complete`), and the
assembly of the program (`genProgram_complete_of_fold`). The result is a reachable
*whole program*.

There are two, at the opposite ends of the range of the steps. The first is the
abstract-type step, which is the most simple kind, and it grows one field of the
state. The second is the datatype step, which grows three (`C`, `reserved` and
`dtCons`) and passes through the `addMutualBlock` gate. The second is therefore the
one that checks that the state a per-step lemma *names* is the state the fold
*threads*, which a one-field step cannot really test.

Both typecheck with no adjustment beyond `simpa` or `simp [genDeclsFold]`, so the
interface of the lemmas holds up in use. These are the paths in the package from a
fact about a declaration to the support of `genProgram`. They remain narrow, because
each has a single declaration. -/

example (b : Bounds) (nm : String) (ar : Nat) (C' : LContext Core.CoreLParams)
    (hnm : nm ∈ SetGen.support
      (DatatypeGen.genFreshName (G := SetGen.Set) initState.reserved))
    (har : ar ≤ b.maxTyConArity)
    (hC : initState.C.addKnownTypeWithError { name := nm, metadata := ar } default = .ok C') :
    (Core.Program.mk (decls := [mkAbstractTypeDecl nm ar])) ∈
      SetGen.support (genProgram (G := SetGen.Set) 1 b) := by
  refine genProgram_complete_of_fold (sf := initState.addAbstract nm ar C') ?_
  have hstep := genDeclAbstract_complete (s := initState) (b := b) hnm har hC
  have hdispatch := genDeclStep_complete_of_mem (s := initState) (b := b)
    (ds := [mkAbstractTypeDecl nm ar]) (Or.inl hstep)
  have hfold := genDeclsFold_cons_complete (n := 0) hdispatch
    (show ([], initState.addAbstract nm ar C') ∈
      SetGen.support (genDeclsFold (G := SetGen.Set) (initState.addAbstract nm ar C') b 0) from by
      simp [genDeclsFold])
  simpa using hfold

/-- The same composition for the **datatype** step, which is the step that grows
    six fields of the state at once (`C`, `reserved`, `dtCons` and the three operator
    contexts). It therefore
    checks the part of the interface that the abstract-type path above does not: that
    the state which `genDeclDatatype_complete` names is exactly the state the fold
    threads onward. -/
example (b : Bounds) (block : MutualDatatype Unit) (C' : LContext Core.CoreLParams)
    (hblock : block ∈ SetGen.support
      (DatatypeGen.genMutuallyRecursiveDatatypes (G := SetGen.Set)
        initState.baseTypes (initState.tyCons ++ initState.dtCons)
        b.maxExtraDatatypes b.maxTyParams b.maxExtraBaseConstrs b.maxRecConstrs
        b.maxArgs b.maxDatatypeSize initState.reserved))
    (hC : @LContext.addMutualBlock Core.CoreLParams _ instInhabitedPUnit instInhabitedPUnit
      instToFormatIDMetaCoreLParams initState.C block = .ok C') :
    (Core.Program.mk (decls := [.type (.data block) .empty])) ∈
      SetGen.support (genProgram (G := SetGen.Set) 1 b) := by
  have hstep := genDeclDatatype_complete (s := initState) (b := b) hblock hC
  have hdispatch := genDeclStep_complete_of_mem (s := initState) (b := b)
    (ds := [.type (.data block) .empty])
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hstep)))))
  refine genProgram_complete_of_fold
    (sf := { initState with C := C'
                            reserved := block.map (·.name) ++ initState.reserved
                            dtCons := block.map (fun d => (d.name, d.typeArgs.length))
                              ++ initState.dtCons
                            octx := OpCtx.ofList
                              (adtDerivedOps block b.derivedFamilies ++ initState.octx.ops)
                            pctx :=
                              adtDerivedPolyOps block b.derivedFamilies ++ initState.pctx
                            derivedPctx := adtDerivedPolyOps block b.derivedFamilies
                              ++ initState.derivedPctx }) ?_
  refine genDeclsFold_cons_complete (n := 0) (rest := []) hdispatch ?_
  simp [genDeclsFold]

end ProgramGen
