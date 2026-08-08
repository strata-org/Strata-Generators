import StrataGenerators.ProgramGen

/-!
# Completeness of the whole-program generator (fold inversion)

As documented in `docs/program-gen-completeness.md`, a monolithic
"every `ProgramHasTypeA` program is reachable" theorem is inherently false for a
*bounded sampler* without a union of per-declaration reachability side conditions
(the same reason datatype completeness needs `ArityOk`; see
`docs/mutualadtwf-arity-gap.md`).

What *is* cleanly provable — and is the useful completeness contribution — is that
the **fold composes**: if each declaration step is individually reachable from its
incoming state, the whole declaration list is reachable by `genDeclsFold`, and
hence the assembled `Program` by `genProgram`. Composed with the sub-generators'
own completeness lemmas (`genFunction_complete`, `genArgTy_complete_of_MutualADTWF`,
`genLExpr_complete`), this reduces program reachability to per-declaration
reachability with no new program-level obligation.

This file proves that composition, plus a representative per-step reachability
lemma (the axiom step) to demonstrate the shape callers use.

## Status: this module is an API with no consumers yet

**Every lemma here is currently unused** — each has exactly one occurrence in the
package, its own declaration. That is deliberate rather than dead code: these are
the *reduction* half of completeness, waiting on the per-declaration reachability
lemmas that do not exist yet. Only `genDeclAxiom_complete` (one of seven kinds) is
written; abstract types, aliases, `distinct`, datatype blocks, functions and
procedures still need theirs. Repo issue #66 catalogues that, along with the other
blockers (`genIdentName` has no two-directional support lemma, `ArityOk` needs a
Strata-side fix, `recFuncBlock` is not generated, and `genLExpr` is itself
incomplete — issue #64).

Two consequences worth knowing before building on this:

* **The interface is unexercised.** Because nothing consumes these lemmas, their
  ergonomics are untested; the first real caller may well want a different shape.
  Treat the signatures as provisional and change them freely rather than working
  around them.
* **Do not read the presence of this module as "completeness is proved."** There is
  no whole-program completeness theorem, and there cannot be a tight one until at
  least #64 is closed. What is proved is that program reachability *reduces to*
  per-declaration reachability with no new program-level obligation.
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
  -- dispatch touches at most these seven literals and no downstream user.
  rcases hmem with h | h | h | h | h | h | h
  · exact ⟨1, fun () => genDeclAbstract s b, by simp, by omega, h⟩
  · exact ⟨1, fun () => genDeclAlias s b, by simp, by omega, h⟩
  · exact ⟨1, fun () => genDeclAxiom s b, by simp, by omega, h⟩
  · exact ⟨1, fun () => genDeclDistinct s b, by simp, by omega, h⟩
  · exact ⟨3, fun () => genDeclDatatype s b, by simp, by omega, h⟩
  · exact ⟨3, fun () => genDeclFunction s b, by simp, by omega, h⟩
  · exact ⟨4, fun () => genDeclProcedure s b, by simp, by omega, h⟩

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

/-! ## Program assembly

`genProgram` is `genDeclsFold` from `initState` wrapped into a `Program`. So a
reachable fold trace gives a reachable program. -/

theorem genProgram_complete_of_fold {numDecls : Nat} {b : Bounds} {decls : List Decl}
    {sf : GenState}
    (h : (decls, sf) ∈ SetGen.support (genDeclsFold (G := SetGen.Set) initState b numDecls)) :
    (Program.mk (decls := decls)) ∈ SetGen.support (genProgram (G := SetGen.Set) numDecls b) := by
  simp only [genProgram, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨(decls, sf), h, rfl⟩

end ProgramGen
