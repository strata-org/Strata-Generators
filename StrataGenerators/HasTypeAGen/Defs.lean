import StrataGenerators.HasTypeAGen.Core
import Strata.DL.Lambda.Factory
import Strata.Languages.Core.FactoryWF

open Lambda RandomChoice

/-!
# Generator definitions for well-typed `LExpr`s (lightweight, no Mathlib)

This file re-exports the core generator definitions from `Core.lean` and adds
`Factory`-accepting wrappers.

The full `HasTypeAGen` module re-exports everything here plus soundness/completeness proofs.
-/

-- Re-export everything from Core
export ArbNat (Nat.arbitrary)

-- ── Factory conversion ──────────────────────────────────────────────

/-- Extract the flat operator list from a `Factory` by computing the curried
    type of each operation (inputs → output).

    The curried type is built with `mkArrow'` — exactly the *generic type* form
    `OpsConsistent`/`OpsConsistentR` canonicalize each operator to
    (`mkArrow' fn.output fn.inputs.values`). Using the same builder here means the
    annotation the generator stamps on a `factoryOps`-sourced `.op` node *is*
    definitionally the operator's generic type, so no `destructArrow`/`mkArrow`
    reconciliation (nor an `ArrowSpineOK`/`FactoryOutputWF` side condition) is
    needed to see it is op-consistent. -/
def factoryOps (F : @Factory LExprParams') : OpCtx :=
  OpCtx.ofList <| F.toArray.toList.filterMap fun f =>
    some (f.name.name, LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))

/-- `coreMonoOps` is `factoryOps` applied to `Core.Factory`.

    `coreMonoOps` lives in `HasTypeAGen/Core.lean`, and that file cannot call
    `factoryOps`, because this file imports it. Therefore `coreMonoOps` repeats the
    body of `factoryOps`. This lemma pins the two together: a change to one of them
    and not the other makes the build fail here, instead of making the operator
    vocabulary of the generators drift from the factory in silence. -/
theorem coreMonoOps_eq_factoryOps : coreMonoOps = factoryOps Core.Factory := rfl

/-- Extract the polymorphic operator context from a `Factory` by recording each
    operation's full type *scheme*: quantify over the operation's type arguments,
    then curry its inputs to its output.

    This is the polymorphic analogue of `factoryOps`. Where `factoryOps` collapses
    each function to a single `LMonoTy` (losing polymorphism), `factoryPolyOps`
    keeps the `∀ typeArgs. …` scheme that the polymorphic generation rules
    (`genIndirPoly`/`findPolymorphicOps`) need. The scheme is built with the same
    `mkArrow'` builder as `factoryOps`, so an entry here is *by construction* the
    generic type of a real factory function — that is exactly the `PCtxWF F`
    well-formedness condition, discharged as a lemma rather than assumed. -/
def factoryPolyOps (F : @Factory LExprParams') : PolyOpCtx :=
  F.toArray.toList.filterMap fun f =>
    some (f.name.name,
      Lambda.LTy.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))

/-- Every `corePolyOps` entry is a genuine `factoryPolyOps Core.Factory` entry.

    `corePolyOps` has to repeat `factoryPolyOps`' body (it lives in `HasTypeAGen/Core.lean`,
    which this file imports), so this is what keeps the two from drifting. It is also the
    fact `PCtxWF Core.Factory corePolyOps` needs: an entry of `corePolyOps` is the generic
    type of a real factory function, not a hand-written approximation of one. -/
theorem corePolyOps_subset_factoryPolyOps :
    ∀ e ∈ corePolyOps, e ∈ factoryPolyOps Core.Factory := by
  intro e he
  simp only [corePolyOps, List.mem_filterMap] at he
  obtain ⟨f, hf, hfe⟩ := he
  refine List.mem_filterMap.mpr ⟨f, hf, ?_⟩
  split at hfe
  · exact absurd hfe (by simp)
  · exact hfe

-- …and nothing is *missing*: `corePolyOps` is exactly the polymorphic part of the factory.
-- Checked by evaluation rather than `rfl`, which does not reduce through the 353-entry
-- factory. This is the guard that would have caught `Sequence.select!`, `mapConst` and
-- `TriggerGroup.addTrigger` being absent from the old hand-written list.
#guard corePolyOps ==
  (factoryPolyOps Core.Factory).filter (fun e => !(e.2.boundVars.isEmpty))

/-- **Scheme closedness holds for the real operator vocabulary.**

    The `hclosed` conjunct of `SchemeInstAt` is the one condition that stays as a
    premise. This theorem shows that the condition is easy to satisfy: every entry of
    `corePolyOps` satisfies it. A caller that has a concrete `pctx` can discharge
    `hclosed` the same way.

    Now that `corePolyOps` is derived from `Core.Factory`, this is *proved* rather than
    `decide`d — and from an upstream invariant rather than by enumeration. `FuncWF` (which
    `LFuncWF` extends) carries `inputs_typevars_in_typeArgs` and
    `output_typevars_in_typeArgs`, and upstream proves `Core.Factory_wf`, so scheme
    closedness holds for *any* well-formed factory (`factoryPolyOps_closed`). The old
    `by decide` could not survive the change anyway: the kernel does not reduce through the
    353-entry factory. -/
theorem factoryPolyOps_closed {F : @Lambda.Factory LExprParams'}
    (hwf : Lambda.FactoryWF F) :
    ∀ p ∈ factoryPolyOps F,
      match p.2 with
      | .forAll boundVars monoTy => ∀ v ∈ monoTy.freeVars, v ∈ boundVars := by
  -- `freeVars (mkArrow' out ins)` splits into the output's and the inputs' free vars.
  have hsplit : ∀ (out : LMonoTy) (vals : List LMonoTy) (v : TyIdentifier),
      v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' out vals) →
      v ∈ LMonoTy.freeVars out ∨ ∃ t ∈ vals, v ∈ LMonoTy.freeVars t := by
    intro out vals v hv
    induction vals with
    | nil => exact Or.inl (by rwa [LMonoTy.mkArrow'_nil] at hv)
    | cons t rest ih =>
      rw [LMonoTy.mkArrow'_cons, LMonoTy.arrow] at hv
      simp only [LMonoTy.freeVars, LMonoTys.freeVars_of_cons, List.mem_append] at hv
      rcases hv with hv | hv
      · exact Or.inr ⟨t, List.mem_cons_self, hv⟩
      · rcases ih (by
          simp only [LMonoTys.freeVars] at hv
          rcases hv with hv | hv
          · exact hv
          · simp at hv) with h | ⟨t', ht', hv'⟩
        · exact Or.inl h
        · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hv'⟩
  intro p hp
  simp only [factoryPolyOps, List.mem_filterMap, Option.some.injEq] at hp
  obtain ⟨f, hf, rfl⟩ := hp
  intro v hv
  have hfwf := hwf.lfuncs_wf f (Array.mem_def.mpr hf)
  rcases hsplit f.output (f.inputs.map Prod.snd) v hv with hout | ⟨t, htmem, hvt⟩
  · exact hfwf.output_typevars_in_typeArgs hout
  · exact hfwf.inputs_typevars_in_typeArgs t (by rwa [ListMap.values_eq_map_snd]) hvt

theorem corePolyOps_closed :
    ∀ p ∈ corePolyOps,
      match p.2 with
      | .forAll boundVars monoTy => ∀ v ∈ monoTy.freeVars, v ∈ boundVars :=
  fun p hp => factoryPolyOps_closed Core.Factory_wf p
    (corePolyOps_subset_factoryPolyOps p hp)

-- ── Factory-accepting wrappers ──────────────────────────────────────

/-- Generate a well-typed `LExpr` using a `Factory` for operators.
    This is a convenience wrapper around `genLExpr` that converts the factory
    to an `OpCtx` via `factoryOps`. Uses the Indir and IndirPoly rules to
    generate fully-applied operator applications. -/
def genLExprWithFactory [Gen G] (fctx : FVarCtx) (F : @Factory LExprParams')
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (pctx : PolyOpCtx := factoryPolyOps F) : G LExpr' :=
  genLExpr fctx (factoryOps F) pctx tvars bctx depth τ

/-- Generate a well-typed closed expression (no free variables) using the
    given factory for operators. -/
def genClosedLExprWithFactory [Gen G] (F : @Factory LExprParams')
    (tvars : List TyIdentifier) (depth : Nat)
    (pctx : PolyOpCtx := factoryPolyOps F) : G LExpr' := do
  let τ ← genLMonoTy tvars depth
  genLExprWithFactory [] F tvars [] depth τ pctx

/-- Generate a well-typed `LExpr` using explicit operator and polymorphic
    operator contexts. This is a convenience wrapper around `genLExpr` that
    avoids requiring a `Factory` value.

    `retryCont` is forwarded verbatim to `genLExpr`: it is the continuation invoked
    to retry generation when a subterm fails, applied at every nesting level. It
    defaults to `id` (no retrying), so existing call sites are unaffected; the test
    harness passes `retryGenArg` here. See `genLExpr` for the full rationale. -/
def genLExprWithOps [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx)
    (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat := 3)
    (retryCont : (LMonoTy → G LExpr') → (LMonoTy → G LExpr') := id) : G LExpr' :=
  genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs retryCont
