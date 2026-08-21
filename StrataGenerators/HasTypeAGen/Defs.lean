import StrataGenerators.HasTypeAGen.Core
import Strata.DL.Lambda.Factory
import Strata.Languages.Core.FactoryWF

open Lambda RandomChoice

/-!
# The definitions of the generator for a well-typed `LExpr`, without Mathlib

This file exports the core definitions of the generator again, and it adds the wrappers that
take a `Factory`. It needs no part of Mathlib.

The main `HasTypeAGen` module exports each definition of this file, and it adds the proofs of
soundness and of completeness.
-/

-- This line exports each definition of the core module again.
export ArbNat (Nat.arbitrary)

-- ── How the module reads a `Factory` ────────────────────────────────

/-- The flat list of operators of a `Factory`. The function computes the type of each operation as a
    chain of arrows, from its inputs to its output.

    `mkArrow'` builds that chain. It is exactly the *generic type* form that `OpsConsistent` and
    `OpsConsistentR` give to each operator, which is `mkArrow' fn.output fn.inputs.values`. This
    function uses the same builder, so the annotation that the generator puts on an `.op` node from
    `factoryOps` *is*, by definition, the generic type of the operator. A proof of op-consistency
    therefore needs no reconciliation between `destructArrow` and `mkArrow`, and it needs no side
    condition such as `ArrowSpineOK` or `FactoryOutputWF`. -/
def factoryOps (F : @Factory LExprParams') : OpCtx :=
  OpCtx.ofList <| F.toArray.toList.filterMap fun f =>
    some (f.name.name, LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))

/-- `coreMonoOps` equals `factoryOps Core.Factory`.

    `coreMonoOps` is in the core module, and that module cannot call `factoryOps`, because this file
    imports it. `coreMonoOps` therefore repeats the body of `factoryOps`. This theorem joins the two
    definitions: a change to one of them alone makes the build fail here, and it does not let the
    vocabulary of operators of the generators differ from the factory in silence. -/
theorem coreMonoOps_eq_factoryOps : coreMonoOps = factoryOps Core.Factory := rfl

/-- The context of polymorphic operators of a `Factory`. The function records the full type *scheme*
    of each operation: it quantifies over the type arguments of the operation, and it then makes a
    chain of arrows from the inputs to the output.

    This function is the polymorphic form of `factoryOps`. `factoryOps` reduces each function to one
    `LMonoTy` and it loses the polymorphism. `factoryPolyOps` keeps the scheme `∀ typeArgs. …`, and
    the polymorphic rules of the generator need that scheme. Those rules are `genIndirPoly` and
    `findPolymorphicOps`. The scheme uses the same `mkArrow'` builder as `factoryOps`, so an entry
    here is *by construction* the generic type of a real function of the factory. That is exactly the
    condition `PCtxWF F` for good form, and a lemma proves it and does not assume it. -/
def factoryPolyOps (F : @Factory LExprParams') : PolyOpCtx :=
  F.toArray.toList.filterMap fun f =>
    some (f.name.name,
      Lambda.LTy.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))

/-- Each entry of `corePolyOps` is an entry of `factoryPolyOps Core.Factory`.

    `corePolyOps` must repeat the body of `factoryPolyOps`, because it is in the core module and this
    file imports that module. This theorem therefore keeps the two definitions in agreement. It is
    also the fact that `PCtxWF Core.Factory corePolyOps` needs: an entry of `corePolyOps` is the
    generic type of a real function of the factory, and not a form that someone wrote by hand. -/
theorem corePolyOps_subset_factoryPolyOps :
    ∀ e ∈ corePolyOps, e ∈ factoryPolyOps Core.Factory := by
  intro e he
  simp only [corePolyOps, List.mem_filterMap] at he
  obtain ⟨f, hf, hfe⟩ := he
  refine List.mem_filterMap.mpr ⟨f, hf, ?_⟩
  split at hfe
  · exact absurd hfe (by simp)
  · exact hfe

-- No entry is *absent* either: `corePolyOps` is exactly the polymorphic part of the factory. This
-- guard uses evaluation and not `rfl`, because `rfl` does not reduce through the whole factory,
-- which holds 353 entries. The guard finds an operator that `corePolyOps` misses, such as
-- `Sequence.select!`, `mapConst` or `TriggerGroup.addTrigger`.
#guard corePolyOps ==
  (factoryPolyOps Core.Factory).filter (fun e => !(e.2.boundVars.isEmpty))

/-- **Each type scheme of the real vocabulary of operators is closed.** A scheme is closed when its
    binder list holds each free type variable of its monotype.

    The `hclosed` part of `SchemeInstAt` is the one condition that stays a premise. This theorem
    shows that the condition is easy to meet: each entry of `factoryPolyOps` of a well-formed factory
    meets it. A caller with a concrete `pctx` can discharge `hclosed` in the same way.

    The proof uses an invariant of upstream, and it does not enumerate the entries. `FuncWF`, which
    `LFuncWF` extends, holds the fields `inputs_typevars_in_typeArgs` and
    `output_typevars_in_typeArgs`, and upstream proves `Core.Factory_wf`. Closedness of a scheme
    therefore holds for *each* well-formed factory. A proof by `decide` cannot work here, because the
    kernel does not reduce through the whole factory, which holds 353 entries. -/
theorem factoryPolyOps_closed {F : @Lambda.Factory LExprParams'}
    (hwf : Lambda.FactoryWF F) :
    ∀ p ∈ factoryPolyOps F,
      match p.2 with
      | .forAll boundVars monoTy => ∀ v ∈ monoTy.freeVars, v ∈ boundVars := by
  -- A free variable of `mkArrow' out ins` is a free variable of the output, or it is a free variable
  -- of an input.
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

/-- Each type scheme in `corePolyOps` is closed. This is `factoryPolyOps_closed` at
    `Core.Factory`. -/
theorem corePolyOps_closed :
    ∀ p ∈ corePolyOps,
      match p.2 with
      | .forAll boundVars monoTy => ∀ v ∈ monoTy.freeVars, v ∈ boundVars :=
  fun p hp => factoryPolyOps_closed Core.Factory_wf p
    (corePolyOps_subset_factoryPolyOps p hp)

-- ── The wrappers that take a `Factory` ──────────────────────────────

/-- Makes a well-typed `LExpr` and takes its operators from a `Factory`. This wrapper around
    `genLExpr` turns the factory into an `OpCtx` with `factoryOps`. It uses the `Indir` rule and the
    `IndirPoly` rule, so it makes an application of an operator to each of its arguments. -/
def genLExprWithFactory [Gen G] (fctx : FVarCtx) (F : @Factory LExprParams')
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (pctx : PolyOpCtx := factoryPolyOps F) : G LExpr' :=
  genLExpr fctx (factoryOps F) pctx tvars bctx depth τ

/-- Makes a well-typed closed expression, which holds no free variable, and takes its operators from
    the given factory. -/
def genClosedLExprWithFactory [Gen G] (F : @Factory LExprParams')
    (tvars : List TyIdentifier) (depth : Nat)
    (pctx : PolyOpCtx := factoryPolyOps F) : G LExpr' := do
  let τ ← genLMonoTy tvars depth
  genLExprWithFactory [] F tvars [] depth τ pctx

/-- Makes a well-typed `LExpr` from an operator context and a context of polymorphic operators that
    the caller gives. This wrapper around `genLExpr` needs no `Factory` value.

    The wrapper gives `retryCont` to `genLExpr` without a change. That continuation retries a draw
    when a subterm fails, and it applies at each level of the nesting. Its default value is `id`,
    which makes no retry. The test harness gives `retryGenArg` here. The documentation of `genLExpr`
    gives the full reason. -/
def genLExprWithOps [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx)
    (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat := 3)
    (retryCont : (LMonoTy → G LExpr') → (LMonoTy → G LExpr') := id) : G LExpr' :=
  genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs retryCont
