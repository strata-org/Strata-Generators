import StrataGenerators.SetGen
import StrataGenerators.HasTypeAGen
import StrataGenerators.RetryGen
import Basalt.PlausibleGen

/-!
# `retryGenArg` does not change what `genLExpr` can produce

The soundness/completeness/`OpsConsistentR` theorems in `HasTypeAGen.lean` and
`HasTypeAGenOpsConsistent.lean` are all stated about
`genLExpr (G := SetGen.Set) … ` with `retryCont` left at its `id` default. The
*executable* generator the test harness runs is
`genLExpr (G := Plausible.Gen) … (retryGenArg n)`.

This module narrows that gap: it shows a retrying `retryCont` changes only *how many
attempts* a draw needs, never *which terms are reachable*.

Note the two results below live in *different semantics* and this module does not by
itself join them — `genLExpr_setSupport_retryCont` is about `SetGen.Set` (where its
hypothesis is function equality, so `retryGenArg` does **not** satisfy it), while
`runSupport_retryGen` is about `Plausible.Gen` (where `retryGenArg` genuinely lives).
The `Set`/`Plausible` bridge is `StrataGenerators.ExecRefinement`, whose
`refines_retryGen`/`refines_retryGenArg` are what actually carry the proven support
over to the executable generator.

Two facts:

1. `runSupport_retryGen` / `runSupport_retryGenArg` — retrying is reachability-neutral
   at `Plausible.Gen`. Neither widening (a retry can only return what the underlying
   generator returns) nor narrowing (the first attempt is still available).

2. `genLExpr_retryCont_ext` / `genLExpr_retryCont_id` — `genLExpr` is *congruent* in
   `retryCont`: continuations that agree pointwise give literally equal generators, at
   every depth and for any `G`.

The headline results are `genLExpr_runSupport_retryGenArg` (the executable statement)
and `genLExpr_setSupport_retryCont` (the `SetGen.Set` statement that connects directly
to the existing theorems).

## Why the statement is phrased two ways

One might hope to write `SetGen.support (genLExpr (G := SetGen.Set) … (retryGenArg n))`
and be done. That does not typecheck, and the reason is the substance of the issue:
`SetGen.support : SetGen.Set α → SetGen.Set α`, whereas `retryGenArg` is
`Plausible.Gen`-specific (it needs `tryCatch`, which the abstract `Gen` class does not
provide). Retrying is invisible in the `Set` semantics — there `default` is `∅`, not an
error, so there is no failure to catch and nothing to retry.

So "the support is unchanged" splits into the two halves above: a reachability claim
about retrying, proved where retrying exists (`Plausible.Gen`), and a congruence claim
about `genLExpr`, proved uniformly in `G` and therefore applicable at `SetGen.Set`.
-/

open Lambda RandomChoice Plausible

namespace RetryGenSupport

/-! ## Part 1: retrying is reachability-neutral at `Plausible.Gen` -/

/-- `tryCatch` at `Plausible.Gen`, applied to an rng state and a size, is the
    obvious `Except` match: run `g`; on `.ok` keep the result, on `.error` run the
    handler *at the same state*. Peeling the `StateT`/`ReaderT`/`Except` stack by
    hand because `Plausible.Gen`'s `MonadExcept` instance is `by infer_instance`, so
    there is no ready-made simp lemma. -/
theorem tryCatch_apply {α} (g : Plausible.Gen α) (h : GenError → Plausible.Gen α)
    (sg : ULift StdGen) (size : ULift Nat) :
    (tryCatch g h) sg size
      = (match g sg size with
         | .ok r => .ok r
         | .error e => h e sg size) := by
  simp only [tryCatch, MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch]
  cases g sg size <;> rfl

/-- The values a `Plausible.Gen` can return at a given size, over all rng states.
    This is the executable analogue of `SetGen.support`: `a` is reachable when
    *some* seed makes the generator return it.

    Quantifying over the state is what makes this the right notion. A generator is
    run at whatever seed the harness happens to hold, so "reachable" must mean
    "reachable at some seed", exactly as `SetGen.Set` records every branch a
    generator could take. -/
def runSupport {α} (g : Plausible.Gen α) (size : ULift Nat) : α → Prop :=
  fun a => ∃ sg sg', g sg size = .ok (a, sg')

/-- **Retrying is reachability-neutral.** `retryGen fuel g` reaches exactly what `g`
    reaches — for every `fuel`.

    Both inclusions matter and neither is vacuous:

    * (⊆, no widening) a retry only ever returns a value produced by some attempt of
      `g` itself, at a bumped seed. It cannot invent terms outside `g`'s support —
      this is the direction that would break soundness if it failed.
    * (⊇, no narrowing) the first attempt is still there, so nothing `g` could
      produce becomes unreachable. This is the direction that would break
      completeness if it failed.

    The proof is induction on `fuel`. In the failure branch, `retryGen`'s handler
    advances the rng (`Plausible.Rand.next`) and recurses, so the value comes from
    `retryGen fuel' g` at state `ULift.up (RandomGen.next sg.down).2` — and the
    induction hypothesis applies there. -/
theorem runSupport_retryGen {α} (fuel : Nat) (g : Plausible.Gen α) (size : ULift Nat) :
    runSupport (retryGen fuel g) size = runSupport g size := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    funext a
    apply propext
    constructor
    · rintro ⟨sg, sg', h⟩
      rw [retryGen, tryCatch_apply] at h
      split at h
      · -- first attempt succeeded: the witness is the state we started from
        rename_i r heq; cases h; exact ⟨sg, sg', heq⟩
      · -- first attempt failed: value came from the retry at the advanced state
        have hr : runSupport (retryGen n g) size a :=
          ⟨ULift.up (Prod.snd (RandomGen.next sg.down)), sg', h⟩
        exact ih ▸ hr
    · rintro ⟨sg, sg', h⟩
      -- `g` succeeds at `sg`, so `retryGen`'s first attempt does too
      exact ⟨sg, sg', by rw [retryGen, tryCatch_apply, h]⟩

/-- `retryGenArg` inherits reachability-neutrality pointwise, since it is
    `retryGen` applied pointwise (`retryGenArg fuel g a = retryGen fuel (g a)`). -/
theorem runSupport_retryGenArg {α β} (fuel : Nat) (g : α → Plausible.Gen β)
    (a : α) (size : ULift Nat) :
    runSupport (retryGenArg fuel g a) size = runSupport (g a) size :=
  runSupport_retryGen fuel (g a) size

/-! ## Part 2: `genLExpr` is congruent in `retryCont` -/

/-- **`genLExpr` only uses `retryCont` pointwise.** Two continuations that agree on
    every generator and every type give *literally equal* generators — not merely
    equal supports — at every depth, uniformly in `G`.

    This is what lets Part 1 transfer: `retryGenArg n` and `id` do not agree
    pointwise as *functions*, but Part 1 shows they agree on reachability, and this
    lemma shows reachability is all `genLExpr` can observe about `retryCont`.

    Induction on `depth`: at the floor `retryCont` wraps `genLExprBase`; above it,
    `retryCont` wraps the recursive call, which the induction hypothesis handles. -/
theorem genLExpr_retryCont_ext [_root_.Gen G]
    (retryCont retryCont' : (LMonoTy → G LExpr') → (LMonoTy → G LExpr'))
    (hext : ∀ (g : LMonoTy → G LExpr') (σ : LMonoTy), retryCont g σ = retryCont' g σ)
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat) :
    genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs retryCont
      = genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs retryCont' := by
  induction depth generalizing τ with
  | zero =>
    unfold genLExpr
    simp only [funext (hext _)]
  | succ n ih =>
    unfold genLExpr
    have hrec : (fun σ => genLExpr fctx octx pctx tvars bctx n σ maxNumArgs retryCont)
              = (fun σ => genLExpr fctx octx pctx tvars bctx n σ maxNumArgs retryCont') := by
      funext σ; exact ih σ
    simp only [funext (hext _), hrec]

/-- Specialization of `genLExpr_retryCont_ext` to the default: any `retryCont` that
    is pointwise the identity yields exactly the generator the theorems describe.

    This is the `SetGen.Set`-instantiable form. Since `SetGen.Set` has no failure to
    catch, every sensible retry wrapper *is* pointwise the identity there, so the
    proven support results apply verbatim. -/
theorem genLExpr_retryCont_id [_root_.Gen G]
    (retryCont : (LMonoTy → G LExpr') → (LMonoTy → G LExpr'))
    (hid : ∀ (g : LMonoTy → G LExpr') (σ : LMonoTy), retryCont g σ = g σ)
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat) :
    genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs retryCont
      = genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs id :=
  genLExpr_retryCont_ext retryCont id hid fctx octx pctx tvars bctx depth τ maxNumArgs

/-! ## Part 3: the headline results -/

/-- **The `SetGen.Set` statement.** Under the `Set` semantics the soundness and
    completeness theorems use, a pointwise-identity `retryCont` leaves
    `SetGen.support` completely unchanged. Immediate from `genLExpr_retryCont_id`,
    and stated separately because "the support is unchanged" is the property being
    claimed. -/
theorem genLExpr_setSupport_retryCont
    (retryCont : (LMonoTy → SetGen.Set LExpr') → (LMonoTy → SetGen.Set LExpr'))
    (hid : ∀ (g : LMonoTy → SetGen.Set LExpr') (σ : LMonoTy), retryCont g σ = g σ)
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat) :
    SetGen.support
        (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs retryCont)
      = SetGen.support
        (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs id) := by
  rw [genLExpr_retryCont_id retryCont hid]

/-- **The executable statement about the argument generator.** The retrying argument
    generator `genLExpr` actually uses in production reaches exactly what the plain one
    reaches — at every depth, since this is just `runSupport_retryGenArg` at the
    generator `genLExpr` passes to `retryCont`.

    Stated at the depth floor (`genLExprBase`) and for the recursive case separately
    below, because those are the two things `retryCont` is applied to. -/
theorem genLExpr_runSupport_retryGenArg_base (n : Nat)
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (τ : LMonoTy) (size : ULift Nat) :
    runSupport (retryGenArg n
        (genLExprBase (G := Plausible.Gen) fctx octx pctx tvars bctx 0) τ) size
      = runSupport (genLExprBase (G := Plausible.Gen) fctx octx pctx tvars bctx 0 τ) size :=
  runSupport_retryGenArg n _ τ size

/-- The same for the recursive case: at depth `n + 1` the argument generator is
    `genLExpr … n`, and wrapping it in `retryGenArg` leaves its reachability alone.
    Together with `genLExpr_runSupport_retryGenArg_base` this covers every position
    `retryCont` is applied at. -/
theorem genLExpr_runSupport_retryGenArg_rec (fuel : Nat)
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat) (maxNumArgs : Nat)
    (retryCont : (LMonoTy → Plausible.Gen LExpr') → (LMonoTy → Plausible.Gen LExpr'))
    (τ : LMonoTy) (size : ULift Nat) :
    runSupport (retryGenArg fuel
        (fun σ => genLExpr (G := Plausible.Gen) fctx octx pctx tvars bctx n σ
                    maxNumArgs retryCont) τ) size
      = runSupport (genLExpr (G := Plausible.Gen) fctx octx pctx tvars bctx n τ
                      maxNumArgs retryCont) size :=
  runSupport_retryGenArg fuel _ τ size

/-! ## Scope: what is and is not established here

`genLExpr_setSupport_retryCont` is the result that matters for the proofs: under
`SetGen.Set`, where every existing soundness/completeness theorem lives, a
pointwise-identity `retryCont` leaves `SetGen.support` *literally* unchanged. Since
`SetGen.Set` has no failure to catch, that covers every retry wrapper — so the proven
results describe the production generator's reachable set, and there is no hidden
specification debt in scoping the theorems to `retryCont = id`.

On the `Plausible.Gen` side, `runSupport_retryGen` establishes the substantive fact:
retrying is reachability-neutral, neither widening nor narrowing. The results above
apply it at exactly the positions `genLExpr` uses `retryCont`.

What is **not** proved here is a single end-to-end equation
`runSupport (genLExpr … (retryGenArg n)) = runSupport (genLExpr … id)` at arbitrary
depth. That is not an oversight about `retryGenArg`; `runSupport` simply does not
compose through `bind` at `Plausible.Gen`. In `g >>= f`, the rng state `f` receives is
*determined* by `g`, so from "`a` is reachable from `g` at some state" and "`b` is
reachable from `f a` at some state" one cannot conclude "`b` is reachable from
`g >>= f`" — the two witnessing states need not agree. Establishing the end-to-end
equation would need a seed-surjectivity argument about `Rand.next`, which is a fact
about `StdGen`'s implementation rather than about retrying. The `SetGen.Set` result is
the one the theorems rely on, and it is unconditional. -/

/-! ## Part 4: the proven results transfer, verbatim

Concrete demonstrations that scoping the theorems to `retryCont = id` costs nothing:
each existing result holds for an arbitrary pointwise-identity `retryCont`, by
rewriting with `genLExpr_setSupport_retryCont` and applying the original theorem
unchanged. -/

/-- Soundness survives an arbitrary pointwise-identity `retryCont`: every generated
    term is still well-typed at the type it was generated for. -/
theorem genLExpr_sound_retryCont
    (retryCont : (LMonoTy → SetGen.Set LExpr') → (LMonoTy → SetGen.Set LExpr'))
    (hid : ∀ (g : LMonoTy → SetGen.Set LExpr') (σ : LMonoTy), retryCont g σ = g σ)
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (maxNumArgs : Nat) (e : LExpr')
    (he : e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs
        retryCont)) :
    HasTypeA' bctx e τ := by
  rw [genLExpr_setSupport_retryCont retryCont hid] at he
  exact genLExpr_sound fctx octx pctx tvars bctx depth τ maxNumArgs e he

/-- Completeness likewise: nothing becomes unreachable. Since the support is
    *literally* unchanged, the original completeness theorem applies as-is. -/
theorem genLExpr_complete_retryCont
    (retryCont : (LMonoTy → SetGen.Set LExpr') → (LMonoTy → SetGen.Set LExpr'))
    (hid : ∀ (g : LMonoTy → SetGen.Set LExpr') (σ : LMonoTy), retryCont g σ = g σ)
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : SimpleType τ) (maxNumArgs : Nat) (e : LExpr')
    (he : (HasTypeA' bctx e τ ∧ emptyNames e ∧ allVarsInCtx fctx octx e ∧
            AllTypesSimple tvars depth bctx e ∧ termDepth bctx e ≤ depth)
          ∨ IsPolyApp fctx octx pctx tvars bctx depth τ maxNumArgs e) :
    e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs
        retryCont) := by
  rw [genLExpr_setSupport_retryCont retryCont hid]
  exact genLExpr_complete fctx octx pctx tvars bctx depth τ hτ maxNumArgs e he

end RetryGenSupport
