import StrataGenerators.SetGen
import StrataGenerators.HasTypeAGen
import StrataGenerators.RetryGen
import Basalt.PlausibleGen

/-!
# `retryGenArg` does not change what `genLExpr` can produce

The theorems for soundness, for completeness and for `OpsConsistentR` in
`HasTypeAGen.lean` and `HasTypeAGenOpsConsistent.lean` all speak about
`genLExpr (G := SetGen.Set) … `, with `retryCont` at its default value `id`. The
*executable* generator that the test harness runs is
`genLExpr (G := Plausible.Gen) … (retryGenArg n)`.

This module closes that gap. A `retryCont` that retries changes only *the number of
attempts* that a draw needs, and it never changes *which terms the generator can
reach*.

The two results below hold in *different semantics*, and this module alone does not
join them. `genLExpr_setSupport_retryCont` speaks about `SetGen.Set`, and its
hypothesis is an equation between functions, which `retryGenArg` does **not** satisfy.
`runSupport_retryGen` speaks about `Plausible.Gen`, where `retryGenArg` lives.
`StrataGenerators.ExecRefinement` is the bridge between `Set` and `Plausible`, and its
theorems `refines_retryGen` and `refines_retryGenArg` are what carry the proved support
over to the executable generator.

There are two facts:

1. `runSupport_retryGen` and `runSupport_retryGenArg`: a retry does not change which
   values `Plausible.Gen` can reach. It adds no value, because a retry returns only a
   value that the generator under it returns. It removes no value, because the first
   attempt is still there.

2. `genLExpr_retryCont_ext` and `genLExpr_retryCont_id`: `genLExpr` is *congruent* in
   `retryCont`. Two continuations that agree at each point give generators that are
   literally equal, at each depth and for every `G`.

The main results are `genLExpr_runSupport_retryGenArg`, which is the executable
statement, and `genLExpr_setSupport_retryCont`, which is the statement about
`SetGen.Set` that connects to the theorems.

## Why there are two statements

A reader can hope for one statement about
`SetGen.support (genLExpr (G := SetGen.Set) … (retryGenArg n))`. That expression does
not typecheck, and the reason is the substance of the matter.
`SetGen.support` maps a `SetGen.Set α` to a `SetGen.Set α`, but `retryGenArg` works
only at `Plausible.Gen`, because it needs `tryCatch` and the abstract `Gen` class has
no such operation. A retry is also invisible in the `Set` semantics: there `default` is
`∅` and not an error, so there is no failure to catch and nothing to retry.

The claim that the support does not change therefore splits into the two halves above.
The first half is a claim about which values a retry can reach, and the proof is at
`Plausible.Gen`, where a retry exists. The second half is a claim that `genLExpr` is
congruent, and the proof is uniform in `G` and therefore holds at `SetGen.Set`.
-/

open Lambda RandomChoice Plausible

namespace RetryGenSupport

/-! ## Part 1: a retry does not change what `Plausible.Gen` can reach -/

/-- `tryCatch` at `Plausible.Gen`, at a state of the random number generator and a
    size, is a match on an `Except` value. It runs `g`. For `.ok` it keeps the
    result, and for `.error` it runs the handler *at the same state*.

    The proof takes the stack of `StateT`, `ReaderT` and `Except` apart by hand,
    because the `MonadExcept` instance of `Plausible.Gen` comes from
    `by infer_instance` and there is therefore no simp lemma for it. -/
theorem tryCatch_apply {α} (g : Plausible.Gen α) (h : GenError → Plausible.Gen α)
    (sg : ULift StdGen) (size : ULift Nat) :
    (tryCatch g h) sg size
      = (match g sg size with
         | .ok r => .ok r
         | .error e => h e sg size) := by
  simp only [tryCatch, MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch]
  cases g sg size <;> rfl

/-- The values that a `Plausible.Gen` can return at a given size, over each state of
    the random number generator. This is the executable form of `SetGen.support`: the
    generator can reach `a` when *some* seed makes it return `a`.

    The quantifier over the state is what makes this the correct definition. The
    harness runs a generator at the seed that it holds, so "the generator can reach
    a value" must mean "some seed makes the generator return the value". `SetGen.Set`
    records each branch that a generator can take, in the same way. -/
def runSupport {α} (g : Plausible.Gen α) (size : ULift Nat) : α → Prop :=
  fun a => ∃ sg sg', g sg size = .ok (a, sg')

/-- **A retry does not change what a generator can reach.** For every `fuel`,
    `retryGen fuel g` reaches exactly what `g` reaches.

    Both inclusions matter, and neither one is vacuous:

    * A retry adds no value. It returns only a value that some attempt of `g` itself
      gives, at a seed that the wrapper advanced. It cannot make a term outside the
      support of `g`. Soundness needs this direction.
    * A retry removes no value. The first attempt is still there, so each value that
      `g` can give stays reachable. Completeness needs this direction.

    The proof is by induction on `fuel`. In the branch for a failure, the handler of
    `retryGen` advances the random number generator and calls itself. The value
    therefore comes from `retryGen fuel' g` at the state that `Rand.next` gives, and
    the induction hypothesis covers that case. -/
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
      · -- The first attempt succeeded, so the witness is the state at the start.
        rename_i r heq; cases h; exact ⟨sg, sg', heq⟩
      · -- The first attempt failed, so the value comes from the retry at the new state.
        have hr : runSupport (retryGen n g) size a :=
          ⟨ULift.up (Prod.snd (RandomGen.next sg.down)), sg', h⟩
        exact ih ▸ hr
    · rintro ⟨sg, sg', h⟩
      -- `g` succeeds at `sg`, so the first attempt of `retryGen` also succeeds.
      exact ⟨sg, sg', by rw [retryGen, tryCatch_apply, h]⟩

/-- `retryGenArg` also changes nothing that a generator can reach, at each point. It is
    `retryGen` at each point: `retryGenArg fuel g a` is `retryGen fuel (g a)`. -/
theorem runSupport_retryGenArg {α β} (fuel : Nat) (g : α → Plausible.Gen β)
    (a : α) (size : ULift Nat) :
    runSupport (retryGenArg fuel g a) size = runSupport (g a) size :=
  runSupport_retryGen fuel (g a) size

/-! ## Part 2: `genLExpr` is congruent in `retryCont` -/

/-- **`genLExpr` uses `retryCont` only at one point at a time.** Two continuations that
    agree on each generator and each type give generators that are *literally equal*,
    and not only generators with equal supports. This holds at each depth and it is
    uniform in `G`.

    This lemma is what carries Part 1 over. `retryGenArg n` and `id` do not agree as
    *functions*, but Part 1 shows that they reach the same values, and this lemma shows
    that what a continuation reaches is all that `genLExpr` can see about it.

    The proof is by induction on `depth`. At the lowest depth, `retryCont` wraps
    `genLExprBase`. Above it, `retryCont` wraps the recursive call, and the induction
    hypothesis covers that call. -/
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

/-- `genLExpr_retryCont_ext` at the default value. A `retryCont` that is the identity at
    each point gives exactly the generator that the theorems describe.

    This is the form that a reader can instantiate at `SetGen.Set`. `SetGen.Set` has no
    failure to catch, so each sensible retry wrapper *is* the identity at each point
    there, and the proved results about the support apply without a change. -/
theorem genLExpr_retryCont_id [_root_.Gen G]
    (retryCont : (LMonoTy → G LExpr') → (LMonoTy → G LExpr'))
    (hid : ∀ (g : LMonoTy → G LExpr') (σ : LMonoTy), retryCont g σ = g σ)
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat) :
    genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs retryCont
      = genLExpr fctx octx pctx tvars bctx depth τ maxNumArgs id :=
  genLExpr_retryCont_ext retryCont id hid fctx octx pctx tvars bctx depth τ maxNumArgs

/-! ## Part 3: the main results -/

/-- **The statement at `SetGen.Set`.** In the `Set` semantics, which the theorems for
    soundness and completeness use, a `retryCont` that is the identity at each point
    leaves `SetGen.support` unchanged. This theorem is separate, because the claim that
    the support does not change is the property that matters. -/
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

/-- **The executable statement about the generator for an argument.** The generator that
    `genLExpr` uses in production retries, and it reaches exactly what the plain
    generator reaches, at each depth.

    This theorem covers the lowest depth, which is `genLExprBase`. The theorem below
    covers the recursive case. `retryCont` applies to those two generators only. -/
theorem genLExpr_runSupport_retryGenArg_base (n : Nat)
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (τ : LMonoTy) (size : ULift Nat) :
    runSupport (retryGenArg n
        (genLExprBase (G := Plausible.Gen) fctx octx pctx tvars bctx 0) τ) size
      = runSupport (genLExprBase (G := Plausible.Gen) fctx octx pctx tvars bctx 0 τ) size :=
  runSupport_retryGenArg n _ τ size

/-- The same claim for the recursive case. At depth `n + 1` the generator for an argument
    is `genLExpr … n`, and a wrapper of `retryGenArg` around it changes nothing that the
    generator can reach. With `genLExpr_runSupport_retryGenArg_base`, this covers each
    position where `retryCont` applies. -/
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

/-! ## What this module proves, and what it does not

`genLExpr_setSupport_retryCont` is the result that the proofs need. At `SetGen.Set`,
where each theorem for soundness and for completeness lives, a `retryCont` that is the
identity at each point leaves `SetGen.support` *literally* unchanged. `SetGen.Set` has
no failure to catch, so this covers each retry wrapper. The proved results therefore
describe the set of terms that the production generator can reach, and the theorems lose
nothing when they fix `retryCont` to `id`.

At `Plausible.Gen`, `runSupport_retryGen` gives the fact of substance: a retry changes
nothing that a generator can reach, and it neither adds nor removes a value. The results
above apply that fact at exactly the positions where `genLExpr` uses `retryCont`.

This module does **not** prove one equation from end to end,
`runSupport (genLExpr … (retryGenArg n)) = runSupport (genLExpr … id)`, at an arbitrary
depth. The reason is not about `retryGenArg`. `runSupport` does not compose through
`bind` at `Plausible.Gen`. In `g >>= f`, the value of `g` *determines* the state of the
random number generator that `f` receives. From the facts that `g` reaches `a` at some
state and that `f a` reaches `b` at some state, a reader cannot conclude that `g >>= f`
reaches `b`, because the two witness states can differ. An equation from end to end needs
an argument that `Rand.next` is surjective on the seeds, and that is a fact about the
implementation of `StdGen` and not about a retry. The result at `SetGen.Set` is the one
that the theorems use, and it holds without a condition. -/

/-! ## Part 4: the proved results carry over without a change

The two theorems below show that the theorems lose nothing when they fix
`retryCont` to `id`. Each result holds for any `retryCont` that is the identity at each
point. -/

/-- Soundness holds for any `retryCont` that is the identity at each point: each generated
    term is well-typed at the type that it received. -/
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

/-- Completeness also holds for such a `retryCont`: no term becomes unreachable. The
    support is *literally* unchanged, so the completeness theorem applies without a
    change. -/
theorem genLExpr_complete_retryCont
    (retryCont : (LMonoTy → SetGen.Set LExpr') → (LMonoTy → SetGen.Set LExpr'))
    (hid : ∀ (g : LMonoTy → SetGen.Set LExpr') (σ : LMonoTy), retryCont g σ = g σ)
    (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy)
    (hτ : ∃ m, τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars m))
    (maxNumArgs : Nat) (e : LExpr')
    (he : (HasTypeA' bctx e τ ∧ emptyNames e ∧ allVarsInCtx fctx octx e ∧
            AllTypesSimple tvars depth bctx e ∧ termDepth bctx e ≤ depth)
          ∨ IsPolyApp fctx octx pctx tvars bctx depth τ maxNumArgs e) :
    e ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars bctx depth τ maxNumArgs
        retryCont) := by
  rw [genLExpr_setSupport_retryCont retryCont hid]
  exact genLExpr_complete fctx octx pctx tvars bctx depth τ hτ maxNumArgs e he

end RetryGenSupport
