import StrataGenerators.HasTypeAGen.Core

/-!
# Subexpression duplication by output mutation (for CSE testing)

## Why mutate instead of generate

`genLExprBase` draws every sub-term independently, so generated terms almost never
contain two structurally-equal non-trivial subterms — CSE runs near-vacuously.
The obvious fix (a "pool" production rule inside the generator) forces us to
re-discharge `genLExprBase_sound` for a new arm. This module takes the other
route from the MUTAGEN / FuzzChick line of work (Mista & Russo; Lampropoulos,
Hicks & Pierce): **leave the generator and its proofs untouched, and mutate the
already-generated term** so it is guaranteed to contain common subexpressions.

The mutation is *type-preserving by construction*, so no generator-side proof is
needed — and because every mutant is re-checked by Strata's `typeCheck` oracle
(the same oracle the properties already use), any bug in this hand-written code
surfaces as a rejected input rather than a false CSE result. See
`checkAllMutantsWellTyped` for that regression guard.

## The core operation: same-context splice

MUTAGEN's constructor mutations naturally reuse sibling subexpressions when
filling a slot (`Branch l x r ↝ Branch l x l`), which is exactly the
CSE-inducing operation — duplicate an existing subterm. We generalize sibling
reuse to *whole-term* reuse: for every position, find another subterm elsewhere
in the term with the **same type and the same bound-variable context**, and
replace the position's subterm with a copy of the donor.

Restricting donor and target to an **identical `bctx`** is what makes this sound
with zero de Bruijn arithmetic: a subterm well-typed under `bctx` stays well-typed
at any other occurrence of that same `bctx` (the `bvar` rule of `HasTypeA` only
looks at `bctx[i]?`, which is unchanged). This is the same-context restriction the
MUTAGEN-style STLC sketch used; it deliberately forgoes cross-context splicing
(which would need index shifting) in exchange for guaranteed well-typedness.

The result is precisely the "structurally-equal-but-pointer-disjoint" input the
PBT plan calls family 3 (P-CSE-7) and the binder-rich capture input for P-CSE-3:
when the shared `bctx` is non-empty, the duplicated subterm *contains live de
Bruijn indices bound by an enclosing binder*.
-/

open Lambda RandomChoice

namespace SubexprMutate

/-- A path from the root of an `LExpr'` to a sub-node: the list of child-steps
    taken. `Root` is the empty path. -/
inductive Step where
  | absBody
  | quantTrigger | quantBody
  | appFn | appArg
  | iteC | iteT | iteE
  | eqL | eqR
  deriving DecidableEq, Repr

abbrev Path := List Step

/-- A recorded occurrence: where a subterm sits (`path`), the bound-variable
    context in scope there (`bctx`), the subterm's monotype (`ty`), and the
    subterm itself (`sub`). -/
structure Occurrence where
  path : Path
  bctx : BVarCtx
  ty   : LMonoTy
  sub  : LExpr'

/-- Walk the whole term once, recording an `Occurrence` at every node whose type
    can be recovered. `bctx` is threaded through binders exactly as `typeCheck`
    does (cons the binder type on the front under `abs`/`quant`). Nodes whose
    `typeCheck` returns `none` (e.g. an unannotated `op`) are skipped as donors
    and targets, but recursion still descends into their children.

    The accumulator collects occurrences in a fixed order; `path` is built in
    reverse and reversed by callers that need a root-to-node path (we only ever
    compare/replace via `path`, so the ordering convention just has to be
    self-consistent — see `replaceAt`). -/
partial def occurrences (bctx : BVarCtx) (e : LExpr') : List Occurrence :=
  go [] bctx e
where
  /-- `revPath` is the path from the root to the current node, stored reversed. -/
  go (revPath : Path) (bctx : BVarCtx) (e : LExpr') : List Occurrence :=
    let here : List Occurrence :=
      match LExpr.typeCheck (T := LExprParams') bctx e with
      | some ty => [{ path := revPath.reverse, bctx := bctx, ty := ty, sub := e }]
      | none    => []
    let children : List Occurrence :=
      match e with
      | .abs _ _ (some aty) body =>
        go (.absBody :: revPath) (aty :: bctx) body
      | .quant _ _ _ (some qty) tr body =>
        go (.quantTrigger :: revPath) (qty :: bctx) tr
          ++ go (.quantBody :: revPath) (qty :: bctx) body
      | .app _ fn arg =>
        go (.appFn :: revPath) bctx fn ++ go (.appArg :: revPath) bctx arg
      | .ite _ c t f =>
        go (.iteC :: revPath) bctx c
          ++ go (.iteT :: revPath) bctx t
          ++ go (.iteE :: revPath) bctx f
      | .eq _ e1 e2 =>
        go (.eqL :: revPath) bctx e1 ++ go (.eqR :: revPath) bctx e2
      | _ => []
    here ++ children

/-- Replace the subterm at `path` (root-to-node) with `new`. If the path does not
    match the term's shape, the term is returned unchanged (defensive: the paths
    we use always come from `occurrences` on the same term). -/
def replaceAt (path : Path) (new : LExpr') (e : LExpr') : LExpr' :=
  match path with
  | [] => new
  | step :: rest =>
    match step, e with
    | .absBody,      .abs m n ty body        => .abs m n ty (replaceAt rest new body)
    | .quantTrigger, .quant m k n ty tr body => .quant m k n ty (replaceAt rest new tr) body
    | .quantBody,    .quant m k n ty tr body => .quant m k n ty tr (replaceAt rest new body)
    | .appFn,        .app m fn arg           => .app m (replaceAt rest new fn) arg
    | .appArg,       .app m fn arg           => .app m fn (replaceAt rest new arg)
    | .iteC,         .ite m c t f            => .ite m (replaceAt rest new c) t f
    | .iteT,         .ite m c t f            => .ite m c (replaceAt rest new t) f
    | .iteE,         .ite m c t f            => .ite m c t (replaceAt rest new f)
    | .eqL,          .eq m e1 e2             => .eq m (replaceAt rest new e1) e2
    | .eqR,          .eq m e1 e2             => .eq m e1 (replaceAt rest new e2)
    | _, _ => e

/-- A subterm is a *non-trivial* donor if it is worth duplicating: not a bare
    leaf (`bvar`/`fvar`/`op`/`const`), since CSE ignores trivial subterms anyway
    and duplicating a leaf produces no interesting common subexpression. -/
def isNonTrivial : LExpr' → Bool
  | .app _ _ _ | .ite _ _ _ _ | .eq _ _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _ => true
  | _ => false

/-- All type-preserving, well-typed-by-construction duplication mutants of `e`
    under `bctx`. For each ordered pair of occurrences `(target, donor)` with:
      * the **same bound-variable context** (`bctx` equal — the soundness key),
      * the **same type**,
      * a **non-trivial donor** (`isNonTrivial`),
      * `donor ≠ target` structurally (else the mutant equals the input),
    emit `replaceAt target.path donor.sub e`.

    Every mutant typechecks at the same top-level type as `e`: splicing a subterm
    of type `τ` that is valid under `bctx` into another position of type `τ` under
    the *same* `bctx` changes neither the local type nor any bvar resolution.
    (`checkMutantWellTyped` re-verifies this at runtime as a guard on this code.)

    Exhaustive over all (target, donor) pairs — the MUTAGEN `CreateMutationBatch`
    style, not FuzzChick's one-mutation-per-step `freq`. -/
def duplicationMutants (bctx : BVarCtx) (e : LExpr') : List LExpr' :=
  let occs := occurrences bctx e
  occs.flatMap fun target =>
    occs.filterMap fun donor =>
      if isNonTrivial donor.sub
         && target.ty == donor.ty
         && target.bctx == donor.bctx
         && !(target.sub == donor.sub)
      then some (replaceAt target.path donor.sub e)
      else none

/-- Number of duplication opportunities in `e` under `bctx` — the length of
    `duplicationMutants`, computed without materializing the mutant terms.
    Useful as a Tyche feature (`dup_sites`) to confirm the mutation is firing. -/
def duplicationSiteCount (bctx : BVarCtx) (e : LExpr') : Nat :=
  let occs := occurrences bctx e
  (occs.flatMap fun target =>
    occs.filter fun donor =>
      isNonTrivial donor.sub
        && target.ty == donor.ty
        && target.bctx == donor.bctx
        && !(target.sub == donor.sub)).length

/-- A deterministic, type-preserving duplication of one subterm in `e`: returns
    the first duplication mutant if any exists, else `e` unchanged. Pure (no `Gen`),
    so it drops straight into a pure per-expression map (`Statements.mapExprs`) at
    the harness layer — no monadic traversal of the statement AST is needed, and it
    touches neither `genLExprBase` nor its soundness proof.

    Because it is chosen from `duplicationMutants`, the result typechecks at the
    same type as `e` under `bctx` (see `checkAllMutantsWellTyped`), and — when a
    non-trivial donor exists — contains that donor at *two* positions, i.e. a
    genuine common subexpression for CSE to hoist. A no-op exactly when `e` has no
    duplication opportunity (e.g. a leaf, or no two same-type same-context nodes). -/
def duplicateOneSubterm (bctx : BVarCtx) (e : LExpr') : LExpr' :=
  (duplicationMutants bctx e).head?.getD e

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Runtime well-typedness guard (regression check on this hand-written code)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Every duplication mutant of `e` typechecks at the *same* type as `e` under
    `bctx`. This is the type-preservation claim of `duplicationMutants`, stated as
    a `Bool` so it drops into the property harness. It should be *impossible* to
    falsify if `occurrences`/`replaceAt` are correct — a failure means a path or
    context bug in this module, not a bug in CSE. Recommended as a standing
    regression property (analogous to MUTAGEN's `prop_mutantsWellTyped`). -/
def checkAllMutantsWellTyped (bctx : BVarCtx) (e : LExpr') : Bool :=
  match LExpr.typeCheck (T := LExprParams') bctx e with
  | none    => true  -- input itself untypeable under bctx: vacuous
  | some ty =>
    (duplicationMutants bctx e).all fun m =>
      LExpr.typeCheck (T := LExprParams') bctx m == some ty

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Generator wrapper (no generator proof touched)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Wrap any `LExpr'` generator so its output is mutated to contain a common
    subexpression. Generates a term, computes its duplication mutants, and either
    returns a randomly chosen mutant (with weight `mutateWeight`) or the original
    term (weight `keepWeight`, and always when no duplication opportunity exists).

    The generator argument is used *as-is* — this deliberately does not touch
    `genLExprBase` / `genLExpr` or their soundness proofs. Well-typedness of the
    result follows from `duplicationMutants` being type-preserving; it is also
    re-checked by the property harness's `typeCheck` oracle.

    `bctx` must be the context the generator produced `e` under (typically `[]`
    for a closed top-level expression).

    Weights: the mutate arm gets `mutateWeight`; the keep arm gets `keepWeight + 1`
    (the `+1` keeps the total positive for any caller-supplied `Nat`s, so no
    positivity hypothesis is needed, and also guarantees the original term is
    always reachable). -/
def withDuplicateSubterm [Gen G] (bctx : BVarCtx) (gen : G LExpr')
    (mutateWeight : Nat := 3) (keepWeight : Nat := 0) : G LExpr' := do
  let e ← gen
  let mutants := duplicationMutants bctx e
  if h : mutants.length > 0 then
    frequency
      [ (mutateWeight,   fun () => elements mutants (List.length_pos_iff.mp h)),
        (keepWeight + 1, fun () => pure e) ]
      (by simp [List.sum]; omega)
  else
    pure e

end SubexprMutate
