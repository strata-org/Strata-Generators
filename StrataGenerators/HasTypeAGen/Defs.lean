import Basalt.Gen
import Basalt.IO
import Strata.DL.Lambda.Denote.LExprAnnotated

open Lambda RandomChoice

/-!
# Generator definitions for well-typed `LExpr`s (lightweight, no Mathlib)

This file contains just the generator *definitions* from `HasTypeAGen` without
any correctness proofs or Mathlib-dependent imports. It can be imported alongside
`Strata.DL.Lambda.LExprEval` without triggering the `List.Forall₂` collision.

The full `HasTypeAGen` module re-exports everything here plus soundness/completeness proofs.
-/

namespace ArbNat

/-- Generate an arbitrary natural number with geometrically decreasing
    probability: 0 with probability 1/2, 1 with 1/4, etc. -/
def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

end ArbNat

open ArbNat

-- ── Parameter types ──────────────────────────────────────────────────

/-- The base `LExprParams` we use: unit metadata and unit identifier-metadata. -/
abbrev LExprParams' : LExprParams := ⟨Unit, Unit⟩
/-- The full `LExprParamsT` (with `LMonoTy` as the type annotation type). -/
abbrev LExprParamsT' : LExprParamsT := LExprParams.mono LExprParams'

instance : DecidableEq Unit := instDecidableEqPUnit

/-- Our working expression type: `LExpr` with unit metadata and monotype annotations. -/
abbrev LExpr' := LExpr LExprParamsT'

instance : BEq LMonoTy := instBEqOfDecidableEq

-- ── Contexts ─────────────────────────────────────────────────────────

/-- Bound-variable context: `bctx[i]?` is the type of de Bruijn index `i`. -/
abbrev BVarCtx := List LMonoTy
/-- Free-variable context: maps variable names to their types (locally nameless). -/
abbrev FVarCtx := List (String × LMonoTy)
/-- Operator context: maps operator names to their types. -/
abbrev OpCtx := List (String × LMonoTy)

-- ── SimpleType and depth ─────────────────────────────────────────────

/-- A monotype is *simple* if it is built from `bool`, `int`, `arrow`, and `ftvar`.
    This characterizes exactly the types produced by `genLMonoTy`. -/
inductive SimpleType : LMonoTy → Prop where
  | bool  : SimpleType .bool
  | int   : SimpleType .int
  | arrow : SimpleType τ₁ → SimpleType τ₂ → SimpleType (.arrow τ₁ τ₂)
  | ftvar : SimpleType (.ftvar name)

/-- The nesting depth of a monotype: 0 for base types, `max(depth τ₁, depth τ₂) + 1`
    for arrows. Matches the fuel consumed by `genLMonoTy` to produce the type. -/
def monoTyDepth : LMonoTy → Nat
  | .arrow τ₁ τ₂ => max (monoTyDepth τ₁) (monoTyDepth τ₂) + 1
  | _             => 0

-- ── Well-typing relation ─────────────────────────────────────────────

/-- Strata's `HasTypeA` typing judgement instantiated at our parameter types. -/
abbrev HasTypeA' := LExpr.HasTypeA (T := LExprParams')

-- ── Helpers ──────────────────────────────────────────────────────────

/-- All de Bruijn indices in `bctx` whose type equals `τ`. -/
def bvarsOfType (bctx : BVarCtx) (τ : LMonoTy) : List Nat :=
  go bctx 0
where
  go : List LMonoTy → Nat → List Nat
    | [],         _  => []
    | τ' :: rest, i  => if τ' == τ then i :: go rest (i + 1) else go rest (i + 1)

/-- Pick a uniformly random bound variable of type `τ` from `bctx`. -/
def pickBVar [Gen G] (bctx : BVarCtx) (τ : LMonoTy)
    (_h : (bvarsOfType bctx τ).length > 0) : G LExpr' := do
  let indices := bvarsOfType bctx τ
  let idx ← choose 0 (indices.length - 1) (by omega)
  pure (.bvar () (indices.getD idx.down 0))

/-- All variable names in `fctx` whose type equals `τ`. -/
def fvarsOfType (fctx : FVarCtx) (τ : LMonoTy) : List String :=
  fctx.filterMap (fun (x, ty) => if ty == τ then some x else none)

/-- Pick a uniformly random free variable of type `τ` from `fctx`. The generated
    `fvar` node carries a type annotation `(some τ)` so that `HasTypeA` can
    typecheck it without an external environment. -/
def pickFVar [Gen G] (fctx : FVarCtx) (τ : LMonoTy)
    (_h : (fvarsOfType fctx τ).length > 0) : G LExpr' := do
  let names := fvarsOfType fctx τ
  let idx ← choose 0 (names.length - 1) (by omega)
  pure (.fvar () ⟨names.getD idx.down "", ()⟩ (some τ))

/-- All operator names in `octx` whose type equals `τ`. -/
def opsOfType (octx : OpCtx) (τ : LMonoTy) : List String :=
  octx.filterMap (fun (x, ty) => if ty == τ then some x else none)

/-- Pick a uniformly random operator of type `τ` from `octx`. -/
def pickOp [Gen G] (octx : OpCtx) (τ : LMonoTy)
    (_h : (opsOfType octx τ).length > 0) : G LExpr' := do
  let names := opsOfType octx τ
  let idx ← choose 0 (names.length - 1) (by omega)
  pure (.op () ⟨names.getD idx.down "", ()⟩ (some τ))

-- ── Type generator ───────────────────────────────────────────────────

/-- Pick a uniformly random type variable name from `tvars` and return it
    as an `LMonoTy.ftvar`. -/
def pickTyVar [Gen G] (tvars : List TyIdentifier)
    (_h : tvars.length > 0) : G LMonoTy := do
  let idx ← choose 0 (tvars.length - 1) (by omega)
  pure (.ftvar (tvars.getD idx.down ""))

/-- Generate a simple monotype of depth ≤ `n`. When `tvars` is non-empty,
    type variables (`ftvar`) may appear at leaves alongside `bool` and `int`.
    Arrow types are only generated at depth `n + 1` with sub-types at depth `n`. -/
def genLMonoTy [Gen G] (tvars : List TyIdentifier) : Nat → G LMonoTy
  | 0 =>
    if h : tvars.length > 0 then
      pick (fun () => pure .bool)
           (fun () => pick (fun () => pure .int)
                           (fun () => pickTyVar tvars h))
    else
      pick (fun () => pure .bool)
           (fun () => pure .int)
  | n + 1 =>
    if h : tvars.length > 0 then
      pick
        (fun () => pure .bool)
        (fun () =>
          pick
            (fun () => pure .int)
            (fun () =>
              pick
                (fun () => do
                  let τ₁ ← genLMonoTy tvars n
                  let τ₂ ← genLMonoTy tvars n
                  pure (.arrow τ₁ τ₂))
                (fun () => pickTyVar tvars h)))
    else
      pick
        (fun () => pure .bool)
        (fun () =>
          pick
            (fun () => pure .int)
            (fun () => do
              let τ₁ ← genLMonoTy tvars n
              let τ₂ ← genLMonoTy tvars n
              pure (.arrow τ₁ τ₂)))

-- ── Expression generator ─────────────────────────────────────────────

/-- Generate a well-typed `LExpr` of type `τ` with term depth bounded by the
    first `Nat` argument. At depth 0, only leaf expressions (bvar, fvar, op,
    constants) are produced; at depth `n+1`, compound expressions may be
    produced with sub-expressions at depth `n`.

    The generated term satisfies `HasTypeA' bctx e τ` (see `genLExpr_sound`). -/
def genLExpr [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) : Nat → LMonoTy → G LExpr'
  -- Depth 0 + arrow: only leaf expressions allowed; `default` on failure.
  -- This ensures `termDepth e ≤ 0` for all outputs (Option C).
  | 0, .arrow τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.arrow τ₁ τ₂)
    pick
      (fun () =>
        if hv : bvars.length > 0 then pickBVar bctx _ hv
        else default)
      (fun () =>
        pick
          (fun () =>
            if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0
            then pickFVar fctx _ hf
            else default)
          (fun () =>
            if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0
            then pickOp octx _ ho
            else default))
  | n + 1, .arrow τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.arrow τ₁ τ₂)
    pick
      (fun () => do
        let body ← genLExpr fctx octx tvars (τ₁ :: bctx) n τ₂
        pure (.abs () "" (some τ₁) body))
      (fun () =>
        pick
          (fun () => do
            let τ' ← genLMonoTy tvars n
            let arg ← genLExpr fctx octx tvars bctx n τ'
            let fn  ← genLExpr fctx octx tvars bctx n (.arrow τ' (.arrow τ₁ τ₂))
            pure (.app () fn arg))
          (fun () =>
            pick
              (fun () => do
                let c ← genLExpr fctx octx tvars bctx n .bool
                let t ← genLExpr fctx octx tvars bctx n (.arrow τ₁ τ₂)
                let e ← genLExpr fctx octx tvars bctx n (.arrow τ₁ τ₂)
                pure (.ite () c t e))
              (fun () =>
                pick
                  (fun () =>
                    if hv : bvars.length > 0 then pickBVar bctx _ hv
                    else do
                      let body ← genLExpr fctx octx tvars (τ₁ :: bctx) n τ₂
                      pure (.abs () "" (some τ₁) body))
                  (fun () =>
                    pick
                      (fun () =>
                        if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0
                        then pickFVar fctx _ hf
                        else do
                          let body ← genLExpr fctx octx tvars (τ₁ :: bctx) n τ₂
                          pure (.abs () "" (some τ₁) body))
                      (fun () =>
                        if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0
                        then pickOp octx _ ho
                        else do
                          let body ← genLExpr fctx octx tvars (τ₁ :: bctx) n τ₂
                          pure (.abs () "" (some τ₁) body))))))
  | 0, .bool =>
    let bvars := bvarsOfType bctx .bool
    pick
      (fun () =>
        pick (fun () => pure (.boolConst () true))
             (fun () => pure (.boolConst () false)))
      (fun () =>
        pick
          (fun () =>
            if hv : bvars.length > 0 then pickBVar bctx .bool hv
            else pick (fun () => pure (.boolConst () true))
                      (fun () => pure (.boolConst () false)))
          (fun () =>
            pick
              (fun () =>
                if hf : (fvarsOfType fctx .bool).length > 0
                then pickFVar fctx .bool hf
                else pick (fun () => pure (.boolConst () true))
                          (fun () => pure (.boolConst () false)))
              (fun () =>
                if ho : (opsOfType octx .bool).length > 0
                then pickOp octx .bool ho
                else pick (fun () => pure (.boolConst () true))
                          (fun () => pure (.boolConst () false)))))
  | n + 1, .bool =>
    let bvars := bvarsOfType bctx .bool
    pick
      (fun () =>
        pick (fun () => pure (.boolConst () true))
             (fun () => pure (.boolConst () false)))
      (fun () =>
        pick
          (fun () => do
            let c ← genLExpr fctx octx tvars bctx n .bool
            let t ← genLExpr fctx octx tvars bctx n .bool
            let e ← genLExpr fctx octx tvars bctx n .bool
            pure (.ite () c t e))
          (fun () =>
            pick
              (fun () => do
                let τ' ← genLMonoTy tvars n
                let e₁ ← genLExpr fctx octx tvars bctx n τ'
                let e₂ ← genLExpr fctx octx tvars bctx n τ'
                pure (.eq () e₁ e₂))
              (fun () =>
                pick
                  (fun () => do
                    let τ' ← genLMonoTy tvars n
                    let arg ← genLExpr fctx octx tvars bctx n τ'
                    let fn  ← genLExpr fctx octx tvars bctx n (.arrow τ' .bool)
                    pure (.app () fn arg))
                  (fun () =>
                    pick
                      (fun () => do
                        let τ' ← genLMonoTy tvars n
                        let τ_tr ← genLMonoTy tvars n
                        let tr ← genLExpr fctx octx tvars (τ' :: bctx) n τ_tr
                        let body ← genLExpr fctx octx tvars (τ' :: bctx) n .bool
                        pure (.quant () .all "" (some τ') tr body))
                      (fun () =>
                        pick
                          (fun () => do
                            let τ' ← genLMonoTy tvars n
                            let τ_tr ← genLMonoTy tvars n
                            let tr ← genLExpr fctx octx tvars (τ' :: bctx) n τ_tr
                            let body ← genLExpr fctx octx tvars (τ' :: bctx) n .bool
                            pure (.quant () .exist "" (some τ') tr body))
                          (fun () =>
                            pick
                              (fun () =>
                                if hv : bvars.length > 0 then pickBVar bctx .bool hv
                                else pick (fun () => pure (.boolConst () true))
                                          (fun () => pure (.boolConst () false)))
                              (fun () =>
                                pick
                                  (fun () =>
                                    if hf : (fvarsOfType fctx .bool).length > 0
                                    then pickFVar fctx .bool hf
                                    else pick (fun () => pure (.boolConst () true))
                                              (fun () => pure (.boolConst () false)))
                                  (fun () =>
                                    if ho : (opsOfType octx .bool).length > 0
                                    then pickOp octx .bool ho
                                    else pick (fun () => pure (.boolConst () true))
                                              (fun () => pure (.boolConst () false))))))))))
  | 0, .int =>
    let bvars := bvarsOfType bctx .int
    pick
      (fun () =>
        pick
          (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
          (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int)))))
      (fun () =>
        pick
          (fun () =>
            if hv : bvars.length > 0 then pickBVar bctx .int hv
            else pick
              (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
              (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int)))))
          (fun () =>
            pick
              (fun () =>
                if hf : (fvarsOfType fctx .int).length > 0
                then pickFVar fctx .int hf
                else pick
                  (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
                  (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int)))))
              (fun () =>
                if ho : (opsOfType octx .int).length > 0
                then pickOp octx .int ho
                else pick
                  (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
                  (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int)))))))
  | n + 1, .int =>
    let bvars := bvarsOfType bctx .int
    pick
      (fun () =>
        pick
          (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
          (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int)))))
      (fun () =>
        pick
          (fun () => do
            let τ' ← genLMonoTy tvars n
            let arg ← genLExpr fctx octx tvars bctx n τ'
            let fn  ← genLExpr fctx octx tvars bctx n (.arrow τ' .int)
            pure (.app () fn arg))
          (fun () =>
            pick
              (fun () => do
                let c ← genLExpr fctx octx tvars bctx n .bool
                let t ← genLExpr fctx octx tvars bctx n .int
                let e ← genLExpr fctx octx tvars bctx n .int
                pure (.ite () c t e))
              (fun () =>
                pick
                  (fun () =>
                    if hv : bvars.length > 0 then pickBVar bctx _ hv
                    else pick
                      (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
                      (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int)))))
                  (fun () =>
                    pick
                      (fun () =>
                        if hf : (fvarsOfType fctx .int).length > 0
                        then pickFVar fctx .int hf
                        else pick
                          (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
                          (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int)))))
                      (fun () =>
                        if ho : (opsOfType octx .int).length > 0
                        then pickOp octx .int ho
                        else pick
                          (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
                          (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int)))))))))
  | 0, .ftvar name =>
    let bvars := bvarsOfType bctx (.ftvar name)
    pick
      (fun () =>
        if hv : bvars.length > 0 then pickBVar bctx _ hv
        else if hf : (fvarsOfType fctx (.ftvar name)).length > 0
        then pickFVar fctx _ hf
        else if ho : (opsOfType octx (.ftvar name)).length > 0
        then pickOp octx _ ho
        else default)
      (fun () =>
        pick
          (fun () =>
            if hf : (fvarsOfType fctx (.ftvar name)).length > 0
            then pickFVar fctx _ hf
            else if hv : bvars.length > 0 then pickBVar bctx _ hv
            else if ho : (opsOfType octx (.ftvar name)).length > 0
            then pickOp octx _ ho
            else default)
          (fun () =>
            if ho : (opsOfType octx (.ftvar name)).length > 0
            then pickOp octx _ ho
            else if hv : bvars.length > 0 then pickBVar bctx _ hv
            else if hf : (fvarsOfType fctx (.ftvar name)).length > 0
            then pickFVar fctx _ hf
            else default))
  | n + 1, .ftvar name =>
    let bvars := bvarsOfType bctx (.ftvar name)
    pick
      (fun () => do
        let τ' ← genLMonoTy tvars n
        let arg ← genLExpr fctx octx tvars bctx n τ'
        let fn  ← genLExpr fctx octx tvars bctx n (.arrow τ' (.ftvar name))
        pure (.app () fn arg))
      (fun () =>
        pick
          (fun () => do
            let c ← genLExpr fctx octx tvars bctx n .bool
            let t ← genLExpr fctx octx tvars bctx n (.ftvar name)
            let e ← genLExpr fctx octx tvars bctx n (.ftvar name)
            pure (.ite () c t e))
          (fun () =>
            pick
              (fun () =>
                if hv : bvars.length > 0 then pickBVar bctx _ hv
                else if hf : (fvarsOfType fctx (.ftvar name)).length > 0
                then pickFVar fctx _ hf
                else if ho : (opsOfType octx (.ftvar name)).length > 0
                then pickOp octx _ ho
                else default)
              (fun () =>
                pick
                  (fun () =>
                    if hf : (fvarsOfType fctx (.ftvar name)).length > 0
                    then pickFVar fctx _ hf
                    else if hv : bvars.length > 0 then pickBVar bctx _ hv
                    else default)
                  (fun () =>
                    if ho : (opsOfType octx (.ftvar name)).length > 0
                    then pickOp octx _ ho
                    else if hv : bvars.length > 0 then pickBVar bctx _ hv
                    else default))))
  | _, _ => pure (.boolConst () false)

/-- Generate a well-typed closed expression (no free variables or operators)
    by first generating a random type and then an expression of that type. -/
def genClosedLExpr [Gen G] (tvars : List TyIdentifier) (depth : Nat) : G LExpr' := do
  let τ ← genLMonoTy tvars depth
  genLExpr [] [] tvars [] depth τ
