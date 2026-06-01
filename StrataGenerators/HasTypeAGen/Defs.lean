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

abbrev LExprParams' : LExprParams := ⟨Unit, Unit⟩
abbrev LExprParamsT' : LExprParamsT := LExprParams.mono LExprParams'

instance : DecidableEq Unit := instDecidableEqPUnit

abbrev LExpr' := LExpr LExprParamsT'

instance : BEq LMonoTy := instBEqOfDecidableEq

-- ── Contexts ─────────────────────────────────────────────────────────

abbrev BVarCtx := List LMonoTy
abbrev FVarCtx := List (String × LMonoTy)
abbrev OpCtx := List (String × LMonoTy)

-- ── SimpleType and depth ─────────────────────────────────────────────

inductive SimpleType : LMonoTy → Prop where
  | bool  : SimpleType .bool
  | int   : SimpleType .int
  | arrow : SimpleType τ₁ → SimpleType τ₂ → SimpleType (.arrow τ₁ τ₂)
  | ftvar : SimpleType (.ftvar name)

def monoTyDepth : LMonoTy → Nat
  | .arrow τ₁ τ₂ => max (monoTyDepth τ₁) (monoTyDepth τ₂) + 1
  | _             => 0

-- ── Well-typing relation ─────────────────────────────────────────────

abbrev HasTypeA' := LExpr.HasTypeA (T := LExprParams')

-- ── Helpers ──────────────────────────────────────────────────────────

def bvarsOfType (bctx : BVarCtx) (τ : LMonoTy) : List Nat :=
  go bctx 0
where
  go : List LMonoTy → Nat → List Nat
    | [],         _  => []
    | τ' :: rest, i  => if τ' == τ then i :: go rest (i + 1) else go rest (i + 1)

def pickBVar [Gen G] (bctx : BVarCtx) (τ : LMonoTy)
    (_h : (bvarsOfType bctx τ).length > 0) : G LExpr' := do
  let indices := bvarsOfType bctx τ
  let idx ← choose 0 (indices.length - 1) (by omega)
  pure (.bvar () (indices.getD idx.down 0))

def fvarsOfType (fctx : FVarCtx) (τ : LMonoTy) : List String :=
  fctx.filterMap (fun (x, ty) => if ty == τ then some x else none)

def pickFVar [Gen G] (fctx : FVarCtx) (τ : LMonoTy)
    (_h : (fvarsOfType fctx τ).length > 0) : G LExpr' := do
  let names := fvarsOfType fctx τ
  let idx ← choose 0 (names.length - 1) (by omega)
  pure (.fvar () ⟨names.getD idx.down "", ()⟩ (some τ))

def opsOfType (octx : OpCtx) (τ : LMonoTy) : List String :=
  octx.filterMap (fun (x, ty) => if ty == τ then some x else none)

def pickOp [Gen G] (octx : OpCtx) (τ : LMonoTy)
    (_h : (opsOfType octx τ).length > 0) : G LExpr' := do
  let names := opsOfType octx τ
  let idx ← choose 0 (names.length - 1) (by omega)
  pure (.op () ⟨names.getD idx.down "", ()⟩ (some τ))

-- ── Type generator ───────────────────────────────────────────────────

def pickTyVar [Gen G] (tvars : List TyIdentifier)
    (_h : tvars.length > 0) : G LMonoTy := do
  let idx ← choose 0 (tvars.length - 1) (by omega)
  pure (.ftvar (tvars.getD idx.down ""))

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

def genLExpr [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) : Nat → LMonoTy → G LExpr'
  | 0, .arrow τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.arrow τ₁ τ₂)
    pick
      (fun () =>
        if hv : bvars.length > 0 then pickBVar bctx _ hv
        else do
          let body ← genLExpr fctx octx tvars (τ₁ :: bctx) 0 τ₂
          pure (.abs () "" (some τ₁) body))
      (fun () =>
        pick
          (fun () =>
            if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0
            then pickFVar fctx _ hf
            else do
              let body ← genLExpr fctx octx tvars (τ₁ :: bctx) 0 τ₂
              pure (.abs () "" (some τ₁) body))
          (fun () =>
            if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0
            then pickOp octx _ ho
            else do
              let body ← genLExpr fctx octx tvars (τ₁ :: bctx) 0 τ₂
              pure (.abs () "" (some τ₁) body)))
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

def genClosedLExpr [Gen G] (tvars : List TyIdentifier) (size : Nat) : G LExpr' := do
  let τ ← genLMonoTy tvars size
  genLExpr [] [] tvars [] size τ
