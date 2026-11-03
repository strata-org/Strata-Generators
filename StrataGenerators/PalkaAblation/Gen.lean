import StrataGenerators.HasTypeAGen.Core

/-!
# `genLExprBase` with the Pałka et al. branches' weights as parameters

`genLExprBaseW … wI wP` is `genLExprBase` with the weight of every **Indir** branch replaced by
`wI` and of every **IndirPoly** branch by `wP`; nothing else differs (the body is a mechanical copy).
`genLExprBaseW_eq` proves that `wI = wP = 4` *is* `genLExprBase`, so the copy cannot drift from
the shipping generator: a change to one alone breaks that theorem.

The **ablation** is `wI = wP = 0`: the same generator with its Indir and IndirPoly branches (Pałka
et al.'s rules for applying a factory operator) removed at every depth and every type. Everything
else stays, including `genAppArgTy`'s context-directed argument-type guess. (`@[tunable]` cannot express this ablation, since `Tuning.weight` is always
at least `1`.)
-/

open Lambda RandomChoice

def genLExprBaseW [Gen G] (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (wI wP : Nat) (bctx : BVarCtx) : Nat → LMonoTy → G LExpr'
  -- ── Arrow type ────────────────────────────────────────────────────
  | 0, .arrow τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.arrow τ₁ τ₂)
    oneOf
      [ (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        (fun () =>
          if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else default),
        (fun () =>
          if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else default) ]
      (by simp <;> omega)
  | n + 1, .arrow τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.arrow τ₁ τ₂)
    frequency
      [ (4, fun () => genAbs (genLExprBaseW fctx octx pctx tvars wI wP (τ₁ :: bctx) n τ₂) τ₁),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.arrow τ₁ τ₂)) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) (.arrow τ₁ τ₂)),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.arrow τ₁ τ₂))
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.arrow τ₁ τ₂))),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else genAbs (genLExprBaseW fctx octx pctx tvars wI wP (τ₁ :: bctx) n τ₂) τ₁),
        (2, fun () =>
          if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else genAbs (genLExprBaseW fctx octx pctx tvars wI wP (τ₁ :: bctx) n τ₂) τ₁),
        (2, fun () =>
          if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else genAbs (genLExprBaseW fctx octx pctx tvars wI wP (τ₁ :: bctx) n τ₂) τ₁),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx (.arrow τ₁ τ₂)).length > 0
          then genIndir octx (.arrow τ₁ τ₂) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n (.arrow τ₁ τ₂)),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.arrow τ₁ τ₂)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.arrow τ₁ τ₂))) ]
      (by simp <;> omega)
  -- ── Bool type ─────────────────────────────────────────────────────
  | 0, .bool =>
    let bvars := bvarsOfType bctx .bool
    oneOf
      [ (fun () => genBoolConst),
        (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx .bool hv
          else genBoolConst),
        (fun () =>
          if hf : (fvarsOfType fctx .bool).length > 0
          then pickFVar fctx .bool hf
          else genBoolConst),
        (fun () =>
          if ho : (opsOfType octx .bool).length > 0
          then pickOp octx .bool ho
          else genBoolConst) ]
      (by simp <;> omega)
  | n + 1, .bool =>
    let bvars := bvarsOfType bctx .bool
    frequency
      [ (1, fun () => genBoolConst),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .bool) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) .bool),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)),
        (2, fun () => genEq (genGenerableTy fctx octx tvars bctx n) (genLExprBaseW fctx octx pctx tvars wI wP bctx n)),
        (2, fun () => genQuant .all (genGenerableTy fctx octx tvars bctx n)
          (fun τ' => genLExprBaseW fctx octx pctx tvars wI wP (τ' :: bctx) n)
          (fun τ' => genLExprBaseW fctx octx pctx tvars wI wP (τ' :: bctx) n .bool)),
        (2, fun () => genQuant .exist (genGenerableTy fctx octx tvars bctx n)
          (fun τ' => genLExprBaseW fctx octx pctx tvars wI wP (τ' :: bctx) n)
          (fun τ' => genLExprBaseW fctx octx pctx tvars wI wP (τ' :: bctx) n .bool)),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx .bool hv
          else genBoolConst),
        (2, fun () =>
          if hf : (fvarsOfType fctx .bool).length > 0
          then pickFVar fctx .bool hf
          else genBoolConst),
        (2, fun () =>
          if ho : (opsOfType octx .bool).length > 0
          then pickOp octx .bool ho
          else genBoolConst),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx .bool).length > 0
          then genIndir octx .bool (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx .bool
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)) ]
      (by simp <;> omega)
  -- ── Int type ──────────────────────────────────────────────────────
  | 0, .int =>
    let bvars := bvarsOfType bctx .int
    oneOf
      [ (fun () => genIntConst),
        (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx .int hv
          else genIntConst),
        (fun () =>
          if hf : (fvarsOfType fctx .int).length > 0
          then pickFVar fctx .int hf
          else genIntConst),
        (fun () =>
          if ho : (opsOfType octx .int).length > 0
          then pickOp octx .int ho
          else genIntConst) ]
      (by simp <;> omega)
  | n + 1, .int =>
    let bvars := bvarsOfType bctx .int
    frequency
      [ (1, fun () => genIntConst),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .int) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) .int),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .int)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .int)),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else genIntConst),
        (2, fun () =>
          if hf : (fvarsOfType fctx .int).length > 0
          then pickFVar fctx .int hf
          else genIntConst),
        (2, fun () =>
          if ho : (opsOfType octx .int).length > 0
          then pickOp octx .int ho
          else genIntConst),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx .int).length > 0
          then genIndir octx .int (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n .int),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx .int
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n .int)) ]
      (by simp <;> omega)
  -- ── FtVar type (rigid type variable) ────────────────────────────────
  | 0, .ftvar name =>
    let bvars := bvarsOfType bctx (.ftvar name)
    oneOf
      [ (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.ftvar name)).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx (.ftvar name)).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if hf : (fvarsOfType fctx (.ftvar name)).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if ho : (opsOfType octx (.ftvar name)).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if ho : (opsOfType octx (.ftvar name)).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.ftvar name)).length > 0
          then pickFVar fctx _ hf
          else default) ]
      (by simp <;> omega)
  | n + 1, .ftvar name =>
    let bvars := bvarsOfType bctx (.ftvar name)
    frequency
      [ (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.ftvar name)) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) (.ftvar name)),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.ftvar name))
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.ftvar name))),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.ftvar name)).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx (.ftvar name)).length > 0
          then pickOp octx _ ho
          else default),
        (2, fun () =>
          if hf : (fvarsOfType fctx (.ftvar name)).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        (2, fun () =>
          if ho : (opsOfType octx (.ftvar name)).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx (.ftvar name)).length > 0
          then genIndir octx (.ftvar name) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n (.ftvar name)),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.ftvar name)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.ftvar name))) ]
      (by simp <;> omega)
  -- ── String type ────────────────────────────────────────────────────
  | 0, .string =>
    let bvars := bvarsOfType bctx .string
    oneOf
      [ (fun () => genStrConst),
        (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx .string hv
          else genStrConst),
        (fun () =>
          if hf : (fvarsOfType fctx .string).length > 0
          then pickFVar fctx .string hf
          else genStrConst),
        (fun () =>
          if ho : (opsOfType octx .string).length > 0
          then pickOp octx .string ho
          else genStrConst) ]
      (by simp <;> omega)
  | n + 1, .string =>
    let bvars := bvarsOfType bctx .string
    frequency
      [ (1, fun () => genStrConst),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .string) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) .string),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .string)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .string)),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else genStrConst),
        (2, fun () =>
          if hf : (fvarsOfType fctx .string).length > 0
          then pickFVar fctx .string hf
          else genStrConst),
        (2, fun () =>
          if ho : (opsOfType octx .string).length > 0
          then pickOp octx .string ho
          else genStrConst),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx .string).length > 0
          then genIndir octx .string (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n .string),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx .string
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n .string)) ]
      (by simp <;> omega)
  -- ── Real type ─────────────────────────────────────────────────────
  | 0, .real =>
    let bvars := bvarsOfType bctx .real
    oneOf
      [ (fun () => genRealConst),
        (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx .real hv
          else genRealConst),
        (fun () =>
          if hf : (fvarsOfType fctx .real).length > 0
          then pickFVar fctx .real hf
          else genRealConst),
        (fun () =>
          if ho : (opsOfType octx .real).length > 0
          then pickOp octx .real ho
          else genRealConst) ]
      (by simp <;> omega)
  | n + 1, .real =>
    let bvars := bvarsOfType bctx .real
    frequency
      [ (1, fun () => genRealConst),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .real) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) .real),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .real)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .real)),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else genRealConst),
        (2, fun () =>
          if hf : (fvarsOfType fctx .real).length > 0
          then pickFVar fctx .real hf
          else genRealConst),
        (2, fun () =>
          if ho : (opsOfType octx .real).length > 0
          then pickOp octx .real ho
          else genRealConst),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx .real).length > 0
          then genIndir octx .real (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n .real),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx .real
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n .real)) ]
      (by simp <;> omega)
  -- ── Bitvec type ───────────────────────────────────────────────────
  -- The width binder is `w` and not `n`. `@[tunable (depth := n)]` resolves `n` to the innermost
  -- `Nat` local of that name. A width named `n` here would therefore make this site read its weight
  -- schedules at the bitvector width rather than at the remaining depth.
  | 0, .bitvec w =>
    let bvars := bvarsOfType bctx (.bitvec w)
    oneOf
      [ (fun () => genBitvecConst w),
        (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx (.bitvec w) hv
          else genBitvecConst w),
        (fun () =>
          if hf : (fvarsOfType fctx (.bitvec w)).length > 0
          then pickFVar fctx (.bitvec w) hf
          else genBitvecConst w),
        (fun () =>
          if ho : (opsOfType octx (.bitvec w)).length > 0
          then pickOp octx (.bitvec w) ho
          else genBitvecConst w) ]
      (by simp <;> omega)
  | n + 1, .bitvec w =>
    let bvars := bvarsOfType bctx (.bitvec w)
    frequency
      [ (1, fun () => genBitvecConst w),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.bitvec w)) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) (.bitvec w)),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.bitvec w))
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.bitvec w))),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else genBitvecConst w),
        (2, fun () =>
          if hf : (fvarsOfType fctx (.bitvec w)).length > 0
          then pickFVar fctx (.bitvec w) hf
          else genBitvecConst w),
        (2, fun () =>
          if ho : (opsOfType octx (.bitvec w)).length > 0
          then pickOp octx (.bitvec w) ho
          else genBitvecConst w),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx (.bitvec w)).length > 0
          then genIndir octx (.bitvec w) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n (.bitvec w)),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.bitvec w)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.bitvec w))) ]
      (by simp <;> omega)
  -- ── Regex type (base type, no constants) ───────────────────────────
  | 0, .regex =>
    let bvars := bvarsOfType bctx .regex
    oneOf
      [ (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx .regex).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx .regex).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if hf : (fvarsOfType fctx .regex).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if ho : (opsOfType octx .regex).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if ho : (opsOfType octx .regex).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx .regex).length > 0
          then pickFVar fctx _ hf
          else default) ]
      (by simp <;> omega)
  | n + 1, .regex =>
    let bvars := bvarsOfType bctx .regex
    frequency
      [ (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .regex) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) .regex),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .regex)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n .regex)),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx .regex).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx .regex).length > 0
          then pickOp octx _ ho
          else default),
        (2, fun () =>
          if hf : (fvarsOfType fctx .regex).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        (2, fun () =>
          if ho : (opsOfType octx .regex).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx .regex).length > 0
          then genIndir octx .regex (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n .regex),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx .regex
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n .regex)) ]
      (by simp <;> omega)
  -- ── Map type ──────────────────────────────────────────────────────
  | 0, .map τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.map τ₁ τ₂)
    oneOf
      [ (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else default) ]
      (by simp <;> omega)
  | n + 1, .map τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.map τ₁ τ₂)
    frequency
      [ (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.map τ₁ τ₂)) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) (.map τ₁ τ₂)),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.map τ₁ τ₂))
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.map τ₁ τ₂))),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else default),
        (2, fun () =>
          if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        (2, fun () =>
          if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx (.map τ₁ τ₂)).length > 0
          then genIndir octx (.map τ₁ τ₂) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n (.map τ₁ τ₂)),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.map τ₁ τ₂)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.map τ₁ τ₂))) ]
      (by simp <;> omega)
  -- ── Sequence type ─────────────────────────────────────────────────
  | 0, .seq τ =>
    let bvars := bvarsOfType bctx (.seq τ)
    oneOf
      [ (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.seq τ)).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx (.seq τ)).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if hf : (fvarsOfType fctx (.seq τ)).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if ho : (opsOfType octx (.seq τ)).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if ho : (opsOfType octx (.seq τ)).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.seq τ)).length > 0
          then pickFVar fctx _ hf
          else default) ]
      (by simp <;> omega)
  | n + 1, .seq τ =>
    let bvars := bvarsOfType bctx (.seq τ)
    frequency
      [ (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.seq τ)) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) (.seq τ)),
        (2, fun () => genIte (genLExprBaseW fctx octx pctx tvars wI wP bctx n .bool)
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.seq τ))
                              (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.seq τ))),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx (.seq τ)).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx (.seq τ)).length > 0
          then pickOp octx _ ho
          else default),
        (2, fun () =>
          if hf : (fvarsOfType fctx (.seq τ)).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        (2, fun () =>
          if ho : (opsOfType octx (.seq τ)).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else default),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx (.seq τ)).length > 0
          then genIndir octx (.seq τ) (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n (.seq τ)),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.seq τ)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n (.seq τ))) ]
      (by simp <;> omega)
  -- ── The other type constructors ──────────────────────────────────
  --
  -- Such a type is a datatype, an abstract type or the body of an alias. There is no constant at such a type,
  -- so this arm gives `default` when each context that it reads is empty.
  | 0, τ =>
    let bvars := bvarsOfType bctx τ
    oneOf
      [ (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx τ).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx τ).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if hf : (fvarsOfType fctx τ).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if ho : (opsOfType octx τ).length > 0
          then pickOp octx _ ho
          else default),
        (fun () =>
          if ho : (opsOfType octx τ).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx τ).length > 0
          then pickFVar fctx _ hf
          else default) ]
      (by simp <;> omega)
  -- The same three leaves at depth `n + 1`, and also the monomorphic Indir branch
  -- and the polymorphic IndirPoly branch that each named arm has. Indir applies an
  -- operator whose result type is `τ`, and a constructor of the datatype is such an
  -- operator. IndirPoly applies a polymorphic operator at an instance that it
  -- samples, and a derived function of a polymorphic datatype is such an operator.
  -- The two branches put a compound term, such as `Cons(1, Nil)`, at the position of an argument. A variable
  -- and a constructor of arity 0 are the two other terms that can fill that position.
  | n + 1, τ =>
    let bvars := bvarsOfType bctx τ
    frequency
      [ (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx τ).length > 0
          then pickFVar fctx _ hf
          else if ho : (opsOfType octx τ).length > 0
          then pickOp octx _ ho
          else default),
        (2, fun () =>
          if hf : (fvarsOfType fctx τ).length > 0
          then pickFVar fctx _ hf
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if ho : (opsOfType octx τ).length > 0
          then pickOp octx _ ho
          else default),
        (2, fun () =>
          if ho : (opsOfType octx τ).length > 0
          then pickOp octx _ ho
          else if hv : bvars.length > 0 then pickBVar bctx _ hv
          else if hf : (fvarsOfType fctx τ).length > 0
          then pickFVar fctx _ hf
          else default),
        -- The monomorphic Indir rule.
        (wI, fun () =>
          if hi : (findOpsInCtx octx τ).length > 0
          then genIndir octx τ (genLExprBaseW fctx octx pctx tvars wI wP bctx n) hi
          else genLExprBaseW fctx octx pctx tvars wI wP bctx n τ),
        -- The polymorphic IndirPoly rule.
        (wP, fun () =>
          genIndirPolyCore fctx octx pctx bctx τ
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n)
            (genLExprBaseW fctx octx pctx tvars wI wP bctx n τ)) ]
      (by simp <;> omega)

/-- With the shipping weights, the copy is `genLExprBase`. -/
theorem genLExprBaseW_eq [Gen G] (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (n : Nat) :
    ∀ (bctx : BVarCtx) (τ : LMonoTy),
      genLExprBaseW (G := G) fctx octx pctx tvars 4 4 bctx n τ
        = genLExprBase fctx octx pctx tvars bctx n τ := by
  induction n with
  | zero =>
    intro bctx τ
    rw [genLExprBaseW.eq_def]
    split <;> first
      | (exfalso; omega)
      | (rw [genLExprBase.eq_1] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_2] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_3] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_4] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_5] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_6] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_7] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_8] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_9] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_10] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_11] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_12] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_13] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_14] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_15] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_16] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_17] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_18] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_19] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_20] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_21] <;> first | assumption | simp only [ih]) 
      | (rw [genLExprBase.eq_22] <;> first | assumption | simp only [ih]) 
  | succ n ih =>
    have ih' : ∀ bctx, genLExprBaseW (G := G) fctx octx pctx tvars 4 4 bctx n
        = genLExprBase fctx octx pctx tvars bctx n := fun bctx => funext (ih bctx)
    intro bctx τ
    rw [genLExprBaseW.eq_def]
    split <;> (try simp only [Nat.succ.injEq] at *) <;> (try subst_vars) <;> first
      | (exfalso; omega)
      | (rw [genLExprBase.eq_1] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_2] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_3] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_4] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_5] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_6] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_7] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_8] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_9] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_10] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_11] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_12] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_13] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_14] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_15] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_16] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_17] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_18] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_19] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_20] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_21] <;> first | assumption | simp only [ih, ih']) 
      | (rw [genLExprBase.eq_22] <;> first | assumption | simp only [ih, ih']) 
