import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import Basalt.Examples.ArbNat.Def
import Basalt.Examples.ArbChar.Def
import Basalt.Examples.ArbString.Def
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.LTyUnify

open Lambda RandomChoice ArbNat ArbChar ArbString

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
/-- Flattened representation of a factory's operators as (name, curried type) pairs.
    Used internally by the generator and proofs. -/
abbrev OpCtx := List (String × LMonoTy)

-- ── Type abbreviations ──────────────────────────────────────────────

namespace Lambda

/-- The regex monotype (a base type with no parameters). -/
abbrev LMonoTy.regex : LMonoTy := .tcons "regex" []

/-- The Map monotype with key type `k` and value type `v`. -/
abbrev LMonoTy.map (k v : LMonoTy) : LMonoTy := .tcons "Map" [k, v]

/-- The Sequence monotype with element type `a`. -/
abbrev LMonoTy.seq (a : LMonoTy) : LMonoTy := .tcons "Sequence" [a]

end Lambda

-- ── SimpleType and depth ─────────────────────────────────────────────

/-- The fixed set of bitvector widths that `genLMonoTy` may produce. -/
def bitvecWidths : List Nat := [1, 8, 16, 32, 64]

/-- Predicate for bitvector widths producible by `genLMonoTy`. -/
def IsGenWidth (n : Nat) : Prop := n ∈ (bitvecWidths : List Nat)

/-- A monotype is *simple* if it is built from `bool`, `int`, `string`, `real`,
    `bitvec n` (for `IsGenWidth n`), `arrow`, and `ftvar`.
    This characterizes exactly the types produced by `genLMonoTy`. -/
inductive SimpleType : LMonoTy → Prop where
  | bool   : SimpleType .bool
  | int    : SimpleType .int
  | string : SimpleType .string
  | real   : SimpleType .real
  | regex  : SimpleType .regex
  | bitvec : IsGenWidth n → SimpleType (.bitvec n)
  | map    : SimpleType τ₁ → SimpleType τ₂ → SimpleType (.map τ₁ τ₂)
  | seq    : SimpleType τ → SimpleType (.seq τ)
  | arrow  : SimpleType τ₁ → SimpleType τ₂ → SimpleType (.arrow τ₁ τ₂)
  | ftvar  : SimpleType (.ftvar name)

/-- The nesting depth of a monotype: 0 for base types, `max(depth τ₁, depth τ₂) + 1`
    for arrows. Matches the fuel consumed by `genLMonoTy` to produce the type. -/
def monoTyDepth : LMonoTy → Nat
  | .arrow τ₁ τ₂ => max (monoTyDepth τ₁) (monoTyDepth τ₂) + 1
  | .map τ₁ τ₂   => max (monoTyDepth τ₁) (monoTyDepth τ₂) + 1
  | .seq τ        => monoTyDepth τ + 1
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
    (h : (bvarsOfType bctx τ).length > 0) : G LExpr' :=
  have hne : (bvarsOfType bctx τ).map (LExpr.bvar () ·) ≠ [] := by
    simp [List.map_eq_nil_iff]
    exact List.length_pos_iff.mp h
  elements _ hne

/-- All variable names in `fctx` whose type equals `τ`. -/
def fvarsOfType (fctx : FVarCtx) (τ : LMonoTy) : List String :=
  fctx.filterMap (fun (x, ty) => if ty == τ then some x else none)

/-- Pick a uniformly random free variable of type `τ` from `fctx`. The generated
    `fvar` node carries a type annotation `(some τ)` so that `HasTypeA` can
    typecheck it without an external environment. -/
def pickFVar [Gen G] (fctx : FVarCtx) (τ : LMonoTy)
    (h : (fvarsOfType fctx τ).length > 0) : G LExpr' :=
  have hne : (fvarsOfType fctx τ).map (fun name => LExpr.fvar () ⟨name, ()⟩ (some τ)) ≠ [] := by
    simp [List.map_eq_nil_iff]
    exact List.length_pos_iff.mp h
  elements _ hne

/-- All operator names in `octx` whose curried type equals `τ`. -/
def opsOfType (octx : OpCtx) (τ : LMonoTy) : List String :=
  octx.filterMap (fun (x, ty) => if ty == τ then some x else none)

/-- Pick a uniformly random operator of type `τ` from `octx`. -/
def pickOp [Gen G] (octx : OpCtx) (τ : LMonoTy)
    (h : (opsOfType octx τ).length > 0) : G LExpr' :=
  have hne : (opsOfType octx τ).map (fun name => LExpr.op () ⟨name, ()⟩ (some τ)) ≠ [] := by
    simp [List.map_eq_nil_iff]
    exact List.length_pos_iff.mp h
  elements _ hne

-- ── Biased choice combinator ─────────────────────────────────────────────

/-- A biased binary choice: takes the first branch with probability 1/10 (and
    the second with probability 9/10). Used at the outermost branch point of
    recursive generator cases to heavily suppress the probability of trivial
    base-case terms when depth budget remains. -/
def RandomChoice.pickBiased [Monad m] [RandomChoice m] (x y : Unit → m α) := do
  if (← coin (1 / 10)) then x () else y ()

-- ── Type generator ───────────────────────────────────────────────────

/-- Pick a uniformly random type variable name from `tvars` and return it
    as an `LMonoTy.ftvar`. -/
def pickTyVar [Gen G] (tvars : List TyIdentifier)
    (h : tvars.length > 0) : G LMonoTy :=
  have hne : tvars ≠ [] := List.length_pos_iff.mp h
  LMonoTy.ftvar <$> elements tvars hne

/-- Pick a uniformly random bitvector width from `bitvecWidths` and return
    it as an `LMonoTy.bitvec`. -/
def pickBitvecWidth [Gen G] : G LMonoTy :=
  LMonoTy.bitvec <$> elements bitvecWidths (by decide)

/-- Pick a uniformly random base type (bool, int, string, real, regex, or bitvec). -/
def pickBaseType [Gen G] : G LMonoTy :=
  pick (fun () => pure .bool)
       (fun () => pick (fun () => pure .int)
                       (fun () => pick (fun () => pure .string)
                                       (fun () => pick (fun () => pure .real)
                                                       (fun () => pick (fun () => pure .regex)
                                                                       (fun () => pickBitvecWidth)))))

/-- Generate a simple monotype of depth ≤ `n`. When `tvars` is non-empty,
    type variables (`ftvar`) may appear at leaves alongside base types.
    Compound types (arrow, map, sequence) are generated at depth `n + 1`
    with sub-types at depth `n`. -/
def genLMonoTy [Gen G] (tvars : List TyIdentifier) : Nat → G LMonoTy
  | 0 =>
    if h : tvars.length > 0 then
      pick (fun () => pickBaseType)
           (fun () => pickTyVar tvars h)
    else
      pickBaseType
  | n + 1 =>
    if h : tvars.length > 0 then
      pickBiased
        (fun () => pickBaseType)
        (fun () =>
          pick
            (fun () => do
              let τ₁ ← genLMonoTy tvars n
              let τ₂ ← genLMonoTy tvars n
              pure (.arrow τ₁ τ₂))
            (fun () => pick
              (fun () => do
                let τ₁ ← genLMonoTy tvars n
                let τ₂ ← genLMonoTy tvars n
                pure (.map τ₁ τ₂))
              (fun () => pick
                (fun () => do
                  let τ ← genLMonoTy tvars n
                  pure (.seq τ))
                (fun () => pickTyVar tvars h))))
    else
      pickBiased
        (fun () => pickBaseType)
        (fun () =>
          pick
            (fun () => do
              let τ₁ ← genLMonoTy tvars n
              let τ₂ ← genLMonoTy tvars n
              pure (.arrow τ₁ τ₂))
            (fun () => pick
              (fun () => do
                let τ₁ ← genLMonoTy tvars n
                let τ₂ ← genLMonoTy tvars n
                pure (.map τ₁ τ₂))
              (fun () => do
                let τ ← genLMonoTy tvars n
                pure (.seq τ))))

-- ── Expression sub-generator combinators ─────────────────────────────────
-- These combinators take in the generators that they invoke as explicit arguments,
-- in order to avoid mutual recursion (which makes the proofs much more challegning).

/-- Generate a random boolean constant (`true` or `false`). -/
@[reducible] def genBoolConst [Gen G] : G LExpr' :=
  pick (fun () => pure (.boolConst () true))
       (fun () => pure (.boolConst () false))

/-- Generate a random integer constant (non-negative or negative). -/
@[reducible] def genIntConst [Gen G] : G LExpr' :=
  pick (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
       (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int))))

abbrev genAlphanumList [Gen G] : G (List Char) := genCharList

/-- Generate a random string constant (alphanumeric strings). -/
@[reducible] def genStrConst [Gen G] : G LExpr' := do
  let s ← String.arbitrary
  pure (.strConst () s)

/-- Generate a random rational constant (non-negative or negative). -/
@[reducible] def genRealConst [Gen G] : G LExpr' :=
  pick (fun () => do
          let num ← Nat.arbitrary
          let den ← Nat.arbitrary
          pure (.realConst () (↑num / (↑den + 1 : Rat))))
       (fun () => do
          let num ← Nat.arbitrary
          let den ← Nat.arbitrary
          pure (.realConst () (-(↑num / (↑den + 1 : Rat)))))

/-- Generate a random bitvector constant of width `n`. -/
@[reducible] def genBitvecConst [Gen G] (n : Nat) : G LExpr' := do
  let k ← Nat.arbitrary
  pure (.bitvecConst () n (BitVec.ofNat n k))

/-- Generate an application: pick a random argument type, generate the argument
    and a function from that type to `τ`, then apply. -/
@[reducible] def genApp [Gen G] (genTy : G LMonoTy) (genExpr : LMonoTy → G LExpr')
    (τ : LMonoTy) : G LExpr' := do
  let τ' ← genTy
  let arg ← genExpr τ'
  let fn ← genExpr (.arrow τ' τ)
  pure (.app () fn arg)

/-- Generate a lambda abstraction with binder type `τ₁`. -/
@[reducible] def genAbs [Gen G] (genBody : G LExpr') (τ₁ : LMonoTy) : G LExpr' := do
  let body ← genBody
  pure (.abs () "" (some τ₁) body)

/-- Generate an if-then-else expression. -/
@[reducible] def genIte [Gen G] (genCond genThen genElse : G LExpr') : G LExpr' := do
  let c ← genCond
  let t ← genThen
  let e ← genElse
  pure (.ite () c t e)

/-- Generate an equality test: pick a random type, then generate two
    expressions of that type. -/
@[reducible] def genEq [Gen G] (genTy : G LMonoTy) (genExpr : LMonoTy → G LExpr') : G LExpr' := do
  let τ' ← genTy
  let e₁ ← genExpr τ'
  let e₂ ← genExpr τ'
  pure (.eq () e₁ e₂)

/-- Generate a quantifier (∀ or ∃) expression. Picks a binder type and a
    trigger type (the trigger is used for SMT in the LExpr grammar but is otherwise unused by the generator),
    then generates the terms for the trigger and body in the extended context. -/
@[reducible] def genQuant [Gen G] (k : QuantifierKind) (genTy : G LMonoTy)
    (genTrigger : LMonoTy → LMonoTy → G LExpr') (genBody : LMonoTy → G LExpr') : G LExpr' := do
  let τ' ← genTy
  let τ_trigger ← genTy
  let trigger ← genTrigger τ' τ_trigger
  let body ← genBody τ'
  pure (.quant () k "" (some τ') trigger body)

-- ── Expression generator ─────────────────────────────────────────────

/-- Generate a well-typed `LExpr` of type `τ` with term depth bounded by the
    first `Nat` argument. At depth 0, only leaf expressions (bvar, fvar, op,
    constants) are produced; at depth `n+1`, compound expressions may be
    produced with sub-expressions at depth `n`.

    The generated term satisfies `HasTypeA' bctx e τ` (see `genLExpr_sound`). -/
def genLExprBase [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (bctx : BVarCtx) : Nat → LMonoTy → G LExpr'
  -- ── Arrow type ────────────────────────────────────────────────────
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
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (4, fun () => genAbs (genLExprBase fctx octx tvars (τ₁ :: bctx) n τ₂) τ₁),
        (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) (.arrow τ₁ τ₂)),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n (.arrow τ₁ τ₂))
                              (genLExprBase fctx octx tvars bctx n (.arrow τ₁ τ₂))),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else genAbs (genLExprBase fctx octx tvars (τ₁ :: bctx) n τ₂) τ₁),
        (2, fun () =>
          if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else genAbs (genLExprBase fctx octx tvars (τ₁ :: bctx) n τ₂) τ₁),
        (2, fun () =>
          if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else genAbs (genLExprBase fctx octx tvars (τ₁ :: bctx) n τ₂) τ₁) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+4+2+2+2+2; omega
    frequency gs hw
  -- ── Bool type ─────────────────────────────────────────────────────
  | 0, .bool =>
    let bvars := bvarsOfType bctx .bool
    pick
      (fun () => genBoolConst)
      (fun () =>
        pick
          (fun () =>
            if hv : bvars.length > 0 then pickBVar bctx .bool hv
            else genBoolConst)
          (fun () =>
            pick
              (fun () =>
                if hf : (fvarsOfType fctx .bool).length > 0
                then pickFVar fctx .bool hf
                else genBoolConst)
              (fun () =>
                if ho : (opsOfType octx .bool).length > 0
                then pickOp octx .bool ho
                else genBoolConst)))
  | n + 1, .bool =>
    let bvars := bvarsOfType bctx .bool
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genBoolConst),
        (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) .bool),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n .bool)),
        (2, fun () => genEq (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n)),
        (2, fun () => genQuant .all (genLMonoTy tvars n)
          (fun τ' => genLExprBase fctx octx tvars (τ' :: bctx) n)
          (fun τ' => genLExprBase fctx octx tvars (τ' :: bctx) n .bool)),
        (2, fun () => genQuant .exist (genLMonoTy tvars n)
          (fun τ' => genLExprBase fctx octx tvars (τ' :: bctx) n)
          (fun τ' => genLExprBase fctx octx tvars (τ' :: bctx) n .bool)),
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
          else genBoolConst) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+4+2+2+2+2+2+2+2; omega
    frequency gs hw
  -- ── Int type ──────────────────────────────────────────────────────
  | 0, .int =>
    let bvars := bvarsOfType bctx .int
    pick
      (fun () => genIntConst)
      (fun () =>
        pick
          (fun () =>
            if hv : bvars.length > 0 then pickBVar bctx .int hv
            else genIntConst)
          (fun () =>
            pick
              (fun () =>
                if hf : (fvarsOfType fctx .int).length > 0
                then pickFVar fctx .int hf
                else genIntConst)
              (fun () =>
                if ho : (opsOfType octx .int).length > 0
                then pickOp octx .int ho
                else genIntConst)))
  | n + 1, .int =>
    let bvars := bvarsOfType bctx .int
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genIntConst),
        (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) .int),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n .int)
                              (genLExprBase fctx octx tvars bctx n .int)),
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
          else genIntConst) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+4+2+2+2+2; omega
    frequency gs hw
  -- ── FtVar type (rigid type variable) ────────────────────────────────
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
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) (.ftvar name)),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n (.ftvar name))
                              (genLExprBase fctx octx tvars bctx n (.ftvar name))),
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
          else default) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+2+2+2+2; omega
    frequency gs hw
  -- ── String type ────────────────────────────────────────────────────
  | 0, .string =>
    let bvars := bvarsOfType bctx .string
    pick
      (fun () => genStrConst)
      (fun () =>
        pick
          (fun () =>
            if hv : bvars.length > 0 then pickBVar bctx .string hv
            else genStrConst)
          (fun () =>
            pick
              (fun () =>
                if hf : (fvarsOfType fctx .string).length > 0
                then pickFVar fctx .string hf
                else genStrConst)
              (fun () =>
                if ho : (opsOfType octx .string).length > 0
                then pickOp octx .string ho
                else genStrConst)))
  | n + 1, .string =>
    let bvars := bvarsOfType bctx .string
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genStrConst),
        (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) .string),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n .string)
                              (genLExprBase fctx octx tvars bctx n .string)),
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
          else genStrConst) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+4+2+2+2+2; omega
    frequency gs hw
  -- ── Real type ─────────────────────────────────────────────────────
  | 0, .real =>
    let bvars := bvarsOfType bctx .real
    pick
      (fun () => genRealConst)
      (fun () =>
        pick
          (fun () =>
            if hv : bvars.length > 0 then pickBVar bctx .real hv
            else genRealConst)
          (fun () =>
            pick
              (fun () =>
                if hf : (fvarsOfType fctx .real).length > 0
                then pickFVar fctx .real hf
                else genRealConst)
              (fun () =>
                if ho : (opsOfType octx .real).length > 0
                then pickOp octx .real ho
                else genRealConst)))
  | n + 1, .real =>
    let bvars := bvarsOfType bctx .real
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genRealConst),
        (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) .real),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n .real)
                              (genLExprBase fctx octx tvars bctx n .real)),
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
          else genRealConst) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+4+2+2+2+2; omega
    frequency gs hw
  -- ── Bitvec type ───────────────────────────────────────────────────
  | 0, .bitvec n =>
    let bvars := bvarsOfType bctx (.bitvec n)
    pick
      (fun () => genBitvecConst n)
      (fun () =>
        pick
          (fun () =>
            if hv : bvars.length > 0 then pickBVar bctx (.bitvec n) hv
            else genBitvecConst n)
          (fun () =>
            pick
              (fun () =>
                if hf : (fvarsOfType fctx (.bitvec n)).length > 0
                then pickFVar fctx (.bitvec n) hf
                else genBitvecConst n)
              (fun () =>
                if ho : (opsOfType octx (.bitvec n)).length > 0
                then pickOp octx (.bitvec n) ho
                else genBitvecConst n)))
  | m + 1, .bitvec n =>
    let bvars := bvarsOfType bctx (.bitvec n)
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genBitvecConst n),
        (4, fun () => genApp (genLMonoTy tvars m) (genLExprBase fctx octx tvars bctx m) (.bitvec n)),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx m .bool)
                              (genLExprBase fctx octx tvars bctx m (.bitvec n))
                              (genLExprBase fctx octx tvars bctx m (.bitvec n))),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else genBitvecConst n),
        (2, fun () =>
          if hf : (fvarsOfType fctx (.bitvec n)).length > 0
          then pickFVar fctx (.bitvec n) hf
          else genBitvecConst n),
        (2, fun () =>
          if ho : (opsOfType octx (.bitvec n)).length > 0
          then pickOp octx (.bitvec n) ho
          else genBitvecConst n) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+4+2+2+2+2; omega
    frequency gs hw
  -- ── Regex type (base type, no constants) ───────────────────────────
  | 0, .regex =>
    let bvars := bvarsOfType bctx .regex
    pick
      (fun () =>
        if hv : bvars.length > 0 then pickBVar bctx _ hv
        else if hf : (fvarsOfType fctx .regex).length > 0
        then pickFVar fctx _ hf
        else if ho : (opsOfType octx .regex).length > 0
        then pickOp octx _ ho
        else default)
      (fun () =>
        pick
          (fun () =>
            if hf : (fvarsOfType fctx .regex).length > 0
            then pickFVar fctx _ hf
            else if hv : bvars.length > 0 then pickBVar bctx _ hv
            else if ho : (opsOfType octx .regex).length > 0
            then pickOp octx _ ho
            else default)
          (fun () =>
            if ho : (opsOfType octx .regex).length > 0
            then pickOp octx _ ho
            else if hv : bvars.length > 0 then pickBVar bctx _ hv
            else if hf : (fvarsOfType fctx .regex).length > 0
            then pickFVar fctx _ hf
            else default))
  | n + 1, .regex =>
    let bvars := bvarsOfType bctx .regex
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) .regex),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n .regex)
                              (genLExprBase fctx octx tvars bctx n .regex)),
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
          else default) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+2+2+2+2; omega
    frequency gs hw
  -- ── Map type ──────────────────────────────────────────────────────
  | 0, .map τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.map τ₁ τ₂)
    pick
      (fun () =>
        if hv : bvars.length > 0 then pickBVar bctx _ hv
        else if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0
        then pickFVar fctx _ hf
        else if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0
        then pickOp octx _ ho
        else default)
      (fun () =>
        pick
          (fun () =>
            if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0
            then pickFVar fctx _ hf
            else if hv : bvars.length > 0 then pickBVar bctx _ hv
            else if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0
            then pickOp octx _ ho
            else default)
          (fun () =>
            if ho : (opsOfType octx (.map τ₁ τ₂)).length > 0
            then pickOp octx _ ho
            else if hv : bvars.length > 0 then pickBVar bctx _ hv
            else if hf : (fvarsOfType fctx (.map τ₁ τ₂)).length > 0
            then pickFVar fctx _ hf
            else default))
  | n + 1, .map τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.map τ₁ τ₂)
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) (.map τ₁ τ₂)),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n (.map τ₁ τ₂))
                              (genLExprBase fctx octx tvars bctx n (.map τ₁ τ₂))),
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
          else default) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+2+2+2+2; omega
    frequency gs hw
  -- ── Sequence type ─────────────────────────────────────────────────
  | 0, .seq τ =>
    let bvars := bvarsOfType bctx (.seq τ)
    pick
      (fun () =>
        if hv : bvars.length > 0 then pickBVar bctx _ hv
        else if hf : (fvarsOfType fctx (.seq τ)).length > 0
        then pickFVar fctx _ hf
        else if ho : (opsOfType octx (.seq τ)).length > 0
        then pickOp octx _ ho
        else default)
      (fun () =>
        pick
          (fun () =>
            if hf : (fvarsOfType fctx (.seq τ)).length > 0
            then pickFVar fctx _ hf
            else if hv : bvars.length > 0 then pickBVar bctx _ hv
            else if ho : (opsOfType octx (.seq τ)).length > 0
            then pickOp octx _ ho
            else default)
          (fun () =>
            if ho : (opsOfType octx (.seq τ)).length > 0
            then pickOp octx _ ho
            else if hv : bvars.length > 0 then pickBVar bctx _ hv
            else if hf : (fvarsOfType fctx (.seq τ)).length > 0
            then pickFVar fctx _ hf
            else default))
  | n + 1, .seq τ =>
    let bvars := bvarsOfType bctx (.seq τ)
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (4, fun () => genApp (genLMonoTy tvars n) (genLExprBase fctx octx tvars bctx n) (.seq τ)),
        (2, fun () => genIte (genLExprBase fctx octx tvars bctx n .bool)
                              (genLExprBase fctx octx tvars bctx n (.seq τ))
                              (genLExprBase fctx octx tvars bctx n (.seq τ))),
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
          else default) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+2+2+2+2; omega
    frequency gs hw
  -- ── Fallback (other tcons — not generated) ────────────────────────
  | _, _ => pure (.boolConst () false)

-- ── Shared helpers ──────────────────────────────────────────────────

/-- Build a left-nested application: `foldl app base [a₁, a₂, ...] = app (app base a₁) a₂ ...` -/
def mkApps (base : LExpr') (args : List LExpr') : LExpr' :=
  args.foldl (fun acc arg => .app () acc arg) base

-- ── IndirPoly rule helpers ──────────────────────────────────────────

/-- A polymorphic operator context entry: a name paired with a polymorphic type
    scheme (`LTy`). Analogous to `[(String, PolyTyp)]` in the Haskell generator. -/
abbrev PolyOpCtx := List (String × Lambda.LTy)

open Lambda in
/-- Unify two monotypes using Strata's constraint unification.
    Returns `none` on failure, or `some subst` on success. -/
def unifyTypes (t1 t2 : LMonoTy) : Option Lambda.Subst :=
  match Constraints.unify [(t1, t2)] .empty with
  | .ok si => some si.subst
  | .error _ => none

/-- Decompose a curried function type into (argument types, return type). -/
def decomposeArrow : LMonoTy → List LMonoTy × LMonoTy
  | .tcons "arrow" [σ, rest] =>
    let (args, ret) := decomposeArrow rest
    (σ :: args, ret)
  | ty => ([], ty)

/-- Find free type variables in a substitution that haven't been assigned:
    those among `boundVars` that don't appear as keys in `subst`. -/
def findFreeTyVars (boundVars : List TyIdentifier) (subst : Lambda.Subst) : List TyIdentifier :=
  boundVars.filter (fun v => Maps.find? subst v == none)

-- ── Alpha-renaming for polymorphic operators (OpsConsistent fix) ──────
-- See `docs/ops-consistent-capture-bug.md`. Without freshening, a polymorphic
-- operator whose bound type variable shares a name with a free type variable of
-- the target type (e.g. `id : ∀α. α → α` at target `.ftvar "α"`) yields an `.op`
-- annotation that is *not* a valid factory instantiation, violating
-- `OpsConsistent`. Freshening the bound variables away from the context's free
-- variables before unification restores coherence.

/-- Append primes to `candidate` until it avoids `used`, using `fuel` steps.
    `fuel = used.length + 1` always suffices: the candidates produced have
    strictly increasing length, so they are pairwise distinct, and there are
    `fuel` of them for `used.length` names to avoid — by pigeonhole one is
    free. -/
def freshenGo (fuel : Nat) (candidate : String) (used : List TyIdentifier) : TyIdentifier :=
  match fuel with
  | 0 => candidate
  | fuel + 1 =>
    if candidate ∉ used then candidate
    else freshenGo fuel (candidate ++ "'") used

/-- Generate a fresh name not in `used` by appending primes. -/
def freshen (name : TyIdentifier) (used : List TyIdentifier) : TyIdentifier :=
  freshenGo (used.length + 1) name used

/-- Alpha-rename bound variables that collide with `contextVars`.
    Returns `(freshened bound var names, freshened monotype body)`. Bound
    variables that do not collide are left untouched. -/
def freshenBoundVars (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (contextVars : List TyIdentifier) : List TyIdentifier × LMonoTy :=
  let allUsed := contextVars ++ boundVars
  let (freshBound, _) := boundVars.foldl (fun (acc, used) v =>
    if v ∈ contextVars then
      let fresh := freshen v used
      (acc ++ [fresh], fresh :: used)
    else
      (acc ++ [v], used))
    ([], allUsed)
  let renameSubst : Lambda.Subst :=
    [(boundVars.zip freshBound).filterMap (fun (old, new) =>
      if old == new then none else some (old, .ftvar new))]
  let freshMonoTy := LMonoTy.subst renameSubst monoTy
  (freshBound, freshMonoTy)

/-- Compute the set of "generable types" from a context, following
    Pałka et al. (2011, Section 4). We collect all syntactic sub-types
    from the bvar context, fvar context, and op context, then close under
    function application (if `σ → τ` and `σ` are both generable, so is `τ`). -/
def syntacticSubtypes : LMonoTy → List LMonoTy
  | ty@(.tcons "arrow" [a, b]) => ty :: (syntacticSubtypes a ++ syntacticSubtypes b)
  | ty => [ty]

/-- Iteratively close a set of types under function application:
    if `σ → τ` and `σ` are both in the set, then `τ` is added.
    Uses a fuel parameter to ensure termination. -/
def addNewTypes (fuel : Nat) (tys : List LMonoTy) : List LMonoTy :=
  match fuel with
  | 0 => tys
  | fuel + 1 =>
    let newTys := tys.filterMap fun ty =>
      match ty with
      | .tcons "arrow" [argTy, retTy] =>
        if argTy ∈ tys && retTy ∉ tys then some retTy else none
      | _ => none
    if newTys.isEmpty then tys
    else addNewTypes fuel (tys ++ newTys)

/-- Compute the set of "generable types" reachable from a context, following
    Pałka et al. (2011, Section 4). This is a conservative over-approximation of
    the types that are *inhabited* (i.e. for which some term can be built) given
    the variables and operators in scope. It is used to bias type guesses — in
    the (App) rule and when instantiating undetermined type variables of a
    polymorphic operator (see `genIndirPoly`) — towards types that are plausibly
    inhabited, rather than guessing arbitrary types that would dead-end and force
    backtracking.

    The computation has two stages, mirroring the paper:
    1. **Seed.** Collect the syntactic sub-types (`syntacticSubtypes`) of every
       type in the bvar, fvar, and op contexts. Decomposing into sub-types (down
       to base types) is what makes the next stage able to fire: e.g. from
       `f : String → Bool → Int` we seed `String`, `Bool`, `Int`, `Bool → Int`,
       not just the whole arrow type.
    2. **Close under application** (`addNewTypes`). Repeatedly add `τ` whenever
       both `σ → τ` and `σ` are already present — i.e. if we can build a function
       and its argument, we can build its result. `fuel = initial.length` bounds
       the iterations (each round adds at least one new type, or stops).

    Note: unlike the paper, we do not additionally *fabricate* new arrow types
    from this set here; arrow-type generation is handled separately by
    `genLMonoTy`. So this implements only the "select an inhabited type directly"
    half of the paper's construction. -/
def generableTypesFromCtx (bctx : BVarCtx) (fctx : FVarCtx) (octx : OpCtx) : List LMonoTy :=
  let allTys := bctx ++ fctx.map Prod.snd ++ octx.map Prod.snd
  let initial := (allTys.flatMap syntacticSubtypes).eraseDups
  -- Use fuel = initial.length as an upper bound on iterations
  addNewTypes initial.length initial

/-- For each polymorphic operator in `pctx`, attempt to unify its return type
    with the target type `τ`. Returns a list of
    `(name, concreteArgTypes, fullConcreteType)` triples for operators that
    successfully unify (with undetermined type variables to be sampled). -/
def findPolyOpsForResult (pctx : PolyOpCtx) (τ : LMonoTy)
    (generableTys : List LMonoTy) : List (String × List LMonoTy × LMonoTy) :=
  pctx.filterMap fun (name, lty) =>
    match lty with
    | .forAll boundVars monoTy =>
      let (argTys, retTy) := decomposeArrow monoTy
      if argTys.isEmpty || argTys.length > 3 then none
      else match unifyTypes retTy τ with
        | none => none
        | some subst =>
          let freeTyVars := findFreeTyVars boundVars subst
          if !freeTyVars.isEmpty && generableTys.isEmpty then none
          else some (name, argTys, monoTy, subst, freeTyVars)
  |>.map fun (name, argTys, monoTy, subst, freeTyVars) =>
    let defaultSubst : Lambda.SubstOne := freeTyVars.map (fun v => (v, generableTys.headD .bool))
    let fullSubst : Lambda.Subst := defaultSubst :: subst
    let concreteArgTys := argTys.map (LMonoTy.subst fullSubst)
    let concreteTy := LMonoTy.subst fullSubst monoTy
    (name, concreteArgTys, concreteTy)

/-- Collect the concrete (name, argTypes) pairs that result from instantiating
    polymorphic operators against target type `τ`. This is the pure computation
    that determines which operators can be called and at which types.

    Each entry `(name, concreteArgTys)` means operator `name` can be called with
    arguments of types `concreteArgTys` to produce a result of type `τ`. -/
def polyOpsForResult (pctx : PolyOpCtx) (τ : LMonoTy)
    (generableTys : List LMonoTy) (sampledTys : List LMonoTy)
    : List (String × List LMonoTy) :=
  -- Free type variables in scope that a bound var must not be captured by:
  -- those of the target type together with those of the sampled generable types.
  let contextVars := (LMonoTy.freeVars τ ++ generableTys.flatMap LMonoTy.freeVars).eraseDups
  pctx.filterMap fun (name, lty) =>
    match lty with
    | .forAll boundVars monoTy =>
      -- Alpha-rename the operator's bound vars away from `contextVars` so that a
      -- bound var sharing a name with a context free var doesn't get treated as
      -- already-solved by unification (see `docs/ops-consistent-capture-bug.md`).
      let (freshBoundVars, freshMonoTy) := freshenBoundVars boundVars monoTy contextVars
      let (argTys, retTy) := decomposeArrow freshMonoTy
      if argTys.isEmpty || argTys.length > 3 then none
      else match unifyTypes retTy τ with
        | none => none
        | some subst =>
          let freeTyVars := findFreeTyVars freshBoundVars subst
          if !freeTyVars.isEmpty && generableTys.isEmpty then none
          else
            let fullSubst : Lambda.Subst := (freeTyVars.zip sampledTys) :: subst
            let concreteArgTys := argTys.map (LMonoTy.subst fullSubst)
            -- Forward-instance guard (declarative `OpsConsistentR`; see
            -- `docs/ops-consistent-polymorphic-gap.md`). We keep the candidate iff
            -- applying the generator's own substitution `fullSubst` to the return
            -- type `retTy` actually yields the target `τ`.
            --
            -- Why this is needed for `OpsConsistentR` (which never runs
            -- `opTypeSubst`): the emitted annotation is built as
            -- `concreteArgTys.foldr arrow τ`, i.e. it *hardcodes* `τ` in the return
            -- position. To discharge `OpsConsistentR.op_in` the soundness proof
            -- (`polyOpsForResult_instanceR`) must exhibit *some* substitution `S`
            -- with `annotation = genericTy.subst S`, and it constructs that witness
            -- from `fullSubst` (composed with the freshening renaming). That witness
            -- reproduces the annotation's return position as `subst fullSubst retTy`
            -- — so the hardcoded `τ` and the witness-produced return agree exactly
            -- when `subst fullSubst retTy = τ`. This guard enforces that
            -- precondition; the proof then reads it back off via `beq_iff_eq`.
            --
            -- It rejects only the candidates where unification oriented the
            -- `retTy ~ τ` equation against `τ` (e.g. `id : ∀α. α → α` at target `β`,
            -- where `unify α β` may solve `β ↦ α`: then `subst fullSubst retTy = α ≠
            -- β = τ` and no `fullSubst`-derived witness reconstructs the annotation).
            -- It is strictly more permissive than the old ground-only guard: it
            -- still admits annotations mentioning a free (non-quantified) type
            -- variable, as long as that variable comes from the context (`τ`/the
            -- sampled types) and the forward reading holds.
            if LMonoTy.subst fullSubst retTy == τ then
              some (name, concreteArgTys)
            else none

/-- Generate a well-typed `LExpr` of type `τ` using the IndirPoly rule from
    Pałka et al. (2011, Section 4). Calls polymorphic library functions by:
    1. Unifying the function's return type with the target type `τ`
    2. Sampling undetermined type variables from the set of generable types
    3. Generating arguments at the resulting concrete types

    This is analogous to `genIndirPoly` in the Haskell generator.

    The structure mirrors the monomorphic `genLExpr` Indir rule:
    given a list of `(name, concreteArgTys)` candidates, choose one,
    generate args via `mapM genLExprBase`, and assemble via `mkApps`. -/
def genIndirPoly [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) : G LExpr' := do
  -- Compute the set of generable types from the current context
  let generableTys := generableTypesFromCtx bctx fctx octx
  -- Sample types for instantiation (one per possible free tyvar, up to 3)
  let sampledTys ← List.replicate 3 ()
    |>.mapM (fun _ =>
      if hg : generableTys.length > 0 then do
        let tidx ← choose 0 (generableTys.length - 1) (by omega)
        pure (generableTys.getD tidx.down .bool)
      else pure .bool)
  -- Compute concrete candidates
  let ops := polyOpsForResult pctx τ generableTys sampledTys
  if h : ops.length > 0 then do
    -- Randomly choose one candidate
    let idx ← choose 0 (ops.length - 1) (by omega)
    let (name, concreteArgTys) := ops.getD idx.down ("", [])
    -- Construct the op with the full curried type annotation
    let fullArrowTy := concreteArgTys.foldr (fun σ acc => .arrow σ acc) τ
    let opExpr : LExpr' := .op () ⟨name, ()⟩ (some fullArrowTy)
    -- Generate arguments
    let args ← concreteArgTys.mapM (genLExprBase fctx octx tvars bctx depth)
    pure (mkApps opExpr args)
  else
    -- No candidates: fall back to base generator
    genLExprBase fctx octx tvars bctx depth τ

-- ── Indir rule helpers ──────────────────────────────────────────────

/-- Extract the argument types from a curried function type, given that its
    result type (after peeling all arrows) should equal `τ`. Returns `none`
    if the type does not return `τ`, or `some args` where `args` is the list
    of argument types.
    E.g. `argsForResult (.arrow .int (.arrow .int .int)) .int = some [.int, .int]`
         `argsForResult (.arrow .int .bool) .int = none`
         `argsForResult .int .int = some []` -/
def argsForResult (fullTy : LMonoTy) (τ : LMonoTy) : Option (List LMonoTy) :=
  match fullTy with
  | .tcons "arrow" [σ, rest] =>
    match argsForResult rest τ with
    | some args => some (σ :: args)
    | none => none
  | other => if other == τ then some [] else none

/-- All (name, argTypes) pairs from `octx` for operators that return `τ`
    after they have been fully applied. -/
def findOpsInCtx (octx : OpCtx) (τ : LMonoTy) : List (String × List LMonoTy) :=
  octx.filterMap fun (name, ty) =>
    match argsForResult ty τ with
    | some (arg :: args) => some (name, arg :: args)
    | _ => none

/-- Generate a well-typed `LExpr` of type `τ` using the Indir rule from
    Pałka et al. (2011) in addition to the standard generation rules.

    When operators in `octx` have result type `τ` (after full application),
    the generator non-deterministically picks between:
    - The **Indir rule**: pick such an operator and recursively generate all
      its arguments at the determined types (no type guessing needed).
    - The **standard rules** (`genLExprBase`): variables, constants, App with
      random type, lambda, if-then-else, etc.

    This produces significantly more fully-applied operator expressions
    (e.g. `Int.Add #1 #2`) compared to relying solely on the App rule's
    random type guessing. -/
def genLExpr [Gen G] (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) : G LExpr' :=
  if h : (findOpsInCtx octx τ).length > 0 then
    pickBiased
      (fun () => genLExprBase fctx octx tvars bctx depth τ)
      (fun () =>
        pick
          (fun () => do
            -- Monomorphic Indir rule: find all operators `ops` in the context
            -- that when fully applied, produce a term of the result type `τ`
            let ops := findOpsInCtx octx τ
            -- Randomly choose one of these operators
            let idx ← choose 0 (ops.length - 1) (by omega)
            let (name, argTys) := ops.getD idx.down ("", [])
            -- Construct the `LExpr` corresponding to the chosen `op`
            let fullArrowTy := argTys.foldr (fun σ acc => .arrow σ acc) τ
            let opExpr := .op () ⟨name, ()⟩ (some fullArrowTy)
            -- Iterate through the argument types in order
            -- and generate successive random terms of those types
            let args ← List.mapM (genLExprBase fctx octx tvars bctx depth) argTys
            -- Then, apply the operator to all the args
            pure (mkApps opExpr args))
          (fun () =>
            -- Polymorphic IndirPoly rule (Pałka et al. 2011, Section 4)
            genIndirPoly fctx octx pctx tvars bctx depth τ))
  else
    -- No monomorphic Indir candidates; try IndirPoly or fall back to base
    pick
      (fun () => genLExprBase fctx octx tvars bctx depth τ)
      (fun () => genIndirPoly fctx octx pctx tvars bctx depth τ)

-- ── Top-level generators ─────────────────────────────────────────────

/-- Generate a well-typed closed expression (no free variables, no operators)
    with bounded depth. -/
def genClosedLExpr [Gen G] (tvars : List TyIdentifier) (depth : Nat) : G LExpr' := do
  let τ ← genLMonoTy tvars depth
  genLExpr [] [] [] tvars [] depth τ
