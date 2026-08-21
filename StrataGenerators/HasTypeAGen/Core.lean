import Std.Data.HashMap
import Basalt.Gen
import Basalt.IO
import Basalt.Combinators
import BasaltExamples.ArbChar.Def
import BasaltExamples.ArbString.Def
import StrataGenerators.PrimitiveGens
import Strata.Languages.Core.Factory
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.LTyUnify

namespace ArbNat
open RandomChoice

/-- A generator for a `Nat`.

    This file keeps the definition local and does not import `BasaltExamples.ArbNat`, because that
    module imports the full `Basalt` library. `Basalt` gives `List.dedup` of Mathlib, which collides
    with `List.dedup` of Strata. This file must stay free of Mathlib. The definition here is
    definitionally equal to the one in Basalt, so a proof can unfold either one. -/
def Nat.arbitrary [Gen G] : G Nat := do
  pick
    (fun () => pure 0)
    (fun () => do
      let n ← Nat.arbitrary
      pure (n + 1))
partial_fixpoint

end ArbNat

open Lambda RandomChoice ArbNat ArbChar ArbString

-- ── Parameter types ──────────────────────────────────────────────────

/-- The base `LExprParams` of this package: unit metadata and unit identifier metadata. -/
abbrev LExprParams' : LExprParams := ⟨Unit, Unit⟩
/-- The full `LExprParamsT`, which uses `LMonoTy` as the type of an annotation. -/
abbrev LExprParamsT' : LExprParamsT := LExprParams.mono LExprParams'

instance : DecidableEq Unit := instDecidableEqPUnit

/-- The expression type of this package: an `LExpr` with unit metadata and monotype annotations. -/
abbrev LExpr' := LExpr LExprParamsT'

instance : BEq LMonoTy := instBEqOfDecidableEq

-- ── Contexts ─────────────────────────────────────────────────────────

/-- A context for the bound variables. `bctx[i]?` is the type of the de Bruijn index `i`. -/
abbrev BVarCtx := List LMonoTy
/-- A context for the free variables. It maps the name of a variable to its type. -/
abbrev FVarCtx := List (String × LMonoTy)

/-- The operators of a factory, as a list of (name, curried type) pairs.

    This is the plain list. `OpCtx` below holds this list with an index by type. -/
abbrev OpList := List (String × LMonoTy)

/-- Each operator name in `ops` that has the curried type `τ`. A linear scan finds
    the names.

    This function is the specification of an operator lookup by type.
    `OpCtx.opsOfType` is the fast form. `OpCtx.agrees` shows that the two functions
    give the same list, in the same order. Each proof in this package uses this scan.
    No proof uses the hash map. -/
def opsOfTypeList (ops : OpList) (τ : LMonoTy) : List String :=
  ops.filterMap (fun (x, ty) => if ty == τ then some x else none)

/-- One step of the fold in `OpCtx.ofList`. The step appends the name in `p` to the
    entry for the type in `p`.

    The append keeps the order of the scan. Therefore `agrees` can be an equality of
    lists. This form of the invariant is the most convenient one. A proof can rewrite a
    lookup into the scan, and back, with no side condition.

    The order is not necessary for the distribution of the generator. The names in one
    of these lists are all different. `pickOp` draws a uniform index. Therefore
    `pickOp` is uniform over the elements for each possible order. -/
private def opIndexStep (m : Std.HashMap LMonoTy (List String)) (p : String × LMonoTy) :
    Std.HashMap LMonoTy (List String) :=
  m.insert p.2 (m.getD p.2 [] ++ [p.1])

/-- The fold of `opIndexStep` over `l` adds the scan of `l` at `τ` to the entry that
    `m` holds for `τ`.

    The lemma applies to an arbitrary start map `m`. This generality makes the
    induction step possible, because the recursive call gets the extended map and not
    `∅`. -/
private theorem getD_foldl_opIndexStep (l : OpList)
    (m : Std.HashMap LMonoTy (List String)) (τ : LMonoTy) :
    (l.foldl opIndexStep m).getD τ [] = m.getD τ [] ++ opsOfTypeList l τ := by
  induction l generalizing m with
  | nil => simp [opsOfTypeList]
  | cons p rest ih =>
    simp only [List.foldl_cons, ih, opIndexStep, opsOfTypeList, List.filterMap_cons]
    by_cases h : p.2 = τ
    · subst h; simp
    · rw [Std.HashMap.getD_insert]; simp [h, beq_iff_eq]

/-- An operator context. It holds the operators of a factory as (name, curried type)
    pairs, together with an index from a type to the operators of that type.

    A generator looks for an operator by type one time at each candidate leaf. The context holds each
    function of `Core.Factory`, which is more than 300 entries. The index makes each lookup one hash and
    not a linear scan. The index is also small, because those entries have far fewer different curried
    types. The index does not make the whole generator faster, because a lookup is not the largest cost.

    The `agrees` field connects the index to the scan that specifies it. Therefore the index cannot
    disagree with `ops`. `Lambda.Factory` uses the same pattern, with an array and a hash map from a name
    to an index, and invariants between them. The key here is the curried type, because a generator looks
    for an operator by type. Strata looks for an operator by name, and it therefore needs no index by
    type.

    `OpCtx` holds the index. A separate structure beside `OpCtx` is also possible, but then `opsOfType`,
    `pickOp` and each lemma about them need a new signature. With the index inside `OpCtx`, those
    signatures do not change. -/
structure OpCtx where
  /-- The operators, in the order of the factory. The proofs use this list. -/
  ops : OpList
  /-- The index. It maps a type to the names of the operators of that type. -/
  byType : Std.HashMap LMonoTy (List String)
  /-- The index gives the same list as the scan, in the same order. -/
  agrees : ∀ τ, byType.getD τ [] = opsOfTypeList ops τ

/-- Make an operator context. This function computes the index from the list. -/
def OpCtx.ofList (ops : OpList) : OpCtx :=
  { ops := ops
    byType := ops.foldl opIndexStep ∅
    agrees := fun τ => by simpa using getD_foldl_opIndexStep ops ∅ τ }

/-- The empty operator context. -/
instance : Inhabited OpCtx := ⟨OpCtx.ofList []⟩
instance : EmptyCollection OpCtx := ⟨OpCtx.ofList []⟩

@[simp] theorem OpCtx.ops_ofList (ops : OpList) : (OpCtx.ofList ops).ops = ops := rfl

@[simp] theorem OpCtx.ops_empty : (∅ : OpCtx).ops = [] := rfl

-- ── Type abbreviations ──────────────────────────────────────────────

namespace Lambda

/-- The regex monotype (a base type with no parameters). -/
@[match_pattern] abbrev LMonoTy.regex : LMonoTy := .tcons "regex" []

/-- The Map monotype with key type `k` and value type `v`. -/
@[match_pattern] abbrev LMonoTy.map (k v : LMonoTy) : LMonoTy := .tcons "Map" [k, v]

/-- The Sequence monotype with element type `a`. -/
@[match_pattern] abbrev LMonoTy.seq (a : LMonoTy) : LMonoTy := .tcons "Sequence" [a]

end Lambda

-- ── Monotype depth ───────────────────────────────────────────────────

/-- The depth of a monotype. A base type has the depth 0. A compound type has the depth of its
    largest component plus 1. The value is the fuel that `genLMonoTy` needs for the type. -/
def monoTyDepth : LMonoTy → Nat
  | .arrow τ₁ τ₂ => max (monoTyDepth τ₁) (monoTyDepth τ₂) + 1
  | .map τ₁ τ₂   => max (monoTyDepth τ₁) (monoTyDepth τ₂) + 1
  | .seq τ        => monoTyDepth τ + 1
  | _             => 0

-- ── Well-typing relation ─────────────────────────────────────────────

/-- The `HasTypeA` typing judgement of Strata, at the parameter types of this package. -/
abbrev HasTypeA' := LExpr.HasTypeA (T := LExprParams')

-- ── Helpers ──────────────────────────────────────────────────────────

/-- Each de Bruijn index in `bctx` that has the type `τ`. -/
def bvarsOfType (bctx : BVarCtx) (τ : LMonoTy) : List Nat :=
  go bctx 0
where
  go : List LMonoTy → Nat → List Nat
    | [],         _  => []
    | τ' :: rest, i  => if τ' == τ then i :: go rest (i + 1) else go rest (i + 1)

/-- Draw a uniformly random bound variable of the type `τ` from `bctx`. -/
def pickBVar [Gen G] (bctx : BVarCtx) (τ : LMonoTy)
    (h : (bvarsOfType bctx τ).length > 0) : G LExpr' :=
  have hne : (bvarsOfType bctx τ).map (LExpr.bvar () ·) ≠ [] := by
    simp [List.map_eq_nil_iff]
    exact List.length_pos_iff.mp h
  elements _ hne

/-- Each variable name in `fctx` that has the type `τ`. -/
def fvarsOfType (fctx : FVarCtx) (τ : LMonoTy) : List String :=
  fctx.filterMap (fun (x, ty) => if ty == τ then some x else none)

/-- Draw a uniformly random free variable of the type `τ` from `fctx`. The `fvar` node holds the type
    annotation `(some τ)`, so `HasTypeA` can type check it with no external environment. -/
def pickFVar [Gen G] (fctx : FVarCtx) (τ : LMonoTy)
    (h : (fvarsOfType fctx τ).length > 0) : G LExpr' :=
  have hne : (fvarsOfType fctx τ).map (fun name => LExpr.fvar () ⟨name, ()⟩ (some τ)) ≠ [] := by
    simp [List.map_eq_nil_iff]
    exact List.length_pos_iff.mp h
  elements _ hne

/-- Each operator name in `octx` that has the curried type `τ`.

    This function reads the index and does no scan. Therefore the cost does not
    increase with the size of the context. `opsOfType_eq_scan` below shows that the
    result is the same list, in the same order, as the linear scan
    `opsOfTypeList octx.ops τ`. Therefore each proof that unfolds a lookup uses the
    scan and never the hash map. -/
def opsOfType (octx : OpCtx) (τ : LMonoTy) : List String :=
  octx.byType.getD τ []

/-- The fast lookup is equal to the scan. This lemma is the only connection that the
    proofs need. A proof that must see the contents of a lookup uses
    `simp only [opsOfType_eq_scan, opsOfTypeList, …]`.

    This lemma is not a `@[simp]` lemma, and this is deliberate. Almost every proof
    about the generator holds `opsOfType octx τ` as an opaque list. The list is the
    guard of an `if`, or the argument of `pickOp`. A rewrite to a `filterMap` in all of
    those goals changes their shape and gives no benefit. Only the few proofs that must
    see the contents of the lookup name this lemma. -/
theorem opsOfType_eq_scan (octx : OpCtx) (τ : LMonoTy) :
    opsOfType octx τ = opsOfTypeList octx.ops τ :=
  octx.agrees τ

theorem opsOfType_empty (τ : LMonoTy) : opsOfType ∅ τ = [] := by
  rw [opsOfType_eq_scan]; simp [opsOfTypeList]

/-- Draw a uniformly random operator of the type `τ` from `octx`. -/
def pickOp [Gen G] (octx : OpCtx) (τ : LMonoTy)
    (h : (opsOfType octx τ).length > 0) : G LExpr' :=
  have hne : (opsOfType octx τ).map (fun name => LExpr.op () ⟨name, ()⟩ (some τ)) ≠ [] := by
    simp [List.map_eq_nil_iff]
    exact List.length_pos_iff.mp h
  elements _ hne

-- ── Type generator ───────────────────────────────────────────────────

/-- Draw a uniformly random type-variable name from `tvars`, and give it as an `LMonoTy.ftvar`. -/
def pickTyVar [Gen G] (tvars : List TyIdentifier)
    (h : tvars.length > 0) : G LMonoTy :=
  have hne : tvars ≠ [] := List.length_pos_iff.mp h
  LMonoTy.ftvar <$> elements tvars hne

/-- Draw a random bitvector width, and give it as an `LMonoTy.bitvec`. The width comes from
    `Nat.arbitrary`, and it can be any natural number, because the Strata Core syntax puts no limit on
    the width of a bitvector. -/
def pickBitvecWidth [Gen G] : G LMonoTy :=
  LMonoTy.bitvec <$> Nat.arbitrary

/-- The names of the base type constructors of arity 0 in Strata Core, which are `bool`, `int`,
    `string`, `real` and `regex`.

    These are the ground type names that `pickBaseType` gives, as `.tcons name []`. They are also the
    names that `inGenLMonoTySupport` accepts, and the pool of base types for the datatype generator.
    A bitvector is separate, because its width is a parameter and not a name. `pickBitvecWidth`
    handles it. -/
def nullaryBaseTypeNames : List String :=
  ["bool", "int", "string", "real", "regex"]

/-- Draw a uniformly random base type: `bool`, `int`, `string`, `real`, `regex` or a bitvector. -/
def pickBaseType [Gen G] : G LMonoTy :=
  oneOf
    [ (fun () => pure .bool),
      (fun () => pure .int),
      (fun () => pure .string),
      (fun () => pure .real),
      (fun () => pure .regex),
      (fun () => pickBitvecWidth) ]
    (by simp)

/-- Generate a simple monotype of a depth that is not more than `n`.

    When `tvars` holds a name, a type variable can also appear at a leaf, beside a base type. At the
    depth `n + 1`, the generator can give a compound type, which is an arrow, a map or a sequence,
    with each component at the depth `n`. -/
def genLMonoTy [Gen G] (tvars : List TyIdentifier) : Nat → G LMonoTy
  | 0 =>
    if h : tvars.length > 0 then
      pick (fun () => pickBaseType)
           (fun () => pickTyVar tvars h)
    else
      pickBaseType
  | n + 1 =>
    if h : tvars.length > 0 then
      frequency
        [ (9, fun () => pickBaseType),
          (1, fun () =>
            oneOf
              [ (fun () => do
                  let τ₁ ← genLMonoTy tvars n
                  let τ₂ ← genLMonoTy tvars n
                  pure (.arrow τ₁ τ₂)),
                (fun () => do
                  let τ₁ ← genLMonoTy tvars n
                  let τ₂ ← genLMonoTy tvars n
                  pure (.map τ₁ τ₂)),
                (fun () => do
                  let τ ← genLMonoTy tvars n
                  pure (.seq τ)),
                (fun () => pickTyVar tvars h) ]
              (by simp)) ]
        (by simp)
    else
      frequency
        [ (9, fun () => pickBaseType),
          (1, fun () =>
            oneOf
              [ (fun () => do
                  let τ₁ ← genLMonoTy tvars n
                  let τ₂ ← genLMonoTy tvars n
                  pure (.arrow τ₁ τ₂)),
                (fun () => do
                  let τ₁ ← genLMonoTy tvars n
                  let τ₂ ← genLMonoTy tvars n
                  pure (.map τ₁ τ₂)),
                (fun () => do
                  let τ ← genLMonoTy tvars n
                  pure (.seq τ)) ]
              (by simp)) ]
        (by simp)

-- ── The combinators for a sub-generator of an expression ─────────────
--
-- Each combinator takes the generators that it calls as explicit arguments. Therefore no combinator
-- is mutually recursive with another one, and each proof about a combinator stays simple.

/-- Generate a random boolean constant, which is `true` or `false`. -/
@[reducible] def genBoolConst [Gen G] : G LExpr' :=
  pick (fun () => pure (.boolConst () true))
       (fun () => pure (.boolConst () false))

/-- Generate a random integer constant. The value can be negative or not negative. -/
@[reducible] def genIntConst [Gen G] : G LExpr' :=
  pick (fun () => do let k ← Nat.arbitrary; pure (.intConst () (k : Int)))
       (fun () => do let k ← Nat.arbitrary; pure (.intConst () (-(↑k + 1 : Int))))

/-- The list of characters that `String.arbitrary` of Basalt draws from. -/
abbrev genAlphanumList [Gen G] : G (List Char) := listOf Char.arbitrary

/-- Generate a random string constant.

    The generator draws from `genInterestingString`
    (`StrataGenerators.PrimitiveGens`), and not from `String.arbitrary` of Basalt.
    `String.arbitrary` gives only characters that satisfy `Char.isAlphanum`, and
    therefore it never goes outside printable ASCII. The non-ASCII pool is what
    makes the agreement property between SMT and concrete evaluation non-vacuous
    at type `string`. An ASCII-only pool cannot reach the defect in the SMT-LIB
    escape function.

    The support proofs depend on the shape `do let s ← _; pure (.strConst () s)`. Each such proof
    takes the shape apart as one `bind` and then one `pure`, and it discards the inner membership
    hypothesis. Therefore a proof does not depend on *which* generator gives the string, but it does
    depend on the shape. -/
@[reducible] def genStrConst [Gen G] : G LExpr' := do
  let s ← StrataGenerators.PrimitiveGens.genInterestingString
  pure (.strConst () s)

/-- Generate a random rational constant.

    The generator draws from `genRat` (`StrataGenerators.PrimitiveGens`). `genRat`
    builds its value with `mkRat`, the smart constructor from the standard library,
    so the result is always in normal form. It is also biased toward a **non-zero**
    rational: about 9% of the draws are zero. A generator that draws its numerator
    from `Nat.arbitrary` gives a zero numerator half of the time, which makes the
    whole value zero, and about 46% of its draws are zero.

    The code depends on the shape, which is one `bind` and then one `pure`. Read
    `genStrConst`. -/
@[reducible] def genRealConst [Gen G] : G LExpr' := do
  let r ← StrataGenerators.PrimitiveGens.genRat
  pure (.realConst () r)

/-- Generate a random bitvector constant of width `n`.

    The generator draws from `genBiasedBitVec` (`StrataGenerators.PrimitiveGens`).
    `genBiasedBitVec` has a weight of 7 to 1 for a boundary value over a plain
    `Nat.arbitrary` draw. The boundary values are `INT_MIN`, `INT_MAX`, `0`, `1`,
    `allOnes` or `-1`, and the powers of two with their neighbours. The bias is
    important because the signed overflow predicates are true only at a boundary.
    `BitVec.negOverflow` and `BitVec.sdivOverflow` are true *only* at `INT_MIN`. A
    geometric generator, whose values group near zero, reaches that value with
    probability about `2^-n`.

    The unbiased tail, which is 1 draw in 8, keeps the support complete. Each
    `BitVec n` stays reachable, so this generator narrows nothing that the
    completeness proofs quantify over. The code depends on the shape, which is one
    `bind` and then one `pure`. Read `genStrConst`. -/
@[reducible] def genBitvecConst [Gen G] (n : Nat) : G LExpr' := do
  let k ← StrataGenerators.PrimitiveGens.genBiasedBitVec n
  pure (.bitvecConst () n k)

/-- Generate an application. The generator draws a random argument type. It then generates the
    argument, and a function from that type to `τ`, and it applies the function to the argument. -/
@[reducible] def genApp [Gen G] (genTy : G LMonoTy) (genExpr : LMonoTy → G LExpr')
    (τ : LMonoTy) : G LExpr' := do
  let τ' ← genTy
  let arg ← genExpr τ'
  let fn ← genExpr (.arrow τ' τ)
  pure (.app () fn arg)

/-- Generate a lambda abstraction whose binder has the type `τ₁`. -/
@[reducible] def genAbs [Gen G] (genBody : G LExpr') (τ₁ : LMonoTy) : G LExpr' := do
  let body ← genBody
  pure (.abs () "" (some τ₁) body)

/-- Generate an `if-then-else` expression. -/
@[reducible] def genIte [Gen G] (genCond genThen genElse : G LExpr') : G LExpr' := do
  let c ← genCond
  let t ← genThen
  let e ← genElse
  pure (.ite () c t e)

/-- Generate an equality test. The generator draws a random type, and it then generates two
    expressions of that type. -/
@[reducible] def genEq [Gen G] (genTy : G LMonoTy) (genExpr : LMonoTy → G LExpr') : G LExpr' := do
  let τ' ← genTy
  let e₁ ← genExpr τ'
  let e₂ ← genExpr τ'
  pure (.eq () e₁ e₂)

/-- Generate a quantifier expression, which is a `∀` or a `∃`.

    The generator draws a type for the binder and a type for the trigger. It then generates the term
    of the trigger and the term of the body, in the extended context. The trigger is a part of the
    `LExpr` syntax for SMT, and the generator itself makes no other use of it. -/
@[reducible] def genQuant [Gen G] (k : QuantifierKind) (genTy : G LMonoTy)
    (genTrigger : LMonoTy → LMonoTy → G LExpr') (genBody : LMonoTy → G LExpr') : G LExpr' := do
  let τ' ← genTy
  let τ_trigger ← genTy
  let trigger ← genTrigger τ' τ_trigger
  let body ← genBody τ'
  pure (.quant () k "" (some τ') trigger body)

/-- Each syntactic subtype of a type, which is each subterm of the type expression. -/
def syntacticSubtypes : LMonoTy → List LMonoTy
  | ty@(.tcons "arrow" [a, b]) => ty :: (syntacticSubtypes a ++ syntacticSubtypes b)
  | ty => [ty]

/-- One part of the computation of the generable types. The function applies this rule: if the set
    holds `σ → τ` and it also holds `σ`, then add `τ`. The fuel parameter makes the function
    terminate. -/
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

/-! ### The fast forms of the two helpers that have a quadratic cost

A generator calls `generableTypesFromCtx` at each node of each draw. With the 310 operators of
`Core.Factory`, this function is the largest cost in generation. Two linear scans, one inside the
other, are the reason:

- `List.eraseDups` over the list of subtypes, which has more than a thousand elements.
- The membership tests `argTy ∈ tys` and `retTy ∉ tys` in the loop of `addNewTypes`.

Each fast form below holds a `Std.HashSet` as an index for membership. `OpCtx` holds a hash map for a
lookup by type in the same way. Both functions keep their lists, and the dedup keeps the order of the
input.

The order is not necessary for the distribution. `elements` takes the result, draws a uniform index,
and gives that element. The list holds no duplicate element, because a dedup makes it. Therefore a
uniform index is a uniform element for each possible order, and the support is the same set.

The order gives one other property: the draws are a function of the seed only. `Std.HashSet` does not
specify its order, and that order can change with a new version of the toolchain, a new hash
function, or a different sequence of insertions.

A `@[csimp]` lemma connects each fast form to the original function. Therefore the compiler uses the
fast form, but `simp`, `rw` and `unfold` use the original definition. Each proof about `addNewTypes`
and `generableTypesFromCtx` therefore needs no change. -/

/-- A dedup that keeps the order. It keeps the first occurrence of each element, in the
    same way as `List.eraseDups`. The cost is linear and not quadratic. -/
def dedupTys (l : List LMonoTy) : List LMonoTy := go l ∅ []
where
  go : List LMonoTy → Std.HashSet LMonoTy → List LMonoTy → List LMonoTy
    | [], _, acc => acc.reverse
    | x :: rest, seen, acc =>
      if seen.contains x then go rest seen acc else go rest (seen.insert x) (x :: acc)

/-- The invariant of the accumulator: `seen` holds the elements of `acc` and no other
    element.

    The lemma applies to an arbitrary pair of `seen` and `acc`. This generality makes
    the induction step possible, because the recursive call gets the extended pair. -/
private theorem dedupTys_go_eq (l : List LMonoTy) (seen : Std.HashSet LMonoTy)
    (acc : List LMonoTy) (hinv : ∀ x, seen.contains x = true ↔ x ∈ acc) :
    dedupTys.go l seen acc = List.eraseDupsBy.loop (· == ·) l acc := by
  induction l generalizing seen acc with
  | nil => simp [dedupTys.go, List.eraseDupsBy.loop]
  | cons x rest ih =>
    rw [dedupTys.go, List.eraseDupsBy.loop]
    by_cases hx : seen.contains x = true
    · have : acc.any (x == ·) = true := by
        simp only [List.any_eq_true, beq_iff_eq]
        exact ⟨x, (hinv x).mp hx, rfl⟩
      simp only [hx, this, if_true]
      exact ih seen acc hinv
    · have hnot : acc.any (x == ·) = false := by
        simp only [Bool.eq_false_iff, ne_eq, List.any_eq_true, beq_iff_eq, not_exists]
        rintro y ⟨hy, rfl⟩
        exact hx ((hinv _).mpr hy)
      simp only [hx, hnot, Bool.false_eq_true, if_false]
      refine ih (seen.insert x) (x :: acc) ?_
      intro y
      rw [Std.HashSet.contains_insert]
      simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, hinv y]
      exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩

/-- `dedupTys` is equal to `List.eraseDups`, and the order is also equal.

    `csimp` accepts only the replacement of a complete constant, in the form
    `@f = @g`. `List.eraseDups` is polymorphic, but `dedupTys` applies only to
    `LMonoTy`, because it needs a `Hashable` instance. Therefore a `csimp` lemma
    cannot replace `List.eraseDups`. Instead, `generableTypesFromCtx` calls `dedupTys`,
    and the proofs rewrite with this lemma. -/
theorem dedupTys_eq (l : List LMonoTy) : dedupTys l = l.eraseDups := by
  rw [List.eraseDups, List.eraseDupsBy, dedupTys]
  exact dedupTys_go_eq l ∅ [] (by intro x; simp)

/-- `addNewTypes` with a `Std.HashSet` membership index beside `tys`. The two functions
    give the same list, element for element. -/
def fastAddNewTypes (fuel : Nat) (tys : List LMonoTy) : List LMonoTy :=
  go fuel tys (Std.HashSet.ofList tys)
where
  go : Nat → List LMonoTy → Std.HashSet LMonoTy → List LMonoTy
    | 0, tys, _ => tys
    | fuel + 1, tys, seen =>
      let newTys := tys.filterMap fun ty =>
        match ty with
        | .tcons "arrow" [argTy, retTy] =>
          if seen.contains argTy && !seen.contains retTy then some retTy else none
        | _ => none
      if newTys.isEmpty then tys
      else go fuel (tys ++ newTys) (newTys.foldl (·.insert ·) seen)

/-- A fold that inserts the elements of a list into a set adds those elements and no
    other element. -/
private theorem contains_foldl_insert (l : List LMonoTy) (s : Std.HashSet LMonoTy)
    (x : LMonoTy) :
    (l.foldl (·.insert ·) s).contains x = true ↔ (s.contains x = true ∨ x ∈ l) := by
  induction l generalizing s with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h

private theorem fastAddNewTypes_go_eq (fuel : Nat) (tys : List LMonoTy)
    (seen : Std.HashSet LMonoTy) (hinv : ∀ x, seen.contains x = true ↔ x ∈ tys) :
    fastAddNewTypes.go fuel tys seen = addNewTypes fuel tys := by
  induction fuel generalizing tys seen with
  | zero => simp [fastAddNewTypes.go, addNewTypes]
  | succ n ih =>
    rw [fastAddNewTypes.go]
    -- The two predicates of `filterMap` are equal at each type, because `seen` gives
    -- membership in `tys`.
    have hfun : (fun ty : LMonoTy =>
                  match ty with
                  | .tcons "arrow" [argTy, retTy] =>
                    if seen.contains argTy && !seen.contains retTy then some retTy else none
                  | _ => none)
              = (fun ty : LMonoTy =>
                  match ty with
                  | .tcons "arrow" [argTy, retTy] =>
                    if argTy ∈ tys && retTy ∉ tys then some retTy else none
                  | _ => none) := by
      funext ty
      split
      · rename_i a b
        rw [show seen.contains a = decide (a ∈ tys) by
              rw [Bool.eq_iff_iff, decide_eq_true_eq]; exact hinv a,
            show seen.contains b = decide (b ∈ tys) by
              rw [Bool.eq_iff_iff, decide_eq_true_eq]; exact hinv b]
        simp
      · rfl
    simp only [hfun]
    rw [addNewTypes]
    -- The two conditions are equal, and therefore one `split` gives both branches.
    split
    · rfl
    · refine ih _ _ ?_
      intro x
      rw [contains_foldl_insert, List.mem_append, hinv x]

@[csimp] theorem addNewTypes_eq_fast : addNewTypes = fastAddNewTypes := by
  funext fuel tys
  rw [fastAddNewTypes]
  exact (fastAddNewTypes_go_eq fuel tys _ (by intro x; simp)).symm

/-- The generable types, which are the types that the current context can generate. The definition
    follows Pałka et al. 2011.

    The function first computes the syntactic subtypes of each type in the context. It then adds a new
    type to the set by this rule: if the set holds `σ → τ` and it also holds `σ`, then add `τ`.

    The `@[csimp]` lemmas above apply to the dedup and to `addNewTypes`. Therefore the cost at run
    time is linear in the size of the context, and this definition stays the one that each proof
    uses. -/
def generableTypesFromCtx (bctx : BVarCtx) (fctx : FVarCtx) (octx : OpCtx) : List LMonoTy :=
  let allTys := bctx ++ fctx.map Prod.snd ++ octx.ops.map Prod.snd
  let initial := dedupTys (allTys.flatMap syntacticSubtypes)
  -- The fuel `initial.length` is an upper limit on the number of rounds.
  addNewTypes initial.length initial

/-- A decision procedure for the statement "`τ` is in the support of `genLMonoTy tvars n`".

    `genGenerableTy` uses this predicate to keep only the generable types that `genLMonoTy` can also
    give. Therefore the support of `genGenerableTy` is equal to the support of `genLMonoTy`.

    The predicate agrees with `monoTyDepth`: a bitvector of any width is generable, an arrow, a `Map`
    and a `Sequence` each take one unit of depth, and `tvars` must declare each `ftvar`. -/
def inGenLMonoTySupport (tvars : List TyIdentifier) : Nat → LMonoTy → Bool
  | _, .bitvec _ => true
  | _, .ftvar name => tvars.contains name
  | n + 1, .tcons "arrow" [a, b] =>
    inGenLMonoTySupport tvars n a && inGenLMonoTySupport tvars n b
  | n + 1, .tcons "Map" [a, b] =>
    inGenLMonoTySupport tvars n a && inGenLMonoTySupport tvars n b
  | n + 1, .tcons "Sequence" [a] => inGenLMonoTySupport tvars n a
  | _, .tcons name [] => nullaryBaseTypeNames.contains name
  | _, _ => false

/-- A type generator that reads the context. It is the source of the *argument* type for `genApp`,
    `genEq` and `genQuant`.

    Those three combinators draw a type `τ'` and then ask for a term of the type `τ'`. `genApp` also
    asks for a term of the type `τ' → τ`. A `τ'` that comes from `genLMonoTy`, which reads no context,
    is the largest cause of generation failure. `genLExprBase` can inhabit a compound type only when
    `bctx`, `fctx` or `octx` holds that exact type. A blind `τ'` is therefore usually not inhabitable,
    and the leaf goes to `default`. Each recursive step draws a new `τ'`, so the probability of failure
    grows quickly with the depth.

    This generator therefore draws mostly from `generableTypesFromCtx`, which gives the types that the
    leaf generator can truly inhabit.

    Two details keep the support equal to the support of `genLMonoTy`:

    1. `inGenLMonoTySupport tvars n` filters the list from the context. Therefore the list holds only
       a type that `genLMonoTy tvars n` can also give. A raw type from the context does not always
       satisfy that condition, because it can be too deep, or it can name an `ftvar` that `tvars` does
       not declare, or it can use a constructor that the type generator does not build. The soundness
       proofs need the drawn argument type to be generable at a depth that is not more than `n`.
    2. The `genLMonoTy` branch stays, with a positive weight. The support of `frequency` is the union
       of the supports of its branches that have a positive weight. Therefore the filtered branch adds
       nothing, and the support is exactly the support of `genLMonoTy`.

    The support is therefore the same, and each soundness proof and completeness proof still applies.
    Only the *distribution* moves onto the types that the leaf generator can inhabit. -/
def genGenerableTy [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat) : G LMonoTy :=
  let generable :=
    (generableTypesFromCtx bctx fctx octx).filter (inGenLMonoTySupport tvars n)
  if hg : generable.length > 0 then
    frequency
      [ (9, fun () => elements generable (List.ne_nil_of_length_pos hg)),
        (1, fun () => genLMonoTy tvars n) ]
      (by simp)
  else
    genLMonoTy tvars n

/-- The source of the argument type for `genApp`.

    `genApp` is more difficult than `genEq` and `genQuant`. After it draws an argument type `τ'`, it
    needs a term of the type `τ'` *and* a term of the type `τ' → τ`. A `τ'` from the generable set,
    which is what `genGenerableTy` gives, satisfies the first need only. The function position can then
    be the one that fails, because the generable set often holds `τ'` but not `τ' → τ`.

    This generator therefore works backwards. It looks for a generable type of the form `σ → τ`, which
    is a function that gives the target type `τ`, and it takes `σ` as the argument type. This is the
    rule of Pałka et al. that both positions must be satisfiable.

    As in `genGenerableTy`, the fallback branch stays with a positive weight. Therefore the support is
    still exactly the support of `genLMonoTy`, and each existing proof still applies. -/
def genAppArgTy [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) : G LMonoTy :=
  let generable := generableTypesFromCtx bctx fctx octx
  -- The argument type `σ` of each generable function type `σ → τ` that gives the target type.
  -- The `inGenLMonoTySupport` guard is a separate outer `filter`, and it is not a part of the
  -- `filterMap`. Therefore membership in the list gives the predicate at once, which is what the
  -- support proof needs.
  let argTys := (generable.filterMap (fun ty =>
    match ty with
    | .tcons "arrow" [σ, ret] => if ret == τ then some σ else none
    | _ => none)).filter (inGenLMonoTySupport tvars n)
  if hg : argTys.length > 0 then
    frequency
      [ (9, fun () => elements argTys (List.ne_nil_of_length_pos hg)),
        (1, fun () => genLMonoTy tvars n) ]
      (by simp)
  else
    genGenerableTy fctx octx tvars bctx n


-- ── Shared helpers ──────────────────────────────────────────────────

/-- Build an application that nests to the left, such as `app (app base a₁) a₂`. -/
def mkApps (base : LExpr') (args : List LExpr') : LExpr' :=
  args.foldl (fun acc arg => .app () acc arg) base

-- ── The helpers for the IndirPoly rule ──────────────────────────────

/-- A context of polymorphic operators. Each entry is a name and a polymorphic type scheme. -/
abbrev PolyOpCtx := List (String × Lambda.LTy)

open Lambda in
/-- Unify two monotypes with the constraint unification of Strata. The result is `some subst` on
    success, and `none` on failure. -/
def unifyTypes (t1 t2 : LMonoTy) : Option Lambda.Subst :=
  match Constraints.unify [(t1, t2)] .empty with
  | .ok si => some si.subst
  | .error _ => none

/-- Take an arrow type apart into the list of its argument types and its result type. -/
def decomposeArrow : LMonoTy → List LMonoTy × LMonoTy
  | .tcons "arrow" [σ, rest] =>
    let (args, ret) := decomposeArrow rest
    (σ :: args, ret)
  | ty => ([], ty)

/-- Build a `Lambda.Subst` of one scope from an association list of type-variable bindings.

    A `Lambda.Subst` is a stack of scopes, and each scope is a hash map. The function reverses the list
    before `HMap.ofList`, so that the *first* binding for a key wins. That is the convention of an
    association list. `HMap.ofList` alone lets the last binding win. -/
def substScope (bindings : List (TyIdentifier × LMonoTy)) : Lambda.Subst :=
  [Strata.Util.HMap.ofList bindings.reverse]

/-- The free type variables that a substitution does not instantiate. The result holds each element of
    `boundVars` that is not a key of `subst`. -/
def findFreeTyVars (boundVars : List TyIdentifier) (subst : Lambda.Subst) : List TyIdentifier :=
  boundVars.filter (fun v => Strata.Util.HMaps.find? subst v == none)

-- ── Alpha renaming for a polymorphic operator ───────────────────────
--
-- A bound type variable of a polymorphic factory function can have the same name as a free type
-- variable of the target type. An example is `id : ∀α. α → α` at the target `.ftvar "α"`. Without a
-- rename, the annotation on the `.op` node is then not a valid instance of the polymorphic type of
-- the function, and the term does not satisfy `OpsConsistent`. A rename of each bound type variable
-- before unification stops this problem.

/-- A supply of candidate names for a fresh type variable, which is `a`, `b` up to `z`, and then `a1`,
    `b1` and more names. `freshNameSupply n` gives a list of `n` or more different names. -/
def freshNameSupply (n : Nat) : List TyIdentifier :=
  -- A numeric suffix groups the names. The suffix `i` gives the whole alphabet with that suffix,
  -- which is 26 names. The suffix 0 is empty. Therefore `n / 26 + 1` suffixes give `n` or more
  -- names, and the caller then filters the list.
  let numSuffixes := n / 26 + 1
  -- suffixes are "", "1", "2", ...
  let suffixes := "" :: (fun i => toString (i + 1)) <$> (List.range numSuffixes)
  suffixes.flatMap (fun suffix =>
    (List.range 26).flatMap (fun c =>
      [String.append (Char.toString $ Char.ofNat (97 + c)) suffix]))

/-- Rename each bound variable whose name is also in `varsAlreadyInUse`. The result is the new list of
    names for the bound variables, together with the body of the monotype after the rename. -/
def freshenBoundVars (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (varsAlreadyInUse : List TyIdentifier) : List TyIdentifier × LMonoTy :=
  -- The conflicting type variables are the ones that appear in `varsAlreadyInUse`
  let conflictingTyVars := boundVars.filter (· ∈ varsAlreadyInUse)

  -- Aggregate all the type variables that are in use
  let allTypeVarsInUse := varsAlreadyInUse ++ conflictingTyVars

  -- The fresh names, which are the names outside the set of each name in use.
  let numFreshNames := allTypeVarsInUse.length + conflictingTyVars.length + 1
  let freshNames := (freshNameSupply numFreshNames).filter (· ∉ allTypeVarsInUse)

  -- Build a substitution from `conflictingTyVars` to `freshNames`
  let subst := conflictingTyVars.zip freshNames

  -- Apply the substitution to the bound variables
  -- A variable that the substitution does not map stays unchanged.
  let renamedBoundVars := (fun v => (subst.lookup v).getD v) <$> boundVars

  -- Apply the `subst` to `monoTy` (the body of the universally quantified type)
  -- using the substitution
  let renamedTy :=
    LMonoTy.subst (substScope (subst.map (fun (old, new) => (old, LMonoTy.ftvar new)))) monoTy

  -- Assemble everything together
  (renamedBoundVars, renamedTy)


/-- The concrete candidates that come from an instantiation of a polymorphic operator against the
    target type `τ`. Each candidate is a name together with the concrete types of the arguments that
    the term applies. The result therefore says which polymorphic factory functions can build a term of
    the type `τ`.

    The monomorphic `findOpsInCtx` looks at a full application only. This function looks at **each
    split point** `k` from 0 up to the arity. It applies the first `k` arguments, and it unifies the
    remaining arrow type with the target `τ`. Therefore one scheme can give more than one candidate,
    which is one candidate for each split point whose remaining type can equal `τ`. Two consequences
    follow:

    - The split point `k = 0` is included. A scheme such as `Sequence.empty : ∀a. seq a` is therefore
      reachable at the target `seq int`, and a partial application such as
      `Sequence.append s : seq int → seq int` is reachable at an arrow target.
    - The result gives the concrete types of exactly those `k` arguments. Therefore the annotation that
      `genIndirPoly` builds is the fully instantiated arrow type of the operator, and it is a true
      instance of its scheme.

    `generableTys` holds the types that the context can generate. `sampledTys` holds random types to
    instantiate a type variable with.

    `maxNumArgs` is an upper limit on the **arity** of the scheme of a polymorphic factory function.
    Its default value is 3. It limits the number of arguments that the scheme takes, and not the number
    that a candidate applies. -/
def findPolymorphicOps (pctx : PolyOpCtx) (τ : LMonoTy)
    (generableTys : List LMonoTy) (sampledTys : List LMonoTy) (maxNumArgs : Nat := 3)
    : List (String × List LMonoTy) :=

  -- Each type variable in the set of generable types.
  let tyVarsInGenerableSet := generableTys.flatMap LMonoTy.freeVars

  -- The type variables that are already in use. Such a variable occurs in the target type or in
  -- the set of generable types.
  let varsAlreadyInUse := (LMonoTy.freeVars τ ++ tyVarsInGenerableSet).eraseDups

  -- Look at each polymorphic factory function.
  pctx.flatMap fun (name, .forAll boundVars monoTy) =>

    -- Rename each bound type variable of the body away from the names that are in use. `monoTy` is
    -- the body, which is the `τ` in `∀ α. τ`.
    let (freshBoundVars, freshMonoTy) := freshenBoundVars boundVars monoTy varsAlreadyInUse

    -- The type of each of its arguments.
    let (argTys, retTy) := decomposeArrow freshMonoTy

    -- Skip a factory function whose arity is more than `maxNumArgs`.
    if argTys.length > maxNumArgs then []
    else
    -- Handle a partial application. For each `k` from 0 up to the arity, apply the first `k`
    -- arguments. The remaining arguments stay in the result type, which then unifies with `τ`.
    (List.range (argTys.length + 1)).filterMap fun k => do

      -- The term applies the first `k` argument types. For a partial application, the remaining
      -- argument types go into the result type.
      let appliedTys := argTys.take k
      let updatedRetTy := (argTys.drop k).foldr (fun σ acc => .arrow σ acc) retTy

      -- Unify the result type, after the rename, with the target type `τ`.
      let subst ← unifyTypes updatedRetTy τ

      -- The type variables that the substitution does not map.
      let uninstantiatedTyVars := findFreeTyVars freshBoundVars subst

      -- Each type variable must have an instance. If one does not, the context must be able to
      -- generate a random monotype for it.
      guard (uninstantiatedTyVars.isEmpty || !generableTys.isEmpty)

      -- Extend the substitution, so that it maps each remaining type variable to a sampled type.
      let extendedSubst : Lambda.Subst := substScope (uninstantiatedTyVars.zip sampledTys) ++ subst

      -- Apply the substitution to each applied argument type. Each such type is then concrete.
      let concreteAppliedTys := appliedTys.map (LMonoTy.subst extendedSubst)

      -- Keep this candidate only if `extendedSubst`, applied to the result type, gives the target
      -- type `τ`. This condition makes the generated term satisfy `OpsConsistent`, which is to say
      -- that the annotated type is a valid instance of the polymorphic type of the function.
      guard (LMonoTy.subst extendedSubst updatedRetTy == τ)

      pure (name, concreteAppliedTys)

-- ── Indir rule helpers ──────────────────────────────────────────────

/-- The argument types of a curried function type whose result type is `τ`. The result is
    `some args` when the type gives `τ`, and `none` when it does not. Three examples:
    - `argsForResult (.arrow .int (.arrow .int .int)) .int = some [.int, .int]`
    - `argsForResult (.arrow .int .bool) .int = none`
    - `argsForResult .int .int = some []` -/
def argsForResult (fullTy : LMonoTy) (τ : LMonoTy) : Option (List LMonoTy) :=
  match fullTy with
  | .tcons "arrow" [σ, rest] =>
    match argsForResult rest τ with
    | some args => some (σ :: args)
    | none => none
  | other => if other == τ then some [] else none

/-- Each operator of `octx` that gives the type `τ` after a full application, as a name together with
    its argument types. -/
def findOpsInCtx (octx : OpCtx) (τ : LMonoTy) : List (String × List LMonoTy) :=
  octx.ops.filterMap fun (name, ty) =>
    match argsForResult ty τ with
    | some (arg :: args) => some (name, arg :: args)
    | _ => none

-- ── The cores of the Indir and IndirPoly rules ──────────────────────
--
-- Both cores are *here*, before `genLExprBase`, because `genLExprBase` calls them. That call is what
-- makes a factory application reachable under an `ite` arm and under a binder body. Therefore neither
-- core can name `genLExprBase`, and each generator that a core needs is a parameter. Those
-- parameters are the argument generator `genArg`, and, for IndirPoly, the `fallback` for the case of
-- no polymorphic candidate. Each core is not recursive, so it has no obligation to terminate of its
-- own. The measure of the recursion belongs to the caller.
--
-- `genIndirPoly`, which is the wrapper that adds the depth-indexed defaults, is *after*
-- `genLExprBase`, further down this file.

/-- The **monomorphic Indir rule** of Pałka et al. 2011. The generator draws an operator of `octx`
    whose result type is `τ` after a full application. It then generates each argument at the argument
    type that the operator gives, so it guesses no type.

    The parameter `genArg` generates an argument. Therefore the caller owns the measure of the
    recursion, and this function is not recursive. The hypothesis `h` is a witness that at least one
    such operator exists. -/
def genIndir [Gen G] (octx : OpCtx) (τ : LMonoTy)
    (genArg : LMonoTy → G LExpr')
    (h : (findOpsInCtx octx τ).length > 0) : G LExpr' := do
  -- Each operator of the context that gives a term of the type `τ` after a full application.
  let ops := findOpsInCtx octx τ
  -- Draw one of these operators at random.
  let (name, argTys) ← elements ops (by apply List.ne_nil_of_length_pos; assumption)
  -- Build the `LExpr` for the operator.
  let fullArrowTy := argTys.foldr (fun σ acc => .arrow σ acc) τ
  let opExpr := .op () ⟨name, ()⟩ (some fullArrowTy)
  -- Generate a random term at each argument type, in order.
  let args ← List.mapM genArg argTys
  -- Apply the operator to each of the arguments.
  pure (mkApps opExpr args)

/-- Generate a well-typed `LExpr` of the type `τ` with the IndirPoly rule of Pałka et al. 2011,
    Section 4. The rule applies a polymorphic library function in three steps:
    1. It unifies the result type of the function with the target type `τ`.
    2. It samples a type from the set of generable types for each type variable that step 1 leaves
       open.
    3. It generates each argument at the concrete type that steps 1 and 2 give.

    The structure follows the monomorphic Indir rule: from a list of candidates, draw one, generate
    each argument with `genArg`, and assemble the term with `mkApps`.

    **The argument generator `genArg` and the fallback are both parameters.** This is the same open
    style of recursion as in `genApp`, `genIte` and `genEq`. It removes each mention of `genLExprBase`
    from this definition, and that is what lets `genLExprBase` call this function. `genIndirPoly` below
    gives a default value to each of the two parameters.

    This function takes **no `depth` parameter**, because only the argument generator and the fallback
    need a depth, and the caller gives both of them. -/
def genIndirPolyCore [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → G LExpr') (fallback : G LExpr')
    (maxNumArgs : Nat := 3) : G LExpr' := do
  -- The set of generable types of the current context.
  let generableTys := generableTypesFromCtx bctx fctx octx

  -- Sample a random type for each type variable that a candidate can leave open. When the context
  -- gives no generable type, draw a random base type with `pickBaseType`. A constant such as `.bool`
  -- would make each ground type except one unreachable for an empty context.
  let sampledTys ← List.replicate maxNumArgs ()
    |>.mapM (fun _ =>
      if hg : generableTys.length > 0 then do
        elements generableTys (by
          apply List.ne_nil_of_length_pos
          assumption)
      else pickBaseType)
  -- Each polymorphic library function that gives the target type `τ`.
  let ops := findPolymorphicOps pctx τ generableTys sampledTys maxNumArgs
  if h : ops.length > 0 then do
    -- Draw one of them at random, together with its argument types.
    let (functionName, argTys) ← elements ops (by
      apply List.ne_nil_of_length_pos
      assumption)

    -- Build the call to the factory function, with its fully instantiated type annotation. The
    -- annotated type holds no quantified type variable. It can hold a free type variable of the
    -- context.
    let fullArrowTy := argTys.foldr (fun σ acc => .arrow σ acc) τ
    let opExpr : LExpr' := .op () ⟨functionName, ()⟩ (some fullArrowTy)

    -- Generate a random term at each argument type.
    let args ← argTys.mapM genArg

    -- Apply the annotated factory function to each of the argument terms.
    pure (mkApps opExpr args)
  else
    -- There is no polymorphic candidate, so use the fallback of the caller.
    fallback

-- ── Expression generator ─────────────────────────────────────────────

/-- Generate a well-typed `LExpr` of the type `τ`. The first `Nat` argument is an upper limit on the
    depth of the term. At the depth 0, the generator gives a leaf only, which is a bound variable, a
    free variable, an operator or a constant. At the depth `n + 1`, it can give a compound expression
    whose subexpressions have the depth `n`.

    Each generated term satisfies `HasTypeA' bctx e τ`.

    ## The Indir and IndirPoly branches

    Each `n + 1` case holds a **monomorphic Indir** branch and a **polymorphic IndirPoly** branch, at
    the end of its `frequency` list. The branches are *here* and not only in `genLExpr`. Therefore a
    factory application, and in particular a polymorphic one, can appear at each position that this
    generator gives. Those positions include an `ite` arm, an `abs` body, a `quant` body, and the
    function and the argument of an application.

    Both branches draw each argument from `genLExprBase` at the *smaller* depth index `n`. Therefore
    this definition is **structurally recursive**, and it stays reducible. Many proofs unfold it with
    `simp only [genLExprBase]` or with `rw [genLExprBase]`, and they need that reducibility. A
    *mutual* recursion between this function and `genLExpr` would instead call `genLExprBase (n + 1)`
    from `genLExpr (n + 1)`, at an equal index. That form of recursion needs a lexicographic measure,
    it makes `genLExprBase` irreducible, and it then breaks each of those proofs.

    The cases at the depth 0 hold no Indir branch, because a full application at the depth floor
    leaves no budget for its arguments. -/
def genLExprBase [Gen G] (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier) (bctx : BVarCtx) : Nat → LMonoTy → G LExpr'
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
      (by simp)
  | n + 1, .arrow τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.arrow τ₁ τ₂)
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (4, fun () => genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.arrow τ₁ τ₂)) (genLExprBase fctx octx pctx tvars bctx n) (.arrow τ₁ τ₂)),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))
                              (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))),
        (2, fun () =>
          if hv : bvars.length > 0 then pickBVar bctx _ hv
          else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
        (2, fun () =>
          if hf : (fvarsOfType fctx (.arrow τ₁ τ₂)).length > 0
          then pickFVar fctx _ hf
          else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
        (2, fun () =>
          if ho : (opsOfType octx (.arrow τ₁ τ₂)).length > 0
          then pickOp octx _ ho
          else genAbs (genLExprBase fctx octx pctx tvars (τ₁ :: bctx) n τ₂) τ₁),
        -- The monomorphic Indir rule.
        (4, fun () =>
          if hi : (findOpsInCtx octx (.arrow τ₁ τ₂)).length > 0
          then genIndir octx (.arrow τ₁ τ₂) (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂)),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.arrow τ₁ τ₂)
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂))) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 4+1+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  | n + 1, .bool =>
    let bvars := bvarsOfType bctx .bool
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genBoolConst),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .bool) (genLExprBase fctx octx pctx tvars bctx n) .bool),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .bool)),
        (2, fun () => genEq (genGenerableTy fctx octx tvars bctx n) (genLExprBase fctx octx pctx tvars bctx n)),
        (2, fun () => genQuant .all (genGenerableTy fctx octx tvars bctx n)
          (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n)
          (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n .bool)),
        (2, fun () => genQuant .exist (genGenerableTy fctx octx tvars bctx n)
          (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n)
          (fun τ' => genLExprBase fctx octx pctx tvars (τ' :: bctx) n .bool)),
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
        (4, fun () =>
          if hi : (findOpsInCtx octx .bool).length > 0
          then genIndir octx .bool (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .bool),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx .bool
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n .bool)) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+1+2+2+2+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  | n + 1, .int =>
    let bvars := bvarsOfType bctx .int
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genIntConst),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .int) (genLExprBase fctx octx pctx tvars bctx n) .int),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .int)
                              (genLExprBase fctx octx pctx tvars bctx n .int)),
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
        (4, fun () =>
          if hi : (findOpsInCtx octx .int).length > 0
          then genIndir octx .int (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .int),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx .int
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n .int)) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+1+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  | n + 1, .ftvar name =>
    let bvars := bvarsOfType bctx (.ftvar name)
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.ftvar name)) (genLExprBase fctx octx pctx tvars bctx n) (.ftvar name)),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))
                              (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))),
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
        (4, fun () =>
          if hi : (findOpsInCtx octx (.ftvar name)).length > 0
          then genIndir octx (.ftvar name) (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n (.ftvar name)),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.ftvar name)
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n (.ftvar name))) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  | n + 1, .string =>
    let bvars := bvarsOfType bctx .string
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genStrConst),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .string) (genLExprBase fctx octx pctx tvars bctx n) .string),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .string)
                              (genLExprBase fctx octx pctx tvars bctx n .string)),
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
        (4, fun () =>
          if hi : (findOpsInCtx octx .string).length > 0
          then genIndir octx .string (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .string),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx .string
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n .string)) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+1+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  | n + 1, .real =>
    let bvars := bvarsOfType bctx .real
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genRealConst),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .real) (genLExprBase fctx octx pctx tvars bctx n) .real),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .real)
                              (genLExprBase fctx octx pctx tvars bctx n .real)),
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
        (4, fun () =>
          if hi : (findOpsInCtx octx .real).length > 0
          then genIndir octx .real (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .real),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx .real
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n .real)) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+1+2+2+2+2+4+4; omega
    frequency gs hw
  -- ── Bitvec type ───────────────────────────────────────────────────
  | 0, .bitvec n =>
    let bvars := bvarsOfType bctx (.bitvec n)
    oneOf
      [ (fun () => genBitvecConst n),
        (fun () =>
          if hv : bvars.length > 0 then pickBVar bctx (.bitvec n) hv
          else genBitvecConst n),
        (fun () =>
          if hf : (fvarsOfType fctx (.bitvec n)).length > 0
          then pickFVar fctx (.bitvec n) hf
          else genBitvecConst n),
        (fun () =>
          if ho : (opsOfType octx (.bitvec n)).length > 0
          then pickOp octx (.bitvec n) ho
          else genBitvecConst n) ]
      (by simp)
  | m + 1, .bitvec n =>
    let bvars := bvarsOfType bctx (.bitvec n)
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genBitvecConst n),
        (1, fun () => genApp (genAppArgTy fctx octx tvars bctx m (.bitvec n)) (genLExprBase fctx octx pctx tvars bctx m) (.bitvec n)),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx m .bool)
                              (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))
                              (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))),
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
          else genBitvecConst n),
        -- The monomorphic Indir rule.
        (4, fun () =>
          if hi : (findOpsInCtx octx (.bitvec n)).length > 0
          then genIndir octx (.bitvec n) (genLExprBase fctx octx pctx tvars bctx m) hi
          else genLExprBase fctx octx pctx tvars bctx m (.bitvec n)),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.bitvec n)
            (genLExprBase fctx octx pctx tvars bctx m)
            (genLExprBase fctx octx pctx tvars bctx m (.bitvec n))) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+1+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  | n + 1, .regex =>
    let bvars := bvarsOfType bctx .regex
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n .regex) (genLExprBase fctx octx pctx tvars bctx n) .regex),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n .regex)
                              (genLExprBase fctx octx pctx tvars bctx n .regex)),
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
        (4, fun () =>
          if hi : (findOpsInCtx octx .regex).length > 0
          then genIndir octx .regex (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .regex),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx .regex
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n .regex)) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  | n + 1, .map τ₁ τ₂ =>
    let bvars := bvarsOfType bctx (.map τ₁ τ₂)
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.map τ₁ τ₂)) (genLExprBase fctx octx pctx tvars bctx n) (.map τ₁ τ₂)),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))
                              (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))),
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
        (4, fun () =>
          if hi : (findOpsInCtx octx (.map τ₁ τ₂)).length > 0
          then genIndir octx (.map τ₁ τ₂) (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂)),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.map τ₁ τ₂)
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂))) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  | n + 1, .seq τ =>
    let bvars := bvarsOfType bctx (.seq τ)
    let gs : List (Nat × (Unit → G LExpr')) :=
      [ (1, fun () => genApp (genAppArgTy fctx octx tvars bctx n (.seq τ)) (genLExprBase fctx octx pctx tvars bctx n) (.seq τ)),
        (2, fun () => genIte (genLExprBase fctx octx pctx tvars bctx n .bool)
                              (genLExprBase fctx octx pctx tvars bctx n (.seq τ))
                              (genLExprBase fctx octx pctx tvars bctx n (.seq τ))),
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
        (4, fun () =>
          if hi : (findOpsInCtx octx (.seq τ)).length > 0
          then genIndir octx (.seq τ) (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n (.seq τ)),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.seq τ)
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n (.seq τ))) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+2+2+2+2+4+4; omega
    frequency gs hw
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
      (by simp)
  -- The same three leaves at depth `n + 1`, and also the monomorphic Indir branch
  -- and the polymorphic IndirPoly branch that each named arm has. Indir applies an
  -- operator whose result type is `τ`, and a constructor of the datatype is such an
  -- operator. IndirPoly applies a polymorphic operator at an instance that it
  -- samples, and a derived function of a polymorphic datatype is such an operator.
  -- The two branches put a compound term, such as `Cons(1, Nil)`, at the position of an argument. A variable
  -- and a constructor of arity 0 are the two other terms that can fill that position.
  | n + 1, τ =>
    let bvars := bvarsOfType bctx τ
    let gs : List (Nat × (Unit → G LExpr')) :=
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
        (4, fun () =>
          if hi : (findOpsInCtx octx τ).length > 0
          then genIndir octx τ (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n τ),
        -- The polymorphic IndirPoly rule.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx τ
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n τ)) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 2+2+2+4+4; omega
    frequency gs hw


/-- The depth-indexed IndirPoly rule, which is `genIndirPolyCore` with a default value for each of its
    two generator parameters.

    The default value of `genArg` is `genLExprBase … depth`, and the default fallback is
    `genLExprBase … depth τ`. `genLExpr` replaces `genArg` with itself at the smaller depth index, and
    that is what makes a factory application nest in *argument* position.

    The rule itself is in `genIndirPolyCore`, which comes before `genLExprBase`, because
    `genLExprBase` calls it. This wrapper holds only the defaults that name `genLExprBase`, and it must
    therefore come after it. -/
def genIndirPoly [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat := 3)
    (genArg : LMonoTy → G LExpr' := genLExprBase fctx octx pctx tvars bctx depth)
    : G LExpr' :=
  genIndirPolyCore fctx octx pctx bctx τ genArg
    (genLExprBase fctx octx pctx tvars bctx depth τ) maxNumArgs

/-- Generate a well-typed `LExpr` of the type `τ` with the Indir rule of Pałka et al. 2011, together
    with the standard generation rules.

    When an operator of `octx` gives the type `τ` after a full application, the generator draws between
    two groups of rules:
    - The **Indir rule**: draw such an operator, and generate each of its arguments at the type that
      the operator gives. The rule guesses no type.
    - The **standard rules** of `genLExprBase`: a variable, a constant, an application at a random
      type, a lambda, an `if-then-else`, and more.

    The result holds many more fully applied operators, such as `Int.Add #1 #2`, than the application
    rule alone gives with its random type.

    **A factory application nests.** At the depth `n + 1`, each argument of an Indir application or an
    IndirPoly application comes from `genLExpr` *itself*, at the smaller index `n`. Therefore a factory
    call can be the argument of another factory call, as in
    `Int.Add (Int.SafeDiv #0 #-2) (Int.SafeDiv #0 #0)`. At the depth floor, each argument comes from
    `genLExprBase` at the depth 0, and it is therefore a leaf.

    The recursion is **structural**. Each recursive occurrence is at `n` under the pattern `n + 1`.
    `genIndir` and `genIndirPoly` are separate functions that are not recursive, and each of them takes
    the recursive call as its `genArg` parameter. A recursive call that goes to a higher-order helper in
    this way keeps the recursion structural, so this definition needs no `termination_by` and no
    `decreasing_by`. It also leaves `genLExprBase` alone, and `genLExprBase` keeps its own structural
    recursion. A *mutual* recursion between the two would instead need a lexicographic measure, it
    would make `genLExprBase` irreducible, and it would break each proof that unfolds `genLExprBase`
    by `rfl`.

    ## What this function adds

    `genLExprBase` holds the two Indir rules in each of its own `frequency` lists. Therefore a factory
    application, and a polymorphic one too, is reachable at each position of a subterm.

    The contribution of this function is the **distribution at the root**. It weights the base rules
    against the two Indir rules by 1 to 9, and the merged lists in `genLExprBase` weight them about
    equally. This function also owns `retryCont`.

    ## The `retryCont` parameter

    `retryCont` is a **continuation that retries generation after a failure**. It takes the argument
    generator that this function uses in the argument position of the two Indir rules, and it gives the
    generator to use in place of it. A caller can therefore say "draw this subterm again with new
    randomness after a failure", and this module needs no definition of a failure.

    The parameter must be a transformer of a generator, and not a plain generator. At the depth
    `n + 1` the argument generator must be *this generator at `n`*. A fixed value of the type
    `LMonoTy → G LExpr'` would therefore pin the caller to one depth. `retryCont` instead goes through
    the recursion, so it applies at **each** level. That is the point, because the probability of a
    failure grows quickly with the depth of the nesting, and a caller cannot otherwise reach a nested
    level.

    At the depth `n + 1`, `retryCont` wraps the *whole* generator of the level `n`. That includes the
    instantiation of a type variable inside `genIndirPoly`. Therefore a continuation that retries also
    samples a new instantiation at each nested level, and neither `genIndir` nor `genIndirPoly` needs a
    change.

    A retry has an effect under `Plausible.Gen` only, where a failed leaf throws. Under `SetGen.Set`,
    which is the semantics of the soundness and completeness theorems, `default` is `∅` and not an
    error. There is therefore no failure to observe and nothing to retry. The abstract `Gen` class
    gives no `tryCatch` and no `Alternative`, and that is why the caller supplies this continuation.

    The default value is `id`, which retries nothing. The parameter is **last**, after the optional
    parameter `maxNumArgs`, so each positional call site elaborates as before. The order matters,
    because `retryCont` in an earlier position would silently take a positional argument. The theorems
    about this generator describe the case `retryCont = id`, which is the honest scope. A retry changes
    the number of attempts that a draw needs, and not the set of reachable terms. -/
def genLExpr [Gen G] (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat := 3)
    (retryCont : (LMonoTy → G LExpr') → (LMonoTy → G LExpr') := id) : G LExpr' :=
  -- The argument generator for the two Indir rules. At the depth floor it is the base generator,
  -- which gives a leaf. Above the floor it is `genLExpr` itself at the smaller index `n`, and that
  -- is what lets a factory application nest. The recursion is structural on `depth`.
  --
  -- `retryCont` is the retry continuation of the caller. It wraps the generator in the argument
  -- position, and it goes into the recursive call, so it applies at each level.
  let genArg : LMonoTy → G LExpr' :=
    retryCont <|
      match depth with
      | 0 => genLExprBase fctx octx pctx tvars bctx 0
      | n + 1 => fun σ => genLExpr fctx octx pctx tvars bctx n σ maxNumArgs retryCont
  if h : (findOpsInCtx octx τ).length > 0 then
    frequency
      [ (1, fun () => genLExprBase fctx octx pctx tvars bctx depth τ),
        (9, fun () =>
        pick
          (fun () =>
            -- The monomorphic Indir rule.
            genIndir octx τ genArg h)
          (fun () =>
            -- The polymorphic IndirPoly rule.
            genIndirPoly fctx octx pctx tvars bctx depth τ maxNumArgs genArg)) ]
      (by simp)
  else
    -- There is no monomorphic candidate, so try IndirPoly or the base generator.
    pick
      (fun () => genLExprBase fctx octx pctx tvars bctx depth τ)
      (fun () => genIndirPoly fctx octx pctx tvars bctx depth τ maxNumArgs genArg)

-- ── Top-level generators ─────────────────────────────────────────────

/-- Generate a well-typed closed expression of a bounded depth. Such an expression holds no free
    variable and no operator. -/
def genClosedLExpr [Gen G] (tvars : List TyIdentifier) (depth : Nat)
    (maxNumArgs : Nat := 3) : G LExpr' := do
  let τ ← genLMonoTy tvars depth
  genLExpr [] ∅ [] tvars [] depth τ maxNumArgs

/-! ## The operator contexts of Strata Core

The two definitions below give the monomorphic operators and the polymorphic operators of
`Core.Factory`. They are here, and not in `TestSupport`, so that a *generator* can also start from a
realistic set of operators. `ProgramGen` uses them for the body of an axiom, a function and a
procedure. `TestSupport` exports them again for the property suites. -/

/-- Each monomorphic operator of `Core.Factory`, as a name and a curried type. The Indir generation
    rule uses this context.

    The definition derives the list from the factory itself. Therefore the vocabulary here cannot differ
    from the operators that Core defines. A list that a person writes by hand can differ from the
    factory, and it then hides each operator that it does not name. A generator over such a list cannot
    build a term such as `Str.Length "é"`, and a property about that operator then says nothing.

    The body repeats the body of `factoryOps` and does not call it, because `factoryOps` is in
    `HasTypeAGen/Defs.lean`, and that file imports this one. The two must stay the same, and a theorem
    in `Defs.lean` proves that they are. Therefore a change to one of them alone breaks the build. -/
def coreMonoOps : OpCtx :=
  OpCtx.ofList <| Core.Factory.toArray.toList.filterMap fun f =>
    some (f.name.name, LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))

/-- Each **polymorphic** operator of `Core.Factory`, as a name and its full type scheme. The IndirPoly
    generation rule uses this context.

    The definition derives the list from the factory, for the same reason as `coreMonoOps`. A list that
    a person writes by hand can differ from the factory in three ways. It can omit an operator, and no
    generated term can then apply that operator. It can name an operator that the factory does not
    define, and a draw of that operator then gives a term that Core cannot interpret. It can also give
    an operator the wrong arity, and the annotation on the generated term then disagrees with the
    factory.

    A monomorphic entry of the factory is excluded, which is the condition `typeArgs ≠ []`.
    `coreMonoOps` already covers such an entry through the Indir rule, and a second copy here would only
    repeat that work at each draw.

    The body repeats the body of `factoryPolyOps`, for the polymorphic entries, and does not call it,
    because `factoryPolyOps` is in `HasTypeAGen/Defs.lean`, and that file imports this one. A theorem in
    `Defs.lean` proves that the two agree, so a change to one of them alone breaks the build. -/
def corePolyOps : PolyOpCtx :=
  Core.Factory.toArray.toList.filterMap fun f =>
    if f.typeArgs.isEmpty then none
    else some (f.name.name,
      Lambda.LTy.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))
