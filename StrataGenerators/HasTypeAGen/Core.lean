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

/-- A `Nat` generator, defined locally rather than imported from
    `BasaltExamples.ArbNat`. The upstream `non_empty_combinators` reorg dropped the
    lightweight `ArbNat.Def` split, so `BasaltExamples.ArbNat` now imports the
    full `Basalt` umbrella — which transitively pulls in Mathlib's `List.dedup`
    and collides with Strata's `List.dedup` (from `Strata.DL.Util.List`, imported
    via `Strata.DL.Lambda.*`). This file is deliberately kept Mathlib-free, so we
    inline the definition. It is definitionally identical to the upstream one
    (`pick 0 / (·+1)`), so the support proofs in `HasTypeAGen.lean` that unfold
    `Nat.arbitrary` are unaffected. -/
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

    A generator looks for an operator by type one time at each candidate leaf. The
    context holds each function of `Core.Factory`, which is 310 entries. The index
    makes each lookup one hash instead of a linear scan. The index is also small,
    because the 310 entries have only 81 different curried types. In compiled code,
    one lookup takes 0.005 ms with the index and 0.103 ms with a scan.

    The index does not make the whole generator faster, because a lookup is not the
    largest cost. `generableTypesFromCtx` costs about 0.092 ms for each call, and a
    generator calls it at each node.

    The `agrees` field connects the index to the scan that specifies it. Therefore the
    index cannot disagree with `ops`. `Lambda.Factory`
    (`Strata/DL/Lambda/Factory.lean`) uses the same pattern: it holds `toArray` with
    `nameMap : Std.HashMap String Nat` and three invariants between them. The key here
    is the curried type, because a generator looks for an operator by type. Strata
    looks for an operator by name, and therefore Strata needs no index by type.

    `OpCtx` holds the index. A separate `OpIndex` structure beside `OpCtx` is also
    possible, but then `opsOfType`, `pickOp` and each lemma about them need a new
    signature. With the index inside `OpCtx`, these signatures do not change, and the
    proofs that use an operator context stay the same. -/
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
abbrev LMonoTy.regex : LMonoTy := .tcons "regex" []

/-- The Map monotype with key type `k` and value type `v`. -/
abbrev LMonoTy.map (k v : LMonoTy) : LMonoTy := .tcons "Map" [k, v]

/-- The Sequence monotype with element type `a`. -/
abbrev LMonoTy.seq (a : LMonoTy) : LMonoTy := .tcons "Sequence" [a]

end Lambda

-- ── SimpleType and depth ─────────────────────────────────────────────

/-- A monotype is *simple* if it is built from `bool`, `int`, `string`, `real`,
    `bitvec n` (for *any* width `n`), `arrow`, and `ftvar`.
    This characterizes exactly the types produced by `genLMonoTy`.

    Bitvector widths are unconstrained: the Strata Core AST does not restrict
    them, so `genLMonoTy` may produce a `bitvec` of any width. -/
inductive SimpleType : LMonoTy → Prop where
  | bool   : SimpleType .bool
  | int    : SimpleType .int
  | string : SimpleType .string
  | real   : SimpleType .real
  | regex  : SimpleType .regex
  | bitvec : SimpleType (.bitvec n)
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

/-- Pick a uniformly random operator of type `τ` from `octx`. -/
def pickOp [Gen G] (octx : OpCtx) (τ : LMonoTy)
    (h : (opsOfType octx τ).length > 0) : G LExpr' :=
  have hne : (opsOfType octx τ).map (fun name => LExpr.op () ⟨name, ()⟩ (some τ)) ≠ [] := by
    simp [List.map_eq_nil_iff]
    exact List.length_pos_iff.mp h
  elements _ hne

-- ── Type generator ───────────────────────────────────────────────────

/-- Pick a uniformly random type variable name from `tvars` and return it
    as an `LMonoTy.ftvar`. -/
def pickTyVar [Gen G] (tvars : List TyIdentifier)
    (h : tvars.length > 0) : G LMonoTy :=
  have hne : tvars ≠ [] := List.length_pos_iff.mp h
  LMonoTy.ftvar <$> elements tvars hne

/-- Pick a random bitvector width and return it as an `LMonoTy.bitvec`. The
    width is drawn from `Nat.arbitrary` (any natural), since the Strata Core AST
    does not constrain bitvector widths. -/
def pickBitvecWidth [Gen G] : G LMonoTy :=
  LMonoTy.bitvec <$> Nat.arbitrary

/-- The names of the nullary (arity-0) base type constructors Strata Core knows:
    `bool`, `int`, `string`, `real`, `regex`. These are the ground type names
    `pickBaseType` produces (as `.tcons name []`), the ones `inGenLMonoTySupport`
    recognizes, and the shared base-type pool the datatype generator draws from
    (`DatatypeGen.defaultBaseTypes`). Bitvectors are handled separately by
    `pickBitvecWidth`, since their width is a parameter rather than a name. -/
def nullaryBaseTypeNames : List String :=
  ["bool", "int", "string", "real", "regex"]

/-- Pick a uniformly random base type (bool, int, string, real, regex, or bitvec). -/
def pickBaseType [Gen G] : G LMonoTy :=
  oneOf
    [ (fun () => pure .bool),
      (fun () => pure .int),
      (fun () => pure .string),
      (fun () => pure .real),
      (fun () => pure .regex),
      (fun () => pickBitvecWidth) ]
    (by simp)

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

/-- The character-list backing of `String.arbitrary`. Upstream Basalt dropped
    `genCharList` and now defines `String.arbitrary := String.ofList <$> listOf
    Char.arbitrary`, so this is `listOf Char.arbitrary`. -/
abbrev genAlphanumList [Gen G] : G (List Char) := listOf Char.arbitrary

/-- Generate a random string constant.

    The generator draws from `genInterestingString`
    (`StrataGenerators.PrimitiveGens`), and not from `String.arbitrary` of Basalt.
    `String.arbitrary` gives only characters that satisfy `Char.isAlphanum`, and
    therefore it never goes outside printable ASCII. The non-ASCII pool is what
    makes the agreement property between SMT and concrete evaluation non-vacuous
    at type `string`. An ASCII-only pool cannot reach the defect in the SMT-LIB
    escape function.

    The code depends on the `do let s ← _; pure (.strConst () s)` shape. The support
    proofs in `HasTypeAGen.lean` and `HasTypeAGenOpsConsistent.lean` destructure
    it as one `bind` and then one `pure`, and they discard the inner membership
    hypothesis. Thus they do not depend on *which* string generator supplies the
    value, but they do depend on the shape. -/
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

/-- Collects all syntactic sub-types (i.e. sub-terms of a type expression) that appear in a type -/
def syntacticSubtypes : LMonoTy → List LMonoTy
  | ty@(.tcons "arrow" [a, b]) => ty :: (syntacticSubtypes a ++ syntacticSubtypes b)
  | ty => [ty]

/-- Helper function used when building the set of generable types.
    Implements this rule: if `σ → τ` and `σ` are both in the set, then `τ` is added.
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

/-! ### Fast forms of the two helpers with a quadratic cost

A generator calls `generableTypesFromCtx` at each node of each draw. With the 310
operators of `Core.Factory`, this function is the largest cost in generation. Two
linear scans, one inside the other, are the reason:

- `List.eraseDups` over the subtype list, which has 1404 elements.
- The membership tests `argTy ∈ tys` and `retTy ∉ tys` in the loop of `addNewTypes`.

The fast forms below give 0.092 ms for each call to `generableTypesFromCtx`. They give
44 ms for 300 draws at depth 2. They give 4.9 s for the LSpec suite at `100 5`. A context of 40
operators needs 12 ms for the same 300 draws. The difference is proportional to the
number of operators, because the subtype list gets larger with the context.

Each fast form holds a `Std.HashSet` as a membership index. `OpCtx` holds a hash map
for a lookup by type in the same way. The two functions keep their lists, and the
dedup keeps the order of the input.

The order is not necessary for the distribution. `elements` gets the result, draws a
uniform index, and returns that element. The list has no duplicate elements, because a
dedup makes it. Therefore a uniform index is a uniform element for each possible order,
and the support is the same set. A list from `Std.HashSet.toList` gives the same
distribution and the same speed. The measurements are 2.43 ms and 2.47 ms for each
call.

The order gives one other property: the draws are a function of the seed only.
`Std.HashSet` does not specify its order. The order can change with a new version of
the toolchain, a new hash function, or a different sequence of insertions. This
property is useful if the suite has a seed. The suite has no seed now. This is also why
two of its properties give different results in different runs.

A `@[csimp]` lemma connects each fast form to the original function. Therefore the
compiler uses the fast form, but `simp`, `rw` and `unfold` use the original definition.
Each proof about `addNewTypes` and `generableTypesFromCtx` stays the same. These proofs
include `addNewTypes_simple` and `generableTypesFromCtx_simple` in `HasTypeAGen.lean`.
The fast forms add no `sorry` and no axiom. -/

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

/-- Compute the set of "generable types" (i.e. types that can be generated from the
  current context), following Palka et al. 2011.

  We begin by computing the syntactic sub-types for each types in the context,
  then add new types to the set according to the following rule:
  if (σ → τ) and σ are both in the set, then τ is too.

  The `@[csimp]` lemmas above apply to the dedup and to `addNewTypes`. Therefore the
  cost is linear in the size of the context at run time, and this definition stays the
  one that each proof uses. -/
def generableTypesFromCtx (bctx : BVarCtx) (fctx : FVarCtx) (octx : OpCtx) : List LMonoTy :=
  let allTys := bctx ++ fctx.map Prod.snd ++ octx.ops.map Prod.snd
  let initial := dedupTys (allTys.flatMap syntacticSubtypes)
  -- The fuel `initial.length` is an upper limit on the number of rounds.
  addNewTypes initial.length initial

/-- Boolean decision procedure for "`τ` is in the support of `genLMonoTy tvars n`",
    i.e. for `SimpleType τ ∧ monoTyDepth τ ≤ n ∧ allFtvarsIn tvars τ`
    (see `genLMonoTy_support`). Used to filter the context-derived generable types
    down to those `genLMonoTy` could itself have produced, which is what makes
    `genGenerableTy`'s support *equal* to `genLMonoTy`'s — see
    `genGenerableTy_support`. Kept in lockstep with `SimpleType`/`monoTyDepth`:
    a `bitvec` of any width is generable, `arrow`/`Map`/`Sequence` consume
    one unit of depth, and every `ftvar` must be declared in `tvars`. -/
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

/-- Context-aware type generator: the type source used for the *argument* type of
    `genApp`, `genEq`, and `genQuant`.

    Those three combinators pick a type `τ'` and then demand a term of type `τ'`
    (and, for `genApp`, of type `τ' → τ`). Drawing `τ'` from the context-blind
    `genLMonoTy` is the dominant cause of generation failure: `genLExprBase` can
    only inhabit a compound type when *something in `bctx`/`fctx`/`octx` has that
    exact type*, so a blindly-chosen `τ'` is usually uninhabitable and the leaf
    falls through to `default` (i.e. throws `inhabitedWitness`). Because each
    recursive step re-draws a fresh `τ'`, the failure probability compounds with
    depth — the superlinear blowup.

    So we draw mostly from `generableTypesFromCtx` (Pałka et al. 2011: the types
    reachable from the context by closing `σ → τ` and `σ` ⊢ `τ`), which are
    exactly the types the leaf generator can actually inhabit.

    Two details make this a drop-in replacement for `genLMonoTy` in the proofs:

    1. The context-derived list is filtered by `inGenLMonoTySupport tvars n`, so it only
       ever contains types `genLMonoTy tvars n` could itself have produced. A raw
       context type need not be one (it can be too deep, mention an undeclared
       `ftvar`, or use a non-simple constructor), and the soundness proofs rely on
       the drawn argument type being `SimpleType` of depth ≤ `n`.
    2. The `genLMonoTy` branch is *retained* with positive weight. Since
       `frequency`'s support is the union of its positive-weight branches'
       supports (`mem_support_frequency_iff`), the filtered branch contributes
       nothing new and the support is exactly `genLMonoTy`'s — see
       `genGenerableTy_support`.

    So support is unchanged (every existing soundness/completeness proof still
    applies verbatim, via that one rewrite) while the *distribution* shifts
    decisively onto types the leaf generator can actually inhabit. This is the
    reweighting-free part of the fix: it changes which types are likely, not
    which are possible. -/
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

/-- The argument-type source for `genApp` specifically.

    `genApp` is harder than `genEq`/`genQuant`: having drawn an argument type `τ'`
    it needs terms of type `τ'` *and* of type `τ' → τ`. Drawing `τ'` from the
    generable set (as `genGenerableTy` does) only ensures the former — measured
    against `coreMonoOps`, the function type `τ' → bool` was absent from the
    generable set for 11 of the 16 generable `τ'`, so the *function* position was
    then the one that failed.

    So instead of choosing `τ'` and hoping `τ' → τ` is inhabited, we work
    backwards: look for generable types of the form `σ → τ` (i.e. functions that
    actually *return* the target type `τ`) and take `σ` as the argument type. This
    is the Pałka et al. rule that both positions be satisfiable.

    As with `genGenerableTy`, the fallback branch is retained with positive weight,
    so the support is still exactly `genLMonoTy`'s (see `genAppArgTy_support`) and
    the existing proofs continue to apply. -/
def genAppArgTy [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (n : Nat) (τ : LMonoTy) : G LMonoTy :=
  let generable := generableTypesFromCtx bctx fctx octx
  -- Argument types `σ` of generable function types `σ → τ` returning the target.
  -- The `inGenLMonoTySupport` guard is a separate outer `filter` (rather than folded
  -- into the `filterMap`) so that membership immediately yields the predicate,
  -- which is what `genAppArgTy_support` needs.
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

/-- Build a left-nested application: `foldl app base [a₁, a₂, ...] = app (app base a₁) a₂ ...` -/
def mkApps (base : LExpr') (args : List LExpr') : LExpr' :=
  args.foldl (fun acc arg => .app () acc arg) base

-- ── IndirPoly rule helpers ──────────────────────────────────────────

/-- A polymorphic operator context entry: a name paired with a polymorphic type
    scheme (`LTy`). -/
abbrev PolyOpCtx := List (String × Lambda.LTy)

open Lambda in
/-- Unify two monotypes using Strata's constraint unification.
    Returns `none` on failure, or `some subst` on success. -/
def unifyTypes (t1 t2 : LMonoTy) : Option Lambda.Subst :=
  match Constraints.unify [(t1, t2)] .empty with
  | .ok si => some si.subst
  | .error _ => none

/-- Decomposes an arrow type into a pair consisting of (list of argument types, return type)-/
def decomposeArrow : LMonoTy → List LMonoTy × LMonoTy
  | .tcons "arrow" [σ, rest] =>
    let (args, ret) := decomposeArrow rest
    (σ :: args, ret)
  | ty => ([], ty)

/-- Build a single-scope `Lambda.Subst` from an association list of type-variable
    bindings.

    `Lambda.Subst` is a stack of scopes; upstream made each scope an opaque
    hash map (`Strata.Util.HMap`) rather than an association list, so a scope can
    no longer be written as a list literal. Reversing before `HMap.ofList`
    preserves the association-list convention that the *first* binding for a key
    wins (`HMap.ofList` would otherwise let the last one win). -/
def substScope (bindings : List (TyIdentifier × LMonoTy)) : Lambda.Subst :=
  [Strata.Util.HMap.ofList bindings.reverse]

/-- Find free type variables that haven't been instantiated in a substituion,
    i.e. `findFreeTyVars boundVars subst` elements of `boundVars` that don't appear as keys in `subst`. -/
def findFreeTyVars (boundVars : List TyIdentifier) (subst : Lambda.Subst) : List TyIdentifier :=
  boundVars.filter (fun v => Strata.Util.HMaps.find? subst v == none)

-- ── Alpha-renaming for polymorphic operators (OpsConsistent fix) ──────
-- Without freshening type variables, a polymorphic factory
-- function whose type variables shares a name with a free type variable of
-- the target type (e.g. `id : ∀α. α → α` at target `.ftvar "α"`) would result in an `.op`
-- annotation that is *not* a valid type instantiation of the factory function's polymorphic
-- type, violating `OpsConsistent`. Freshening bound type variables before unification prevents this problem.

/-- A supply of candidate fresh type-variable names: `a, b, …, z, a1, b1, c1, …` —
    `freshNameSupply n` returns a list containing at least `n` distinct names. -/
def freshNameSupply (n : Nat) : List TyIdentifier :=
  -- Names are grouped by numeric suffix: suffix `i` contributes the whole
  -- alphabet `a…z` tagged with `i` (suffix 0 is untagged), giving 26 names per
  -- suffix — `a b … z, a1 b1 … z1, a2 …`. Using `minCount / 26 + 1` suffixes
  -- yields at least `minCount` names (the caller filters/truncates from there).
  let numSuffixes := n / 26 + 1
  -- suffixes are "", "1", "2", ...
  let suffixes := "" :: (fun i => toString (i + 1)) <$> (List.range numSuffixes)
  suffixes.flatMap (fun suffix =>
    (List.range 26).flatMap (fun c =>
      [String.append (Char.toString $ Char.ofNat (97 + c)) suffix]))

/-- Alpha-rename bound variables that collide with `varsAlreadyInUse`.
    Returns `(freshened bound var names, freshened monotype body)`. Bound

    See comments in function body for more details. -/
def freshenBoundVars (boundVars : List TyIdentifier) (monoTy : LMonoTy)
    (varsAlreadyInUse : List TyIdentifier) : List TyIdentifier × LMonoTy :=
  -- The conflicting type variables are the ones that appear in `varsAlreadyInUse`
  let conflictingTyVars := boundVars.filter (· ∈ varsAlreadyInUse)

  -- Aggregate all the type variables that are in use
  let allTypeVarsInUse := varsAlreadyInUse ++ conflictingTyVars

  -- Obtain fresh names (names that aren't in the set of all used names)
  let numFreshNames := allTypeVarsInUse.length + conflictingTyVars.length + 1
  let freshNames := (freshNameSupply numFreshNames).filter (· ∉ allTypeVarsInUse)

  -- Build a substitution from `conflictingTyVars` to `freshNames`
  let subst := conflictingTyVars.zip freshNames

  -- Apply the substitution to the bound variables
  -- (any variables which aren't mapped by `subst` are left unchanged)
  let renamedBoundVars := (fun v => (subst.lookup v).getD v) <$> boundVars

  -- Apply the `subst` to `monoTy` (the body of the universally quantified type)
  -- using the substitution
  let renamedTy :=
    LMonoTy.subst (substScope (subst.map (fun (old, new) => (old, LMonoTy.ftvar new)))) monoTy

  -- Assemble everything together
  (renamedBoundVars, renamedTy)


/-- Collect the concrete (name, appliedArgTys) pairs that result from instantiating
    polymorphic operators against the target type `τ`. This function
    determines which polymorphic factory functions can be invoked
    if we want to generate a term of type `τ`.

    Unlike the monomorphic `findOpsInCtx`, a polymorphic operator is considered at
    **every split point** `k ∈ [0, arity]`: we apply only the first `k` arguments
    and leave the suffix `σ_{k+1} → … → σₙ → retTy` to unify with the target `τ`.
    This means a single scheme may yield several candidates — one per split point at
    which its instantiated suffix can equal `τ`. In particular:
    - `k = 0` (the nullary/partial case) is included, so a scheme like
      `Sequence.empty : ∀a. seq a` is reachable at `seq int` and a partially-applied
      `Sequence.append s : seq int → seq int` is reachable at an arrow target.
    - the returned `appliedArgTys` are the concrete types of exactly those `k`
      arguments, so `genIndirPoly`'s annotation `appliedArgTys.foldr arrow τ` is the
      operator's fully-instantiated arrow type (a genuine instance of its scheme).

    The argument `generableTys` is a collection of types that are generable given the
    context, while `sampledTys` contains a list of random types with which to
    instantiate type variables.

    The argument `maxNumArgs` is an upper bound on the **arity** of a polymorphic
    factory function's scheme (by default, this is 3); it bounds the number of
    arguments the scheme takes, not the number applied at a candidate split point. -/
def findPolymorphicOps (pctx : PolyOpCtx) (τ : LMonoTy)
    (generableTys : List LMonoTy) (sampledTys : List LMonoTy) (maxNumArgs : Nat := 3)
    : List (String × List LMonoTy) :=

  -- Collect all type variables in the set of generable types
  let tyVarsInGenerableSet := generableTys.flatMap LMonoTy.freeVars

  -- Determine the set of type variables which are already "in use",
  -- i.e. mentioned either in the result type (the target type we're generating for)
  -- or in `tyVarsInGenerableSet`
  let varsAlreadyInUse := (LMonoTy.freeVars τ ++ tyVarsInGenerableSet).eraseDups

  -- For each polymorphic factory function:
  pctx.flatMap fun (name, .forAll boundVars monoTy) =>

    -- Alpha-rename bound type variables in `monoTy` (the body of the quantified type expression,
    -- i.e. the `τ` in `∀ α. τ`) away from `varsAlreadyInUse` to avoid naming collisions
    let (freshBoundVars, freshMonoTy) := freshenBoundVars boundVars monoTy varsAlreadyInUse

    -- Obtain the type of its arguments
    let (argTys, retTy) := decomposeArrow freshMonoTy

    -- Skip over factory functions whose arity exceeds `maxNumArgs`
    if argTys.length > maxNumArgs then []
    else
    -- Handle partial application: Consider appplying only `k` arguments for each `k ∈ [0, argTys.length]`.
    -- Specifically, apply the first `k` args and leave the remaining args as the result type to
    -- unify with the target type `τ`.
    (List.range (argTys.length + 1)).filterMap fun k => do

      -- The first `k` argument types are applied.
      -- Update the return type if `k != argTys.length` (i.e. partial application).
      let appliedTys := argTys.take k
      let updatedRetTy := (argTys.drop k).foldr (fun σ acc => .arrow σ acc) retTy

      -- Unify the (freshened) return type with our target type `τ`
      let subst ← unifyTypes updatedRetTy τ

      -- Find type variables which aren't mapped to anything through the substittuion
      let uninstantiatedTyVars := findFreeTyVars freshBoundVars subst

      -- There must be either no type variables which aren't instantiated yet.
      -- If not, we must be able to generate random monotypes with which to instantiate them.
      guard (uninstantiatedTyVars.isEmpty || !generableTys.isEmpty)

      -- Extend substitution to map the uninstantiated type variables to these newly sampled types
      let extendedSubst : Lambda.Subst := substScope (uninstantiatedTyVars.zip sampledTys) ++ subst

      -- Apply the substitution to each of the applied argument types
      -- This makes all the applied argument types fully instantiated (concrete)
      let concreteAppliedTys := appliedTys.map (LMonoTy.subst extendedSubst)

      -- We keep this candidate polymorphic factory function
      -- only if the substitution we have built up so far (`extendedSubst`),
      -- when applied to the return type gives us our desired target type `τ`.
      -- This condition is needed in order to ensure that the generated term (which
      -- invokes this factory function) satisfies `OpsConsistent`, i.e. that the
      -- annotated type is a valid instantiation of the function's polymorphic type.
      guard (LMonoTy.subst extendedSubst updatedRetTy == τ)

      pure (name, concreteAppliedTys)

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
  octx.ops.filterMap fun (name, ty) =>
    match argsForResult ty τ with
    | some (arg :: args) => some (name, arg :: args)
    | _ => none

-- ── Indir / IndirPoly rules (depth-agnostic cores) ──────────────────
--
-- Both rules are defined *here*, ahead of `genLExprBase`, because
-- `genLExprBase` calls them (that is what makes factory applications reachable
-- under `ite` arms and binder bodies). To make that possible they
-- must not mention `genLExprBase` themselves, so every generator they need is a
-- parameter: the argument generator `genArg`, and (for IndirPoly) the `fallback`
-- used when no polymorphic candidate matches. Being non-recursive and
-- generator-parametric, they impose no termination obligation of their own — the
-- recursion measure lives entirely in the caller.
--
-- `genIndirPoly` (the depth-indexed wrapper that restores the historical
-- defaults) is defined *after* `genLExprBase`, further down this file.

/-- The **monomorphic Indir rule** (Pałka et al. 2011): pick an operator from
    `octx` whose result type is `τ` after full application, then generate all of
    its arguments at the determined argument types (no type guessing needed).

    Argument generation is the parameter `genArg`, so the caller owns the
    recursion measure and this function stays non-recursive.
    Requires `h` witnessing that at least one such operator exists. -/
def genIndir [Gen G] (octx : OpCtx) (τ : LMonoTy)
    (genArg : LMonoTy → G LExpr')
    (h : (findOpsInCtx octx τ).length > 0) : G LExpr' := do
  -- Find all operators `ops` in the context that, when fully applied,
  -- produce a term of the result type `τ`
  let ops := findOpsInCtx octx τ
  -- Randomly choose one of these operators
  let (name, argTys) ← elements ops (by apply List.ne_nil_of_length_pos; assumption)
  -- Construct the `LExpr` corresponding to the chosen `op`
  let fullArrowTy := argTys.foldr (fun σ acc => .arrow σ acc) τ
  let opExpr := .op () ⟨name, ()⟩ (some fullArrowTy)
  -- Iterate through the argument types in order
  -- and generate successive random terms of those types
  let args ← List.mapM genArg argTys
  -- Then, apply the operator to all the args
  pure (mkApps opExpr args)

/-- Generate a well-typed `LExpr` of type `τ` using the IndirPoly rule from
    Pałka et al. (2011, Section 4). Calls polymorphic library functions by:
    1. Unifying the function's return type with the target type `τ`
    2. Sampling undetermined type variables from the set of generable types
    3. Generating arguments at the resulting concrete types

    The structure mirrors the monomorphic Indir rule (`genIndir`):
    given a list of `(name, concreteArgTys)` candidates, choose one,
    generate args via `mapM genArg`, and assemble via `mkApps`.

    **Both the argument generator and the no-candidate fallback are parameters**
    (`genArg`, `fallback`), following the same open-recursion style as
    `genApp`/`genIte`/`genEq`. That is what removes every mention of
    `genLExprBase` from this definition, which in turn is what lets
    `genLExprBase` call *it*. `genIndirPoly` below restores the
    historical defaults for both.

    There is deliberately **no `depth` parameter**: `depth` was only ever
    consumed by the default argument generator and the fallback, and both are now
    supplied by the caller. -/
def genIndirPolyCore [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (bctx : BVarCtx) (τ : LMonoTy)
    (genArg : LMonoTy → G LExpr') (fallback : G LExpr')
    (maxNumArgs : Nat := 3) : G LExpr' := do
  -- Compute the set of generable types from the current context
  let generableTys := generableTypesFromCtx bctx fctx octx

  -- For each possible type variable, sample a random type to instantiate it with.
  -- When no generable types exist, fall back to an arbitrary base type
  -- (`pickBaseType`: bool/int/string/real/regex/bitvec) rather than always `.bool`,
  -- so the empty-context case still explores every ground type.
  let sampledTys ← List.replicate maxNumArgs ()
    |>.mapM (fun _ =>
      if hg : generableTys.length > 0 then do
        elements generableTys (by
          apply List.ne_nil_of_length_pos
          assumption)
      else pickBaseType)
  -- Find all polymorphic library functions that result in the target type `τ`
  let ops := findPolymorphicOps pctx τ generableTys sampledTys maxNumArgs
  if h : ops.length > 0 then do
    -- Randomly choose a polymorphic library function, and obtain its argument types
    let (functionName, argTys) ← elements ops (by
      apply List.ne_nil_of_length_pos
      assumption)

    -- Construct a call to the factory function, along with its (fully instantiated) type annotation
    -- There are no quantified type variables in the annotated type (although it may contain free type variables
    -- which appear in the context)
    let fullArrowTy := argTys.foldr (fun σ acc => .arrow σ acc) τ
    let opExpr : LExpr' := .op () ⟨functionName, ()⟩ (some fullArrowTy)

    -- For each argument, generate a random term of that type
    let args ← argTys.mapM genArg

    -- Fully apply the factory function (carrying a type annotation) to its random argument terms
    pure (mkApps opExpr args)
  else
    -- No polymorphic functions available: defer to the caller's fallback
    fallback

-- ── Expression generator ─────────────────────────────────────────────

/-- Generate a well-typed `LExpr` of type `τ` with term depth bounded by the
    first `Nat` argument. At depth 0, only leaf expressions (bvar, fvar, op,
    constants) are produced; at depth `n+1`, compound expressions may be
    produced with sub-expressions at depth `n`.

    The generated term satisfies `HasTypeA' bctx e τ` (see `genLExpr_sound`).

    ## The Indir/IndirPoly branches

    Each `n + 1` case carries, at the end of its `frequency` list, a
    **monomorphic Indir** branch and a **polymorphic IndirPoly** branch. Because
    they live *here* rather than only in `genLExpr`, a factory application — and
    in particular a *polymorphic* one — can appear in any position this generator
    produces: under `ite` arms, under `abs`/`quant` bodies, and in `genApp`'s
    function and argument. Formerly the polymorphic rule existed only at
    `genLExpr`'s root and in Indir argument position, so
    `if c then Sequence.length s else #0` was outside the support.

    Both branches draw their arguments from `genLExprBase … n`, the *smaller*
    depth index. That keeps this definition **structurally recursive** (`#print`
    shows `Nat.brecOn`, not `WellFounded.fix`), so it stays reducible and the
    ~150 `simp only [genLExprBase]` / `rw [genLExprBase]` proof sites keep
    working. Making this and `genLExpr` *mutually* recursive would instead call
    `genLExprBase (n + 1)` from `genLExpr (n + 1)` at an equal index, forcing a
    lexicographic measure, turning `genLExprBase` `@[irreducible]`, and breaking
    definitional unfolding at every one of those sites.

    The depth-`0` cases deliberately have no Indir branches: a fully-applied
    operator at the depth floor would leave no budget for its arguments. -/
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is (.arrow τ₁ τ₂), with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx (.arrow τ₁ τ₂)).length > 0
          then genIndir octx (.arrow τ₁ τ₂) (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n (.arrow τ₁ τ₂)),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is .bool, with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx .bool).length > 0
          then genIndir octx .bool (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .bool),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is .int, with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx .int).length > 0
          then genIndir octx .int (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .int),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is (.ftvar name), with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx (.ftvar name)).length > 0
          then genIndir octx (.ftvar name) (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n (.ftvar name)),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is .string, with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx .string).length > 0
          then genIndir octx .string (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .string),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is .real, with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx .real).length > 0
          then genIndir octx .real (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .real),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is (.bitvec n), with arguments drawn from this generator at `m`.
        (4, fun () =>
          if hi : (findOpsInCtx octx (.bitvec n)).length > 0
          then genIndir octx (.bitvec n) (genLExprBase fctx octx pctx tvars bctx m) hi
          else genLExprBase fctx octx pctx tvars bctx m (.bitvec n)),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is .regex, with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx .regex).length > 0
          then genIndir octx .regex (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n .regex),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is (.map τ₁ τ₂), with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx (.map τ₁ τ₂)).length > 0
          then genIndir octx (.map τ₁ τ₂) (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n (.map τ₁ τ₂)),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
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
        -- Monomorphic Indir rule: a fully-applied operator whose
        -- result type is (.seq τ), with arguments drawn from this generator at `n`.
        (4, fun () =>
          if hi : (findOpsInCtx octx (.seq τ)).length > 0
          then genIndir octx (.seq τ) (genLExprBase fctx octx pctx tvars bctx n) hi
          else genLExprBase fctx octx pctx tvars bctx n (.seq τ)),
        -- Polymorphic IndirPoly rule. Having it *here* rather than
        -- only at `genLExpr`'s root is what makes a polymorphic factory call
        -- reachable under `ite` arms and `abs`/`quant` bodies.
        (4, fun () =>
          genIndirPolyCore fctx octx pctx bctx (.seq τ)
            (genLExprBase fctx octx pctx tvars bctx n)
            (genLExprBase fctx octx pctx tvars bctx n (.seq τ))) ]
    have hw : 0 < List.sum (List.map Prod.fst gs) := by show 0 < 1+2+2+2+2+4+4; omega
    frequency gs hw
  -- ── Other type constructors (datatypes, abstract types, aliases) ──
  -- Reached for any `tcons` the cases above do not name — in practice a
  -- *datatype* declared earlier in the program (`List<int>`, `Opt<a>`, …), an
  -- abstract type, or an alias body.
  --
  -- This used to be `default` (empty support / a thrown `inhabitedWitness`), which
  -- made every such type **uninhabitable by the base generator**. That is what
  -- stopped a generated function or procedure body from ever calling a datatype's
  -- derived functions: a tester `D..isC : D → bool` or accessor `D..hd : D → int`
  -- is only useful if the argument position — of type `D` — can be filled, and at
  -- the depth floor arguments come from *this* generator. So the Indir rule kept
  -- picking those candidates and kept dead-ending.
  --
  -- There are no *constants* at such a type, so the only leaves available are the
  -- context ones: a bound variable, a free variable, or a nullary operator of that
  -- exact type — the last being precisely a nullary constructor (`Nil : List<a>`,
  -- `None : Opt<a>`). The branch is still `default` when nothing in scope has the
  -- type, so support is empty exactly when it was unreachable anyway.
  --
  -- **This case is deliberately leaf-only, and so is depth-agnostic** (`| _, τ`),
  -- unlike every named case above, each of which has `genApp`/`genIte`/Indir/IndirPoly
  -- branches at `n + 1`. The consequence is precise and worth stating: a
  -- datatype-typed *argument* is drawn from the context, never built up, so
  -- `isCons(xs)` is reachable with `xs` a variable or `Nil`, while `isCons(Cons(1,
  -- Nil))` is not. Extending this case with Indir/IndirPoly branches — letting a
  -- non-nullary constructor application fill a datatype position — is a real
  -- coverage gain and is *not* done here. Three proofs discharge this arm by "leaves
  -- only" (`case h_21` of `genLExprBase_sound`, `_fvars_subset` and
  -- `_opsConsistentR`), and each would need the inductive hypothesis plus, for
  -- IndirPoly, the `hPoly` premise. `genLExprBase_termDepth_bound` is unaffected
  -- either way: it is indexed by `SimpleType τ`, which has no datatype `tcons` case,
  -- so no depth bound is stated for a datatype target at all.
  | _, τ =>
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


/-- The depth-indexed IndirPoly rule: `genIndirPolyCore` with its two generator
    parameters defaulted the historical way.

    `genArg` defaults to `genLExprBase … depth` and the no-candidate fallback is
    `genLExprBase … depth τ`, exactly as before — so every existing call site
    and every existing proof about `genIndirPoly` continues to mean what it did.
    `genLExpr` overrides `genArg` with itself at the smaller depth index, which is
    what makes factory applications nest in *argument* position.

    The rule proper lives in `genIndirPolyCore`, defined before `genLExprBase`
    because `genLExprBase` calls it. This wrapper exists only to hold the
    `genLExprBase`-valued defaults, which is why it has to be defined here,
    afterwards. -/
def genIndirPoly [Gen G] (fctx : FVarCtx) (octx : OpCtx)
    (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat := 3)
    (genArg : LMonoTy → G LExpr' := genLExprBase fctx octx pctx tvars bctx depth)
    : G LExpr' :=
  genIndirPolyCore fctx octx pctx bctx τ genArg
    (genLExprBase fctx octx pctx tvars bctx depth τ) maxNumArgs

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
    random type guessing.

    **Factory applications nest.** At depth `n + 1` the arguments of
    an Indir/IndirPoly application are drawn from `genLExpr` *itself* at the
    smaller index `n`, so a factory call can appear inside the argument of
    another factory call — e.g. `Int.Add (Int.SafeDiv #0 #-2) (Int.SafeDiv #0 #0)`,
    a shape that was unreachable while both branches bottomed out in
    `genLExprBase`. At the depth floor (`0`) arguments come from
    `genLExprBase … 0`, i.e. leaves.

    Termination is **structural**: every recursive occurrence is at `n` under the
    `n + 1` pattern, and `genIndir`/`genIndirPoly` are separate non-recursive
    functions that receive the recursive call as their `genArg` parameter. Passing
    a recursive call to a higher-order helper this way does not disturb structural
    recursion (`#print genLExpr` shows `Nat.brecOn`, not `WellFounded.fix`), so no
    `termination_by`/`decreasing_by` is required. Crucially this also leaves
    `genLExprBase` alone — it keeps its own structural recursion, so the ~150
    existing `simp only [genLExprBase]` / `rw [genLExprBase]` proof sites are
    untouched. Making the two *mutually* recursive would instead force a
    lexicographic measure, turn `genLExprBase` well-founded and `@[irreducible]`,
    and break definitional unfolding (`rfl`) at all of those sites.

    ## What this function still adds

    `genLExprBase` now carries the Indir/IndirPoly rules in its own
    per-type `frequency` lists, so factory applications — polymorphic ones
    included — are reachable at *every* subterm position, `ite` arms and
    `abs`/`quant` bodies among them. The positional gap this docstring used to
    describe as a "known remaining gap" is closed, and it is closed *inside*
    `genLExprBase`, not here.

    What remains this function's own contribution is the **root-level
    distribution**: a 1:9 weighting of the base rules against the Indir/IndirPoly
    rules, against roughly 8:8 in the merged branch lists. It also owns
    `retryCont`. So `genLExpr` is now a thin distribution-shaping wrapper rather
    than the only place the polymorphic rule lives.

    ## The `retryCont` parameter

    `retryCont` is a **continuation that is invoked to retry generation when it
    fails**. It receives the argument generator this function would otherwise have
    used in Indir/IndirPoly argument position, and returns the generator to use
    instead — so a caller can interpose "if this sub-draw fails, draw it again with
    fresh randomness" without this module needing to know what failure *is*.

    Why it has to be a parameter, and why it has to be a *transformer* rather than
    a plain generator: at depth `n + 1` the argument generator must be *this
    generator itself at `n`*, so a fixed `LMonoTy → G LExpr'` value would pin the
    caller to one particular depth. `retryCont` instead threads through the
    recursion and is therefore applied at **every** level — which is the point,
    since generation failure compounds multiplicatively with nesting depth and the
    nested levels are exactly what a caller cannot otherwise reach.

    Note also that `retryCont` at depth `n + 1` wraps the *whole* level-`n`
    generator, `genIndirPoly`'s type-variable instantiation (`sampledTys`) very much
    included. So a retrying continuation resamples unfillable instantiations at
    every nested level, and neither `genIndir` nor `genIndirPoly` needs to change.

    Retrying is meaningful only under `Plausible.Gen`, where a failed leaf throws.
    Under `SetGen.Set` — the semantics the soundness/completeness theorems use —
    `default` is `∅` rather than an error, so there is no failure to observe and
    nothing to retry. The abstract `Gen` class deliberately provides no
    `tryCatch`/`Alternative`, which is precisely why this is a caller-supplied
    continuation rather than something this function could do itself.

    It defaults to `id` (retry nothing) and is placed **last**, after the
    `optParam` `maxNumArgs`, so every existing positional call site elaborates
    unchanged and `genLExpr … depth τ` is definitionally what it was before.
    The ordering matters: putting `retryCont` earlier would silently swallow
    positional arguments. The theorems in `HasTypeAGen.lean` /
    `HasTypeAGenOpsConsistent.lean` continue to describe the `retryCont = id` case,
    which is the honest scope — a retry changes how many attempts a draw needs, not
    which terms are reachable. -/
def genLExpr [Gen G] (fctx : FVarCtx) (octx : OpCtx) (pctx : PolyOpCtx)
    (tvars : List TyIdentifier)
    (bctx : BVarCtx) (depth : Nat) (τ : LMonoTy) (maxNumArgs : Nat := 3)
    (retryCont : (LMonoTy → G LExpr') → (LMonoTy → G LExpr') := id) : G LExpr' :=
  -- The argument generator for the Indir/IndirPoly rules. At the depth floor it is
  -- the base generator (leaves); above it, `genLExpr` itself at the smaller index
  -- `n` — which is what lets factory applications nest. The recursion is structural
  -- on `depth`, so no `termination_by` is needed.
  --
  -- `retryCont` is the caller's retry continuation (see the docstring): it wraps
  -- whichever generator we use in argument position, and threads into the
  -- recursive call so it applies at every level, not just this one.
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
            -- Monomorphic Indir rule
            genIndir octx τ genArg h)
          (fun () =>
            -- Polymorphic IndirPoly rule (Pałka et al. 2011, Section 4)
            genIndirPoly fctx octx pctx tvars bctx depth τ maxNumArgs genArg)) ]
      (by simp)
  else
    -- No monomorphic Indir candidates; try IndirPoly or fall back to base
    pick
      (fun () => genLExprBase fctx octx pctx tvars bctx depth τ)
      (fun () => genIndirPoly fctx octx pctx tvars bctx depth τ maxNumArgs genArg)

-- ── Top-level generators ─────────────────────────────────────────────

/-- Generate a well-typed closed expression (no free variables, no operators)
    with bounded depth. -/
def genClosedLExpr [Gen G] (tvars : List TyIdentifier) (depth : Nat)
    (maxNumArgs : Nat := 3) : G LExpr' := do
  let τ ← genLMonoTy tvars depth
  genLExpr [] ∅ [] tvars [] depth τ maxNumArgs

/-! ## Core operator contexts

The monomorphic and polymorphic operator contexts drawn from Strata's
`Core.Factory`. These live here (rather than in `TestSupport`) so that
*generators* — not just the test harness — can be seeded with a realistic set of
operators; `ProgramGen` uses them for axiom, function, and procedure bodies.
`TestSupport` re-exports them for the property suites. -/

/-- Every monomorphic operator of Strata's `Core.Factory`, as a pair of a name and
    a curried type. The Indir generation rule uses this context.

    `factoryOps` derives the list from the factory itself, so the vocabulary here
    cannot drift from the operators that Core defines. An earlier version of this
    definition was a hand-written list of 40 entries. Each entry named a real
    factory operator, and each type agreed with the factory, but the list held only
    the operators on `int`, `bool` and a few on `string` and `regex`. It therefore
    excluded most operators on `string`, and every operator on `real` and on
    `bitvec`, out of the 310 that the factory defines.

    A generator over the smaller list cannot build a term such as `Str.Length "é"`
    or `Bv8.SafeSDiv`, so each property about those operators passed vacuously. The
    Tyche panels showed the same gap as an absence of coverage.

    The body repeats the body of `factoryOps` rather than a call to it, because
    `factoryOps` lives in `HasTypeAGen/Defs.lean`, and that file imports this one.
    The two must stay the same. `coreMonoOps_eq_factoryOps` in `Defs.lean` proves
    that they are, so a change to one of them and not the other breaks the build. -/
def coreMonoOps : OpCtx :=
  OpCtx.ofList <| Core.Factory.toArray.toList.filterMap fun f =>
    some (f.name.name, LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))

/-- Every **polymorphic** operator of Strata's `Core.Factory`, as a name paired with its
    full type scheme `∀ typeArgs. mkArrow' output inputs`. The IndirPoly generation rule
    uses this context (Pałka et al. 2011, Section 4).

    Derived from the factory for exactly the reason `coreMonoOps` is (see there): a
    hand-written list drifts. The list this replaced had drifted three ways against
    `strata-org/Strata` `main`:

    * it was **missing** `mapConst`, `Sequence.select!` and `TriggerGroup.addTrigger`, so
      no generated term could apply them and every property about them passed vacuously;
    * it carried a `const : ∀ k v. v → Map k v` that `Core.Factory` does **not** define —
      the real entry is `mapConst`; and
    * its `Sequence.build` was `∀ a. a → Sequence a`, while the factory's takes *two*
      arguments (`∀ a. Sequence a → a → Sequence a`). A generated `Sequence.build e` was
      therefore annotated at an arity the factory disagrees with, which is what the
      printer reported as "unknown operation, rendering as generic call: Sequence.build".

    Monomorphic factory entries are excluded (`typeArgs ≠ []`): `coreMonoOps` already
    covers them through the Indir rule, and admitting them here would only duplicate that
    work at every draw.

    The body repeats the body of `factoryPolyOps` (restricted to the polymorphic entries)
    rather than calling it, because `factoryPolyOps` lives in `HasTypeAGen/Defs.lean` and
    that file imports this one. `corePolyOps_eq_factoryPolyOps` in `Defs.lean` proves the
    two agree, so a change to one and not the other breaks the build. -/
def corePolyOps : PolyOpCtx :=
  Core.Factory.toArray.toList.filterMap fun f =>
    if f.typeArgs.isEmpty then none
    else some (f.name.name,
      Lambda.LTy.forAll f.typeArgs (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))
