import StrataGenerators.SetGen
import Basalt.IO
import Strata.DL.Lambda.LExprTypeSpec

open Lambda RandomChoice SetGen

namespace HT

/-- Simple geometric-distributed nat generator, only needs `Gen`. -/
def Nat.arb [Gen G] : G Nat :=
  pick
    (fun () => pure 0)
    (fun () => do let n ← Nat.arb; pure (n + 1))
partial_fixpoint

/-!
# Generator of Well-Typed Terms Satisfying a Simplified `HasType`

A Basalt `SetGen`-based random generator for well-typed Strata `LExpr`s
that satisfy a simplified `HasType` relation (Hindley-Milner without
let-polymorphism, restricted to the monomorphic fragment).

## Import Constraint

The full `HasType` relation lives in `Strata.DL.Lambda.LExprTypeSpec`, which
imports `Strata.DL.Util.List`. That module conflicts with `Batteries.Data.List.Basic`
(both define `List.Forall₂.below.casesOn`). Since SetGen depends on batteries,
we cannot import both.

**Solution**: We define a simplified `HasType` locally that captures exactly the
fragment we generate for. The full equivalence (this relation ↔ the subset of
Strata's `HasType` without `tgen`/`talias`/annotated rules) can be proved in a
file that imports `LExprTypeSpec` without SetGen.

## Design

The generator targets monomorphic types only (`.forAll [] monoTy`). Polymorphism
is handled by fusing `tvar`+`tinst`: when looking up a variable or operator with
a polymorphic scheme, we use `matchScheme` to compute the instantiation.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- §1. matchScheme
-- ═══════════════════════════════════════════════════════════════════════

/-- Given a polymorphic type scheme `∀α₁...αₙ. body` and a monomorphic target
type, compute the substitution `[α₁ := σ₁, ..., αₙ := σₙ]` such that
`body[αᵢ := σᵢ] = target`, or return `none` if no such substitution exists. -/
def matchScheme (typeScheme : LTy) (target : LMonoTy) : Option (List LMonoTy) :=
    match typeScheme with
    | .forAll tyVars body => do
      let subst ← go tyVars body target {}
      tyVars.mapM subst.find?
  where
    go (tyVars : List TyIdentifier) (body : LMonoTy) (target : LMonoTy)
       (subst : Map TyIdentifier LMonoTy)
        : Option (Map TyIdentifier LMonoTy) :=
      match body, target with
      | .ftvar name, t =>
        if name ∈ tyVars then
          match subst.find? name with
          | none          => some (subst.insert name t)
          | some existing => if existing == t then some subst else none
        else
          if t == .ftvar name then some subst else none
      | .tcons name1 args1, .tcons name2 args2 =>
        if name1 == name2 && args1.length == args2.length then
          goArgs tyVars args1 args2 subst
        else none
      | .bitvec n1, .bitvec n2 =>
        if n1 == n2 then some subst else none
      | _, _ => none
    goArgs (tyVars : List TyIdentifier) (args1 : List LMonoTy) (args2 : List LMonoTy)
      (subst : Map TyIdentifier LMonoTy) : Option (Map TyIdentifier LMonoTy) :=
      match args1, args2 with
      | [], [] => some subst
      | a :: as, b :: bs => do
          let subst' ← go tyVars a b subst
          goArgs tyVars as bs subst'
      | _, _ => none

-- ═══════════════════════════════════════════════════════════════════════
-- §2. Parameters and Expression Type
-- ═══════════════════════════════════════════════════════════════════════

abbrev HTParams : LExprParams := ⟨Unit, Unit⟩
abbrev HTExpr := LExpr (LExprParams.mono HTParams)
abbrev HTIdent := Identifier Unit

instance : DecidableEq Unit := instDecidableEqPUnit
instance instBEqLMonoTy : BEq LMonoTy := instBEqOfDecidableEq
instance : BEq HTIdent := instBEqOfDecidableEq

-- ═══════════════════════════════════════════════════════════════════════
-- §3. Simplified HasType (local definition)
-- ═══════════════════════════════════════════════════════════════════════

/-- Variable context: maps identifiers to polymorphic type schemes. -/
abbrev VarCtx := List (HTIdent × LTy)

/-- Operator context: maps operator names to polymorphic type schemes. -/
abbrev OpSchemeCtx := List (String × LTy)

/-- Apply a substitution to an LMonoTy, replacing free type variables. -/
def LMonoTy.applySubst (subst : List (TyIdentifier × LMonoTy)) : LMonoTy → LMonoTy
  | .ftvar name =>
    match subst.lookup name with
    | some ty => ty
    | none => .ftvar name
  | .tcons name args => .tcons name (args.map (applySubst subst))
  | .bitvec n => .bitvec n

/-- Instantiate a type scheme with a list of monotypes. -/
def LTy.instantiate (scheme : LTy) (tys : List LMonoTy) : LMonoTy :=
  match scheme with
  | .forAll tyVars body =>
    LMonoTy.applySubst (tyVars.zip tys) body

/-- Simplified `HasType` relation for the monomorphic fragment.
    This captures exactly the rules we generate for:
    - Constants (bool, int)
    - Variables with scheme instantiation (tvar + tinst fused)
    - Operators with scheme instantiation (top + tinst fused)
    - Abstraction, application, if-then-else, equality -/
inductive SHasType : VarCtx → OpSchemeCtx → HTExpr → LMonoTy → Prop where
  | tbool_const : SHasType Γ Δ (.boolConst () b) .bool
  | tint_const  : SHasType Γ Δ (.intConst () k) .int
  | tvar : (x, scheme) ∈ Γ →
           matchScheme scheme τ = some subst →
           SHasType Γ Δ (.fvar () x none) τ
  | top  : (name, scheme) ∈ Δ →
           matchScheme scheme τ = some subst →
           SHasType Γ Δ (.op () ⟨name, ()⟩ none) τ
  | tabs : SHasType ((x, .forAll [] τ₁) :: Γ) Δ body τ₂ →
           SHasType Γ Δ (.abs () "" none (LExpr.varClose 0 (x, none) body))
                        (.arrow τ₁ τ₂)
  | tapp : SHasType Γ Δ fn (.arrow τ₂ τ₁) →
           SHasType Γ Δ arg τ₂ →
           SHasType Γ Δ (.app () fn arg) τ₁
  | tif  : SHasType Γ Δ c .bool →
           SHasType Γ Δ t τ →
           SHasType Γ Δ e τ →
           SHasType Γ Δ (.ite () c t e) τ
  | teq  : SHasType Γ Δ e₁ τ' →
           SHasType Γ Δ e₂ τ' →
           SHasType Γ Δ (.eq () e₁ e₂) .bool

-- ═══════════════════════════════════════════════════════════════════════
-- §4. Simple Types and Depth
-- ═══════════════════════════════════════════════════════════════════════

inductive SimpleType : LMonoTy → Prop where
  | bool  : SimpleType .bool
  | int   : SimpleType .int
  | arrow : SimpleType τ₁ → SimpleType τ₂ → SimpleType (.arrow τ₁ τ₂)

def monoTyDepth : LMonoTy → Nat
  | .arrow τ₁ τ₂ => max (monoTyDepth τ₁) (monoTyDepth τ₂) + 1
  | _             => 0

-- ═══════════════════════════════════════════════════════════════════════
-- §5. Context Helpers
-- ═══════════════════════════════════════════════════════════════════════

def varsMatchingTarget (vctx : VarCtx) (τ : LMonoTy) : List HTIdent :=
  vctx.filterMap fun (x, scheme) =>
    if (matchScheme scheme τ).isSome then some x else none

def opsMatchingTarget (octx : OpSchemeCtx) (τ : LMonoTy) : List String :=
  octx.filterMap fun (name, scheme) =>
    if (matchScheme scheme τ).isSome then some name else none

def pickMatchingVar [Gen G] (vctx : VarCtx) (τ : LMonoTy)
    (h : (varsMatchingTarget vctx τ).length > 0) : G HTExpr := do
  let names := varsMatchingTarget vctx τ
  let idx ← choose 0 (names.length - 1) (by omega)
  pure (.fvar () (names.getD idx.down ⟨"", ()⟩) none)

def pickMatchingOp [Gen G] (octx : OpSchemeCtx) (τ : LMonoTy)
    (h : (opsMatchingTarget octx τ).length > 0) : G HTExpr := do
  let names := opsMatchingTarget octx τ
  let idx ← choose 0 (names.length - 1) (by omega)
  pure (.op () ⟨names.getD idx.down "", ()⟩ none)

-- ═══════════════════════════════════════════════════════════════════════
-- §6. Type Generator
-- ═══════════════════════════════════════════════════════════════════════

def genLMonoTy [Gen G] : Nat → G LMonoTy
  | 0 =>
    pick (fun () => pure .bool)
         (fun () => pure .int)
  | n + 1 =>
    pick
      (fun () => pure .bool)
      (fun () =>
        pick
          (fun () => pure .int)
          (fun () => do
            let τ₁ ← genLMonoTy n
            let τ₂ ← genLMonoTy n
            pure (.arrow τ₁ τ₂)))

-- ═══════════════════════════════════════════════════════════════════════
-- §7. Fresh Names
-- ═══════════════════════════════════════════════════════════════════════

def freshName (counter : Nat) : HTIdent := ⟨s!"x{counter}", ()⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §8. Expression Generator
-- ═══════════════════════════════════════════════════════════════════════

def genHTExpr [Gen G] (vctx : VarCtx) (octx : OpSchemeCtx)
    (counter : Nat) : Nat → LMonoTy → G HTExpr
  | 0, .bool =>
    let matchingVars := varsMatchingTarget vctx .bool
    let matchingOps := opsMatchingTarget octx .bool
    pick
      (fun () =>
        if hv : matchingVars.length > 0
        then pickMatchingVar vctx .bool hv
        else pick (fun () => pure (.boolConst () true))
                  (fun () => pure (.boolConst () false)))
      (fun () =>
        if ho : matchingOps.length > 0
        then pickMatchingOp octx .bool ho
        else pick (fun () => pure (.boolConst () true))
                  (fun () => pure (.boolConst () false)))
  | 0, .int =>
    let matchingVars := varsMatchingTarget vctx .int
    let matchingOps := opsMatchingTarget octx .int
    pick
      (fun () =>
        if hv : matchingVars.length > 0
        then pickMatchingVar vctx .int hv
        else do let k ← Nat.arb; pure (.intConst () (k : Int)))
      (fun () =>
        if ho : matchingOps.length > 0
        then pickMatchingOp octx .int ho
        else do let k ← Nat.arb; pure (.intConst () (k : Int)))
  | 0, .arrow τ₁ τ₂ =>
    let matchingVars := varsMatchingTarget vctx (.arrow τ₁ τ₂)
    let matchingOps := opsMatchingTarget octx (.arrow τ₁ τ₂)
    let x := freshName counter
    pick
      (fun () =>
        if hv : matchingVars.length > 0
        then pickMatchingVar vctx (.arrow τ₁ τ₂) hv
        else do
          let body ← genHTExpr ((x, .forAll [] τ₁) :: vctx) octx (counter + 1) 0 τ₂
          pure (.abs () "" none (LExpr.varClose 0 (x, none) body)))
      (fun () =>
        if ho : matchingOps.length > 0
        then pickMatchingOp octx (.arrow τ₁ τ₂) ho
        else do
          let body ← genHTExpr ((x, .forAll [] τ₁) :: vctx) octx (counter + 1) 0 τ₂
          pure (.abs () "" none (LExpr.varClose 0 (x, none) body)))
  | 0, _ =>
    pure (.boolConst () false)

  | n + 1, .bool =>
    let matchingVars := varsMatchingTarget vctx .bool
    let matchingOps := opsMatchingTarget octx .bool
    pick
      (fun () =>
        pick (fun () => pure (.boolConst () true))
             (fun () => pure (.boolConst () false)))
      (fun () =>
        pick
          (fun () => do
            let c ← genHTExpr vctx octx counter n .bool
            let t ← genHTExpr vctx octx counter n .bool
            let e ← genHTExpr vctx octx counter n .bool
            pure (.ite () c t e))
          (fun () =>
            pick
              (fun () => do
                let τ' ← genLMonoTy n
                let e₁ ← genHTExpr vctx octx counter n τ'
                let e₂ ← genHTExpr vctx octx counter n τ'
                pure (.eq () e₁ e₂))
              (fun () =>
                pick
                  (fun () => do
                    let τ' ← genLMonoTy n
                    let fn ← genHTExpr vctx octx counter n (.arrow τ' .bool)
                    let arg ← genHTExpr vctx octx counter n τ'
                    pure (.app () fn arg))
                  (fun () =>
                    pick
                      (fun () =>
                        if hv : matchingVars.length > 0
                        then pickMatchingVar vctx .bool hv
                        else pick (fun () => pure (.boolConst () true))
                                  (fun () => pure (.boolConst () false)))
                      (fun () =>
                        if ho : matchingOps.length > 0
                        then pickMatchingOp octx .bool ho
                        else pick (fun () => pure (.boolConst () true))
                                  (fun () => pure (.boolConst () false)))))))

  | n + 1, .int =>
    let matchingVars := varsMatchingTarget vctx .int
    let matchingOps := opsMatchingTarget octx .int
    pick
      (fun () =>
        pick
          (fun () => do let k ← Nat.arb; pure (.intConst () (k : Int)))
          (fun () => do let k ← Nat.arb; pure (.intConst () (-(↑k + 1 : Int)))))
      (fun () =>
        pick
          (fun () => do
            let τ' ← genLMonoTy n
            let fn ← genHTExpr vctx octx counter n (.arrow τ' .int)
            let arg ← genHTExpr vctx octx counter n τ'
            pure (.app () fn arg))
          (fun () =>
            pick
              (fun () => do
                let c ← genHTExpr vctx octx counter n .bool
                let t ← genHTExpr vctx octx counter n .int
                let e ← genHTExpr vctx octx counter n .int
                pure (.ite () c t e))
              (fun () =>
                pick
                  (fun () =>
                    if hv : matchingVars.length > 0
                    then pickMatchingVar vctx .int hv
                    else do let k ← Nat.arb; pure (.intConst () (k : Int)))
                  (fun () =>
                    if ho : matchingOps.length > 0
                    then pickMatchingOp octx .int ho
                    else do let k ← Nat.arb; pure (.intConst () (k : Int))))))

  | n + 1, .arrow τ₁ τ₂ =>
    let matchingVars := varsMatchingTarget vctx (.arrow τ₁ τ₂)
    let matchingOps := opsMatchingTarget octx (.arrow τ₁ τ₂)
    let x := freshName counter
    pick
      (fun () => do
        let body ← genHTExpr ((x, .forAll [] τ₁) :: vctx) octx (counter + 1) n τ₂
        pure (.abs () "" none (LExpr.varClose 0 (x, none) body)))
      (fun () =>
        pick
          (fun () => do
            let τ' ← genLMonoTy n
            let fn ← genHTExpr vctx octx counter n (.arrow τ' (.arrow τ₁ τ₂))
            let arg ← genHTExpr vctx octx counter n τ'
            pure (.app () fn arg))
          (fun () =>
            pick
              (fun () => do
                let c ← genHTExpr vctx octx counter n .bool
                let t ← genHTExpr vctx octx counter n (.arrow τ₁ τ₂)
                let e ← genHTExpr vctx octx counter n (.arrow τ₁ τ₂)
                pure (.ite () c t e))
              (fun () =>
                pick
                  (fun () =>
                    if hv : matchingVars.length > 0
                    then pickMatchingVar vctx (.arrow τ₁ τ₂) hv
                    else do
                      let body ← genHTExpr ((x, .forAll [] τ₁) :: vctx) octx (counter + 1) n τ₂
                      pure (.abs () "" none (LExpr.varClose 0 (x, none) body)))
                  (fun () =>
                    if ho : matchingOps.length > 0
                    then pickMatchingOp octx (.arrow τ₁ τ₂) ho
                    else do
                      let body ← genHTExpr ((x, .forAll [] τ₁) :: vctx) octx (counter + 1) n τ₂
                      pure (.abs () "" none (LExpr.varClose 0 (x, none) body))))))

  | _, _ => pure (.boolConst () false)

def genClosedHTExpr [Gen G] (size : Nat) : G HTExpr := do
  let τ ← genLMonoTy size
  genHTExpr [] [] 0 size τ

-- ═══════════════════════════════════════════════════════════════════════
-- §9. Soundness
-- ═══════════════════════════════════════════════════════════════════════

private theorem varsMatchingTarget_mem (vctx : VarCtx) (τ : LMonoTy) (x : HTIdent)
    (h : x ∈ varsMatchingTarget vctx τ) :
    ∃ scheme subst, (x, scheme) ∈ vctx ∧ matchScheme scheme τ = some subst := by
  simp only [varsMatchingTarget, List.mem_filterMap] at h
  obtain ⟨⟨y, scheme⟩, hmem, hif⟩ := h
  simp only at hif
  split at hif
  · rename_i hsome
    simp at hif; subst hif
    rw [Option.isSome_iff_exists] at hsome
    obtain ⟨subst, hsubst⟩ := hsome
    exact ⟨scheme, subst, hmem, hsubst⟩
  · simp at hif

private theorem opsMatchingTarget_mem (octx : OpSchemeCtx) (τ : LMonoTy) (name : String)
    (h : name ∈ opsMatchingTarget octx τ) :
    ∃ scheme subst, (name, scheme) ∈ octx ∧ matchScheme scheme τ = some subst := by
  simp only [opsMatchingTarget, List.mem_filterMap] at h
  obtain ⟨⟨n, scheme⟩, hmem, hif⟩ := h
  simp only at hif
  split at hif
  · rename_i hsome
    simp at hif; subst hif
    rw [Option.isSome_iff_exists] at hsome
    obtain ⟨subst, hsubst⟩ := hsome
    exact ⟨scheme, subst, hmem, hsubst⟩
  · simp at hif

private theorem pickMatchingVar_sound (vctx : VarCtx) (octx : OpSchemeCtx)
    (τ : LMonoTy) (hv : (varsMatchingTarget vctx τ).length > 0)
    (e : HTExpr)
    (he : e ∈ SetGen.support (pickMatchingVar (G := SetGen.Set) vctx τ hv)) :
    SHasType vctx octx e τ := by
  simp only [pickMatchingVar, mem_support_bind_iff, mem_support_choose_iff,
             mem_support_pure_iff] at he
  obtain ⟨idx, ⟨_, hhi⟩, heq⟩ := he
  subst heq
  have hlt : idx.down < (varsMatchingTarget vctx τ).length := by omega
  have helem : (varsMatchingTarget vctx τ)[idx.down] ∈ (varsMatchingTarget vctx τ) := List.getElem_mem hlt
  have hgetD : (varsMatchingTarget vctx τ).getD idx.down ⟨"", ()⟩ = (varsMatchingTarget vctx τ)[idx.down] := by
    simp [List.getD, List.getElem?_eq_getElem hlt]
  rw [hgetD]
  obtain ⟨scheme, subst, hmem, hmatch⟩ := varsMatchingTarget_mem vctx τ _ helem
  exact .tvar hmem hmatch

private theorem pickMatchingOp_sound (vctx : VarCtx) (octx : OpSchemeCtx)
    (τ : LMonoTy) (ho : (opsMatchingTarget octx τ).length > 0)
    (e : HTExpr)
    (he : e ∈ SetGen.support (pickMatchingOp (G := SetGen.Set) octx τ ho)) :
    SHasType vctx octx e τ := by
  simp only [pickMatchingOp, mem_support_bind_iff, mem_support_choose_iff,
             mem_support_pure_iff] at he
  obtain ⟨idx, ⟨_, hhi⟩, heq⟩ := he
  subst heq
  have hlt : idx.down < (opsMatchingTarget octx τ).length := by omega
  have helem : (opsMatchingTarget octx τ)[idx.down] ∈ (opsMatchingTarget octx τ) := List.getElem_mem hlt
  have hgetD : (opsMatchingTarget octx τ).getD idx.down "" = (opsMatchingTarget octx τ)[idx.down] := by
    simp [List.getD, List.getElem?_eq_getElem hlt]
  rw [hgetD]
  obtain ⟨scheme, subst, hmem, hmatch⟩ := opsMatchingTarget_mem octx τ _ helem
  exact .top hmem hmatch

private theorem norm_bool : LMonoTy.bool = LMonoTy.tcons "bool" [] := rfl
private theorem norm_int : LMonoTy.int = LMonoTy.tcons "int" [] := rfl
private theorem norm_arrow (τ₁ τ₂ : LMonoTy) :
    LMonoTy.arrow τ₁ τ₂ = LMonoTy.tcons "arrow" [τ₁, τ₂] := rfl

private theorem genLMonoTy_simple (n : Nat) (τ : LMonoTy)
    (h : τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) n)) : SimpleType τ := by
  induction n generalizing τ with
  | zero =>
    simp only [genLMonoTy, mem_support_pick_iff, mem_support_pure_iff] at h
    rcases h with rfl | rfl
    · exact .bool
    · exact .int
  | succ n ih =>
    simp only [genLMonoTy, mem_support_pick_iff, mem_support_pure_iff,
               mem_support_bind_iff] at h
    rcases h with rfl | rfl | ⟨τ₁, h₁, τ₂, h₂, rfl⟩
    · exact .bool
    · exact .int
    · exact .arrow (ih τ₁ h₁) (ih τ₂ h₂)

set_option maxHeartbeats 1600000 in
theorem genHTExpr_sound (vctx : VarCtx) (octx : OpSchemeCtx)
    (counter : Nat) (size : Nat) (τ : LMonoTy)
    (hτ : SimpleType τ) (e : HTExpr)
    (he : e ∈ SetGen.support (genHTExpr (G := SetGen.Set) vctx octx counter size τ)) :
    SHasType vctx octx e τ := by
  match size, τ, hτ with
  | 0, _, SimpleType.bool =>
    rw [norm_bool] at he; simp only [genHTExpr, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨_, h⟩ | ⟨_, rfl | rfl⟩) | (⟨_, h⟩ | ⟨_, rfl | rfl⟩)
    all_goals first
      | exact pickMatchingVar_sound vctx octx .bool _ _ h
      | exact pickMatchingOp_sound vctx octx .bool _ _ h
      | exact .tbool_const
  | 0, _, SimpleType.int =>
    rw [norm_int] at he; simp only [genHTExpr, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)
    all_goals first
      | exact pickMatchingVar_sound vctx octx .int _ _ h
      | exact pickMatchingOp_sound vctx octx .int _ _ h
      | exact .tint_const
  | 0, _, SimpleType.arrow hs₁ hs₂ =>
    rename_i τ₁ τ₂
    rw [norm_arrow] at he; simp only [genHTExpr, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨_, h⟩ | ⟨_, body, hbody, rfl⟩) | (⟨_, h⟩ | ⟨_, body, hbody, rfl⟩)
    · exact pickMatchingVar_sound vctx octx _ _ _ h
    · exact .tabs (genHTExpr_sound ((freshName counter, .forAll [] τ₁) :: vctx) octx
                    (counter + 1) 0 τ₂ hs₂ _ hbody)
    · exact pickMatchingOp_sound vctx octx _ _ _ h
    · exact .tabs (genHTExpr_sound ((freshName counter, .forAll [] τ₁) :: vctx) octx
                    (counter + 1) 0 τ₂ hs₂ _ hbody)
  | n + 1, _, SimpleType.bool =>
    rw [norm_bool] at he; simp only [genHTExpr, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (rfl | rfl) |
      ⟨c, hc, t, ht, e', he', rfl⟩ | ⟨τ', hτ', e₁, he₁, e₂, he₂, rfl⟩ |
      ⟨τ', hτ', fn, hfn, arg, harg, rfl⟩ |
      (⟨_, h⟩ | ⟨_, rfl | rfl⟩) | (⟨_, h⟩ | ⟨_, rfl | rfl⟩)
    · exact .tbool_const
    · exact .tbool_const
    · exact .tif (genHTExpr_sound vctx octx counter n .bool .bool _ hc)
                  (genHTExpr_sound vctx octx counter n .bool .bool _ ht)
                  (genHTExpr_sound vctx octx counter n .bool .bool _ he')
    · exact .teq (genHTExpr_sound vctx octx counter n τ' (genLMonoTy_simple n _ hτ') _ he₁)
                  (genHTExpr_sound vctx octx counter n τ' (genLMonoTy_simple n _ hτ') _ he₂)
    · exact .tapp (genHTExpr_sound vctx octx counter n (.arrow τ' .bool)
                    (.arrow (genLMonoTy_simple n _ hτ') .bool) _ hfn)
                  (genHTExpr_sound vctx octx counter n τ' (genLMonoTy_simple n _ hτ') _ harg)
    · exact pickMatchingVar_sound vctx octx .bool _ _ h
    · exact .tbool_const
    · exact .tbool_const
    · exact pickMatchingOp_sound vctx octx .bool _ _ h
    · exact .tbool_const
    · exact .tbool_const
  | n + 1, _, SimpleType.int =>
    rw [norm_int] at he; simp only [genHTExpr, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) |
      ⟨τ', hτ', fn, hfn, arg, harg, rfl⟩ |
      ⟨c, hc, t, ht, e', he', rfl⟩ |
      (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩) | (⟨_, h⟩ | ⟨_, ⟨k, _, rfl⟩⟩)
    · exact .tint_const
    · exact .tint_const
    · exact .tapp (genHTExpr_sound vctx octx counter n (.arrow τ' .int)
                    (.arrow (genLMonoTy_simple n _ hτ') .int) _ hfn)
                  (genHTExpr_sound vctx octx counter n τ' (genLMonoTy_simple n _ hτ') _ harg)
    · exact .tif (genHTExpr_sound vctx octx counter n .bool .bool _ hc)
                  (genHTExpr_sound vctx octx counter n .int .int _ ht)
                  (genHTExpr_sound vctx octx counter n .int .int _ he')
    · exact pickMatchingVar_sound vctx octx .int _ _ h
    · exact .tint_const
    · exact pickMatchingOp_sound vctx octx .int _ _ h
    · exact .tint_const
  | n + 1, _, SimpleType.arrow hs₁ hs₂ =>
    rename_i τ₁ τ₂
    rw [norm_arrow] at he; simp only [genHTExpr, pick_mem_iff, SetGen.Set.mem_bind,
      SetGen.Set.mem_pure, mem_support_iff, SetGen.mem_dite] at he
    rcases he with ⟨body, hbody, rfl⟩ |
      ⟨τ', hτ', fn, hfn, arg, harg, rfl⟩ |
      ⟨c, hc, t, ht, e', he', rfl⟩ |
      (⟨_, h⟩ | ⟨_, body, hbody, rfl⟩) | (⟨_, h⟩ | ⟨_, body, hbody, rfl⟩)
    · exact .tabs (genHTExpr_sound ((freshName counter, .forAll [] τ₁) :: vctx) octx
                    (counter + 1) n τ₂ hs₂ _ hbody)
    · exact .tapp (genHTExpr_sound vctx octx counter n (.arrow τ' (.arrow τ₁ τ₂))
                    (.arrow (genLMonoTy_simple n _ hτ') (.arrow hs₁ hs₂)) _ hfn)
                  (genHTExpr_sound vctx octx counter n τ' (genLMonoTy_simple n _ hτ') _ harg)
    · exact .tif (genHTExpr_sound vctx octx counter n .bool .bool _ hc)
                  (genHTExpr_sound vctx octx counter n (.arrow τ₁ τ₂) (.arrow hs₁ hs₂) _ ht)
                  (genHTExpr_sound vctx octx counter n (.arrow τ₁ τ₂) (.arrow hs₁ hs₂) _ he')
    · exact pickMatchingVar_sound vctx octx _ _ _ h
    · exact .tabs (genHTExpr_sound ((freshName counter, .forAll [] τ₁) :: vctx) octx
                    (counter + 1) n τ₂ hs₂ _ hbody)
    · exact pickMatchingOp_sound vctx octx _ _ _ h
    · exact .tabs (genHTExpr_sound ((freshName counter, .forAll [] τ₁) :: vctx) octx
                    (counter + 1) n τ₂ hs₂ _ hbody)
  termination_by (size, sizeOf τ)
  decreasing_by all_goals simp_wf; first | omega | simp_all [LMonoTy.arrow]; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §10. Completeness
-- ═══════════════════════════════════════════════════════════════════════

/-- Fragment predicate characterizing expressions in the generator's range. -/
inductive InFragment : Nat → Nat → VarCtx → OpSchemeCtx → HTExpr → LMonoTy → Prop where
  | boolConst : InFragment size counter vctx octx (.boolConst () b) .bool
  | intConst  : InFragment size counter vctx octx (.intConst () k) .int
  | var       : (x, scheme) ∈ vctx →
                matchScheme scheme τ = some subst →
                InFragment size counter vctx octx (.fvar () x none) τ
  | op        : (name, scheme) ∈ octx →
                matchScheme scheme τ = some subst →
                InFragment size counter vctx octx (.op () ⟨name, ()⟩ none) τ
  | abs       : InFragment n (counter + 1) ((freshName counter, .forAll [] τ₁) :: vctx) octx body τ₂ →
                InFragment (n + 1) counter vctx octx
                  (.abs () "" none (LExpr.varClose 0 ((freshName counter), none) body))
                  (.arrow τ₁ τ₂)
  | app       : SimpleType τ' → monoTyDepth τ' ≤ n →
                InFragment n counter vctx octx fn (.arrow τ' τ) →
                InFragment n counter vctx octx arg τ' →
                InFragment (n + 1) counter vctx octx (.app () fn arg) τ
  | ite       : InFragment n counter vctx octx c .bool →
                InFragment n counter vctx octx t τ →
                InFragment n counter vctx octx e τ →
                InFragment (n + 1) counter vctx octx (.ite () c t e) τ
  | eq        : SimpleType τ' → monoTyDepth τ' ≤ n →
                InFragment n counter vctx octx e₁ τ' →
                InFragment n counter vctx octx e₂ τ' →
                InFragment (n + 1) counter vctx octx (.eq () e₁ e₂) .bool

private theorem genLMonoTy_support (n : Nat) (τ : LMonoTy) :
    τ ∈ SetGen.support (genLMonoTy (G := SetGen.Set) n) ↔
      SimpleType τ ∧ monoTyDepth τ ≤ n := by
  induction n generalizing τ with
  | zero =>
    simp only [genLMonoTy, mem_support_pick_iff, mem_support_pure_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨.bool, Nat.le_refl _⟩
      · exact ⟨.int, Nat.le_refl _⟩
    · intro ⟨hs, hd⟩
      cases hs with
      | bool  => left; rfl
      | int   => right; rfl
      | arrow =>
        rename_i τ₁ τ₂ _ _
        have hd' : monoTyDepth (.tcons "arrow" [τ₁, τ₂]) ≤ 0 := hd
        rw [monoTyDepth.eq_1] at hd'; omega
  | succ n ih =>
    simp only [genLMonoTy, mem_support_pick_iff, mem_support_pure_iff,
               mem_support_bind_iff]
    constructor
    · rintro (rfl | rfl | ⟨τ₁, h₁, τ₂, h₂, rfl⟩)
      · exact ⟨.bool, Nat.zero_le _⟩
      · exact ⟨.int, Nat.zero_le _⟩
      · have ⟨hs₁, hd₁⟩ := (ih τ₁).mp h₁
        have ⟨hs₂, hd₂⟩ := (ih τ₂).mp h₂
        refine ⟨.arrow hs₁ hs₂, ?_⟩
        change monoTyDepth (.tcons "arrow" [τ₁, τ₂]) ≤ n + 1
        rw [monoTyDepth.eq_1]; omega
    · intro ⟨hs, hd⟩
      cases hs with
      | bool  => left; rfl
      | int   => right; left; rfl
      | arrow hs₁ hs₂ =>
        rename_i τ₁ τ₂
        right; right
        have hd' : monoTyDepth (.tcons "arrow" [τ₁, τ₂]) ≤ n + 1 := hd
        rw [monoTyDepth.eq_1] at hd'
        exact ⟨τ₁, (ih τ₁).mpr ⟨hs₁, by omega⟩,
               τ₂, (ih τ₂).mpr ⟨hs₂, by omega⟩, rfl⟩

private theorem varsMatchingTarget_length_pos (vctx : VarCtx) (τ : LMonoTy)
    (x : HTIdent) (scheme : LTy) (subst : List LMonoTy)
    (hmem : (x, scheme) ∈ vctx) (hmatch : matchScheme scheme τ = some subst) :
    (varsMatchingTarget vctx τ).length > 0 := by
  have : x ∈ varsMatchingTarget vctx τ := by
    simp only [varsMatchingTarget, List.mem_filterMap]
    exact ⟨(x, scheme), hmem, by simp [hmatch, Option.isSome]⟩
  exact List.length_pos_of_mem this

private theorem opsMatchingTarget_length_pos (octx : OpSchemeCtx) (τ : LMonoTy)
    (name : String) (scheme : LTy) (subst : List LMonoTy)
    (hmem : (name, scheme) ∈ octx) (hmatch : matchScheme scheme τ = some subst) :
    (opsMatchingTarget octx τ).length > 0 := by
  have : name ∈ opsMatchingTarget octx τ := by
    simp only [opsMatchingTarget, List.mem_filterMap]
    exact ⟨(name, scheme), hmem, by simp [hmatch, Option.isSome]⟩
  exact List.length_pos_of_mem this

private theorem pickMatchingVar_complete (vctx : VarCtx) (τ : LMonoTy)
    (x : HTIdent) (scheme : LTy) (subst : List LMonoTy)
    (hmem : (x, scheme) ∈ vctx) (hmatch : matchScheme scheme τ = some subst)
    (hv : (varsMatchingTarget vctx τ).length > 0) :
    .fvar () x none ∈ SetGen.support (pickMatchingVar (G := SetGen.Set) vctx τ hv) := by
  simp only [pickMatchingVar, mem_support_bind_iff, mem_support_choose_iff,
             mem_support_pure_iff]
  have hx_mem : x ∈ varsMatchingTarget vctx τ := by
    simp only [varsMatchingTarget, List.mem_filterMap]
    exact ⟨(x, scheme), hmem, by simp [hmatch, Option.isSome]⟩
  obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hx_mem
  have : idx ≤ (varsMatchingTarget vctx τ).length - 1 := by omega
  refine ⟨⟨idx⟩, ⟨Nat.zero_le _, this⟩, ?_⟩
  simp [List.getD, List.getElem?_eq_getElem hidx_lt, hidx_eq]

private theorem pickMatchingOp_complete (octx : OpSchemeCtx) (τ : LMonoTy)
    (name : String) (scheme : LTy) (subst : List LMonoTy)
    (hmem : (name, scheme) ∈ octx) (hmatch : matchScheme scheme τ = some subst)
    (ho : (opsMatchingTarget octx τ).length > 0) :
    .op () ⟨name, ()⟩ none ∈ SetGen.support (pickMatchingOp (G := SetGen.Set) octx τ ho) := by
  simp only [pickMatchingOp, mem_support_bind_iff, mem_support_choose_iff,
             mem_support_pure_iff]
  have hn_mem : name ∈ opsMatchingTarget octx τ := by
    simp only [opsMatchingTarget, List.mem_filterMap]
    exact ⟨(name, scheme), hmem, by simp [hmatch, Option.isSome]⟩
  obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hn_mem
  have : idx ≤ (opsMatchingTarget octx τ).length - 1 := by omega
  refine ⟨⟨idx⟩, ⟨Nat.zero_le _, this⟩, ?_⟩
  simp [List.getD, List.getElem?_eq_getElem hidx_lt, hidx_eq]

set_option maxHeartbeats 3200000 in
/-- Completeness: every expression in the fragment is in the generator's support.

The proof proceeds by induction on the `InFragment` derivation. Each constructor
maps to a specific branch of the nested `pick` in the generator. The key helpers
are `pickMatchingVar_complete`, `pickMatchingOp_complete`, and `genLMonoTy_support`. -/
theorem genHTExpr_complete (vctx : VarCtx) (octx : OpSchemeCtx)
    (counter : Nat) (size : Nat) (τ : LMonoTy)
    (hτ : SimpleType τ) (e : HTExpr)
    (hfrag : InFragment size counter vctx octx e τ) :
    e ∈ SetGen.support (genHTExpr (G := SetGen.Set) vctx octx counter size τ) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════
-- §11. Quick Test
-- ═══════════════════════════════════════════════════════════════════════

open Std in
instance : ToFormat Unit where
  format _ := .nil

-- Test with some polymorphic operators in the context
-- e.g., "id" : ∀α. α → α
-- e.g., "eq" : ∀α. α → α → bool
def testOpCtx : OpSchemeCtx :=
  [ ("id", .forAll ["a"] (.arrow (.ftvar "a") (.ftvar "a")))
  , ("eq_op", .forAll ["a"] (.arrow (.ftvar "a") (.arrow (.ftvar "a") .bool)))
  ]

#guard_msgs(drop warning) in
#eval (for _ in [:5] do
  IO.println <| Std.format (← genHTExpr [] testOpCtx 0 2 .bool) |>.pretty : IO Unit)

end HT
