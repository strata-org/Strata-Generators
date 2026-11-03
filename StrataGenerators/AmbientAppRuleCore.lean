import StrataGenerators.AmbientAppRule
import Strata.Languages.Core.Factory

/-!
# The app-rule comparison over Strata Core's factory

`AmbientAppRule.lean` proves its results for an arbitrary signature `sig`. Here `sig` is
`coreSig`: every monomorphic function of `Core.Factory`, with its Core type translated to the
toy STLC's types by `Ty.ofLMonoTy`. Like `coreMonoOps` (`HasTypeAGen/Core.lean`), the list is
derived from the factory itself, so it cannot drift from the functions Core defines.

The one side condition of the general results, that every argument type is a base type, holds
for the whole factory (`coreSig_args_base`: Core's factory is first order). Hence, for every
monomorphic Core factory function `f` of arity `m ≥ 1`:

* `core_palka_ratio_ge`: with `k` uniformly drawn base types, Pałka et al.'s rule calls `f` at
  least `kᵐ · palkaFloor coreSig m` times as often as the STLC application rule;
* `core_separation`: the STLC rule's probability of calling `f` tends to `0` as the number of base
  types grows, Pałka et al.'s stays `≥ palkaFloor coreSig m`, and from some `N` on Pałka et al.'s
  rule is strictly more frequent.

`substr_separation` is the instance for the three-argument `Str.Substr : String → Int → Int →
String`.

**Scope.** The generators are still the toy `genExpr`/`genExprP`, not `genLExprBase`/`genLExpr`:
those already contain the Indir rules (Pałka et al.'s) at every depth, so Strata has no STLC-only
generator to compare against. Polymorphic factory functions (IndirPoly) are excluded, as the toy
has no type variables.

**Axioms.** `coreSig_args_base` is checked with `native_decide`. This adds no axiom beyond those
`Core.Factory` already depends on: its own `name_nodup` field is proved by `native_decide`, so
every statement that mentions the factory already depends on `Lean.ofReduceBool`.
-/

namespace StrataGenerators.AmbientApp

open scoped ENNReal
open SPMF (prob)
open Lambda

/-- A Core type as a toy type: arrows, `int`, `string`, `bool` and bitvectors map to their toy
counterparts, and every other Core type (`real`, `regex`, `Map int bool`, …) to the opaque base
type `.other`. -/
def Ty.ofLMonoTy : LMonoTy → Ty
  | .tcons "arrow" [a, b] => .arrow (ofLMonoTy a) (ofLMonoTy b)
  | .tcons "int" [] => .int
  | .tcons "string" [] => .str
  | .tcons "bool" [] => .bool
  | .bitvec w => .bv w
  | t => .other t

/-- Every monomorphic function of `Core.Factory`, as an ambient function: its name, and its
curried type `input₁ → ⋯ → inputₘ → output`. -/
def coreSig : List Fn :=
  Core.Factory.toArray.toList.filterMap fun f =>
    if f.typeArgs.isEmpty then
      some ⟨f.name.name, Ty.ofLMonoTy (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))⟩
    else none

/-- The Boolean test behind `Ty.IsBase`. -/
def Ty.isBase : Ty → Bool
  | .arrow _ _ => false
  | _ => true

theorem Ty.isBase_iff (τ : Ty) : τ.isBase = true ↔ τ.IsBase := by
  cases τ <;> simp [Ty.isBase, Ty.IsBase]

/-- **Core's factory is first order**: no monomorphic factory function takes a function. -/
theorem coreSig_args_base : ∀ f ∈ coreSig, ∀ a ∈ f.ty.args, a.IsBase := by
  have h : (coreSig.all fun f => f.ty.args.all Ty.isBase) = true := by native_decide
  simp only [List.all_eq_true] at h
  exact fun f hf a ha => (Ty.isBase_iff a).1 (h f hf a ha)

/-- **Ratio, over Core's factory.** For every monomorphic Core factory function
`f : a₁ → ⋯ → aₘ → r` and `k ≥ 2` uniformly drawn base types, Pałka et al.'s rule calls `f` at
least `kᵐ · palkaFloor coreSig m` times as often as the STLC application rule. -/
theorem core_palka_ratio_ge (n : Nat) (Γ : List Ty) {f : Fn} (hmem : f ∈ coreSig)
    {k : Nat} (hk : 2 ≤ k) :
    (k : ℝ≥0∞) ^ f.ty.args.length * palkaFloor coreSig f.ty.args.length
        * prob (genExpr (genTyUniform k) coreSig (n + 1) Γ f.ty.res) (CallOf f)
      ≤ prob (genExprP (genTyUniform k) coreSig (n + 1) Γ f.ty.res) (CallOf f) :=
  palka_ratio_ge coreSig n Γ hmem (coreSig_args_base f hmem) hk

/-- **Separation, over Core's factory.** For every monomorphic Core factory function `f` with at
least one argument, as the number of base types grows: the STLC rule's probability of calling
`f` drops below any `ε > 0`; Pałka et al.'s stays at least `palkaFloor coreSig m`; and from some
`N` on, Pałka et al.'s rule is strictly more frequent. -/
theorem core_separation (n : Nat) (Γ : List Ty) {f : Fn} (hmem : f ∈ coreSig)
    (harity : f.ty.args ≠ []) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ numBaseTypes ≥ N,
        prob (genExpr (genTyUniform numBaseTypes) coreSig n Γ f.ty.res) (CallOf f) < ε)
      ∧ (∀ numBaseTypes, palkaFloor coreSig f.ty.args.length ≤
          prob (genExprP (genTyUniform numBaseTypes) coreSig (n + 1) Γ f.ty.res) (CallOf f))
      ∧ ∃ N, ∀ numBaseTypes ≥ N,
          prob (genExpr (genTyUniform numBaseTypes) coreSig (n + 1) Γ f.ty.res) (CallOf f)
            < prob (genExprP (genTyUniform numBaseTypes) coreSig (n + 1) Γ f.ty.res)
                (CallOf f) :=
  default_vs_palka_separation coreSig n Γ hmem harity (coreSig_args_base f hmem)

/-- `Str.Substr : String → Int → Int → String`, as it appears in `coreSig`. -/
def substrFn : Fn := ⟨"Str.Substr", .arrow .str (.arrow .int (.arrow .int .str))⟩

theorem substrFn_mem : substrFn ∈ coreSig := by
  have h : coreSig.contains substrFn = true := by native_decide
  simpa using h

/-- A three-argument instance: `Str.Substr`. With `k` uniform base types, the STLC rule must
guess three argument types (`≤ 1/k³`), while Pałka et al.'s rule stays above
`palkaFloor coreSig 3`. -/
theorem substr_separation (n : Nat) (Γ : List Ty) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ numBaseTypes ≥ N,
        prob (genExpr (genTyUniform numBaseTypes) coreSig n Γ .str) (CallOf substrFn) < ε)
      ∧ (∀ numBaseTypes, palkaFloor coreSig 3 ≤
          prob (genExprP (genTyUniform numBaseTypes) coreSig (n + 1) Γ .str) (CallOf substrFn))
      ∧ ∃ N, ∀ numBaseTypes ≥ N,
          prob (genExpr (genTyUniform numBaseTypes) coreSig (n + 1) Γ .str) (CallOf substrFn)
            < prob (genExprP (genTyUniform numBaseTypes) coreSig (n + 1) Γ .str)
                (CallOf substrFn) :=
  core_separation n Γ substrFn_mem (by simp [substrFn, Ty.args])

end StrataGenerators.AmbientApp
