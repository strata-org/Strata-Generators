/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import StrataGenerators.GenSupport
import Basalt.Tuning

open Lean.Order RandomChoice

/-!
# Proving a tuned generator θ-invariant at `SPMF`

`@[tunable]` replaces each literal weight in a generator's `frequency` sites by a
`Tuning.weight θ i d` read in place. The two generators therefore have the same *branches* and
differ only in their weights, and `Tuning.weight` clamps every weight to 1 or more, so no runtime `θ`
can zero a branch out. The intended guarantee is that a tuning changes how often a branch is taken
and never whether it is reachable.

At `SPMF` that guarantee is an equality of **supports** and not of generators: a weight is part of the
mass, so `genFoo.tuned θ ≠ genFoo` as soon as `θ` differs from the defaults.

`Basalt.SPMF.Support` supplies the fact at one site:

* `SPMF.support_frequency_congr_weights` — two `frequency`s over the same branches, all weights
  positive on both sides, have the same support.

This file supplies what carries that fact from a site to a whole generator.

## The two shapes

**A site under `bind`, `map`, `dite` or `ite`.** `SPMF.support_bind` says the support of a bind is
determined by the support of its parts, so the support-level congruences below (`support_bind_congr`
and friends) push a site-level equation out through the surrounding `do` block. This is what replaces
the old `rw`-with-a-generator-equality recipe, which could rewrite anywhere in a term but is no longer
available.

**A recursive generator.**

* Structural recursion (`Nat.brecOn`, as in `genLMonoTy` and `genLExprBase`) and well-founded
  recursion (`WellFounded.fix`, as in `genCmd` and the `genStmt` block) are handled by ordinary
  induction on the recursion argument: the induction hypothesis *is* the support equation at the
  smaller index, and the congruences above consume it.
* `partial_fixpoint` (`Lean.Order.fix`) needs `support_fix_congr_of_pointwise` below, because there is
  no argument to induct on. Fixpoint induction replaces it.
-/

namespace SPMF

/-! ## Support congruences

Each lemma says that a combinator's support is a function of the supports of its parts. Together they
let a site-level support equation travel out to the top of a `do` block. -/

/-- The support of a `bind` depends only on the support of the first generator and the supports of the
continuation's results. -/
theorem support_bind_congr {x y : SPMF α} {f g : α → SPMF β}
    (hx : x.support = y.support) (hf : ∀ a, (f a).support = (g a).support) :
    (x >>= f).support = (y >>= g).support := by
  ext b
  simp only [mem_support_bind_iff]
  constructor
  · rintro ⟨a, ha, hb⟩; exact ⟨a, hx ▸ ha, hf a ▸ hb⟩
  · rintro ⟨a, ha, hb⟩; exact ⟨a, hx ▸ ha, (hf a).symm ▸ hb⟩

/-- The special case of `support_bind_congr` where only the continuation changes. This is the shape a
tuning takes when the site sits after one or more draws. -/
theorem support_bind_congr_right {x : SPMF α} {f g : α → SPMF β}
    (hf : ∀ a, (f a).support = (g a).support) :
    (x >>= f).support = (x >>= g).support :=
  support_bind_congr rfl hf

/-- The support of a `map` depends only on the support of its argument. -/
theorem support_map_congr {x y : SPMF α} {f : α → β} (h : x.support = y.support) :
    (f <$> x).support = (f <$> y).support := by
  ext b; simp only [mem_support_map_iff, h]

/-- The support of a `dite` is decided branch by branch. -/
theorem support_dite_congr {p : Prop} [Decidable p] {t t' : p → SPMF α} {e e' : ¬p → SPMF α}
    (ht : ∀ h, (t h).support = (t' h).support) (he : ∀ h, (e h).support = (e' h).support) :
    (dite p t e).support = (dite p t' e').support := by
  by_cases hp : p <;> simp [hp, ht, he]

/-- The support of an `ite` is decided branch by branch. -/
theorem support_ite_congr {p : Prop} [Decidable p] {t t' e e' : SPMF α}
    (ht : t.support = t'.support) (he : e.support = e'.support) :
    (ite p t e).support = (ite p t' e').support := by
  by_cases hp : p <;> simp [hp, ht, he]

/-- The support of a `pick` is the union of the two branches' supports. -/
theorem support_pick_congr {x x' y y' : SPMF α}
    (hx : x.support = x'.support) (hy : y.support = y'.support) :
    (pick (fun () => x) (fun () => y)).support
      = (pick (fun () => x') (fun () => y')).support := by
  rw [support_pick, support_pick, hx, hy]

/-- The support of `optionGen` depends only on the support of its payload. `optionGen` splits on a
rational `coin`, which no tuning can address, so a site inside the payload has to travel out through
this lemma. -/
theorem support_optionGen_congr {g g' : SPMF α} (h : g.support = g'.support) :
    (optionGen g).support = (optionGen g').support := by
  ext o
  simp only [mem_support_optionGen_iff, h]

/-- The support of `oneOf` depends only on the supports of its branches, branch by branch. -/
theorem support_oneOf_congr {gs gs' : List (Unit → SPMF α)} (hne : gs ≠ []) (hne' : gs' ≠ [])
    (h : List.Forall₂ (fun g g' => (g ()).support = (g' ()).support) gs gs') :
    (oneOf gs hne).support = (oneOf gs' hne').support := by
  ext a
  simp only [mem_support_oneOf_iff]
  constructor
  · rintro ⟨g, hg, ha⟩
    obtain ⟨g', hg', hrel⟩ := forall₂_exists_of_mem h hg
    exact ⟨g', hg', hrel ▸ ha⟩
  · rintro ⟨g', hg', ha⟩
    obtain ⟨g, hg, hrel⟩ := forall₂_exists_of_mem h.flip hg'
    exact ⟨g, hg, hrel ▸ ha⟩
where
  /-- A `Forall₂` relates each member of one list to some member of the other. -/
  forall₂_exists_of_mem {α β : Type _} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
      (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
    induction h with
    | nil => cases ha
    | @cons x y xs ys hxy hrest ih =>
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨y, List.mem_cons_self, hxy⟩
      · obtain ⟨b, hb, hab⟩ := ih ha'
        exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- **A `frequency` whose branches are only support-equal.** `support_frequency_congr_weights` needs
the branch lists to agree on the nose, which is the shape a tuning has at a *non-recursive* site. Under
a recursion the branches mention the recursive call, and the two sides' recursive calls agree only in
support, so the pairwise form is the one that applies. -/
theorem support_frequency_congr_branches {gs gs' : List (Nat × (Unit → SPMF α))}
    (hpos : ∀ p ∈ gs, 0 < p.1) (hpos' : ∀ p ∈ gs', 0 < p.1)
    (hrel : List.Forall₂ (fun p q => (p.2 ()).support = (q.2 ()).support) gs gs')
    (h : 0 < List.sum (List.map Prod.fst gs)) (h' : 0 < List.sum (List.map Prod.fst gs')) :
    (frequency gs h).support = (frequency gs' h').support := by
  ext a
  simp only [mem_support_frequency_iff]
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    obtain ⟨⟨w', g'⟩, hmem', hrel'⟩ := support_oneOf_congr.forall₂_exists_of_mem hrel hmem
    exact ⟨w', g', hmem', hpos' _ hmem', hrel' ▸ ha⟩
  · rintro ⟨w, g, hmem, _, ha⟩
    obtain ⟨⟨w', g'⟩, hmem', hrel'⟩ := support_oneOf_congr.forall₂_exists_of_mem hrel.flip hmem
    exact ⟨w', g', hmem', hpos _ hmem', hrel' ▸ ha⟩

/-- The support of `List.mapM` depends only on the supports of the results. This is what carries a
support equation into the argument list of an application spine — `genIndir` and `genIndirPolyCore`
draw each argument with a `mapM` over the argument generator. -/
theorem support_mapM_congr {ι : Type u} {α : Type u} {f g : ι → SPMF α}
    (hfg : ∀ i, (f i).support = (g i).support) :
    ∀ l : List ι, (l.mapM (m := SPMF) f).support = (l.mapM (m := SPMF) g).support := by
  intro l
  induction l with
  | nil => simp only [List.mapM_nil]
  | cons a as ih =>
    simp only [List.mapM_cons]
    exact support_bind_congr (hfg a) (fun _ => support_bind_congr ih (fun _ => rfl))

/-! ## Fixpoint induction for a support equation

`Lean.Order.fix` is the least upper bound of the transfinite iteration of its functional, so a claim
about `fix F` follows from `Lean.Order.fix_induct` once the claim is *admissible*: it must pass from
the members of a chain to the chain's supremum. A support inclusion is admissible, because
`SPMF.mem_support_csup` says the support of a supremum is the union of the supports. -/

/-- A support inclusion is admissible, so fixpoint induction can prove one. -/
theorem admissible_support_subset {γ : Type u} (T : Set γ) :
    admissible (fun (s : SPMF γ) => s.support ⊆ T) := by
  intro c hc h a ha
  obtain ⟨s, hcs, has⟩ := (mem_support_csup hc).mp ha
  exact h s hcs has

/-- **θ-invariance for a `partial_fixpoint` generator.**

`F` is the functional of the tuned generator and `G` the functional of the untuned one. The two
hypotheses are exactly what a tuning gives:

* `hpt` — at *the same* argument, the two functionals have the same support. This is the site-level
  fact: the bodies differ only in `frequency` weights, and
  `SPMF.support_frequency_congr_weights` sees through that. Note that `x` is shared, so proving this
  needs no induction — just the congruences above down to each site.
* `hmono` — `G`'s support is monotone in the support of its argument. Every combinator a generator is
  built from has this property, so the proof walks the body once.

`F` inherits `hmono` from `G` through `hpt`, which is why only one of the two is required. -/
theorem support_fix_congr_of_pointwise {ι : Sort u} {γ : ι → Type v}
    {F G : (∀ i, SPMF (γ i)) → (∀ i, SPMF (γ i))}
    (hF : monotone F) (hG : monotone G)
    (hpt : ∀ x i, (F x i).support = (G x i).support)
    (hmono : ∀ x y : (∀ i, SPMF (γ i)), (∀ i, (x i).support ⊆ (y i).support) →
      ∀ i, (G x i).support ⊆ (G y i).support) :
    ∀ i, (fix F hF i).support = (fix G hG i).support := by
  -- Each direction is one fixpoint induction. The motive is a support inclusion into the *other*
  -- fixpoint, and the step unrolls that other fixpoint once with `fix_eq`.
  have key : ∀ (F' G' : (∀ i, SPMF (γ i)) → (∀ i, SPMF (γ i))) (hF' : monotone F')
      (hG' : monotone G'), (∀ x i, (F' x i).support = (G' x i).support) →
      (∀ x y : (∀ i, SPMF (γ i)), (∀ i, (x i).support ⊆ (y i).support) →
        ∀ i, (G' x i).support ⊆ (G' y i).support) →
      ∀ i, (fix F' hF' i).support ⊆ (fix G' hG' i).support := by
    intro F' G' hF' hG' hpt' hmono'
    refine fix_induct hF' (motive := fun x => ∀ i, (x i).support ⊆ (fix G' hG' i).support) ?_ ?_
    · exact admissible_pi_apply (fun i (s : SPMF (γ i)) => s.support ⊆ (fix G' hG' i).support)
        (fun i => admissible_support_subset _)
    · intro x hx i
      calc (F' x i).support
          = (G' x i).support := hpt' x i
        _ ⊆ (G' (fix G' hG') i).support := hmono' x _ hx i
        _ = (fix G' hG' i).support := by rw [← fix_eq hG']
  intro i
  refine Set.Subset.antisymm (key F G hF hG hpt hmono i) (key G F hG hF ?_ ?_ i)
  · intro x i; exact (hpt x i).symm
  · intro x y hxy i; exact (hpt x i) ▸ (hpt y i) ▸ hmono x y hxy i

/-- **θ-invariance for a well-founded recursive generator.** Both sides are one `WellFounded.fix` over
the *same* accessibility proof — `@[tunable]` rewrites the elaborated body and never re-runs the
equation compiler — so the two differ only in their step functions. Well-founded induction then gives
the recursive calls' support equation as its induction hypothesis, and `h` consumes it. -/
theorem support_wellFounded_fix_congr {ι : Sort u} {r : ι → ι → Prop} (hwf : WellFounded r)
    {γ : ι → Type v} {F F' : ∀ x, (∀ y, r y x → SPMF (γ y)) → SPMF (γ x)}
    (h : ∀ x (g g' : ∀ y, r y x → SPMF (γ y)),
          (∀ y (hy : r y x), (g y hy).support = (g' y hy).support) →
          (F x g).support = (F' x g').support) :
    ∀ x, (WellFounded.fix hwf F x).support = (WellFounded.fix hwf F' x).support := by
  intro x
  induction x using hwf.induction with
  | _ x ih =>
    rw [WellFounded.fix_eq, WellFounded.fix_eq]
    exact h x _ _ (fun y hy => ih y hy)

end SPMF

/-! ## A tactic for the per-branch obligations

The congruences above are structural, so applying them to a generator's body is mechanical: descend
through every `bind`, `dite`, `ite`, `map`, `pick`, `oneOf` and `frequency`, and finish each leaf
either by reflexivity (the leaf does not mention the recursive call) or with the induction hypothesis.
`support_congr` does exactly that. Pass the induction hypotheses as arguments; they are tried at every
leaf. -/

open Lean.Parser.Tactic in
/-- Discharge a support equation between two generators that differ only in `frequency` weights and in
their recursive occurrences, by descending through the combinators. The given terms (typically the
induction hypotheses) are tried at each leaf. -/
syntax "support_congr" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| support_congr) => `(tactic| support_congr [])
  | `(tactic| support_congr [$hs,*]) =>
    `(tactic|
      repeat' first
        | rfl
        -- `support_frequency_congr_branches` subsumes `support_frequency_congr_weights`: an
        -- unchanged branch is closed by `rfl` inside the `List.Forall₂` walk below.
        | refine SPMF.support_frequency_congr_branches ?_ ?_ ?_ _ _
        | refine SPMF.support_bind_congr ?_ (fun _ => ?_)
        | refine SPMF.support_dite_congr (fun _ => ?_) (fun _ => ?_)
        | refine SPMF.support_ite_congr ?_ ?_
        | refine SPMF.support_pick_congr ?_ ?_
        | refine SPMF.support_map_congr ?_
        | refine SPMF.support_mapM_congr (fun _ => ?_) _
        | refine SPMF.support_optionGen_congr ?_
        | refine SPMF.support_oneOf_congr _ _ ?_
        | refine List.Forall₂.cons ?_ ?_
        | exact List.Forall₂.nil
        | first $[| exact $hs ..]*
        | first $[| exact $hs _ _]*
        | first $[| exact $hs _]*
        -- A `mutual` block's induction hypothesis is stated with `HEq`, because its members return
        -- different types; `eq_of_heq` puts it back at the support equation of one member.
        | first $[| exact eq_of_heq ($hs _ _)]*
        -- Last resort: a `frequency`'s positivity side condition. Shaped as `∀ p ∈ gs, 0 < p.1`, so
        -- the `intro` guard keeps this from firing on a `List.Forall₂` goal.
        | (intro _ hmem; fin_cases hmem <;> simp [Tuning.weight_pos])
        | (intro _ hmem; revert hmem; simp [Tuning.weight_pos]))
