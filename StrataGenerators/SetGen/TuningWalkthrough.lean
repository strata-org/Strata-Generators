/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import StrataGenerators.SetGen
import Basalt.Tuning.Attr
import Basalt.GenStats

open RandomChoice
open scoped SetGen.Set

/-!
# How to tune a generator: the end-user walkthrough

Six steps, each one compiled below, taking a generator with hard-coded branch weights and ending
with a runtime-selectable weighting plus a proof that selecting one cannot change what the generator
can produce.

`StrataGenerators.SetGen.TuningExamples` is the reference for *what the attribute emits* (site
tables, error cases, every recursion form); `StrataGenerators.SetGen.TuningPrototypes` applies the
same steps to this repo's shipping generators. This file is the "how do I actually do it" version.

| step | what you write |
|---|---|
| 1 | `@[tunable]` on the generator — or `attribute [tunable] genFoo` for someone else's |
| 2 | `#eval genFoo.sites` / `#eval genFoo.defaults`, to find the flat index of the branch you care about |
| 3 | a `Tuning` — a literal, or `defaults.schedules.set!` to move one branch |
| 4 | `genFoo.tuned θ args` wherever you wrote `genFoo args` |
| 5 | draw from it, and check the distribution actually moved |
| 6 | a θ-invariance theorem, so no existing proof has to change |

The one thing to know before starting: **weights are `Nat`s, and the attribute needs to see them.**
Each branch weight must be a literal, and the branch list must be a literal list — not a `let`-bound
variable. Everything else (recursion form, where the definition lives, how many sites it has) is
free.
-/

namespace TuningWalkthrough

/-- The values our example generator produces. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree
deriving Repr, DecidableEq

/-- Number of constructors in a tree. Used in step 5 to observe the distribution. -/
def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => 1 + l.size + r.size

/-! ## Step 1 — tag the generator

Here is an ordinary generator. The `1 : 2` split between `leaf` and `node` is baked into the source:
changing it means editing this file and recompiling.

```lean
def genTree [Gen G] (depth : Nat) : G Tree :=
  frequency [
    (1, fun _ => pure .leaf),
    (2, fun _ => do
      let l ← genTree (depth + 1)
      let r ← genTree (depth + 1)
      return .node l r)
  ] (by simp)
partial_fixpoint
```

Adding `@[tunable]` is the entire change to the generator. Note what you do *not* have to do: no
threading a weight parameter through the recursion, no rewriting the `frequency` call, no changing
the type. -/

@[tunable]
def genTree [Gen G] (depth : Nat) : G Tree :=
  frequency [
    (1, fun _ => pure .leaf),
    (2, fun _ => do
      let l ← genTree (depth + 1)
      let r ← genTree (depth + 1)
      return .node l r)
  ] (by simp)
partial_fixpoint

/-! The attribute emits four declarations alongside it:

* `genTree.tuned (θ : Tuning) …` — the same generator, reading its weights from `θ`;
* `genTree.defaults : Tuning` — the weights as written above;
* `genTree.sites : Array Site` — where the knobs are;
* `genTree.tuned_defaults` — a proof that the two agree at `defaults`.

If the generator is someone else's and you would rather not touch their file, tag it from yours —
this works on any `def`, in any module:

```lean
attribute [tunable] genPrecondition   -- see TuningPrototypes §1
```
-/

/-! ## Step 2 — find the knob

A `Tuning` is one flat array of weight schedules covering *every* site in the generator, so to move a
particular branch you need its flat index. `sites` is the map. -/

/-- info: #[{ name := `TuningWalkthrough.genTree.site0, offset := 0, arity := 2, holes := #[0, 2] }] -/
#guard_msgs in
#eval genTree.sites

/-- info: { schedules := #[(1, 0), (2, 0)] } -/
#guard_msgs in
#eval genTree.defaults

/-! Read that as: one site, starting at flat index `offset = 0`, with `arity = 2` branches — so index
`0` is `leaf` and index `1` is `node`, in source order. `holes` says how many recursive calls each
branch makes (`#[0, 2]`: none from `leaf`, two from `node`), which is what tells you whether raising a
weight risks non-termination.

With more than one `frequency`, sites are numbered outside-in and their blocks are laid out
end-to-end, so `offset` is what turns "branch `j` of site `i`" into a flat index. -/

@[tunable]
def genTwoSite [Gen G] (depth : Nat) : G (Tree × Tree) := do
  let l ← frequency [
    (1, fun _ => pure Tree.leaf),
    (3, fun _ => genTree (depth + 1))
  ] (by simp)
  let r ← frequency [
    (1, fun _ => pure Tree.leaf),
    (1, fun _ => genTree (depth + 1)),
    (1, fun _ => pure (Tree.node .leaf .leaf))
  ] (by simp)
  pure (l, r)

/--
info: #[{ name := `TuningWalkthrough.genTwoSite.site0, offset := 0, arity := 2, holes := #[0, 0] },
  { name := `TuningWalkthrough.genTwoSite.site1, offset := 2, arity := 3, holes := #[0, 0, 0] }]
-/
#guard_msgs in
#eval genTwoSite.sites

/-- Five branches over two sites, so a `Tuning` for this generator has five schedules: indices `0..1`
    are the first `frequency`, indices `2..4` the second. -/
example : genTwoSite.defaults = ⟨#[(1, 0), (3, 0), (1, 0), (1, 0), (1, 0)]⟩ := rfl

/-! ## Step 3 — write a `Tuning`

An entry is a pair `(a, b)`, denoting the depth-indexed weight `w(d) = max a 1 + b · d`, where `d` is
the value of the generator's `depth` binder at that site. A constant weight is `(a, 0)`. (If the
binder is called something else, say so once: `@[tunable (depth := lvl)]`. With no such binder in
scope, every site reads at depth `0` and only the `a` component matters.)

Three idioms, in increasing order of how much they respect the rest of the generator. -/

/-- **Spell it out.** Fine for a small generator; note that you are restating *every* branch, so this
    silently goes stale if a branch is added to the source. -/
def leafHeavy : Tuning := ⟨#[(5, 0), (1, 0)]⟩

/-- **Move one branch, keep the rest.** Start from `defaults` and `set!` the index you looked up in
    step 2. This is the idiom to prefer: it does not restate weights you did not mean to change. -/
def nodeHeavy : Tuning :=
  { schedules := genTree.defaults.schedules.set! 1 (8, 0) }

/-- **Let a weight grow with depth.** The point of the `b` component: `w_leaf(d) = 1 + 8·d` while
    `w_node(d) = 2`, so recursion is likely at the root and is forced closed a few levels down.

    This is how you get a generator that explores widely near the root without diverging. Expressing
    decay as *growth of the base case* rather than shrinkage of the recursive one is deliberate — a
    weight is clamped to `≥ 1` (`Tuning.weight`) and so can never reach `0`, which is what keeps the
    support intact no matter how aggressive the schedule (step 6). -/
def decaying : Tuning := ⟨#[(1, 8), (2, 0)]⟩

/-- A zero in a runtime `θ` is therefore harmless — it reads as `1`, not as a pruned branch. -/
example (i d : Nat) :
    Tuning.weight ⟨#[(0, 0), (0, 0)]⟩ i d = Tuning.weight ⟨#[(1, 0), (1, 0)]⟩ i d := by
  simp only [Tuning.weight]
  rcases i with _ | _ | i <;> simp

/-! ## Step 4 — call the tuned generator

`genTree.tuned θ` has exactly `genTree`'s type after the `θ`, so it drops into any position the
original occupied — including at a different `Gen` instance. `θ` is an ordinary runtime value: it can
come from a config file, a search loop, or a command-line flag, and evaluating a new candidate
weighting costs a function call rather than a recompile. -/

/-- A generator parameterized by its weighting, at whatever monad the caller wants. -/
def genTreeAt [Gen G] (θ : Tuning) (depth : Nat) : G Tree := genTree.tuned θ depth

/-! ## Step 5 — check the distribution actually moved

`Basalt.GenStats` provides a seeded, pure interpretation (`StatGen`), so this is reproducible and can
be *asserted* rather than eyeballed. `runDraws` fixes the seed by default; `#genstats` (from
`Basalt.GenStats.Command`) prints the same information as a human-readable panel instead.

`fuel` bounds the number of random choices per draw, and a draw that exceeds it comes back as
`Error.outOfFuel` rather than a value. Keep it small here: an unbounded budget lets a supercritical
weighting nest deep enough to exhaust the *interpreter's* C stack, which is a crash rather than a
recoverable failure. (Basalt raises `--tstack` in its own test library for this reason.) -/

/-- 200 seeded draws under the weighting `θ`, each capped at 60 random choices. -/
def draws (θ : Tuning) : Array (Except GenStats.Error (Tree × Nat)) :=
  GenStats.runDraws (genTree.tuned θ 0 : GenStats.StatGen Tree) { draws := 200, fuel := 60 }

/-- Total constructors produced over those draws; a failed draw contributes nothing. -/
def totalSize (θ : Tuning) : Nat :=
  (draws θ).foldl (fun n r => match r with | .ok (t, _) => n + t.size | _ => n) 0

/-- How many of those draws ran out of budget. -/
def outOfFuel (θ : Tuning) : Nat :=
  (draws θ).foldl (fun n r => match r with | .ok _ => n | _ => n + 1) 0

/-! The three usable weightings order exactly as intended — leaf-heavy smallest, and a *slower* decay
coefficient giving bigger trees. All three come from one compiled generator, selected at runtime,
with no recompilation between them. Concretely: 288, 604 and 1302 constructors, and no draw fails. -/

#guard totalSize leafHeavy < totalSize decaying
#guard totalSize decaying < totalSize ⟨#[(1, 1), (2, 0)]⟩
#guard outOfFuel leafHeavy == 0 && outOfFuel decaying == 0

/-! `nodeHeavy` is the cautionary one. It raises the recursive branch to weight 8 against `leaf`'s 1
with no decay to stop it, so the mean number of offspring is `2 · 8/9 > 1`: the recursion is
supercritical and 175 of the 200 draws exhaust their budget without producing a tree. This is the
failure mode `holes` in step 2 was warning about — `#[0, 2]` says branch 1 recurses twice, so its
weight is the one that has to stay under control. The fix is a growth coefficient, as in `decaying`,
not a smaller constant.

Note which way the sizes come out: `nodeHeavy` asks for *more* recursion and gets 39 constructors
against `decaying`'s 604, because most of its draws die before returning anything. A weighting that
looks more aggressive on paper can generate strictly less. -/

#guard outOfFuel nodeHeavy > 150
#guard totalSize nodeHeavy < totalSize decaying

/-! ## Step 6 — check that nothing else broke

Two facts, both free.

First, the defaults *are* the generator as written — `tuned_defaults` is `Eq.refl`, checked by the
kernel — so adopting tuning cannot change the behavior you already had. -/

example (depth : Nat) :
    (genTree.tuned genTree.defaults depth : SetGen.Set Tree) = genTree depth :=
  genTree.tuned_defaults depth

/-! Second, and the reason to care: at the `Set` interpretation, *every* `θ` denotes the same
generator, so no weighting can change what is reachable. `unseal` is needed because
`partial_fixpoint` definitions are irreducible; see `StrataGenerators.SetGen.Tuning` for the recipe
and for the non-recursive and buried-in-a-`do`-block variants. -/

unseal genTree genTree.tuned

theorem genTree_tuned_eq (θ : Tuning) :
    (genTree.tuned θ : Nat → SetGen.Set Tree) = genTree := by
  apply SetGen.fix_congr
  funext f depth
  apply SetGen.frequency_congr_weights
  · rfl
  all_goals simp [Tuning.weight_pos]

/-- So a soundness-and-completeness result proved once for the untuned generator holds of every
    tuning of it, and the proof does not need to know what the property is. That is the whole payoff:
    tuning is a distribution change, never a language change. -/
example (θ : Tuning) (depth : Nat) (P : Tree → Prop)
    (h : SetGen.IsSoundAndComplete (genTree depth : SetGen.Set Tree) P) :
    SetGen.IsSoundAndComplete (genTree.tuned θ depth : SetGen.Set Tree) P :=
  SetGen.IsSoundAndComplete.of_support_eq (by rw [genTree_tuned_eq]) h

end TuningWalkthrough
