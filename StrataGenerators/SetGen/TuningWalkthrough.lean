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

This file takes a generator with hard-coded branch weights through six steps. At the end the
weighting is selectable at run time, and a proof shows that no weighting changes what the generator
can produce. Each step compiles below.

`StrataGenerators.SetGen.TuningExamples` is the reference for *what the attribute emits*: the site
tables, the error cases and every recursion form. `StrataGenerators.SetGen.TuningPrototypes` applies
the same steps to this repo's shipping generators. This file is the practical guide.

| step | what you write |
|---|---|
| 1 | `@[tunable]` on the generator, or `attribute [tunable] genFoo` for one you do not own |
| 2 | `#eval genFoo.sites` and `#eval genFoo.defaults`, to find the flat index of your branch |
| 3 | a `Tuning`: a literal, or `defaults.schedules.set!` to move one branch |
| 4 | `genFoo.tuned θ args` wherever you wrote `genFoo args` |
| 5 | a draw from it, and a check that the distribution moved |
| 6 | a θ-invariance theorem, so that no existing proof has to change |

Know one thing before you start: **a weight is a `Nat`, and the attribute must see it.** Each branch
weight must be a literal. The branch list must be a literal list rather than a `let`-bound variable.
Everything else is free: the recursion form, the module the definition lives in, and the number of
sites.
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

/-! ## Step 1: tag the generator

Here is an ordinary generator. The source fixes the 1 to 2 split between `leaf` and `node`, so a
change to that split means an edit to this file and a recompile.

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

`@[tunable]` is the entire change to the generator. Note what you do *not* have to do. You do not
thread a weight parameter through the recursion. You do not rewrite the `frequency` call. You do not
change the type. -/

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

/-! The attribute emits four declarations next to it:

* `genTree.tuned (θ : Tuning) …` is the same generator, and it reads its weights from `θ`.
* `genTree.defaults : Tuning` holds the weights as written above.
* `genTree.sites : Array Site` says where the knobs are.
* `genTree.tuned_defaults` proves that the two generators agree at `defaults`.

If you do not own the generator and would rather not touch its file, tag it from yours. This works on
any `def`, in any module:

```lean
attribute [tunable] genPrecondition   -- see TuningPrototypes §1
```
-/

/-! ## Step 2: find the knob

A `Tuning` is one flat array of weight schedules, and it covers *every* site in the generator. To move
one branch you therefore need its flat index, and `sites` is the map. -/

/-- info: #[{ name := `TuningWalkthrough.genTree.site0, offset := 0, arity := 2, holes := #[0, 2] }] -/
#guard_msgs in
#eval genTree.sites

/-- info: { schedules := #[(1, 0), (2, 0)] } -/
#guard_msgs in
#eval genTree.defaults

/-! Read that as one site that starts at flat index 0 and has 2 branches. Index 0 is therefore `leaf`
and index 1 is `node`, in source order. `holes` gives the number of recursive calls that each branch
makes: none from `leaf`, and two from `node`. That is what tells you whether a raised weight risks
non-termination.

With more than one `frequency`, the attribute numbers the sites outside-in and lays their blocks out
end to end. `offset` is what turns "branch `j` of site `i`" into a flat index. -/

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

/-- Five branches over two sites, so a `Tuning` for this generator holds five schedules. Indices 0 and
    1 are the first `frequency`, and indices 2 to 4 are the second. -/
example : genTwoSite.defaults = ⟨#[(1, 0), (3, 0), (1, 0), (1, 0), (1, 0)]⟩ := rfl

/-! ## Step 3: write a `Tuning`

An entry is a pair `(a, b)`, and it denotes the depth-indexed weight `w(d) = max a 1 + b · d`. Here `d`
is the value of the generator's `depth` binder at that site, and a constant weight is `(a, 0)`. If the
binder has another name, say so once with `@[tunable (depth := lvl)]`. With no such binder in scope,
every site reads at depth 0 and only the `a` component matters.

There are three idioms. Each one respects the rest of the generator more than the one before it. -/

/-- **Spell it out.** This is fine for a small generator. It restates *every* branch, so it goes stale
    without warning when somebody adds a branch to the source. -/
def leafHeavy : Tuning := ⟨#[(5, 0), (1, 0)]⟩

/-- **Move one branch and keep the rest.** Start from `defaults`, and `set!` the index you looked up in
    step 2. Prefer this idiom, because it does not restate a weight you did not mean to change. -/
def nodeHeavy : Tuning :=
  { schedules := genTree.defaults.schedules.set! 1 (8, 0) }

/-- **Let a weight grow with depth.** This is what the `b` component is for. Here
    `w_leaf(d) = 1 + 8·d` and `w_node(d) = 2`, so recursion is likely at the root and closes a few
    levels down.

    This is how to write a generator that explores widely near the root and does not diverge. The decay
    is expressed as *growth of the base case* rather than as shrinkage of the recursive one, and that is
    deliberate. `Tuning.weight` clamps a weight to 1 or more, so no weight reaches 0. The support
    therefore stays intact however aggressive the schedule is, as step 6 shows. -/
def decaying : Tuning := ⟨#[(1, 8), (2, 0)]⟩

/-- A zero in a runtime `θ` is therefore harmless. It reads as 1 rather than as a pruned branch. -/
example (i d : Nat) :
    Tuning.weight ⟨#[(0, 0), (0, 0)]⟩ i d = Tuning.weight ⟨#[(1, 0), (1, 0)]⟩ i d := by
  simp only [Tuning.weight]
  rcases i with _ | _ | i <;> simp

/-! ## Step 4: call the tuned generator

After the `θ`, `genTree.tuned θ` has exactly `genTree`'s type. It therefore fits any position the
original held, and that includes a position at a different `Gen` instance. `θ` is an ordinary runtime
value, so it can come from a config file, from a search loop or from a command-line flag. A new
candidate weighting then costs a function call rather than a recompile. -/

/-- A generator parameterized by its weighting, at whatever monad the caller wants. -/
def genTreeAt [Gen G] (θ : Tuning) (depth : Nat) : G Tree := genTree.tuned θ depth

/-! ## Step 5: check that the distribution moved

`Basalt.GenStats` gives a seeded, pure interpretation called `StatGen`. A measurement is therefore
reproducible, and a `#guard` can *assert* it rather than a human read it. `runDraws` fixes the seed by
default. `#genstats` prints the same information as a panel that a human reads.

`fuel` bounds the number of random choices per draw, and a draw that exceeds it returns
`Error.outOfFuel` rather than a value. Keep the budget small here. An unbounded budget lets a
supercritical weighting nest deep enough to exhaust the *interpreter's* C stack, and that is a crash
rather than a failure you can recover from. Basalt raises `--tstack` in its own test library for this
reason. -/

/-- 200 seeded draws under the weighting `θ`, each capped at 60 random choices. -/
def draws (θ : Tuning) : Array (Except GenStats.Error (Tree × Nat)) :=
  GenStats.runDraws (genTree.tuned θ 0 : GenStats.StatGen Tree) { draws := 200, fuel := 60 }

/-- Total constructors produced over those draws; a failed draw contributes nothing. -/
def totalSize (θ : Tuning) : Nat :=
  (draws θ).foldl (fun n r => match r with | .ok (t, _) => n + t.size | _ => n) 0

/-- How many of those draws ran out of budget. -/
def outOfFuel (θ : Tuning) : Nat :=
  (draws θ).foldl (fun n r => match r with | .ok _ => n | _ => n + 1) 0

/-! The three usable weightings order as intended. The leaf-heavy one gives the smallest trees, and a
*slower* decay coefficient gives bigger trees. All three come from one compiled generator, selected at
run time, with no recompile between them. The totals are 288, 604 and 1302 constructors, and no draw
fails. -/

#guard totalSize leafHeavy < totalSize decaying
#guard totalSize decaying < totalSize ⟨#[(1, 1), (2, 0)]⟩
#guard outOfFuel leafHeavy == 0 && outOfFuel decaying == 0

/-! `nodeHeavy` is the cautionary one. It raises the recursive branch to weight 8 against `leaf`'s 1,
and no decay stops it. The mean number of offspring is `2 · 8/9`, which is above 1, so the recursion is
supercritical. 175 of the 200 draws exhaust their budget and produce no tree.

This is the failure that `holes` warned about in step 2. There `#[0, 2]` says that branch 1 recurses
twice, so its weight is the one to keep under control. The fix is a growth coefficient, as in
`decaying`, and not a smaller constant.

Note which way the sizes come out. `nodeHeavy` asks for *more* recursion and gives 39 constructors
against `decaying`'s 604, because most of its draws die before they return anything. A weighting that
looks more aggressive on paper can generate strictly less. -/

#guard outOfFuel nodeHeavy > 150
#guard totalSize nodeHeavy < totalSize decaying

/-! ## Step 6: check that nothing else broke

Two facts come free.

First, the defaults *are* the generator as written. `tuned_defaults` is `Eq.refl` and the kernel checks
it, so tuning cannot change the behaviour you already had. -/

example (depth : Nat) :
    (genTree.tuned genTree.defaults depth : SetGen.Set Tree) = genTree depth :=
  genTree.tuned_defaults depth

/-! Second, and this is the reason to care: at the `Set` interpretation *every* `θ` denotes the same
generator, so no weighting changes what is reachable. The `unseal` is needed because a
`partial_fixpoint` definition is irreducible. `StrataGenerators.SetGen.Tuning` holds this recipe, and
the recipes for the other recursion forms. -/

unseal genTree genTree.tuned

theorem genTree_tuned_eq (θ : Tuning) :
    (genTree.tuned θ : Nat → SetGen.Set Tree) = genTree := by
  apply SetGen.fix_congr
  funext f depth
  apply SetGen.frequency_congr_weights
  · rfl
  all_goals simp [Tuning.weight_pos]

/-- A soundness and completeness result that is proved once for the untuned generator therefore holds
    of every tuning of it. This proof does not need to know what the property is. That is the whole
    payoff: a tuning changes the distribution and never the language. -/
example (θ : Tuning) (depth : Nat) (P : Tree → Prop)
    (h : SetGen.IsSoundAndComplete (genTree depth : SetGen.Set Tree) P) :
    SetGen.IsSoundAndComplete (genTree.tuned θ depth : SetGen.Set Tree) P :=
  SetGen.IsSoundAndComplete.of_support_eq (by rw [genTree_tuned_eq]) h

end TuningWalkthrough
