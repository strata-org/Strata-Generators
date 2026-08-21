import StrataGenerators.Test.Types

/-!
# Tyche panels, derived

One panel per registered property, generated from the property's own `PropertyRunner`
(which for almost every property is the one its input type's instances induce).

The old front end wrote a panel by hand for each property family: a result
structure, a `TycheSample` instance, a `gen*Prop` sampler, and a line in
`runTychePanels`. Because a `PropertyRunner` already carries the printer, the shrinker
and the feature breakdown, none of that is property-specific — so a panel comes
free with a registration, and a property written in a user's own file is visible
in Tyche without touching this module.

What the derived panel does per sample, matching what the hand-written ones did:

* draw at a random generator size, and record that size as the `generator_size`
  axis (so a vacuous small draw is distinguishable from a large one);
* score the property, and record the verdict both as the sample's status and as an
  axis named after the property (Tyche can then split a panel by pass/fail);
* on a failure, minimize with the generator's own shrinker before displaying, so
  the panel shows the smallest reproducer rather than the raw draw, and recompute
  the features from the minimized value so the axes describe what is shown.

A `Body.witnesses` property enumerates its fixed input space exactly once instead
of sampling it, since sampling a finite set with replacement would emit the same
few marks repeatedly.
-/

namespace StrataGenerators.Test

/-- Greedy minimization against a failing check: repeatedly replace the value by
    the first one-step reduction that still fails, until none does.

    The same shape as the bespoke minimizers the old panels used
    (`minimizeProgramCounterexample`, `shrinkWhile`), lifted to act on any
    `PropertyRunner`'s shrinker. `fuel` bounds the walk; a shrinker that offers no
    reduction (the default) makes this the identity. -/
def minimizeWith (shrink : α → List α) (fails : α → Bool) : Nat → α → α
  | 0, x => x
  | fuel + 1, x =>
    match (shrink x).find? fails with
    | some y => minimizeWith shrink fails fuel y
    | none => x

/-- One Tyche mark: a rendered value, a verdict, and the axes. -/
private structure Mark where
  representation : String
  passed : Bool
  features : List (String × Tyche.Feature)

private instance : Tyche.TycheSample Mark where
  toSample m :=
    { representation := m.representation
      status := if m.passed then .passed else .failed
      features := m.features }

/-- Draw one sample for a property's panel and score it. `maxSize` bounds the
    generator size drawn per sample.

    `check` is the *decided* form of the property. A panel has to classify every sample
    and a shrinker has to reject every candidate, so both need a decision procedure
    rather than a `Prop`; `Body.sampled` carries the `DecidablePred` instance that
    supplies it. Plausible gets the undecided `Prop` instead, which is what keeps a
    counterexample's failure message legible. -/
private def sampleMark (runner : PropertyRunner α) (check : α → Bool) (name : String)
    (maxSize : Nat) : IO Mark := do
  let size ← IO.rand 0 maxSize
  let x ← Plausible.Gen.run runner.gen size
  let passed := check x
  let shown := if passed then x else minimizeWith runner.shrink (fun y => !check y) 400 x
  pure { representation := runner.render shown
         passed
         features := (name, .nominal (if passed then "pass" else "fail"))
           :: ("generator_size", .ordinal size)
           :: runner.features shown }

/-- Write the panel for one property. A property that supplied its own `panel`
    writer gets that; otherwise the panel is derived from the body, and a
    `Body.witness` or `Body.action` property (nothing to sample) is skipped.

    A panel draws from the process-wide RNG, which `--seed=` fixes for the whole run, so
    a seeded run's panels are reproducible. It deliberately ignores a property's *pinned*
    seed: a panel is a picture of a distribution, and a thousand samples of one pinned
    draw would be a picture of nothing. -/
def writePanel (handle : IO.FS.Handle) (d : TestDecl) (cfg : RunConfig)
    (numSamples runStart : Nat) : IO Unit := do
  unless d.tyche do return
  if let some write := d.panel then
    return ← write handle cfg numSamples runStart
  match d.body with
  | .sampled runner check dec _ =>
    Tyche.runInto handle
      (sampleMark runner (fun x => @decide (check x) (dec x)) d.name cfg.maxSize)
      d.name numSamples runStart
  | .witnesses cases render check features =>
    Tyche.writeInto handle
      (cases.map fun c =>
        let passed := check c
        ({ representation := render c
           passed
           features := (d.name, .nominal (if passed then "pass" else "fail"))
             :: features c } : Mark))
      d.name runStart
  -- Nothing to sample: a closed `Bool`, or an action that reports only a verdict. Such
  -- a property can still have a panel, through `TestDecl.withPanel` above.
  | .witness _ | .action _ => pure ()

/-- Write one panel per registered property with a sampled or enumerated body, and
    one per diagnostic that supplied its own. Never affects the exit code. -/
def writePanels (handle : IO.FS.Handle) (ds : List TestDecl) (diags : List Diagnostic)
    (cfg : RunConfig) (numSamples : Nat) : IO Unit := do
  let runStart ← IO.monoMsNow
  for d in ds do
    if d.enabled cfg then
      writePanel handle d cfg numSamples runStart
  for d in diags do
    if let some write := d.panel then
      write handle cfg numSamples runStart

end StrataGenerators.Test
