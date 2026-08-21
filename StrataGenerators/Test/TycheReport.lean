import StrataGenerators.Test.Types

/-!
# The Tyche panel that a body gives

There is one panel for each registered property, and it comes from the `PropertyRunner` of that
property. For almost every property, that runner is the one that the instances of the input type
give.

A `PropertyRunner` already holds the printer, the shrinker and the breakdown into features. None
of that data is specific to one property. A panel therefore comes with a registration, and Tyche
shows a property from any file without a change to this module.

The panel does this work for each sample:

* It draws at a random generator size, and it records that size as the `generator_size` axis. A
  reader can then tell a small and vacuous draw from a large one.
* It scores the property, and it records the verdict two times: as the status of the sample, and
  as an axis with the name of the property. Tyche can then split a panel by the verdict.
* When the property does not hold, the panel reduces the value with the shrinker of the
  generator before it shows the value. The panel therefore shows the smallest reproducer and not
  the raw draw. It also computes the features again from the smaller value, so the axes describe
  what a reader sees.

A `Body.witnesses` property lists its fixed input space one time, and the panel does not sample
the space. A sample of a finite set with replacement would give the same few marks many times.
-/

namespace StrataGenerators.Test

/-- Greedy reduction against a check that does not hold. The function replaces the value by the
    first reduction of one step that still does not hold, and it repeats this step while such a
    reduction exists.

    The function acts on the shrinker of any `PropertyRunner`. `fuel` bounds the number of steps.
    A shrinker that gives no reduction, which is the default, makes this function the
    identity. -/
def minimizeWith (shrink : α → List α) (fails : α → Bool) : Nat → α → α
  | 0, x => x
  | fuel + 1, x =>
    match (shrink x).find? fails with
    | some y => minimizeWith shrink fails fuel y
    | none => x

/-- One Tyche mark. It holds the printed value, the verdict and the axes. -/
private structure Mark where
  representation : String
  passed : Bool
  features : List (String × Tyche.Feature)

private instance : Tyche.TycheSample Mark where
  toSample m :=
    { representation := m.representation
      status := if m.passed then .passed else .failed
      features := m.features }

/-- Draws one sample for the panel of a property, and scores the sample. `maxSize` bounds the
    generator size for each sample.

    `check` is the *decided* form of the property. A panel must classify each sample, and a
    shrinker must reject each candidate, so both need a decision procedure and not a `Prop`.
    `Body.sampled` holds the `DecidablePred` instance that gives it. Plausible gets the `Prop`
    without a decision, and that is what keeps the message of a counterexample readable. -/
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

/-- Writes the panel for one property. A property that gives its own `panel` writer gets that
    panel. For each other property, the panel comes from the body. A `Body.witness` property and
    a `Body.action` property have nothing to sample, so this function writes no panel for
    them. -/
def writePanel (handle : IO.FS.Handle) (d : TestDecl) (cfg : RunConfig)
    (numSamples runStart : Nat) : IO Unit := do
  unless d.tyche do return
  if let some write := d.panel then
    return ← write handle cfg numSamples runStart
  match d.body with
  | .sampled runner check dec _ _ =>
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
  -- There is nothing to sample: a closed `Bool`, or an action that reports only a verdict. Such
  -- a property can still have a panel, through `TestDecl.withPanel`.
  | .witness _ | .action _ => pure ()

/-- Writes one panel for each registered property whose body samples or lists its inputs, and one
    panel for each diagnostic that gives its own. The function never changes the exit code. -/
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
