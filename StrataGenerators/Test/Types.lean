import Plausible
import StrataGenerators.Tyche

/-!
# The vocabulary for a property test

This module holds the types that the author of a property uses, and the runner that runs one
property. Nothing here depends on a harness. No declaration knows about LSpec, about the
output file of Tyche, or about the command line.

## The one idea

A property *carries* its generator as data. A `PropertyRunner α` holds the `Plausible.Gen`,
the renderer, the shrinker and the Tyche breakdown for the input type. `Body.sampled` then
packs the input type away as an existential. One heterogeneous `List TestDecl` can therefore
hold every property in the suite, and a driver is a fold over that list that never mentions
an input type.

A `PropertyRunner` holds exactly the data of the `SampleableExt` class of Plausible.
Therefore `TestDecl.run` gives it back to the runner of Plausible, `Testable.checkIO`, as an
explicit instance. The schedule of the trials, the reduction of a counterexample and the
count for `gaveUp` are all the work of Plausible. This module adds no logic for sampling.
-/

open Plausible

namespace StrataGenerators.Test

/-- The settings for a run. The driver reads them from the command line one time, and it
    gives them to each property. `gates` holds the tags that the run enables, and the flag
    `--smt` adds the tag `"smt"`. If the `TestDecl.gate` field of a property is not in this
    list, the driver reports the property as skipped and does not run it. -/
structure RunConfig where
  numTrials : Nat := 1000
  maxSize   : Nat := 100
  gates     : List String := []
  deriving Inhabited

/-- The Plausible configuration for a `RunConfig`. -/
def RunConfig.toConfiguration (cfg : RunConfig) : Configuration :=
  { numInst := cfg.numTrials, maxSize := cfg.maxSize }

/-- The report of a property that drives itself with `IO`. It gives the verdict, the number
    of its own samples that passed, the number of samples that it drew, and a message.

    The shape agrees with the tuple of `LSpec.TestSeq.individualIO`, so such a property joins
    the registry without a change. A round trip from `format` to `parse` that shrinks and
    prints its own reproducers is one example. A check for SMT agreement that starts a
    subprocess for each term is another. -/
structure ActionResult where
  passed  : Bool
  samples : Nat
  total   : Nat
  message : Option String := none

/-- Builds an `ActionResult` from the tuple `(success, samples, total, message)` that a check
    which drives itself returns. -/
def ActionResult.ofTuple : Bool × Nat × Nat × Option String → ActionResult
  | (passed, samples, total, message) => { passed, samples, total, message }

/-- The Tyche axes of an input type. The class breaks a generated value into named facets, so
    a panel can separate a *vacuous* draw from a live one.

    This is a fourth class next to `Arbitrary`, `Repr` and `Shrinkable` of Plausible, and for
    the same reason. An axis such as `num_decls`, `decl_kinds` or `program_size` is a fact
    about the *type* and not about one claim, so each property over that type wants the same
    axes. One instance therefore gives a Tyche panel to a property that someone writes later.

    The catch-all instance gives no axis. A type needs its own instance only when it has
    something to plot. -/
class TycheFeatures (α : Type) where
  features : α → List (String × Tyche.Feature)

instance (priority := low) : TycheFeatures α := ⟨fun _ => []⟩

/-- The generator, the printer and the shrinker for one input type, as data. These are the
    parts of a run that are not the check.

    This structure is the first-class form of the `Arbitrary`, `Repr`, `Shrinkable` and
    `TycheFeatures` instances. A property does not name it in the usual case, because
    `TestDecl.property` builds it from the instances in the same way as Plausible. It is data
    for two reasons: `Body.sampled` makes the input type *existential*, and a property can
    need something other than the default of its type.

    The name comes from the "property runner" of Keles et al., *Programmable Property-Based
    Testing* (ICFP 2026). The figures of that paper divide a runner into these same parts: a
    generator, a shrinker and a printer that feed the check. The *runner* of the paper is the
    loop over those parts that generates, checks, shrinks and prints, and `runSampled` is that
    loop. -/
structure PropertyRunner (α : Type) where
  gen      : Gen α
  render   : α → String
  /-- The reductions of one step, with the smallest first. The default is an empty list. A
      property that keeps the default loses only the quality of its counterexamples. -/
  shrink   : α → List α := fun _ => []
  /-- The Tyche axes for an input value. -/
  features : α → List (String × Tyche.Feature) := fun _ => []

/-- The `PropertyRunner` that the instances of Plausible give. `TestDecl.property` uses this
    function, so the phrase "the generator for `α`" means the same thing here as it means to
    `#test` and to `Plausible.Testable.check`. -/
def PropertyRunner.ofInstances (α : Type)
    [Arbitrary α] [Repr α] [Shrinkable α] [TycheFeatures α] : PropertyRunner α :=
  { gen      := Arbitrary.arbitrary
    render   := fun x => toString (repr x)
    shrink   := Shrinkable.shrink
    features := TycheFeatures.features }

/-- Adds axes to the Tyche breakdown of a runner. A property uses this when its panel needs an
    axis that the input type does not give. -/
def PropertyRunner.withFeatures (runner : PropertyRunner α)
    (features : α → List (String × Tyche.Feature)) : PropertyRunner α :=
  { runner with features := fun x => runner.features x ++ features x }

/-- Replaces the renderer of a runner. A property uses this when its counterexample needs a
    diagnostic view and not the default output of the input type. -/
def PropertyRunner.withRender (spec : PropertyRunner α) (render : α → String) : PropertyRunner α :=
  { spec with render }

/-- How a property gets its verdict. The type `α` of the sampled shapes is existential, so
    properties over different input types share one registry. -/
inductive Body where
  /-- Draws `numTrials` inputs from `runner`, scores each input with `check`, and reduces the
      first counterexample. Almost every property has this shape.

      `check` returns a `Prop`. Two instances travel with it, because a different consumer
      needs each one and neither instance is available later:

      * Plausible runs `inst`. The registration site must capture it, because that site is
        the only place that knows the shape of `check x`. The shape selects the
        `PrintableProp` instance that makes a counterexample readable. A `Testable` instance
        that a later step builds from `dec` falls back to the catch-all and reports
        `issue: ⋯ does not hold`.
      * The Tyche panel and the shrinker need `dec`, because both must *decide* each
        candidate and not only test it. -/
  | sampled {α : Type} (runner : PropertyRunner α) (check : α → Prop)
      (dec : DecidablePred check) (inst : ∀ x, Testable (check x))
  /-- One witness that the author builds. The verdict is a closed `Bool` and there is no
      sampling. Use it for a claim whose best statement is one program or one operator, such
      as a phase that changes nothing, or one bitvector width. A random sample would hide
      which case the claim covers. -/
  | witness (verdict : Bool)
  /-- A *fixed and finite* input space, scored one element at a time. The property is the
      conjunction over the elements. The Tyche panel lists the space one time, and it does
      not sample the space with replacement. -/
  | witnesses {α : Type} (cases : List α) (render : α → String) (check : α → Bool)
      (features : α → List (String × Tyche.Feature) := fun _ => [])
  /-- An `IO` action that drives itself. It samples, shrinks and prints on its own, and it
      reports only a verdict. Use it when the oracle is a subprocess, or when the diagnostics
      must come between the draws. -/
  | action (run : RunConfig → IO ActionResult)

/-- What a property claims about its own verdict.

    Almost every property claims to hold. That claim is `mustHold`, and it is the default.
    Use `knownFailure` for a property that states a *real defect in the code under test*. The
    claim is right and the implementation is wrong. The property therefore stays in the suite
    as the net around the future fix, and it does not block a merge for a defect that someone
    already reported.

    `reason` is prose, and it is the place for the upstream report. It takes the place of the
    counterexample on the report line, so it is the only explanation that a reader gets. Name
    the defect in it.

    `knownFailure` is *not* a way to quiet a property that is only noisy. The run fails as
    soon as someone fixes the defect, so the mark cannot hide a change that breaks a property
    that holds today. The mark is also wrong for a property that a draw falsifies only
    sometimes. Such a property holds on most runs, and the mark would then make the suite red
    on those runs. Leave that property without a mark, and pin the defect with a `#guard` on a
    witness that you build by hand. -/
inductive Expectation where
  /-- The property must hold. This is the value for each property that does not say
      otherwise. -/
  | mustHold
  /-- The property must not hold, because the code under test has a defect. The report hides
      its counterexample and the run continues. If the property ever *holds*, the run fails,
      because a fix must not go without notice. -/
  | knownFailure (reason : String)
  deriving Inhabited

/-- One property under test. This structure is all that the author of a property writes.

    `name` is the only label. It is the line in each report and the title of the Tyche panel.
    Its `area:` prefix also gives the report group. The name must be unique in the registry,
    and `Report.duplicateNames` checks this at the start of a run, because two properties with
    one name would join their panels.

    There is no separate field for the group. The report group is a *function of the name*, so
    the author gives one string and a check, and nothing else. -/
structure TestDecl where
  name  : String
  /-- The tag that enables the property. The property runs only when the driver receives this
      tag, and the flag `--smt` gives the tag `"smt"`. A value of `none` always runs. -/
  gate  : Option String := none
  /-- What this property claims about its own verdict. The field has a default, so a property
      says nothing about a known defect until its author adds `knownFailure`. -/
  expect : Expectation := .mustHold
  /-- Whether the run emits a Tyche panel. A sampled property and a property over a set of
      witnesses get a panel by default. A `witness` body and an `action` body have nothing to
      sample, so the smart constructors below set this field to `false` for them. -/
  tyche : Bool := true
  /-- A Tyche panel of its own, in place of the panel that the body gives.

      The panel from the body covers a `Bool` check over a `PropertyRunner`, and almost every
      property has that shape. A property is an exception when its oracle is an `IO` action,
      such as a solver run or a round trip from `format` to `parse`. It is also an exception
      when its panel needs a breakdown that the input does not give. Such a property gives its
      own writer here, so the panel stays next to the property and not in a central file that
      someone must edit at the same time.

      The arguments are the open output handle, the configuration of the run, the number of
      samples for this panel, and the start time of the run. -/
  panel : Option (IO.FS.Handle → RunConfig → Nat → Nat → IO Unit) := none
  body  : Body

/-- A report that does not gate. It prints, and it never changes the exit code. Statistics for
    coverage and counts that locate an error are diagnostics and not properties, because they
    measure a distribution and they assert no fact. The registry holds them in the same way as
    a property, so you add a new one in a single file. -/
structure Diagnostic where
  /-- The heading above the report. It is also the title of the Tyche panel, if the diagnostic
      has one. -/
  name : String
  run  : RunConfig → IO Unit
  /-- A Tyche panel for the same measurement. A diagnostic can have a panel although it gates
      nothing, because a panel is where a reader can see a distribution. -/
  panel : Option (IO.FS.Handle → RunConfig → Nat → Nat → IO Unit) := none

-- ── Smart constructors ────────────────────────────────────────────────

/-- **Use this function to state a property.** It takes a decidable `Prop` over a type that
    Plausible can sample. The generator, the printer and the shrinker come from the
    `Arbitrary`, `Repr` and `Shrinkable` instances of that type. The Tyche axes come from its
    `TycheFeatures` instance.

    This is `quickCheck prop_foo` of QuickCheck, where `prop_foo :: T -> Bool` gets its
    generator from the type of its argument. Give the argument a type annotation, because the
    annotation selects the generator:

    ```lean
    .property "mypass: idempotent"
      fun (gp : GenProgram) => myPass (myPass gp.prog) = myPass gp.prog
    ```

    A check that returns a `Bool` also works, because `Bool` coerces to `Prop`. You can
    therefore give a named `check*` predicate to this function without a change. A claim whose
    shape is an equality or an order is better as a `Prop`. The `PrintableProp` instance of
    Plausible then prints *both sides* of the comparison, and not the single word `false`.

    `TestDecl.forAll` does the same work, but its caller names the runner. Use it for the rare
    property that needs something other than the default of its type. -/
def TestDecl.property (name : String)
    [Arbitrary α] [Repr α] [Shrinkable α] [TycheFeatures α]
    (check : α → Prop) [dec : DecidablePred check] [inst : ∀ x, Testable (check x)]
    (gate : Option String := none) : TestDecl :=
  { name, gate, body := .sampled (PropertyRunner.ofInstances α) check dec inst }

/-- A property over a `PropertyRunner` that the caller names. Use it when the default
    instances of the type are wrong for the property: a narrower draw, a diagnostic renderer,
    or one more Tyche axis. This is the `forAll` of QuickCheck, which also names its generator.
    Prefer `TestDecl.property`. -/
def TestDecl.forAll (name : String) (runner : PropertyRunner α) (check : α → Prop)
    [dec : DecidablePred check] [inst : ∀ x, Testable (check x)]
    (gate : Option String := none) : TestDecl :=
  { name, gate, body := .sampled runner check dec inst }

/-- A property whose verdict is a closed `Bool`. It has no generated input. -/
def TestDecl.witness (name : String) (verdict : Bool)
    (gate : Option String := none) : TestDecl :=
  { name, gate, tyche := false, body := .witness verdict }

/-- A property over a fixed and finite input space. -/
def TestDecl.witnesses (name : String) (cases : List α) (render : α → String)
    (check : α → Bool)
    (features : α → List (String × Tyche.Feature) := fun _ => [])
    (gate : Option String := none) : TestDecl :=
  { name, gate, body := .witnesses cases render check features }

/-- A property that drives itself with `IO`. -/
def TestDecl.action (name : String) (run : RunConfig → IO ActionResult)
    (gate : Option String := none) : TestDecl :=
  { name, gate, tyche := false, body := .action run }

/-- **Marks a property that a defect in the code under test falsifies.** The report hides its
    counterexample, and the property stops gating the exit code. If the property ever holds,
    the run fails and it names this call as the code to delete.

    This is a prefix and not a method, so a reader sees the mark first and the property needs
    no parentheses:

    ```lean
    @[strata_property]
    def liftOutputTypechecks : TestDecl :=
      knownFailure "a minted snapshot name escapes its scope" <|
        TestDecl.property "lift: the output typechecks"
          fun (gp : GenProgram) => checkLiftOutputTypechecks gp.prog
    ```

    The reason travels with the mark, and it does not sit in a central list that someone must
    edit at the same time. The registry is therefore the one answer to the question of which
    properties are known to fail, and `--list` prints that answer. For one member of a
    `family`, give the `Expectation` as the third component of the entry, because an attribute
    and a prefix cannot address one entry of a list.

    Prefer this mark to the deletion of a property, and to a comment around it. A property
    that you delete stops watching the defect, and nothing then reports the fix. -/
def knownFailure (reason : String) (d : TestDecl) : TestDecl :=
  { d with expect := .knownFailure reason }

/-- Adds a Tyche panel of its own that samples `gen`. The argument `gen` is an `IO` action that
    gives a sample with its classes.

    Use this for a property whose panel needs more than the panel from the body: an `IO`
    oracle, or a breakdown of *why* a sample did not hold that the input does not give. The
    title of the panel comes from the `name` of the property, so the two always agree. -/
def TestDecl.withPanel [Tyche.TycheSample β] (d : TestDecl) (gen : IO β) : TestDecl :=
  { d with tyche := true
           panel := some (fun handle _ numSamples runStart =>
             Tyche.runInto handle gen d.name numSamples runStart) }

/-- Adds a Tyche panel of its own that lists a fixed and finite set of samples in place of a
    draw. Use it for a property whose input space is finite. -/
def TestDecl.withEnumeratedPanel [Tyche.TycheSample β] (d : TestDecl) (cases : List β) :
    TestDecl :=
  { d with tyche := true
           panel := some (fun handle _ _ runStart =>
             Tyche.writeInto handle cases d.name runStart) }

/-- Gives a diagnostic a Tyche panel that samples `gen`. -/
def Diagnostic.withPanel [Tyche.TycheSample β] (d : Diagnostic) (gen : IO β) :
    Diagnostic :=
  { d with panel := some (fun handle _ numSamples runStart =>
             Tyche.runInto handle gen d.name numSamples runStart) }

/-- The report group, which is the `area` part of a name of the form `area: description`.

    The group comes from the name and no one declares it, so the two cannot disagree. A name
    that holds no `": "` is its own group. -/
def TestDecl.group (d : TestDecl) : String :=
  (d.name.splitOn ": ").headD d.name

/-- Whether the gates of this run let the property run. -/
def TestDecl.enabled (d : TestDecl) (cfg : RunConfig) : Bool :=
  match d.gate with
  | none => true
  | some g => cfg.gates.contains g

-- ── Running one property ──────────────────────────────────────────────

/-- The verdict of one property, in the form every renderer needs. -/
structure Outcome where
  passed  : Bool
  /-- The number of samples that passed, and the number of samples that the run drew, when
      the body knows them. A report line prints them as `(n/m)`. The value is `none` for a
      property with one witness, which has no count of trials. -/
  counts  : Option (Nat × Nat) := none
  message : Option String := none
  /-- `true` when the run did not enable the gate of the property. The driver then reports the
      property as skipped and not as a pass, so a solver that is not present does not look
      like a pass. -/
  skipped : Bool := false
  /-- `true` when `Outcome.reconcile` changed a raw verdict into the expected verdict. The
      property then asserts nothing about this run, so a driver reports it as `XFAIL` and not
      as a pass. This is the same reason as for `skipped`: a defect that the report hides must
      not look like a pass. -/
  xfail   : Bool := false

/-- Reads a `TestResult` of Plausible as an `Outcome`. Both bodies that use Plausible go
    through this function, so a `Bool` property and a `Prop` property report in the same
    way. -/
def Outcome.ofTestResult (cfg : Configuration) {p : Prop} : TestResult p → Outcome
  | .success _ => { passed := true, counts := some (cfg.numInst, cfg.numInst) }
  | .gaveUp n => { passed := false, message := some s!"Gave up {n} times" }
  | .failure _ xs n =>
    { passed := false, message := some (Testable.formatFailure "Found problems!" xs n) }

/-- Runs a decidable `Prop` over a generator through the runner of Plausible.

    The call gives the fields of the runner as explicit instances, and Lean does not
    synthesize them. This is what lets the input type be existential. The `varTestable`
    instance of `Plausible.Testable` needs `SampleableExt α`, and the default `SampleableExt`
    instance of Plausible holds `Arbitrary`, `Repr` and `Shrinkable`. A property that
    `TestDecl.property` builds therefore runs against the same instances that Plausible would
    find.

    The code applies `NamedBinder` by hand, because `varTestable` matches only a `∀` that has
    that decoration. `mk_decorations` cannot help here, because a term builds the proposition
    and no one writes it as syntax.

    The `Prop` reaches Plausible *without a decision*, and this is what gives a readable
    counterexample such as `issue: 1 = 2 does not hold` in place of
    `issue: false does not hold`. A decision first erases the shape that `PrintableProp`
    reads. -/
def runSampled (α : Type) [Repr α] [Shrinkable α] [Arbitrary α]
    (check : α → Prop) [∀ x, Testable (check x)] (cfg : Configuration) : IO Outcome := do
  let r ← Testable.checkIO (NamedBinder "input" (∀ x : α, check x)) cfg
  pure (Outcome.ofTestResult cfg r)

/-- Reconciles a raw verdict with the claim of the declaration.

    Each verdict in the package goes through this function, and each driver reads the result.
    Therefore the two drivers cannot disagree about a known failure, and they cannot disagree
    about a pass. The reconciliation happens one time, below the output.

    The function returns a skipped property without a change. The run did not enable its gate,
    so there is no verdict to reconcile. A report of `XFAIL` for a property that did not run
    would claim that someone saw the defect. -/
def Outcome.reconcile (o : Outcome) : Expectation → Outcome
  | .mustHold => o
  | .knownFailure reason =>
    if o.skipped then o
    else if o.passed then
      -- The defect is fixed, or the mark was wrong. Either way this must be seen.
      { o with passed := false,
               message := some s!"expected to fail, but passed — the defect appears to \
                 be fixed, so drop its known-failure mark ({reason})" }
    else
      -- Drop `o.message`. `Testable.formatFailure` put the counterexample there, and it is
      -- noise for a defect that someone already understands and reported.
      { o with passed := true, xfail := true, message := some reason }

/-- Runs one property and reports the *raw* verdict, before the reconciliation against
    `TestDecl.expect`.

    This function is separate from `run` for two reasons. The suppression is then one visible
    step, and it is not part of each of the four bodies. A consumer that wants the verdict
    without the reconciliation also has one. The Tyche pass scores each sample through the
    `dec` field of the body, so a mark does not change a panel. This is the correct behaviour,
    because a panel is where a reader sees the distribution of a known failure. -/
def TestDecl.runRaw (d : TestDecl) (cfg : RunConfig) : IO Outcome := do
  if !d.enabled cfg then
    return { passed := true, skipped := true }
  match d.body with
  | .sampled runner check _ inst =>
    @runSampled _ ⟨fun x _ => runner.render x⟩ ⟨runner.shrink⟩ ⟨runner.gen⟩
      check inst cfg.toConfiguration
  | .witness verdict => pure { passed := verdict }
  | .witnesses cases render check _ =>
    let failures := cases.filter (fun c => !check c)
    let total := cases.length
    if failures.isEmpty then
      pure { passed := true, counts := some (total, total) }
    else
      let shown := failures.take 3 |>.map render
      pure { passed := false
             counts := some (total - failures.length, total)
             message := some s!"{failures.length}/{total} cases fail, e.g. \
               {String.intercalate "; " shown}" }
  | .action run =>
    let r ← run cfg
    pure { passed := r.passed, counts := some (r.samples, r.total), message := r.message }

/-- Runs one property and reconciles the verdict against the claim of the property. **A driver
    calls this function.** `runRaw` is for a consumer that wants the verdict without the
    reconciliation.

    The result is a `skipped` outcome when the gates of the run do not let the property run. It
    is an `xfail` outcome when `TestDecl.expect` says that the property is known to fail. -/
def TestDecl.run (d : TestDecl) (cfg : RunConfig) : IO Outcome := do
  let raw ← d.runRaw cfg
  return raw.reconcile d.expect

end StrataGenerators.Test
