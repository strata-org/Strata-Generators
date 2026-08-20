import Plausible
import StrataGenerators.Tyche

/-!
# The property-test vocabulary

The types a property author writes against, and the runner that executes one
property. Everything here is harness-independent: nothing in this module knows
about LSpec, about Tyche's output file, or about the CLI.

## The one idea

The old front end fixed the *input type* of a property in the harness: each
family of properties had a bundle of a fixed `α`, and each driver had a
hand-written fold per `α` that supplied `Arbitrary`/`Repr`/`Shrinkable` by
instance synthesis. Adding a property over a new input type therefore meant
editing the harness.

Here a property instead *carries* its generator as data — a `PropertyRunner α` bundling
the `Plausible.Gen`, the renderer, the shrinker and the Tyche breakdown — and the
input type is then existentially packed away in `Body.sampled`. One heterogeneous
`List TestDecl` can hold every property in the suite, so a driver is a fold over
that list and never mentions an input type at all.

`PropertyRunner` is exactly the data Plausible's `SampleableExt` class holds, so
`TestDecl.run` hands it straight back to Plausible's own runner
(`Testable.checkIO`) as an explicitly-supplied instance. The trial schedule,
the counterexample minimisation and the `gaveUp` accounting are therefore
Plausible's, unchanged — this module adds no sampling logic of its own.
-/

open Plausible

namespace StrataGenerators.Test

/-- Runtime knobs, parsed once from the command line and passed to every
    property. `gates` holds the opt-in tags the run was started with (`--smt`
    contributes `"smt"`); a property whose `TestDecl.gate` is not in this list is
    reported as skipped rather than run. -/
structure RunConfig where
  numTrials : Nat := 1000
  maxSize   : Nat := 100
  gates     : List String := []
  deriving Inhabited

/-- The Plausible configuration a `RunConfig` induces. -/
def RunConfig.toConfiguration (cfg : RunConfig) : Configuration :=
  { numInst := cfg.numTrials, maxSize := cfg.maxSize }

/-- What a self-driving `IO` property reports: its verdict, how many of its own
    samples passed, how many it drew, and an optional message.

    The shape deliberately matches `LSpec.TestSeq.individualIO`'s tuple, because
    these properties predate this front end (a format→parse round-trip that
    shrinks and prints its own reproducers; an SMT agreement check that shells out
    per term) and they join the registry unchanged. -/
structure ActionResult where
  passed  : Bool
  samples : Nat
  total   : Nat
  message : Option String := none

/-- Adapt the `(success, samples, total, message)` tuple the pre-existing
    self-driving checks return. -/
def ActionResult.ofTuple : Bool × Nat × Nat × Option String → ActionResult
  | (passed, samples, total, message) => { passed, samples, total, message }

/-- The Tyche axes of an input type: a breakdown of a generated value into named
    facets, so a panel can separate a *vacuous* draw from a live one.

    A fourth class alongside Plausible's `Arbitrary`/`Repr`/`Shrinkable`, and for the
    same reason: `num_decls` / `decl_kinds` / `program_size` are facts about the
    *type*, not about any one claim, so every property over that type wants the same
    axes. Declaring the instance once is what makes a Tyche panel free for a property
    written later.

    The catch-all instance below gives no axes, so a type needs an instance only if
    it has something worth plotting. -/
class TycheFeatures (α : Type) where
  features : α → List (String × Tyche.Feature)

instance (priority := low) : TycheFeatures α := ⟨fun _ => []⟩

/-- The generator, the printer and the shrinker for one input type, as data — the
    components a run needs for every input other than the check itself.

    This is the first-class form of the `Arbitrary`/`Repr`/`Shrinkable`/`TycheFeatures`
    instances. Properties do not normally mention it: `TestDecl.property` builds it from
    the instances, exactly as Plausible would. It exists as data because `Body.sampled`
    makes the input type *existential*, and because a property may occasionally want
    something other than its type's default.

    Named after the "property runner" of Keles et al., *Programmable Property-Based
    Testing* (ICFP 2026), whose figures decompose a runner into exactly these
    components: a generator, a shrinker and a printer, feeding the check. Note that the
    paper's *runner* is the generate-check-shrink-print loop over those components, and
    that loop is `runSampled` below. -/
structure PropertyRunner (α : Type) where
  gen      : Gen α
  render   : α → String
  /-- One-step reductions, smaller first. Defaults to no shrinking, which costs
      only counterexample quality. -/
  shrink   : α → List α := fun _ => []
  /-- Tyche axes computed from the input. -/
  features : α → List (String × Tyche.Feature) := fun _ => []

/-- The `PropertyRunner` that Plausible's own instances induce. This is what
    `TestDecl.property` uses, so "the generator for `α`" means the same thing here as it
    does to `#test` or to `Plausible.Testable.check`. -/
def PropertyRunner.ofInstances (α : Type)
    [Arbitrary α] [Repr α] [Shrinkable α] [TycheFeatures α] : PropertyRunner α :=
  { gen      := Arbitrary.arbitrary
    render   := fun x => toString (repr x)
    shrink   := Shrinkable.shrink
    features := TycheFeatures.features }

/-- Add to a runner's Tyche breakdown. Used by the few properties whose panel needs an
    axis the input type alone does not suggest. -/
def PropertyRunner.withFeatures (runner : PropertyRunner α)
    (features : α → List (String × Tyche.Feature)) : PropertyRunner α :=
  { runner with features := fun x => runner.features x ++ features x }

/-- Replace a generator's renderer, for a property whose counterexample needs a
    diagnostic view rather than the input type's default rendering. -/
def PropertyRunner.withRender (spec : PropertyRunner α) (render : α → String) : PropertyRunner α :=
  { spec with render }

/-- How a property gets its verdict. The `α` of the sampled shapes is existential,
    so properties over different input types share one registry. -/
inductive Body where
  /-- Draw `numTrials` inputs from `runner`, score each with `check`, and minimize the
      first counterexample. The shape of essentially every property.

      `check` returns a `Prop`, and two instances travel with it because each is needed
      by a different consumer and neither can be recovered later:

      * `inst` is what Plausible runs. It has to be captured *here*, at the registration
        site, because that is the only place the shape of `check x` is known — and the
        shape is what selects the `PrintableProp` instance that makes a counterexample
        legible. Rebuilding `Testable` from `dec` further down would fall back to the
        catch-all and report `issue: ⋯ does not hold`.
      * `dec` is what the Tyche panel and the shrinker need, since both must *decide*
        each candidate rather than merely test it. -/
  | sampled {α : Type} (runner : PropertyRunner α) (check : α → Prop)
      (dec : DecidablePred check) (inst : ∀ x, Testable (check x))
  /-- One constructed witness: the verdict is a closed `Bool`, with no sampling.
      For a claim whose sharpest statement is a single program or operator —
      a pipeline phase's no-op, a specific bitvector width — where sampling would
      only obscure which case is at stake. -/
  | witness (verdict : Bool)
  /-- A *fixed finite* input space, scored element by element. The property is the
      conjunction; the Tyche panel enumerates the space exactly once instead of
      sampling it with replacement. -/
  | witnesses {α : Type} (cases : List α) (render : α → String) (check : α → Bool)
      (features : α → List (String × Tyche.Feature) := fun _ => [])
  /-- A self-driving `IO` action: it samples, shrinks and prints on its own and
      reports only a verdict. For a property whose oracle is a subprocess or whose
      diagnostics have to be interleaved with generation. -/
  | action (run : RunConfig → IO ActionResult)

/-- One property under test. This is the whole of what a property author writes.

    `name` is the only label there is: it is the line in every report, the Tyche panel
    title, and — through its `area:` prefix — the report group. It must be unique across
    the registry; `Report.duplicateNames` checks that at startup, since two properties
    sharing a name would silently collapse their panels.

    There is deliberately no separate group field. A report group is a *function of the
    name*, so a property author supplies one string and a check, and nothing else. -/
structure TestDecl where
  name  : String
  /-- Opt-in gate: the property runs only when the driver was given this tag
      (`--smt` supplies `"smt"`). `none` runs always. -/
  gate  : Option String := none
  /-- Whether to emit a Tyche panel. Sampled and witness-set properties get one by
      default; `witness` and `action` bodies have nothing to sample, so they
      default to off via the smart constructors below. -/
  tyche : Bool := true
  /-- A bespoke Tyche panel, overriding the one derived from the body.

      The derived panel covers a `Bool` check over a `PropertyRunner`, which is almost
      every property. The exceptions are the handful whose oracle is itself an `IO`
      action (a solver run, a format→parse round-trip) or whose panel wants a
      breakdown that the input alone does not determine — those pass their own
      writer here, so the panel stays next to the property it belongs to instead of
      in a central file that has to be edited in step.

      Arguments: the open output handle, the run configuration, the number of
      samples for this panel, and the run's start timestamp. -/
  panel : Option (IO.FS.Handle → RunConfig → Nat → Nat → IO Unit) := none
  body  : Body

/-- A non-gating report: it prints, and never affects the exit code. Coverage
    statistics and localisation tallies live here rather than as properties,
    because they measure a distribution instead of asserting a fact — but they are
    registered and discovered exactly like properties, so a new one is also a
    one-file change. -/
structure Diagnostic where
  /-- Heading printed above the report, and the Tyche panel title if there is one. -/
  name : String
  run  : RunConfig → IO Unit
  /-- A Tyche panel for the same measurement. A diagnostic may have one even though
      it gates nothing: the panel is where a distribution is legible, which is the
      whole point of measuring it. -/
  panel : Option (IO.FS.Handle → RunConfig → Nat → Nat → IO Unit) := none

-- ── Smart constructors ────────────────────────────────────────────────

/-- **The way to state a property.** A decidable `Prop` over a type Plausible can
    sample: the generator, the printer and the shrinker come from that type's
    `Arbitrary`/`Repr`/`Shrinkable` instances, and the Tyche axes from its
    `TycheFeatures` instance.

    This is QuickCheck's `quickCheck prop_foo`, where `prop_foo :: T -> Bool` picks its
    generator from the type of its argument. Annotate the argument, since that
    annotation is what selects the generator:

    ```lean
    .property "mypass: idempotent"
      fun (gp : GenProgram) => myPass (myPass gp.prog) = myPass gp.prog
    ```

    A `Bool`-valued check works unchanged, since `Bool` coerces to `Prop`, so a named
    `check*` predicate can be handed over as-is. Stating the claim as a `Prop` is worth
    it wherever the shape is an equality or an order: Plausible's `PrintableProp` then
    prints *both sides* of the failing comparison instead of the single word `false`.

    `TestDecl.forAll` is the same thing with the runner named explicitly, for the rare
    property that wants something other than its type's default. -/
def TestDecl.property (name : String)
    [Arbitrary α] [Repr α] [Shrinkable α] [TycheFeatures α]
    (check : α → Prop) [dec : DecidablePred check] [inst : ∀ x, Testable (check x)]
    (gate : Option String := none) : TestDecl :=
  { name, gate, body := .sampled (PropertyRunner.ofInstances α) check dec inst }

/-- A property over an explicitly named `PropertyRunner`, for the case where the type's
    default instances are not what you want — a narrowed draw, a diagnostic renderer,
    an extra Tyche axis. The explicit-generator sense of QuickCheck's `forAll`. Prefer
    `TestDecl.property`. -/
def TestDecl.forAll (name : String) (runner : PropertyRunner α) (check : α → Prop)
    [dec : DecidablePred check] [inst : ∀ x, Testable (check x)]
    (gate : Option String := none) : TestDecl :=
  { name, gate, body := .sampled runner check dec inst }

/-- A closed-`Bool` property with no generated input. -/
def TestDecl.witness (name : String) (verdict : Bool)
    (gate : Option String := none) : TestDecl :=
  { name, gate, tyche := false, body := .witness verdict }

/-- A property over a fixed finite input space. -/
def TestDecl.witnesses (name : String) (cases : List α) (render : α → String)
    (check : α → Bool)
    (features : α → List (String × Tyche.Feature) := fun _ => [])
    (gate : Option String := none) : TestDecl :=
  { name, gate, body := .witnesses cases render check features }

/-- A self-driving `IO` property. -/
def TestDecl.action (name : String) (run : RunConfig → IO ActionResult)
    (gate : Option String := none) : TestDecl :=
  { name, gate, tyche := false, body := .action run }

/-- Attach a bespoke Tyche panel that samples `gen`, an `IO` action producing an
    already-classified sample.

    For the handful of properties whose panel is richer than the derived one — an
    `IO` oracle, or a breakdown of *why* a sample failed that the input alone does
    not determine. The panel's title is taken from the property's own `name`, so the
    two cannot drift apart. -/
def TestDecl.withPanel [Tyche.TycheSample β] (d : TestDecl) (gen : IO β) : TestDecl :=
  { d with tyche := true
           panel := some (fun handle _ numSamples runStart =>
             Tyche.runInto handle gen d.name numSamples runStart) }

/-- Attach a bespoke Tyche panel that enumerates a fixed finite set of samples
    rather than drawing them, for a property whose input space is finite. -/
def TestDecl.withEnumeratedPanel [Tyche.TycheSample β] (d : TestDecl) (cases : List β) :
    TestDecl :=
  { d with tyche := true
           panel := some (fun handle _ _ runStart =>
             Tyche.writeInto handle cases d.name runStart) }

/-- Give a diagnostic a Tyche panel sampling `gen`. -/
def Diagnostic.withPanel [Tyche.TycheSample β] (d : Diagnostic) (gen : IO β) :
    Diagnostic :=
  { d with panel := some (fun handle _ numSamples runStart =>
             Tyche.runInto handle gen d.name numSamples runStart) }

/-- The report group: the `area` of an `area: description` name.

    Grouping is derived rather than declared, so it cannot disagree with the name. A
    name with no `": "` is its own group. -/
def TestDecl.group (d : TestDecl) : String :=
  (d.name.splitOn ": ").headD d.name

/-- Whether this run's gates admit the property. -/
def TestDecl.enabled (d : TestDecl) (cfg : RunConfig) : Bool :=
  match d.gate with
  | none => true
  | some g => cfg.gates.contains g

-- ── Running one property ──────────────────────────────────────────────

/-- The verdict of one property, in the form every renderer needs. -/
structure Outcome where
  passed  : Bool
  /-- `(passing samples, total drawn)`, when the body knows them, for the `(n/m)`
      a report line carries. `none` for a single-witness property, which has no
      trial count to report. -/
  counts  : Option (Nat × Nat) := none
  message : Option String := none
  /-- Set when the property's gate was not enabled: the driver reports it as
      skipped rather than as a pass, so an absent solver cannot read as green. -/
  skipped : Bool := false

/-- Read Plausible's own `TestResult` as an `Outcome`. Both Plausible-backed bodies go
    through this, so a `Bool` property and a `Prop` property report identically. -/
def Outcome.ofTestResult (cfg : Configuration) {p : Prop} : TestResult p → Outcome
  | .success _ => { passed := true, counts := some (cfg.numInst, cfg.numInst) }
  | .gaveUp n => { passed := false, message := some s!"Gave up {n} times" }
  | .failure _ xs n =>
    { passed := false, message := some (Testable.formatFailure "Found problems!" xs n) }

/-- Run a decidable `Prop` over a generator through Plausible's own runner.

    The runner's fields are supplied as explicit instances rather than synthesized,
    which is the trick that lets the input type be existential:
    `Plausible.Testable`'s `varTestable` needs `SampleableExt α`, and Plausible's
    default `SampleableExt` instance holds precisely `Arbitrary`/`Repr`/`Shrinkable`.
    So a property built by `TestDecl.property` is run against the very instances
    Plausible would have found for itself.

    `NamedBinder` is applied by hand because `varTestable` matches only on a
    decorated `∀`; `mk_decorations` cannot help here, since the proposition is built
    from a term rather than written as syntax.

    The `Prop` reaches Plausible *undecided*, which is what buys the readable
    counterexample — `issue: 1 = 2 does not hold` rather than
    `issue: false does not hold`. Deciding it first erases the shape `PrintableProp`
    reads. -/
def runSampled (α : Type) [Repr α] [Shrinkable α] [Arbitrary α]
    (check : α → Prop) [∀ x, Testable (check x)] (cfg : Configuration) : IO Outcome := do
  let r ← Testable.checkIO (NamedBinder "input" (∀ x : α, check x)) cfg
  pure (Outcome.ofTestResult cfg r)

/-- Run one property. Returns a `skipped` outcome when the run's gates do not
    admit it. -/
def TestDecl.run (d : TestDecl) (cfg : RunConfig) : IO Outcome := do
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

end StrataGenerators.Test
