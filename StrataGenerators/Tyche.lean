import Basalt.IO
import Lean.Data.Json

/-!
# Support for the Tyche visualization

This module writes the samples of a generator in the JSONL format of
[Tyche](https://github.com/tyche-pbt/tyche-extension). Tyche is an extension for VS Code that
shows the distribution of a generator for a property-based test.

## The JSONL format

Each line of the output file is a JSON object whose `type` field is `"test_case"`:
```json
{"type":"test_case","run_start":<timestamp>,"property":"<name>",
 "status":"passed","status_reason":"","representation":"<value>",
 "features":{...},"coverage":null}
```

## How to use this module

1. Write a `TycheSample` instance for your generated type.
2. Call `Tyche.run` with a generator action and an output path.
3. Open the `.jsonl` file with Tyche. In VS Code, use `Tyche: Open`.
-/

open Lean (Json JsonNumber)

namespace Tyche

/-- The status of a generated test case. -/
inductive Status where
  | passed
  | failed
  | gaveUp
  deriving Inhabited

/-- The value of one feature, for the Tyche visualization. -/
inductive Feature where
  | ordinal (v : Int)
  | nominal (v : String)
  | continuous (v : Float)
  deriving Inhabited

/-- One sample from a generator, in the form that the Tyche output needs. -/
structure Sample where
  representation : String
  features : List (String × Feature)
  status : Status := .passed
  /-- A reason for the status, in words. An error from the parser is one example. The output holds
      it in the `status_reason` field of Tyche. -/
  statusReason : String := ""
  deriving Inhabited

/-- The class for a type that this module can convert to a Tyche sample. -/
class TycheSample (α : Type) where
  toSample : α → Sample

/-- The JSON form of a status. -/
def Status.toJson : Status → Json
  | .passed => "passed"
  | .failed => "failed"
  | .gaveUp => "gave_up"

/-- The JSON form of a feature value. -/
def Feature.toJson : Feature → Json
  | .ordinal v => Json.num (JsonNumber.fromInt v)
  | .nominal v => Json.str v
  | .continuous v => Lean.toJson v

/-- Writes a sample as one line of Tyche JSONL. -/
def Sample.toJsonLine (s : Sample) (property : String) (runStart : Nat) : String :=
  Json.compress <| Json.mkObj [
    ("type", "test_case"),
    ("run_start", Json.num (JsonNumber.fromNat runStart)),
    ("property", property),
    ("status", s.status.toJson),
    ("status_reason", s.statusReason),
    ("representation", s.representation),
    ("features", Json.mkObj (s.features.map fun (k, v) => (k, v.toJson))),
    ("coverage", Json.null)
  ]

/-- The configuration of a Tyche run. -/
structure Config where
  numSamples : Nat := 1000
  propertyName : String := "generator"
  outputPath : String := "tyche_output.jsonl"
  deriving Inhabited

/-- Adds `numSamples` generated samples to an open handle, as lines of Tyche JSONL. The function
    tries again after a failure, so it writes exactly `numSamples` lines. Many generators can
    therefore share one output file, and no panel needs a temporary file. -/
def runInto [TycheSample α] (handle : IO.FS.Handle) (gen : IO α)
    (property : String) (numSamples : Nat) (runStart : Nat) : IO Unit := do
  let mut written := 0
  let mut retries := 0
  let maxRetries := numSamples * 10
  while written < numSamples && retries < maxRetries do
    try
      let val ← gen
      handle.putStrLn ((TycheSample.toSample val).toJsonLine property runStart)
      written := written + 1
    catch _ =>
      retries := retries + 1

/-- Writes one JSONL line for each element of `samples`, under one property name.

    This function is the deterministic partner of `runInto`. Use it for a property whose input
    space is a *fixed and finite set* and not a distribution. The registered bitvector widths, the
    eighteen `Bv↔Int` operators, and a witness that the author builds are three examples. A sample
    with replacement would give the same few marks many times, so the panel lists the space one
    time. -/
def writeInto [TycheSample α] (handle : IO.FS.Handle) (samples : List α)
    (property : String) (runStart : Nat) : IO Unit := do
  for val in samples do
    handle.putStrLn ((TycheSample.toSample val).toJsonLine property runStart)

/-- Runs a generator `numSamples` times and writes the Tyche JSONL output. The function tries again
    after a failure, so the output always holds exactly `numSamples` lines. -/
def run [TycheSample α] (gen : IO α) (config : Config := {}) : IO Unit := do
  let startTime ← IO.monoMsNow
  let handle ← IO.FS.Handle.mk config.outputPath .write
  runInto handle gen config.propertyName config.numSamples startTime

/-- Runs many generators that have names, and writes each sample to one JSONL file. -/
def runMultiple (generators : List (String × IO Sample)) (config : Config := {}) : IO Unit := do
  let startTime ← IO.monoMsNow
  let handle ← IO.FS.Handle.mk config.outputPath .write
  for (name, gen) in generators do
    for _ in List.range config.numSamples do
      let sample ← gen
      let line := sample.toJsonLine name startTime
      handle.putStrLn line

end Tyche
