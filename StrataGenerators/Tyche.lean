import Basalt.IO
import Lean.Data.Json

/-!
# Tyche Visualization Support

This module provides infrastructure for outputting generator samples in the
[Tyche](https://github.com/tyche-pbt/tyche-extension) JSONL format.
Tyche is a VS Code extension for visualizing PBT generator distributions.

## JSONL Format

Each line in the output file is a JSON object with `type: "test_case"`:
```json
{"type":"test_case","run_start":<timestamp>,"property":"<name>",
 "status":"passed","status_reason":"","representation":"<value>",
 "features":{...},"coverage":null}
```

## Usage

1. Implement a `TycheSample` instance for your generated type.
2. Call `Tyche.run` with a generator action and output path.
3. Open the resulting `.jsonl` file with Tyche (`Tyche: Open` in VS Code).
-/

open Lean (Json JsonNumber)

namespace Tyche

/-- The status of a generated test case. -/
inductive Status where
  | passed
  | failed
  | gaveUp
  deriving Inhabited

/-- A feature value for Tyche visualization. -/
inductive Feature where
  | ordinal (v : Int)
  | nominal (v : String)
  | continuous (v : Float)
  deriving Inhabited

/-- A single sample produced by a generator, ready for Tyche serialization. -/
structure Sample where
  representation : String
  features : List (String × Feature)
  status : Status := .passed
  /-- Optional human-readable reason for the status (e.g. a parser error on a
      failure). Serialized to Tyche's `status_reason` field. -/
  statusReason : String := ""
  deriving Inhabited

/-- Typeclass for types that can be converted to Tyche samples. -/
class TycheSample (α : Type) where
  toSample : α → Sample

def Status.toJson : Status → Json
  | .passed => "passed"
  | .failed => "failed"
  | .gaveUp => "gave_up"

def Feature.toJson : Feature → Json
  | .ordinal v => Json.num (JsonNumber.fromInt v)
  | .nominal v => Json.str v
  | .continuous v => Lean.toJson v

/-- Serialize a sample as one line of Tyche JSONL. -/
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

/-- Configuration for a Tyche run. -/
structure Config where
  numSamples : Nat := 1000
  propertyName : String := "generator"
  outputPath : String := "tyche_output.jsonl"
  deriving Inhabited

/-- Append `numSamples` generated samples to an already-open handle as Tyche
    JSONL lines. Retries on failure so exactly `numSamples` lines are written.
    Lets many generators share one output file without per-panel temp files. -/
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

/-- Write one JSONL line per element of `samples`, all under the same property
    name. The deterministic counterpart of `runInto`: for a property whose input
    space is a *fixed finite set* rather than a distribution — the registered
    bitvector widths, the eighteen `Bv↔Int` operators, a constructed no-op witness —
    sampling with replacement would emit the same few marks repeatedly, so the panel
    enumerates the space exactly once instead. -/
def writeInto [TycheSample α] (handle : IO.FS.Handle) (samples : List α)
    (property : String) (runStart : Nat) : IO Unit := do
  for val in samples do
    handle.putStrLn ((TycheSample.toSample val).toJsonLine property runStart)

/-- Run a generator `numSamples` times and write Tyche JSONL output.
    Retries on failure so the output always contains exactly `numSamples` lines. -/
def run [TycheSample α] (gen : IO α) (config : Config := {}) : IO Unit := do
  let startTime ← IO.monoMsNow
  let handle ← IO.FS.Handle.mk config.outputPath .write
  runInto handle gen config.propertyName config.numSamples startTime

/-- Run multiple named generators and write all samples to one JSONL file. -/
def runMultiple (generators : List (String × IO Sample)) (config : Config := {}) : IO Unit := do
  let startTime ← IO.monoMsNow
  let handle ← IO.FS.Handle.mk config.outputPath .write
  for (name, gen) in generators do
    for _ in List.range config.numSamples do
      let sample ← gen
      let line := sample.toJsonLine name startTime
      handle.putStrLn line

end Tyche
