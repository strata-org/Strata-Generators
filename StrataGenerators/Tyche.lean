import Basalt.IO

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
  deriving Inhabited

/-- Typeclass for types that can be converted to Tyche samples. -/
class TycheSample (α : Type) where
  toSample : α → Sample

private def escapeJson (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | c => acc.push c) ""

def Status.toJson : Status → String
  | .passed => "\"passed\""
  | .failed => "\"failed\""
  | .gaveUp => "\"gave_up\""

def Feature.toJson : Feature → String
  | .ordinal v => toString v
  | .nominal v => s!"\"{escapeJson v}\""
  | .continuous v => toString v

private def featuresJson (features : List (String × Feature)) : String :=
  let pairs := features.map fun (k, v) =>
    s!"\"{k}\":{Feature.toJson v}"
  "{" ++ String.intercalate "," pairs ++ "}"

/-- Serialize a sample as one line of Tyche JSONL. -/
def Sample.toJsonLine (s : Sample) (property : String) (runStart : Nat) : String :=
  let repr := escapeJson s.representation
  s!"\{\"type\":\"test_case\",\"run_start\":{runStart},\"property\":\"{property}\",\"status\":{Status.toJson s.status},\"status_reason\":\"\",\"representation\":\"{repr}\",\"features\":{featuresJson s.features},\"coverage\":null}"

/-- Configuration for a Tyche run. -/
structure Config where
  numSamples : Nat := 1000
  propertyName : String := "generator"
  outputPath : String := "tyche_output.jsonl"
  deriving Inhabited

/-- Run a generator `numSamples` times and write Tyche JSONL output. -/
def run [TycheSample α] (gen : IO α) (config : Config := {}) : IO Unit := do
  let startTime ← IO.monoMsNow
  let handle ← IO.FS.Handle.mk config.outputPath .write
  let mut i := 0
  while i < config.numSamples do
    try
      let val ← gen
      let sample := TycheSample.toSample val
      let line := sample.toJsonLine config.propertyName startTime
      handle.putStrLn line
    catch _ => pure ()
    i := i + 1

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
