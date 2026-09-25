/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
-/
import Basalt.Fuzz.Runner
import StrataFuzz.Props
import StrataGenerators.RetryGen

/-!
# `strata-fuzz` executable entry point

Lean owns `main`; it selects a named property and a backend. The `fuzz` backend is Basalt's
libFuzzer driver (`Basalt.Fuzz.go`). The **random** backends are dispatched *here*, in Strata, not
by Basalt's generic `dispatch` — so that a `Plausible.Gen` draw is run exactly as the legacy Strata
suite runs one: wrapped in `retryGen`, which retries a failed draw *inside* the `Gen` monad,
advancing the RNG with `Rand.next`.

Why that wrapper is needed only here: a Basalt generator can fail (`default`), and Plausible rolls
its RNG state back when it catches that failure — so a raw generator drawn once per `Gen.run`
repeats the same failing input forever. The Plausible suite never hits this because its `Arbitrary`
instances are already `retryGen`-wrapped; we do the same. `FuzzGen` needs no wrapper (a failed draw
is a `none` that libFuzzer mutates past); `IO` re-draws on failure (each `IO.rand` reseeds). Basalt
and Plausible are untouched.

Each registry entry is a `Basalt.PBT.Property` (a `PropM G Unit` polymorphic in the monad) — so one
entry serves all three backends. This module and everything it imports is Mathlib-free (Plausible is),
so the executable links a small closure; it is built by `fuzz-experiment/scripts/build.sh`.
-/

open Basalt.Fuzz Basalt.PBT

/-- The property registry, selected by the first non-flag CLI argument. -/
def properties : List (String × Property) :=
  [ ("expr-preservation", fun _ => StrataFuzz.Expr.prop_exprPreservation),
    ("expr-progress",     fun _ => StrataFuzz.Expr.prop_exprProgress),
    ("stmt-anf-preservation", fun _ => StrataFuzz.Stmt.prop_stmtAnfPreservesTyping),
    ("stmt-typecheck-complete", fun _ => StrataFuzz.Stmt.prop_stmtTypeCheckComplete),
    ("expr-preservation-deep", fun _ => StrataFuzz.Expr.prop_exprPreservationDeep),
    ("prog-lift-output-typechecks", fun _ => StrataFuzz.Program.prop_liftOutputTypechecks) ]

/-- Attempts a failed draw is redrawn before it is scored as a discard. -/
def retryFuel : Nat := 500

/-- One `Plausible.Gen` draw, run the way the legacy Strata suite runs one: `retryGen` retries a
failed draw in-`Gen` (advancing via `Rand.next`) instead of repeating it. A draw that never succeeds
becomes a `discard`, so the campaign never crashes. -/
def plausibleStep (T : Property) : IO TestOutcome := do
  try Plausible.Gen.run (retryGen retryFuel (runProp (T Plausible.Gen))) 0
  catch _ => pure (.error .discard)

/-- One `IO` draw: re-run on a thrown generation failure (each `IO.rand` reseeds, so the redraw
differs); a draw that never succeeds becomes a `discard`. -/
def ioStep (T : Property) : Nat → IO TestOutcome
  | 0 => pure (.error .discard)
  | fuel + 1 => try runProp (T IO) catch _ => ioStep T fuel

/-- Replay every saved input in a directory against a property, under `FuzzGen`, in **one process**.
Used by the coverage study: running a whole libFuzzer corpus this way lets the coverage meter
(`fuzz-experiment/scripts/covmeter.c`, linked into the `strata-cov` build) accumulate the code-under-
test edges the fuzzer's corpus reaches, on the *same* counter the `io`/`plausible` campaigns use — so
the three backends are compared on one metric. Not for libFuzzer builds (no coverage guidance here);
this just executes each input once. -/
def replayDir (T : Property) (dir : String) : IO Unit := do
  let entries ← System.FilePath.readDir dir
  let mut n := 0
  let mut fails := 0
  for e in entries do
    if ← e.path.isDir then continue
    let bytes ← IO.FS.readBinFile e.path
    -- Match on the outcome so the (pure) `runOne` is forced — the point is to *execute* the
    -- instrumented code-under-test, which the coverage meter observes.
    match runOne (T FuzzGen) bytes with
    | .error (.fail _) => fails := fails + 1
    | _ => pure ()
    n := n + 1
  IO.println s!"[strata-cov] replayed {n} corpus inputs from {dir} ({fails} counterexamples)"

/-- Strata-owned dispatch. `fuzz` uses Basalt's libFuzzer driver; `io`/`plausible` reuse Basalt's
`PBT.campaign` loop but with a Strata-constructed, failure-robust step; `replay` uses Basalt;
`replay-dir` runs a whole corpus in one process for the coverage study. -/
def strataDispatch (props : List (String × Property)) (args : List String) : IO Unit := do
  let names := String.intercalate ", " (props.map (·.1))
  let usage :=
    "usage: strata-fuzz [--backend=fuzz|io|plausible] <property> [-runs=N] [libFuzzer args...]\n"
      ++ "       strata-fuzz replay <property> <file>\n"
      ++ "       strata-fuzz replay-dir <property> <dir>\n"
      ++ s!"known properties: {names}"
  match args with
  | "replay" :: name :: path :: _ =>
    match props.lookup name with
    | some T => replay (T FuzzGen) path
    | none => IO.eprintln s!"unknown property '{name}'; known: {names}"
  | "replay-dir" :: name :: dir :: _ =>
    match props.lookup name with
    | some T => replayDir T dir
    | none => IO.eprintln s!"unknown property '{name}'; known: {names}"
  | _ =>
    let (flags, rest) := args.partition (·.startsWith "--backend=")
    let backend? := flags.head?.map (fun f => f.drop "--backend=".length)
    match rest with
    | [] => IO.eprintln usage
    | name :: rest =>
      match props.lookup name with
      | none => IO.eprintln s!"unknown property '{name}'; known: {names}"
      | some T =>
        let backend := backend?.getD "fuzz"
        if backend == "fuzz" then go (T FuzzGen) rest.toArray
        else if backend == "io" then campaign "IO" (ioStep T retryFuel) (runsOf rest.toArray)
        else if backend == "plausible" then
          campaign "Plausible.Gen" (plausibleStep T) (runsOf rest.toArray)
        else IO.eprintln s!"unknown backend '{backend}'\n{usage}"

def main (args : List String) : IO Unit :=
  strataDispatch properties args
