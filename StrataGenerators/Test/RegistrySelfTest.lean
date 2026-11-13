import StrataGenerators.Test
import StrataGenerators.TycheViz

/-!
# A self-test of the registration attributes

`parseTuningArg?` and `seedOf?` in `StrataGenerators.Test.Registry` read the syntax of
`@[strata_property …]` by position (`spec[3]`, `arg[4][3]`), not with a quotation pattern. A
change to the grammar can therefore make them read the wrong node, and the result is silent:
the property registers *untuned*, or *without* its pin, and the suite still runs. This module
registers 1 property for each form of the attribute and checks, at build time, what the registry
recorded. A misread fails `lake build`.

This module is in the `StrataGenerators` library, not under `StrataTests/`. No driver imports it,
so its properties never join the suite.
-/

namespace StrataGenerators.Test.RegistrySelfTest

open Lean Elab Command
open StrataGenerators StrataGenerators.Test StrataGenerators.TuningProfiles

/-- The body of each property below. It is never run. -/
private def trivialProp (name : String) : TestDecl :=
  .property name fun (_ : GenStmts) => True

@[strata_property]
def plain : TestDecl := trivialProp "selftest: plain"

@[strata_property (seed := 7)]
def seedOnly : TestDecl := trivialProp "selftest: seed only"

@[strata_property (seed := 7, numTrials := 100)]
def seedTrials : TestDecl := trivialProp "selftest: seed and trials"

@[strata_property (seed := 7, maxSize := 3)]
def seedSize : TestDecl := trivialProp "selftest: seed and size"

@[strata_property (seed := 7, numTrials := 100, maxSize := 2)]
def seedFull : TestDecl := trivialProp "selftest: full pin"

@[strata_property (tuning := stmtLoopHeavy)]
def tuned : TestDecl := trivialProp "selftest: tuned"

@[strata_property (tuning := stmtLoopHeavy) (seed := 9, numTrials := 50, maxSize := 4)]
def tunedPinned : TestDecl := trivialProp "selftest: tuned and pinned"

@[strata_property (tunings := [("default", stmtDefault), ("loop-heavy", stmtLoopHeavy)])]
def tuningMatrix : TestDecl := trivialProp "selftest: tuning matrix"

@[strata_properties (seed := 11, numTrials := 20, maxSize := 1)]
def pinnedFamily : List TestDecl :=
  [trivialProp "selftest: family 1", trivialProp "selftest: family 2"]

-- `numTrials := 0` tests nothing, so the attribute rejects it.
/--
error: `numTrials := 0` draws no inputs, so the property tests nothing. Give at least 1 trial.
-/
#guard_msgs in
@[strata_property (seed := 7, numTrials := 0)]
def zeroTrials : TestDecl := trivialProp "selftest: zero trials"

/-- What the registry must hold for this module, in declaration order. A tuned property
    registers its generated `….tuned` declaration, so an entry with the plain name in place of
    the tuned one means that the tuning was dropped. -/
private def expected : List Entry :=
  let ns := `StrataGenerators.Test.RegistrySelfTest
  let pin (s t m : Nat) : Option SeedPin := some { seed := s, numTrials := t, maxSize := m }
  [ .single (ns ++ `plain) none,
    .single (ns ++ `seedOnly) (pin 7 defaultNumTrials defaultMaxSize),
    .single (ns ++ `seedTrials) (pin 7 100 defaultMaxSize),
    .single (ns ++ `seedSize) (pin 7 defaultNumTrials 3),
    .single (ns ++ `seedFull) (pin 7 100 2),
    .single (ns ++ `tuned ++ `tuned) none,
    .single (ns ++ `tunedPinned ++ `tuned) (pin 9 50 4),
    .many (ns ++ `tuningMatrix ++ `tuned) none,
    .many (ns ++ `pinnedFamily) (pin 11 20 1) ]

run_cmd do
  let ns := `StrataGenerators.Test.RegistrySelfTest
  let mine := (registryEntries (← getEnv)).toList.filter fun
    | .single n _ | .many n _ => ns.isPrefixOf n
  unless mine == expected do
    throwError "the registry misread an attribute.\nexpected:{indentD (repr expected)}\n\
      got:{indentD (repr mine)}"

end StrataGenerators.Test.RegistrySelfTest
