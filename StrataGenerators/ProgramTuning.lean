import StrataGenerators.ProgramGen
import StrataGenerators.TuningProfiles

open Lambda RandomChoice Core Imperative

/-!
# The program generator's declaration weights

`StrataGenerators.TuningProfiles` holds the profiles for the statement, procedure, command and
expression families. The program family lives here instead. `ProgramGen` imports the datatype,
function and procedure proof files, and those files import Mathlib. `TuningProfiles` must stay
Mathlib-free, because Strata's transform passes import it.

`genDeclStep` chooses the kind of the next declaration. Its seven branches decide how many
polymorphic functions and polymorphic datatypes a program declares. This module exposes those
branches and adds `progPolyHeavy`, the profile for the `mono:` family.

This module reads the weights from `θ` by hand. `@[tunable]` cannot do it, because the attribute
needs every weight to be a positive literal, and two of `genDeclStep`'s weights are computed. The
generator front-loads functions until one function is callable. A hand-written read keeps that phase
split and exposes both phases. The cost is a hand-written index table, and `genProgramT_defaults`
checks that table. A wrong default weight makes the proof fail.
-/

namespace StrataGenerators.ProgramTuning

open ProgramGen

/-! ## Flat indices

`Tuning.weight` addresses a branch by its index into `Tuning.schedules`. These are the names a
profile is written in. Indices 0 to 4 are the five declaration kinds that carry a literal weight.
Indices 5 to 8 are the two phases of the function and procedure weights. -/

namespace ProgIdx
def abstract : Nat := 0
def alias : Nat := 1
def «axiom» : Nat := 2
def distinct : Nat := 3
def datatype : Nat := 4
/-- The function weight once some declared function is callable. -/
def funcCallable : Nat := 5
/-- The procedure weight in the same phase. -/
def procCallable : Nat := 6
/-- The function weight before any declared function is callable. -/
def funcFrontLoad : Nat := 7
/-- The procedure weight in the same phase. -/
def procFrontLoad : Nat := 8
end ProgIdx

/-- The shipping declaration-kind distribution: 1 each for an abstract type, an alias, an axiom and
a `distinct` assertion, 3 for a datatype block, and 3 : 4 for a function against a procedure once a
function is callable, 6 : 1 before that. -/
def progDefault : Tuning :=
  { schedules := #[(1, 0), (1, 0), (1, 0), (1, 0), (3, 0), (3, 0), (4, 0), (6, 0), (1, 0)] }

/-- The one site a program tuning addresses, for the length check in `TestDecl.withTuning`.

The site holds nine weights but `genDeclStepT` offers seven branches, because the function and the
procedure each carry one weight per phase. Nine is the number a hand-built tuning must match, which
is what this table is for. -/
def progSites : Array Site :=
  #[⟨`genDeclStepT.site0, 0, 9, #[0, 0, 0, 0, 0, 0, 0, 0, 0]⟩]

/-- **Function-heavy** (`mono: …`). `MonomorphizeFunctions` specializes a polymorphic function at
each type its callers instantiate. On a program that declares no polymorphic function the pass is the
identity, and the properties about specialization hold for a reason that has nothing to do with the
pass. This profile raises the function weight in both phases, and raises the datatype block a little.

The procedure weight stays at its default. A procedure body is where a `funcDecl` statement declares
a function, and two properties are about that statement.

Measured, `dist-report 250 100 --prog`:

| | default | `progPolyHeavy` | `progDatatypeHeavy` |
| --- | --- | --- | --- |
| declares a polymorphic function | 63% | **82%** | 28% |
| declares a polymorphic datatype | 44% | 32% | **82%** |
| the pass rewrote the program | 63% | **83%** | 28% |
| declarations in, and out | 3.8 → 3.0 | 3.5 → **2.1** | 3.5 → 3.2 |

The last row is the pass at work. It replaces a polymorphic original by its specializations, so the
output is *shorter* than the input, and the gap widens as polymorphic functions get more common.

The two profiles pull apart, because a declaration is one kind or the other. A function crowds out a
datatype block and a datatype block crowds out a function, so there is a profile for each rather than
one compromise.

The knob is the *number* of functions and datatype blocks. It is not the number of type parameters
each one takes. Type parameters come from `genTypeArgs`, and from the datatype generator's
`maxTyParams` bound. Both draw a count with `RandomChoice.choose` rather than with a `frequency`, so
no `Tuning` reaches them. The number of declarations is enough, because most declared functions are
already polymorphic. -/
def progPolyHeavy : Tuning :=
  StrataGenerators.TuningProfiles.withWeights progDefault
    [(ProgIdx.datatype, 6), (ProgIdx.funcCallable, 20), (ProgIdx.funcFrontLoad, 20)]

/-- **Datatype-heavy** (`mono: a polymorphic datatype …`). The pass keeps a polymorphic datatype
polymorphic and rewrites the functions that the datatype derives. Both claims need a datatype block
with type parameters, so this raises only that branch. See the table in `progPolyHeavy` for the
measured trade against the function rate. -/
def progDatatypeHeavy : Tuning :=
  StrataGenerators.TuningProfiles.withWeights progDefault [(ProgIdx.datatype, 12)]

/-- `genDeclStep` with the seven declaration-kind weights read from `θ`. `d` is the number of
declaration steps that remain, so a schedule can taper a kind as the program fills up.

The pair of function and procedure weights is chosen by one `if`, as `genDeclStep` chooses it. Two
separate `if`s would read the same but would not be definitionally equal to it, because the
projection of an `ite` does not reduce while the condition is a variable. -/
def genDeclStepT [_root_.Gen G] (θ : Tuning) (s : GenState) (b : Bounds) (d : Nat) :
    G StepResult :=
  let (wFunc, wProc) :=
    if hasCallableFunc s then (θ.weight ProgIdx.funcCallable d, θ.weight ProgIdx.procCallable d)
    else (θ.weight ProgIdx.funcFrontLoad d, θ.weight ProgIdx.procFrontLoad d)
  frequency
    [ (θ.weight ProgIdx.abstract d, fun () => genDeclAbstract s b)
    , (θ.weight ProgIdx.alias d, fun () => genDeclAlias s b)
    , (θ.weight ProgIdx.axiom d, fun () => genDeclAxiom s b)
    , (θ.weight ProgIdx.distinct d, fun () => genDeclDistinct s b)
    , (θ.weight ProgIdx.datatype d, fun () => genDeclDatatype s b)
    , (wFunc, fun () => genDeclFunction s b)
    , (wProc, fun () => genDeclProcedure s b) ]
    (by
      have := Tuning.weight_pos θ ProgIdx.abstract d
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)

/-- `genDeclsFold` over the tuned step. -/
def genDeclsFoldT [_root_.Gen G] (θ : Tuning) (s : GenState) (b : Bounds) :
    Nat → G (List Decl × GenState)
  | 0 => pure ([], s)
  | n + 1 => do
    let (ds, s') ← genDeclStepT θ s b (n + 1)
    let (rest, s'') ← genDeclsFoldT θ s' b n
    pure (ds ++ rest, s'')

/-- `genProgram` with the declaration-kind weights read from `θ`. -/
def genProgramT [_root_.Gen G] (θ : Tuning) (numDecls : Nat := 6) (b : Bounds := {}) : G Program :=
  do
  let (decls, _) ← genDeclsFoldT θ initState b numDecls
  pure { decls := decls }

-- Each `rfl` below reduces nine `Array.getD` reads against a literal schedule.
set_option maxRecDepth 4000

/-- At `progDefault` every weight reads back as the literal the shipping generator writes, so the
tuned declaration step is `ProgramGen.genDeclStep`. This is what keeps `progDefault` honest: a wrong
entry in the table above breaks this proof rather than silently shifting the untuned distribution.

The weight of each branch reduces to its literal at any depth `d`, because every growth coefficient
in `progDefault` is `0`. -/
@[simp] theorem genDeclStepT_defaults [_root_.Gen G] (s : GenState) (b : Bounds) (d : Nat) :
    genDeclStepT (G := G) progDefault s b d = genDeclStep s b := rfl

/-- The tuned declaration fold at `progDefault` is `ProgramGen.genDeclsFold`, for any number of
steps. -/
@[simp] theorem genDeclsFoldT_defaults [_root_.Gen G] (s : GenState) (b : Bounds) (n : Nat) :
    genDeclsFoldT (G := G) progDefault s b n = genDeclsFold s b n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [genDeclsFoldT, genDeclsFold, genDeclStepT_defaults, ih]

/-- The tuned program generator at `progDefault` is `ProgramGen.genProgram`. -/
@[simp] theorem genProgramT_defaults [_root_.Gen G] (numDecls : Nat) (b : Bounds) :
    genProgramT (G := G) progDefault numDecls b = genProgram numDecls b := by
  simp only [genProgramT, genProgram, genDeclsFoldT_defaults]

/-! The index table names a branch each profile moves. These pin the two facts a reader needs: the
table has an entry per branch, and each profile moves the branch it names. -/

example : progDefault.schedules.size = 9 := rfl
example : (progSites.foldl (fun n s => n + s.arity) 0) = progDefault.schedules.size := rfl
example : progPolyHeavy.schedules[ProgIdx.datatype]! = (6, 0) := rfl
example : progPolyHeavy.schedules[ProgIdx.procCallable]! = (4, 0) := rfl
example : progDatatypeHeavy.schedules[ProgIdx.funcCallable]! = (3, 0) := rfl

end StrataGenerators.ProgramTuning
